; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Quantifiers anywhere in a term, nested.
;
; Defun-sk accepts only one outermost quantifier.  Elab-quantifiers takes a
; term in which (forall vars body) and (exists vars body) may appear anywhere,
; nested, and returns
;
;   - the term with each quantified subterm replaced by a call of a generated
;     function, and
;   - the defun-sk events (with table events) that introduce those functions.
;
; Quantifiers are elaborated innermost first, so each generated defun-sk has
; one outermost quantifier and a quantifier-free body.  The arguments of a
; generated function are the free variables of its quantified subterm, in
; order of first occurrence; they are computed by translating the subterm, so
; macros and let are handled.
;
; Generated functions are shared: zq-table maps each quantified formula,
; normalized by renaming its variables to a fixed pattern, to its function.
; So two quantified formulas that are the same up to renaming of variables
; give calls of the same function.  For that reason the functions have
; neutral names, zq$1, zq$2, ....  A function defined with defunz whose body
; is a quantifier at the top, such as subset, is entered in the table too, so
; a later quantifier with the same formula becomes a call of it.  The table
; guard checks every entry against the event that introduced its function.
;
; The generated functions are introduced with def::un-skd from
; coi/quantification: a defun-sk, disabled, with coi's rules and registration,
; so that the hints quant::inst? and quant::skosimp can instantiate and
; skolemize them automatically.
;
; In proof output, calls of generated functions are printed as the quantified
; formulas they stand for (see "Display" below), so zq$n is normally not seen
; in goals and checkpoints.  The names do still appear in a few places, since
; zq$n are real functions and only the printing of terms is changed:
;
;   - in the output of coi's hints during a proof, for example
;       Instantiable Formula In Goal:
;          ZQ$1 : (EXISTS (Y) (AND (IN A Y) (IN Y X)))
;       Computed Hint: (:USE (:INSTANCE ZQ$1-SUFF ...))
;     (the first shows the formula next to the name);
;   - in the summary of a proof, under Rules (for example
;     (:REWRITE ZQ$1-BY-MULTIPLICITY)) and Hint-events (for example
;     (:USE ZQ$1-SUFF));
;   - in values that ACL2 prints as data rather than as terms, for example the
;     result of (acl2::formula 'in-union nil (w state)), and in :pe of a
;     generated function;
;   - in the events that defunz, defthmz, defthmdz and thmz print when they
;     run, which
;     include the def::un-skd for each new zq$n.
;
; Each zq$n is a defun-sk for one quantified formula; :pe zq$n shows it, and
; zq-table and zq-display-table record which formula it stands for.

(in-package "ZF")

(include-book "coi/quantification/quantification" :dir :system)

;;; Recognizing quantifiers

(defun quant-form-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (member-eq (car x) '(forall exists))
       (consp (cdr x))
       (consp (cddr x))
       (null (cdddr x))
       (or (and (symbolp (cadr x))
                (cadr x))
           (and (symbol-listp (cadr x))
                (consp (cadr x))
                (no-duplicatesp-eq (cadr x))))))

(defun quant-bound-vars (x)
  (declare (xargs :guard (quant-form-p x)))
  (if (symbolp (cadr x))
      (list (cadr x))
    (cadr x)))

;;; Variables of a translated term, in order of first occurrence.  ACL2
;;; lambdas are closed, so only their actuals contribute.

(mutual-recursion
 (defun term-vars-in-order (term acc)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbol-listp acc))
                   :verify-guards nil))
   (cond ((acl2::variablep term)
          (if (member-eq term acc) acc (append acc (list term))))
         ((acl2::fquotep term) acc)
         (t (term-list-vars-in-order (acl2::fargs term) acc))))
 (defun term-list-vars-in-order (terms acc)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbol-listp acc))))
   (cond ((endp terms) acc)
         (t (term-list-vars-in-order
             (cdr terms)
             (term-vars-in-order (car terms) acc))))))

;;; Canonical form of a quantified formula, for sharing: free variables are
;;; renamed ZQ-F0, ZQ-F1, ... (in argument order) and bound variables ZQ-B0,
;;; ZQ-B1, ... (in the order given).

(defun zq-canonical-vars (prefix n vars)
  (declare (xargs :guard (and (symbolp prefix) (natp n) (true-listp vars))
                  :verify-guards nil))
  (cond ((endp vars) nil)
        (t (acons (car vars)
                  (packn-pos (list prefix n) 'zq-table)
                  (zq-canonical-vars prefix (1+ n) (cdr vars))))))

(defun zq-key (kind bound args tbody)

; Tbody is the translated body, with calls of the functions for its inner
; quantifiers.  The number of arguments is part of the key, since a function
; defined with defunz may have formals that do not occur in its body.

  (declare (xargs :mode :program))
  (let ((alist (append (zq-canonical-vars 'zq-f 0 args)
                       (zq-canonical-vars 'zq-b 0 bound))))
    (list kind (len bound) (len args) (acl2::sublis-var alist tbody))))

;;; While elaborating, an inner quantifier whose function does not exist yet is
;;; represented by (zq-placeholder 'name (list args ...)), which translates
;;; and keeps the variables.  Placeholders-to-calls then turns the translated
;;; term into the one with real calls (name args ...), so that a key is
;;; computed from the same term that the body of the function translates to,
;;; as the table guard recomputes it.

(defun zq-placeholder (name args)
  (declare (ignore name args)
           (xargs :guard t))
  nil)

(defun translated-list-elements (term)

; Term is the translation of (list x1 ... xn); return (x1 ... xn).

  (declare (xargs :mode :program))
  (if (and (consp term) (eq (car term) 'cons))
      (cons (cadr term) (translated-list-elements (caddr term)))
    nil))

(mutual-recursion
 (defun placeholders-to-calls (term)
   (declare (xargs :mode :program))
   (cond ((or (acl2::variablep term) (acl2::fquotep term)) term)
         ((and (eq (car term) 'zq-placeholder)
               (acl2::quotep (cadr term)))
          (cons (acl2::unquote (cadr term))
                (placeholders-to-calls-lst
                 (translated-list-elements (caddr term)))))
         ((consp (car term)) ; lambda
          (cons (list 'lambda (cadr (car term))
                      (placeholders-to-calls (caddr (car term))))
                (placeholders-to-calls-lst (cdr term))))
         (t (cons (car term) (placeholders-to-calls-lst (cdr term))))))
 (defun placeholders-to-calls-lst (terms)
   (declare (xargs :mode :program))
   (if (endp terms)
       nil
     (cons (placeholders-to-calls (car terms))
           (placeholders-to-calls-lst (cdr terms))))))

(defun zq-fresh-name (prefix n taken wrld)

; The first prefix followed by n, n >= 1, that is not already a function or
; macro, nor among the names taken by the current elaboration.

  (declare (xargs :mode :program))
  (let ((name (packn (list prefix n))))
    (if (or (member-eq name taken)
            (acl2::function-symbolp name wrld)
            (getpropc name 'acl2::macro-args nil wrld))
        (zq-fresh-name prefix (1+ n) taken wrld)
      name)))

(defun zsub-form-p (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (eql (len x) 4)
       (eq (car x) 'zsub)
       (acl2::legal-variablep (cadr x))))

(defun zs-key (args x ts tphi)
  (declare (xargs :mode :program))
  (let ((alist (append (zq-canonical-vars 'zq-f 0 args)
                       (list (cons x 'zq-b0)))))
    (list :zsub
          (len args)
          (acl2::sublis-var alist ts)
          (acl2::sublis-var alist tphi))))

(defun zs-entry-key (val wrld)

  (declare (xargs :mode :program))
  (case-match val
    (('zsub & args x s u)
     (mv-let (erp1 ts)
       (acl2::translate-cmp s t nil t 'zs-entry-key wrld
                            (acl2::default-state-vars nil))
       (mv-let (erp2 tu)
         (acl2::translate-cmp u t nil t 'zs-entry-key wrld
                              (acl2::default-state-vars nil))
         (and (not erp1)
              (not erp2)
              (zs-key args x ts tu)))))
    (& nil)))

(defun zs-lookup-table (key alist wrld)
  (declare (xargs :mode :program))
  (cond ((endp alist) nil)
        ((and (consp (car alist))
              (consp (cdar alist))
              (eq (car (cdar alist)) 'zsub)
              (equal (zs-entry-key (cdar alist) wrld) key))
         (nth 1 (cdar alist)))
        (t (zs-lookup-table key (cdr alist) wrld))))

(defun zs-lookup (key pending wrld)

  (declare (xargs :mode :program))
  (or (cdr (assoc-equal key pending))
      (zs-lookup-table key (table-alist 'zfc-table wrld) wrld)))

(defun zq-theorem-props (term wrld)

  (declare (xargs :mode :program))
  (let ((keys (strip-cars (table-alist 'zfc-table wrld))))
    (and keys
         (intersection-eq keys
                          (acl2::instantiable-ancestors
                           (acl2::all-fnnames term) wrld nil)))))

;;; The table guard.  As zfc-table-guard in base.lisp checks that an entry
;;; names the event that its macro would produce, an entry
;;;
;;;   key -> (name args kind bvars body dcls)
;;;
;;; is accepted only if
;;;
;;;   - key is the canonical key of the formula (kind bvars body) with
;;;     arguments args, recomputed here from the translation of body, and
;;;   - the event that introduced name-witness is exactly the encapsulate that
;;;     (def::un-skd name args (kind bvars body) :witness-dcls dcls) produces
;;;     through defun-sk.
;;;     That encapsulate defines name and proves its -suff (or -necc) theorem,
;;;     so name means exactly that formula.
;;;
;;; So no entry can map a quantified formula to a function that does not mean
;;; it.  The comparison is with ACL2's own defun-sk-fn, given the keyword
;;; arguments that def::un-skd passes to defun-sk.

(mutual-recursion
 (defun strip-with-output (x)

; Remove with-output wrappers, which the stored events do not have.

   (declare (xargs :mode :program))
   (cond ((atom x) x)
         ((eq (car x) 'with-output) (strip-with-output (car (last x))))
         (t (strip-with-output-lst x))))
 (defun strip-with-output-lst (x)
   (declare (xargs :mode :program))
   (if (atom x)
       x
     (cons (strip-with-output (car x)) (strip-with-output-lst (cdr x))))))

(mutual-recursion
 (defun find-witness-encapsulate (witness x)

; The encapsulate in x whose signature introduces witness.

   (declare (xargs :mode :program))
   (cond ((atom x) nil)
         ((and (eq (car x) 'encapsulate)
               (consp (cdr x))
               (consp (cadr x))
               (consp (car (cadr x)))
               (consp (car (car (cadr x))))
               (eq (car (car (car (cadr x)))) witness))
          x)
         (t (find-witness-encapsulate-lst witness x))))
 (defun find-witness-encapsulate-lst (witness x)
   (declare (xargs :mode :program))
   (if (atom x)
       nil
     (or (find-witness-encapsulate witness (car x))
         (find-witness-encapsulate-lst witness (cdr x))))))

(defun zq-witness-event (name args kind bvars body dcls)

; The encapsulate introducing name-witness that def::un-skd produces.

  (declare (xargs :mode :program))
  (let* ((witness (acl2::add-suffix name "-WITNESS"))
         (thm (acl2::add-suffix name (if (eq kind 'exists) "-SUFF" "-NECC")))
         (rest `(,@dcls (,kind ,bvars ,body)
                        :skolem-name ,witness :thm-name ,thm)))
    (find-witness-encapsulate
     witness
     (strip-with-output
      (acl2::defun-sk-fn `(defun-sk ,name ,args ,@rest) name args rest)))))

(defun zq-table-guard (key val wrld)
  (declare (xargs :mode :program)) ; because of get-event
  (case-match val
    ((name args kind bvars body dcls)
     (and (symbolp name)
          name
          (symbol-listp args)
          (no-duplicatesp-eq args)
          (member-eq kind '(forall exists))
          (or (and (symbolp bvars) bvars)
              (and (symbol-listp bvars) (consp bvars)))
          (true-listp dcls)
          (let ((bound (if (symbolp bvars) (list bvars) bvars)))
            (mv-let (erp tbody)
              (acl2::translate-cmp body t nil t 'zq-table-guard wrld
                                   (acl2::default-state-vars nil))
              (and (not erp)
                   (equal key (zq-key kind bound args tbody))
                   (equal (zq-witness-event name args kind bvars body dcls)
                          (get-event (acl2::add-suffix name "-WITNESS")
                                     wrld)))))))
    (& nil)))

(table zq-table nil nil
       :guard (acl2::strict-table-guard (zq-table-guard key val world)))

(defun zq-lookup (key pending verify wrld)
  (declare (xargs :mode :program))
  (or (cdr (assoc-equal key pending))
      (let ((name (car (cdr (assoc-equal key (table-alist 'zq-table wrld))))))
        (and name
             (or (not verify)
                 (equal (getpropc name 'acl2::guard acl2::*t* wrld)
                        acl2::*t*))
             name))))

;;; Display.  Generated functions should not show in proof output: a call
;;; (zq$n a1 ... ak) is printed as the quantified formula it stands for, with
;;; the arguments substituted.  Zq-display-table maps each generated function
;;; to (formals kind bound tbody).  This affects printing only (see :DOC
;;; user-defined-functions-table), not what is proved.
;;;
;;; A bound variable is renamed when it occurs in the arguments, so that it
;;; does not capture them: (zq$1 a y), where zq$1 is (exists y (and (in a y)
;;; (in y x))), prints as (exists y1 (and (in a y1) (in y1 y))).

(defun suffix-symbol-zq (suffix sym)

  (declare (type string suffix)
           (type symbol sym))
  (fix-intern-in-pkg-of-sym
   (concatenate 'string (symbol-name sym) suffix)
   sym))

(defun zq-display-guard (key val wrld)

; An entry name -> (formals kind bound tbody) is accepted only if zq-table,
; whose entries are checked against their events, has an entry for name with
; these formals and with the key of (kind bound formals tbody).  So a call of
; name prints as the formula that name means.

  (declare (xargs :mode :program))
  (case-match val
    ((formals :zsub x (ts tphi))
     (let ((entry (cdr (assoc-eq (suffix-symbol-zq "$PROP" key)
                                 (table-alist 'zfc-table wrld)))))
       (case-match entry
         (('zsub !key !formals !x s u)
          (mv-let (erp1 ts2)
            (acl2::translate-cmp s t nil t 'zq-display-guard wrld
                                 (acl2::default-state-vars nil))
            (mv-let (erp2 tu2)
              (acl2::translate-cmp u t nil t 'zq-display-guard wrld
                                   (acl2::default-state-vars nil))
              (and (not erp1) (not erp2)
                   (equal ts ts2)
                   (equal tphi tu2)))))
         (& nil))))
    ((formals kind bound tbody)
     (let ((pair (assoc-equal (zq-key kind bound formals tbody)
                              (table-alist 'zq-table wrld))))
       (and pair
            (eq (nth 0 (cdr pair)) key)
            (equal (nth 1 (cdr pair)) formals))))
    (& nil)))

(table zq-display-table nil nil
       :guard (acl2::strict-table-guard (zq-display-guard key val world)))

(defun zq-fresh-var (v avoid n)
  (declare (xargs :mode :program))
  (let ((v2 (if (eql n 0) v (packn-pos (list v n) v))))
    (if (member-eq v2 avoid)
        (zq-fresh-var v avoid (1+ n))
      v2)))

(defun zq-fresh-vars (vars avoid)

; Returns an alist mapping each of vars to a variable not in avoid, all
; distinct.

  (declare (xargs :mode :program))
  (if (endp vars)
      nil
    (let ((v (zq-fresh-var (car vars) avoid 0)))
      (acons (car vars) v (zq-fresh-vars (cdr vars) (cons v avoid))))))

(mutual-recursion
 (defun zq-display-term (term tbl)
   (declare (xargs :mode :program))
   (cond
    ((or (acl2::variablep term) (acl2::fquotep term)) term)
    ((consp (car term)) ; lambda
     (cons (list 'lambda (cadr (car term))
                 (zq-display-term (caddr (car term)) tbl))
           (zq-display-term-lst (cdr term) tbl)))
    (t
     (let ((entry (cdr (assoc-eq (car term) tbl))))
       (if (and entry
                (eql (len (car entry)) (len (cdr term))))
           (let* ((formals (nth 0 entry))
                  (kind (nth 1 entry))
                  (bound (if (eq kind :zsub)
                             (list (nth 2 entry))
                           (nth 2 entry)))
                  (tbody (nth 3 entry))
                  (ren (zq-fresh-vars bound
                                      (acl2::all-vars1-lst (cdr term) nil)))
                  (alist (append ren (pairlis$ formals (cdr term))))
                  (vars (strip-cdrs ren)))
             (if (eq kind :zsub)
                 (list 'zsub
                       (car vars)
                       (zq-display-term (acl2::sublis-var alist (car tbody))
                                        tbl)
                       (zq-display-term (acl2::sublis-var alist (cadr tbody))
                                        tbl))
               (list kind
                     (if (cdr vars) vars (car vars))
                     (zq-display-term (acl2::sublis-var alist tbody) tbl))))
         (cons (car term) (zq-display-term-lst (cdr term) tbl)))))))
 (defun zq-display-term-lst (terms tbl)
   (declare (xargs :mode :program))
   (if (endp terms)
       nil
     (cons (zq-display-term (car terms) tbl)
           (zq-display-term-lst (cdr terms) tbl)))))

(defun zq-untranslate-preprocess (term wrld)
  (declare (xargs :mode :program))
  (let ((tbl (table-alist 'zq-display-table wrld)))
    (and tbl
         (let ((new (zq-display-term term tbl)))
           (and (not (equal new term))
                new)))))

; WARNING: ACL2 has a single untranslate-preprocess entry.  Another book that
; sets it, for example misc/untranslate-patterns, overrides this one if it is
; included later, and is overridden by this one if it is included earlier.
; Then calls of zq$n print as calls, or the other book's patterns are not
; applied.  Nothing that is proved changes.

(table acl2::user-defined-functions-table
       'acl2::untranslate-preprocess
       'zq-untranslate-preprocess)

;;; The elaborator.  For a term x it returns (mv erp (list new ph pending
;;; events) state), where new is x with quantifiers replaced by calls, ph is x
;;; with quantifiers replaced by placeholders, pending is the alist of
;;; canonical keys to names created so far, and events are the events
;;; creating them, innermost first.

(defun zq-quant-events (name args kind bound body-new key dcls verify-event
                             tbody)

; Tbody is non-nil for a generated function, which is then entered in
; zq-display-table so that its calls print as quantifiers.

  (declare (xargs :mode :program))
  (let ((bvars (if (cdr bound) bound (car bound))))
    `((def::un-skd ,name ,args (,kind ,bvars ,body-new)
        ,@(and dcls `(:witness-dcls ,dcls)))
      ,@(and verify-event (list verify-event))
      (table zq-table ',key '(,name ,args ,kind ,bvars ,body-new ,dcls))
      ,@(and tbody
             `((table zq-display-table ',name
                      '(,args ,kind ,bound ,tbody)))))))

(mutual-recursion
 (defun elab-q (x pending verify ctx wrld state)
   (declare (xargs :mode :program :stobjs state))
   (cond
    ((or (atom x) (eq (car x) 'quote))
     (value (list x x pending nil)))
    ((quant-form-p x)
     (let ((kind (car x))
           (bound (quant-bound-vars x)))
       (er-let* ((r (elab-q (caddr x) pending verify ctx wrld state)))
         (let ((body-new (nth 0 r))
               (body-ph (nth 1 r))
               (pending (nth 2 r))
               (events (nth 3 r)))
           (er-let* ((tbody-ph (acl2::translate body-ph t nil t ctx wrld
                                                state)))
             (let* ((tbody (placeholders-to-calls tbody-ph))
                    (args (set-difference-eq (term-vars-in-order tbody nil)
                                             bound))
                    (key (zq-key kind bound args tbody))
                    (old (zq-lookup key pending verify wrld))
                    (name (or old
                              (zq-fresh-name 'zq$ 1 (strip-cdrs pending)
                                             wrld))))
               (value
                (list (cons name args)
                      `(zq-placeholder ',name (list ,@args))
                      (if old pending (acons key name pending))
                      (cond
                       ((not old)
                        (append events
                                (zq-quant-events
                                 name args kind bound body-new key nil
                                 (and verify `(verify-guards ,name))
                                 tbody)))
                       ((and verify
                             (not (rassoc-eq old pending))
                             (not (eq (acl2::symbol-class old wrld)
                                      :common-lisp-compliant)))
                        (append events `((verify-guards ,old))))
                       (t events))))))))))
    ((zsub-form-p x)
     (er-let* ((p (elab-zsub-parts x pending verify ctx wrld state)))
       (let* ((xv (cadr x))
              (s-new (nth 0 p))
              (phi-new (nth 1 p))
              (ts (nth 2 p))
              (tphi (nth 3 p))
              (pending (nth 4 p))
              (events (nth 5 p))
              (args (set-difference-eq
                     (term-list-vars-in-order (list ts tphi) nil)
                     (list xv)))
              (key (zs-key args xv ts tphi))
              (old (zs-lookup key pending wrld))
              (name (or old
                        (zq-fresh-name 'zs$ 1 (strip-cdrs pending) wrld))))
         (value
          (list (cons name args)
                `(zq-placeholder ',name (list ,@args))
                (if old pending (acons key name pending))
                (if old
                    events
                  (append events
                          `((zsub-define ,name ,args ,xv ,s-new ,phi-new)
                            (table zq-display-table ',name
                                   '(,args :zsub ,xv (,ts ,tphi)))))))))))
    (t (elab-q-lst x pending verify ctx wrld state))))
 (defun elab-zsub-parts (x pending verify ctx wrld state)

   (declare (xargs :mode :program :stobjs state))
   (let ((xv (cadr x)))
     (er-let* ((r1 (elab-q (caddr x) pending verify ctx wrld state))
               (r2 (elab-q (cadddr x) (nth 2 r1) verify ctx wrld state))
               (ts-ph (acl2::translate (nth 1 r1) t nil t ctx wrld state))
               (tphi-ph (acl2::translate (nth 1 r2) t nil t ctx wrld state)))
       (let ((ts (placeholders-to-calls ts-ph))
             (tphi (placeholders-to-calls tphi-ph)))
         (if (member-eq xv (acl2::all-vars ts))
             (er soft ctx
                 "The variable ~x0 of ~x1 occurs free in its set ~x2."
                 xv x (caddr x))
           (value (list (nth 0 r1) (nth 0 r2) ts tphi (nth 2 r2)
                        (append (nth 3 r1) (nth 3 r2)))))))))
 (defun elab-q-lst (x pending verify ctx wrld state)
   (declare (xargs :mode :program :stobjs state))
   (cond
    ((atom x) (value (list x x pending nil)))
    (t (er-let* ((r1 (elab-q (car x) pending verify ctx wrld state))
                 (r2 (elab-q-lst (cdr x) (nth 2 r1) verify ctx wrld
                                 state)))
         (value (list (cons (nth 0 r1) (nth 0 r2))
                      (cons (nth 1 r1) (nth 1 r2))
                      (nth 2 r2)
                      (append (nth 3 r1) (nth 3 r2)))))))))

(defun elab-quantifiers (term verify ctx state)

; Returns (mv erp (cons new-term events) state).

  (declare (xargs :mode :program :stobjs state))
  (er-let* ((r (elab-q term nil verify ctx (w state) state)))
    (value (cons (nth 0 r) (nth 3 r)))))

(mutual-recursion
 (defun zq-has-quantifier (x)
   (declare (xargs :mode :program))
   (cond ((or (atom x) (eq (car x) 'quote)) nil)
         ((quant-form-p x) t)
         ((zsub-form-p x) t)
         (t (zq-has-quantifier-lst x))))
 (defun zq-has-quantifier-lst (x)
   (declare (xargs :mode :program))
   (and (consp x)
        (or (zq-has-quantifier (car x))
            (zq-has-quantifier-lst (cdr x))))))
