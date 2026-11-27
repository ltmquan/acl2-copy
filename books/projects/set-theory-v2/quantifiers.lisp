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
; is a single quantifier, such as subset, is entered in the table too, so a
; later quantifier with the same formula becomes a call of it.  The table
; guard checks every entry against the event that introduced its function.
;
; The generated functions are introduced with def::un-skd from
; coi/quantification: a defun-sk, disabled, with coi's rules and registration,
; so that the hints quant::inst? and quant::skosimp can instantiate and
; skolemize them automatically.

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

(defun zq-fresh-name (n taken wrld)

; The first zq$n, n >= 1, that is not already a function or macro, nor among
; the names taken by the current elaboration.

  (declare (xargs :mode :program))
  (let ((name (packn (list 'zq$ n))))
    (if (or (member-eq name taken)
            (getpropc name 'acl2::formals nil wrld)
            (getpropc name 'acl2::macro-args nil wrld))
        (zq-fresh-name (1+ n) taken wrld)
      name)))

;;; The table guard.  As zfc-table-guard in base.lisp checks that an entry
;;; names the event that its macro would produce, an entry
;;;
;;;   key -> (name args kind bvars body)
;;;
;;; is accepted only if
;;;
;;;   - key is the canonical key of the formula (kind bvars body) with
;;;     arguments args, recomputed here from the translation of body, and
;;;   - the event that introduced name-witness is exactly the encapsulate that
;;;     (def::un-skd name args (kind bvars body)) produces through defun-sk.
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

(defun zq-witness-event (name args kind bvars body)

; The encapsulate introducing name-witness that def::un-skd produces.

  (declare (xargs :mode :program))
  (let* ((witness (acl2::add-suffix name "-WITNESS"))
         (thm (acl2::add-suffix name (if (eq kind 'exists) "-SUFF" "-NECC")))
         (rest `((,kind ,bvars ,body) :skolem-name ,witness :thm-name ,thm)))
    (find-witness-encapsulate
     witness
     (strip-with-output
      (acl2::defun-sk-fn `(defun-sk ,name ,args ,@rest) name args rest)))))

(defun zq-table-guard (key val wrld)
  (declare (xargs :mode :program)) ; because of get-event
  (case-match val
    ((name args kind bvars body)
     (and (symbolp name)
          name
          (symbol-listp args)
          (no-duplicatesp-eq args)
          (member-eq kind '(forall exists))
          (or (and (symbolp bvars) bvars)
              (and (symbol-listp bvars) (consp bvars)))
          (let ((bound (if (symbolp bvars) (list bvars) bvars)))
            (mv-let (erp tbody)
              (acl2::translate-cmp body t nil t 'zq-table-guard wrld
                                   (acl2::default-state-vars nil))
              (and (not erp)
                   (equal key (zq-key kind bound args tbody))
                   (equal (zq-witness-event name args kind bvars body)
                          (get-event (acl2::add-suffix name "-WITNESS")
                                     wrld)))))))
    (& nil)))

(table zq-table nil nil
       :guard (acl2::strict-table-guard (zq-table-guard key val world)))

(defun zq-lookup (key pending wrld)
  (declare (xargs :mode :program))
  (or (cdr (assoc-equal key pending))
      (car (cdr (assoc-equal key (table-alist 'zq-table wrld))))))

;;; Display.  Generated functions should not show in proof output: a call
;;; (zq$n a1 ... ak) is printed as the quantified formula it stands for, with
;;; the arguments substituted.  Zq-display-table maps each generated function
;;; to (formals kind bound tbody).  This affects printing only (see :DOC
;;; user-defined-functions-table), not what is proved.
;;;
;;; A bound variable is renamed when it occurs in the arguments, so that it
;;; does not capture them: (zq$1 a y), where zq$1 is (exists y (and (in a y)
;;; (in y x))), prints as (exists y1 (and (in a y1) (in y1 y))).

(defun zq-display-guard (key val wrld)

; An entry name -> (formals kind bound tbody) is accepted only if zq-table,
; whose entries are checked against their events, has an entry for name with
; these formals and with the key of (kind bound formals tbody).  So a call of
; name prints as the formula that name means.

  (declare (xargs :mode :program))
  (case-match val
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
                  (bound (nth 2 entry))
                  (tbody (nth 3 entry))
                  (ren (zq-fresh-vars bound
                                      (acl2::all-vars1-lst (cdr term) nil)))
                  (body (acl2::sublis-var
                         (append ren (pairlis$ formals (cdr term)))
                         tbody))
                  (vars (strip-cdrs ren)))
             (list kind
                   (if (cdr vars) vars (car vars))
                   (zq-display-term body tbl)))
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

(table acl2::user-defined-functions-table
       'acl2::untranslate-preprocess
       'zq-untranslate-preprocess)

;;; The elaborator.  For a term x it returns (mv erp (list new ph pending
;;; events) state), where new is x with quantifiers replaced by calls, ph is x
;;; with quantifiers replaced by placeholders, pending is the alist of
;;; canonical keys to names created so far, and events are the events
;;; creating them, innermost first.

(defun zq-quant-events (name args kind bound body-new key tbody)

; Tbody is non-nil for a generated function, which is then entered in
; zq-display-table so that its calls print as quantifiers.

  (declare (xargs :mode :program))
  (let ((bvars (if (cdr bound) bound (car bound))))
    `((def::un-skd ,name ,args (,kind ,bvars ,body-new))
      (table zq-table ',key '(,name ,args ,kind ,bvars ,body-new))
      ,@(and tbody
             `((table zq-display-table ',name
                      '(,args ,kind ,bound ,tbody)))))))

(mutual-recursion
 (defun elab-q (x pending ctx wrld state)
   (declare (xargs :mode :program :stobjs state))
   (cond
    ((or (atom x) (eq (car x) 'quote))
     (value (list x x pending nil)))
    ((quant-form-p x)
     (let ((kind (car x))
           (bound (quant-bound-vars x)))
       (er-let* ((r (elab-q (caddr x) pending ctx wrld state)))
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
                    (old (zq-lookup key pending wrld))
                    (name (or old
                              (zq-fresh-name 1 (strip-cdrs pending) wrld))))
               (value (list (cons name args)
                            `(zq-placeholder ',name (list ,@args))
                            (if old pending (acons key name pending))
                            (if old
                                events
                              (append events
                                      (zq-quant-events name args kind bound
                                                       body-new key tbody)))))))))))
    (t (elab-q-lst x pending ctx wrld state))))
 (defun elab-q-lst (x pending ctx wrld state)
   (declare (xargs :mode :program :stobjs state))
   (cond
    ((atom x) (value (list x x pending nil)))
    (t (er-let* ((r1 (elab-q (car x) pending ctx wrld state))
                 (r2 (elab-q-lst (cdr x) (nth 2 r1) ctx wrld state)))
         (value (list (cons (nth 0 r1) (nth 0 r2))
                      (cons (nth 1 r1) (nth 1 r2))
                      (nth 2 r2)
                      (append (nth 3 r1) (nth 3 r2)))))))))

(defun elab-quantifiers (term ctx state)

; Returns (mv erp (cons new-term events) state).

  (declare (xargs :mode :program :stobjs state))
  (er-let* ((r (elab-q term nil ctx (w state) state)))
    (value (cons (nth 0 r) (nth 3 r)))))

(defun defunz-events (name args dcls body ctx state)

; If body is a single quantifier, name itself is the defun-sk (with def::un-skd,
; so it is registered with coi), and it is entered in zq-table unless its
; formula is already there.  Otherwise name is defined by defun, with the
; quantifiers in body elaborated.

  (declare (xargs :mode :program :stobjs state))
  (let ((wrld (w state)))
    (cond
     ((quant-form-p body)
      (let ((kind (car body))
            (bound (quant-bound-vars body)))
        (cond
         (dcls (er soft ctx
                   "Declarations are not supported when the body is a ~
                    quantifier, as for ~x0."
                   name))
         (t
          (er-let* ((r (elab-q (caddr body) nil ctx wrld state)))
            (let ((body-new (nth 0 r))
                  (body-ph (nth 1 r))
                  (events (nth 3 r)))
              (er-let* ((tbody-ph (acl2::translate body-ph t nil t ctx wrld
                                                   state)))
                (let* ((key (zq-key kind bound args
                                    (placeholders-to-calls tbody-ph)))
                       (q-events (zq-quant-events name args kind bound
                                                  body-new key nil)))
                  (value (append events
                                 (if (zq-lookup key (nth 2 r) wrld)
                                     (list (car q-events))
                                   q-events)))))))))))
     (t
      (er-let* ((pr (elab-quantifiers body ctx state)))
        (value (append (cdr pr)
                       `((defun ,name ,args ,@dcls ,(car pr))))))))))

;;; Macros using it (names provisional)

(defmacro defunz (name args &rest rest)

; (defunz name args dcl ... dcl body)

  `(make-event
    (er-let* ((evs (defunz-events ',name ',args ',(butlast rest 1)
                     ',(car (last rest)) 'defunz state)))
      (value (cons 'progn evs)))))

(defmacro defthmzq (name term &rest args)
  `(make-event
    (er-let* ((pr (elab-quantifiers ',term 'defthmzq state)))
      (value `(progn ,@(cdr pr)
                     (defthmz ,',name ,(car pr) ,@',args))))))

(defmacro defthmdzq (name term &rest args)
  `(make-event
    (er-let* ((pr (elab-quantifiers ',term 'defthmdzq state)))
      (value `(progn ,@(cdr pr)
                     (defthmdz ,',name ,(car pr) ,@',args))))))

(defmacro thmzq (term &rest args)
  `(make-event
    (er-let* ((pr (elab-quantifiers ',term 'thmzq state)))
      (value `(progn ,@(cdr pr)
                     (thmz ,(car pr) ,@',args))))))
