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
; neutral names, zq$1, zq$2, ....
;
; The generated functions are introduced with def::un-skd from
; coi/quantification: a defun-sk, disabled, with coi's rules and registration,
; so that the hints quant::inst? and quant::skosimp can instantiate and
; skolemize them automatically.

(in-package "ZF")

(include-book "base")
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
  (declare (xargs :mode :program))
  (let ((alist (append (zq-canonical-vars 'zq-f 0 args)
                       (zq-canonical-vars 'zq-b 0 bound))))
    (list kind (len bound) (acl2::sublis-var alist tbody))))

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

(table zq-table nil nil)

;;; The elaborator.  For a term x it returns (mv erp (list new ph pending
;;; events) state), where new is x with quantifiers replaced by calls, ph is x
;;; with quantifiers replaced by placeholders (cons 'name (list args ...))
;;; that translate and preserve the variables, pending is the alist of
;;; canonical keys to names created so far, and events are the events
;;; creating them, innermost first.

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
           (er-let* ((tbody (acl2::translate body-ph t nil t ctx wrld state)))
             (let* ((args (set-difference-eq (term-vars-in-order tbody nil)
                                             bound))
                    (key (zq-key kind bound args tbody))
                    (old (or (cdr (assoc-equal key pending))
                             (cdr (assoc-equal key
                                               (table-alist 'zq-table wrld)))))
                    (name (or old
                              (zq-fresh-name 1 (strip-cdrs pending) wrld)))
                    (new-events
                     (and (not old)
                          `((def::un-skd ,name ,args
                              (,kind ,(if (cdr bound) bound (car bound))
                                     ,body-new))
                            (table zq-table ',key ',name)))))
               (value (list (cons name args)
                            `(cons ',name (list ,@args))
                            (if old pending (acons key name pending))
                            (append events new-events)))))))))
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

;;; Macros using it (names provisional)

(defmacro defunz (name args body)
  `(make-event
    (er-let* ((pr (elab-quantifiers ',body 'defunz state)))
      (value `(progn ,@(cdr pr)
                     (defun ,',name ,',args ,(car pr)))))))

(defmacro defthmzq (name term &rest args)
  `(make-event
    (er-let* ((pr (elab-quantifiers ',term 'defthmzq state)))
      (value `(progn ,@(cdr pr)
                     (defthmz ,',name ,(car pr) ,@',args))))))

(defmacro thmzq (term &rest args)
  `(make-event
    (er-let* ((pr (elab-quantifiers ',term 'thmzq state)))
      (value `(progn ,@(cdr pr)
                     (thmz ,(car pr) ,@',args))))))

;;; Tests

; One exists: the meaning of union, without in-in.  The proof relates the
; generated function to in-in by their witnesses; the rule package to come
; should make such hints unnecessary.
(defthmzq in-union-q
  (equal (in a (union x))
         (exists y (and (in a y) (in y x))))
  :hints (("Goal"
           :in-theory (enable zq$1)
           :use ((:instance in-in-suff (y (zq$1-witness a x)))
                 (:instance zq$1-suff (y (in-in-witness a x)))))))

; One forall.
(defunz subset-q (x y)
  (forall a (implies (in a x) (in a y))))

; Same formula up to renaming of variables: shares the generated function.
(defunz subset-q2 (s u)
  (forall b (implies (in b s) (in b u))))

(assert-event (equal (acl2::body 'subset-q nil (w state))
                     '(zq$2 x y)))
(assert-event (equal (acl2::body 'subset-q2 nil (w state))
                     '(zq$2 s u)))

; Several bound variables in one quantifier.
(defunz funp-q (f)
  (forall (p1 p2)
          (implies (and (in p1 f)
                        (in p2 f)
                        (equal (car p1) (car p2)))
                   (equal p1 p2))))

; Nested: forall over exists, so two generated functions; the inner one has
; the outer bound variable y among its arguments.  (Apply is not yet in the
; core, so a stub stands in for it.)
(defstub app (f x) t)

(defunz surjective-q (f a b)
  (forall y (implies (in y b)
                     (exists x (and (in x a)
                                    (equal (app f x) y))))))

(assert-event (equal (acl2::body 'surjective-q nil (w state))
                     '(zq$5 b a f)))
(assert-event (equal (acl2::formals 'zq$4 (w state)) '(a f y)))
(assert-event (equal (acl2::formals 'zq$5 (w state)) '(b a f)))

; A quantifier under let: the let-bound variable is an argument.
(defunz in-union-of-pair-q (a u v)
  (let ((z (pair u v)))
    (exists y (and (in a y) (in y z)))))

; Shares zq$1 with in-union-q, since the exists is the same up to renaming.
(assert-event (equal (acl2::body 'in-union-of-pair-q nil (w state))
                     '((lambda (z a) (zq$1 a z)) (pair u v) a)))

;;; Experiments: quantified theorems written with forall and exists directly,
;;; nested, proved with only coi's hints.

; T1
(thmzq (forall a (implies (in a x) (in a x)))
       :hints ((quant::skosimp) (quant::inst?)))

; T2: transitivity of subset, with the subsets written as quantifiers.
(thmzq (implies (and (forall a (implies (in a x) (in a y)))
                     (forall a (implies (in a y) (in a z))))
                (forall a (implies (in a x) (in a z))))
       :hints ((quant::skosimp) (quant::inst?)))

; T3: forall over exists on both sides, with no union.
(thmzq (implies (forall a (implies (in a x) (in a y)))
                (forall b (implies (exists u (and (in b u) (in u x)))
                                   (exists v (and (in b v) (in v y))))))
       :hints ((quant::skosimp) (quant::inst?)))

; T3 with union, through in-union-q.
(thmzq (implies (forall a (implies (in a x) (in a y)))
                (forall b (implies (in b (union x)) (in b (union y)))))
       :hints ((quant::skosimp) (quant::inst?)))
