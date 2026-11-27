; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Tests of quantifiers.lisp, using the axioms of base.lisp, where subset is
; defined by defunz and in-union is stated with exists.

(in-package "ZF")

(include-book "base")
(include-book "std/testing/must-fail" :dir :system)

;;; What base.lisp produced

; Subset is itself the defun-sk (registered with coi), not a wrapper.
(assert-event (equal (acl2::formals 'subset (w state)) '(x y)))
(assert-event (acl2::getpropc 'subset-necc 'acl2::theorem nil (w state)))

; In-union is stated with a generated function for the exists, in place of
; Matt's in-in.
(assert-event (equal (acl2::formals 'zq$1 (w state)) '(a x)))

;;; Sharing

; A quantifier with the formula of subset, inside another definition, becomes
; a call of subset.
(defunz all-subsets (x y)
  (forall z (implies (in z x)
                     (forall a (implies (in a z) (in a y))))))

(assert-event (equal (acl2::body 'all-subsets-witness nil (w state))
                     nil)) ; constrained, has no body
(assert-event
 (equal (acl2::formula 'all-subsets-necc nil (w state))
        '(implies (not (implies (in z x) (subset z y)))
                  (not (all-subsets x y)))))

; The exists of in-union, inside a definition, becomes a call of zq$1.
(defunz in-union-of-pair-q (a u v)
  (let ((z (pair u v)))
    (exists y (and (in a y) (in y z)))))

(assert-event (equal (acl2::body 'in-union-of-pair-q nil (w state))
                     '((lambda (z a) (zq$1 a z)) (pair u v) a)))

; Several bound variables in one quantifier.
(defunz funp-q (f)
  (forall (p1 p2)
          (implies (and (in p1 f)
                        (in p2 f)
                        (equal (car p1) (car p2)))
                   (equal p1 p2))))

; Nested: forall over exists.  Surjective-q is the forall; the exists is a
; generated function with the outer bound variable y among its arguments.
; (Apply is not yet in the core, so a stub stands in for it.)
(defstub app (f x) t)

(defunz surjective-q (f a b)
  (forall y (implies (in y b)
                     (exists x (and (in x a)
                                    (equal (app f x) y))))))

(assert-event (equal (acl2::formals 'zq$2 (w state)) '(a f y)))

;;; Proofs with only coi's hints

; Transitivity of subset.
(defthmz subset-transitive
  (implies (and (subset x y) (subset y z))
           (subset x z))
  :hints ((quant::skosimp) (quant::inst?))
  :rule-classes nil)

; The same with the subsets written out; they become calls of subset.
(thmz (implies (and (forall a (implies (in a x) (in a y)))
                     (forall a (implies (in a y) (in a z))))
                (forall a (implies (in a x) (in a z))))
       :hints ((quant::skosimp) (quant::inst?)))

; Forall over exists on both sides, with no union.
(thmz (implies (subset x y)
                (forall b (implies (exists u (and (in b u) (in u x)))
                                   (exists v (and (in b v) (in v y))))))
       :hints ((quant::skosimp) (quant::inst?)))

; Monotonicity of union, through the axiom in-union.
(defthmz subset-union
  (implies (subset x y)
           (subset (union x) (union y)))
  :hints ((quant::skosimp) (quant::inst?))
  :rule-classes nil)

;;; The table guard

; The guard refuses entries that do not match the events they name:
;  - a function that is not a defun-sk (union2);
;  - subset paired with the key of another formula (the exists of in-union);
;  - the key and form of the exists of in-union paired with subset;
;  - the key of subset with the arguments swapped.
(acl2::must-fail
 (table zq-table '(forall 1 2 (implies (in zq-b0 zq-f0) (in zq-b0 zq-f1)))
        '(union2 (x y) forall a (implies (in a x) (in a y)) nil)))
(acl2::must-fail
 (table zq-table '(exists 1 2 (if (in zq-f0 zq-b0) (in zq-b0 zq-f1) 'nil))
        '(subset (x y) forall a (implies (in a x) (in a y)) nil)))
(acl2::must-fail
 (table zq-table '(exists 1 2 (if (in zq-f0 zq-b0) (in zq-b0 zq-f1) 'nil))
        '(subset (a x) exists y (and (in a y) (in y x)) nil)))
(acl2::must-fail
 (table zq-table '(forall 1 2 (implies (in zq-b0 zq-f1) (in zq-b0 zq-f0)))
        '(subset (x y) forall a (implies (in a x) (in a y)) nil)))
(acl2::must-fail
 (table zq-table '(forall 1 2 (implies (in zq-b0 zq-f0) (in zq-b0 zq-f1)))
        '(subset (x y) forall a (implies (in a x) (in a y))
                 ((declare (xargs :guard (consp x)))))))

; A correct entry is accepted (it is already present, so this is a no-op).
(table zq-table '(forall 1 2 (implies (in zq-b0 zq-f0) (in zq-b0 zq-f1)))
       '(subset (x y) forall a (implies (in a x) (in a y)) nil))

;;; Display: generated functions print as the quantifiers they stand for

; Zq$1 is the exists of in-union.
(assert-event
 (equal (zq-untranslate-preprocess '(zq$1 a x) (w state))
        '(exists y (if (in a y) (in y x) 'nil))))

; The bound variable y is renamed, since it occurs in the arguments.
(assert-event
 (equal (zq-untranslate-preprocess '(zq$1 a y) (w state))
        '(exists y1 (if (in a y1) (in y1 y) 'nil))))

; Nested: surjective-q's inner exists, inside a term.
(assert-event
 (equal (zq-untranslate-preprocess '(not (zq$2 a f x)) (w state))
        '(not (exists x1 (if (in x1 a) (equal (app f x1) x) 'nil)))))

; Functions defined with defunz are not affected.
(assert-event
 (equal (zq-untranslate-preprocess '(subset x y) (w state)) nil))

; The display table refuses an entry that would print a call as a formula the
; function does not mean: zq$1 shown as a forall.
(acl2::must-fail
 (table zq-display-table 'zq$1
        '((a x) forall (y) (if (in a y) (in y x) 'nil))))

;;; A later function with the same formula replaces the earlier one in
;;; zq-table (with a warning), so later quantifiers become calls of it.

(defunz subset2 (s u)
  (forall b (implies (in b s) (in b u))))

(assert-event
 (equal (zq-lookup '(forall 1 2 (implies (in zq-b0 zq-f0) (in zq-b0 zq-f1)))
                   nil nil (w state))
        'subset2))

(defunz all-subsets2 (x y)
  (forall z (implies (in z x)
                     (forall a (implies (in a z) (in a y))))))

(assert-event
 (equal (acl2::formula 'all-subsets2-necc nil (w state))
        '(implies (not (implies (in z x) (subset2 z y)))
                  (not (all-subsets2 x y)))))

;;; Guards

(defunz nth-has (n x)
  (declare (xargs :guard (and (natp n) (true-listp x))))
  (exists y (in y (nth n x))))

(assert-event
 (eq (acl2::symbol-class 'nth-has (w state)) :common-lisp-compliant))

(defunz transitive-q (x)
  (declare (xargs :guard t :verify-guards t))
  (forall a (implies (in a x)
                     (forall b (implies (in b a) (in b x))))))

(assert-event
 (let* ((wrld (w state))
        (q (car (caddr (cadr (cadr (acl2::formula 'transitive-q-necc nil
                                                     wrld)))))))
   (and (eq (acl2::symbol-class 'transitive-q wrld) :common-lisp-compliant)
        (eq (acl2::symbol-class q wrld) :common-lisp-compliant))))

(defunz nonempty-consp (x)
  (declare (xargs :guard (consp x)))
  (exists y (in y x)))

(defunz empty-q (x)
  (declare (xargs :guard t :verify-guards t))
  (not (exists y (in y x))))

(assert-event
 (and (not (equal (acl2::body 'empty-q nil (w state))
                  '(not (nonempty-consp x))))
      (eq (acl2::symbol-class 'empty-q (w state)) :common-lisp-compliant)))

(defunz closed-1 ()
  (not (forall x (exists y (in y x)))))

(defunz closed-2 ()
  (not (exists x (forall y (in y x)))))

(assert-event
 (not (equal (acl2::body 'closed-1 nil (w state))
             (acl2::body 'closed-2 nil (w state)))))

(defthmdz subset-union-elements
  (implies (subset x y)
           (forall b (implies (exists u (and (in b u) (in u x)))
                              (exists v (and (in b v) (in v y))))))
  :hints ((quant::skosimp) (quant::inst?)))

(assert-event
 (not (acl2::enabled-runep '(:rewrite subset-union-elements)
                          (acl2::ens state) (w state))))
