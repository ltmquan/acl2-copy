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
(thmzq (implies (and (forall a (implies (in a x) (in a y)))
                     (forall a (implies (in a y) (in a z))))
                (forall a (implies (in a x) (in a z))))
       :hints ((quant::skosimp) (quant::inst?)))

; Forall over exists on both sides, with no union.
(thmzq (implies (subset x y)
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
        '(union2 (x y) forall a (implies (in a x) (in a y)))))
(acl2::must-fail
 (table zq-table '(exists 1 2 (if (in zq-f0 zq-b0) (in zq-b0 zq-f1) 'nil))
        '(subset (x y) forall a (implies (in a x) (in a y)))))
(acl2::must-fail
 (table zq-table '(exists 1 2 (if (in zq-f0 zq-b0) (in zq-b0 zq-f1) 'nil))
        '(subset (a x) exists y (and (in a y) (in y x)))))
(acl2::must-fail
 (table zq-table '(forall 1 2 (implies (in zq-b0 zq-f1) (in zq-b0 zq-f0)))
        '(subset (x y) forall a (implies (in a x) (in a y)))))

; A correct entry is accepted (it is already present, so this is a no-op).
(table zq-table '(forall 1 2 (implies (in zq-b0 zq-f0) (in zq-b0 zq-f1)))
       '(subset (x y) forall a (implies (in a x) (in a y))))
