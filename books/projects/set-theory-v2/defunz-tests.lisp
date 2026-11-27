; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "base")
(include-book "std/testing/must-fail" :dir :system)

;;; Defun-sk options when the body is a quantifier at the top

(defunz rel-p (r)
  (declare (xargs :guard t))
  (forall p (implies (in p r) (consp p)))
  :rewrite :direct)

(assert-event
 (equal (acl2::formula 'rel-p-necc nil (w state))
        '(implies (rel-p r)
                  (implies (in p r) (consp p)))))

(defunz has-elt (x)
  (exists y (in y x))
  :skolem-name has-elt-choose
  :thm-name has-elt-intro)

(assert-event (acl2::function-symbolp 'has-elt-choose (w state)))
(assert-event (acl2::getpropc 'has-elt-intro 'acl2::theorem nil (w state)))

(acl2::must-fail
 (defunz bad-option (x)
   (exists y (in y x))
   :measure (acl2-count x)))

;;; Defundz

(defundz pair-self (x)
  (pair x x))

(assert-event
 (not (acl2::enabled-runep '(:definition pair-self)
                           (acl2::ens state) (w state))))

;;; Recursion inside a quantifier is refused

(acl2::must-fail
 (defunz all-below (x n)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       t
     (forall y (implies (in y x) (all-below y (1- n)))))))

;;; Declarations when the body is a set-builder at the top

(defunz inter-guarded (a b)
  (declare (xargs :guard (consp a)))
  (zsub x a (in x b)))

(assert-event (equal (acl2::formals 'inter-guarded (w state)) '(a b)))
(assert-event (equal (acl2::getpropc 'inter-guarded 'acl2::guard nil
                                     (w state))
                     '(consp a)))

(defun uses-inter-guarded (a b)
  (declare (xargs :guard (consp a) :verify-guards t))
  (inter-guarded a b))

(acl2::must-fail
 (defun uses-inter-guarded-bad (a b)
   (declare (xargs :guard t :verify-guards t))
   (inter-guarded a b)))

(defunz pairs-of (n a)
  (declare (type (integer 0 *) n))
  (zimg x a (pair x n)))

(assert-event (equal (acl2::formals 'pairs-of (w state)) '(n a)))
(assert-event
 (equal (acl2::getpropc 'pairs-of 'acl2::guard nil (w state))
        '(if (integerp n) (not (< n '0)) 'nil)))

(acl2::must-fail
 (defunz inter-ignoring (a b)
   (declare (ignore b))
   (zsub x a t)))

;;; Mutual recursion

(mutual-recursionz
 (defunz even-has-elt (x n)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (exists y (in y x))
     (odd-has-elt x (1- n))))
 (defundz odd-has-elt (x n)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (not (exists y (in y x)))
     (even-has-elt x (1- n)))))

(assert-event
 (let ((wrld (w state)))
   (equal (caddr (acl2::body 'even-has-elt nil wrld))
          (cadr (caddr (acl2::body 'odd-has-elt nil wrld))))))

(assert-event
 (not (acl2::enabled-runep '(:definition odd-has-elt)
                           (acl2::ens state) (w state))))

(acl2::must-fail
 (mutual-recursionz
  (defunz f1 (x n)
    (declare (xargs :measure (nfix n)))
    (if (zp n) t (forall y (implies (in y x) (f2 y (1- n))))))
  (defunz f2 (x n)
    (declare (xargs :measure (nfix n)))
    (if (zp n) t (f1 x (1- n))))))
