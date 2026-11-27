; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "base")
(include-book "std/testing/must-fail" :dir :system)

;;; Definitions with a zsub at the top

(defunz inter (a b)
  (zsub x a (in x b)))

(assert-event (equal (len (acl2::formals 'inter (w state))) 2))
(assert-event (acl2::getpropc 'inter$comprehension 'acl2::theorem nil
                              (w state)))
(assert-event (assoc-eq 'inter$prop (table-alist 'zfc-table (w state))))

; The props of a theorem are found from its functions: inter$prop here.
(defthmz in-inter
  (equal (in z (inter a b))
         (and (in z a) (in z b))))

(assert-event
 (equal (acl2::formula 'in-inter nil (w state))
        '(implies (if (force (zfc)) (force (inter$prop)) 'nil)
                  (equal (in z (inter a b))
                         (if (in z a) (in z b) 'nil)))))

(defunz diff (a b)
  (zsub x a (not (in x b))))

; A quantifier in the condition.
(defunz big-inter (f)
  (zsub x (union f)
        (forall y (implies (in y f) (in x y)))))

(defthmz in-big-inter
  (implies (and (in z (big-inter f))
                (in y f))
           (in z y))
  :hints ((quant::skosimp) (quant::inst?)))

;;; Set-builders inside formulas

; A set-builder with the formula of inter becomes a call of inter.
(defthmz zsub-is-inter
  (equal (zsub y u (in y v))
         (inter u v))
  :rule-classes nil)

(assert-event
 (equal (acl2::formula 'zsub-is-inter nil (w state))
        '(implies (if (force (zfc)) (force (inter$prop)) 'nil)
                  (equal (inter u v) (inter u v)))))

; A new set-builder gets a generated function and its prop.
(defthmz in-zsub-pair
  (equal (in z (zsub x (pair a b) (in x c)))
         (and (or (equal z a) (equal z b))
              (in z c))))

(assert-event
 (let ((hyps (cadr (acl2::formula 'in-zsub-pair nil (w state)))))
   (and (equal (car hyps) 'if)
        (equal (cadr hyps) '(force (zfc)))
        (equal (car (caddr hyps)) 'force))))

; The props of functions defined from sets are found through definitions.
(defunz self-inter (a)
  (inter a a))

(defthmz self-inter-is-identity
  (equal (in z (self-inter a))
         (in z a)))

(assert-event
 (acl2::member-equal '(force (inter$prop))
                     (acl2::flatten-ands-in-lit
                      (cadr (acl2::formula 'self-inter-is-identity nil
                                           (w state))))))

; Nested: a set-builder whose set is a set-builder.
(defthmz in-nested-zsub
  (equal (in z (zsub x (zsub y a (in y b)) (not (in x c))))
         (and (in z a) (in z b) (not (in z c)))))

;;; Display

(assert-event
 (let* ((wrld (w state))
        (name (zs-lookup (zs-key '(a b c) 'x '(pair a b) '(in x c)) nil wrld)))
   (equal (zq-untranslate-preprocess (list name 'p 'q 'x) wrld)
          '(zsub x1 (pair p q) (in x1 x)))))

;;; Errors and the table guard

; The variable of a set-builder must not occur free in its set.
(acl2::must-fail
 (thmz (equal (zsub x (pair x x) (in x c)) 0)))

; Zfc-table refuses an entry that does not name the event zsub-define makes.
(acl2::must-fail
 (table zfc-table 'inter$prop '(zsub inter (a b) x a (not (in x b)))))
