; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "base")
(include-book "std/testing/must-fail" :dir :system)

;;; Definitions with a zimg at the top

(defunz singletons (a)
  (zimg x a (pair x x)))

(assert-event (acl2::getpropc 'singletons$replacement 'acl2::theorem nil
                              (w state)))
(assert-event (acl2::getpropc 'singletons$member 'acl2::theorem nil
                              (w state)))
(assert-event (assoc-eq 'singletons$prop (table-alist 'zfc-table (w state))))

(defthmz singleton-in-singletons
  (implies (in z a)
           (in (pair z z) (singletons a))))

(assert-event
 (acl2::member-equal '(force (singletons$prop))
                     (acl2::flatten-ands-in-lit
                      (cadr (acl2::formula 'singleton-in-singletons nil
                                           (w state))))))

(defthmz in-singletons-elim
  (implies (in y (singletons a))
           (exists x (and (in x a) (equal y (pair x x)))))
  :hints (("Goal" :in-theory (enable singletons$replacement))
          (quant::skosimp) (quant::inst?)))

; A function as a set: its graph.
(defunz singleton-graph (a)
  (zimg x a (cons x (pair x x))))

(defthmz pair-in-singleton-graph
  (implies (in z a)
           (in (cons z (pair z z)) (singleton-graph a))))

;;; Images inside formulas

; An image with the formula of singletons becomes a call of singletons.
(defthmz zimg-is-singletons
  (equal (zimg u b (pair u u))
         (singletons b))
  :rule-classes nil)

(assert-event
 (equal (acl2::formula 'zimg-is-singletons nil (w state))
        '(implies (if (force (zfc)) (force (singletons$prop)) 'nil)
                  (equal (singletons b) (singletons b)))))

; A new image gets a generated function and its prop.
(defthmz pair-in-pairs
  (implies (in z a)
           (in (pair z c) (zimg w a (pair w c)))))

; An image inside a set-builder.
(defthmz pair-in-zsub-of-zimg
  (implies (and (in z a) (in (pair z z) b))
           (in (pair z z)
               (zsub v (zimg w a (pair w w)) (in v b)))))

;;; Display

(assert-event
 (let* ((wrld (w state))
        (name (zs-lookup (zs-key :zimg '(a c) 'w 'a '(pair w c)) nil wrld)))
   (equal (zq-untranslate-preprocess (list name 'p 'w) wrld)
          '(zimg acl2::w1 p (pair acl2::w1 w)))))

;;; Errors and the table guard

(acl2::must-fail
 (thmz (equal (zimg x (pair x x) (pair x x)) 0)))

(acl2::must-fail
 (table zfc-table 'singletons$prop '(zimg singletons (a) x a (cons x x))))
