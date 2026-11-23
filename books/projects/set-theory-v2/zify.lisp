; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

; This book introduces zify and zify*, macros that create a set-theoretic
; function corresponding to a given ACL2 function.

; The difference between zify and zify* is that zify creates a set-theoretic
; function that corresponds directly to a unary ACL2 function, while zify* does
; this for any ACL2 function, unary or not, by creating a set-theoretic
; function whose domain corresponds to the set of arglists of the given ACL2
; function.

; See zify-motivation.lisp for an example that was created to motivate the
; development of zify.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The set ACL2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "prove-acl2p")

; We often want a function to have domain and codomain (set containing the
; image) that consist of all ACL2 objects.  We start by defining that set.

(zsub acl2 ()   ; name, args
      x         ; x
      (v-omega) ; s
      (acl2p x) ; u
      )

; Zify-prop will be useful in our applications of zify.  We introduce it now
; because it's also useful for lemma acl2p-is-acl2 below.
(extend-zfc-table zify-prop
                  prod2$prop domain$prop inverse$prop zfc)

(defthmz acl2p-is-acl2
  (equal (in x (acl2))
         (acl2p x))
  :props (zify-prop acl2$prop v$prop))

(in-theory (disable acl2$comprehension))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Zify
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Zify is built on zfn (Replacement), not zsub (Separation) as the original
; zify in projects/set-theory is.  Zfn builds (NAME ...) from dom and fn alone,
; so a codomain is needed only for subset-image-NAME.  The generic events below
; follow zfn's constraint names, with (zify-prop) added as a hypothesis, just
; as the original zify's generic-rel$comprehension adds it to zsub's
; NAME$comprehension.

(encapsulate
  (((generic-prop) => *)
   ((generic-dom) => *)
   ((generic-rel) => *)
   ((generic-fn *) => *))
  (local (defun generic-prop () nil))
  (local (defun generic-dom () 0))
  (local (defun generic-rel () 0))
  (local (defun generic-fn (x) x))
  (defthm generic-rel$funp
    (funp (generic-rel)))
  (defthmz generic-rel$domain-1
    (implies (force (domain$prop))
             (subset (domain (generic-rel))
		     (generic-dom))))
  (defthm generic-rel$domain-2
    (implies (and (in x (generic-dom))
		  (force (generic-prop))
		  (force (zify-prop)))
             (in x (domain (generic-rel)))))
  (defthm generic-rel$chooses
    (implies (and (equal (apply (generic-rel) x) y)
		  (in x (domain (generic-rel)))
		  (force (generic-prop))
		  (force (zify-prop)))
             (equal (equal y (generic-fn x)) t))))

(defthm apply-generic-rel
  (implies (and (in x (generic-dom))
                (force (generic-prop))
                (force (zify-prop)))
           (equal (apply (generic-rel) x)
                  (generic-fn x))))

(defthm domain-of-generic-fn-is-generic-dom
  (implies (and (force (generic-prop))
		(force (zify-prop)))
           (equal (domain (generic-rel))
		  (generic-dom)))
  :hints (("Goal" :in-theory (enable extensionality-rewrite subset))))

(defthm in-generic-rel
  (implies (and (force (zify-prop))
		(generic-prop))
           (equal (in p (generic-rel))
		  (and (consp p)
		       (in (car p) (generic-dom))
		       (equal (cdr p) (generic-fn (car p))))))
  :hints (("Goal" :use ((:instance apply-intro
				   (f (generic-rel)))))))

(encapsulate
  (((generic-ran) => *))
  (local (defun generic-ran () (image (generic-rel))))
  (defthm generic-image-is-image
    (implies (and (in x (generic-dom))
		  (generic-prop)
		  (force (zify-prop)))
             (in (generic-fn x) (generic-ran)))
    :hints (("Goal" :use ((:instance in-apply-image (r (generic-rel))))))))

;; this is the same as generic-image-is-image, but works better for the next theorem
(defthm in-generic-ran
  (implies (and (equal y (generic-fn x))
		(in x (generic-dom))
		(generic-prop)
		(force (zify-prop)))
           (in y (generic-ran))))

(defthm subset-image-generic-rel-generic-ran
  (implies (and (force (generic-prop))
		(force (zify-prop)))
           (subset (image (generic-rel))
		   (generic-ran)))
  :hints (("Goal" :in-theory (enable subset in-image-rewrite))))

;; in-generic-rel in the form of zsub's NAME$comprehension, as used by the
;; original zify, for when a codomain is given: the pair is in the product of
;; the domain and codomain.
(defthm in-generic-rel-with-ran
  (implies (and (force (generic-prop))
                (force (zify-prop)))
           (equal (in p (generic-rel))
                  (and (in p (prod2 (generic-dom) (generic-ran)))
                       (equal (cdr p) (generic-fn (car p)))))))

(defun check-arity-fn (fn arity ctx state)
  (declare (xargs :stobjs state
                  :guard (and (posp arity)
                              (error1-state-p state))))
  (cond ((and (symbolp fn)
              (= (len (getpropc fn 'formals nil (w state)))
                 arity))
         (value t))
        (t (er soft ctx
               "~x0 must be a function symbol of arity ~x1 in this context, ~
                but it is not."
               fn arity))))

(defmacro check-arity (x arity)
  `(with-output
     :off (error summary)
     :stack :push
     (make-event
      (er-progn (with-output
                 :stack :pop
                 (check-arity-fn ',x ,arity 'check-arity state))
                (value '(value-triple nil)))
      :on-behalf-of :quiet
      :check-expansion t
      :expansion? (value-triple nil))))

(defun check-zify-fn (name fn dom ran props xhyps all-args var ctx state)
  (declare (xargs :stobjs state :guard (error1-state-p state))
           (ignore dom ran))
  (cond
   ((not (symbolp name))
    (er soft ctx
        "The first argument of ~x0 must be a symbol, but ~x1 is not."
        'zify name))
   ((not (or (symbolp fn)
             (and (symbol-listp fn)
                  (no-duplicatesp (cdr fn) :test 'eq))))
    (er soft ctx
        "The second argument of ~x0 must be a symbol or of the form (f v1 ... ~
         vk) where f and each vi are symbols and the vi are pairwise ~
         distinct, but ~x1 does not have this form."
        'zify fn))
   ((not (and (symbol-listp all-args)
              (no-duplicatesp all-args :test 'eq)))
    (er soft ctx
        "The arguments supplied to ~x0 (appending the cdr of the new ~
         function's arguments when that argument is a list to the value of ~
         the :args keyword) must be a duplicates-free true list of symbols, ~
         but ~x1 is not."
        'zify all-args))
   ((not (symbol-listp props))
    (er soft ctx
        "The value of the :props keyword of ~x0 must be a true list of ~
         symbols, but ~x1 is not."
        'zify props))
   ((not (true-listp xhyps))
    (er soft ctx
        "The :xhyps value of ~x0 is ~x1, which is illegal since it must be a ~
         true-list."
        'zify xhyps))
   ((or (not (symbolp var))
        (member-eq var all-args))
    (er soft ctx
        "The :var value of ~x0 (default ~x1) must be a symbol that is ~
         disjoint from the arguments (both the second argument's cdr when ~
         that argument is a list and the value of the :args keyword)."
        'zify 'p))
   (t (value nil))))

(defmacro check-zify (name fn dom ran props xhyps all-args var)
  `(make-event
    (er-progn (check-zify-fn ',name ',fn ',dom ',ran ',props ',xhyps ',all-args
                             ',var 'zify state)
              (value '(value-triple nil)))
    :on-behalf-of :quiet
    :check-expansion t
    :expansion? (value-triple nil)))

(defun zify-fn (name fn dom ran props xhyps args var verbose)
  (declare (xargs :guard t))
  (let* ((name0 name)
         (name (and (symbolp name)
                    name))
         (props0 props)
         (props (and (true-listp props)
                     props))
         (props (if (null dom)
                    (append '(v$prop acl2$prop) props)
                  props))
         (fn-args (cond ((symbolp fn)
                         (list (suffix-symbol "-ARG" fn)))
                        ((symbol-listp fn)
                         (cdr fn))
                        (t ; error case
                         nil)))
         (fn0 fn)
         (fn (cond ((symbolp fn)
                    fn)
                   ((symbol-listp fn)
                    (car fn))
                   (t ; error case
                    nil)))
         (fn-params (cdr fn-args))
         (dom (or dom '(acl2)))
         (name$prop (and (symbolp name)
                         (suffix-symbol "$PROP" name)))
         (name$y (and (symbolp name)
                      (suffix-symbol "$Y" name)))
         (name$domain-2-better (and (symbolp name)
                                   (packn (list name '$domain-2-better))))
         (name$chooses-better (and (symbolp name)
                                   (packn (list name '$chooses-better))))
         (all-args (append fn-params args))
         (call (cons name all-args))
         (hyps (and (true-listp xhyps)
                    (append? (force-props props)
                             (pairlis-x1 'force (pairlis-x2 xhyps nil)))))
         (unforced-hyps (append? (props-to-hyps props) xhyps))
         (generic-prop-hyp (if unforced-hyps
                          `(and (,name$prop)
                                ,@unforced-hyps)
                        `(,name$prop)))
         (generic-subst `((generic-prop
                      ,(if unforced-hyps
                           `(lambda ()
                              (and (,name$prop)
                                   ,@unforced-hyps))
                         name$prop))
                     (generic-dom (lambda () ,dom))
                     (generic-rel (lambda () ,call))
                     (generic-fn  (lambda (,(car fn-args))
                               (,fn ,@fn-args)))))
         (form
          `(progn
             (check-zify ,name0 ,fn0 ,dom ,ran ,props0 ,xhyps ,all-args ,var)
             (check-arity ,fn ,(len fn-args))

; Zfn proves its constraints for the local witness in the current theory,
; where rules about DOM may force props it cannot relieve, for example v$prop
; for (v-omega).  So we admit it in a minimal theory.

             (encapsulate
               ()
               (local (in-theory (union-theories '(domain-0 subset-0 funp-0)
                                                 (theory 'minimal-theory))))
               (zfn ,name                                     ; name
                    ,all-args                                 ; args
                    ,(car fn-args)                            ; x
                    ,name$y                                   ; y
                    ,dom                                      ; bound
                    (equal (equal ,name$y (,fn ,@fn-args)) t) ; u
                    ))

; Zfn leaves NAME$chooses enabled.  Its left-hand side is (equal y (fn x ...))
; for any y, so it fires on equalities about fn everywhere and then forces
; (NAME$prop).  NAME-is-FN below says the same thing safely, so we disable it;
; the hints below that need it name it explicitly.

             (in-theory (disable ,(packn (list name '$chooses))))

; As in the original zify, domain-NAME is a functional instance of a generic
; theorem, and its constraints are proved here once for all the functional
; instances below.  Most of them follow by rewriting with zfn's theorems, as
; the original zify's follow from zsub's NAME$comprehension.  But zfn's
; NAME$domain-2 has the hypothesis u with the free variable NAME$y, which
; rewriting cannot bind; for zfn's general u that hypothesis says that some
; witness exists.  Here the witness is always the value of fn, so we
; first prove NAME$domain-2-better, which is NAME$domain-2 without that
; hypothesis.  It is local since domain-NAME subsumes it.  Similarly, zfn's
; NAME$chooses cannot rewrite when the call of NAME has arguments that the call
; of fn does not, for example the :args, since they are then free in its first
; hypothesis.  So we also prove NAME$chooses-better, with y bound to the value
; of the call of NAME, locally since NAME-is-FN subsumes it.

; We prove domain-NAME in a minimal theory because of NAME$domain-1: its
; left-hand side, (subset (domain (NAME ...)) dom), contains dom.  ACL2
; rewrites the arguments of a term before trying rules on it, so in the
; default theory dom may be rewritten first (for example, prodn-fn opens for
; (prodn* 3 (acl2))), and then NAME$domain-1 no longer matches its obligation.
; The original zify does not have this problem: its only rule about dom, zsub's
; NAME$comprehension, has dom only on its right-hand side.  (The other
; obligations would be fine in the default theory, since, as in the original
; zify's generic-rel$comprehension, the constraints generic-rel$domain-2 and
; generic-rel$chooses have (zify-prop) among their hypotheses, so props that
; rules about dom force can be relieved.)

             (encapsulate
               ()
               (local (defthm ,name$domain-2-better
                        (implies (and (in ,(car fn-args) ,dom)
                                      (force (,name$prop)))
                                 (in ,(car fn-args) (domain ,call)))
                        :hints (("Goal"
                                 :use (:instance ,(packn (list name '$domain-2))
                                                 (,name$y (,fn ,@fn-args)))
                                 :in-theory (theory 'minimal-theory)))))
               (local (defthm ,name$chooses-better
                        (implies (and (in ,(car fn-args) (domain ,call))
                                      (force (,name$prop)))
                                 (equal (apply ,call ,(car fn-args))
                                        (,fn ,@fn-args)))
                        :hints (("Goal"
                                 :use (:instance ,(packn (list name '$chooses))
                                                 (,name$y (apply ,call
                                                                 ,(car fn-args))))
                                 :in-theory (theory 'minimal-theory)))))
               (defthm ,(prefix-symbol "DOMAIN-" name)
                 (implies (and (force ,generic-prop-hyp)
                               (force (zify-prop)))
                          (equal (domain ,call)
                                 ,dom))
                 :hints
                 (("Goal" :by (:functional-instance
                               domain-of-generic-fn-is-generic-dom
                               ,@generic-subst)
                   :in-theory (union-theories
                               '(,(packn (list name '$funp))
                                 ,(packn (list name '$domain-1))
                                 ,name$domain-2-better
                                 ,name$chooses-better)
                               (theory 'minimal-theory))))))

             (defthm ,(suffix-symbol (concatenate 'string
                                                  "-IS-"
                                                  (symbol-name fn))
                                     name)
               (implies (and (in ,(car fn-args) ,dom)
                             (force (,name$prop))
                             (force (zify-prop))
                             ,@hyps)
                        (equal (apply ,call ,(car fn-args))
                               (,fn ,@fn-args)))


; Unlike the original zify, we need a hint: without one, the proof relies on
; NAME$chooses
; matching the call of FN, which fails when the call is normalized, for
; example (binary-+ n k) to (binary-+ k n).

               :hints
               (("Goal" :use (:functional-instance
                              (:instance apply-generic-rel (x ,(car fn-args)))
                              ,@generic-subst)
                 :in-theory (union-theories '(force)
                                            (theory 'minimal-theory)))))

             ,@(and ran
                    `((defthm ,(prefix-symbol "SUBSET-IMAGE-" name)
                        (implies (and (force ,generic-prop-hyp)
                                      (force (zify-prop)))
                                 (subset (image ,call) ,ran))
                        :hints
                        (("Goal" :by (:functional-instance
                                      subset-image-generic-rel-generic-ran
                                      ,@generic-subst
                                      (generic-ran (lambda () ,ran))))))))

; When a codomain is given, in-NAME has the form of zsub's NAME$comprehension,
; as for the original zify, which is easier to use in rewriting: membership in
; the product
; gives both (in (car p) dom) and (in (cdr p) ran).  It comes after
; subset-image-NAME, whose proof discharges the codomain constraint.

             (defthm ,(prefix-symbol "IN-" name)
               (implies (and (force ,generic-prop-hyp)
                             (force (zify-prop)))
                        (equal (in ,var ,call)
                               ,(if ran
                                    `(and (in ,var (prod2 ,dom ,ran))
                                          (equal (cdr ,var)
                                                 (,fn (car ,var) ,@fn-params)))
                                  `(and (consp ,var)
                                        (in (car ,var) ,dom)
                                        (equal (cdr ,var)
                                               (,fn (car ,var) ,@fn-params))))))
               :hints
               (("Goal" :use (:functional-instance
                              (:instance ,(if ran 'in-generic-rel-with-ran 'in-generic-rel)
                                         (p ,var))
                              ,@generic-subst
                              ,@(and ran `((generic-ran (lambda () ,ran)))))
                 :in-theory (union-theories '(force)
                                            (theory 'minimal-theory)))))
             (value-triple ',name))))
    (cond (verbose form)
          (t `(with-output :off (:other-than error) :gag-mode nil
                ,form)))))

(defmacro zify (name fn &key dom ran props xhyps args (var 'p) verbose)

; Fn is either a unary ACL2 function symbol or a call (f v1 ... vk) where the
; vi are distinct variables and k is the arity of the ACL2 function symbol, fn.
; We define a function, name, that is the set-theoretic realization of fn
; viewed as a function of its first argument, the other arguments being
; considered as parameters, with domain dom.  More precisely, (name . args) is
; that function if fn is a symbol, and otherwise (name v2 ... vk . args) is
; that function.

; The keyword arguments are as for the original zify, except that :ran is
; optional and has no default: when supplied, we also prove subset-image-NAME,
; which requires fn to map dom into ran.  Without :ran, nothing needs to be
; proved about fn.

  (declare (xargs :guard t)) ; see check-zify
  (zify-fn name fn dom ran props xhyps args var verbose))

; Now we test based on the example in zify-motivation.lisp.

(defun fib (n)
  (declare (xargs :guard (natp n)
                  :guard-hints (("Goal" :in-theory (enable natp)))))
  (cond ((zp n) 0)
        ((= n 1) 1)
        (t (+ (fib (- n 1)) (fib (- n 2))))))

(zify zfib fib :dom (omega) :ran (omega))

(thmz (equal (map (zfib) '(0 1 2 3 4 5 6 7))
             '(0 1 1 2 3 5 8 13))
      :props (zify-prop zfib$prop))

(defun map-fib (lst)
  (declare (xargs :guard (nat-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (fib (car lst))
                 (map-fib (cdr lst))))))

(defthmz map-zfib
  (implies (nat-listp lst)
           (equal (map (zfib) lst)
                  (map-fib lst)))
  :props (zify-prop zfib$prop))

; Another test of zify:

(defun fact (n)
  (declare (type (integer 0 *) n))
  (if (zp n) 1 (* n (fact (1- n)))))

(zify zfact fact :dom (omega) :ran (omega))

(thmz (equal (map (zfact) '(2 3 4 5))
             '(2 6 24 120))
      :props (zify-prop zfact$prop))

(defun map-fact (lst)
  (declare (xargs :guard (nat-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (fact (car lst))
                 (map-fact (cdr lst))))))

(defthmz map-of-fact-is-map-fact
  (implies (nat-listp lst)
           (equal (map (zfact) lst)
                  (map-fact lst)))
  :props (zfact$prop zify-prop))

; Now for a simpler example: the identity function.

(zify identity-fun-sv-omega identity
      :dom (v-omega)
      :ran (v-omega)
      :props (v$prop))

; Yet another example.

(defun mirror (x)
  (cond ((atom x) x)
        (t (cons (mirror (cdr x))
                 (mirror (car x))))))

(prove-acl2p mirror)

(zify zmirror mirror)

; Here is an example with :args.

(defun erase-atoms (tree lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((atom tree)
         (if (member-equal tree lst)
             nil
           tree))
        (t (cons (erase-atoms (car tree) lst)
                 (erase-atoms (cdr tree) lst)))))

; Variant of (prove-acl2p erase-atoms):
(defthm acl2p-erase-atoms
  (implies (acl2p tree)
           (acl2p (erase-atoms tree lst)))
  :hints (("Goal" :in-theory (enable erase-atoms))))

(zify zerase-atoms (erase-atoms tree lst))

; Here is a somewhat silly variant of the zify call just above, which however
; illustrates the use of arguments in the second argument of zify.

(encapsulate
  ()

  (local (include-book "set-algebra"))

  (local (defun erase-atoms2 (tree lst d)
           (declare (xargs :guard (true-listp lst)) (irrelevant d))
           (cond ((atom tree)
                  (if (member-equal tree lst)
                      nil
                    tree))
                 (t (cons (erase-atoms2 (car tree) lst d)
                          (erase-atoms2 (cdr tree) lst d))))))

  (local (defthm acl2p-erase-atoms2
           (implies (acl2p tree)
                    (acl2p (erase-atoms2 tree lst d)))))

  (local (zify zerase-atoms2 (erase-atoms2 tree lst d)
               :dom (int2 d (acl2))
               :props (acl2$prop v$prop diff$prop))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Prodn, prodn*
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Just as (prod2 s1 s2) is the Cartesian product s1 X s2, (prodn s1 s2
; ... sk) is the set of true-lists whose ith component is in si, i = 1, ..., k.
; We could just as well define (prodn s1 s2 ... sk) = s1 X s2 X ... X sk,
; where X is right-associated. But we intend to use prodn to produce the set
; of argument lists, each of which is a true list.

; (Prodn* k s) is (prod s s ... s) with k arguments of s.

(defmacro prodn (&rest args)
  `(prodn-fn (list ,@args)))

(defmacro prodn* (k s)
  (declare (xargs :guard (natp k)))
  `(prodn ,@(make-list k :initial-element s)))

(defun prodn-fn (lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) (singleton nil))
        (t (prod2 (car lst)
                  (prodn-fn (cdr lst))))))

(in-theory (disable (:e prodn-fn)))

; Example
(thm (equal (prodn x y z)
            (prod2 x (prod2 y (prod2 z (singleton nil))))))

(defun in-prodn-fn-induction (a lst)
  (if (consp lst)
      (in-prodn-fn-induction (cdr a) (cdr lst))
    (list a lst)))

(defthmz prodn-members
  (implies (in a (prodn-fn lst))
           (and (true-listp a)
                (equal (len a) (len lst))))
  :props (zfc prod2$prop)
  :hints (("Goal" :induct (in-prodn-fn-induction a lst)))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Zify*
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun arglist-to-list-of-nths (k x acc)
  (declare (xargs :guard (and (natp k)
                              (true-listp acc))))
  (cond ((zp k) acc)
        (t (arglist-to-list-of-nths (1- k)
                                    x
                                    (cons `(nth ,(1- k) ,x)
                                          acc)))))

(defun list-of-nths (var bound acc)
  (declare (xargs :guard (and (natp bound)
                              (true-listp acc))))
  (cond ((zp bound) acc)
        (t (let ((bound (1- bound)))
             (list-of-nths var bound (cons `(nth ,bound ,var) acc))))))

(defthm equal-len-n
  (implies (and (syntaxp (quotep n))
                (natp n))
           (equal (equal n (len x))
                  (if (equal n 0)
                      (atom x)
                    (and (consp x)
                         (equal (len (cdr x)) (1- n)))))))

; Just a little test:
(thmz (equal (in a (prodn x y z))
             (and (true-listp a)
                  (equal (len a) 3)
                  (in (nth 0 a) x)
                  (in (nth 1 a) y)
                  (in (nth 2 a) z)))
      :props (zfc prod2$prop))

(defun check-zify*-fn (name fn arity dom ran props xhyps params args verbose
                            fn* fn*-var fn*-dcls ctx state)
  (declare (xargs :stobjs state :guard (error1-state-p state))
           (ignore dom ran verbose fn*-dcls))
  (cond
   ((not (symbolp name))
    (er soft ctx
        "The first argument of ~x0 must be a symbol, but ~x1 is not."
        'zify* name))
   ((not (symbolp fn))
    (er soft ctx
        "The second argument of ~x0 must be a symbol, but ~x1 is not."
        'zify* fn))
   ((not (posp arity))
    (er soft ctx
        "The third argument of ~x0 must be a positive integer, but ~x1 is not."
        'zify* arity))
   ((not (symbol-listp props))
    (er soft ctx
        "The value of the :props keyword of ~x0 must be a true list of ~
         symbols, but ~x1 is not."
        'zify props))
   ((not (true-listp xhyps))
    (er soft ctx
        "The :xhyps value of ~x0 is ~x1, which is illegal since it must be a ~
         true-list."
        'zify xhyps))
   ((not (and (symbol-listp args)
              (no-duplicatesp args :test 'eq)
              (symbol-listp params)
              (no-duplicatesp params :test 'eq)
              (not (intersectp-eq args params))))
    (er soft ctx
        "The :args and :params keywords of ~x0 must be duplicates-free true ~
         lists of symbols that do not intersection.  But these have values ~
         ~x1 and ~x2, respectively."
        'zify* args params))
   ((not (symbolp fn*))
    (er soft ctx
        "The :fn* value of ~x0 is ~x1, which is illegal since it must be a ~
         symbol."
        'zify fn*))
   ((not (symbolp fn*-var))
    (er soft ctx
        "The :fn* value of ~x0 is ~x1, which is illegal since it must be a ~
         symbol."
        'zify fn*-var))
   (t (value nil))))

(defmacro check-zify* (name fn arity dom ran props xhyps params args verbose
                            fn* fn*-var fn*-dcls)
  `(make-event
    (er-progn (check-zify*-fn ',name ',fn ',arity ',dom ',ran ',props ',xhyps
                              ',params ',args  ',verbose ',fn* ',fn*-var
                              ',fn*-dcls 'zify* state)
              (value '(value-triple nil)))
    :on-behalf-of :quiet
    :check-expansion t
    :expansion? (value-triple nil)))

(defthm true-listp-arglist-to-list-of-nths
  (equal (true-listp (arglist-to-list-of-nths k x acc))
         (true-listp acc)))

(defun zify*-fn (name fn arity dom ran props xhyps params args var verbose
                       fn* fn*-var fn*-dcls)

; As for the original zify*-fn, except that ran has no default.

  (declare (xargs :guard t :mode :logic))
  (let* ((fn* (or fn*
                  (and (symbolp fn)
                       (suffix-symbol "*" fn))))
         (props (if (null dom)

; This is the right default for the common case, where dom defaults to (acl2).

                    (append '(v$prop acl2$prop) props)
                  props))
         (arity0 arity)
         (arity (nfix arity0))
         (dom (or dom `(prodn* ,arity (acl2))))
         (args0 args)
         (args (and (symbol-listp args0) args0))
         (params0 params)
         (params (and (symbol-listp params0) params))
         (args-minus-params (set-difference-eq args params))
         (fn*-args (cons fn*-var params)))
    `(progn (check-zify* ,name ,fn ,arity0 ,dom ,ran ,props ,xhyps ,params0
                         ,args0 ,verbose ,fn* ,fn*-var ,fn*-dcls)
            (defun ,fn* ,fn*-args
              ,@(and (true-listp fn*-dcls) fn*-dcls)
              (,fn ,@(arglist-to-list-of-nths arity fn*-var nil)
                   ,@params))
            (zify ,name (,fn* ,@fn*-args)
                   ,@(and dom (list :dom dom))
                   ,@(and ran (list :ran ran))
                   ,@(and props (list :props props))
                   ,@(and xhyps (list :xhyps xhyps))
                   ,@(and args-minus-params (list :args args-minus-params))
                   ,@(and var (list :var var))
                   ,@(and verbose (list :verbose verbose))))))

(defmacro zify* (name fn arity
                       &key dom ran props xhyps params args (var 'p) verbose
                       fn* (fn*-var 'du) fn*-dcls)

; Summary.

; Recall that (zify name fn ...) creates a set-theoretic constant, (name), that
; is the set-theoretic realization of the unary ACL2 function fn, basically, so
; that (apply (name) x) = (fn x).  (Zify* name fn k ...) is similar but
; removes the requirement that fn be unary and creates name such that, in
; essence, (apply (name) (list x1 ... xk)) = (fn x1 ... xk).

; Details.

; Fn is an ACL2 function symbol with the given arity.  We define a function,
; name, that is the set-theoretic realization of fn, whose domain is dom.  Dom
; defaults to the arity-fold product of (acl2) and should be a set of true
; lists, each of length arity, corresponding to the valid argument lists for
; fn.  For example, if fn has arity 2 and name is intended to take any two
; natural numbers i < j, then dom would contain all lists (i j) ranging over
; natural numbers i < j.  Ran is optional, as for zify: when supplied, it
; should contain the values of fn for argument lists in dom, and we also prove
; subset-image-NAME.  We want name to correspond logically to fn over dom, so
; if fn returns (mv v1 ... vk) we think of fn as returning (list v1 ... vk).

; The keyword arguments of zify* include those of zify but include fn*, which
; is the name of an auxiliary unary ACL2 function to be introduced whose value
; on a list is equal to the value of fn on the respective members of the list.

  (declare (xargs :guard (natp arity)))
  (zify*-fn name fn arity dom ran props xhyps params args var verbose fn*
             fn*-var fn*-dcls))

; Test:
(zify* zput-assoc* put-assoc 3)

; A trivial consequence:
(thmz (implies (and (in x0 (acl2))
                    (in x1 (acl2))
                    (in x2 (acl2)))
               (equal (apply (zput-assoc*) (list x0 x1 x2))
                      (put-assoc x0 x1 x2)))
      :props (zput-assoc*$prop zify-prop v$prop acl2$prop))

; More tests.

(defun f0 (x y z)
  (list z y x))

(prove-acl2p f0)

(zify* zf0* f0 3
       :props (prod2$prop domain$prop inverse$prop zfc))

(zify* zmirror* mirror 1)

; Test fn returning an mv.

(defun f1 (x)
  (mv x x))

(zify zf1 f1)

(defun f2 (x y)
  (mv x y x))

(zify* zf2* f2 2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; zify without :ran
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Zify needs a codomain only for subset-image-NAME, so these omit :ran, and
; nothing is proved about where fn maps dom.

(zify zfib-nr fib :dom (omega))

(thmz (equal (apply (zfib-nr) 10) 55)
      :props (zify-prop zfib-nr$prop))

(thmz (equal (domain (zfib-nr)) (omega))
      :props (zify-prop zfib-nr$prop))

; Without :ran, in-NAME has the general form.
(thmz (in '(5 . 5) (zfib-nr))
      :props (zify-prop zfib-nr$prop))

(zify zfact-nr fact :dom (omega))

(thmz (equal (map (zfact-nr) '(2 3 4 5))
             '(2 6 24 120))
      :props (zify-prop zfact-nr$prop))

;; What this zify can do that the original cannot: zify a function without
;; proving that it maps its domain into a codomain.  The original zify's :ran
;; defaults to (acl2), so its tests of mirror and erase-atoms above need
;; (prove-acl2p mirror) and acl2p-erase-atoms.  Here are copies of mirror and
;; erase-atoms with no acl2p theorems, and zify without :ran needs nothing about
;; them.

(defun mirror-nr (x)
  (cond ((atom x) x)
        (t (cons (mirror-nr (cdr x))
                 (mirror-nr (car x))))))

(zify zmirror-nr mirror-nr)

(thmz (implies (in x (acl2))
               (equal (apply (zmirror-nr) x)
                      (mirror-nr x)))
      :props (zify-prop zmirror-nr$prop v$prop acl2$prop))

(defun erase-atoms-nr (tree lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((atom tree)
         (if (member-equal tree lst)
             nil
           tree))
        (t (cons (erase-atoms-nr (car tree) lst)
                 (erase-atoms-nr (cdr tree) lst)))))

(zify zerase-atoms-nr (erase-atoms-nr tree lst))

(thmz (implies (in tree (acl2))
               (equal (apply (zerase-atoms-nr lst) tree)
                      (erase-atoms-nr tree lst)))
      :props (zify-prop zerase-atoms-nr$prop v$prop acl2$prop))

; A parameter of fn in the domain, and a call that arithmetic normalizes.
(zify zplus-nr (binary-+ n k) :dom (omega))

(thmz (implies (in n (omega))
               (equal (apply (zplus-nr k) n) (+ n k)))
      :props (zify-prop zplus-nr$prop))

; :args, where the domain is a variable, and :props.
(zify identity-fun-nr identity :dom s :args (s))

(thmz (equal (domain (identity-fun-nr s)) s)
      :props (zify-prop identity-fun-nr$prop))

(zify identity-fun-sv-omega-nr identity
       :dom (v-omega)
       :props (v$prop))

; Multiple values.
(zify zf1-nr f1)

(thmz (implies (in x (acl2))
               (equal (apply (zf1-nr) x) (list x x)))
      :props (zify-prop zf1-nr$prop v$prop acl2$prop))

; Zify*.
(zify* zput-assoc*-nr put-assoc 3 :fn* put-assoc*-nr)

(thmz (implies (and (in x0 (acl2))
                    (in x1 (acl2))
                    (in x2 (acl2)))
               (equal (apply (zput-assoc*-nr) (list x0 x1 x2))
                      (put-assoc x0 x1 x2)))
      :props (zput-assoc*-nr$prop zify-prop v$prop acl2$prop))

(zify* zf2*-nr f2 2 :fn* f2*-nr)
