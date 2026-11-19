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

(encapsulate
  (((generic-prop) => *)
   ((generic-dom) => *)
   ((generic-ran) => *)
   ((generic-rel) => *)
   ((generic-fn *) => *))
  (local (defun generic-prop () nil))
  (local (defun generic-dom () 0))
  (local (defun generic-ran () 0))
  (local (defun generic-rel () 0))
  (local (defun generic-fn (x) x))
  (defthm generic-image-is-image
    (implies (and (in x (generic-dom))
                  (generic-prop)
                  (force (zify-prop)))
             (in (generic-fn x) (generic-ran))))
  (defthm generic-rel$comprehension
    (implies (and (force (zify-prop))
                  (generic-prop))
             (equal (in p (generic-rel))
                    (and (in p (prod2 (generic-dom) (generic-ran)))
                         (equal (cdr p) (generic-fn (car p))))))))

(defthm subset-domain-generic-rel-generic-dom
  (implies (and (force (zify-prop))
                (generic-prop))
           (subset (domain (generic-rel))
                   (generic-dom)))
  :hints (("Goal" :in-theory (e/d (subset in-domain-rewrite)
                                  (in-cons-apply)))))

(defthm subset-generic-dom-domain-generic-rel-lemma
  (implies (and (in x (generic-dom))
                (generic-prop)
                (force (zify-prop)))
           (in x (domain (generic-rel))))
  :hints (("Goal" :use ((:instance generic-rel$comprehension
                                   (p (cons x (generic-fn x)))))
           :in-theory (disable generic-rel$comprehension))))

(defthm subset-generic-dom-domain-generic-rel
  (implies (and (generic-prop)
                (force (zify-prop)))
           (subset (generic-dom)
                   (domain (generic-rel))))
  :hints (("Goal" :in-theory (enable subset))))

(defthm domain-of-generic-fn-is-generic-dom
  (implies (and (force (generic-prop))
                (force (zify-prop)))
           (equal (domain (generic-rel))
                  (generic-dom)))
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

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

; This is the right default for the common case, where dom defaults to (acl2).

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
         (ran (or ran '(acl2)))
         (name$prop (and (symbolp name)
                         (suffix-symbol "$PROP" name)))
         (all-args (append fn-params args))
         (call (cons name all-args))
         (hyps (and (true-listp xhyps)
                    (append? (force-props props)
                             (pairlis-x1 'force (pairlis-x2 xhyps nil)))))
         (unforced-hyps (append? (props-to-hyps props) xhyps))
         (form
          `(progn
             (check-zify ,name0 ,fn0 ,dom ,ran ,props0 ,xhyps ,all-args ,var)
             (check-arity ,fn ,(len fn-args))

             (zsub ,name                                           ; name
                   ,all-args                                       ; args
                   ,var                                            ; x
                   (prod2 ,dom ,ran)                              ; s
                   (equal (cdr ,var) (,fn (car ,var) ,@fn-params)) ; u
                   )

             (defthm ,(prefix-symbol "FUNP-" name)
               (implies (and (force (,name$prop))
                             (force (zify-prop))
                             ,@hyps)
                        (funp ,call))
               :hints (("Goal" :in-theory (enable relation-p funp))))

             (defthm ,(prefix-symbol "DOMAIN-" name)
               (implies (and (force ,(if unforced-hyps
                                         `(and (,name$prop)
                                               ,@unforced-hyps)
                                       `(,name$prop)))
                             (force (zify-prop)))
                        (equal (domain ,call)
                               ,dom))
               :hints
               (("Goal" :by (:functional-instance
                             domain-of-generic-fn-is-generic-dom
                             (generic-prop
                              ,(if unforced-hyps
                                   `(lambda ()
                                      (and (,name$prop)
                                           ,@unforced-hyps))
                                 name$prop))
                             (generic-dom (lambda () ,dom))
                             (generic-ran (lambda () ,ran))
                             (generic-rel (lambda () ,call))
                             (generic-fn  (lambda (,(car fn-args))
                                            (,fn ,@fn-args)))))))

             (defthm ,(suffix-symbol (concatenate 'string
                                                  "-IS-"
                                                  (symbol-name fn))
                                     name)
               (implies (and (in ,(car fn-args) ,dom)
                             (force (,name$prop))
                             (force (zify-prop))
                             ,@hyps)
                        (equal (apply ,call ,(car fn-args))
                               (,fn ,@fn-args))))
             (value-triple ',name))))
    (cond (verbose form)
          (t `(with-output :off (:other-than error) :gag-mode nil
                ,form)))))

(defmacro zify (name fn &key dom ran props xhyps args (var 'p) verbose)

; Fn is either a unary ACL2 function symbol or a call (f v1 ... vk) where the
; vi are distinct variables and k is the arity of the ACL2 function symbol, fn.
; We define a function, name, that is the set-theoretic realization of fn
; viewed as a function of its first argument, the other arguments being
; considered as parameters, whose domain and codomain (range) are specified as
; dom and ran.  More precisely, (name . args) is that function if fn is a
; symbol, and otherwise (name v2 ... vk . args) is that function.

; The keyword arguments are optional.  Dom and ran default to (acl2) and the
; others default to nil.  Args contains all variables occurring free in dom or
; ran.  Props is a list of additional hypotheses as zero-ary functions, under
; which the desired properties are to hold, in addition to the hypotheses of
; (name$prop) and (zify-prop).  Xhyps is a list of untranslated terms to be
; added to the hypothese generated from props.  Verbose defeats the default
; behavior of inhibiting non-error output from zify.

; Note that the functional instantiation of
; domain-of-generic-fn-is-generic-dom (shown below) requires a proof that the
; domain of the generated function is indeed dom, which is only the case if fn
; maps dom into ran.

; Note that the variable p mustn't occur free in dom or ran.  This is enforced
; by zsub.

  (declare (xargs :guard t)) ; see check-zify
  (zify-fn name fn dom ran props xhyps args var verbose))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Zify
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(extend-zfc-table zify2-prop
		  domain$prop prod2$prop inverse$prop zfc)

(encapsulate
  (((g2-prop) => *)
   ((g2-dom) => *)
   ((g2-rel) => *)
   ((g2-fn *) => *))
  (local (defun g2-prop () nil))
  (local (defun g2-dom () 0))
  (local (defun g2-rel () 0))
  (local (defun g2-fn (x) x))
  (defthm g2-rel$funp
    (funp (g2-rel)))
  (defthmz g2-rel$domain-1
    (implies (force (domain$prop))
             (subset (domain (g2-rel))
		     (g2-dom))))
  (defthm g2-rel$domain-2
    (implies (and (in x (g2-dom))
		  (force (g2-prop)))
             (in x (domain (g2-rel)))))
  (defthm g2-rel$chooses
    (implies (and (equal (apply (g2-rel) x) y)
		  (in x (domain (g2-rel)))
		  (force (g2-prop)))
             (equal (equal y (g2-fn x)) t))))

(defthm apply-g2-rel
  (implies (and (in x (g2-dom))
                (force (g2-prop)))
           (equal (apply (g2-rel) x)
                  (g2-fn x))))

(defthm domain-of-g2-fn-is-g2-dom
  (implies (and (force (g2-prop))
		(force (zify2-prop)))
           (equal (domain (g2-rel))
		  (g2-dom)))
  :hints (("Goal" :in-theory (enable extensionality-rewrite subset))))

(defthm in-g2-rel
  (implies (and (force (zify2-prop))
		(g2-prop))
           (equal (in p (g2-rel))
		  (and (consp p)
		       (in (car p) (g2-dom))
		       (equal (cdr p) (g2-fn (car p))))))
  :hints (("Goal" :use ((:instance apply-intro
				   (f (g2-rel)))))))

(encapsulate
  (((g2-ran) => *))
  (local (defun g2-ran () (image (g2-rel))))
  (defthm g2-image-is-image
    (implies (and (in x (g2-dom))
		  (g2-prop)
		  (force (zify2-prop)))
             (in (g2-fn x) (g2-ran)))
    :hints (("Goal" :use ((:instance in-apply-image (r (g2-rel))))))))

;; this is the same as g2-image-is-image, but works better for the next theorem
(defthm in-g2-ran
  (implies (and (equal y (g2-fn x))
		(in x (g2-dom))
		(g2-prop)
		(force (zify2-prop)))
           (in y (g2-ran))))

(defthm subset-image-g2-rel-g2-ran
  (implies (and (force (g2-prop))
		(force (zify2-prop)))
           (subset (image (g2-rel))
		   (g2-ran)))
  :hints (("Goal" :in-theory (enable subset in-image-rewrite))))

(defun zify2-fn (name fn dom ran props xhyps args var verbose)
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
         (all-args (append fn-params args))
         (call (cons name all-args))
         (hyps (and (true-listp xhyps)
                    (append? (force-props props)
                             (pairlis-x1 'force (pairlis-x2 xhyps nil)))))
         (unforced-hyps (append? (props-to-hyps props) xhyps))
         (g2-prop-hyp (if unforced-hyps
                          `(and (,name$prop)
                                ,@unforced-hyps)
                        `(,name$prop)))
         (g2-subst `((g2-prop
                      ,(if unforced-hyps
                           `(lambda ()
                              (and (,name$prop)
                                   ,@unforced-hyps))
                         name$prop))
                     (g2-dom (lambda () ,dom))
                     (g2-rel (lambda () ,call))
                     (g2-fn  (lambda (,(car fn-args))
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

; As for zify, domain-NAME is a functional instance of a generic theorem, and
; its constraints are proved here once for all the functional instances below.
; Most of them follow by rewriting with zfn's theorems, as for zify.  But zfn's
; NAME$domain-2 has the hypothesis u with the free variable NAME$y, which
; rewriting cannot bind; for zfn's general u that hypothesis says that some
; witness exists.  For zify2 the witness is always the value of fn, so we
; first prove NAME$domain-2-better, which is NAME$domain-2 without that
; hypothesis.  It is local since domain-NAME subsumes it.  We use a minimal
; theory since the only prop in the obligations is (NAME$prop), so rules about
; dom could force (zfc).

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
               (defthm ,(prefix-symbol "DOMAIN-" name)
                 (implies (and (force ,g2-prop-hyp)
                               (force (zify2-prop)))
                          (equal (domain ,call)
                                 ,dom))
                 :hints
                 (("Goal" :by (:functional-instance
                               domain-of-g2-fn-is-g2-dom
                               ,@g2-subst)
                   :in-theory (union-theories
                               '(force zify2-prop
                                       ,(packn (list name '$funp))
                                       ,(packn (list name '$domain-1))
                                       ,name$domain-2-better
                                       ,(packn (list name '$chooses)))
                               (theory 'minimal-theory))))))

             (defthm ,(suffix-symbol (concatenate 'string
                                                  "-IS-"
                                                  (symbol-name fn))
                                     name)
               (implies (and (in ,(car fn-args) ,dom)
                             (force (,name$prop))
                             (force (zify2-prop))
                             ,@hyps)
                        (equal (apply ,call ,(car fn-args))
                               (,fn ,@fn-args)))


; Unlike zify, we need a hint: without one, the proof relies on NAME$chooses
; matching the call of FN, which fails when the call is normalized, for
; example (binary-+ n k) to (binary-+ k n).

               :hints
               (("Goal" :use (:functional-instance
                              (:instance apply-g2-rel (x ,(car fn-args)))
                              ,@g2-subst)
                 :in-theory (union-theories '(force)
                                            (theory 'minimal-theory)))))

             (defthm ,(prefix-symbol "IN-" name)
               (implies (and (force ,g2-prop-hyp)
                             (force (zify2-prop)))
                        (equal (in ,var ,call)
                               (and (consp ,var)
                                    (in (car ,var) ,dom)
                                    (equal (cdr ,var)
                                           (,fn (car ,var) ,@fn-params)))))
               :hints
               (("Goal" :use (:functional-instance
                              (:instance in-g2-rel (p ,var))
                              ,@g2-subst)
                 :in-theory (union-theories '(force)
                                            (theory 'minimal-theory)))))

             ,@(and ran
                    `((defthm ,(prefix-symbol "IMAGE-" name)
                        (implies (and (force ,g2-prop-hyp)
                                      (force (zify2-prop)))
                                 (subset (image ,call) ,ran))
                        :hints
                        (("Goal" :by (:functional-instance
                                      subset-image-g2-rel-g2-ran
                                      ,@g2-subst
                                      (g2-ran (lambda () ,ran))))))))
             (value-triple ',name))))
    (cond (verbose form)
          (t `(with-output :off (:other-than error) :gag-mode nil
                ,form)))))

(defmacro zify2 (name fn &key dom ran props xhyps args (var 'p) verbose)

; As for zify, except that :ran is optional: when supplied, we also prove
; image-NAME, which requires fn to map dom into ran.

  (declare (xargs :guard t)) ; see check-zify
  (zify2-fn name fn dom ran props xhyps args var verbose))

; Now we test based on the example in zify-motivation.lisp.

(defun fib (n)
  (declare (xargs :guard (natp n)
                  :guard-hints (("Goal" :in-theory (enable natp)))))
  (cond ((zp n) 0)
        ((= n 1) 1)
        (t (+ (fib (- n 1)) (fib (- n 2))))))

(zify zfib fib :dom (omega) :ran (omega))

;; zify2
(zify2 zfib2 fib :dom (omega) :ran (omega))

(thmz (equal (map (zfib) '(0 1 2 3 4 5 6 7))
             '(0 1 1 2 3 5 8 13))
      :props (zify-prop zfib$prop))

;; zify2
(thmz (equal (map (zfib2) '(0 1 2 3 4 5 6 7))
	     '(0 1 1 2 3 5 8 13))
      :props (zify2-prop zfib2$prop))

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

;; zify2
(defthmz map-zfib2
  (implies (nat-listp lst)
	   (equal (map (zfib2) lst)
		  (map-fib lst)))
  :props (zify2-prop zfib2$prop))

; Another test of zify:

(defun fact (n)
  (declare (type (integer 0 *) n))
  (if (zp n) 1 (* n (fact (1- n)))))

(zify zfact fact :dom (omega) :ran (omega))

;; zify2
(zify2 zfact2 fact :dom (omega) :ran (omega))

(thmz (equal (map (zfact) '(2 3 4 5))
             '(2 6 24 120))
      :props (zify-prop zfact$prop))

;; zify2
(thmz (equal (map (zfact2) '(2 3 4 5))
             '(2 6 24 120))
      :props (zify2-prop zfact2$prop))

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

;; zify2
(defthmz map-of-fact2-is-map-fact
  (implies (nat-listp lst)
           (equal (map (zfact2) lst)
                  (map-fact lst)))
  :props (zfact2$prop zify2-prop))

; Now for a simpler example: the identity function.

(zify identity-fun-sv-omega identity
      :dom (v-omega)
      :ran (v-omega)
      :props (v$prop))

;; zify2
(zify2 identity-fun-sv-omega2 identity
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

;; zify2
;; zify's :ran defaults to (acl2), so we supply it for the same image theorem.
(zify2 zmirror2 mirror :ran (acl2))

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

;; zify2
;; (Named zerase-atoms-2, since zerase-atoms2 is used just below.)
(zify2 zerase-atoms-2 (erase-atoms tree lst) :ran (acl2))

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
               :props (acl2$prop v$prop diff$prop)))

;; zify2
  (local (zify2 zerase-atoms2-2 (erase-atoms2 tree lst d)
                :dom (int2 d (acl2))
                :ran (acl2)
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

(defun zify*-fn (name fn arity dom ran props xhyps params args var verbose fn*
                      fn*-var fn*-dcls)
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
         (ran (or ran '(acl2)))
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
; name, that is the set-theoretic realization of fn, whose domain is dom and
; image is contained in ran.  Dom defaults to the arity-fold product of
; (acl2) and should be a set of true lists, each of length arity, corresponding
; to the valid argument lists for fn.  For example, if fn has arity 2 and name
; is intended to take any two natural numbers i < j, then dom would contain all
; lists (i j) ranging over natural numbers i < j.  Ran defaults to (acl2) and
; should contain the values of fn for argument lists in dom.  We want name to
; correspond logically to fn over dom, so if fn returns (mv v1 ... vk) we think
; of fn as returning (list v1 ... vk).

; The keyword arguments of zify* include those of zify but include fn*, which
; is the name of an auxiliary unary ACL2 function to be introduced whose value
; on a list is equal to the value of fn on the respective members of the list.

  (declare (xargs :guard (natp arity)))
  (zify*-fn name fn arity dom ran props xhyps params args var verbose fn*
            fn*-var fn*-dcls))

;; zify2*

(defun zify2*-fn (name fn arity dom ran props xhyps params args var verbose
                       fn* fn*-var fn*-dcls)

; As for zify*-fn, but calling zify2, and ran has no default.

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
            (zify2 ,name (,fn* ,@fn*-args)
                   ,@(and dom (list :dom dom))
                   ,@(and ran (list :ran ran))
                   ,@(and props (list :props props))
                   ,@(and xhyps (list :xhyps xhyps))
                   ,@(and args-minus-params (list :args args-minus-params))
                   ,@(and var (list :var var))
                   ,@(and verbose (list :verbose verbose))))))

(defmacro zify2* (name fn arity
                       &key dom ran props xhyps params args (var 'p) verbose
                       fn* (fn*-var 'du) fn*-dcls)

; As for zify*, except that we call zify2, so :ran is optional: when supplied,
; we also prove image-NAME.

  (declare (xargs :guard (natp arity)))
  (zify2*-fn name fn arity dom ran props xhyps params args var verbose fn*
             fn*-var fn*-dcls))

; Test:
(zify* zput-assoc* put-assoc 3)

;; zify2
;; (The default :fn*, put-assoc*, was introduced just above.)
(zify2* zput-assoc2* put-assoc 3 :fn* put-assoc2* :ran (acl2))

; A trivial consequence:
(thmz (implies (and (in x0 (acl2))
                    (in x1 (acl2))
                    (in x2 (acl2)))
               (equal (apply (zput-assoc*) (list x0 x1 x2))
                      (put-assoc x0 x1 x2)))
      :props (zput-assoc*$prop zify-prop v$prop acl2$prop))

;; zify2
(thmz (implies (and (in x0 (acl2))
                    (in x1 (acl2))
                    (in x2 (acl2)))
               (equal (apply (zput-assoc2*) (list x0 x1 x2))
                      (put-assoc x0 x1 x2)))
      :props (zput-assoc2*$prop zify2-prop v$prop acl2$prop))

; More tests.

(defun f0 (x y z)
  (list z y x))

(prove-acl2p f0)

(zify* zf0* f0 3
       :props (prod2$prop domain$prop inverse$prop zfc))

;; zify2
(zify2* zf0-2* f0 3 :fn* f0-2* :ran (acl2)
        :props (prod2$prop domain$prop inverse$prop zfc))

(zify* zmirror* mirror 1)

;; zify2
(zify2* zmirror2* mirror 1 :fn* mirror2* :ran (acl2))

; Test fn returning an mv.

(defun f1 (x)
  (mv x x))

(zify zf1 f1)

;; zify2
(zify2 zf1-2 f1 :ran (acl2))

(defun f2 (x y)
  (mv x y x))

(zify* zf2* f2 2)

;; zify2
(zify2* zf2-2* f2 2 :fn* f2-2* :ran (acl2))
