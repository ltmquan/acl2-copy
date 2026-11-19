; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Zify2: a zify built on zfn (Replacement) instead of zsub (Separation).

; (zify2 NAME FN :dom DOM [:ran RAN] ...) takes the same arguments as zify
; and introduces (NAME v2 ... vk . args), a set-theoretic function with domain
; DOM that agrees with FN on DOM, by way of
;   (zfn NAME (v2 ... vk . args) x NAME$y DOM (equal (equal NAME$y (FN x ...)) t)).
; That relation always has a witness, so the domain is exactly DOM with no
; hypotheses about FN.  Unlike zify, a codomain is needed only for the image
; theorem, so :ran is optional and has no default.

; Generated events, with call = (NAME v2 ... vk . args) and H the forced
; hypotheses (NAME$prop) and the :props and :xhyps, and (zify-prop):
;   zfn's NAME$funp, NAME$domain-1, NAME$domain-2 and NAME$chooses
;   domain-NAME   H => (domain call) = DOM
;   NAME-is-FN    (in x DOM) & H => (apply call x) = (FN x v2 ... vk)
;   in-NAME       H => (in p call) = (consp p) & (car p) in DOM
;                                    & (cdr p) = (FN (car p) v2 ... vk)
; and, only when :ran is supplied:
;   image-NAME    H => (subset (image call) RAN)
; These are functional instances of the g2-* events below, as zify's
; domain-NAME is a functional instance of its generic-* events.  In-NAME takes
; the place of zsub's NAME$comprehension.

(in-package "ZF")

; We reuse acl2, zify-prop, check-zify, check-arity, and prodn* from zify.
(include-book "zify")

;;; The generic function.  Its constraints are what zfn exports, with the same
;;; names, so the functional-instance obligations are zfn's NAME$funp,
;;; NAME$domain-1, NAME$domain-2 and NAME$chooses.  One difference: zfn's
;;; NAME$domain-2 has the hypothesis u, (equal (equal y (FN x ...)) t), which
;;; always holds for some y, so we drop it here.

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
                (force (zify-prop)))
           (equal (domain (g2-rel))
                  (g2-dom)))
  :hints (("Goal" :in-theory (enable extensionality-rewrite subset))))

(defthm in-g2-rel
  (implies (and (force (zify-prop))
                (g2-prop))
           (equal (in p (g2-rel))
                  (and (consp p)
                       (in (car p) (g2-dom))
                       (equal (cdr p) (g2-fn (car p))))))
  :hints (("Goal" :use ((:instance apply-intro
                                   (f (g2-rel)))))))

;;; The codomain, only for :ran.  It is in its own encapsulate so that
;;; instantiating the events above never requires a codomain; instantiating
;;; g2-ran costs only the obligation that FN maps DOM into RAN, which is
;;; proved in the user's theory, as for zify's generic-image-is-image.

(encapsulate
  (((g2-ran) => *))
  (local (defun g2-ran () (image (g2-rel))))
  (defthm g2-image-is-image
    (implies (and (in x (g2-dom))
                  (g2-prop)
                  (force (zify-prop)))
             (in (g2-fn x) (g2-ran)))
    :hints (("Goal" :use ((:instance in-apply-image (r (g2-rel))))))))

; The free x is bound by an equality hypothesis (equal y (g2-fn x)), such as
; the one that in-image-rewrite and in-g2-rel produce below.

(defthm in-g2-ran-when-equal-g2-fn
  (implies (and (equal y (g2-fn x))
                (in x (g2-dom))
                (g2-prop)
                (force (zify-prop)))
           (in y (g2-ran))))

(defthm image-g2-rel
  (implies (and (force (g2-prop))
                (force (zify-prop)))
           (subset (image (g2-rel)) (g2-ran)))
  :hints (("Goal" :in-theory (enable subset in-image-rewrite))))

;;; The macro

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
                               (force (zify-prop)))
                          (equal (domain ,call)
                                 ,dom))
                 :hints
                 (("Goal" :by (:functional-instance
                               domain-of-g2-fn-is-g2-dom
                               ,@g2-subst)
                   :in-theory (union-theories
                               '(force zify-prop
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
                             (force (zify-prop))
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
                             (force (zify-prop)))
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
                                      (force (zify-prop)))
                                 (subset (image ,call) ,ran))
                        :hints
                        (("Goal" :by (:functional-instance
                                      image-g2-rel
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


(defun zify2*-fn (name fn arity dom ran props xhyps params args var verbose
                       fn* fn*-var fn*-dcls)
  (declare (xargs :guard t :mode :logic))
  (let* ((fn* (or fn*
                  (and (symbolp fn)
                       (suffix-symbol "*" fn))))
         (props (if (null dom)
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
                   :dom ,dom
                   ,@(and ran (list :ran ran))
                   ,@(and props (list :props props))
                   ,@(and xhyps (list :xhyps xhyps))
                   ,@(and args-minus-params (list :args args-minus-params))
                   ,@(and var (list :var var))
                   ,@(and verbose (list :verbose verbose))))))

(defmacro zify2* (name fn arity
                       &key dom ran props xhyps params args (var 'p) verbose
                       fn* (fn*-var 'du) fn*-dcls)
  (declare (xargs :guard (natp arity)))
  (zify2*-fn name fn arity dom ran props xhyps params args var verbose fn*
             fn*-var fn*-dcls))

;;; Tests

(local (include-book "arithmetic/top" :dir :system))

; With :ran.
(zify2 zfib2 fib :dom (omega) :ran (omega))

(thmz (equal (apply (zfib2) 10) 55)
      :props (zify-prop zfib2$prop))

(thmz (subset (image (zfib2)) (omega))
      :props (zify-prop zfib2$prop))

; Without :ran: no codomain obligation at all.
(zify2 zfact2 fact :dom (omega))

(thmz (in '(5 . 120) (zfact2))
      :props (zify-prop zfact2$prop))

; Default domain (acl2), with a parameter.
(zify2 zerase-atoms2a (erase-atoms tree lst))

(thmz (implies (in tree (acl2))
               (equal (apply (zerase-atoms2a lst) tree)
                      (erase-atoms tree lst)))
      :props (zify-prop zerase-atoms2a$prop v$prop acl2$prop))

; Zify2*.
(zify2* zput-assoc2* put-assoc 3 :fn* put-assoc2*)

(thmz (implies (and (in x0 (acl2)) (in x1 (acl2)) (in x2 (acl2)))
               (equal (apply (zput-assoc2*) (list x0 x1 x2))
                      (put-assoc x0 x1 x2)))
      :props (zify-prop zput-assoc2*$prop v$prop acl2$prop))

; The tests from zify.lisp, on the zify2 versions.
(thmz (equal (map (zfib2) '(0 1 2 3 4 5 6 7))
             '(0 1 1 2 3 5 8 13))
      :props (zify-prop zfib2$prop))

(defthmz map-zfib2
  (implies (nat-listp lst)
           (equal (map (zfib2) lst)
                  (map-fib lst)))
  :props (zify-prop zfib2$prop))

(thmz (equal (map (zfact2) '(2 3 4 5))
             '(2 6 24 120))
      :props (zify-prop zfact2$prop))

; The identity on (v-omega), with :props.
(zify2 identity2-fun-sv-omega identity
       :dom (v-omega)
       :ran (v-omega)
       :props (v$prop))

; Default domain, :ran (acl2): the obligation is acl2p-mirror.
(zify2 zmirror2 mirror :ran (acl2))

(thmz (subset (image (zmirror2)) (acl2))
      :props (zify-prop zmirror2$prop v$prop acl2$prop))

; Default domain, no :ran: nothing to prove about mirror.
(defun mirror-no-acl2p (x)
  (cond ((atom x) (list x))
        (t (cons (mirror-no-acl2p (cdr x))
                 (mirror-no-acl2p (car x))))))

(zify2 zmirror-no-acl2p mirror-no-acl2p)

; A parameter in the domain, and :xhyps.
(zify2 zplus2 (binary-+ n k)
       :dom (omega)
       :ran (omega)
       :xhyps ((natp k)))

(thmz (implies (natp k)
               (subset (image (zplus2 k)) (omega)))
      :props (zify-prop zplus2$prop))

; As for zify, the :xhyps are hypotheses of all the generated theorems.
(thmz (implies (and (in n (omega))
                    (natp k))
               (equal (apply (zplus2 k) n) (+ n k)))
      :props (zify-prop zplus2$prop))

(encapsulate
  ()
  (local (include-book "set-algebra"))
  (local (defun erase-atoms3 (tree lst d)
           (declare (xargs :guard (true-listp lst)) (irrelevant d))
           (cond ((atom tree)
                  (if (member-equal tree lst)
                      nil
                    tree))
                 (t (cons (erase-atoms3 (car tree) lst d)
                          (erase-atoms3 (cdr tree) lst d))))))
  (local (defthm acl2p-erase-atoms3
           (implies (acl2p tree)
                    (acl2p (erase-atoms3 tree lst d)))))
  (local (zify2 zerase-atoms3 (erase-atoms3 tree lst d)
                :dom (int2 d (acl2))
                :ran (acl2)
                :props (acl2$prop v$prop diff$prop))))

; The zify* tests.
(zify2* zf0-2* f0 3 :fn* f0-2*
        :props (prod2$prop domain$prop inverse$prop zfc))
(zify2* zmirror2* mirror 1 :fn* mirror2*)
(zify2 zf1-2 f1)
(zify2* zf2-2* f2 2 :fn* f2-2* :ran (prodn* 3 (acl2)))

; Multiple values, with :ran.
(zify2 zf1-2r f1 :ran (acl2))

; A parameter named x, the variable of the generic events.
(zify2 zplus2x (binary-+ n x) :dom (omega))
