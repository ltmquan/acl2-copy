; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Zify2: a zify built on zfn (Replacement) instead of zsub (Separation).

; (zify2 NAME (FN x v2 ... vk) :dom DOM [:ran RAN] ...) introduces
; (NAME v2 ... vk . args), a set-theoretic function with domain DOM that agrees
; with FN on DOM, by way of
;   (zfn NAME (v2 ... vk . args) x y DOM (equal (equal y (FN x v2 ... vk)) t)).
; That relation always has a witness y, so the domain is exactly DOM with no
; hypotheses about FN.  A codomain is needed only for the image theorem, so
; :ran is optional: when it is supplied, the user's theory must prove that FN
; maps DOM into RAN (under :xhyps), and we export (subset (image call) RAN).

; Generated events, with call = (NAME v2 ... vk . args) and H the forced
; hypotheses (NAME$prop), (zify-prop) and the :props:
;   funp-NAME          (funp call)
;   domain-NAME        H => (domain call) = DOM
;   NAME-is-FN         H & (in x DOM) => (apply call x) = (FN x v2 ... vk)
;   in-NAME            H => (in p call) = (consp p) & (car p) in DOM
;                                         & (cdr p) = (FN (car p) v2 ... vk)
; and, only when :ran is supplied:
;   NAME-maps-to-ran   H & xhyps & (in x DOM) => (in (FN x v2 ... vk) RAN)
;   image-NAME         H & xhyps => (subset (image call) RAN)

; All but NAME-maps-to-ran are functional instances of the generic theorems
; below, proved in a minimal theory, so nothing depends on how DOM or FN
; rewrite.

(in-package "ZF")

; We reuse acl2, zify-prop, the argument checks, and prodn* from zify.
(include-book "zify")

;;; The generic function.  Its constraints are what zfn exports for
;;; (zfn g2-rel () x y (g2-dom) (equal (equal y (g2-fn x)) t)), with y
;;; instantiated: by (g2-fn x) in $domain-2 and by the value of apply in
;;; $chooses.  Zify2 proves those two instances per function (NAME$in-domain
;;; and NAME$apply below), by :use, so no rule with a free y is ever needed.

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
                     (g2-dom)))
    :hints (("Goal" :in-theory (enable domain-0))))
  (defthm g2-rel$in-domain
    (implies (and (in x (g2-dom))
                  (force (g2-prop)))
             (in x (domain (g2-rel)))))
  (defthm g2-rel$apply
    (implies (and (in x (domain (g2-rel)))
                  (force (g2-prop)))
             (equal (apply (g2-rel) x)
                    (g2-fn x)))))

(defthm domain-g2-rel
  (implies (and (force (g2-prop))
                (force (zify-prop)))
           (equal (domain (g2-rel))
                  (g2-dom)))
  :hints (("Goal"
           :expand ((subset (g2-dom) (domain (g2-rel))))
           :in-theory (enable extensionality-rewrite))))

(defthm g2-rel-is-g2-fn
  (implies (and (in x (g2-dom))
                (force (g2-prop))
                (force (zify-prop)))
           (equal (apply (g2-rel) x)
                  (g2-fn x))))

(defthm in-g2-rel
  (implies (and (force (g2-prop))
                (force (zify-prop)))
           (equal (in p (g2-rel))
                  (and (consp p)
                       (in (car p) (g2-dom))
                       (equal (cdr p) (g2-fn (car p))))))
  :hints (("Goal" :use ((:instance apply-intro (f (g2-rel)))))))

;;; The codomain, for the image theorem.  Its constraint is the user's
;;; obligation NAME-maps-to-ran.

(encapsulate
  (((g2-ran) => *))
  (local (defun g2-ran () (image (g2-rel))))
  (defthm g2-fn-maps-to-g2-ran
    (implies (and (in x (g2-dom))
                  (g2-prop)
                  (zify-prop))
             (in (g2-fn x) (g2-ran)))
    :hints (("Goal"
             :use ((:instance in-apply-image (r (g2-rel)))))))
  (in-theory (disable g2-fn-maps-to-g2-ran)))

(defthm image-g2-rel
  (implies (and (force (g2-prop))
                (force (zify-prop)))
           (subset (image (g2-rel)) (g2-ran)))
  :hints (("Goal"
           :expand ((subset (image (g2-rel)) (g2-ran)))
           :use ((:instance in-image-necc
                            (f (g2-rel))
                            (x (subset-witness (image (g2-rel)) (g2-ran))))
                 (:instance g2-fn-maps-to-g2-ran
                            (x (apply (inverse (g2-rel))
                                      (subset-witness (image (g2-rel))
                                                      (g2-ran)))))))))

;;; The macro

(defun zify2-fi (thm prop dom call x fx extra)
  (declare (xargs :guard t))
  `(:functional-instance
    ,thm
    (g2-prop (lambda () ,prop))
    (g2-dom (lambda () ,dom))
    (g2-rel (lambda () ,call))
    (g2-fn (lambda (,x) ,fx))
    ,@(and (true-listp extra) extra)))

(defun zify2-fn (name fn dom ran props xhyps args var verbose out)

; Out is the number of values that fn returns.  Zfn puts its relation in a
; defun body, where a call of a multiple-value fn must be wrapped in mv-list.

  (declare (xargs :guard t))
  (let* ((name0 name)
         (name (and (symbolp name) name))
         (props0 props)
         (props (and (symbol-listp props) props))
         (props (if (null dom)

; As for zify: the right default for the common case, where dom defaults to
; (acl2).

                    (append '(v$prop acl2$prop) props)
                  props))
         (xhyps (and (true-listp xhyps) xhyps))
         (fn-args (cond ((symbolp fn)
                         (list (suffix-symbol "-ARG" fn)))
                        ((symbol-listp fn)
                         (cdr fn))
                        (t nil)))
         (fn0 fn)
         (fn (cond ((symbolp fn) fn)
                   ((symbol-listp fn) (car fn))
                   (t nil)))
         (x (car fn-args))
         (fn-params (cdr fn-args))
         (dom (or dom '(acl2)))
         (name$prop (and name (suffix-symbol "$PROP" name)))
         (y (and name (suffix-symbol "$Y" name)))
         (all-args (append fn-params (and (symbol-listp args) args)))
         (call (cons name all-args))
         (fx `(,fn ,@fn-args))
         (fxl (if (and (natp out) (< 1 out))
                  `(mv-list ,out ,fx)
                fx))
         (name$in-domain (and name (packn (list name '$in-domain))))
         (name$apply (and name (packn (list name '$apply))))
         (zfn-rules (and name
                         (list (packn (list name '$funp))
                               (packn (list name '$domain-1))
                               name$in-domain
                               name$apply)))
         (min-theory '(union-theories '(force mv-list) (theory 'minimal-theory)))

; The generic prop is (NAME$prop) and the props, plus the xhyps for the image
; theorem.

         (gprop (if props
                    `(and (,name$prop) ,@(props-to-hyps props))
                  `(,name$prop)))
         (gprop-ran (if xhyps
                        `(and ,gprop ,@xhyps)
                      gprop))
         (maps-name (suffix-symbol "-MAPS-TO-RAN" name))
         (theory `(union-theories '(force mv-list zify-prop ,@zfn-rules)
                                  (theory 'minimal-theory)))
         (form
          `(progn
             (check-zify ,name0 ,fn0 ,dom ,ran ,props0 ,xhyps ,all-args ,var)
             (check-arity ,fn ,(len fn-args))

; Zfn proves its constraints for the local witness (all zero) in the current
; theory, where rules about DOM may fire first and force props it cannot
; relieve, for example v$prop for (v-omega).  So we admit it in a minimal
; theory.

             (encapsulate
               ()
               (local (in-theory (union-theories '(domain-0 subset-0 funp-0)
                                                 (theory 'minimal-theory))))
               (zfn ,name ,all-args ,x ,y ,dom
                    (equal (equal ,y ,fxl) t)))

             (defthmd ,name$in-domain
               (implies (and (in ,x ,dom)
                             (force (,name$prop)))
                        (in ,x (domain ,call)))
               :hints (("Goal"
                        :use ((:instance ,(packn (list name '$domain-2))
                                         (,y ,fxl)))
                        :in-theory ,min-theory)))

             (defthmd ,name$apply
               (implies (and (in ,x (domain ,call))
                             (force (,name$prop)))
                        (equal (apply ,call ,x) ,fxl))
               :hints (("Goal"
                        :use ((:instance ,(packn (list name '$chooses))
                                         (,y (apply ,call ,x))))
                        :in-theory ,min-theory)))

             (defthm ,(prefix-symbol "FUNP-" name)
               (funp ,call))

             (defthm ,(prefix-symbol "DOMAIN-" name)
               (implies (and (force ,gprop)
                             (force (zify-prop)))
                        (equal (domain ,call) ,dom))
               :hints (("Goal" :use ,(zify2-fi 'domain-g2-rel gprop dom call x fxl nil)
                         :in-theory ,theory)))

             (defthm ,(suffix-symbol (concatenate 'string "-IS-"
                                                  (symbol-name fn))
                                     name)
               (implies (and (in ,x ,dom)
                             (force ,gprop)
                             (force (zify-prop)))
                        (equal (apply ,call ,x) ,fx))
               :hints (("Goal" :use ,(zify2-fi 'g2-rel-is-g2-fn gprop dom call x fxl nil)
                         :in-theory ,theory)))

             (defthm ,(prefix-symbol "IN-" name)
               (implies (and (force ,gprop)
                             (force (zify-prop)))
                        (equal (in ,var ,call)
                               (and (consp ,var)
                                    (in (car ,var) ,dom)
                                    (equal (cdr ,var)
                                           (,fn (car ,var) ,@fn-params)))))
               :hints (("Goal" :use ,(zify2-fi 'in-g2-rel gprop dom call x fxl nil)
                         :in-theory ,theory)))

             ,@(and ran
                    `((defthm ,maps-name
                        (implies (and (in ,x ,dom)
                                      ,gprop-ran
                                      (zify-prop))
                                 (in ,fx ,ran)))

                      (defthm ,(prefix-symbol "IMAGE-" name)
                        (implies (and (force ,gprop-ran)
                                      (force (zify-prop)))
                                 (subset (image ,call) ,ran))
                        :hints
                        (("Goal"
                          :use ,(zify2-fi 'image-g2-rel gprop-ran dom call x fxl
                                        `((g2-ran (lambda () ,ran))))
                          :in-theory (union-theories '(,maps-name)
                                                     ,theory))))))
             (value-triple ',name))))
    (cond (verbose form)
          (t `(with-output :off (:other-than error) :gag-mode nil
                ,form)))))

(defun zify2-out-arity (fn wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (let ((f (if (consp fn) (car fn) fn)))
    (if (symbolp f)
        (len (getpropc f 'acl2::stobjs-out '(nil) wrld))
      1)))

(defmacro zify2 (name fn &key dom ran props xhyps args (var 'p) verbose)
  (declare (xargs :guard t))
  `(make-event
    (value (zify2-fn ',name ',fn ',dom ',ran ',props ',xhyps ',args ',var
                     ',verbose (zify2-out-arity ',fn (w state))))
    :on-behalf-of :quiet))

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

(thmz (implies (in n (omega))
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
