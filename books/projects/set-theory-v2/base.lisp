; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

; Experiment: definitions here use defunz, and quantified statements use
; forall and exists directly (see quantifiers.lisp), so there are no auxiliary
; defun-sks such as Matt's in-in.
(include-book "quantifiers")

;;; This is the core of Matt Kaufmann's projects/set-theory/base.lisp, kept as
;;; the starting point for a redesign (see NOTES.md): the Preliminaries
;;; (including thmz, defthmz and defthmdz), the Primitives (the axioms, and the
;;; ztriple encoding of ACL2 atoms), and the zfc table without the scheme
;;; macros zsub and zfn, which are to be redesigned.

;;; TABLE OF CONTENTS:
;;; Preliminaries
;;; Primitives
;;; Zfc-table

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Preliminaries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun char-listp0 (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (characterp (car x))
           (char-listp0 (cdr x)))
    (equal x 0)))

(defun make-listp0 (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x)
            (make-listp0 (cdr x)))
    0))

(defun prefix-symbol (prefix sym)
  (declare (type string prefix)
           (type symbol sym))
  (fix-intern-in-pkg-of-sym
   (concatenate 'string prefix (symbol-name sym))
   sym))

(defun suffix-symbol (suffix sym)
  (declare (type string suffix)
           (type symbol sym))
  (fix-intern-in-pkg-of-sym
   (concatenate 'string (symbol-name sym) suffix)
   sym))

(defun props-to-hyps (lst)
  (declare (xargs :guard (true-listp lst)))
  (pairlis-x2 lst nil))

(defun force-props (lst)
  (declare (xargs :guard (true-listp lst)))
  (pairlis-x1 'force
              (pairlis-x2 (props-to-hyps lst) nil)))

(defun extend-with-props (form props)
  (declare (xargs :guard (symbol-listp props)))
  (mv-let (hyps concl)
    (case-match form
      (('implies ('and . x) y)
       (mv (and (true-listp x) ; always true; needed for guard proof
                x)
           y))
      (('implies x y)
       (mv (list x) y))
      (& (mv nil form)))
    (list 'implies
          (conjoin-untranslated-terms (append hyps (force-props props)))
          concl)))

(defun unbound-keys (syms alist)
  (declare (xargs :guard (true-listp syms)))
  (cond ((endp syms) nil)
        ((hons-assoc-equal (car syms) alist) ; avoid assoc guard issue
         (unbound-keys (cdr syms) alist))
        (t (cons (car syms)
                 (unbound-keys (cdr syms) alist)))))

(defun check-props-fn (lst ctx state)

; This function references zfc-table, whose introduction is delayed until later
; below when the necessary infrastructure is available for that.

  (declare (xargs :stobjs state :guard (error1-state-p state)))
  (cond ((not (symbol-listp lst))
         (er soft ctx
             "The :props argument must be a list of symbols, but ~x0 is not."
             lst))
        ((unbound-keys lst (table-alist 'zfc-table (w state)))
         (er soft ctx
             "Every symbol in the :props argument must be a key of the table, ~
              ~x0, to indicate that it is justified by the assumption that we ~
              are working in ACL2/ZFC.  However, ~&1 ~#1~[is~/are~] not such ~
              ~#1~[a key~/keys~]."
             'zfc-table
             (unbound-keys lst (table-alist 'zfc-table (w state)))))
        (t (value nil))))

(defmacro check-props (ctx lst)
  `(make-event
    (er-progn (check-props-fn ',lst ',ctx state)
              (value '(value-triple nil)))
    :on-behalf-of :quiet
    :check-expansion t
    :expansion? (value-triple nil)))

(defun thmz-fn (event)

; Despite the name, this function may be applied to any defthmz, defthmdz, or
; thmz event, to extend its formula's hypotheses with calls of the zero-ary
; functions in its :props argument, default (zfc).

  (declare (xargs :guard (and (true-listp event)
                              (member-eq (car event)
                                         '(thmz defthmz defthmdz)))))
  (mv-let (macro-name name form1 args)
    (cond ((eq (car event) 'thmz)
           (mv 'thm nil (cadr event) (cddr event)))
          (t
           (mv (if (eq (car event) 'defthmz)
                   'defthm
                 'defthmd)
               (cadr event) (caddr event) (cdddr event))))
    (let ((p (position :props args :test 'eq)))
      (mv-let (props props-p args)
        (cond ((null p) (mv '(zfc) nil args))
              (t (mv (nth (1+ p) args)
                     t
                     (append (take p args)
                             (nthcdr (+ 2 p) args)))))
        (let ((ev `(,macro-name ,@(and name (list name))
                                ,(extend-with-props form1

; The check-props call below will guarantee that (symbol-listp props) holds
; before submitting ev.

                                                    (and (symbol-listp props)
                                                         props))
                                ,@args)))
          (cond (props-p `(progn (check-props ,(car event) ,props)
                                 ,ev))
                (t ev)))))))

(defun thmz-remove-props (args)
  (declare (xargs :mode :program))
  (cond ((or (endp args) (endp (cdr args))) args)
        ((eq (car args) :props) (cddr args))
        (t (list* (car args) (cadr args) (thmz-remove-props (cddr args))))))

(defun thmz-props-event (event pos state)

  (declare (xargs :mode :program :stobjs state))
  (let* ((wrld (w state))
         (args (nthcdr (1+ pos) event))
         (tail (assoc-keyword :props args))
         (user (cadr tail)))
    (if (or (not (assoc-eq 'zfc (table-alist 'zfc-table wrld)))
            (not (symbol-listp user)))
        (value (thmz-fn event))
      (er-let* ((tterm (acl2::translate (nth pos event) t t t (car event) wrld
                                        state)))
        (let* ((computed (zq-theorem-props tterm wrld))
               (props (cons 'zfc
                            (set-difference-eq
                             (append user (set-difference-eq computed user))
                             '(zfc)))))
          (if (and (null tail) (equal props '(zfc)))
              (value (thmz-fn event))
            (value (thmz-fn (append (take (1+ pos) event)
                                    (list :props props)
                                    (thmz-remove-props args))))))))))

(defun thmz-elaborate-event (event pos state)
  (declare (xargs :mode :program :stobjs state))
  (if (zq-has-quantifier (nth pos event))
      (er-let* ((pr (elab-quantifiers (nth pos event) nil (car event) state)))
        (let ((event2 (update-nth pos (car pr) event)))
          (if (cdr pr)
              (value `(progn ,@(cdr pr)
                             (make-event
                              (thmz-props-event ',event2 ,pos state))))
            (thmz-props-event event2 pos state))))
    (thmz-props-event event pos state)))

(defun thmz-quantifiers-fn (event)
  (declare (xargs :mode :program))
  (let ((pos (if (eq (car event) 'thmz) 1 2)))
    `(make-event (thmz-elaborate-event ',event ,pos state))))

(defmacro thmz (&whole ev &rest args)
  (declare (ignore args))
  (thmz-quantifiers-fn ev))

(defmacro defthmz (&whole ev &rest args)
  (declare (ignore args))
  (thmz-quantifiers-fn ev))

(defmacro defthmdz (&whole ev &rest args)
  (declare (ignore args))
  (thmz-quantifiers-fn ev))

(defun zq-dcl-items (dcls)
  (declare (xargs :mode :program))
  (if (endp dcls)
      nil
    (append (and (consp (car dcls))
                 (eq (car (car dcls)) 'declare)
                 (cdr (car dcls)))
            (zq-dcl-items (cdr dcls)))))

(defun zq-xargs-values (items key)
  (declare (xargs :mode :program))
  (cond ((endp items) nil)
        ((and (consp (car items))
              (eq (car (car items)) 'xargs))
         (let ((tail (assoc-keyword key (cdr (car items)))))
           (append (and tail (list (cadr tail)))
                   (zq-xargs-values (cdr items) key))))
        (t (zq-xargs-values (cdr items) key))))

(defun zq-has-type-dcl (items)
  (declare (xargs :mode :program))
  (cond ((endp items) nil)
        ((and (consp (car items))
              (eq (car (car items)) 'type))
         t)
        (t (zq-has-type-dcl (cdr items)))))

(defun zq-verify-p (items wrld)
  (declare (xargs :mode :program))
  (let ((vg (zq-xargs-values items :verify-guards)))
    (if vg
        (car (last vg))
      (let ((eagerness (acl2::default-verify-guards-eagerness wrld)))
        (cond ((eql eagerness 0) nil)
              ((eql eagerness 1)
               (or (zq-xargs-values items :guard)
                   (zq-xargs-values items :stobjs)
                   (zq-has-type-dcl items)))
              (t t))))))

(defun zq-remove-keywords (keys kv)
  (declare (xargs :mode :program))
  (cond ((or (endp kv) (endp (cdr kv))) kv)
        ((member-eq (car kv) keys) (zq-remove-keywords keys (cddr kv)))
        (t (list* (car kv) (cadr kv) (zq-remove-keywords keys (cddr kv))))))

(defun zq-strip-items (items)
  (declare (xargs :mode :program))
  (cond ((endp items) nil)
        ((and (consp (car items))
              (eq (car (car items)) 'xargs))
         (let ((kv (zq-remove-keywords '(:verify-guards :guard-hints
                                                        :guard-debug
                                                        :guard-simplify)
                                       (cdr (car items)))))
           (if kv
               (cons (cons 'xargs kv) (zq-strip-items (cdr items)))
             (zq-strip-items (cdr items)))))
        (t (cons (car items) (zq-strip-items (cdr items))))))

(defun zq-verify-guards-event (name items)
  (declare (xargs :mode :program))
  (let ((hints (zq-xargs-values items :guard-hints))
        (debug (zq-xargs-values items :guard-debug))
        (simp (zq-xargs-values items :guard-simplify)))
    `(verify-guards ,name
                    ,@(and hints `(:hints ,(car (last hints))))
                    ,@(and debug `(:guard-debug ,(car (last debug))))
                    ,@(and simp `(:guard-simplify ,(car (last simp)))))))

(defun defunz-events (name args dcls body ctx state)

; If body is a quantifier at the top (with or without quantifiers inside it),
; name itself is the defun-sk (with def::un-skd, so it is registered with
; coi), the quantifiers inside are elaborated into generated functions as
; usual, and name is entered in zq-table.  If its
; formula is already there, for an earlier function, name replaces that
; function in the table, with a warning: later quantifiers with that formula
; become calls of name, the function defined last.  Otherwise name is defined
; by defun, with the quantifiers in body elaborated.

  (declare (xargs :mode :program :stobjs state))
  (let* ((wrld (w state))
         (items (zq-dcl-items dcls))
         (verify (zq-verify-p items wrld)))
    (cond
     ((quant-form-p body)
      (let ((kind (car body))
            (bound (quant-bound-vars body)))
        (er-let* ((r (elab-q (caddr body) nil verify ctx wrld state)))
          (let ((body-new (nth 0 r))
                (body-ph (nth 1 r))
                (events (nth 3 r)))
            (er-let* ((tbody-ph (acl2::translate body-ph t nil t ctx wrld
                                                 state)))
              (let* ((key (zq-key kind bound args
                                  (placeholders-to-calls tbody-ph)))
                     (old (zq-lookup key (nth 2 r) nil wrld))
                     (new-dcls
                      (and dcls
                           `((declare ,@(zq-strip-items items)
                                      (xargs :verify-guards nil))))))
                (pprogn
                 (if old
                     (acl2::warning$ ctx "Zq"
                                     "~x0 has the same formula as ~x1, ~
                                      up to renaming of variables.  ~
                                      Quantifiers with that formula will ~
                                      now become calls of ~x0 instead of ~
                                      ~x1."
                                     name old)
                   state)
                 (value (append events
                                (zq-quant-events
                                 name args kind bound body-new key new-dcls
                                 (and verify
                                      (zq-verify-guards-event name items))
                                 nil))))))))))
     ((zsub-form-p body)
      (if dcls
          (er soft ctx
              "Declarations are not supported when the body is a zsub at ~
               the top, as for ~x0."
              name)
        (er-let* ((p (elab-zsub-parts body nil verify ctx wrld state)))
          (let* ((xv (cadr body))
                 (key (zs-key args xv (nth 2 p) (nth 3 p)))
                 (old (zs-lookup key (nth 4 p) wrld)))
            (pprogn
             (if old
                 (acl2::warning$ ctx "Zq"
                                 "~x0 is the same set as ~x1, up to renaming ~
                                  of variables.  Sets with that formula will ~
                                  now become calls of ~x0 instead of ~x1."
                                 name old)
               state)
             (value (append (nth 5 p)
                            `((zsub-define ,name ,args ,xv ,(nth 0 p)
                                           ,(nth 1 p))))))))))
     (t
      (er-let* ((pr (elab-quantifiers body verify ctx state)))
        (value (append (cdr pr)
                       `((defun ,name ,args ,@dcls ,(car pr))))))))))

(defmacro defunz (name args &rest rest)

; (defunz name args dcl ... dcl body)

  `(make-event
    (er-let* ((evs (defunz-events ',name ',args ',(butlast rest 1)
                     ',(car (last rest)) 'defunz state)))
      (value (cons 'progn evs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Primitives
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we introduce our formalization of ZFG (ZF plus Global Choice), except
; for the axiom schemes of Comprehension and (our version of) Replacement,
; which come later (see zsub and zfn).

(encapsulate
  (((zfc) => *)        ; See below.
   ((in * *) => *)     ; (in a x) <=> a \in x
   ((pair * *) => *)   ; (pair x y) = {x,y}
   ((min-in *) => *)   ; (min-in x) \in x and (min-in x) does not intersect x
                       ;   [So min-in witnesses the ZF Axiom of Regularity, but
                       ;    does so uniformly, which gives us Global Choice.
                       ;    See min-in-1 (for non-empty sets), and min-in-2.]
   ((union *) => *)    ; (union x) = union of {a: a \in x}
   ((omega) => *)      ; the set of natural numbers
   ((powerset *) => *) ; (powerset x) is the set of all subsets of x
   )

(local (defun zfc ()

; This predicate will serve as a hypothesis of many axioms and theorems.  Its
; local witness is nil so that the axioms exported here are provable
; (trivially).  A metatheoretic argument, essentially interpreting the ACL2
; primitives and "good" objects into set theory, shows how we can view zfc as
; being true.

         nil))

; The local values are what we imagine our functions returning when (zfc) is
; false.

(local (defun in (x y)
         (declare (ignore x y)
                  (xargs :guard t))
         nil))
(local (defun pair (x y)
         (declare (ignore x y)
                  (xargs :guard t))
         nil))
(local (defun min-in (x)
         (declare (ignore x)
                  (xargs :guard t))
         0))
(local (defun union (x)
         (declare (ignore x)
                  (xargs :guard t))
         nil))
(local (defun omega ()
         (declare (xargs :guard t))
         nil))
(local (defun powerset (x)
         (declare (ignore x)
                  (xargs :guard t))
         nil))

(defthm booleanp-in
  (booleanp (in x y))
  :rule-classes :type-prescription)

(defunz subset (x y)
  (forall a (implies (in a x)
                     (in a y))))

; Axiom of Extensionality: Two sets are equal iff they have the same elements.
(defthmdz extensionality
  (implies (and (subset x y)
                (subset y x))
           (equal (equal x y)
                  t)))

; We avoid errors due to guard verification depending on local events.
; This event is local to the surrounding encapsulate.
(set-verify-guards-eagerness 0)

(defunz singleton (x) ; {x} = {x,x}
  (pair x x))

(defunz union2 (x y) ; x U y = U{x,y}
  (union (pair x y)))

(defthmz min-in-1
; Regularity and global choice, part 1: (min z) is in z if z is non-empty.
  (equal (in (min-in z) z)
         (not (equal z 0))))

(defthmz min-in-2
; Regularity and global choice, part 2: intersection of z and (min z) is
; empty.
  (implies (in a z)
           (not (in a (min-in z)))))

(defthm min-in-0 ; default
  (equal (min-in 0)
         0))

(defthmz in-pair
  (equal (in a (pair x y))
         (or (equal a x)
             (equal a y))))

(defthmz in-union
  (equal (in a (union x))
         (exists y (and (in a y)
                        (in y x)))))

(defthmz infinity
  (equal (in n (omega))
         (natp n)))

(defthmz in-powerset
  (equal (in a (powerset x))
         (subset a x)))

; Embedding of ACL2 data types into the set-theoretic universe:

(defthm 0-is-emptyset ; 0 = {}
  (not (in a 0)))

(defthmdz n+1-as-union2 ; n+1 = n U {n}
  (implies (natp n)
           (equal (+ 1 n)
                  (union2 n (singleton n)))))

(defthmdz cons-as-ordered-pair

; This is based on the classic ZF definition of an ordered pair, i.e.,
; <x,y> = {{x},{x,y}}.  Cons is the ordered-pair operation.

  (equal (cons x y)
         (pair (singleton x)
               (pair x y))))

(defunz insert (x s) ; {x} U s
  (union2 (singleton x) s))

(defunz ztriple (y z) ; {0,y,z}
  (declare (xargs :guard (and (posp y)
                              (not (natp z)))))
  (insert 0 (pair y z)))

(defunz negative-int-as-ztriple (x)
  (declare (xargs :guard (and (integerp x)
                              (< x 0))))
  (ztriple 1 (cons (- x) 0)))

(defunz integer-as-ztriple (x)
  (declare (xargs :guard (integerp x)))
  (if (< x 0)
      (negative-int-as-ztriple x)
    x))

(defunz numerator-as-ztriple (x)
  (declare (xargs :guard (rationalp x)))
  (integer-as-ztriple (numerator x)))

(defunz ratio-as-ztriple (x)
  (declare (xargs :guard (and (rationalp x)
                              (not (integerp x)))))
  (ztriple 2 (cons (numerator-as-ztriple x) (denominator x))))

(defunz rational-as-ztriple (x)
  (declare (xargs :guard (rationalp x)))
  (if (integerp x)
      (integer-as-ztriple x)
    (ratio-as-ztriple x)))

(defunz complex-as-ztriple (x)
  (declare (xargs :guard (and (complex-rationalp x)
                              (not (rationalp x)))))
  (ztriple 3 (cons (rational-as-ztriple (realpart x))
                   (rational-as-ztriple (imagpart x)))))

(defunz character-as-ztriple (x)
  (declare (xargs :guard (characterp x)))
  (ztriple 4 (cons (char-code x) 0)))

(defunz string-as-ztriple (x)
  (declare (xargs :guard (stringp x)))
  (ztriple 5 (cons (make-listp0 (coerce x 'list)) 0)))

(defunz symbol-as-ztriple (x)
  (declare (xargs :guard (symbolp x)))
  (ztriple 6 (cons (string-as-ztriple (symbol-package-name x))
                   (string-as-ztriple (symbol-name x)))))

(defthmz negative-int-as-ztriple-identity
  (implies (and (integerp x)
                (< x 0))
           (equal (negative-int-as-ztriple x)
                  x)))

(defthmz integer-as-ztriple-identity
  (implies (integerp x)
           (equal (integer-as-ztriple x)
                  x)))

(defthmz ratio-as-ztriple-identity
  (implies (and (rationalp x)
                (not (integerp x)))
           (equal (ratio-as-ztriple x)
                  x)))

(defthmz rational-as-ztriple-identity
  (implies (rationalp x)
           (equal (rational-as-ztriple x)
                  x)))

(defthmz complex-as-ztriple-identity
  (implies (and (complex-rationalp x)
                (not (rationalp x)))
           (equal (complex-as-ztriple x)
                  x)))

(defthmz character-as-ztriple-identity
  (implies (characterp x)
           (equal (character-as-ztriple x)
                  x)))

(defthmz string-as-ztriple-identity
  (implies (stringp x)
           (equal (string-as-ztriple x)
                  x)))

(defthmz symbol-as-ztriple-identity
  (implies (symbolp x)
           (equal (symbol-as-ztriple x)
                  x)))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Scheme implementations:
;;;   zsub (implementing Comprehension)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun check-zsub-fn (name args x s u ctx state)
  (declare (xargs :stobjs state :guard (error1-state-p state))
           (ignore s u))
  (cond
   ((not (symbolp name))
    (er soft ctx
        "The first argument of ~x0 must be a symbol, but ~x1 is not."
        'check-zsub name))
   ((not (and (symbol-listp args)
              (no-duplicatesp-eq args)))
    (er soft ctx
        "The second argument of ~x0 must be a duplicates-free list of symbols ~
         but ~x1 is not."
        'check-zsub args))
   ((not (symbolp x))
    (er soft ctx
        "The third argument of ~x0 must be a symbol, but ~x1 is not."
        'check-zsub x))
   ((member-eq x args)
    (er soft ctx
        "The third argument of ~x0 must not be a member of the second ~
         argument, but ~x1 is a member of ~x2."
        'check-zsub x args))
   (t (value nil))))

(defmacro check-zsub (name args x s u)
  `(make-event
    (er-progn (check-zsub-fn ',name ',args ',x ',s ',u 'check-zsub state)
              (value '(value-triple nil)))
    :on-behalf-of :quiet
    :check-expansion t
    :expansion? (value-triple nil)))

(defun zsub-form-and-prop (name args x s u)
  (declare (xargs :guard t))
  (let* ((name$prop (and (symbolp name)
                         (suffix-symbol "$PROP" name)))
         (name$comprehension (and (symbolp name)
                                  (packn (list name '$comprehension)))))
    (mv `(encapsulate
           (((,name$prop) => *)
            ((,name ,@(make-list (len args) :initial-element '*)) => *))
           (check-zsub ,name ,args ,x ,s ,u)
           (local (defun ,name$prop ()
                    nil))
           (local (defun-nx ,name ,args

; We check that all free variables of a are among args, as are all free
; variables of u other than x.  We also check that x does not occur free in a.
; Note that we use defun-nx in case u is not well-formed with respect to
; multiple-value checking.  We take advantage of this use of defun-nx in
; examples involving mv near the end of zify.lisp.

                    (declare (ignorable . ,args))
                    (list (check-vars-not-free (,x) ,s)
                          (let ((,x 0))
                            (declare (ignorable ,x))
                            ,u))))
           (defthm ,name$comprehension
             (implies (force (,name$prop))
                      (equal (in ,x (,name . ,args))
                             (and (in ,x ,s)
                                  ,u)))))
        name$prop)))

(defmacro zsub-define (name args x s u &key verbose)

; We introduce a set for {x \in s: u}.

; Name is the name of a new function symbol.  X is a variable; s and u are
; untranslated terms; and args is a true list of distinct variables containing
; all the free variables of s and u except not including x.  We want to
; introduce a function f such that:

; x \in (name . args) <=> u & x \in s.

; We require that x not be free in a; otherwise the equivalence above is not as
; intended.  Of course we could in principle replace that prohibition by
; renaming x in s, but that would be awkward since s is an untranslated term.

  (declare (xargs :guard t))
  (mv-let (form prop)
    (zsub-form-and-prop name args x s u)
    (let ((ev `(progn ,form
                      (table zfc-table ',prop '(zsub ,name ,args ,x ,s ,u))
                      (value-triple ',name))))
      (cond (verbose ev)
            (t `(with-output :off (:other-than error) :gag-mode nil
                  ,ev))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Zfc-table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun all-props-calls-present-p (props-calls alist)
  (declare (xargs :guard (true-listp props-calls)))
  (cond ((endp props-calls) t)
        (t (let* ((prop-call (car props-calls))
                  (prop (case-match prop-call
                          ((prop) prop)
                          (('force (prop)) prop)
                          (& nil))))
             (and prop
                  (hons-assoc-equal prop alist)
                  (all-props-calls-present-p (cdr props-calls) alist))))))

(defun immediately-encapsulated-in-pass-2-p (fn wrld)
  (declare (xargs :mode :program))
  (let ((embedded-event-lst (acl2::global-val 'acl2::embedded-event-lst wrld)))
    (and (eq (car (car embedded-event-lst)) 'acl2::encapsulate)
         (assoc-eq fn (cadr (car embedded-event-lst)))

; See encapsulate-pass-2 in the ACL2 sources, where a comment in the call of
; process-embedded-events explains the following test to see whether the
; immediately enclosing encapsulate event is in pass 2.

         (cddr (car embedded-event-lst)))))

(defun zfc-table-guard (val key world)
  (declare (xargs :mode :program ; because of get-event
                  :guard t))
  (cond
   ((eq val t) (eq key 'zfc))
   ((not (assoc-eq 'zfc (table-alist 'zfc-table world)))
; The key, zfc, must be present before adding other props.  It's not completely
; clear that this is necessary, but since we add that key immediately after
; creating the table, this seems like a harmless check that perhaps supports
; the foundations of zfc integration with ACL2.
    nil)
   ((immediately-encapsulated-in-pass-2-p key world)
    t)
   (t (case-match val
        (('zsub name args x a u)
         (mv-let (form prop)
           (zsub-form-and-prop name args x a u)
           (and (eq key prop)
                (equal form (get-event name world)))))

        (('and . props-calls)
         (let ((ev (get-event key world)))
           (case-match ev
             (('defun !key ()
                ('declare ('xargs :guard t))
                ('and . !props-calls))
              (all-props-calls-present-p props-calls
                                         (table-alist 'zfc-table world)))
             (& nil))))
        (& nil)))))

(table zfc-table nil nil

; This table stores pairs (prop . just) where prop is a zero-ary predicate that
; holds in the ZFC/ACL2 universe and just is the justification for that claim.
; When prop is zfc, just is t; zfc is essentially built-in to hold.  Otherwise
; just is an expression that is evaluated in the table guard so as to justify
; that claim; see zfc-table-guard.

       :guard (acl2::strict-table-guard (zfc-table-guard val key world)))

(table zfc-table 'zfc t)

(defmacro extend-zfc-table (prop &rest props)

; Extend the zfc table by introducing prop as an abbreviation for the forced
; props.

  (let ((props-calls (force-props props)))
    `(progn (defun ,prop ()
              (declare (xargs :guard t))
              (and ,@props-calls))
            (in-theory (disable (:e ,prop)))
            (table zfc-table
                   ',prop
                   '(and ,@props-calls)))))
