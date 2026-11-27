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

(defun thmz-quantifiers-fn (event)
  (declare (xargs :mode :program))
  (let ((pos (if (eq (car event) 'thmz) 1 2)))
    (if (zq-has-quantifier (nth pos event))
        `(make-event
          (er-let* ((pr (elab-quantifiers ',(nth pos event) nil
                                          ',(car event) state)))
            (value (cons 'progn
                         (append (cdr pr)
                                 (list (thmz-fn (update-nth ,pos (car pr)
                                                            ',event))))))))
      (thmz-fn event))))

(defmacro thmz (&whole ev &rest args)
  (declare (ignore args))
  (thmz-quantifiers-fn ev))

(defmacro defthmz (&whole ev &rest args)
  (declare (ignore args))
  (thmz-quantifiers-fn ev))

(defmacro defthmdz (&whole ev &rest args)
  (declare (ignore args))
  (thmz-quantifiers-fn ev))

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

; Matt's base.lisp also accepts entries justified by the scheme macros zsub
; and zfn here, checking that the named event is the one the macro would
; produce.  Those macros are to be redesigned, and their cases will come back
; with them.

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
