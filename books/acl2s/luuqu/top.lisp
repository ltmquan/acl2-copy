; top.lisp - Phase 2: ACL2s + local LLM integration
; Book: ~/Documents/acl2-copy/books/acl2s/luuqu/top.lisp

(in-package "ACL2S")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Section 1: Includes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(include-book "tools/include-raw"             :dir :system)
(include-book "kestrel/utilities/checkpoints" :dir :system :ttags :all)
;(include-book "acl2s/cgen/top"               :dir :system :ttags :all)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Section 2: Ttag + Raw Lisp Load
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; defttag establishes the trust tag required for include-raw and defun-bridge.
; subsume-ttags-since-defttag tells ACL2 the defttag covers subsequent tagged ops.
(defttag :acl2s-llm)
(acl2::subsume-ttags-since-defttag)

; (depends-on "suggest-raw.lsp")
; include-raw path is relative to this book's directory.
; :host-readtable t required because suggest-raw.lsp uses ql: and cl-llama:
; package prefixes that the ACL2 readtable cannot handle.
; The model loads at this point as a side effect of loading suggest-raw.lsp.
(acl2::include-raw "suggest-raw.lsp" :host-readtable t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Section 3: query-ai Bridge
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The single raw-Lisp surface. The :program body is a safe stub
; returned when raw Lisp is not loaded.
; The :raw body calls query-ai-raw defined in suggest-raw.lsp.
;
; Returns: (mv erp form)   -- no state; query-ai-raw does not use it
;   erp  = nil   -> form is a parsed Lisp s-expression (any s-expr)
;   erp  = string -> model/parse error; form is nil
;
; NOTE: Shape check (consp + car = 'property) is done on the ACL2 side
; in ai-property-orchestrate, NOT in raw Lisp.
; NOTE: defun-bridge auto-generates (declare (xargs :mode :program)); adding
; a second xargs via :program-declare causes ACL2 to reject. State is omitted
; since query-ai-raw ignores it, eliminating the stobjs-declare problem.
(acl2::defun-bridge query-ai (defs theorem checkpoint)
  :program (mv "raw Lisp not loaded" nil)
  :raw (query-ai-raw defs theorem checkpoint))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Section 4: AI Automation Global Flag
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Stored in an ACL2 table so it integrates with undo/revert machinery.
(table ai-automation-table :enabled nil)

; User-facing control: (set-ai-automation t) or (set-ai-automation nil).
(defmacro set-ai-automation (flag)
  `(table ai-automation-table :enabled ,flag))

; Read the current flag value in program-mode code.
(defun ai-automation-enabled-p (state)
  (declare (xargs :mode :program :stobjs (state)))
  (cdr (assoc :enabled (table-alist 'ai-automation-table (w state)))))

; Summary mode: suppress raw proof output, emit structured report instead.
(table ai-summary-table :enabled nil)

(defmacro set-ai-summary (flag)
  `(table ai-summary-table :enabled ,flag))

(defun ai-summary-enabled-p (state)
  (declare (xargs :mode :program :stobjs (state)))
  (cdr (assoc :enabled (table-alist 'ai-summary-table (w state)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Section 5: String Utilities + Definition Extraction Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Remove every occurrence of sub from str.
; Uses length as the decreasing measure; terminates because each call
; either skips 1 character or skips (length sub) characters.
(defun string-remove-all (str sub)
  (declare (xargs :mode :program))
  (let* ((slen   (length str))
         (sublen (length sub)))
    (cond ((< slen sublen) str)
          ((equal (subseq str 0 sublen) sub)
           (string-remove-all (subseq str sublen slen) sub))
          (t (concatenate 'string
                          (subseq str 0 1)
                          (string-remove-all (subseq str 1 slen) sub))))))

; Like acl2::fms-to-string but strips "ACL2S::" package qualifiers.
; fms-to-string with ~x0 includes package prefixes for ACL2S symbols,
; which confuses the model since it has never seen that format.
(defun acl2s-fms-to-string (fmt-str alist)
  (declare (xargs :mode :program))
  (string-remove-all (acl2::fms-to-string fmt-str alist) "ACL2S::"))

; Check if fn is a user-defined function with a visible body.
; Built-in primitives either have predefined=t or no unnormalized-body.
(defun user-defined-fn-p (fn state)
  (declare (xargs :mode :program :stobjs (state)))
  (let ((wrld (w state)))
    (and (symbolp fn)
         (not (getpropc fn 'acl2::predefined nil wrld))
         (consp (getpropc fn 'acl2::unnormalized-body nil wrld)))))

; Pretty-print one function's definition to a string.
(defun fn-def-to-string (fn state)
  (declare (xargs :mode :program :stobjs (state)))
  (let* ((wrld    (w state))
         (formals (getpropc fn 'acl2::formals nil wrld))
         (body    (getpropc fn 'acl2::unnormalized-body nil wrld))
         (ubody   (acl2::untranslate body nil wrld)))
    (acl2s-fms-to-string "~x0" (list (cons #\0 `(defun ,fn ,formals ,ubody))))))

; Filter a list of function symbols to those that are user-defined.
(defun filter-user-fns (fns state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp fns)
      nil
    (if (user-defined-fn-p (car fns) state)
        (cons (car fns) (filter-user-fns (cdr fns) state))
      (filter-user-fns (cdr fns) state))))

; Concatenate definition strings for a list of functions.
(defun fn-def-strings (fns state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp fns)
      ""
    (concatenate 'string
                 (fn-def-to-string (car fns) state)
                 (string #\Newline)
                 (fn-def-strings (cdr fns) state))))

; Fallback function-name collector that works on raw surface forms.
; Used if acl2::all-fnnames requires a properly translated term.
; Mutually recursive: collect-fn-syms over a form, collect-fn-syms-lst over args.
(mutual-recursion
 (defun collect-fn-syms (form acc)
   (declare (xargs :mode :program))
   (cond ((atom form) acc)
         ((eq (car form) 'quote) acc)
         (t (collect-fn-syms-lst (cdr form)
                                 (if (symbolp (car form))
                                     (add-to-set-eq (car form) acc)
                                   acc)))))
 (defun collect-fn-syms-lst (lst acc)
   (declare (xargs :mode :program))
   (if (endp lst)
       acc
     (collect-fn-syms-lst (cdr lst)
                          (collect-fn-syms (car lst) acc)))))

; Given the theorem body (surface syntax), collect user function defs as a string.
; Tries pseudo-translate + all-fnnames first; falls back to collect-fn-syms.
(defun collect-defs-string (body state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (
       ; try to translate body to extract function names; erp=nil means success
       ((mv erp translated) (acl2::pseudo-translate body nil (w state)))
       ; fall back to surface-syntax scan if translation failed
       (fns (if erp
                (collect-fn-syms body nil)
              (acl2::all-fnnames translated))))
    (fn-def-strings (filter-user-fns fns state) state)))

; Print one checkpoint entry in ACL2 style: clause-id label then prettyified formula.
; entry is one alist from checkpoint-info-list: keys :clause-id and :clause.
(defun print-one-chk-entry (entry state)
  (declare (xargs :mode :program :stobjs (state)))
  (let* ((clause-id (cdr (assoc :clause-id entry)))
         (clause    (cdr (assoc :clause entry)))
         (id-str    (acl2::string-for-tilde-@-clause-id-phrase clause-id))
         (pretty    (acl2::prettyify-clause clause (acl2::let*-abstractionp state) (w state))))
    (cw "~%~s0~%~x1~%" id-str pretty)))

; Iterate over a checkpoint info-list printing each entry.
(defun print-chk-entries (info-list state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp info-list)
      nil
    (prog2$ (print-one-chk-entry (car info-list) state)
            (print-chk-entries (cdr info-list) state))))

; Print one checkpoint section with an ACL2-style "*** Key checkpoint ***" header.
; info-list is the result of checkpoint-info-list (may be :unavailable or nil).
(defun print-chk-section (label info-list state)
  (declare (xargs :mode :program :stobjs (state)))
  (prog2$
    (cw "~%*** Key checkpoint ~s0 ***~%" label)
    (if (or (eq info-list :unavailable) (null info-list))
        (cw " (none)~%")
      (print-chk-entries info-list state))))

; Print both checkpoint stacks (top-level and under induction) with ACL2-style headers.
; top-info and sub-info are results of checkpoint-info-list.
(defun print-checkpoints (top-info sub-info state)
  (declare (xargs :mode :program :stobjs (state)))
  (prog2$
    (print-chk-section "at the top level:" top-info state)
    (print-chk-section "under a top-level induction:" sub-info state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Section 6: Core Orchestration
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ai-try-proof: probe prop-form inside a reverted world.
; Returns (mv failed-p chk-list state). World is always clean on return.
; The checkpoint survives the revert via gag-state-saved (a state global).
; When suppress=t, wraps output to silence proof chatter.
(defun ai-try-proof (prop-form ctx suppress state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (
       ; probe the proof in a reverted world; world is always clean on return
       ((mv proof-erp & state)
        (revert-world
          (acl2::trans-eval
            (if suppress
                `(with-output :off :all :inhibit-er-hard t
                   (with-output :gag-mode t ,prop-form))
              `(with-output :gag-mode t ,prop-form))
            ctx state t)))
       ; collect post-induction checkpoints left after the attempt
       (chk-list (acl2::checkpoint-list-pretty nil state))
       ; proof failed if trans-eval errored or open checkpoints remain
       (failed-p  (or proof-erp
                      (and (not (eq chk-list :unavailable))
                           (consp chk-list)))))
    (mv failed-p chk-list state)))

; filter-property-forms: keep only well-formed (property ...) forms from a list.
(defun filter-property-forms (forms)
  (declare (xargs :mode :program))
  (if (endp forms)
      nil
    (if (and (consp (car forms)) (eq (caar forms) 'property))
        (cons (car forms) (filter-property-forms (cdr forms)))
      (filter-property-forms (cdr forms)))))

; ai-call-model: call the AI and shape-check the result.
; Returns (mv erp raw-form) where raw-form is a (property ...) form.
;   erp = nil    -> raw-form is a well-formed (property ...) form
;   erp = string -> model/parse error or bad shape; raw-form is nil
(defun ai-call-model (defs-str thm-str chk-str)
  (declare (xargs :mode :program))
  (b* (
       ; call the model; query-ai returns (mv erp form)
       ((mv ai-erp raw-form) (query-ai defs-str thm-str chk-str))
       ; bail early if the model returned an error
       ((when ai-erp) (mv ai-erp nil))
       ; check the form is a well-formed (property ...) form
       ((when (not (and (consp raw-form) (eq (car raw-form) 'property))))
        (mv (acl2s-fms-to-string
             "AI output was not a valid (property ...) form: ~x0"
             (list (cons #\0 raw-form))) nil)))
    (mv nil raw-form)))

; ai-admit-and-check: admit raw-form via skip-proofs and verify it landed in the world.
; Returns (value nil) on success; (mv t nil state) on failure to stop er-progn.
(defun ai-admit-and-check (raw-form ctx state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (
       ; admit the suggested lemma silently via skip-proofs
       ((mv admit-erp & state)
        (acl2::trans-eval `(with-output :off :all! (skip-proofs ,raw-form)) ctx state t))
       ; extract the lemma name from the (property name ...) form
       (lemma-name (and (consp raw-form)
                        (consp (cdr raw-form))
                        (cadr raw-form)))
       ; verify the lemma actually landed in the world after admission
       (in-world-p (and lemma-name
                        (symbolp lemma-name)
                        (consp (acl2::getpropc
                                 lemma-name 'acl2::theorem nil (w state)))))
       ; admitted and in world: return success
       ((when (and (not admit-erp) in-world-p)) (value nil))
       ; otherwise report failure; (mv t nil state) stops er-progn
       (- (cw "Validation: Suggested lemma failed admission check.~%")))
    (mv t nil state)))

; ai-retry-and-report: retry the original proof with the suggested lemma in scope.
; Reports whether the proof closes or still fails; always returns (value nil).
(defun ai-retry-and-report (raw-form prop-form ctx summary-p state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (
       ; retry the original proof with the lemma now in scope
       ((mv retry-erp & state)
        (acl2::trans-eval
          `(with-output :off :all :inhibit-er-hard t
             (with-output :gag-mode t ,prop-form))
          ctx state t))
       ; collect post-induction checkpoints after the retry
       (retry-chk (acl2::checkpoint-list-pretty nil state))
       ; retry succeeded if no error and no open checkpoints remain
       (retry-ok  (and (not retry-erp)
                       (or (eq retry-chk :unavailable)
                           (null retry-chk))))
       ; announce success and usage instructions if proof closes
       (- (and retry-ok (cw "Validation: Proof closes with suggested lemma!~%")))
       (- (and retry-ok (cw "To use: first prove the lemma, then re-submit:~%")))
       (- (and retry-ok (cw " -- ~x0~%" raw-form)))
       ((when retry-ok) (value nil))
       ; proof still fails: report
       (- (cw "Validation: Proof still fails with suggested lemma.~%")))
    (value nil)))

; ai-validate-pipeline: chains admit-and-check then retry-and-report via er-progn.
; If admission fails, er-progn stops and retry is skipped entirely.
(defun ai-validate-pipeline (raw-form prop-form ctx summary-p state)
  (declare (xargs :mode :program :stobjs (state)))
  (er-progn
    (ai-admit-and-check raw-form ctx state)
    (ai-retry-and-report raw-form prop-form ctx summary-p state)))

; ai-validate-lemma: runs ai-validate-pipeline inside a reverted world.
; World is clean on return; callers ignore the first two values.
(defun ai-validate-lemma (raw-form prop-form ctx summary-p state)
  (declare (xargs :mode :program :stobjs (state)))
  (er-progn
    (revert-world (ai-validate-pipeline raw-form prop-form ctx summary-p state))
    (value nil)))

; ai-validate-silent: admit raw-form via skip-proofs then retry prop-form.
; Returns (value (list val-ok top-info sub-info)) where val-ok=t means the
; proof closed with the admitted lemma, and top-info/sub-info are the
; checkpoint-info-lists from the retry attempt (for display when val-ok=nil).
; No cw output. Caller must wrap in revert-world.
(defun ai-validate-silent (raw-form prop-form ctx state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (
       ((mv admit-erp & state)
        (acl2::trans-eval `(skip-proofs ,raw-form) ctx state t))
       (lemma-name (and (consp raw-form) (consp (cdr raw-form)) (cadr raw-form)))
       (in-world-p (and (not admit-erp)
                        lemma-name
                        (symbolp lemma-name)
                        (consp (acl2::getpropc lemma-name 'acl2::theorem nil (w state)))))
       ((when (not in-world-p)) (value (list nil :unavailable :unavailable)))
       ((mv retry-erp & state)
        (acl2::trans-eval `(with-output :gag-mode t ,prop-form) ctx state t))
       (retry-top  (acl2::checkpoint-info-list t   state))
       (retry-sub  (acl2::checkpoint-info-list nil state))
       ; Robust success check: verify prop-form's theorem landed in the world.
       ; A HARD ACL2 ERROR (e.g., call-depth limit from a looping rewrite rule)
       ; bypasses retry-erp and leaves no checkpoints, so retry-erp=nil and
       ; retry-sub=nil — indistinguishable from success without this world check.
       (prop-name     (and (consp prop-form) (consp (cdr prop-form)) (cadr prop-form)))
       (prop-proved-p (and (not retry-erp)
                           prop-name
                           (symbolp prop-name)
                           (consp (acl2::getpropc prop-name 'acl2::theorem nil (w state)))))
       (val-ok        (and prop-proved-p
                           (or (eq retry-sub :unavailable) (null retry-sub)))))
    (value (list val-ok retry-top retry-sub))))

; ai-try-one-candidate: run cgen + validation for a single candidate form.
; Returns (mv raw-form cts-found val-ok retry-top retry-sub state).
; No cw output; caller is responsible for candidate header.
(defun ai-try-one-candidate (raw-form prop-form ctx summary-p state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (
       ; cgen plausibility check — prints freely, inside revert-world
       ((mv cts-found & state)
        (if summary-p
            (revert-world (test?-fn1 raw-form nil nil state))
          (mv nil nil state)))
       ; counterexample found: no point validating
       ((when cts-found) (mv raw-form t nil :unavailable :unavailable state))
       ; validation — prints freely, inside revert-world
       ((mv & val-result state)
        (revert-world (ai-validate-silent raw-form prop-form ctx state)))
       (val-ok         (car   val-result))
       (retry-top-info (cadr  val-result))
       (retry-sub-info (caddr val-result)))
    (mv raw-form nil val-ok retry-top-info retry-sub-info state)))

; ai-property-fn: top-level AI pipeline.
; Called by ai-property when both the global flag and :ai t are active.
; Runs all trans-eval operations first (ACL2s prints freely), then prints
; the complete AI summary block at the end as one clean readable section.
; Always returns (value '(value-triple :invisible)) — purely advisory, world unchanged.
(defun ai-property-fn (name vars body stripped-args state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (
       (prop-form (list* 'property name vars body stripped-args))
       (ctx       'ai-property)
       (summary-p (ai-summary-enabled-p state))
       ; Step 1: initial proof — no suppression, ACL2s prints freely
       ((mv failed-p chk-list state) (ai-try-proof prop-form ctx nil state))
       ; proof succeeded without AI; world is clean (revert-world in ai-try-proof)
       ((when (not failed-p)) (value '(value-triple :invisible)))
       ; Capture initial checkpoint info NOW — gag-state-saved is overwritten by Step 6
       (init-top-info (acl2::checkpoint-info-list t   state))
       (init-sub-info (acl2::checkpoint-info-list nil state))
       ; Step 2: stringify the first checkpoint for the model prompt
       (chk-str (and (consp chk-list)
                     (acl2s-fms-to-string "~x0" (list (cons #\0 (car chk-list))))))
       ; Step 3: collect defs and stringify theorem for the prompt
       (defs-str (collect-defs-string body state))
       (thm-str  (acl2s-fms-to-string "~x0" (list (cons #\0 prop-form))))
       ; Step 4: query model — returns a single (property ...) form
       ((mv ai-erp raw-form) (if chk-str
                                 (ai-call-model defs-str thm-str chk-str)
                               (mv "no checkpoint available" nil)))
       ; Steps 5-6: cgen plausibility check + validation
       ((mv & cts-found val-ok retry-top-info retry-sub-info state)
        (if ai-erp
            (mv nil nil nil :unavailable :unavailable state)
          (ai-try-one-candidate raw-form prop-form ctx summary-p state)))
       ; Step 7: print entire AI summary block after all proof output
       (- (cw "~%"))
       (- (cw? summary-p "**Summary of AI Assistance**~%"))
       (- (cw? summary-p "Proof of ~x0 failed.~%" name))
       (- (and summary-p (print-checkpoints init-top-info init-sub-info state)))
       (- (if ai-erp
              (cw "AI query failed: ~s0~%" ai-erp)
            (cw "Suggested lemma:~% -- ~x0~%" raw-form)))
       (- (and summary-p (not ai-erp) raw-form
               (cw "Plausibility check (cgen): ~s0~%"
                   (if cts-found
                       "Counterexample found -- lemma may be wrong."
                     "No counterexample found -- lemma looks plausible."))))
       (- (and (not ai-erp) raw-form
               (if val-ok
                   (cw "Validation: Proof closes with suggested lemma!~%To use: first prove the lemma, then re-submit:~% -- ~x0~%" raw-form)
                 (cw "Validation: Proof still fails with suggested lemma.~%"))))
       (- (and (not ai-erp) raw-form (not val-ok) summary-p
               (print-checkpoints retry-top-info retry-sub-info state))))
    ; Proof failed — do not re-submit prop-form via make-event.
    ; Returning :invisible lets make-event succeed silently; the property is
    ; not in the world (correct: it wasn't proved). The user follows the AI
    ; instructions to prove the suggested lemma, then re-submits.
    (value '(value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Section 7: ai-property Macro
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ai-property behaves exactly like property unless:
;   (a) :ai t is present in the form, AND
;   (b) (set-ai-automation t) has been called in the session.
;
; The :ai keyword is stripped before forwarding to property.
; Double opt-in: :ai t in code is harmless when the global is off.
(defmacro ai-property (name vars body &rest kwd-args)
  (b* (
       ; extract the :ai keyword value (t or nil/absent)
       (ai-flag    (cadr (acl2::assoc-keyword :ai kwd-args)))
       ; strip :ai from the keyword list before forwarding to property
       (clean-args (acl2::remove-keyword :ai kwd-args))
       )
    (if (not ai-flag)
        ;; Fast path: :ai nil or absent -> plain property, zero overhead.
        `(property ,name ,vars ,body ,@clean-args)
      ;; :ai t -> check global flag at runtime inside make-event.
      `(make-event
         (if (ai-automation-enabled-p state)
             ;; Global on + :ai t -> full pipeline.
             (ai-property-fn ',name ',vars ',body ',clean-args state)
           ;; Global off -> plain property.
           (value '(property ,name ,vars ,body ,@clean-args)))))))
