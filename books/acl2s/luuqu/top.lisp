; top.lisp - Phase 2: ACL2s + local LLM integration
; Book: ~/Documents/acl2-copy/books/acl2s/luuqu/top.lisp

(in-package "ACL2S")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Section 1: Includes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "kestrel/utilities/checkpoints" :dir :system :ttags :all)

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
(acl2::defun-bridge query-ai (defs theorem checkpoint proven-lemmas seed verbose)
  :program (mv "raw Lisp not loaded" nil)
  :raw (query-ai-raw defs theorem checkpoint proven-lemmas seed :verbose verbose))

; Section 4 removed — no global automation flag.
; Use (auto <form>) to invoke AI proof search directly.


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

; property-form-to-defthm: convert (property name (v1 :t1 v2 :t2 ...) body) to
; the equivalent plain (defthm name prop) form.
;
; Background: ACL2s's property macro always re-enables the 'comment output channel
; inside its generated with-output forms (via :on (comment summary)).  This makes
; it impossible to suppress property's cw output via any outer with-output wrapper.
; By converting to a plain defthm — which uses the standard ACL2 event machinery
; and respects inhibit-output-lst — we can suppress all output inside trans-eval.
;
; Returns the defthm form on success, nil if the form doesn't have the expected
; (property name vars body) structure (e.g., complex multi-clause bodies).
(defun property-form-to-defthm (form state)
  (declare (xargs :mode :program :stobjs (state)))
  (and (consp form)
       (eq (car form) 'property)
       (consp (cdr form))
       (symbolp (cadr form))           ; name
       (consp (cddr form))
       (true-listp (caddr form))       ; vars list
       (consp (cdddr form))            ; body present
       (let* ((name     (cadr  form))
              (vars-lst (caddr form))
              (body     (cadddr form))
              (pkg      (current-package state))
              (wrld     (w state))
              (tbl      (table-alist 'type-metadata-table wrld))
              (atbl     (table-alist 'type-alias-table wrld))
              (vars     (evens vars-lst))
              (types    (odds  vars-lst))
              (i-types  (map-intern-types types pkg))
              (preds    (map-preds i-types tbl atbl))
              (hyp      (make-input-contract vars preds))
              (prop     (if (eq hyp t) body `(implies ,hyp ,body))))
         `(defthm ,name ,prop))))

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

; Print one validation step line in ACL2s style.
; label should be a fixed-width string with trailing spaces (padding baked in).
; ok=t prints [*], ok=nil prints [FAILED].
(defun %check-line (label ok)
  (declare (xargs :mode :program))
  (cw "~s0~s1~%" label (if ok "[*]" "[FAILED]")))

; Format a list of proven property forms into a newline-separated string
; suitable for inclusion in the AI prompt's "Proven lemmas" section.
; proven is in proved order (first proved = first in list).
(defun format-proven-str (proven)
  (declare (xargs :mode :program))
  (if (endp proven)
      ""
    (concatenate 'string
                 (acl2s-fms-to-string "~x0" (list (cons #\0 (car proven))))
                 (string #\Newline)
                 (format-proven-str (cdr proven)))))

; Print the proof sequence with 1-based indices.
(defun print-proof-seq-aux (forms idx)
  (declare (xargs :mode :program))
  (if (endp forms)
      nil
    (prog2$ (cw "  ~x0. ~x1~%" idx (car forms))
            (print-proof-seq-aux (cdr forms) (1+ idx)))))

(defun print-proof-sequence (forms)
  (declare (xargs :mode :program))
  (print-proof-seq-aux forms 1))

; Extract the body/formula expression from an event form for AI defs scanning.
; For (property name vars body ...): the 4th element is the body.
; For (defthm name prop ...): the 3rd element is the formula.
; Otherwise: fall back to the whole form (symbols still get scanned).
(defun form-proof-body (form)
  (declare (xargs :mode :program))
  (and (consp form)
       (case (car form)
         (property (and (consp (cdddr form)) (cadddr form)))
         (defthm   (and (consp (cddr form))  (caddr form)))
         (t        form))))

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

; ai-call-model: call the AI and shape-check the result.
; proven-str is a newline-separated string of already-proved property forms (or "").
; seed varies per search to get non-deterministic variation across searches.
; Returns (mv erp raw-form) where raw-form is a (property ...) form on success.
(defun ai-call-model (defs-str thm-str chk-str proven-str seed verbose)
  (declare (xargs :mode :program))
  (b* (
       ((mv ai-erp raw-form) (query-ai defs-str thm-str chk-str proven-str seed verbose))
       ((when ai-erp) (mv ai-erp nil))
       ((when (not (and (consp raw-form) (eq (car raw-form) 'property))))
        (mv (acl2s-fms-to-string
             "AI output was not a valid (property ...) form: ~x0"
             (list (cons #\0 raw-form))) nil)))
    (mv nil raw-form)))

; ai-readmit-one: silently re-admit a single proven property form via skip-proofs.
; Uses property-form-to-defthm so suppression works (property re-enables 'comment).
; Returns (mv erp state).
(defun ai-readmit-one (prop-form ctx state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((defthm-form (property-form-to-defthm prop-form state))
       (admit-form  (or defthm-form prop-form))
       ((mv erp & state)
        (acl2::trans-eval
          `(with-output :off :all! (skip-proofs ,admit-form))
          ctx state t)))
    (mv erp state)))

; ai-readmit-all: re-admit every form in proven (in order) silently.
; proven should be in proof order: first proved = first in list.
; Returns (mv erp state).
(defun ai-readmit-all (proven ctx state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp proven)
      (mv nil state)
    (b* (((mv erp state) (ai-readmit-one (car proven) ctx state))
         ((when erp) (mv erp state)))
      (ai-readmit-all (cdr proven) ctx state))))

; ai-try-proof-timed: attempt to prove prop-form with optional time-limit.
; All proof output is suppressed; checkpoints are still saved via :gag-mode t.
; Returns (mv result chk-list state) where result is :proved, :timeout, or :failed.
;
; WARNING: (with-output :off :all ...) suppresses proof-failure errors, making
; erp unreliable as a success indicator (erp=nil even on failure).
; We therefore use the world check — if the theorem name landed in the world,
; the proof succeeded. This matches the pattern from the old ai-validate-steps.
;
; Does NOT use revert-world — caller is responsible for world management.
(defun ai-try-proof-timed (prop-form time-limit ctx state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (
       ; Convert to defthm so output suppression works (property re-enables 'comment).
       (defthm-form (property-form-to-defthm prop-form state))
       (target-form (or defthm-form prop-form))
       ; The theorem name we'll check in the world after the attempt.
       ; Use defthm-form's name if conversion succeeded; otherwise prop-form's name.
       (thm-name    (and (consp target-form) (consp (cdr target-form))
                         (symbolp (cadr target-form)) (cadr target-form)))
       ; Build the suppressed form, optionally wrapped with a time limit.
       (inner-form  `(with-output :off :all :gag-mode t ,target-form))
       (eval-form   (if time-limit
                        `(with-prover-time-limit ,time-limit ,inner-form)
                      inner-form))
       ; Measure wall time for timeout classification.
       ; read-run-time returns a rational; keep elapsed as rational for comparison
       ; (ACL2's >= guard requires rationalp; float literals like 0.85 violate it).
       ((mv t0 state) (acl2::read-run-time state))
       ((mv & & state) (acl2::trans-eval eval-form ctx state t))
       ((mv t1 state) (acl2::read-run-time state))
       (elapsed (- t1 t0))   ; rational; convert to float only for display (not here)
       (chk-list (acl2::checkpoint-list-pretty nil state))
       ; World check: the theorem is in the world iff the proof succeeded.
       ; erp from trans-eval is NOT reliable when :off :all suppresses errors.
       (in-world-p (and thm-name
                        (consp (acl2::getpropc thm-name 'acl2::theorem nil (w state)))))
       ; 85/100 = 17/20 — exact rational equivalent of 0.85, avoids float guard.
       (result (if in-world-p
                   :proved
                 (if (and time-limit (>= elapsed (* time-limit 85/100)))
                     :timeout
                   :failed))))
    (mv result chk-list state)))

; ai-try-with-context: re-admit all proven lemmas, then probe target.
; Everything runs inside revert-world so the world is always clean on return.
; Returns (mv result chk-list state).
(defun ai-try-with-context (proven target time-limit ctx state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (
       ((mv & res-list state)
        (revert-world
          (b* (
               ; Re-admit proven lemmas so prover can use them as rewrite rules.
               ; Ignore readmit errors (indicate a logic bug, not a proof failure).
               ((mv & state) (ai-readmit-all proven ctx state))
               ((mv result chk-list state)
                (ai-try-proof-timed target time-limit ctx state)))
            (value (list result chk-list))))))
    (mv (car res-list) (cadr res-list) state)))

; ai-proof-loop: the recursive proof-search engine.
;
; Arguments:
;   goals       -- forms still to prove; orig always sits at the end
;   proven      -- forms already proved, in proof order (first proved first)
;   step-ctr    -- # suggestions introduced in the current search (consumed on push)
;   search-ctr  -- # of distinct searches attempted (starts at 1)
;   orig        -- the original property form (never popped from goals)
;   defs-str    -- definitions string for AI prompt (computed once)
;   best-proven -- best proven list seen across all searches (for summary on failure)
;   step-limit  -- max suggestions per search before resetting
;   search-limit -- max searches before giving up
;   time-limit  -- seconds per proof attempt (nil = no limit)
;   verbose     -- pass to query-ai
;   ctx         -- trans-eval context symbol
;   state       -- ACL2 state
;
; Returns (mv outcome proved-seq state) where:
;   outcome = :proved | :exhausted | :ai-error | :no-checkpoint
;   proved-seq = list of forms proved (in proof order, for summary display)
(defun ai-proof-loop (goals proven step-ctr search-ctr
                      orig defs-str best-proven init-chk-list
                      step-limit search-limit time-limit
                      verbose ctx state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp goals)
      ; Base case: all goals proved.
      (mv :proved proven state)
    (b* (
         (top     (car goals))
         (is-orig (equal top orig))

         ; Skip the proof attempt when proven is empty and we're checking orig —
         ; Phase 1 already showed it fails without any lemma context.
         (skip-p (and is-orig (null proven)))

         ; Print what we're about to attempt (omit when skipping).
         (- (cond (skip-p nil)
                  (is-orig (cw "~%Proving ~x0 with context... " (cadr orig)))
                  (t (cw "Proving suggested lemma --- "))))

         ; Attempt the proof, or skip it and reuse Phase 1 checkpoints.
         ((mv result chk-list state)
          (if skip-p
              (mv :failed init-chk-list state)
            (ai-try-with-context proven top time-limit ctx state)))

         ; Print result on the same line (omit when skipping).
         (result-str (if (eq result :proved)
                         (if is-orig "[SUCCEEDED]" "[*]")
                       (if (eq result :timeout) "[TIMEOUT]" "[FAILED]")))
         (- (if skip-p nil (cw "~s0~%" result-str)))

         ; Case 1: proved — update proven and continue.
         ((when (eq result :proved))
          (ai-proof-loop (cdr goals) (append proven (list top)) step-ctr search-ctr
                         orig defs-str best-proven init-chk-list
                         step-limit search-limit time-limit verbose ctx state))

         ; Case 2: failed/timeout on an intermediate (non-orig) lemma — discard it.
         ; step-ctr is NOT decremented (the step was consumed when the suggestion was pushed).
         ((when (not is-orig))
          (ai-proof-loop (cdr goals) proven step-ctr search-ctr
                         orig defs-str best-proven init-chk-list
                         step-limit search-limit time-limit verbose ctx state))

         ; Case 3: failed/timeout on orig — need to query AI or reset the search.
         ((when (>= step-ctr step-limit))
          ; Step limit reached for this search.
          (if (>= search-ctr search-limit)
              ; Also at search limit — give up.
              (mv :exhausted
                  (if (>= (len proven) (len best-proven)) proven best-proven)
                  state)
            ; Start a fresh search.
            (b* ((new-best (if (>= (len proven) (len best-proven)) proven best-proven))
                 (new-srch (1+ search-ctr))
                 (- (cw "~%[Search ~x0 exhausted ~x1 steps. Starting search ~x2.]~%"
                        search-ctr step-ctr new-srch)))
              (ai-proof-loop (list orig) nil 0 new-srch
                             orig defs-str new-best init-chk-list
                             step-limit search-limit time-limit verbose ctx state))))

         ; Query AI for a suggestion.
         (chk-str (and (consp chk-list)
                       (acl2s-fms-to-string "~x0" (list (cons #\0 (car chk-list))))))
         ((when (not chk-str))
          (prog2$ (cw "~%AI query skipped: no checkpoint available.~%")
                  (mv :no-checkpoint proven state)))

         (thm-str    (acl2s-fms-to-string "~x0" (list (cons #\0 orig))))
         (proven-str (format-proven-str proven))
         ; Vary seed per search so different searches produce different suggestions.
         ; Use a base that won't overflow uint32 when search-ctr is small.
         ; #xffffffff + 1 = 2^32, which overflows. Instead, multiply to spread seeds.
         (seed       (+ 1234567890 (* search-ctr 100003)))
         (new-step   (1+ step-ctr))

         ((mv ai-erp suggestion)
          (ai-call-model defs-str thm-str chk-str proven-str seed verbose))

         ((when ai-erp)
          (prog2$ (cw "~%AI query failed: ~s0~%" ai-erp)
                  (mv :ai-error proven state)))

         ; Print suggestion header and syntax check lines.
         (- (cw "~%[Search ~x0, Step ~x1] Suggested lemma for ~x2:~% -- ~x3~%~%"
                search-ctr new-step (cadr orig) suggestion))
         (- (%check-line "Parse check --------------- " t))
         (- (%check-line "Property form check ------- " t)))

      ; Push suggestion as new sub-goal and recurse.
      (ai-proof-loop (cons suggestion goals) proven new-step search-ctr
                     orig defs-str best-proven init-chk-list
                     step-limit search-limit time-limit verbose ctx state))))

; map-property-to-local: convert a list of helper forms to (local (defthm ...))
; forms for use inside an encapsulate. property-form-to-defthm is applied first
; to avoid the 'comment channel leak that bypasses :off :all.
(defun map-property-to-local (forms state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp forms)
      nil
    (b* ((f (car forms))
         (d (property-form-to-defthm f state)))
      (cons `(local ,(or d f))
            (map-property-to-local (cdr forms) state)))))

; make-encapsulate-form: wrap proved-seq as a silent encapsulate where helpers
; are local (invisible after encapsulate closes) and only the final theorem is
; exported to the world. proved-seq is in proof order: helpers first, theorem last.
(defun make-encapsulate-form (proved-seq state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((helpers     (butlast proved-seq 1))
       (final       (car (last proved-seq)))
       (final-d     (property-form-to-defthm final state))
       (local-forms (map-property-to-local helpers state)))
    `(with-output :off :all :gag-mode t
       (encapsulate ()
         ,@local-forms
         ,(or final-d final)))))

; ai-auto-fn: top-level AI proof-search orchestrator.
; Called directly by the `auto` macro.
; Phase 1: initial proof attempt (ACL2s prints freely).
; Phase 2: ai-proof-loop — recursive search with goals/proven lists.
; Phase 3: structured summary (checkpoints always shown).
; On success (Phase 1): silently re-admits the form so make-event lands it in the world.
; On success (AI path): returns a silent encapsulate — helpers are local, only
; the final theorem is exported to the world.
; On failure: returns (value-triple :invisible) — world unchanged.
(defun ai-auto-fn (form time-limit step-limit search-limit verbose state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (
       (ctx  'auto)
       ; Event name for display: (cadr form) works for property, defthm, definec, etc.
       (name (and (consp form) (consp (cdr form)) (cadr form)))

       ; Capture start time.
       ((mv start-time state) (acl2::read-run-time state))

       ; Phase 1: initial proof — ACL2s prints freely.
       ; Capture chk-list from Phase 1 to seed the loop without a redundant re-probe.
       ((mv failed-p init-chk-list state) (ai-try-proof form ctx nil state))
       ; Phase 1 succeeded — silently re-admit via make-event so the theorem
       ; lands in the world. property-form-to-defthm avoids the 'comment leak.
       ((when (not failed-p))
        (b* ((defthm-form (property-form-to-defthm form state))
             (admit-form  (or defthm-form form)))
          (value `(with-output :off :all :gag-mode t ,admit-form))))

       ; Capture initial checkpoint info for the summary display (always shown).
       (init-top-info (acl2::checkpoint-info-list t   state))
       (init-sub-info (acl2::checkpoint-info-list nil state))

       ; Collect definitions for the AI prompt (computed once).
       ; form-proof-body extracts the formula/body expression relevant for scanning.
       (defs-str (collect-defs-string (form-proof-body form) state))

       ; Phase 2: AI-guided proof search.
       ; Entry: goals = [form], proven = [], step-ctr = 0, search-ctr = 1.
       ; The loop first re-probes form (suppressed) to get fresh checkpoints,
       ; then queries the AI and recurses.
       ((mv outcome proved-seq state)
        (ai-proof-loop (list form) nil 0 1
                       form defs-str nil init-chk-list
                       step-limit search-limit time-limit
                       verbose ctx state))

       ; Phase 3: summary.
       ((mv end-time state) (acl2::read-run-time state))
       (elapsed  (* (- end-time start-time) 1.0))
       (proved-p (eq outcome :proved))

       (- (cw "~%**Summary of AI Assistance**~%"))
       (- (cw "Proof of ~x0 — ~s1~%~%"
              name (if proved-p "PROVED WITH AI ASSISTANCE" "STILL OPEN")))
       ; Always show initial checkpoints (merged flag — no separate summary toggle).
       (- (print-checkpoints init-top-info init-sub-info state))

       ; proved-seq when :proved includes the original form as the last element.
       ; Separate helpers (all-but-last) from the final theorem for display.
       (helpers (if proved-p (butlast proved-seq 1) proved-seq))

       (- (if proved-p
              (b* (
                   (- (if helpers
                          (cw "~%Helper lemma(s): ~x0 (local, not exported to world)~%"
                              (len helpers))
                        (cw "~%No helper lemmas needed.~%")))
                   (- (cw "~%Theorem admitted to world: ~x0~%" name)))
                nil)
            (if proved-seq
                (b* (
                     (- (cw "~%Best progress: ~x0 helper lemma(s) proved before limit.~%"
                             (len proved-seq)))
                     (- (print-proof-sequence proved-seq)))
                  nil)
              (cw "~%No lemmas were successfully proved.~%"))))

       (- (if proved-p
              (cw "~%Proof complete with AI assistance.~%")
            (cw "~%Could not close the proof within ~x0 search(es), ~x1 step(s) each.~%"
                search-limit step-limit)))

       (- (cw "~%Total time: ~f0 seconds~%" elapsed)))
    ; AI path: if proved, admit via encapsulate — helpers are local (not exported),
    ; only the final theorem lands in the world.
    ; On failure, return :invisible — world stays clean (revert-world cleaned up).
    (if proved-p
        (value (make-encapsulate-form proved-seq state))
      (value '(value-triple :invisible)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Section 7: auto Macro
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (auto <form> :time 30 :step 5 :search 5)
;
; <form>    -- any ACL2 event (property, defthm, definec, ...)
; :time N   -- seconds per proof attempt (default 30)
; :step N   -- max AI suggestions per search (default 5)
; :search N -- max distinct searches (default 5)
; :verbose t -- (debug) print model prompt and raw output
;
; Using (auto ...) always invokes the AI proof-search pipeline.
; No global flag needed — just use the macro.
(defmacro auto (form &rest kwd-args)
  (b* ((time-limit   (or (cadr (acl2::assoc-keyword :time    kwd-args)) 30))
       (step-limit   (or (cadr (acl2::assoc-keyword :step    kwd-args)) 5))
       (search-limit (or (cadr (acl2::assoc-keyword :search  kwd-args)) 5))
       (verbose      (cadr (acl2::assoc-keyword :verbose kwd-args))))
    `(with-output :off summary
       (make-event
         (ai-auto-fn ',form ,time-limit ,step-limit ,search-limit ',verbose state)))))