; test-auto.lisp — integration tests for the (auto ...) macro
;
; Run with:
;   acl2s < books/acl2s/luuqu/test-auto.lisp
; or from the acl2-copy root:
;   acl2s < books/acl2s/luuqu/test-auto.lisp 2>&1 | tee /tmp/auto-test-out.txt
;
; Each test is independent — ai-auto-fn is purely advisory (returns
; value-triple :invisible), so nothing accumulates in the world between tests.

(include-book "acl2s/luuqu/top" :dir :system)

; Helper function used in several tests.
(definec rev1 (x acc :tl) :tl
  (if (endp x) acc (rev1 (cdr x) (cons (car x) acc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Test 1: theorem ACL2s can prove on its own
;;;;
;;;; Expected: Phase 1 succeeds immediately — AI loop never runs.
;;;; Output should show the normal ACL2s proof, then nothing else.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(auto (property append-nil (x :tl)
        (equal (append x nil) x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Test 2: theorem that needs one AI-suggested helper lemma
;;;;
;;;; Expected:
;;;;   Phase 1 fails (ACL2s can't prove rev1-rev directly).
;;;;   AI suggests (property rev1-append (x :tl y :tl) ...).
;;;;   Helper proved, then rev1-rev proved with it in context.
;;;;   Summary: PROVED WITH AI ASSISTANCE, 1 helper lemma.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(auto (property rev1-rev (x :tl)
        (equal (rev1 x nil) (rev x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Test 3: same as Test 2 but with explicit keyword parameters
;;;;
;;;; :time 60  — up to 60 seconds per proof attempt
;;;; :step 3   — try at most 3 AI suggestions per search
;;;; :search 2 — try at most 2 distinct searches before giving up
;;;;
;;;; Expected: same outcome as Test 2 (one helper suffices).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(auto (property rev1-rev-kw (x :tl)
        (equal (rev1 x nil) (rev x)))
      :time 60 :step 3 :search 2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Test 4: defthm form instead of property
;;;;
;;;; auto accepts any ACL2 event. This tests passing a plain
;;;; defthm. ACL2s can prove this directly (append-assoc is
;;;; built-in), so Phase 1 should succeed without AI help.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(auto (defthm append-assoc-test
        (implies (and (true-listp x) (true-listp y))
                 (equal (append (append x y) nil)
                        (append x y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Test 5: verbose mode — shows the prompt sent to the model
;;;;         and the raw model output
;;;;
;;;; Expected: same proof outcome as Test 2 but with extra output:
;;;;   [VERBOSE] Prompt sent to model: ...
;;;;   [VERBOSE] Raw model output: ...
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(auto (property rev1-rev-verbose (x :tl)
        (equal (rev1 x nil) (rev x)))
      :verbose t)

(quit)
