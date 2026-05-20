(in-package :cl-llama)

(defun suggest-lemma (definitions theorem checkpoint proven-lemmas
                      &key (max-tokens 300) (temperature 0.15f0) (seed #xffffffff) verbose)
  "Query the loaded model for a lemma suggestion given an ACL2s proof failure.
   DEFINITIONS, THEOREM, CHECKPOINT are plain strings from the proof context.
   PROVEN-LEMMAS is a string listing already-proved helper lemmas (or nil/\"\").
   Returns the model's output string (the suggested lemma form).
   When VERBOSE is true, prints the prompt and raw output to stdout.

   Retries up to 3 times total on syntax errors (hardcoded, not user-configurable).
   Each retry sends a correction prompt naming the bad output, then re-appends the
   original prompt so the model has full context."
  (let* ((proven-section
          (if (and proven-lemmas (not (equal proven-lemmas "")))
              (format nil "~%Proven lemmas (available as rewrite rules):~%~A" proven-lemmas)
            ""))
         (original-prompt (format nil
"You are an ACL2s assistant helping to prove theorems. A proof has failed.

Definitions:
~A

Theorem being proved:
~A

Failed subgoal:
~A~A

Suggest ONE helper lemma using the ACL2s property form. Your response MUST start with \"(property\" and use this exact syntax:

  (property <name> (<var1> :type1 <var2> :type2 ...) <body>)

Example:
  (property len-append (x :tl y :tl)
    (equal (len (append x y)) (+ (len x) (len y))))

Return ONLY the (property ...) form. No explanation, no commentary, no markdown, no backticks, no quotes. Start your response with \"(property\".

" definitions theorem checkpoint proven-section))
         (current-prompt original-prompt)
         (last-result nil))
    ;; Up to 3 attempts total. Return on first syntactically valid output;
    ;; after exhausting retries, return whatever the model last produced.
    (dotimes (attempt 3 last-result)
      (when verbose
        (format t "~%[VERBOSE] Prompt sent to model~A:~%~A~%[/VERBOSE PROMPT]~%"
                (if (zerop attempt) "" (format nil " (syntax retry ~A/2)" attempt))
                current-prompt))
      (let* ((result (generate current-prompt :max-tokens max-tokens
                                              :temperature temperature :seed seed))
             (trimmed (string-trim '(#\Space #\Newline #\Tab #\Return) result))
             (paren-pos (or (search "(property " trimmed :test #'char-equal)
                            (position #\( trimmed)))
             (parsed    (and paren-pos
                             (ignore-errors
                               (read-from-string trimmed nil nil :start paren-pos)))))
        (setf last-result result)
        (when verbose
          (format t "~%[VERBOSE] Raw model output~A:~%~A~%[/VERBOSE OUTPUT]~%"
                  (if (zerop attempt) "" (format nil " (syntax retry ~A/2)" attempt))
                  result))
        (when parsed
          (return result))   ; syntactically valid — done
        ;; Build correction prompt for the next attempt.
        (setf current-prompt
              (format nil
"Your response:

  ~A

is not valid ACL2s/Lisp syntax. Try again. Your response MUST start with \"(property\" and be a single well-formed s-expression.

Here is the original request:

~A" trimmed original-prompt))))))

(defun suggest-lemma-beam (definitions theorem checkpoint proven-lemmas
                           &key (beam-width 5) (max-tokens 300))
  "Run beam search for lemma candidates given an ACL2s proof failure.
PROVEN-LEMMAS is a string listing already-proved helper lemmas (or nil/\"\").
Returns a list of candidate strings (raw model output), best-scoring first."
  (let* ((proven-section
          (if (and proven-lemmas (not (equal proven-lemmas "")))
              (format nil "~%Proven lemmas (available as rewrite rules):~%~A" proven-lemmas)
            ""))
         (prompt (format nil
"You are an ACL2s assistant helping to prove theorems. A proof has failed.

Definitions:
~A

Theorem being proved:
~A

Failed subgoal:
~A~A

Suggest ONE helper lemma using the ACL2s property form. Your response MUST start with \"(property\" and use this exact syntax:

  (property <name> (<var1> :type1 <var2> :type2 ...) <body>)

Example:
  (property len-append (x :tl y :tl)
    (equal (len (append x y)) (+ (len x) (len y))))

Return ONLY the (property ...) form. No explanation, no commentary, no markdown, no backticks, no quotes. Start your response with \"(property\".

" definitions theorem checkpoint proven-section)))
    (mapcar #'cdr (beam-search prompt :beam-width beam-width :max-tokens max-tokens))))
