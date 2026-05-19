;;; suggest-raw.lsp -- raw Lisp LLM bridge for acl2s/luuqu
;;; Loaded by top.lisp via (acl2::include-raw "suggest-raw.lsp" :host-readtable t)
;;;
;;; Responsibility: call the model, trim output, run read-from-string.
;;; NO ACL2-semantic checks. Shape checking happens on the ACL2 side.
;;;
;;; Uses (values ...) rather than ACL2's (mv ...) so this file works
;;; both inside ACL2 (via include-raw) and in plain SBCL for testing.

(in-package "ACL2S")

;;; -- 1. Load Quicklisp -------------------------------------------------
(load (merge-pathnames "quicklisp/setup.lisp" (user-homedir-pathname)))
(ql:quickload :cl-llama :silent t)

;;; -- 2. Load the model immediately ------------------------------------
;;; Use merge-pathnames + namestring so the C library gets an absolute path.
;;; The ~ shorthand is not expanded by libllama.
(cl-llama:load-model
 (namestring (merge-pathnames
              "Documents/ai-models/Ministral-3-14B-Instruct-2512-Q4_K_M.gguf"
              (user-homedir-pathname)))
 :n-gpu-layers -1)

;;; -- 3. Register shutdown hook -----------------------------------------
;;; cl-llama:shutdown frees context, model, then calls %llama-backend-free.
;;; Without this, ggml-metal's C++ static destructor fires during exit() with
;;; live Metal render sets, triggering GGML_ASSERT failure and SIGABRT.
;;; SBCL runs sb-ext:*exit-hooks* before calling C exit(), so this runs before
;;; the C++ static destructors, giving the Metal backend a clean teardown path.
(pushnew #'cl-llama:shutdown sb-ext:*exit-hooks*)

;;; -- 4. query-ai-raw --------------------------------------------------
;;;
;;; Inputs:  defs       string -- pretty-printed user function definitions
;;;          theorem    string -- the full (property ...) form as a string
;;;          checkpoint string -- first failed subgoal from checkpoint-list-pretty
;;;
;;; Returns: (values erp forms)   [standard CL multiple values]
;;;   erp  = nil    -> forms is a list of parsed Lisp s-expressions (best-first)
;;;   erp  = string -> parse/model error; forms is nil
;;;
;;; Calls suggest-lemma-beam to get K candidate strings via beam search,
;;; then parses each into a (property ...) form. The ACL2 side does shape
;;; checking. State is not taken or returned.

(defun %parse-property-form (raw-str)
  "Parse a single model output string into a (property ...) form.
Returns the form, or NIL if no valid form found."
  (handler-case
    (let* ((trimmed (string-trim '(#\Space #\Newline #\Tab #\Return) raw-str))
           (prop-pos (or (search "(property " trimmed :test #'char-equal)
                         (search "(acl2s::property " trimmed :test #'char-equal)))
           (paren-pos (or prop-pos (position #\( trimmed))))
      (if (null paren-pos)
          nil
        (let ((*package* (find-package "ACL2S")))
          (read-from-string trimmed nil nil :start paren-pos))))
    (error () nil)))

(defun query-ai-raw (defs theorem checkpoint &key (beam-width 5))
  (handler-case
    (let* (;; Step A: Call the model via beam search.
           (strings (cl-llama:suggest-lemma-beam defs theorem checkpoint
                                                  :beam-width beam-width))
           ;; Step B: Parse each candidate string into a Lisp form.
           (forms (remove nil (mapcar #'%parse-property-form strings))))
      (if forms
          (values nil forms)
        (values "query-ai-raw: no valid (property ...) form in any beam output" nil)))
    ;; Step C: Catch any error (model error, parse error, etc.).
    (error (e)
      (values (format nil "query-ai-raw: ~A" e) nil))))
