;;; suggest-raw.lsp -- raw Lisp LLM bridge for acl2s/luuqu
;;; Loaded by top.lisp via (acl2::include-raw "suggest-raw.lsp" :host-readtable t)
;;;
;;; Responsibility: call the model, trim output, run read-from-string.
;;; NO ACL2-semantic checks. Shape checking happens on the ACL2 side.
;;;
;;; Uses (values ...) rather than ACL2's (mv ...) so this file works
;;; both inside ACL2 (via include-raw) and in plain SBCL for testing.

(in-package "ACL2S")

;;; -- 1. Load dependencies via Quicklisp, then load cl-llama from luuqu --
;;; CFFI and cffi-libffi are the only external dependencies of cl-llama.
;;; The cl-llama source files themselves live in cl-llama/ next to this file.
(load (merge-pathnames "quicklisp/setup.lisp" (user-homedir-pathname)))
(ql:quickload '(:cffi :cffi-libffi) :silent t)
(let* ((here (make-pathname :name nil :type nil :defaults *load-truename*))
       (cl-llama-dir (merge-pathnames "cl-llama/" here)))
  (dolist (f '("package.lisp" "library.lisp" "bindings.lisp"
               "high-level.lisp" "suggest.lisp"))
    (load (merge-pathnames f cl-llama-dir))))

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
;;; Inputs:  defs          string -- pretty-printed user function definitions
;;;          theorem       string -- the full (property ...) form as a string
;;;          checkpoint    string -- first failed subgoal from checkpoint-list-pretty
;;;          proven-lemmas string -- newline-separated proven helper forms (or nil/"")
;;;          seed          integer -- random seed; vary per search for non-determinism
;;;
;;; Returns: (values erp form)   [standard CL multiple values]
;;;   erp  = nil    -> form is a parsed Lisp s-expression
;;;   erp  = string -> parse/model error; form is nil

(defun query-ai-raw (defs theorem checkpoint proven-lemmas seed &key verbose)
  (handler-case
    (let* (;; Call the model for a single candidate string.
           ;; proven-lemmas is a string of already-proved forms (or nil/empty).
           ;; seed varies per search so different searches get different suggestions.
           (raw (cl-llama:suggest-lemma defs theorem checkpoint proven-lemmas
                                        :seed seed :verbose verbose))
           ;; Trim whitespace.
           (trimmed (string-trim '(#\Space #\Newline #\Tab #\Return) raw))
           ;; Find the start of the (property ...) form.
           (prop-pos (or (search "(property " trimmed :test #'char-equal)
                         (search "(acl2s::property " trimmed :test #'char-equal)))
           (paren-pos (or prop-pos (position #\( trimmed))))
      (if (null paren-pos)
          (values (format nil "query-ai-raw: no ( found in output: ~S" trimmed) nil)
        (let* ((*package* (find-package "ACL2S"))
               (form (read-from-string trimmed nil nil :start paren-pos)))
          (if form
              (values nil form)
            (values (format nil "query-ai-raw: read-from-string returned nil for: ~S" trimmed) nil)))))
    (error (e)
      (values (format nil "query-ai-raw: ~A" e) nil))))
