(in-package :cl-llama)

(define-foreign-library libllama
  (:darwin "/opt/homebrew/lib/libllama.dylib")
  (:unix (:or "libllama.so" "libllama.so.0"))
  (t (:default "libllama")))

(use-foreign-library libllama)

;;; Use *load-truename* (bound during load) to locate cl-llama-bridge.dylib
;;; relative to this file, instead of going through ASDF.
(define-foreign-library cl-llama-bridge
  (:darwin #.(merge-pathnames "cl-llama-bridge.dylib"
                              (make-pathname :name nil :type nil
                                            :defaults *load-truename*))))

(use-foreign-library cl-llama-bridge)
