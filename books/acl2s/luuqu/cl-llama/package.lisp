(defpackage :cl-llama
  (:use :cl :cffi)
  (:export #:init
           #:shutdown
           #:load-model
           #:unload-model
           #:generate
           #:suggest-lemma
           #:*current-model*
           #:*current-context*
           #:*current-vocab*))
