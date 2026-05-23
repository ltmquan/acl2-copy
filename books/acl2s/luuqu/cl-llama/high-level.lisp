(in-package :cl-llama)

(defvar *current-model*   nil)
(defvar *current-vocab*   nil)
(defvar *current-context* nil)
(defvar *backend-initialized* nil)

;; SBCL traps FPU exceptions by default; mask them for every call into libllama,
;; which does intentional overflow/NaN (e.g. softmax over -inf).
(defmacro with-llama-fenv (&body body)
  `(sb-int:with-float-traps-masked
       (:overflow :underflow :inexact :invalid :divide-by-zero)
     ,@body))

(defun %init-model-params (ptr n-gpu-layers)
  "Write llama_model_params C defaults into PTR via bridge, then override n-gpu-layers."
  (%cl-llama-model-default-params-into ptr)
  (setf (foreign-slot-value ptr '(:struct llama-model-params) 'n-gpu-layers) n-gpu-layers))

(defun %init-context-params (ptr n-ctx n-seq-max)
  "Write llama_context_params C defaults into PTR, then override key fields.
offload-kqv is forced to nil: when the KV cache is on the Metal GPU backend,
llama_memory_seq_cp fails (is_full=nil assertion). Keeping KV on CPU enables
seq_cp, which beam search requires. GPU compute (attention) still runs on Metal."
  (%cl-llama-context-default-params-into ptr)
  (setf (foreign-slot-value ptr '(:struct llama-context-params) 'n-ctx)       n-ctx
        (foreign-slot-value ptr '(:struct llama-context-params) 'n-batch)     n-ctx
        (foreign-slot-value ptr '(:struct llama-context-params) 'n-ubatch)    n-ctx
        (foreign-slot-value ptr '(:struct llama-context-params) 'n-seq-max)   n-seq-max
        (foreign-slot-value ptr '(:struct llama-context-params) 'offload-kqv) nil))

(defun %fill-batch (ptr tokens-ptr n-tokens)
  "Write a simple single-sequence batch into PTR (equivalent to llama_batch_get_one)."
  (setf (foreign-slot-value ptr '(:struct llama-batch) 'n-tokens) n-tokens
        (foreign-slot-value ptr '(:struct llama-batch) 'token)    tokens-ptr
        (foreign-slot-value ptr '(:struct llama-batch) 'embd)     (null-pointer)
        (foreign-slot-value ptr '(:struct llama-batch) 'pos)      (null-pointer)
        (foreign-slot-value ptr '(:struct llama-batch) 'n-seq-id) (null-pointer)
        (foreign-slot-value ptr '(:struct llama-batch) 'seq-id)   (null-pointer)
        (foreign-slot-value ptr '(:struct llama-batch) 'logits)   (null-pointer)))

(defcallback noop-log-callback :void
    ((level :int) (text :pointer) (user-data :pointer))
  (declare (ignore level text user-data)))

(defun init ()
  "Initialize the llama backend. Call once at startup."
  (unless *backend-initialized*
    (with-llama-fenv
      (%llama-log-set (callback noop-log-callback) (null-pointer))
      (%llama-backend-init))
    (setf *backend-initialized* t)))

(defun shutdown ()
  "Release any loaded model and free the backend."
  (with-llama-fenv
    (when *current-context*
      (%llama-free *current-context*)
      (setf *current-context* nil))
    (when *current-model*
      (%llama-model-free *current-model*)
      (setf *current-model* nil
            *current-vocab* nil))
    (when *backend-initialized*
      (%llama-backend-free)
      (setf *backend-initialized* nil))))

(defun load-model (path &key (n-ctx 4096) (n-gpu-layers -1) (n-seq-max 8))
  "Load a GGUF model from PATH. n-seq-max must be >= beam-width for beam search."
  (init)
  (unload-model)
  (with-llama-fenv
    (with-foreign-object (mparams '(:struct llama-model-params))
      (%init-model-params mparams n-gpu-layers)
      (let ((model (%cl-llama-model-load path mparams)))
        (when (null-pointer-p model)
          (error "Failed to load model from ~A" path))
        (setf *current-model* model
              *current-vocab* (%llama-model-get-vocab model))))
    (with-foreign-object (cparams '(:struct llama-context-params))
      (%init-context-params cparams n-ctx n-seq-max)
      (let ((ctx (%cl-llama-init-context *current-model* cparams)))
        (when (null-pointer-p ctx)
          (error "Failed to create context"))
        (setf *current-context* ctx))))
  t)

(defun unload-model ()
  (with-llama-fenv
    (when *current-context*
      (%llama-free *current-context*)
      (setf *current-context* nil))
    (when *current-model*
      (%llama-model-free *current-model*)
      (setf *current-model* nil
            *current-vocab* nil))))

(defun tokenize (text &key (add-special t))
  "Tokenize TEXT against the currently loaded vocab. Returns a list of token ids."
  (let* ((text-len (length (babel:string-to-octets text :encoding :utf-8)))
         (max-tokens (* 4 text-len)))
    (with-foreign-object (tokens 'llama-token max-tokens)
      (let ((n (with-llama-fenv
                 (%llama-tokenize *current-vocab*
                                  text
                                  text-len
                                  tokens
                                  max-tokens
                                  add-special
                                  t))))
        (when (< n 0)
          (error "Tokenization failed (need ~A tokens, had ~A)" (- n) max-tokens))
        (loop for i below n
              collect (mem-aref tokens 'llama-token i))))))

(defun token-to-string (token)
  "Convert a single token id to its piece (a string fragment)."
  (with-foreign-object (buf :char 256)
    (let ((n (with-llama-fenv
               (%llama-token-to-piece *current-vocab* token buf 256 0 nil))))
      (when (< n 0)
        (error "token-to-piece failed for token ~A" token))
      (foreign-string-to-lisp buf :count n :encoding :utf-8))))

(defun generate (prompt &key (max-tokens 200) (temperature 0.15f0) (seed #xffffffff))
  "Generate a completion for PROMPT. Returns the generated string."
  (unless *current-context*
    (error "No model loaded. Call (load-model ...) first."))
  (with-llama-fenv
    (let* ((chain (with-foreign-object (sparams '(:struct llama-sampler-chain-params))
                    (%cl-llama-sampler-chain-default-params-into sparams)
                    (%cl-llama-sampler-chain-init sparams)))
           (temp-sampler (%llama-sampler-init-temp temperature))
           (dist-sampler (%llama-sampler-init-dist seed)))
      (%llama-sampler-chain-add chain temp-sampler)
      (%llama-sampler-chain-add chain dist-sampler)
      (unwind-protect
           (let* ((prompt-tokens (tokenize prompt :add-special t))
                  (n-prompt (length prompt-tokens))
                  (output (make-array 0 :element-type 'character
                                        :fill-pointer 0 :adjustable t)))
             ;; Clear the KV cache from any previous generate call before decoding.
             ;; Without this, the second call fails: the cache still holds tokens
             ;; from the prior inference and decode returns non-zero on the new prompt.
             (%llama-memory-seq-rm (%llama-get-memory *current-context*) -1 -1 -1)
             ;; Decode prompt
             (with-foreign-object (tok-buf 'llama-token n-prompt)
               (loop for i below n-prompt
                     for tok in prompt-tokens
                     do (setf (mem-aref tok-buf 'llama-token i) tok))
               (with-foreign-object (batch '(:struct llama-batch))
                 (%fill-batch batch tok-buf n-prompt)
                 (when (/= 0 (%cl-llama-decode *current-context* batch))
                   (error "Decode failed on prompt"))))
             ;; Generation loop
             (loop for i below max-tokens
                   for next = (%llama-sampler-sample chain *current-context* -1)
                   until (%llama-vocab-is-eog *current-vocab* next)
                   do (%llama-sampler-accept chain next)
                      (let ((piece (token-to-string next)))
                        (loop for c across piece do (vector-push-extend c output)))
                      (with-foreign-object (one-tok 'llama-token 1)
                        (setf (mem-aref one-tok 'llama-token 0) next)
                        (with-foreign-object (batch '(:struct llama-batch))
                          (%fill-batch batch one-tok 1)
                          (when (/= 0 (%cl-llama-decode *current-context* batch))
                            (error "Decode failed on token ~A" i)))))
             (coerce output 'string))
        (%llama-sampler-free chain)))))

;;; --- Beam search ---

(defun log-softmax-top-k (logits-ptr vocab-size k)
  "Read vocab-size floats from logits-ptr; return list of (token-id . log-prob), top k, sorted desc."
  (let* ((logits (loop for i below vocab-size collect (mem-aref logits-ptr :float i)))
         (max-l  (reduce #'max logits))
         (exps   (mapcar (lambda (l) (exp (- l max-l))) logits))
         (sum-e  (reduce #'+ exps))
         (log-s  (log sum-e))
         (lps    (loop for i below vocab-size
                       for e in exps
                       collect (cons i (- (- (nth i logits) max-l) log-s))))
         (sorted (sort lps #'> :key #'cdr)))
    (subseq sorted 0 (min k (length sorted)))))

;;; beam struct: alist with keys :seq-id :tokens :logprob :done
(defun %make-beam (seq-id) (list :seq-id seq-id :tokens nil :logprob 0.0d0 :done nil))
(defun %beam-seq-id  (b) (getf b :seq-id))
(defun %beam-tokens  (b) (getf b :tokens))
(defun %beam-logprob (b) (getf b :logprob))
(defun %beam-done    (b) (getf b :done))

(defun %beam-last-token (beam prompt-tokens)
  "Return the token to feed at the next decode step for BEAM."
  (if (%beam-tokens beam)
      (car (last (%beam-tokens beam)))
    (car (last prompt-tokens))))

(defun %decode-prompt (tok-buf n-tokens seq-id)
  "Decode N-TOKENS from TOK-BUF with explicit SEQ-ID, positions 0..n-1.
Only the last token's logits are requested (for EOS/sampling after prompt).
Signals error on decode failure."
  (with-foreign-object (pos-arr    'llama-pos    n-tokens)
    (with-foreign-object (nseq-arr  :int32        n-tokens)
      (with-foreign-object (sval-arr 'llama-seq-id n-tokens)
        (with-foreign-object (sptr-arr :pointer     n-tokens)
          (with-foreign-object (lgts-arr :int8       n-tokens)
            (loop for i below n-tokens
                  do (setf (mem-aref pos-arr   'llama-pos    i) i
                           (mem-aref nseq-arr  :int32        i) 1
                           (mem-aref sval-arr  'llama-seq-id i) seq-id
                           (mem-aref sptr-arr  :pointer      i)
                           (inc-pointer sval-arr (* i (foreign-type-size 'llama-seq-id)))
                           (mem-aref lgts-arr  :int8         i)
                           (if (= i (1- n-tokens)) 1 0)))
            (with-foreign-object (b '(:struct llama-batch))
              (setf (foreign-slot-value b '(:struct llama-batch) 'n-tokens) n-tokens
                    (foreign-slot-value b '(:struct llama-batch) 'token)    tok-buf
                    (foreign-slot-value b '(:struct llama-batch) 'embd)     (null-pointer)
                    (foreign-slot-value b '(:struct llama-batch) 'pos)      pos-arr
                    (foreign-slot-value b '(:struct llama-batch) 'n-seq-id) nseq-arr
                    (foreign-slot-value b '(:struct llama-batch) 'seq-id)   sptr-arr
                    (foreign-slot-value b '(:struct llama-batch) 'logits)   lgts-arr)
              (when (/= 0 (%cl-llama-decode *current-context* b))
                (error "Beam search: prompt decode failed")))))))))

(defun %decode-beam-step (live-beams prompt-len batch-ptr)
  "Fill BATCH-PTR with one token per live beam and call llama_decode.
  Returns non-zero on error."
  (let ((n (length live-beams)))
    (with-foreign-object (tok-arr 'llama-token n)
      (with-foreign-object (pos-arr 'llama-pos n)
        (with-foreign-object (nseq-arr :int32 n)
          ;; seq-id array: each batch slot needs an int32* pointing to seq-id value
          ;; We allocate a flat int32 array and point into it.
          (with-foreign-object (seqid-vals 'llama-seq-id n)
            (with-foreign-object (seqid-ptrs :pointer n)
              ;; fill token/pos/nseq/seqid arrays
              (loop for i below n
                    for beam in live-beams
                    for pos = (+ prompt-len (1- (length (%beam-tokens beam))))
                    do (setf (mem-aref tok-arr  'llama-token i) (getf beam :%next-token)
                             (mem-aref pos-arr  'llama-pos   i) pos
                             (mem-aref nseq-arr :int32       i) 1
                             (mem-aref seqid-vals 'llama-seq-id i) (%beam-seq-id beam)
                             (mem-aref seqid-ptrs :pointer    i)
                             (inc-pointer seqid-vals (* i (foreign-type-size 'llama-seq-id)))))
              ;; build logits marker: 1 for every slot so we get logits for all
              (with-foreign-object (logits-arr :int8 n)
                (loop for i below n do (setf (mem-aref logits-arr :int8 i) 1))
                ;; fill batch struct fields
                (setf (foreign-slot-value batch-ptr '(:struct llama-batch) 'n-tokens) n
                      (foreign-slot-value batch-ptr '(:struct llama-batch) 'token)    tok-arr
                      (foreign-slot-value batch-ptr '(:struct llama-batch) 'embd)     (null-pointer)
                      (foreign-slot-value batch-ptr '(:struct llama-batch) 'pos)      pos-arr
                      (foreign-slot-value batch-ptr '(:struct llama-batch) 'n-seq-id) nseq-arr
                      (foreign-slot-value batch-ptr '(:struct llama-batch) 'seq-id)   seqid-ptrs
                      (foreign-slot-value batch-ptr '(:struct llama-batch) 'logits)   logits-arr)
                (%cl-llama-decode *current-context* batch-ptr)))))))))

(defun beam-search (prompt &key (beam-width 5) (branching-factor 10) (max-tokens 300))
  "Run beam search on PROMPT with BEAM-WIDTH parallel sequences.
Returns list of (logprob . string) cons cells sorted best-first.

Algorithm:
  1. Decode prompt with seq_id=0; read logits from last prompt position.
  2. Clone prompt KV to seq_ids 1..K-1.
  3. Initialize K beams with the top-K tokens from the prompt logits.
  4. Generation loop: decode last token of each live beam, expand, prune, KV fixup."
  (unless *current-context*
    (error "No model loaded. Call (load-model ...) first."))
  (with-llama-fenv
    (let* ((prompt-tokens (tokenize prompt :add-special t))
           (n-prompt (length prompt-tokens))
           (vocab-size (%llama-vocab-n-tokens *current-vocab*)))
      (with-foreign-object (tok-buf 'llama-token n-prompt)
        (loop for i below n-prompt
              for tok in prompt-tokens
              do (setf (mem-aref tok-buf 'llama-token i) tok))
        ;; Decode prompt with explicit seq_id=0; logits enabled only for last position.
        (%decode-prompt tok-buf n-prompt 0)
        ;; Read logits from the last prompt position.
        ;; %decode-prompt enables logits only for slot (n-prompt-1), not slot 0.
        (let* ((init-lptr (%llama-get-logits-ith *current-context* (1- n-prompt)))
               (init-top (log-softmax-top-k init-lptr vocab-size
                                             (max beam-width branching-factor)))
               ;; Clone prompt KV to all K sequences.
               (mem (%llama-get-memory *current-context*)))
          (loop for k from 1 below beam-width
                do (%llama-memory-seq-cp mem 0 k -1 -1))
          ;; Initialize beams: each beam's first token is one of the top-K from init-top.
          (let ((beams (loop for k below beam-width
                             for (tok . lp) in init-top
                             collect (list :seq-id  k
                                           :tokens  (list tok)
                                           :logprob lp
                                           :done    (%llama-vocab-is-eog *current-vocab* tok)))))
            (with-foreign-object (batch-ptr '(:struct llama-batch))
              ;; GENERATION LOOP: decode generated tokens (not re-decoding prompt).
              ;; Each beam.tokens holds already-generated tokens.
              ;; Decoding last(beam.tokens) at position (n-prompt + len - 1) gives
              ;; logits for the next token.
              (loop for step below max-tokens
                    while (some (lambda (b) (not (%beam-done b))) beams)
                    do
                    (let ((live (remove-if #'%beam-done beams)))
                      ;; Tag beams with the token to feed (last generated token).
                      (setf live (mapcar (lambda (b)
                                           (let ((p (copy-list b)))
                                             (setf (getf p :%next-token)
                                                   (car (last (%beam-tokens b))))
                                             p))
                                         live))
                      (when (/= 0 (%decode-beam-step live n-prompt batch-ptr))
                        (error "Beam search: decode failed at step ~A" step))
                      ;; EXPAND
                      (let ((candidates nil))
                        (loop for i below (length live)
                              for beam in live
                              for lptr = (%llama-get-logits-ith *current-context* i)
                              for top  = (log-softmax-top-k lptr vocab-size branching-factor)
                              do (dolist (tok-lp top)
                                   (push (list :src-beam beam
                                               :token (car tok-lp)
                                               :score (+ (%beam-logprob beam) (cdr tok-lp)))
                                         candidates)))
                        ;; PRUNE
                        (setf candidates
                              (subseq (sort candidates #'> :key (lambda (c) (getf c :score)))
                                      0 (min beam-width (length candidates))))
                        ;; KV FIXUP: copy each survivor's src KV to a temp slot first
                        ;; (avoids clobbering a src still needed by another survivor),
                        ;; then remove old seqs, then move temp to final slots.
                        (let ((new-beams nil))
                          (loop for new-id below (length candidates)
                                for cand in candidates
                                for src-beam = (getf cand :src-beam)
                                for src-id   = (%beam-seq-id src-beam)
                                do (%llama-memory-seq-cp mem src-id
                                                         (+ beam-width new-id) -1 -1)
                                   (push (list :seq-id  new-id
                                               :tokens  (append (%beam-tokens src-beam)
                                                                 (list (getf cand :token)))
                                               :logprob (getf cand :score)
                                               :done    (%llama-vocab-is-eog
                                                          *current-vocab*
                                                          (getf cand :token)))
                                         new-beams))
                          (loop for old-id below beam-width
                                do (%llama-memory-seq-rm mem old-id -1 -1))
                          (loop for new-id below (length candidates)
                                do (%llama-memory-seq-cp mem (+ beam-width new-id)
                                                          new-id -1 -1)
                                   (%llama-memory-seq-rm mem (+ beam-width new-id)
                                                          -1 -1))
                          (setf beams (nreverse new-beams))))))
              ;; RETURN
              (let ((results
                     (sort (mapcar (lambda (b)
                                     (cons (%beam-logprob b)
                                           (apply #'concatenate 'string
                                                  (mapcar #'token-to-string
                                                          (%beam-tokens b)))))
                                   beams)
                           #'> :key #'car)))
                (loop for k below beam-width
                      do (%llama-memory-seq-rm mem k -1 -1))
                results))))))))
