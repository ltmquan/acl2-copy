(in-package :cl-llama)

;; Type aliases matching llama.h
(defctype llama-token :int32)
(defctype llama-pos   :int32)
(defctype llama-seq-id :int32)

;; The llama_batch struct, as a CFFI struct
(defcstruct llama-batch
  (n-tokens :int32)
  (token    :pointer)   ; llama_token *
  (embd     :pointer)   ; float *
  (pos      :pointer)   ; llama_pos *
  (n-seq-id :pointer)   ; int32_t *
  (seq-id   :pointer)   ; llama_seq_id **
  (logits   :pointer))  ; int8_t *

;; --- Init / teardown ---
(defcfun ("llama_backend_init" %llama-backend-init) :void)
(defcfun ("llama_backend_free" %llama-backend-free) :void)
(defcfun ("llama_log_set" %llama-log-set) :void
  (log-callback :pointer)
  (user-data    :pointer))

;; --- Model ---
;; llama_model_params and llama_context_params are large structs.
;; We won't define them as CFFI structs (too brittle across versions).
;; Instead we call the *_default_params functions, which return the struct
;; by value, and pass it straight through. CFFI handles this with :pointer
;; if we treat the returned struct as opaque.
;;
;; The trick: these functions return structs BY VALUE. CFFI's portable way
;; to handle this is to declare them as returning the struct type and let
;; CFFI copy. But the struct is large and we don't want to mirror every
;; field. Workaround: we'll call into a tiny helper or use the fact that
;; on most platforms, the struct fits in a known memory layout we can
;; allocate.
;;
;; The cleanest approach: declare *_default_params as returning :pointer,
;; allocate space for the struct ourselves, and treat its contents as opaque.
;; This requires us to know the struct size. For llama.cpp b9150 on arm64-darwin,
;; llama_model_params is around 88 bytes; llama_context_params is around 224.
;; We'll allocate generously (256 / 512 bytes) to be safe and tweak if needed.
;;
;; ACTUALLY: simpler path. The new API has helper init functions that take the
;; params struct as the LAST argument by value. Common Lisp can't natively pass
;; structs by value without CFFI struct definitions. So we DO need the structs.
;;
;; We'll define them. Yes it's tedious. No, there's no clean workaround.

;; --- llama_model_params struct ---
;; Note: order, padding, and types matter. Match llama.h exactly.
(defcstruct llama-model-params
  (devices                    :pointer)
  (tensor-buft-overrides      :pointer)
  (n-gpu-layers               :int32)
  (split-mode                 :int)     ; enum
  (main-gpu                   :int32)
  (tensor-split               :pointer)
  (progress-callback          :pointer)
  (progress-callback-user-data :pointer)
  (kv-overrides               :pointer)
  ;; Booleans clustered at end per the header comment
  (vocab-only                 :bool)
  (use-mmap                   :bool)
  (use-direct-io              :bool)
  (use-mlock                  :bool)
  (check-tensors              :bool)
  (use-extra-bufts            :bool)
  (no-host                    :bool)
  (no-alloc                   :bool))

(defcfun ("llama_model_default_params" %llama-model-default-params)
  (:struct llama-model-params))

(defcfun ("llama_model_load_from_file" %llama-model-load-from-file)
    :pointer
  (path :string)
  (params (:struct llama-model-params)))

(defcfun ("llama_model_free" %llama-model-free) :void
  (model :pointer))

(defcfun ("llama_model_get_vocab" %llama-model-get-vocab) :pointer
  (model :pointer))

;; --- llama_context_params struct ---
;; This one is bigger. Many fields, mix of ints, floats, enums, pointers, bools.
;; ggml_type is an enum (int). enum llama_*_type are all int-sized.

(defcstruct llama-context-params
  (n-ctx                :uint32)
  (n-batch              :uint32)
  (n-ubatch             :uint32)
  (n-seq-max            :uint32)
  (n-threads            :int32)
  (n-threads-batch      :int32)
  (rope-scaling-type    :int)       ; enum
  (pooling-type         :int)       ; enum
  (attention-type       :int)       ; enum
  (flash-attn-type      :int)       ; enum
  (rope-freq-base       :float)
  (rope-freq-scale      :float)
  (yarn-ext-factor      :float)
  (yarn-attn-factor     :float)
  (yarn-beta-fast       :float)
  (yarn-beta-slow       :float)
  (yarn-orig-ctx        :uint32)
  (defrag-thold         :float)
  (cb-eval              :pointer)
  (cb-eval-user-data    :pointer)
  (type-k               :int)       ; ggml_type enum
  (type-v               :int)       ; ggml_type enum
  (abort-callback       :pointer)
  (abort-callback-data  :pointer)
  (embeddings           :bool)
  (offload-kqv          :bool)
  (no-perf              :bool)
  (op-offload           :bool)
  (swa-full             :bool)
  (kv-unified           :bool)
  (samplers             :pointer)
  (n-samplers           :size))

(defcfun ("llama_context_default_params" %llama-context-default-params)
  (:struct llama-context-params))

(defcfun ("llama_init_from_model" %llama-init-from-model) :pointer
  (model :pointer)
  (params (:struct llama-context-params)))

(defcfun ("llama_free" %llama-free) :void
  (ctx :pointer))

;; --- Tokenization ---
(defcfun ("llama_tokenize" %llama-tokenize) :int32
  (vocab :pointer)
  (text :string)
  (text-len :int32)
  (tokens :pointer)
  (n-tokens-max :int32)
  (add-special :bool)
  (parse-special :bool))

(defcfun ("llama_token_to_piece" %llama-token-to-piece) :int32
  (vocab :pointer)
  (token llama-token)
  (buf :pointer)
  (length :int32)
  (lstrip :int32)
  (special :bool))

(defcfun ("llama_vocab_is_eog" %llama-vocab-is-eog) :bool
  (vocab :pointer)
  (token llama-token))

;; --- Batch / decode ---
(defcfun ("llama_batch_get_one" %llama-batch-get-one)
  (:struct llama-batch)
  (tokens :pointer)
  (n-tokens :int32))

(defcfun ("llama_decode" %llama-decode) :int32
  (ctx :pointer)
  (batch (:struct llama-batch)))

(defcfun ("llama_get_logits_ith" %llama-get-logits-ith) :pointer
  (ctx :pointer)
  (i :int32))

;; --- Sampler chain ---
(defcstruct llama-sampler-chain-params
  (no-perf :bool))

(defcfun ("llama_sampler_chain_default_params"
          %llama-sampler-chain-default-params)
  (:struct llama-sampler-chain-params))

(defcfun ("llama_sampler_chain_init" %llama-sampler-chain-init) :pointer
  (params (:struct llama-sampler-chain-params)))

(defcfun ("llama_sampler_chain_add" %llama-sampler-chain-add) :void
  (chain :pointer)
  (sampler :pointer))

(defcfun ("llama_sampler_init_temp" %llama-sampler-init-temp) :pointer
  (temp :float))

(defcfun ("llama_sampler_init_dist" %llama-sampler-init-dist) :pointer
  (seed :uint32))

(defcfun ("llama_sampler_sample" %llama-sampler-sample) llama-token
  (smpl :pointer)
  (ctx :pointer)
  (idx :int32))

(defcfun ("llama_sampler_accept" %llama-sampler-accept) :void
  (smpl :pointer)
  (token llama-token))

(defcfun ("llama_sampler_free" %llama-sampler-free) :void
  (smpl :pointer))

;; Bridge functions -- pointer wrappers for struct-by-value API boundaries.
;; cffi-libffi on SBCL arm64 corrupts boolean fields in structs >16 bytes
;; passed or returned by value; these wrappers avoid that ABI path entirely.
(defcfun ("cl_llama_model_default_params_into"
          %cl-llama-model-default-params-into) :void
  (out :pointer))

(defcfun ("cl_llama_model_load" %cl-llama-model-load) :pointer
  (path :string)
  (params :pointer))

(defcfun ("cl_llama_context_default_params_into"
          %cl-llama-context-default-params-into) :void
  (out :pointer))

(defcfun ("cl_llama_init_context" %cl-llama-init-context) :pointer
  (model :pointer)
  (params :pointer))

(defcfun ("cl_llama_sampler_chain_default_params_into"
          %cl-llama-sampler-chain-default-params-into) :void
  (out :pointer))

(defcfun ("cl_llama_sampler_chain_init" %cl-llama-sampler-chain-init) :pointer
  (params :pointer))

(defcfun ("cl_llama_decode" %cl-llama-decode) :int32
  (ctx :pointer)
  (batch :pointer))

;; --- Beam search primitives ---
(defcfun ("llama_get_memory" %llama-get-memory) :pointer
  (ctx :pointer))

(defcfun ("llama_vocab_n_tokens" %llama-vocab-n-tokens) :int32
  (vocab :pointer))

(defcfun ("llama_memory_seq_cp" %llama-memory-seq-cp) :void
  (mem    :pointer)
  (src    llama-seq-id)
  (dst    llama-seq-id)
  (p0     llama-pos)
  (p1     llama-pos))

(defcfun ("llama_memory_seq_rm" %llama-memory-seq-rm) :bool
  (mem    :pointer)
  (seq-id llama-seq-id)
  (p0     llama-pos)
  (p1     llama-pos))

(defcfun ("cl_llama_batch_init_into" %cl-llama-batch-init-into) :void
  (out       :pointer)
  (n-tokens  :int32)
  (embd      :int32)
  (n-seq-max :int32))

(defcfun ("cl_llama_batch_free" %cl-llama-batch-free) :void
  (batch :pointer))
