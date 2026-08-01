;; == Linked Lisp Source ==
(load "ffi.lisp")

; Prelude
(declaim (optimize (speed 3) (safety 0) (debug 0)))
(load "runtime.lisp")
(defstruct (clos (:constructor %clos (fn arity)))
  (fn #'identity :type function)
  (arity 0 :type fixnum))
(defun %apply-slow (c args)
  (declare (type list args))
  (let ((n (length args)) (k (clos-arity c)))
    (cond
      ((= n k) (apply (clos-fn c) args))
      ((< n k) (%clos (lambda (&rest more)
                        (apply (clos-fn c)
                               (append args more)))
                      (- k n)))
      (t (%apply-slow (apply (clos-fn c)
                             (subseq args 0 k))
                      (nthcdr k args))))))


; struct
(defstruct (|Sum| (:conc-name |Sum/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Inl| (:include |Sum| (|tag| 0))
  (:conc-name |Inl/|)
  (:constructor |mk/Inl| (|f0|))
  (:predicate |Inl?|))
  (|f0| nil))

(defstruct (|c/Inr| (:include |Sum| (|tag| 1))
  (:conc-name |Inr/|)
  (:constructor |mk/Inr| (|f0|))
  (:predicate |Inr?|))
  (|f0| nil))

; gapply
(defun gapply1 (c a1)
  (if (eql (clos-arity c) 1)
    (funcall (clos-fn c) a1)
    (%apply-slow c (list a1))))

; ftype
(declaim (ftype (function (clos |Sum|) |Sum|) |fn-26|))

(declaim (ftype (function (integer) integer) |fn-27|))

(declaim (ftype (function (integer) integer) |fn-28|))

(declaim (type cons |main-3|))

; body
(defun |fn-26| (|f-5| |?x₀-6|)
  (case (|Sum/tag| |?x₀-6|)
    (0
      (let* ((|f-7| (|Inl/f0| |?x₀-6|))) (|mk/Inl| |f-7|)))
    (1
      (let* ((|f-9| (|Inr/f0| |?x₀-6|)))
         (let* ((|app-10| (gapply1 |f-5| |f-9|))) (|mk/Inr| |app-10|))))
    (t (error "unreachable"))))

(defun |fn-27| (|?x₀-17|)
  (%int* 2 |?x₀-17|))

(defun |fn-28| (|?x₀-22|)
  (%int+ 1 |?x₀-22|))

(defparameter |i_Functor_0-2|
  (%clos (function |fn-26|) 2))

(defparameter |main-3|
  (let* ((|con-13| (|mk/Inl| 2))
         (|con-14| (|mk/Inr| 1))
         (|fn-16| (%clos (function |fn-27|) 1))
         (|app-19| (|fn-26| |fn-16| |con-13|))
         (|fn-21| (%clos (function |fn-28|) 1))
         (|app-24| (|fn-26| |fn-21| |con-14|)))
     (cons |app-19| |app-24|)))
