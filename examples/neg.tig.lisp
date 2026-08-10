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


; ftype
(declaim (ftype (function (integer) integer) |fn-11|))

(declaim (type integer |main-7|))

; body
(defun |fn-11| (|x-4|)
  (%int- 0 |x-4|))

(defparameter |i_Neg_0-2|
  (%clos (function |fn-11|) 1))

(defparameter |main-7|
  (let* ((|v-8| 1)) (|fn-11| |v-8|)))
