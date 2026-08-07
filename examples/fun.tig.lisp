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


; gapply
(defun gapply2 (c a1 a2)
  (if (eql (clos-arity c) 2)
    (funcall (clos-fn c) a1 a2)
    (%apply-slow c (list a1 a2))))

; ftype
(declaim (ftype (function (integer integer) integer) |fn-20|))

(declaim (ftype (function (t) clos) |unwrapBoxed-8|))

(declaim (type clos |unboxedAdd'-13|))

(declaim (type cons |main-15|))

; body
(defun |fn-20| (|?x₀-4| |?x₁-5|)
  (%int+ |?x₀-4| |?x₁-5|))

(defun |unwrapBoxed-8| (|?x₀-9|)
  |?x₀-9|)

(defparameter |boxedAdd-2|
  (%clos (function |fn-20|) 2))

(defparameter |pb#11-12|
  |boxedAdd-2|)

(defparameter |unboxedAdd'-13|
  |pb#11-12|)

(defparameter |main-15|
  (let* ((|app-16| (|unwrapBoxed-8| |boxedAdd-2|))
         (|app-17| (gapply2 |app-16| 20 20))
         (|app-18| (gapply2 |unboxedAdd'-13| 30 30)))
     (cons |app-17| |app-18|)))
