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
(declaim (ftype (function (t) clos) |unwrapBoxed-3|))

(declaim (type clos |unboxedAdd'-4|))

(declaim (ftype (function (integer integer) integer) |fn-20|))

(declaim (type cons |main-5|))

; body
(defun |unwrapBoxed-3| (|?x₀-11|)
  |?x₀-11|)

(defun |fn-20| (|?x₀-7| |?x₁-8|)
  (let* ((|π-9| (%int+ |?x₀-7| |?x₁-8|))) |π-9|))

(defparameter |boxedAdd-2|
  (let* ((|fn-6| (%clos (function |fn-20|) 2))) |fn-6|))

(defparameter |pb#13-14|
  |boxedAdd-2|)

(defparameter |unboxedAdd'-4|
  |pb#13-14|)

(defparameter |main-5|
  (let* ((|app-16| (|unwrapBoxed-3| |boxedAdd-2|))
         (|app-17| (gapply2 |app-16| 20 20))
         (|app-18| (gapply2 |unboxedAdd'-4| 30 30))
         (|p-19| (cons |app-17| |app-18|)))
     |p-19|))
