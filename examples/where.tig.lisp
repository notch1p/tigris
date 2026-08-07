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
(defun gapply1 (c a1)
  (if (eql (clos-arity c) 1)
    (funcall (clos-fn c) a1)
    (%apply-slow c (list a1))))

(defun gapply2 (c a1 a2)
  (if (eql (clos-arity c) 2)
    (funcall (clos-fn c) a1 a2)
    (%apply-slow c (list a1 a2))))

; ftype
(declaim (ftype (function (integer) t) |B-25|))

(declaim (ftype (function (clos clos t t) t) |«`on`»-2|))

(declaim (ftype (function (t t) integer) |«^»-3|))

(declaim (type clos |boxedAdd-16|))

(declaim (type integer |main-21|))

; body
(defun |B-25| (|η-18|)
  |η-18|)

(defun |«`on`»-2| (|f-4| |g-5| |x-6| |y-7|)
  (let* ((|app-8| (gapply1 |g-5| |x-6|))
         (|app-9| (gapply1 |g-5| |y-7|)))
     (gapply2 |f-4| |app-8| |app-9|)))

(defun |«^»-3| (|?x₀-11| |?x₁-12|)
  (%int+ |?x₀-11| |?x₁-12|))

(defparameter |boxedAdd-16|
  (let* ((|B-17| (%clos (function |B-25|) 1)))
     (%clos (lambda (|g0| |g1|)
         (|«`on`»-2| (%clos (function |«^»-3|) 2) |B-17| |g0| |g1|))
       2)))

(defparameter |main-21|
  (|«`on`»-2| (%clos (function |«^»-3|) 2) (%clos (function |B-25|) 1) 20 30))
