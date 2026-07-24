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

(declaim (type clos |boxedAdd-4|))

(declaim (type integer |main-5|))

; body
(defun |B-25| (|η-19|)
  |η-19|)

(defun |«`on`»-2| (|f-6| |g-7| |x-8| |y-9|)
  (let* ((|app-10| (gapply1 |g-7| |x-8|))
         (|app-11| (gapply1 |g-7| |y-9|))
         (|app-12| (gapply2 |f-6| |app-10| |app-11|)))
     |app-12|))

(defun |«^»-3| (|?x₀-13| |?x₁-14|)
  (let* ((|π-17| (%int+ |?x₀-13| |?x₁-14|))) |π-17|))

(defparameter |boxedAdd-4|
  (let* ((|B-18| (%clos (function |B-25|) 1))
         (|app-21| (%clos (lambda (|g0| |g1|)
               (|«`on`»-2| (%clos (function |«^»-3|) 2) |B-18| |g0| |g1|))
             2)))
     |app-21|))

(defparameter |main-5|
  (let* ((|app-24| (|«`on`»-2| (%clos (function |«^»-3|) 2)
             (%clos (function |B-25|) 1)
             20
             30)))
     |app-24|))
