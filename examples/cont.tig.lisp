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

; ftype
(declaim (ftype (function (t clos) t) |fn-53|))

(declaim (ftype (function (clos clos t) t) |fn-55|))

(declaim (ftype (function (clos clos clos) t) |fn-54|))

(declaim (ftype (function (clos t clos) t) |fn-58|))

(declaim (ftype (function (clos t) t) |fn-57|))

(declaim (ftype (function (clos clos) t) |fn-56|))

(declaim (ftype (function (clos integer) t) |fn-60|))

(declaim (ftype (function (clos) t) |fn-59|))

(declaim (ftype (function (integer) integer) |fn-61|))

(declaim (ftype (function (t clos) t) |run-8|))

(declaim (ftype (function (t clos) t) |bind-13|))

(declaim (ftype (function (clos) t) |call/cc-26|))

(declaim (type integer |main-49|))

; body
(defun |fn-53| (|x-3| |k-5|)
  (gapply1 |k-5| |x-3|))

(defun |fn-55| (|k-18| |f-15| |a-20|)
  (let* ((|app-21| (gapply1 |f-15| |a-20|))) (gapply1 |app-21| |k-18|)))

(defun |fn-54| (|f-16| |f-15| |k-18|)
  (let* ((|fn-19| (%clos (lambda (|g0|)
               (|fn-55| |k-18| |f-15| |g0|))
             1)))
     (gapply1 |f-16| |fn-19|)))

(defun |fn-58| (|k-29| |a-31| |_-33|)
  (gapply1 |k-29| |a-31|))

(defun |fn-57| (|k-29| |a-31|)
  (%clos (lambda (|g1|)
      (|fn-58| |k-29| |a-31| |g1|))
    1))

(defun |fn-56| (|f-27| |k-29|)
  (let* ((|fn-30| (%clos (lambda (|g2|)
               (|fn-57| |k-29| |g2|))
             1))
         (|app-36| (gapply1 |f-27| |fn-30|)))
     (gapply1 |app-36| |k-29|)))

(defun |fn-60| (|k-42| |_-45|)
  (gapply1 |k-42| 42))

(defun |fn-59| (|k-42|)
  (let* ((|app-43| (|return-2| 0))
         (|fn-44| (%clos (lambda (|g3|)
               (|fn-60| |k-42| |g3|))
             1)))
     (|bind-13| |app-43| |fn-44|)))

(defun |fn-61| (|x-51|)
  |x-51|)

(defun |return-2| (|x-3|)
  (%clos (lambda (|g4|)
      (|fn-53| |x-3| |g4|))
    1))

(defun |run-8| (|c-9| |k-10|)
  (gapply1 |c-9| |k-10|))

(defun |bind-13| (|?x₀-14| |f-15|)
  (%clos (lambda (|g5|)
      (|fn-54| |?x₀-14| |f-15| |g5|))
    1))

(defun |call/cc-26| (|f-27|)
  (%clos (lambda (|g6|)
      (|fn-56| |f-27| |g6|))
    1))

(defparameter |f-40|
  (let* ((|fn-41| (%clos (function |fn-59|) 1))) (|call/cc-26| |fn-41|)))

(defparameter |main-49|
  (let* ((|fn-50| (%clos (function |fn-61|) 1))) (|run-8| |f-40| |fn-50|)))
