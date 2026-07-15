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
(declaim (ftype (function (t clos) t) |run-3|))

(declaim (ftype (function (t clos) t) |bind-4|))

(declaim (ftype (function (clos) t) |callcc-5|))

(declaim (ftype (function (t clos) t) |fn-53|))

(declaim (ftype (function (clos clos t) t) |fn-55|))

(declaim (ftype (function (clos clos clos) t) |fn-54|))

(declaim (ftype (function (t clos clos) t) |fn-58|))

(declaim (ftype (function (clos t) t) |fn-57|))

(declaim (ftype (function (clos clos) t) |fn-56|))

(declaim (ftype (function (clos integer) t) |fn-60|))

(declaim (ftype (function (clos) t) |fn-59|))

(declaim (ftype (function (integer) integer) |fn-61|))

(declaim (type integer |main-7|))

; body
(defun |return-2| (|x-8|)
  (let* ((|fn-9| (%clos (lambda (|g0|)
               (|fn-53| |x-8| |g0|))
             1)))
     |fn-9|))

(defun |run-3| (|c-13| |k-14|)
  (let* ((|app-16| (gapply1 |c-13| |k-14|))) |app-16|))

(defun |bind-4| (|?x₀-17| |f-18|)
  (let* ((|fn-20| (%clos (lambda (|g1|)
               (|fn-54| |f-18| |?x₀-17| |g1|))
             1)))
     |fn-20|))

(defun |callcc-5| (|f-29|)
  (let* ((|fn-30| (%clos (lambda (|g2|)
               (|fn-56| |f-29| |g2|))
             1)))
     |fn-30|))

(defun |fn-53| (|x-8| |k-10|)
  (let* ((|app-11| (gapply1 |k-10| |x-8|))) |app-11|))

(defun |fn-55| (|f-18| |k-21| |a-23|)
  (let* ((|app-24| (gapply1 |f-18| |a-23|))
         (|app-26| (gapply1 |app-24| |k-21|)))
     |app-26|))

(defun |fn-54| (|f-18| |f-19| |k-21|)
  (let* ((|fn-22| (%clos (lambda (|g3|)
               (|fn-55| |f-18| |k-21| |g3|))
             1))
         (|app-27| (gapply1 |f-19| |fn-22|)))
     |app-27|))

(defun |fn-58| (|a-33| |k-31| |_-35|)
  (let* ((|app-36| (gapply1 |k-31| |a-33|))) |app-36|))

(defun |fn-57| (|k-31| |a-33|)
  (let* ((|fn-34| (%clos (lambda (|g4|)
               (|fn-58| |a-33| |k-31| |g4|))
             1)))
     |fn-34|))

(defun |fn-56| (|f-29| |k-31|)
  (let* ((|fn-32| (%clos (lambda (|g5|)
               (|fn-57| |k-31| |g5|))
             1))
         (|app-38| (gapply1 |f-29| |fn-32|))
         (|app-40| (gapply1 |app-38| |k-31|)))
     |app-40|))

(defun |fn-60| (|k-43| |_-46|)
  (let* ((|app-47| (gapply1 |k-43| 42))) |app-47|))

(defun |fn-59| (|k-43|)
  (let* ((|app-44| (|return-2| 0))
         (|fn-45| (%clos (lambda (|g6|)
               (|fn-60| |k-43| |g6|))
             1))
         (|app-48| (|bind-4| |app-44| |fn-45|)))
     |app-48|))

(defun |fn-61| (|x-51|)
  |x-51|)

(defparameter |f-6|
  (let* ((|fn-42| (%clos (function |fn-59|) 1))
         (|app-49| (|callcc-5| |fn-42|)))
     |app-49|))

(defparameter |main-7|
  (let* ((|fn-50| (%clos (function |fn-61|) 1))
         (|app-52| (|run-3| |f-6| |fn-50|)))
     |app-52|))
