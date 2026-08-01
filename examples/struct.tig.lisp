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
(defstruct (|Point| (:conc-name |Point/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Point| (:include |Point| (|tag| 0))
  (:conc-name |Point/|)
  (:constructor |mk/Point| (|f0| |f1|))
  (:predicate |Point?|))
  (|f0| 0 :type integer)
  (|f1| 0 :type integer))

; gapply
(defun gapply2 (c a1 a2)
  (if (eql (clos-arity c) 2)
    (funcall (clos-fn c) a1 a2)
    (%apply-slow c (list a1 a2))))

; ftype
(declaim (ftype (function (integer integer) boolean) |fn-29|))

(declaim (ftype (function (t) null) |println-2|))

(declaim (ftype (function (|Point|) integer) |distancePow-3|))

(declaim (ftype (function (t) clos) |getEq-5|))

(declaim (type cons |main-6|))

; body
(defun |fn-29| (|x-16| |y-17|)
  (%int= |x-16| |y-17|))

(defun |println-2| (|η-7|)
  (%println |η-7|))

(defun |distancePow-3| (|?x₀-9|)
  (case (|Point/tag| |?x₀-9|)
    (0
      (let* ((|f-10| (|Point/f0| |?x₀-9|))
             (|f-11| (|Point/f1| |?x₀-9|)))
         (let* ((|π-12| (%int* |f-10| |f-10|))
                (|π-13| (%int* |f-11| |f-11|)))
            (%int+ |π-12| |π-13|))))
    (t (error "unreachable"))))

(defun |getEq-5| (|?x₀-20|)
  |?x₀-20|)

(defparameter |i_Eq_0-4|
  (%clos (function |fn-29|) 2))

(defparameter |main-6|
  (let* ((|app-22| (|getEq-5| |i_Eq_0-4|))
         (|app-23| (gapply2 |app-22| 10 10))
         (|app-24| (|println-2| |app-23|))
         (|con-25| (|mk/Point| 6 8))
         (|app-26| (|distancePow-3| |con-25|))
         (|app-27| (|println-2| |app-26|)))
     (cons |app-24| |app-27|)))
