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

(declaim (ftype (function (|Point|) integer) |distancePow-5|))

(declaim (ftype (function (t) clos) |getEq-18|))

(declaim (type cons |main-21|))

; body
(defun |fn-29| (|x-14| |y-15|)
  (%int= |x-14| |y-15|))

(defun |println-2| (|η-3|)
  (%println |η-3|))

(defun |distancePow-5| (|?x₀-6|)
  (case (|Point/tag| |?x₀-6|)
    (0
      (let* ((|f-7| (|Point/f0| |?x₀-6|))
             (|f-8| (|Point/f1| |?x₀-6|)))
         (let* ((|π-9| (%int* |f-7| |f-7|))
                (|π-10| (%int* |f-8| |f-8|)))
            (%int+ |π-9| |π-10|))))
    (t (error "unreachable"))))

(defun |getEq-18| (|?x₀-19|)
  |?x₀-19|)

(defparameter |i_Eq_0-12|
  (%clos (function |fn-29|) 2))

(defparameter |main-21|
  (let* ((|app-22| (|getEq-18| |i_Eq_0-12|))
         (|app-23| (gapply2 |app-22| 10 10))
         (|app-24| (|println-2| |app-23|))
         (|con-25| (|mk/Point| 6 8))
         (|app-26| (|distancePow-5| |con-25|))
         (|app-27| (|println-2| |app-26|)))
     (cons |app-24| |app-27|)))
