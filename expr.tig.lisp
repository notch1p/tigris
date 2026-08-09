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
(defstruct (|Expr| (:conc-name |Expr/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Atom| (:include |Expr| (|tag| 0))
  (:conc-name |Atom/|)
  (:constructor |mk/Atom| (|f0|))
  (:predicate |Atom?|))
  (|f0| nil))

(defstruct (|c/Add| (:include |Expr| (|tag| 1))
  (:conc-name |Add/|)
  (:constructor |mk/Add| (|f0| |f1|))
  (:predicate |Add?|))
  (|f0| nil)
  (|f1| nil))

(defstruct (|c/Sub| (:include |Expr| (|tag| 2))
  (:conc-name |Sub/|)
  (:constructor |mk/Sub| (|f0| |f1|))
  (:predicate |Sub?|))
  (|f0| nil)
  (|f1| nil))

(defstruct (|c/Mul| (:include |Expr| (|tag| 3))
  (:conc-name |Mul/|)
  (:constructor |mk/Mul| (|f0| |f1|))
  (:predicate |Mul?|))
  (|f0| nil)
  (|f1| nil))

(defstruct (|c/Div| (:include |Expr| (|tag| 4))
  (:conc-name |Div/|)
  (:constructor |mk/Div| (|f0| |f1|))
  (:predicate |Div?|))
  (|f0| nil)
  (|f1| nil))

; ftype
(declaim (ftype (function (|Expr|) integer) |eval-2|))

(declaim (type |Expr| |prog-25|))

(declaim (type integer |pb#41-42|))

(declaim (type integer |pb#41-chk-44|))

(declaim (type null |main-47|))

; body
(defun |eval-2| (|?x₀-3|)
  (case (|Expr/tag| |?x₀-3|)
    (1
      (let* ((|f-4| (|Add/f0| |?x₀-3|))
             (|f-5| (|Add/f1| |?x₀-3|)))
         (let* ((|app-6| (|eval-2| |f-4|))
                (|app-7| (|eval-2| |f-5|)))
            (%int+ |app-6| |app-7|))))
    (4
      (let* ((|f-9| (|Div/f0| |?x₀-3|))
             (|f-10| (|Div/f1| |?x₀-3|)))
         (let* ((|app-11| (|eval-2| |f-9|))
                (|app-12| (|eval-2| |f-10|)))
            (%int/ |app-11| |app-12|))))
    (3
      (let* ((|f-14| (|Mul/f0| |?x₀-3|))
             (|f-15| (|Mul/f1| |?x₀-3|)))
         (let* ((|app-16| (|eval-2| |f-14|))
                (|app-17| (|eval-2| |f-15|)))
            (%int* |app-16| |app-17|))))
    (0
      (let* ((|f-19| (|Atom/f0| |?x₀-3|))) |f-19|))
    (2
      (let* ((|f-20| (|Sub/f0| |?x₀-3|))
             (|f-21| (|Sub/f1| |?x₀-3|)))
         (let* ((|app-22| (|eval-2| |f-20|))
                (|app-23| (|eval-2| |f-21|)))
            (%int- |app-22| |app-23|))))
    (t (error "unreachable"))))

(defparameter |prog-25|
  (let* ((|con-26| (|mk/Atom| 20))
         (|con-27| (|mk/Atom| 10))
         (|con-28| (|mk/Atom| 20))
         (|con-29| (|mk/Mul| |con-27| |con-28|))
         (|con-30| (|mk/Atom| 2400))
         (|con-31| (|mk/Atom| 120))
         (|con-32| (|mk/Atom| 10))
         (|con-33| (|mk/Atom| 20))
         (|con-34| (|mk/Mul| |con-32| |con-33|))
         (|con-35| (|mk/Atom| 0))
         (|con-36| (|mk/Add| |con-34| |con-35|))
         (|con-37| (|mk/Add| |con-31| |con-36|))
         (|con-38| (|mk/Div| |con-30| |con-37|))
         (|con-39| (|mk/Sub| |con-29| |con-38|)))
     (|mk/Mul| |con-26| |con-39|)))

(defparameter |pb#41-42|
  (|eval-2| |prog-25|))

(defparameter |pb#41-chk-44|
  (labels ((|fail-45| () (error 'match-failure :discr (list |pb#41-42|))))
     (case |pb#41-42|
       (3850
         |pb#41-42|)
       (t (|fail-45|)))))

(defparameter |main-47|
  nil)

(format t "~S~%" |main-47|)
