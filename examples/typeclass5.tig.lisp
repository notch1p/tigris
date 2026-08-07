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
(defstruct (|List| (:conc-name |List/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Nil| (:include |List| (|tag| 0))
  (:conc-name |Nil/|)
  (:constructor |mk/Nil| ())
  (:predicate |Nil?|)))

(defstruct (|c/Cons| (:include |List| (|tag| 1))
  (:conc-name |Cons/|)
  (:constructor |mk/Cons| (|f0| |f1|))
  (:predicate |Cons?|))
  (|f0| nil)
  (|f1| nil))

(defstruct (|Option| (:conc-name |Option/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/None| (:include |Option| (|tag| 0))
  (:conc-name |None/|)
  (:constructor |mk/None| ())
  (:predicate |None?|)))

(defstruct (|c/Some| (:include |Option| (|tag| 1))
  (:conc-name |Some/|)
  (:constructor |mk/Some| (|f0|))
  (:predicate |Some?|))
  (|f0| nil))

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
(declaim (ftype (function (clos |Option|) |Option|) |fn-40|))

(declaim (ftype (function (integer) integer) |fn-41|))

(declaim (ftype (function (clos |List|) |List|) |listMap-11|))

(declaim (type cons |main-25|))

; body
(defun |fn-40| (|f-4| |?x₀-5|)
  (case (|Option/tag| |?x₀-5|)
    (0
      (|mk/None|))
    (1
      (let* ((|f-7| (|Some/f0| |?x₀-5|)))
         (let* ((|app-8| (gapply1 |f-4| |f-7|))) (|mk/Some| |app-8|))))
    (t (error "unreachable"))))

(defun |fn-41| (|?x₀-28|)
  (%int+ 2 |?x₀-28|))

(defun |listMap-11| (|f-12| |?x₀-13|)
  (case (|List/tag| |?x₀-13|)
    (0
      (|mk/Nil|))
    (1
      (let* ((|f-15| (|Cons/f0| |?x₀-13|))
             (|f-16| (|Cons/f1| |?x₀-13|)))
         (let* ((|app-17| (gapply1 |f-12| |f-15|))
                (|app-18| (|listMap-11| |f-12| |f-16|)))
            (|mk/Cons| |app-17| |app-18|))))
    (t (error "unreachable"))))

(defun |const-22| (|x-23| |_-24|)
  |x-23|)

(defparameter |i_Functor_0-2|
  (%clos (function |fn-40|) 2))

(defparameter |i_Functor_1-20|
  (%clos (function |listMap-11|) 2))

(defparameter |main-25|
  (let* ((|fn-27| (%clos (function |fn-41|) 1))
         (|con-30| (|mk/Some| 1))
         (|app-31| (|fn-40| |fn-27| |con-30|))
         (|app-33| (%clos (lambda (|g0|)
               (|const-22| t |g0|))
             1))
         (|con-34| (|mk/Nil|))
         (|con-35| (|mk/Cons| 3 |con-34|))
         (|con-36| (|mk/Cons| 2 |con-35|))
         (|con-37| (|mk/Cons| 1 |con-36|))
         (|app-38| (gapply2 |i_Functor_1-20| |app-33| |con-37|)))
     (cons |app-31| |app-38|)))
