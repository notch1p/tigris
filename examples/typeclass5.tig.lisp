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

(declaim (ftype (function (clos |List|) |List|) |listMap-3|))

(declaim (type cons |main-6|))

; body
(defun |fn-40| (|f-8| |?x₀-9|)
  (case (|Option/tag| |?x₀-9|)
    (0
      (let* ((|con-10| (|mk/None|))) |con-10|))
    (1
      (let* ((|f-11| (|Some/f0| |?x₀-9|)))
         (let* ((|app-12| (gapply1 |f-8| |f-11|))
                (|con-13| (|mk/Some| |app-12|)))
            |con-13|)))
    (t (error "unreachable"))))

(defun |fn-41| (|?x₀-28|)
  (let* ((|π-29| (%int+ 2 |?x₀-28|))) |π-29|))

(defun |listMap-3| (|f-15| |?x₀-16|)
  (case (|List/tag| |?x₀-16|)
    (0
      (let* ((|con-17| (|mk/Nil|))) |con-17|))
    (1
      (let* ((|f-18| (|Cons/f0| |?x₀-16|))
             (|f-19| (|Cons/f1| |?x₀-16|)))
         (let* ((|app-20| (gapply1 |f-15| |f-18|))
                (|app-21| (|listMap-3| |f-15| |f-19|))
                (|con-22| (|mk/Cons| |app-20| |app-21|)))
            |con-22|)))
    (t (error "unreachable"))))

(defun |const-5| (|x-24| |_-25|)
  |x-24|)

(defparameter |i_Functor_0-2|
  (let* ((|fn-7| (%clos (function |fn-40|) 2))) |fn-7|))

(defparameter |i_Functor_1-4|
  (%clos (function |listMap-3|) 2))

(defparameter |main-6|
  (let* ((|fn-27| (%clos (function |fn-41|) 1))
         (|con-30| (|mk/Some| 1))
         (|app-31| (|fn-40| |fn-27| |con-30|))
         (|app-33| (%clos (lambda (|g0|)
               (|const-5| t |g0|))
             1))
         (|con-34| (|mk/Nil|))
         (|con-35| (|mk/Cons| 3 |con-34|))
         (|con-36| (|mk/Cons| 2 |con-35|))
         (|con-37| (|mk/Cons| 1 |con-36|))
         (|app-38| (gapply2 |i_Functor_1-4| |app-33| |con-37|))
         (|p-39| (cons |app-31| |app-38|)))
     |p-39|))
