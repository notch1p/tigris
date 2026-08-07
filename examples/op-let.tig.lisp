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

; ftype
(declaim (ftype (function (|List| |List|) integer) |«<+>»-2|))

(declaim (ftype (function (|Option| |Option|) |Option|) |«<*>»-12|))

(declaim (type cons |main-21|))

; body
(defun |«<+>»-2| (|xs-3| |ys-4|)
  (case (|List/tag| |xs-3|)
    (0
      (case (|List/tag| |ys-4|)
        (0
          0)
        (t 0)))
    (1
      (let* ((|f-5| (|Cons/f0| |xs-3|))
             (|f-6| (|Cons/f1| |xs-3|)))
         (case (|List/tag| |ys-4|)
           (1
             (let* ((|f-7| (|Cons/f0| |ys-4|))
                    (|f-8| (|Cons/f1| |ys-4|)))
                (let* ((|π-9| (%int+ |f-5| |f-7|))
                       (|app-10| (|«<+>»-2| |f-6| |f-8|)))
                   (%int+ |π-9| |app-10|))))
           (t 0))))
    (t 0)))

(defun |«<*>»-12| (|?x₀-13| |?x₁-14|)
  (labels ((|fail-15| ()
             (error 'match-failure :discr (list |?x₀-13| |?x₁-14|))))
     (case (|Option/tag| |?x₀-13|)
       (1
         (let* ((|f-17| (|Some/f0| |?x₀-13|)))
            (case (|Option/tag| |?x₁-14|)
              (1
                (let* ((|f-18| (|Some/f0| |?x₁-14|)))
                   (let* ((|π-19| (%int* |f-17| |f-18|))) (|mk/Some| |π-19|))))
              (t (|fail-15|)))))
       (t (|fail-15|)))))

(defparameter |main-21|
  (let* ((|con-22| (|mk/Nil|))
         (|con-23| (|mk/Cons| 456 |con-22|))
         (|con-24| (|mk/Cons| 123 |con-23|))
         (|con-25| (|mk/Nil|))
         (|con-26| (|mk/Cons| 290 |con-25|))
         (|con-27| (|mk/Cons| 374 |con-26|))
         (|app-28| (|«<+>»-2| |con-24| |con-27|))
         (|con-29| (|mk/Some| 2))
         (|con-30| (|mk/Some| 3))
         (|app-31| (|«<*>»-12| |con-29| |con-30|))
         (|con-32| (|mk/Some| 4))
         (|app-33| (|«<*>»-12| |app-31| |con-32|)))
     (cons |app-28| |app-33|)))
