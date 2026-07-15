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

(declaim (ftype (function (|Option| |Option|) |Option|) |«<*>»-3|))

(declaim (type cons |main-4|))

; body
(defun |«<+>»-2| (|xs-5| |ys-6|)
  (case (|List/tag| |xs-5|)
    (0
      (case (|List/tag| |ys-6|)
        (0
          0)
        (t 0)))
    (1
      (let* ((|f-7| (|Cons/f0| |xs-5|))
             (|f-8| (|Cons/f1| |xs-5|)))
         (case (|List/tag| |ys-6|)
           (1
             (let* ((|f-9| (|Cons/f0| |ys-6|))
                    (|f-10| (|Cons/f1| |ys-6|)))
                (let* ((|π-11| (%int+ |f-7| |f-9|))
                       (|app-12| (|«<+>»-2| |f-8| |f-10|))
                       (|π-13| (%int+ |π-11| |app-12|)))
                   |π-13|)))
           (t 0))))
    (t 0)))

(defun |«<*>»-3| (|?x₀-14| |?x₁-15|)
  (labels ((|fail-16| ()
             (let* ((|fail-17| (error 'match-failure
                        :discr
                        "no matching clause")))
                |fail-17|)))
     (case (|Option/tag| |?x₀-14|)
       (1
         (let* ((|f-18| (|Some/f0| |?x₀-14|)))
            (case (|Option/tag| |?x₁-15|)
              (1
                (let* ((|f-19| (|Some/f0| |?x₁-15|)))
                   (let* ((|π-20| (%int* |f-18| |f-19|))
                          (|con-21| (|mk/Some| |π-20|)))
                      |con-21|)))
              (t (|fail-16|)))))
       (t (|fail-16|)))))

(defparameter |main-4|
  (let* ((|con-22| (|mk/Nil|))
         (|con-23| (|mk/Cons| 456 |con-22|))
         (|con-24| (|mk/Cons| 123 |con-23|))
         (|con-25| (|mk/Nil|))
         (|con-26| (|mk/Cons| 290 |con-25|))
         (|con-27| (|mk/Cons| 374 |con-26|))
         (|app-28| (|«<+>»-2| |con-24| |con-27|))
         (|con-29| (|mk/Some| 2))
         (|con-30| (|mk/Some| 3))
         (|app-31| (|«<*>»-3| |con-29| |con-30|))
         (|con-32| (|mk/Some| 4))
         (|app-33| (|«<*>»-3| |app-31| |con-32|))
         (|p-34| (cons |app-28| |app-33|)))
     |p-34|))
