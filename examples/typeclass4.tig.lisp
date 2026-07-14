;; == Linked Lisp Source ==
(load "ffi.lisp")

; Prelude
(declaim (optimize (speed 3) (safety 0) (debug 0)))
(load "runtime.lisp")
(defstruct (clos (:constructor %clos (fn arity)))
  (fn #'identity :type function)
  (arity 0 :type fixnum))
(defun %apply-slow (c args)
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
(defun gapply2 (c a1 a2)
  (if (eql (clos-arity c) 2)
    (funcall (clos-fn c) a1 a2)
    (%apply-slow c (list a1 a2))))

; ftype
(declaim (ftype (function (t) clos) |listEq-3|))

(declaim (ftype (function (integer integer) boolean) |fn-76|))

(declaim (ftype (function (t |List| |List|) boolean) |listEq-77|))

(declaim (ftype (function (t |Option| |Option|) boolean) |fn-78|))

(declaim (type cons |main-6|))

; body
(defun |listEq-3| (|d_Eq_0-12|)
  (let* ((|listEq-13| (%clos (lambda (|g0| |g1|)
               (|listEq-77| |d_Eq_0-12| |g0| |g1|))
             2)))
     |listEq-13|))

(defun |i_Eq_1-4| (|d_Eq_0-23|)
  (let* ((|fn-24| (%clos (lambda (|g2| |g3|)
               (|fn-78| |d_Eq_0-23| |g2| |g3|))
             2)))
     |fn-24|))

(defun |i_Eq_2-5| (|d_Eq_0-32|)
  (let* ((|app-33| (|listEq-3| |d_Eq_0-32|))) |app-33|))

(defun |fn-76| (|x-8| |y-9|)
  (let* ((|π-10| (%int= |x-8| |y-9|))) |π-10|))

(defun |listEq-77| (|d_Eq_0-12| |?x₀-14| |?x₁-15|)
  (case (|List/tag| |?x₀-14|)
    (0
      (case (|List/tag| |?x₁-15|)
        (0
          t)
        (t nil)))
    (1
      (let* ((|f-16| (|Cons/f0| |?x₀-14|))
             (|f-17| (|Cons/f1| |?x₀-14|)))
         (case (|List/tag| |?x₁-15|)
           (1
             (let* ((|f-18| (|Cons/f0| |?x₁-15|))
                    (|f-19| (|Cons/f1| |?x₁-15|)))
                (let* ((|app-21| (gapply2 |d_Eq_0-12| |f-16| |f-18|)))
                   (if |app-21|
                     (let* ((|app-22| (|listEq-77| |d_Eq_0-12| |f-17| |f-19|)))
                        |app-22|)
                     nil))))
           (t nil))))
    (t nil)))

(defun |fn-78| (|d_Eq_0-23| |?x₀-25| |?x₁-26|)
  (case (|Option/tag| |?x₀-25|)
    (0
      (case (|Option/tag| |?x₁-26|)
        (0
          t)
        (t nil)))
    (1
      (let* ((|f-27| (|Some/f0| |?x₀-25|)))
         (case (|Option/tag| |?x₁-26|)
           (1
             (let* ((|f-28| (|Some/f0| |?x₁-26|)))
                (let* ((|app-30| (gapply2 |d_Eq_0-23| |f-27| |f-28|)))
                   |app-30|)))
           (t nil))))
    (t nil)))

(defparameter |i_Eq_0-2|
  (let* ((|fn-7| (%clos (function |fn-76|) 2))) |fn-7|))

(defparameter |main-6|
  (let* ((|app-35| (|i_Eq_2-5| |i_Eq_0-2|))
         (|app-36| (|i_Eq_1-4| |i_Eq_0-2|))
         (|con-38| (|mk/Nil|))
         (|con-39| (|mk/Cons| 2 |con-38|))
         (|con-40| (|mk/Cons| 1 |con-39|))
         (|con-41| (|mk/Nil|))
         (|con-42| (|mk/Cons| 3 |con-41|))
         (|con-43| (|mk/Cons| 2 |con-42|))
         (|con-44| (|mk/Cons| 1 |con-43|))
         (|app-45| (gapply2 |app-35| |con-40| |con-44|))
         (|con-47| (|mk/Nil|))
         (|con-48| (|mk/Cons| 3 |con-47|))
         (|con-49| (|mk/Cons| 2 |con-48|))
         (|con-50| (|mk/Cons| 1 |con-49|))
         (|con-51| (|mk/Nil|))
         (|con-52| (|mk/Cons| 3 |con-51|))
         (|con-53| (|mk/Cons| 2 |con-52|))
         (|con-54| (|mk/Cons| 1 |con-53|))
         (|app-55| (gapply2 |app-35| |con-50| |con-54|))
         (|con-57| (|mk/Some| 1))
         (|con-58| (|mk/Some| 2))
         (|app-59| (gapply2 |app-36| |con-57| |con-58|))
         (|con-61| (|mk/Some| 1))
         (|con-62| (|mk/Some| 1))
         (|app-63| (gapply2 |app-36| |con-61| |con-62|))
         (|con-65| (|mk/Some| 1))
         (|con-66| (|mk/None|))
         (|app-67| (gapply2 |app-36| |con-65| |con-66|))
         (|con-68| (|mk/Some| 2))
         (|con-69| (|mk/None|))
         (|p-70| (cons |con-68| |con-69|))
         (|p-71| (cons |app-67| |p-70|))
         (|p-72| (cons |app-63| |p-71|))
         (|p-73| (cons |app-59| |p-72|))
         (|p-74| (cons |app-55| |p-73|))
         (|p-75| (cons |app-45| |p-74|)))
     |p-75|))

(format t "~S~%" |main-6|)
