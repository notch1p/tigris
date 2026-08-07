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
(defun gapply2 (c a1 a2)
  (if (eql (clos-arity c) 2)
    (funcall (clos-fn c) a1 a2)
    (%apply-slow c (list a1 a2))))

; ftype
(declaim (ftype (function (integer integer) boolean) |fn-76|))

(declaim (ftype (function (t |List| |List|) boolean) |listEq-77|))

(declaim (ftype (function (t |Option| |Option|) boolean) |fn-78|))

(declaim (ftype (function (t) clos) |listEq-8|))

(declaim (type cons |main-34|))

; body
(defun |fn-76| (|x-4| |y-5|)
  (%int= |x-4| |y-5|))

(defun |listEq-77| (|d_Eq_0-9| |?x₀-11| |?x₁-12|)
  (case (|List/tag| |?x₀-11|)
    (0
      (case (|List/tag| |?x₁-12|)
        (0
          t)
        (t nil)))
    (1
      (let* ((|f-13| (|Cons/f0| |?x₀-11|))
             (|f-14| (|Cons/f1| |?x₀-11|)))
         (case (|List/tag| |?x₁-12|)
           (1
             (let* ((|f-15| (|Cons/f0| |?x₁-12|))
                    (|f-16| (|Cons/f1| |?x₁-12|)))
                (let* ((|app-18| (gapply2 |d_Eq_0-9| |f-13| |f-15|)))
                   (if |app-18|
                     (|listEq-77| |d_Eq_0-9| |f-14| |f-16|)
                     nil))))
           (t nil))))
    (t nil)))

(defun |fn-78| (|d_Eq_0-21| |?x₀-23| |?x₁-24|)
  (case (|Option/tag| |?x₀-23|)
    (0
      (case (|Option/tag| |?x₁-24|)
        (0
          t)
        (t nil)))
    (1
      (let* ((|f-25| (|Some/f0| |?x₀-23|)))
         (case (|Option/tag| |?x₁-24|)
           (1
             (let* ((|f-26| (|Some/f0| |?x₁-24|)))
                (gapply2 |d_Eq_0-21| |f-25| |f-26|)))
           (t nil))))
    (t nil)))

(defun |listEq-8| (|d_Eq_0-9|)
  (%clos (lambda (|g0| |g1|)
      (|listEq-77| |d_Eq_0-9| |g0| |g1|))
    2))

(defun |i_Eq_1-20| (|d_Eq_0-21|)
  (%clos (lambda (|g2| |g3|)
      (|fn-78| |d_Eq_0-21| |g2| |g3|))
    2))

(defun |i_Eq_2-30| (|d_Eq_0-31|)
  (|listEq-8| |d_Eq_0-31|))

(defparameter |i_Eq_0-2|
  (%clos (function |fn-76|) 2))

(defparameter |main-34|
  (let* ((|app-35| (|i_Eq_2-30| |i_Eq_0-2|))
         (|app-36| (|i_Eq_1-20| |i_Eq_0-2|))
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
         (|p-74| (cons |app-55| |p-73|)))
     (cons |app-45| |p-74|)))
