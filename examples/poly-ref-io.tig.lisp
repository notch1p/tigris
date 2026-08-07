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

(defstruct (|Monad| (:conc-name |Monad/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Monad| (:include |Monad| (|tag| 0))
  (:conc-name |Monad/|)
  (:constructor |mk/Monad| (|f0| |f1|))
  (:predicate |Monad?|))
  (|f0| nil)
  (|f1| nil))

; gapply
(defun gapply1 (c a1)
  (if (eql (clos-arity c) 1)
    (funcall (clos-fn c) a1)
    (%apply-slow c (list a1))))

; ftype
(declaim (ftype (function (t clos) t) |fn-55|))

(declaim (ftype (function (|List|) t) |fn-58|))

(declaim (type |Monad| |i_Monad_0-18|))

; body
(defun |fn-55| (|act-20| |f-21|)
  (let* ((|app-22| (|unsafeIO-15| |act-20|))) (gapply1 |f-21| |app-22|)))

(defun |fn-56| (|ref-33|)
  (let* ((|con-34| (|mk/Nil|))
         (|con-35| (|mk/Cons| 1 |con-34|)))
     (|setf-8| |ref-33| |con-35|)))

(defun |fn-58| (|?x₀-45|)
  (labels ((|fail-46| () (error 'match-failure :discr (list |?x₀-45|))))
     (case (|List/tag| |?x₀-45|)
       (0
         (|pureIO-12| t))
       (t (|fail-46|)))))

(defun |fn-57| (|ref-41|)
  (let* ((|app-43| (|deref-5| |ref-41|))
         (|fn-44| (%clos (function |fn-58|) 1)))
     (|fn-55| |app-43| |fn-44|)))

(defun |mkref-2| (|η-3|)
  (quote |η-3|))

(defun |deref-5| (|η-6|)
  (eval |η-6|))

(defun |setf-8| (|η-9| |η-10|)
  (set |η-9| |η-10|))

(defun |pureIO-12| (|η-13|)
  (identity |η-13|))

(defun |unsafeIO-15| (|η-16|)
  (identity |η-16|))

(defun |f-28| (|_-30|)
  (let* ((|fn-32| (%clos (function |fn-56|) 1))) (|fn-55| |ioref-25| |fn-32|)))

(defun |g-29| (|_-38|)
  (let* ((|fn-40| (%clos (function |fn-57|) 1))) (|fn-55| |ioref-25| |fn-40|)))

(defparameter |i_Monad_0-18|
  (let* ((|fn-19| (%clos (function |fn-55|) 2)))
     (|mk/Monad| (%clos (function |pureIO-12|) 1) |fn-19|)))

(defparameter |ioref-25|
  (let* ((|con-26| (|mk/Nil|))) (|mkref-2| |con-26|)))

(defparameter |main-52|
  (let* ((|app-53| (|f-28| nil))) (|g-29| nil)))
