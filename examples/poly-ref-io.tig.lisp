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

(declaim (type |Monad| |i_Monad_0-7|))

; body
(defun |fn-55| (|act-24| |f-25|)
  (let* ((|app-26| (|unsafeIO-6| |act-24|))) (gapply1 |f-25| |app-26|)))

(defun |fn-56| (|ref-34|)
  (let* ((|con-35| (|mk/Nil|))
         (|con-36| (|mk/Cons| 1 |con-35|)))
     (|setf-4| |ref-34| |con-36|)))

(defun |fn-58| (|?x₀-46|)
  (labels ((|fail-47| () (error 'match-failure :discr (list |?x₀-46|))))
     (case (|List/tag| |?x₀-46|)
       (0
         (|pureIO-5| t))
       (t (|fail-47|)))))

(defun |fn-57| (|ref-42|)
  (let* ((|app-44| (|deref-3| |ref-42|))
         (|fn-45| (%clos (function |fn-58|) 1)))
     (|fn-55| |app-44| |fn-45|)))

(defun |mkref-2| (|η-12|)
  (quote |η-12|))

(defun |deref-3| (|η-14|)
  (eval |η-14|))

(defun |setf-4| (|η-16| |η-17|)
  (set |η-16| |η-17|))

(defun |pureIO-5| (|η-19|)
  (identity |η-19|))

(defun |unsafeIO-6| (|η-21|)
  (identity |η-21|))

(defun |f-9| (|_-31|)
  (let* ((|fn-33| (%clos (function |fn-56|) 1))) (|fn-55| |ioref-8| |fn-33|)))

(defun |g-10| (|_-39|)
  (let* ((|fn-41| (%clos (function |fn-57|) 1))) (|fn-55| |ioref-8| |fn-41|)))

(defparameter |i_Monad_0-7|
  (let* ((|fn-23| (%clos (function |fn-55|) 2)))
     (|mk/Monad| (%clos (function |pureIO-5|) 1) |fn-23|)))

(defparameter |ioref-8|
  (let* ((|con-29| (|mk/Nil|))) (|mkref-2| |con-29|)))

(defparameter |main-11|
  (let* ((|app-53| (|f-9| nil))) (|g-10| nil)))

(format t "~S~%" |main-11|)
