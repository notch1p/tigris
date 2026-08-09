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
(declaim (ftype (function (t clos) t) |fn-58|))

(declaim (ftype (function (|List|) t) |fn-61|))

(declaim (type |Monad| |i_Monad_0-18|))

; body
(defun |fn-58| (|act-20| |f-21|)
  (let* ((|app-22| (|unsafeIO-15| |act-20|))) (gapply1 |f-21| |app-22|)))

(defun |fn-59| (|ref-35|)
  (let* ((|con-36| (|mk/Nil|))
         (|con-37| (|mk/Cons| 1 |con-36|)))
     (|setf-8| |ref-35| |con-37|)))

(defun |fn-61| (|?x₀-48|)
  (labels ((|fail-49| () (error 'match-failure :discr (list |?x₀-48|))))
     (case (|List/tag| |?x₀-48|)
       (0
         (|pureIO-12| t))
       (t (|fail-49|)))))

(defun |fn-60| (|ref-44|)
  (let* ((|app-46| (|deref-5| |ref-44|))
         (|fn-47| (%clos (function |fn-61|) 1)))
     (|fn-58| |app-46| |fn-47|)))

(defun |mkref-2| (|η-3|)
  (%mkref |η-3|))

(defun |deref-5| (|η-6|)
  (symbol-value |η-6|))

(defun |setf-8| (|η-9| |η-10|)
  (set |η-9| |η-10|))

(defun |pureIO-12| (|η-13|)
  (identity |η-13|))

(defun |unsafeIO-15| (|η-16|)
  (identity |η-16|))

(defun |ioref-25| (|_-26|)
  (let* ((|con-27| (|mk/Nil|))) (|mkref-2| |con-27|)))

(defun |f-29| (|_-31|)
  (let* ((|app-33| (|ioref-25| nil))
         (|fn-34| (%clos (function |fn-59|) 1)))
     (|fn-58| |app-33| |fn-34|)))

(defun |g-30| (|_-40|)
  (let* ((|app-42| (|ioref-25| nil))
         (|fn-43| (%clos (function |fn-60|) 1)))
     (|fn-58| |app-42| |fn-43|)))

(defparameter |i_Monad_0-18|
  (let* ((|fn-19| (%clos (function |fn-58|) 2)))
     (|mk/Monad| (%clos (function |pureIO-12|) 1) |fn-19|)))

(defparameter |main-55|
  (let* ((|app-56| (|f-29| nil))) (|g-30| nil)))
