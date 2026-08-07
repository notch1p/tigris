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
(declaim (ftype (function (t) |Option|) |Some-44|))

(declaim (ftype (function (|Option| clos) |Option|) |fn-45|))

(declaim (ftype (function (integer integer integer) |Option|) |fn-48|))

(declaim (ftype (function (integer integer) |Option|) |fn-47|))

(declaim (ftype (function (integer) |Option|) |fn-46|))

(declaim (ftype (function (t) |Option|) |optPure-2|))

(declaim (ftype (function (|Option| clos) |Option|) |optBind-3|))

(declaim (type |Monad| |i_Monad_0-4|))

(declaim (type |Option| |main-5|))

; body
(defun |Some-44| (|η-14|)
  (|mk/Some| |η-14|))

(defun |fn-45| (|?x₀-17| |?x₁-18|)
  (case (|Option/tag| |?x₀-17|)
    (0
      (|mk/None|))
    (1
      (let* ((|f-20| (|Some/f0| |?x₀-17|))) (gapply1 |?x₁-18| |f-20|)))
    (t (error "unreachable"))))

(defun |fn-48| (|x-27| |y-31| |z-36|)
  (let* ((|π-38| (%int+ |x-27| |y-31|))
         (|π-39| (%int+ |π-38| |z-36|)))
     (|Some-44| |π-39|)))

(defun |fn-47| (|x-27| |y-31|)
  (let* ((|app-34| (|Some-44| 30))
         (|fn-35| (%clos (lambda (|g0|)
               (|fn-48| |x-27| |y-31| |g0|))
             1)))
     (|fn-45| |app-34| |fn-35|)))

(defun |fn-46| (|x-27|)
  (let* ((|con-29| (|mk/None|))
         (|fn-30| (%clos (lambda (|g1|)
               (|fn-47| |x-27| |g1|))
             1)))
     (|fn-45| |con-29| |fn-30|)))

(defun |optPure-2| (|x-6|)
  (|mk/Some| |x-6|))

(defun |optBind-3| (|x-8| |f-9|)
  (case (|Option/tag| |x-8|)
    (0
      (|mk/None|))
    (1
      (let* ((|f-11| (|Some/f0| |x-8|))) (gapply1 |f-9| |f-11|)))
    (t (error "unreachable"))))

(defparameter |i_Monad_0-4|
  (let* ((|Some-13| (%clos (function |Some-44|) 1))
         (|fn-16| (%clos (function |fn-45|) 2)))
     (|mk/Monad| |Some-13| |fn-16|)))

(defparameter |main-5|
  (let* ((|app-25| (|Some-44| 20))
         (|fn-26| (%clos (function |fn-46|) 1)))
     (|fn-45| |app-25| |fn-26|)))
