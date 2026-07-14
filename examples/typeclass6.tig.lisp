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
(declaim (ftype (function (t) |Option|) |optPure-2|))

(declaim (ftype (function (|Option| clos) |Option|) |optBind-3|))

(declaim (type |Monad| |i_Monad_0-4|))

(declaim (ftype (function (integer integer integer) |Option|) |fn-37|))

(declaim (ftype (function (integer integer) |Option|) |fn-36|))

(declaim (ftype (function (integer) |Option|) |fn-35|))

(declaim (type |Option| |main-5|))

; body
(defun |optPure-2| (|x-6|)
  (let* ((|con-7| (|mk/Some| |x-6|))) |con-7|))

(defun |optBind-3| (|x-8| |f-9|)
  (case (|Option/tag| |x-8|)
    (0
      (let* ((|con-10| (|mk/None|))) |con-10|))
    (1
      (let* ((|f-11| (|Some/f0| |x-8|)))
         (let* ((|app-12| (gapply1 |f-9| |f-11|))) |app-12|)))
    (t (error "unreachable"))))

(defun |fn-37| (|x-18| |y-22| |z-27|)
  (let* ((|π-29| (%int+ |x-18| |y-22|))
         (|π-30| (%int+ |π-29| |z-27|))
         (|app-31| (|optPure-2| |π-30|)))
     |app-31|))

(defun |fn-36| (|x-18| |y-22|)
  (let* ((|app-25| (|optPure-2| 30))
         (|fn-26| (%clos (lambda (|g0|)
               (|fn-37| |x-18| |y-22| |g0|))
             1))
         (|app-32| (|optBind-3| |app-25| |fn-26|)))
     |app-32|))

(defun |fn-35| (|x-18|)
  (let* ((|con-20| (|mk/None|))
         (|fn-21| (%clos (lambda (|g1|)
               (|fn-36| |x-18| |g1|))
             1))
         (|app-33| (|optBind-3| |con-20| |fn-21|)))
     |app-33|))

(defparameter |i_Monad_0-4|
  (let* ((|con-13| (|mk/Monad| (%clos (function |optPure-2|) 1)
             (%clos (function |optBind-3|) 2))))
     |con-13|))

(defparameter |main-5|
  (let* ((|app-16| (|optPure-2| 20))
         (|fn-17| (%clos (function |fn-35|) 1))
         (|app-34| (|optBind-3| |app-16| |fn-17|)))
     |app-34|))

(format t "~S~%" |main-5|)
