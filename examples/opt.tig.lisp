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

; gapply
(defun gapply1 (c a1)
  (if (eql (clos-arity c) 1)
    (funcall (clos-fn c) a1)
    (%apply-slow c (list a1))))

; ftype
(declaim (ftype (function (integer) integer) |fn-22|))

(declaim (ftype (function (|Option|) t) |get!-2|))

(declaim (ftype (function (clos |Option|) |Option|) |mapOp-7|))

(declaim (type cons |main-14|))

; body
(defun |fn-22| (|?x₀-18|)
  (%int+ 1 |?x₀-18|))

(defun |get!-2| (|?x₀-3|)
  (labels ((|fail-4| () (error 'match-failure :discr (list |?x₀-3|))))
     (case (|Option/tag| |?x₀-3|)
       (1
         (let* ((|f-6| (|Some/f0| |?x₀-3|))) |f-6|))
       (t (|fail-4|)))))

(defun |mapOp-7| (|f-8| |?x₀-9|)
  (case (|Option/tag| |?x₀-9|)
    (0
      (|mk/None|))
    (1
      (let* ((|f-11| (|Some/f0| |?x₀-9|)))
         (let* ((|app-12| (gapply1 |f-8| |f-11|))) (|mk/Some| |app-12|))))
    (t (error "unreachable"))))

(defparameter |main-14|
  (let* ((|con-15| (|mk/Some| 20))
         (|app-16| (|get!-2| |con-15|))
         (|fn-17| (%clos (function |fn-22|) 1))
         (|app-20| (|mapOp-7| |fn-17| |con-15|)))
     (cons |app-16| |app-20|)))
