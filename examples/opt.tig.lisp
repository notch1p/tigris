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

(declaim (ftype (function (clos |Option|) |Option|) |mapOp-3|))

(declaim (type cons |main-4|))

; body
(defun |fn-22| (|?x₀-18|)
  (let* ((|π-19| (%int+ 1 |?x₀-18|))) |π-19|))

(defun |get!-2| (|?x₀-5|)
  (labels ((|fail-6| ()
             (let* ((|fail-7| (error 'match-failure :discr (list |?x₀-5|))))
                |fail-7|)))
     (case (|Option/tag| |?x₀-5|)
       (1
         (let* ((|f-8| (|Some/f0| |?x₀-5|))) |f-8|))
       (t (|fail-6|)))))

(defun |mapOp-3| (|f-9| |?x₀-10|)
  (case (|Option/tag| |?x₀-10|)
    (0
      (let* ((|con-11| (|mk/None|))) |con-11|))
    (1
      (let* ((|f-12| (|Some/f0| |?x₀-10|)))
         (let* ((|app-13| (gapply1 |f-9| |f-12|))
                (|con-14| (|mk/Some| |app-13|)))
            |con-14|)))
    (t (error "unreachable"))))

(defparameter |main-4|
  (let* ((|con-15| (|mk/Some| 20))
         (|app-16| (|get!-2| |con-15|))
         (|fn-17| (%clos (function |fn-22|) 1))
         (|app-20| (|mapOp-3| |fn-17| |con-15|))
         (|p-21| (cons |app-16| |app-20|)))
     |p-21|))
