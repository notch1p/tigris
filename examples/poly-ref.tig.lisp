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

; ftype
(declaim (type integer |main-6|))

; body
(defun |mkref-2| (|η-7|)
  (quote |η-7|))

(defun |deref-3| (|η-9|)
  (eval |η-9|))

(defun |setf-4| (|η-11| |η-12|)
  (set |η-11| |η-12|))

(defparameter |ref-5|
  (let* ((|con-14| (|mk/Nil|))) (|mkref-2| |con-14|)))

(defparameter |main-6|
  (let* ((|con-16| (|mk/Nil|))
         (|con-17| (|mk/Cons| t |con-16|))
         (|app-18| (|setf-4| |ref-5| |con-17|))
         (|app-19| (|deref-3| |ref-5|)))
     (labels ((|fail-20| () (error 'match-failure :discr (list |app-19|))))
        (case (|List/tag| |app-19|)
          (1
            (let* ((|f-22| (|Cons/f0| |app-19|))
                   (|f-23| (|Cons/f1| |app-19|)))
               (%int+ |f-22| 1)))
          (t (|fail-20|))))))

(format t "~S~%" |main-6|)
