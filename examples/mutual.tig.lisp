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
(defstruct (|Tree| (:conc-name |Tree/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Empty| (:include |Tree| (|tag| 0))
  (:conc-name |Empty/|)
  (:constructor |mk/Empty| ())
  (:predicate |Empty?|)))

(defstruct (|c/Node| (:include |Tree| (|tag| 1))
  (:conc-name |Node/|)
  (:constructor |mk/Node| (|f0| |f1|))
  (:predicate |Node?|))
  (|f0| nil)
  (|f1| nil))

(defstruct (|Forest| (:conc-name |Forest/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Nil| (:include |Forest| (|tag| 0))
  (:conc-name |Nil/|)
  (:constructor |mk/Nil| ())
  (:predicate |Nil?|)))

(defstruct (|c/Cons| (:include |Forest| (|tag| 1))
  (:conc-name |Cons/|)
  (:constructor |mk/Cons| (|f0| |f1|))
  (:predicate |Cons?|))
  (|f0| nil)
  (|f1| nil))

; ftype
(declaim (ftype (function (|Forest|) integer) |countForest-2|))

(declaim (ftype (function (|Tree|) integer) |countTree-3|))

(declaim (type integer |main-4|))

; body
(defun |countForest-2| (|?x₀-5|)
  (case (|Forest/tag| |?x₀-5|)
    (0
      0)
    (1
      (let* ((|f-6| (|Cons/f0| |?x₀-5|))
             (|f-7| (|Cons/f1| |?x₀-5|)))
         (let* ((|app-8| (|countTree-3| |f-6|))
                (|app-9| (|countForest-2| |f-7|)))
            (%int+ |app-8| |app-9|))))
    (t (error "unreachable"))))

(defun |countTree-3| (|?x₀-11|)
  (case (|Tree/tag| |?x₀-11|)
    (0
      0)
    (1
      (let* ((|f-12| (|Node/f0| |?x₀-11|))
             (|f-13| (|Node/f1| |?x₀-11|)))
         (let* ((|app-14| (|countForest-2| |f-13|))) (%int+ 1 |app-14|))))
    (t (error "unreachable"))))

(defparameter |main-4|
  (let* ((|con-16| (|mk/Nil|))
         (|con-17| (|mk/Node| 5 |con-16|))
         (|con-18| (|mk/Nil|))
         (|con-19| (|mk/Cons| |con-17| |con-18|))
         (|con-20| (|mk/Node| 2 |con-19|))
         (|con-21| (|mk/Nil|))
         (|con-22| (|mk/Node| 4 |con-21|))
         (|con-23| (|mk/Nil|))
         (|con-24| (|mk/Cons| |con-22| |con-23|))
         (|con-25| (|mk/Node| 3 |con-24|))
         (|con-26| (|mk/Empty|))
         (|con-27| (|mk/Nil|))
         (|con-28| (|mk/Cons| |con-26| |con-27|))
         (|con-29| (|mk/Cons| |con-25| |con-28|))
         (|con-30| (|mk/Cons| |con-20| |con-29|))
         (|con-31| (|mk/Node| 1 |con-30|)))
     (|countTree-3| |con-31|)))
