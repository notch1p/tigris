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

; gapply
(defun gapply1 (c a1)
  (if (eql (clos-arity c) 1)
    (funcall (clos-fn c) a1)
    (%apply-slow c (list a1))))

(defun gapply2 (c a1 a2)
  (if (eql (clos-arity c) 2)
    (funcall (clos-fn c) a1 a2)
    (%apply-slow c (list a1 a2))))

; ftype
(declaim (ftype (function (integer) integer) |fn-62|))

(declaim (ftype (function (integer integer) integer) |fn-63|))

(declaim (ftype (function (integer integer) integer) |fn-64|))

(declaim (ftype (function (clos |List|) |List|) |map-2|))

(declaim (ftype (function (clos t |List|) t) |foldl-3|))

(declaim (ftype (function (|List|) t) |hd-4|))

(declaim (ftype (function (|List|) |List|) |tl-5|))

(declaim (type cons |main-6|))

; body
(defun |fn-61| (|k-33| |_-34|)
  |k-33|)

(defun |fn-62| (|?x₀-41|)
  (%int+ 1 |?x₀-41|))

(defun |fn-63| (|?x₀-45| |?x₁-46|)
  (%int+ |?x₀-45| |?x₁-46|))

(defun |fn-64| (|?x₀-52| |?x₁-53|)
  (%int+ |?x₀-52| |?x₁-53|))

(defun |map-2| (|f-7| |?x₀-8|)
  (case (|List/tag| |?x₀-8|)
    (0
      (|mk/Nil|))
    (1
      (let* ((|f-10| (|Cons/f0| |?x₀-8|))
             (|f-11| (|Cons/f1| |?x₀-8|)))
         (let* ((|app-12| (gapply1 |f-7| |f-10|))
                (|app-13| (|map-2| |f-7| |f-11|)))
            (|mk/Cons| |app-12| |app-13|))))
    (t (error "unreachable"))))

(defun |foldl-3| (|f-15| |init-16| |?x₀-17|)
  (case (|List/tag| |?x₀-17|)
    (0
      |init-16|)
    (1
      (let* ((|f-18| (|Cons/f0| |?x₀-17|))
             (|f-19| (|Cons/f1| |?x₀-17|)))
         (let* ((|app-20| (gapply2 |f-15| |init-16| |f-18|)))
            (|foldl-3| |f-15| |app-20| |f-19|))))
    (t (error "unreachable"))))

(defun |hd-4| (|?x₀-22|)
  (labels ((|fail-23| () (error 'match-failure :discr (list |?x₀-22|))))
     (case (|List/tag| |?x₀-22|)
       (1
         (let* ((|f-25| (|Cons/f0| |?x₀-22|))
                (|f-26| (|Cons/f1| |?x₀-22|)))
            |f-25|))
       (t (|fail-23|)))))

(defun |tl-5| (|?x₀-27|)
  (labels ((|fail-28| () (error 'match-failure :discr (list |?x₀-27|))))
     (case (|List/tag| |?x₀-27|)
       (1
         (let* ((|f-30| (|Cons/f0| |?x₀-27|))
                (|f-31| (|Cons/f1| |?x₀-27|)))
            |f-31|))
       (t (|fail-28|)))))

(defparameter |main-6|
  (let* ((|con-35| (|mk/Nil|))
         (|con-36| (|mk/Cons| 4 |con-35|))
         (|con-37| (|mk/Cons| 3 |con-36|))
         (|con-38| (|mk/Cons| 2 |con-37|))
         (|con-39| (|mk/Cons| 1 |con-38|))
         (|fn-40| (%clos (function |fn-62|) 1))
         (|app-43| (|map-2| |fn-40| |con-39|))
         (|fn-44| (%clos (function |fn-63|) 2))
         (|app-48| (|foldl-3| |fn-44| 0 |con-39|))
         (|app-49| (%clos (lambda (|g0|)
               (|fn-61| 10 |g0|))
             1))
         (|app-50| (|map-2| |app-49| |con-39|))
         (|fn-51| (%clos (function |fn-64|) 2))
         (|app-55| (|foldl-3| |fn-51| 0 |app-43|))
         (|app-56| (|hd-4| |app-43|))
         (|p-57| (cons |app-55| |app-56|))
         (|p-58| (cons |app-48| |p-57|))
         (|p-59| (cons |app-50| |p-58|)))
     (cons |app-43| |p-59|)))
