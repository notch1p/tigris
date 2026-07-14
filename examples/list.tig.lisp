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
(declaim (ftype (function (clos |List|) |List|) |map-2|))

(declaim (ftype (function (clos t |List|) t) |foldl-3|))

(declaim (ftype (function (|List|) t) |hd-4|))

(declaim (ftype (function (|List|) |List|) |tl-5|))

(declaim (ftype (function (integer) integer) |fn-55|))

(declaim (ftype (function (integer integer) integer) |fn-56|))

(declaim (ftype (function (integer integer) integer) |fn-57|))

(declaim (type cons |main-6|))

; body
(defun |map-2| (|f-7| |?x₀-8|)
  (case (|List/tag| |?x₀-8|)
    (0
      (let* ((|con-9| (|mk/Nil|))) |con-9|))
    (1
      (let* ((|f-10| (|Cons/f0| |?x₀-8|))
             (|f-11| (|Cons/f1| |?x₀-8|)))
         (let* ((|app-12| (gapply1 |f-7| |f-10|))
                (|app-13| (|map-2| |f-7| |f-11|))
                (|con-14| (|mk/Cons| |app-12| |app-13|)))
            |con-14|)))
    (t (error "unreachable"))))

(defun |foldl-3| (|f-15| |init-16| |?x₀-17|)
  (case (|List/tag| |?x₀-17|)
    (0
      |init-16|)
    (1
      (let* ((|f-18| (|Cons/f0| |?x₀-17|))
             (|f-19| (|Cons/f1| |?x₀-17|)))
         (let* ((|app-20| (gapply2 |f-15| |init-16| |f-18|))
                (|app-21| (|foldl-3| |f-15| |app-20| |f-19|)))
            |app-21|)))
    (t (error "unreachable"))))

(defun |hd-4| (|?x₀-22|)
  (labels ((|fail-23| ()
             (let* ((|fail-24| (error 'match-failure
                        :discr
                        "no matching clause")))
                |fail-24|)))
     (case (|List/tag| |?x₀-22|)
       (1
         (let* ((|f-25| (|Cons/f0| |?x₀-22|))
                (|f-26| (|Cons/f1| |?x₀-22|)))
            |f-25|))
       (t (|fail-23|)))))

(defun |tl-5| (|?x₀-27|)
  (labels ((|fail-28| ()
             (let* ((|fail-29| (error 'match-failure
                        :discr
                        "no matching clause")))
                |fail-29|)))
     (case (|List/tag| |?x₀-27|)
       (1
         (let* ((|f-30| (|Cons/f0| |?x₀-27|))
                (|f-31| (|Cons/f1| |?x₀-27|)))
            |f-31|))
       (t (|fail-28|)))))

(defun |fn-55| (|?x₀-38|)
  (let* ((|π-39| (%int+ 1 |?x₀-38|))) |π-39|))

(defun |fn-56| (|?x₀-42| |?x₁-43|)
  (let* ((|π-44| (%int+ |?x₀-42| |?x₁-43|))) |π-44|))

(defun |fn-57| (|?x₀-47| |?x₁-48|)
  (let* ((|π-49| (%int+ |?x₀-47| |?x₁-48|))) |π-49|))

(defparameter |main-6|
  (let* ((|con-32| (|mk/Nil|))
         (|con-33| (|mk/Cons| 4 |con-32|))
         (|con-34| (|mk/Cons| 3 |con-33|))
         (|con-35| (|mk/Cons| 2 |con-34|))
         (|con-36| (|mk/Cons| 1 |con-35|))
         (|fn-37| (%clos (function |fn-55|) 1))
         (|app-40| (|map-2| |fn-37| |con-36|))
         (|fn-41| (%clos (function |fn-56|) 2))
         (|app-45| (|foldl-3| |fn-41| 0 |con-36|))
         (|fn-46| (%clos (function |fn-57|) 2))
         (|app-50| (|foldl-3| |fn-46| 0 |app-40|))
         (|app-51| (|hd-4| |app-40|))
         (|p-52| (cons |app-50| |app-51|))
         (|p-53| (cons |app-45| |p-52|))
         (|p-54| (cons |app-40| |p-53|)))
     |p-54|))

(format t "~S~%" |main-6|)
