;; == System F IR ==

let (::) : ∀α, α → List α → List α = Λ α. Cons@α

let i_Functor_0 : Functor List =
  let rd_Functor_0 : Functor List = i_Functor_0
  in Functor@List
       Λ a b.
         fun f : a → b =>
           fun ?x₀ : List a =>
             match ?x₀ with
             | Nil => Nil@b
             | Cons x xs => Cons@b (f x) (rd_Functor_0[0, fmap]@List f xs)

let main : Int =
  let rd_Functor_0 : Functor List = i_Functor_0
  in let foldr : ∀α β, (α → β → β) → β → List α → β =
       Λ α β.
         rec fun foldr : (α → β → β) → β → List α → β =>
           fun f : α → β → β =>
             fun init : β =>
               fun ?x₀ : List α =>
                 match ?x₀ with
                 | Nil => init
                 | Cons x xs => f x (foldr f init xs)
     in foldr@Int@Int fun ?x₀ : Int => fun ?x₁ : Int => add ?x₀ ?x₁ 0
          (rd_Functor_0[0, fmap]@List fun ?x₀ : Int => add ?x₀ 1
             (Cons@Int 1 (Cons@Int 2 (Cons@Int 3 Nil@Int))))
;; == Runtime ==
(load "runtime.lisp")

;; == Linked Lisp Source ==
(load "ffi.lisp")

;; == Common Lisp ==

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
(declaim (ftype (function (clos |List|) |List|) |fn-37|))

(declaim (ftype (function (clos t |List|) t) |foldr-38|))

(declaim (ftype (function (integer integer) integer) |fn-39|))

(declaim (ftype (function (integer) integer) |fn-40|))

(declaim (type integer |main-14|))

; body
(defun |fn-37| (|f-4| |?x₀-5|)
  (case (|List/tag| |?x₀-5|)
    (0
      (|mk/Nil|))
    (1
      (let* ((|f-7| (|Cons/f0| |?x₀-5|))
             (|f-8| (|Cons/f1| |?x₀-5|)))
         (let* ((|app-9| (gapply1 |f-4| |f-7|))
                (|app-11| (|fn-37| |f-4| |f-8|)))
            (|mk/Cons| |app-9| |app-11|))))
    (t (error "unreachable"))))

(defun |foldr-38| (|f-16| |init-17| |?x₀-18|)
  (case (|List/tag| |?x₀-18|)
    (0
      |init-17|)
    (1
      (let* ((|f-19| (|Cons/f0| |?x₀-18|))
             (|f-20| (|Cons/f1| |?x₀-18|)))
         (let* ((|app-21| (|foldr-38| |f-16| |init-17| |f-20|)))
            (gapply2 |f-16| |f-19| |app-21|))))
    (t (error "unreachable"))))

(defun |fn-39| (|?x₀-24| |?x₁-25|)
  (%int+ |?x₀-24| |?x₁-25|))

(defun |fn-40| (|?x₀-29|)
  (%int+ |?x₀-29| 1))

(defparameter |i_Functor_0-2|
  (%clos (function |fn-37|) 2))

(defparameter |main-14|
  (let* ((|fn-23| (%clos (function |fn-39|) 2))
         (|fn-28| (%clos (function |fn-40|) 1))
         (|con-31| (|mk/Nil|))
         (|con-32| (|mk/Cons| 3 |con-31|))
         (|con-33| (|mk/Cons| 2 |con-32|))
         (|con-34| (|mk/Cons| 1 |con-33|))
         (|app-35| (|fn-37| |fn-28| |con-34|)))
     (|foldr-38| |fn-23| 0 |app-35|)))
