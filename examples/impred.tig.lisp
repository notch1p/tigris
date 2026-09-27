;; == System F IR ==

let (::) : ∀α, α → List α → List α = Λ α. Cons@α

let id : ∀α, α → α = Λ α. fun x : α => x
and head : ∀α, List α → α =
  Λ α.
    fun l : List α =>
      match l with
      | Cons x _ => x
and run : (∀a, a → a) → Int = fun f : ∀a, a → a => f 1
and g : Int → (∀a, a → a) → Int = fun x : Int => fun f : ∀a, a → a => f x
and apply : ∀α β, (α → β) → α → β = Λ α β. fun f : α → β => fun x : α => f x

let consP : (∀a, a → a) → List (∀a, a → a) → List (∀a, a → a) = Cons@(∀a, a → a)

let ex1 : Int =
  let r : (∀a, a → a) → Int = id@((∀a, a → a) → Int) run in r id@?m.1
and ex2 : Int =
  let r : (∀a, a → a) → Int =
    head@((∀a, a → a) → Int)
      (Cons@((∀a, a → a) → Int) run Nil@((∀a, a → a) → Int))
  in r id@?m.1
and ex3 : Int =
  let k : (∀a, a → a) → Int = apply@Int@((∀a, a → a) → Int) g 1 in k id@?m.1
and ex4 : Int × Bool =
  let ids : List (∀a, a → a) =
    consP fun x : ?m.1 => x (consP id@?m.1 Nil@(∀a, a → a))
  and f : ∀a, a → a = Λ a. head@(∀a, a → a) ids
  in ⟨f 1, f true⟩
and main : Int × Int × Int × Int × Bool = ⟨ex1, ⟨ex2, ⟨ex3, ex4⟩⟩⟩
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

; ftype
(declaim (ftype (function (clos |List|) |List|) |Cons-51|))

(declaim (ftype (function (|List|) t) |head-4|))

(declaim (ftype (function (clos) integer) |run-10|))

(declaim (ftype (function (integer clos) integer) |g-13|))

(declaim (ftype (function (clos t) t) |apply-17|))

(declaim (type clos |consP-21|))

(declaim (type integer |ex1-26|))

(declaim (type integer |ex2-29|))

(declaim (type integer |ex3-34|))

(declaim (type cons |ex4-37|))

(declaim (type cons |main-47|))

; body
(defun |Cons-51| (|η-23| |η-24|)
  (|mk/Cons| |η-23| |η-24|))

(defun |fn-52| (|x-39|)
  |x-39|)

(defun |id-2| (|x-3|)
  |x-3|)

(defun |head-4| (|l-5|)
  (labels ((|fail-6| () (error 'match-failure :discr (list |l-5|))))
     (case (|List/tag| |l-5|)
       (1
         (let* ((|f-8| (|Cons/f0| |l-5|))
                (|f-9| (|Cons/f1| |l-5|)))
            |f-8|))
       (t (|fail-6|)))))

(defun |run-10| (|f-11|)
  (gapply1 |f-11| 1))

(defun |g-13| (|x-14| |f-15|)
  (gapply1 |f-15| |x-14|))

(defun |apply-17| (|f-18| |x-19|)
  (gapply1 |f-18| |x-19|))

(defparameter |consP-21|
  (%clos (function |Cons-51|) 2))

(defparameter |ex1-26|
  (let* ((|app-27| (|id-2| (%clos (function |run-10|) 1))))
     (gapply1 |app-27| (%clos (function |id-2|) 1))))

(defparameter |ex2-29|
  (let* ((|con-30| (|mk/Nil|))
         (|con-31| (|mk/Cons| (%clos (function |run-10|) 1) |con-30|))
         (|app-32| (|head-4| |con-31|)))
     (gapply1 |app-32| (%clos (function |id-2|) 1))))

(defparameter |ex3-34|
  (let* ((|app-35| (|apply-17| (%clos (function |g-13|) 2) 1)))
     (gapply1 |app-35| (%clos (function |id-2|) 1))))

(defparameter |ex4-37|
  (let* ((|fn-38| (%clos (function |fn-52|) 1))
         (|con-40| (|mk/Nil|))
         (|app-41| (|Cons-51| (%clos (function |id-2|) 1) |con-40|))
         (|app-42| (|Cons-51| |fn-38| |app-41|))
         (|app-43| (|head-4| |app-42|))
         (|app-44| (gapply1 |app-43| 1))
         (|app-45| (gapply1 |app-43| t)))
     (cons |app-44| |app-45|)))

(defparameter |main-47|
  (let* ((|p-48| (cons |ex3-34| |ex4-37|))
         (|p-49| (cons |ex2-29| |p-48|)))
     (cons |ex1-26| |p-49|)))
