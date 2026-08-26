;; == System F IR ==

let id : ∀α, α → α = Λ α. fun x : α => x

let head : ∀α, List (α → α) → α → α =
  Λ α.
    fun l : List (α → α) =>
      match l with
      | Cons x _ => x
      | Nil => id@α

let ids : ∀α, List (α → α) = Λ α. Cons@(α → α) id@α Nil@(α → α)

let app : ∀α β, (α → β) → α → β = Λ α β. fun f : α → β => fun x : α => f x

let revapp : ∀α β, α → (α → β) → β = Λ α β. fun x : α => fun f : α → β => f x

let main : Int = revapp@(List (Int → Int))@(Int → Int) ids@Int head@Int 1
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
(declaim (ftype (function (|List|) clos) |head-4|))

(declaim (type |List| |ids-8|))

(declaim (ftype (function (clos t) t) |app-11|))

(declaim (ftype (function (t clos) t) |revapp-15|))

(declaim (type integer |main-19|))

; body
(defun |id-2| (|x-3|)
  |x-3|)

(defun |head-4| (|l-5|)
  (case (|List/tag| |l-5|)
    (0
      (%clos (function |id-2|) 1))
    (1
      (let* ((|f-6| (|Cons/f0| |l-5|))
             (|f-7| (|Cons/f1| |l-5|)))
         |f-6|))
    (t (error "unreachable"))))

(defun |app-11| (|f-12| |x-13|)
  (gapply1 |f-12| |x-13|))

(defun |revapp-15| (|x-16| |f-17|)
  (gapply1 |f-17| |x-16|))

(defparameter |ids-8|
  (let* ((|con-9| (|mk/Nil|))) (|mk/Cons| (%clos (function |id-2|) 1) |con-9|)))

(defparameter |main-19|
  (let* ((|app-20| (|revapp-15| |ids-8| (%clos (function |head-4|) 1))))
     (gapply1 |app-20| 1)))
