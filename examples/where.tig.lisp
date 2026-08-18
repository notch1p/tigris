;; == System F IR ==

let (`on`) : Unit = ()

let (^) : Unit = ()

let rec ^ : Boxed Int → Boxed Int → Int =
  fun ?x₀ : Boxed Int =>
    fun ?x₁ : Boxed Int =>
      match ?x₀,
      ?x₁ with
      | B x, B y => add x y
and `on` : ∀α β γ, (β → β → γ) → (α → β) → α → α → γ =
  Λ α β γ.
    rec fun `on` : (β → β → γ) → (α → β) → α → α → γ =>
      fun f : β → β → γ =>
        fun g : α → β => fun x : α => fun y : α => f (g x) (g y)
and boxedAdd : Int → Int → Int = `on`@Int@(Boxed Int)@Int ^ B@Int
and main : Int = let x : Int = 20 and y : Int = 30 in boxedAdd 20 30
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
(declaim (ftype (function (integer) t) |B-25|))

(declaim (ftype (function (t t) integer) |^-2|))

(declaim (ftype (function (clos clos t t) t) |`on`-3|))

(declaim (type clos |boxedAdd-16|))

(declaim (type integer |main-21|))

; body
(defun |B-25| (|η-18|)
  |η-18|)

(defun |^-2| (|?x₀-4| |?x₁-5|)
  (%int+ |?x₀-4| |?x₁-5|))

(defun |`on`-3| (|f-9| |g-10| |x-11| |y-12|)
  (let* ((|app-13| (gapply1 |g-10| |x-11|))
         (|app-14| (gapply1 |g-10| |y-12|)))
     (gapply2 |f-9| |app-13| |app-14|)))

(defparameter |boxedAdd-16|
  (let* ((|B-17| (%clos (function |B-25|) 1)))
     (%clos (lambda (|g0| |g1|)
         (|`on`-3| (%clos (function |^-2|) 2) |B-17| |g0| |g1|))
       2)))

(defparameter |main-21|
  (|`on`-3| (%clos (function |^-2|) 2) (%clos (function |B-25|) 1) 20 30))
