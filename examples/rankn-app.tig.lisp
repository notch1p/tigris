;; == System F IR ==

let g : Int → (∀a, a → a) → Int = fun x : Int => fun f : ∀a, a → a => f x

let id : ∀α, α → α = Λ α. fun x : α => x
and apply : ∀α β, (α → β) → α → β = Λ α β. fun f : α → β => fun x : α => f x

let prog1 : Int = g 1 id@?sk.0
and prog2 : Int = let k : (∀a, a → a) → Int = g 1 in k id@?sk.0
and prog3 : Int = apply@Int@((?m.10 → ?m.10) → Int) g 1 id@?m.10
and main : Int × Int × Int = ⟨prog1, ⟨prog2, prog3⟩⟩
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

; ftype
(declaim (ftype (function (integer clos) integer) |g-2|))

(declaim (ftype (function (clos t) t) |apply-8|))

(declaim (type integer |prog1-12|))

(declaim (type integer |prog2-14|))

(declaim (type integer |prog3-17|))

(declaim (type cons |main-20|))

; body
(defun |g-2| (|x-3| |f-4|)
  (gapply1 |f-4| |x-3|))

(defun |id-6| (|x-7|)
  |x-7|)

(defun |apply-8| (|f-9| |x-10|)
  (gapply1 |f-9| |x-10|))

(defparameter |prog1-12|
  (|g-2| 1 (%clos (function |id-6|) 1)))

(defparameter |prog2-14|
  (|g-2| 1 (%clos (function |id-6|) 1)))

(defparameter |prog3-17|
  (let* ((|app-18| (|apply-8| (%clos (function |g-2|) 2) 1)))
     (gapply1 |app-18| (%clos (function |id-6|) 1))))

(defparameter |main-20|
  (let* ((|p-21| (cons |prog2-14| |prog3-17|))) (cons |prog1-12| |p-21|)))
