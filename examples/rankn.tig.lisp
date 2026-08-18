;; == System F IR ==

let id : ∀α, α → α = Λ α. fun x : α => x

let f : (∀a, a → a) → Int × Bool = fun x : ∀a, a → a => ⟨x 1, x true⟩

let main : Int × Bool = f id@?sk.1
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
(declaim (ftype (function (clos) cons) |f-4|))

(declaim (type cons |main-9|))

; body
(defun |id-2| (|x-3|)
  |x-3|)

(defun |f-4| (|x-5|)
  (let* ((|app-6| (gapply1 |x-5| 1))
         (|app-7| (gapply1 |x-5| t)))
     (cons |app-6| |app-7|)))

(defparameter |main-9|
  (|f-4| (%clos (function |id-2|) 1)))
