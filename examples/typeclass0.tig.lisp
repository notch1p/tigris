;; == System F IR ==

let i_Functor_0 : Functor (Λa. a) = Functor@(Λa. a) Λ a₁ b. fun f : a₁ → b => f

let main : Int × Int =
  let rd_Functor_0 : Functor (Λa. a) = i_Functor_0
  in let x : Int = rd_Functor_0[0, fmap]@(Λa. a) fun ?x₀ : Int => add 1 ?x₀ 2
     and y : Int = rd_Functor_0[0, fmap]@(Λa. a) fun _ : Bool => 1 true
     in ⟨x, y⟩
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
(defun gapply2 (c a1 a2)
  (if (eql (clos-arity c) 2)
    (funcall (clos-fn c) a1 a2)
    (%apply-slow c (list a1 a2))))

; ftype
(declaim (ftype (function (clos) clos) |fn-17|))

(declaim (ftype (function (integer) integer) |fn-18|))

(declaim (ftype (function (boolean) integer) |fn-19|))

(declaim (type cons |main-6|))

; body
(defun |fn-17| (|f-4|)
  |f-4|)

(defun |fn-18| (|?x₀-9|)
  (%int+ 1 |?x₀-9|))

(defun |fn-19| (|_-14|)
  1)

(defparameter |i_Functor_0-2|
  (%clos (function |fn-17|) 1))

(defparameter |main-6|
  (let* ((|fn-8| (%clos (function |fn-18|) 1))
         (|app-11| (gapply2 |i_Functor_0-2| |fn-8| 2))
         (|fn-13| (%clos (function |fn-19|) 1))
         (|app-15| (gapply2 |i_Functor_0-2| |fn-13| t)))
     (cons |app-11| |app-15|)))
