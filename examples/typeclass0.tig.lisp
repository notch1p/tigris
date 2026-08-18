;; == System F IR ==

let i_Functor_0 : Functor (Λa. a) = Functor@(Λa. a) Λ a₁ b. fun f : a₁ → b => f

let main : Int =
  let rd_Functor_0 : Functor (Λα. Int) = i_Functor_0
  in rd_Functor_0[0, fmap]@(Λα. Int) fun ?x₀ : Int => add 1 ?x₀ 2
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
(declaim (ftype (function (clos) clos) |fn-12|))

(declaim (ftype (function (integer) integer) |fn-13|))

(declaim (type integer |main-6|))

; body
(defun |fn-12| (|f-4|)
  |f-4|)

(defun |fn-13| (|?x₀-9|)
  (%int+ 1 |?x₀-9|))

(defparameter |i_Functor_0-2|
  (%clos (function |fn-12|) 1))

(defparameter |main-6|
  (let* ((|fn-8| (%clos (function |fn-13|) 1)))
     (gapply2 |i_Functor_0-2| |fn-8| 2)))
