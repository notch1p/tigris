;; == System F IR ==

let i_Functor_0 : Functor (Λa. Maybe a) =
  Functor@Maybe
    Λ a₁ b.
      fun f : a₁ → b =>
        fun ?x₀ : Maybe a₁ =>
          match ?x₀ with
          | Some x => Some@b (f x)
          | None => None@b

let main : Maybe Int =
  let rd_Functor_0 : Functor Maybe = i_Functor_0
  in rd_Functor_0[0, fmap]@Maybe fun ?x₀ : Int => add 1 ?x₀ (Some@Int 2)
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
(defstruct (|Maybe| (:conc-name |Maybe/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Some| (:include |Maybe| (|tag| 0))
  (:conc-name |Some/|)
  (:constructor |mk/Some| (|f0|))
  (:predicate |Some?|))
  (|f0| nil))

(defstruct (|c/None| (:include |Maybe| (|tag| 1))
  (:conc-name |None/|)
  (:constructor |mk/None| ())
  (:predicate |None?|)))

; gapply
(defun gapply1 (c a1)
  (if (eql (clos-arity c) 1)
    (funcall (clos-fn c) a1)
    (%apply-slow c (list a1))))

; ftype
(declaim (ftype (function (clos |Maybe|) |Maybe|) |fn-18|))

(declaim (ftype (function (integer) integer) |fn-19|))

(declaim (type |Maybe| |main-11|))

; body
(defun |fn-18| (|f-4| |?x₀-5|)
  (case (|Maybe/tag| |?x₀-5|)
    (1
      (|mk/None|))
    (0
      (let* ((|f-7| (|Some/f0| |?x₀-5|)))
         (let* ((|app-8| (gapply1 |f-4| |f-7|))) (|mk/Some| |app-8|))))
    (t (error "unreachable"))))

(defun |fn-19| (|?x₀-14|)
  (%int+ 1 |?x₀-14|))

(defparameter |i_Functor_0-2|
  (%clos (function |fn-18|) 2))

(defparameter |main-11|
  (let* ((|fn-13| (%clos (function |fn-19|) 1))
         (|con-16| (|mk/Some| 2)))
     (|fn-18| |fn-13| |con-16|)))
