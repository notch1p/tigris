;; == System F IR ==

let i_C_0 : C (Λa. a) = C@(Λa. a) Λ a₁. fun x : a₁ => x

let f : ∀α β [C α], β → α β =
  Λ α β. fun d_C_0 : C α => fun x : β => d_C_0[0, c]@α x
and g : Int → Int =
  let rd_C_0 : C (Λa. a) = i_C_0 in fun y : Int => rd_C_0[0, c]@(Λa. a) y

let i_C_1 : C Box = C@Box Λ a. fun x : a => Mk@a x x

let main' : ∀α [C α], α (Box Bool) =
  Λ α. fun d_C_0 : C α => f@α@(Box Bool) d_C_0 (Mk@Bool true false)

let main : Box (Box Bool) = let rd_C_0 : C Box = i_C_1 in main'@Box rd_C_0
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
(defstruct (|Box| (:conc-name |Box/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Mk| (:include |Box| (|tag| 0))
  (:conc-name |Mk/|)
  (:constructor |mk/Mk| (|f0| |f1|))
  (:predicate |Mk?|))
  (|f0| nil)
  (|f1| nil))

; gapply
(defun gapply1 (c a1)
  (if (eql (clos-arity c) 1)
    (funcall (clos-fn c) a1)
    (%apply-slow c (list a1))))

; ftype
(declaim (ftype (function (integer) integer) |fn-28|))

(declaim (ftype (function (t) |Box|) |fn-29|))

(declaim (type clos |g-11|))

(declaim (type |Box| |main-25|))

; body
(defun |fn-27| (|x-4|)
  |x-4|)

(defun |fn-28| (|y-13|)
  (|fn-27| |y-13|))

(defun |fn-29| (|x-18|)
  (|mk/Mk| |x-18| |x-18|))

(defun |f-6| (|d_C_0-7| |x-8|)
  (gapply1 |d_C_0-7| |x-8|))

(defun |main'-21| (|d_C_0-22|)
  (let* ((|con-23| (|mk/Mk| t nil))) (|f-6| |d_C_0-22| |con-23|)))

(defparameter |i_C_0-2|
  (%clos (function |fn-27|) 1))

(defparameter |g-11|
  (%clos (function |fn-28|) 1))

(defparameter |i_C_1-16|
  (%clos (function |fn-29|) 1))

(defparameter |main-25|
  (|main'-21| |i_C_1-16|))
