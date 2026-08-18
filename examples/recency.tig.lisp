;; == System F IR ==

let i_C_0 : C Int = C@Int fun x : Int => x

let i_C_1 : C Bool = C@Bool fun _ : Bool => 5

let i_D_0 : D Int = D@Int fun x : Int => 100

let i_C_2 : ∀a [D a], C a =
  Λ a. fun d_D_0 : D a => C@a fun x : a => add (d_D_0[0, d]@a x) 1

let main : Int × Int =
  let rd_D_0 : D Int = i_D_0
  and rd_C_1 : C Int = Λ α. i_C_2@Int rd_D_0
  and rd_C_2 : C Bool = i_C_1
  in ⟨rd_C_1[0, c]@Int 1, rd_C_2[0, c]@Bool true⟩
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
(declaim (ftype (function (integer) integer) |fn-29|))

(declaim (ftype (function (boolean) integer) |fn-30|))

(declaim (ftype (function (integer) integer) |fn-31|))

(declaim (ftype (function (t t) integer) |fn-32|))

(declaim (type cons |main-22|))

; body
(defun |fn-29| (|x-4|)
  |x-4|)

(defun |fn-30| (|_-8|)
  5)

(defun |fn-31| (|x-12|)
  100)

(defun |fn-32| (|d_D_0-15| |x-17|)
  (let* ((|app-19| (gapply1 |d_D_0-15| |x-17|))) (%int+ |app-19| 1)))

(defun |i_C_2-14| (|d_D_0-15|)
  (%clos (lambda (|g0|)
      (|fn-32| |d_D_0-15| |g0|))
    1))

(defparameter |i_C_0-2|
  (%clos (function |fn-29|) 1))

(defparameter |i_C_1-6|
  (%clos (function |fn-30|) 1))

(defparameter |i_D_0-10|
  (%clos (function |fn-31|) 1))

(defparameter |main-22|
  (let* ((|app-23| (|i_C_2-14| |i_D_0-10|))
         (|app-25| (gapply1 |app-23| 1))
         (|app-27| (|fn-30| t)))
     (cons |app-25| |app-27|)))
