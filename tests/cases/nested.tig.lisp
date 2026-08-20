;; == System F IR ==

let apply2 : ((∀a, a → a) → Int) → Int =
  fun h : (∀a, a → a) → Int => h fun x : ?sk.0 => x

let main : Int = apply2 fun g : ∀a, a → a => g 1
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
(declaim (ftype (function (clos) integer) |fn-13|))

(declaim (ftype (function (clos) integer) |apply2-2|))

(declaim (type integer |main-7|))

; body
(defun |fn-12| (|x-5|)
  |x-5|)

(defun |fn-13| (|g-9|)
  (gapply1 |g-9| 1))

(defun |apply2-2| (|h-3|)
  (let* ((|fn-4| (%clos (function |fn-12|) 1))) (gapply1 |h-3| |fn-4|)))

(defparameter |main-7|
  (let* ((|fn-8| (%clos (function |fn-13|) 1))) (|apply2-2| |fn-8|)))
