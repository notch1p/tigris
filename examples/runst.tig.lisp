;; == System F IR ==

let id : ∀α, α → α = Λ α. fun x : α => x

let run : (∀s, s → s) → Int = fun f : ∀s, s → s => f 1

let main : Int = run id@?sk.s
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
(declaim (ftype (function (clos) integer) |run-4|))

(declaim (type integer |main-7|))

; body
(defun |id-2| (|x-3|)
  |x-3|)

(defun |run-4| (|f-5|)
  (gapply1 |f-5| 1))

(defparameter |main-7|
  (|run-4| (%clos (function |id-2|) 1)))

(format t "~S~%" |main-7|)
