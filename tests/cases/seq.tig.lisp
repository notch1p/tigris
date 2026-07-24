;; == TCNF CC & Optimize'd ==

let dbl#7/1 (x#4 : Int) : Int → Int = let π#5 : Int = ADD(#4, #4); ret #5

let main#2/0 : Int = let app#6 : Int = #7(3); ret #6
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


; ftype
(declaim (ftype (function (integer) integer) |dbl-7|))

(declaim (type integer |main-2|))

; body
(defun |dbl-7| (|x-4|)
  (let* ((|π-5| (%int+ |x-4| |x-4|))) |π-5|))

(defparameter |main-2|
  (let* ((|app-6| (|dbl-7| 3))) |app-6|))
