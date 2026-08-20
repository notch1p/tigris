;; == TCNF CC & Optimize'd ==

let fn#18/2 (x#4 : Int, y#5 : Int) : Bool =
  let π#6 : Bool = EQⁱ(#4, #5) in ret #6

let i_Eq_0#2/0 : Eq Int = let fn#3 : Int → Int → Bool = 𝐂⟦18⟧ in ret #3

let rec sumTo#8/2 (n#9 : Int, acc#10 : Int) : Int =
  let app#12 : Bool = #18(#9, 0)
  case #12 of
    true => ret #10;
    false =>
      let π#13 : Int = SUB(#9, 1)
      let π#14 : Int = ADD(#10, #9)
      let app#15 : Int = #8(#13, #14) in ret #15

let main#16/0 : Int = let app#17 : Int = #8(100, 0) in ret #17
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
(declaim (ftype (function (integer integer) boolean) |fn-18|))

(declaim (ftype (function (integer integer) integer) |sumTo-8|))

(declaim (type integer |main-16|))

; body
(defun |fn-18| (|x-4| |y-5|)
  (%int= |x-4| |y-5|))

(defun |sumTo-8| (|n-9| |acc-10|)
  (let* ((|app-12| (|fn-18| |n-9| 0)))
     (if |app-12|
       |acc-10|
       (let* ((|π-13| (%int- |n-9| 1))
              (|π-14| (%int+ |acc-10| |n-9|)))
          (|sumTo-8| |π-13| |π-14|)))))

(defparameter |i_Eq_0-2|
  (%clos (function |fn-18|) 2))

(defparameter |main-16|
  (|sumTo-8| 100 0))
