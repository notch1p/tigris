;; == TCNF CC & Optimize'd ==

let fn#18/2 (x#6 : Int, y#7 : Int) : Int → Int → Bool =
  let π#8 : Bool = EQⁱ(#6, #7); ret #8

let i_Eq_0#2/0 : Eq Int = let fn#5 : Int → Int → Bool = 𝐂⟦18⟧; ret #5

let rec sumTo#3/2 (n#10 : Int, acc#11 : Int) : Int → Int → Int =
  let app#13 : Bool = #18(#10, 0);
  case #13 of
    true => ret #11;
    false =>
      let π#14 : Int = SUB(#10, 1);
      let π#15 : Int = ADD(#11, #10); let app#16 : Int = #3(#14, #15); ret #16

let main#4/0 : Int = let app#17 : Int = #3(100, 0); ret #17
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

(declaim (ftype (function (integer integer) integer) |sumTo-3|))

(declaim (type integer |main-4|))

; body
(defun |fn-18| (|x-6| |y-7|)
  (%int= |x-6| |y-7|))

(defun |sumTo-3| (|n-10| |acc-11|)
  (let* ((|app-13| (|fn-18| |n-10| 0)))
     (if |app-13|
       |acc-11|
       (let* ((|π-14| (%int- |n-10| 1))
              (|π-15| (%int+ |acc-11| |n-10|)))
          (|sumTo-3| |π-14| |π-15|)))))

(defparameter |i_Eq_0-2|
  (%clos (function |fn-18|) 2))

(defparameter |main-4|
  (|sumTo-3| 100 0))
