;; == TCNF CC & Optimize'd ==

let add#2/2 (x#3 : Int, y#4 : Int) : Int → Int → Int =
  let π#5 : Int = ADD(#3, #4); ret #5

let inc#6/0 : Int → Int = let app#7 : Int → Int = #2ᵖ(1); ret #7

let applyTwice#8/2 (f#9 : α → α, x#10 : α) : (α → α) → α → α =
  let app#11 : α = #9(#10); let app#12 : α = #9(#11); ret #12

let main#13/0 : Int × Int × Int =
  let app#15 : Int → Int = #2(1, 41);
  let app#16 : Int = #2(10, 5);
  let app#17 : Int = #8(#6, 0);
  let p#18 : Int × Int = ⟨#16, #17⟩;
  let p#19 : Int × Int × Int = ⟨#15, #18⟩; ret #19
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
(declaim (ftype (function (integer integer) integer) |add-2|))

(declaim (type clos |inc-6|))

(declaim (ftype (function (clos t) t) |applyTwice-8|))

(declaim (type cons |main-13|))

; body
(defun |add-2| (|x-3| |y-4|)
  (%int+ |x-3| |y-4|))

(defun |applyTwice-8| (|f-9| |x-10|)
  (let* ((|app-11| (gapply1 |f-9| |x-10|))) (gapply1 |f-9| |app-11|)))

(defparameter |inc-6|
  (%clos (lambda (|g0|)
      (|add-2| 1 |g0|))
    1))

(defparameter |main-13|
  (let* ((|app-15| (|add-2| 1 41))
         (|app-16| (|add-2| 10 5))
         (|app-17| (|applyTwice-8| |inc-6| 0))
         (|p-18| (cons |app-16| |app-17|)))
     (cons |app-15| |p-18|)))
