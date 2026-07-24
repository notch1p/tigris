;; == TCNF CC & Optimize'd ==

let add#2/2 (x#6 : Int, y#7 : Int) : Int → Int → Int =
  let π#8 : Int = ADD(#6, #7); ret #8

let inc#3/0 : Int → Int = let app#9 : Int → Int = #2ᵖ(1); ret #9

let applyTwice#4/2 (f#10 : α → α, x#11 : α) : (α → α) → α → α =
  let app#12 : α = #10(#11); let app#13 : α = #10(#12); ret #13

let main#5/0 : Int × Int × Int =
  let app#15 : Int → Int = #2(1, 41);
  let app#16 : Int = #2(10, 5);
  let app#17 : Int = #4(#3, 0);
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

(declaim (type clos |inc-3|))

(declaim (ftype (function (clos t) t) |applyTwice-4|))

(declaim (type cons |main-5|))

; body
(defun |add-2| (|x-6| |y-7|)
  (let* ((|π-8| (%int+ |x-6| |y-7|))) |π-8|))

(defun |applyTwice-4| (|f-10| |x-11|)
  (let* ((|app-12| (gapply1 |f-10| |x-11|))
         (|app-13| (gapply1 |f-10| |app-12|)))
     |app-13|))

(defparameter |inc-3|
  (let* ((|app-9| (%clos (lambda (|g0|)
               (|add-2| 1 |g0|))
             1)))
     |app-9|))

(defparameter |main-5|
  (let* ((|app-15| (|add-2| 1 41))
         (|app-16| (|add-2| 10 5))
         (|app-17| (|applyTwice-4| |inc-3| 0))
         (|p-18| (cons |app-16| |app-17|))
         (|p-19| (cons |app-15| |p-18|)))
     |p-19|))
