;; == TCNF CC & Optimize'd ==

let id#2/1 (x#3 : α) : α → α = ret #3

let f#4/1 (x#5 : a → a) : (∀a, a → a) → Int × Bool =
  let app#6 : Int = #5(1);
  let app#7 : Bool = #5(true); let p#8 : Int × Bool = ⟨#6, #7⟩; ret #8

let main#9/0 : Int × Bool = let app#10 : Int × Bool = #4(#2); ret #10
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
(declaim (ftype (function (clos) cons) |f-4|))

(declaim (type cons |main-9|))

; body
(defun |id-2| (|x-3|)
  |x-3|)

(defun |f-4| (|x-5|)
  (let* ((|app-6| (gapply1 |x-5| 1))
         (|app-7| (gapply1 |x-5| t)))
     (cons |app-6| |app-7|)))

(defparameter |main-9|
  (|f-4| (%clos (function |id-2|) 1)))
