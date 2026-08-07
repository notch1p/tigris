;; == TCNF CC & Optimize'd ==

let rec eval#2/1 (?x₀#3 : Expr Int) : Expr Int → Int =
  case #3 of
    Add⟦f#4 : Expr Int, f#5 : Expr Int⟧ =>
      let app#6 : Int = #2(#4);
      let app#7 : Int = #2(#5); let π#8 : Int = ADD(#6, #7); ret #8;
    Mul⟦f#9 : Expr Int, f#10 : Expr Int⟧ =>
      let app#11 : Int = #2(#9);
      let app#12 : Int = #2(#10); let π#13 : Int = MUL(#11, #12); ret #13;
    Atom⟦f#14 : Int⟧ => ret #14;
    _ => (⊥ : Int)

let main#15/0 : Int =
  let con#16 : Expr Int = Atom⟦20⟧;
  let con#17 : Expr Int = Atom⟦10⟧;
  let con#18 : Expr Int = Atom⟦3⟧;
  let con#19 : Expr Int = Add⟦#17, #18⟧;
  let con#20 : Expr Int = Mul⟦#16, #19⟧; let app#21 : Int = #2(#20); ret #21
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
(defstruct (|Expr| (:conc-name |Expr/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Atom| (:include |Expr| (|tag| 0))
  (:conc-name |Atom/|)
  (:constructor |mk/Atom| (|f0|))
  (:predicate |Atom?|))
  (|f0| nil))

(defstruct (|c/Add| (:include |Expr| (|tag| 1))
  (:conc-name |Add/|)
  (:constructor |mk/Add| (|f0| |f1|))
  (:predicate |Add?|))
  (|f0| nil)
  (|f1| nil))

(defstruct (|c/Mul| (:include |Expr| (|tag| 2))
  (:conc-name |Mul/|)
  (:constructor |mk/Mul| (|f0| |f1|))
  (:predicate |Mul?|))
  (|f0| nil)
  (|f1| nil))

; ftype
(declaim (ftype (function (|Expr|) integer) |eval-2|))

(declaim (type integer |main-15|))

; body
(defun |eval-2| (|?x₀-3|)
  (case (|Expr/tag| |?x₀-3|)
    (1
      (let* ((|f-4| (|Add/f0| |?x₀-3|))
             (|f-5| (|Add/f1| |?x₀-3|)))
         (let* ((|app-6| (|eval-2| |f-4|))
                (|app-7| (|eval-2| |f-5|)))
            (%int+ |app-6| |app-7|))))
    (2
      (let* ((|f-9| (|Mul/f0| |?x₀-3|))
             (|f-10| (|Mul/f1| |?x₀-3|)))
         (let* ((|app-11| (|eval-2| |f-9|))
                (|app-12| (|eval-2| |f-10|)))
            (%int* |app-11| |app-12|))))
    (0
      (let* ((|f-14| (|Atom/f0| |?x₀-3|))) |f-14|))
    (t (error "unreachable"))))

(defparameter |main-15|
  (let* ((|con-16| (|mk/Atom| 20))
         (|con-17| (|mk/Atom| 10))
         (|con-18| (|mk/Atom| 3))
         (|con-19| (|mk/Add| |con-17| |con-18|))
         (|con-20| (|mk/Mul| |con-16| |con-19|)))
     (|eval-2| |con-20|)))
