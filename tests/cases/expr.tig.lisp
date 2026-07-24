;; == TCNF CC & Optimize'd ==

let rec eval#2/1 (?x₀#4 : Expr Int) : Expr Int → Int =
  case #4 of
    Add⟦f#5 : Expr Int, f#6 : Expr Int⟧ =>
      let app#7 : Int = #2(#5);
      let app#8 : Int = #2(#6); let π#9 : Int = ADD(#7, #8); ret #9;
    Mul⟦f#10 : Expr Int, f#11 : Expr Int⟧ =>
      let app#12 : Int = #2(#10);
      let app#13 : Int = #2(#11); let π#14 : Int = MUL(#12, #13); ret #14;
    Atom⟦f#15 : Int⟧ => ret #15;
    _ => (⊥ : Int)

let main#3/0 : Int =
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

(declaim (type integer |main-3|))

; body
(defun |eval-2| (|?x₀-4|)
  (case (|Expr/tag| |?x₀-4|)
    (1
      (let* ((|f-5| (|Add/f0| |?x₀-4|))
             (|f-6| (|Add/f1| |?x₀-4|)))
         (let* ((|app-7| (|eval-2| |f-5|))
                (|app-8| (|eval-2| |f-6|))
                (|π-9| (%int+ |app-7| |app-8|)))
            |π-9|)))
    (2
      (let* ((|f-10| (|Mul/f0| |?x₀-4|))
             (|f-11| (|Mul/f1| |?x₀-4|)))
         (let* ((|app-12| (|eval-2| |f-10|))
                (|app-13| (|eval-2| |f-11|))
                (|π-14| (%int* |app-12| |app-13|)))
            |π-14|)))
    (0
      (let* ((|f-15| (|Atom/f0| |?x₀-4|))) |f-15|))
    (t (error "unreachable"))))

(defparameter |main-3|
  (let* ((|con-16| (|mk/Atom| 20))
         (|con-17| (|mk/Atom| 10))
         (|con-18| (|mk/Atom| 3))
         (|con-19| (|mk/Add| |con-17| |con-18|))
         (|con-20| (|mk/Mul| |con-16| |con-19|))
         (|app-21| (|eval-2| |con-20|)))
     |app-21|))
