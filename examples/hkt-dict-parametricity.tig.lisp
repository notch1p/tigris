;; == TCNF IR ==

let i_Functor_0#2/0 : Functor (Sum a) =
  let fn#4 (f5 : a → b, ?x₀6 : Sum a a) : (a → b) → Sum a a → Sum a b =
    case #6 of
      Inl⟦f7 : a⟧ => let con#8 : Sum a b = Inl⟦#7⟧; ret #8;
      Inr⟦f9 : a⟧ =>
        let app#10 : b = #5(#9); let con#11 : Sum a b = Inr⟦#10⟧; ret #11;
      _ => (⊥ : Sum a b);
  let con#12 : Functor (Sum a) = Functor⟦#4⟧; ret #12

let main#3/0 : Functor (Sum α) → Sum Int Int × Sum α Int =
  let fn#13 (d_Functor_014 : Functor (Sum α))
    : Functor (Sum α) → Sum Int Int × Sum α Int =
    let con#15 : Sum Int α = Inl⟦2⟧;
    let con#16 : Sum α Int = Inr⟦1⟧;
    let pr#17 : (a → b) → Sum Int a → Sum Int b = #2@Functor[0];
    let fn#18 (?x₀19 : Int) : Int → Int = let π#20 : Int = MUL(2, #19); ret #20;
    let app#21 : Sum Int b = #17(#18, #15);
    let pr#22 : (a → b) → Sum α a → Sum α b = #14@Functor[0];
    let fn#23 (?x₀24 : Int) : Int → Int = let π#25 : Int = ADD(1, #24); ret #25;
    let app#26 : Sum α b = #22(#23, #16);
    let p#27 : Sum Int Int × Sum α Int = ⟨#21, #26⟩; ret #27;
  ret #13
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
(defstruct (|Sum| (:conc-name |Sum/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Inl| (:include |Sum| (|tag| 0))
  (:conc-name |Inl/|)
  (:constructor |mk/Inl| (|f0|))
  (:predicate |Inl?|))
  (|f0| nil))

(defstruct (|c/Inr| (:include |Sum| (|tag| 1))
  (:conc-name |Inr/|)
  (:constructor |mk/Inr| (|f0|))
  (:predicate |Inr?|))
  (|f0| nil))

; gapply
(defun gapply1 (c a1)
  (if (eql (clos-arity c) 1)
    (funcall (clos-fn c) a1)
    (%apply-slow c (list a1))))

(defun gapply2 (c a1 a2)
  (if (eql (clos-arity c) 2)
    (funcall (clos-fn c) a1 a2)
    (%apply-slow c (list a1 a2))))

; ftype
(declaim (ftype (function (clos |Sum|) |Sum|) |fn-28|))

(declaim (ftype (function (integer) integer) |fn-30|))

(declaim (ftype (function (integer) integer) |fn-31|))

(declaim (ftype (function (t) cons) |fn-29|))

(declaim (type clos |main-3|))

; body
(defun |fn-28| (|f-5| |?x₀-6|)
  (case (|Sum/tag| |?x₀-6|)
    (0
      (let* ((|f-7| (|Inl/f0| |?x₀-6|)))
         (let* ((|con-8| (|mk/Inl| |f-7|))) |con-8|)))
    (1
      (let* ((|f-9| (|Inr/f0| |?x₀-6|)))
         (let* ((|app-10| (gapply1 |f-5| |f-9|))
                (|con-11| (|mk/Inr| |app-10|)))
            |con-11|)))
    (t (error "unreachable"))))

(defun |fn-30| (|?x₀-19|)
  (let* ((|π-20| (%int* 2 |?x₀-19|))) |π-20|))

(defun |fn-31| (|?x₀-24|)
  (let* ((|π-25| (%int+ 1 |?x₀-24|))) |π-25|))

(defun |fn-29| (|d_Functor_0-14|)
  (let* ((|con-15| (|mk/Inl| 2))
         (|con-16| (|mk/Inr| 1))
         (|fn-18| (%clos (function |fn-30|) 1))
         (|app-21| (|fn-28| |fn-18| |con-15|))
         (|fn-23| (%clos (function |fn-31|) 1))
         (|app-26| (gapply2 |d_Functor_0-14| |fn-23| |con-16|))
         (|p-27| (cons |app-21| |app-26|)))
     |p-27|))

(defparameter |i_Functor_0-2|
  (let* ((|fn-4| (%clos (function |fn-28|) 2))) |fn-4|))

(defparameter |main-3|
  (let* ((|fn-13| (%clos (function |fn-29|) 1))) |fn-13|))
