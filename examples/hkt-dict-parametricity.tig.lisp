;; == System F IR ==

let i_Functor_0 : ∀ a, Functor (Sum a) =
  (Λ a.
     Functor@(Sum a)
       (Λ a b.
          fun f : a → b =>
            fun ?x₀ : Sum a a =>
              match ?x₀ with | Inl a => Inl@a@b a | Inr b => Inr@a@b (f b)))

let main : ∀ α [Functor Sum α], Sum Int Int × Sum α Int =
  (Λ α.
     let rd_Functor_0 : Functor (Sum Int) = i_Functor_0@Int
     in fun d_Functor_0 : Functor (Sum α) =>
       let a : ∀ α, Sum Int α = (Λ α. Inl@Int@α 2)
       and b : ∀ α, Sum α Int = (Λ α. Inr@α@Int 1)
       in (rd_Functor_0[0, fmap]@(Sum Int)
          (fun ?x₀ : Int =>
             mul
               2
               ?x₀)
          a@Int , d_Functor_0[0, fmap]@(Sum α)
          (fun ?x₀ : Int => add 1 ?x₀) b@α))
;; == TCNF IR ==

let i_Functor_0#2/0 : Functor (Sum a) =
  let fn#3 (f#4 : a → b, ?x₀#5 : Sum a a) : (a → b) → Sum a a → Sum a b =
    case #5 of
      Inl⟦f#6 : a⟧ => let con#7 : Sum a b = Inl⟦#6⟧; ret #7;
      Inr⟦f#8 : a⟧ =>
        let app#9 : b = #4(#8); let con#10 : Sum a b = Inr⟦#9⟧; ret #10;
      _ => (⊥ : Sum a b);
  let con#11 : Functor (Sum a) = Functor⟦#3⟧; ret #11

let main#12/0 : Functor (Sum α) → Sum Int Int × Sum α Int =
  let fn#13 (d_Functor_0#14 : Functor (Sum α))
    : Functor (Sum α) → Sum Int Int × Sum α Int =
    let con#15 : Sum Int α = Inl⟦2⟧;
    let con#16 : Sum α Int = Inr⟦1⟧;
    let pr#17 : (a → b) → Sum Int a → Sum Int b = #2@Functor[0];
    let fn#18 (?x₀#19 : Int) : Int → Int =
      let π#20 : Int = MUL(2, #19); ret #20;
    let app#21 : Sum Int b = #17(#18, #15);
    let pr#22 : (a → b) → Sum α a → Sum α b = #14@Functor[0];
    let fn#23 (?x₀#24 : Int) : Int → Int =
      let π#25 : Int = ADD(1, #24); ret #25;
    let app#26 : Sum α b = #22(#23, #16);
    let p#27 : Sum Int Int × Sum α Int = ⟨#21, #26⟩; ret #27;
  ret #13
;; == TCNF CC & Optimize'd ==

let fn#28/2 (f#4 : a → b, ?x₀#5 : Sum a a) : (a → b) → Sum a a → Sum a b =
  case #5 of
    Inl⟦f#6 : a⟧ => let con#7 : Sum a b = Inl⟦#6⟧; ret #7;
    Inr⟦f#8 : a⟧ =>
      let app#9 : b = #4(#8); let con#10 : Sum a b = Inr⟦#9⟧; ret #10;
    _ => (⊥ : Sum a b)

let fn#30/1 (?x₀#19 : Int) : Int → Int = let π#20 : Int = MUL(2, #19); ret #20

let fn#31/1 (?x₀#24 : Int) : Int → Int = let π#25 : Int = ADD(1, #24); ret #25

let fn#29/1 (d_Functor_0#14 : Functor (Sum α))
  : Functor (Sum α) → Sum Int Int × Sum α Int =
  let con#15 : Sum Int α = Inl⟦2⟧;
  let con#16 : Sum α Int = Inr⟦1⟧;
  let fn#18 : Int → Int = 𝐂⟦30⟧;
  let app#21 : Sum Int b = #28(#18, #15);
  let fn#23 : Int → Int = 𝐂⟦31⟧;
  let app#26 : Sum α b = #14(#23, #16);
  let p#27 : Sum Int Int × Sum α Int = ⟨#21, #26⟩; ret #27

let i_Functor_0#2/0 : Functor (Sum a) =
  let fn#3 : (a → b) → Sum a a → Sum a b = 𝐂⟦28⟧; ret #3

let main#12/0 : Functor (Sum α) → Sum Int Int × Sum α Int =
  let fn#13 : Functor (Sum α) → Sum Int Int × Sum α Int = 𝐂⟦29⟧; ret #13
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

(declaim (type clos |main-12|))

; body
(defun |fn-28| (|f-4| |?x₀-5|)
  (case (|Sum/tag| |?x₀-5|)
    (0
      (let* ((|f-6| (|Inl/f0| |?x₀-5|))) (|mk/Inl| |f-6|)))
    (1
      (let* ((|f-8| (|Inr/f0| |?x₀-5|)))
         (let* ((|app-9| (gapply1 |f-4| |f-8|))) (|mk/Inr| |app-9|))))
    (t (error "unreachable"))))

(defun |fn-30| (|?x₀-19|)
  (%int* 2 |?x₀-19|))

(defun |fn-31| (|?x₀-24|)
  (%int+ 1 |?x₀-24|))

(defun |fn-29| (|d_Functor_0-14|)
  (let* ((|con-15| (|mk/Inl| 2))
         (|con-16| (|mk/Inr| 1))
         (|fn-18| (%clos (function |fn-30|) 1))
         (|app-21| (|fn-28| |fn-18| |con-15|))
         (|fn-23| (%clos (function |fn-31|) 1))
         (|app-26| (gapply2 |d_Functor_0-14| |fn-23| |con-16|)))
     (cons |app-21| |app-26|)))

(defparameter |i_Functor_0-2|
  (%clos (function |fn-28|) 2))

(defparameter |main-12|
  (%clos (function |fn-29|) 1))
