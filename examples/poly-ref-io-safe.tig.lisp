;; == System F IR ==

let mkref : ∀a, a → IO (Ref a) = Λ a. %mkref

let deref : ∀a, Ref a → IO a = Λ a. symbol-value

let setf : ∀a, Ref a → a → IO Unit = Λ a. set

let pureIO : ∀a, a → IO a = Λ a. identity

let unsafeIO : ∀a, IO a → a = Λ a. identity

let (::) : ∀α, α → List α → List α = Λ α. Cons@α

let (>>=) : ∀α [Monad α], ∀a b, α a → (a → α b) → α b =
  Λ α. fun d_Monad_0 : Monad α => Λ a b. d_Monad_0[1, bind]@α

let (ₚ') : ∀α, α → IO (Ref α) = Λ α. mkref@α

let i_Monad_0 : Monad IO =
  Monad@IO Λ a. pureIO@a
    Λ a₁ b. fun act : IO a₁ => fun f : a₁ → IO b => f (unsafeIO@a₁ act)

let ioref : ∀α β, α → IO (Ref (List β)) =
  Λ α β. fun _ : α => mkref@(List β) Nil@β

let f : ∀α, α → IO Unit =
  Λ α.
    rec fun f : α → IO Unit =>
      fun _ : α =>
        let rd_Monad_0 : Monad IO = i_Monad_0
        in rd_Monad_0[1, bind]@IO (ioref@Unit@Int ())
             fun ref : Ref (List Int) =>
               setf@(List Int) ref (Cons@Int 1 Nil@Int)
and g : ∀α, α → IO Bool =
  Λ α.
    rec fun g : α → IO Bool =>
      fun _ : α =>
        let rd_Monad_0 : Monad IO = i_Monad_0
        in rd_Monad_0[1, bind]@IO (ioref@Unit@?m.67 ())
             fun ref : Ref (List ?m.67) =>
               rd_Monad_0[1, bind]@IO (deref@(List ?m.67) ref)
                 fun ?x₀ : List ?m.67 =>
                   match ?x₀ with
                   | Nil => rd_Monad_0[0, pure]@IO true
and main : IO Bool = let _ : IO Unit = f@Unit () in g@Unit ()
;; == TCNF IR ==

let mkref#2/1 (η#3 : a) : a → IO (Ref a) =
  let ffi#4 : IO (Ref a) = @%mkref(#3); ret #4

let deref#5/1 (η#6 : Ref a) : Ref a → IO a =
  let ffi#7 : IO a = @symbol-value(#6); ret #7

let setf#8/2 (η#9 : Ref a, η#10 : a) : Ref a → a → IO Unit =
  let ffi#11 : IO Unit = @set(#9, #10); ret #11

let pureIO#12/1 (η#13 : a) : a → IO a =
  let ffi#14 : IO a = @identity(#13); ret #14

let unsafeIO#15/1 (η#16 : IO a) : IO a → a =
  let ffi#17 : a = @identity(#16); ret #17

let i_Monad_0#18/0 : Monad IO =
  let fn#19 (act#20 : IO a₁, f#21 : a₁ → IO b) : IO a₁ → (a₁ → IO b) → IO b =
    let app#22 : a₁ = #15(#20); let app#23 : IO b = #21(#22); ret #23;
  let con#24 : Monad IO = Monad⟦#12, #19⟧; ret #24

let ioref#25/1 (_#26 : α) : α → IO (Ref (List β)) =
  let con#27 : List β = Nil⟦⟧; let app#28 : IO (Ref (List β)) = #2(#27); ret #28

let rec f#29/1 (_#31 : α) : α → IO Unit =
  let pr#32 : IO ?m.10 → (?m.10 → IO ?m.11) → IO ?m.11 = #18@Monad[1];
  let app#33 : IO (Ref (List Int)) = #25(());
  let fn#34 (ref#35 : Ref (List Int)) : Ref (List Int) → IO Unit =
    let con#36 : List Int = Nil⟦⟧;
    let con#37 : List Int = Cons⟦1, #36⟧;
    let app#38 : IO Unit = #8(#35, #37); ret #38;
  let app#39 : IO ?m.11 = #32(#33, #34); ret #39

let rec g#30/1 (_#40 : α) : α → IO Bool =
  let pr#41 : IO ?m.10 → (?m.10 → IO ?m.11) → IO ?m.11 = #18@Monad[1];
  let app#42 : IO (Ref (List ?m.67)) = #25(());
  let fn#43 (ref#44 : Ref (List ?m.67)) : Ref (List ?m.67) → IO Bool =
    let pr#45 : IO ?m.10 → (?m.10 → IO ?m.11) → IO ?m.11 = #18@Monad[1];
    let app#46 : IO (List ?m.67) = #5(#44);
    let fn#47 (?x₀#48 : List ?m.67) : List ?m.67 → IO Bool =
      join fail#49 : IO Bool = let fail#50 : IO Bool = #0(#48); ret #50;
      case #48 of
        Nil =>
          let pr#51 : ?m.9 → IO ?m.9 = #18@Monad[0];
          let app#52 : IO ?m.9 = #51(true); ret #52;
        _ => jump #49();
    let app#53 : IO ?m.11 = #45(#46, #47); ret #53;
  let app#54 : IO ?m.11 = #41(#42, #43); ret #54

let main#55/0 : IO Bool =
  let app#56 : IO Unit = #29(()); let app#57 : IO Bool = #30(()); ret #57
;; == TCNF CC & Optimize'd ==

let fn#58/2 (act#20 : IO a₁, f#21 : a₁ → IO b) : IO a₁ → (a₁ → IO b) → IO b =
  let app#22 : a₁ = #15(#20); let app#23 : IO b = #21(#22); ret #23

let fn#59/1 (ref#35 : Ref (List Int)) : Ref (List Int) → IO Unit =
  let con#36 : List Int = Nil⟦⟧;
  let con#37 : List Int = Cons⟦1, #36⟧;
  let app#38 : IO Unit = #8(#35, #37); ret #38

let fn#61/1 (?x₀#48 : List ?m.67) : List ?m.67 → IO Bool =
  join fail#49 : IO Bool = let fail#50 : IO Bool = #0(#48); ret #50;
  case #48 of Nil => let app#52 : IO ?m.9 = #12(true); ret #52; _ => jump #49()

let fn#60/1 (ref#44 : Ref (List ?m.67)) : Ref (List ?m.67) → IO Bool =
  let app#46 : IO (List ?m.67) = #5(#44);
  let fn#47 : List ?m.67 → IO Bool = 𝐂⟦61⟧;
  let app#53 : IO ?m.11 = #58(#46, #47); ret #53

let mkref#2/1 (η#3 : a) : a → IO (Ref a) =
  let ffi#4 : IO (Ref a) = @%mkref(#3); ret #4

let deref#5/1 (η#6 : Ref a) : Ref a → IO a =
  let ffi#7 : IO a = @symbol-value(#6); ret #7

let setf#8/2 (η#9 : Ref a, η#10 : a) : Ref a → a → IO Unit =
  let ffi#11 : IO Unit = @set(#9, #10); ret #11

let pureIO#12/1 (η#13 : a) : a → IO a =
  let ffi#14 : IO a = @identity(#13); ret #14

let unsafeIO#15/1 (η#16 : IO a) : IO a → a =
  let ffi#17 : a = @identity(#16); ret #17

let i_Monad_0#18/0 : Monad IO =
  let fn#19 : IO a₁ → (a₁ → IO b) → IO b = 𝐂⟦58⟧;
  let con#24 : Monad IO = Monad⟦#12, #19⟧; ret #24

let ioref#25/1 (_#26 : α) : α → IO (Ref (List β)) =
  let con#27 : List β = Nil⟦⟧; let app#28 : IO (Ref (List β)) = #2(#27); ret #28

let rec f#29/1 (_#31 : α) : α → IO Unit =
  let app#33 : IO (Ref (List Int)) = #25(());
  let fn#34 : Ref (List Int) → IO Unit = 𝐂⟦59⟧;
  let app#39 : IO ?m.11 = #58(#33, #34); ret #39

let rec g#30/1 (_#40 : α) : α → IO Bool =
  let app#42 : IO (Ref (List ?m.67)) = #25(());
  let fn#43 : Ref (List ?m.67) → IO Bool = 𝐂⟦60⟧;
  let app#54 : IO ?m.11 = #58(#42, #43); ret #54

let main#55/0 : IO Bool =
  let app#56 : IO Unit = #29(()); let app#57 : IO Bool = #30(()); ret #57
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
(defstruct (|List| (:conc-name |List/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Nil| (:include |List| (|tag| 0))
  (:conc-name |Nil/|)
  (:constructor |mk/Nil| ())
  (:predicate |Nil?|)))

(defstruct (|c/Cons| (:include |List| (|tag| 1))
  (:conc-name |Cons/|)
  (:constructor |mk/Cons| (|f0| |f1|))
  (:predicate |Cons?|))
  (|f0| nil)
  (|f1| nil))

(defstruct (|Monad| (:conc-name |Monad/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Monad| (:include |Monad| (|tag| 0))
  (:conc-name |Monad/|)
  (:constructor |mk/Monad| (|f0| |f1|))
  (:predicate |Monad?|))
  (|f0| nil)
  (|f1| nil))

; gapply
(defun gapply1 (c a1)
  (if (eql (clos-arity c) 1)
    (funcall (clos-fn c) a1)
    (%apply-slow c (list a1))))

; ftype
(declaim (ftype (function (t clos) t) |fn-58|))

(declaim (ftype (function (|List|) t) |fn-61|))

(declaim (type |Monad| |i_Monad_0-18|))

; body
(defun |fn-58| (|act-20| |f-21|)
  (let* ((|app-22| (|unsafeIO-15| |act-20|))) (gapply1 |f-21| |app-22|)))

(defun |fn-59| (|ref-35|)
  (let* ((|con-36| (|mk/Nil|))
         (|con-37| (|mk/Cons| 1 |con-36|)))
     (|setf-8| |ref-35| |con-37|)))

(defun |fn-61| (|?x₀-48|)
  (labels ((|fail-49| () (error 'match-failure :discr (list |?x₀-48|))))
     (case (|List/tag| |?x₀-48|)
       (0
         (|pureIO-12| t))
       (t (|fail-49|)))))

(defun |fn-60| (|ref-44|)
  (let* ((|app-46| (|deref-5| |ref-44|))
         (|fn-47| (%clos (function |fn-61|) 1)))
     (|fn-58| |app-46| |fn-47|)))

(defun |mkref-2| (|η-3|)
  (%mkref |η-3|))

(defun |deref-5| (|η-6|)
  (symbol-value |η-6|))

(defun |setf-8| (|η-9| |η-10|)
  (set |η-9| |η-10|))

(defun |pureIO-12| (|η-13|)
  (identity |η-13|))

(defun |unsafeIO-15| (|η-16|)
  (identity |η-16|))

(defun |ioref-25| (|_-26|)
  (let* ((|con-27| (|mk/Nil|))) (|mkref-2| |con-27|)))

(defun |f-29| (|_-31|)
  (let* ((|app-33| (|ioref-25| nil))
         (|fn-34| (%clos (function |fn-59|) 1)))
     (|fn-58| |app-33| |fn-34|)))

(defun |g-30| (|_-40|)
  (let* ((|app-42| (|ioref-25| nil))
         (|fn-43| (%clos (function |fn-60|) 1)))
     (|fn-58| |app-42| |fn-43|)))

(defparameter |i_Monad_0-18|
  (let* ((|fn-19| (%clos (function |fn-58|) 2)))
     (|mk/Monad| (%clos (function |pureIO-12|) 1) |fn-19|)))

(defparameter |main-55|
  (let* ((|app-56| (|f-29| nil))) (|g-30| nil)))
