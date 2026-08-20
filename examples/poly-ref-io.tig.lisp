;; == System F IR ==

let mkref : ∀a, a → IO (Ref a) = Λ a. quote

let deref : ∀a, Ref a → IO a = Λ a. eval

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

let ioref : ∀α, IO (Ref (List α)) = Λ α. mkref@(List α) Nil@α

let f : ∀α, α → IO Unit =
  Λ α.
    rec fun f : α → IO Unit =>
      fun _ : α =>
        let rd_Monad_0 : Monad IO = i_Monad_0
        in rd_Monad_0[1, bind]@IO ioref@Int
             fun ref : Ref (List Int) =>
               setf@(List Int) ref (Cons@Int 1 Nil@Int)
and g : ∀α, α → IO Bool =
  Λ α.
    rec fun g : α → IO Bool =>
      fun _ : α =>
        let rd_Monad_0 : Monad IO = i_Monad_0
        in rd_Monad_0[1, bind]@IO ioref@?m.48
             fun ref : Ref (List ?m.48) =>
               rd_Monad_0[1, bind]@IO (deref@(List ?m.48) ref)
                 fun ?x₀ : List ?m.48 =>
                   match ?x₀ with
                   | Nil => rd_Monad_0[0, pure]@IO true
and main : IO Bool = let _ : IO Unit = f@Unit () in g@Unit ()
;; == TCNF IR ==

let mkref#2/1 (η#3 : a) : IO (Ref a) =
  let ffi#4 : IO (Ref a) = @quote(#3) in ret #4

let deref#5/1 (η#6 : Ref a) : IO a = let ffi#7 : IO a = @eval(#6) in ret #7

let setf#8/2 (η#9 : Ref a, η#10 : a) : IO Unit =
  let ffi#11 : IO Unit = @set(#9, #10) in ret #11

let pureIO#12/1 (η#13 : a) : IO a =
  let ffi#14 : IO a = @identity(#13) in ret #14

let unsafeIO#15/1 (η#16 : IO a) : a = let ffi#17 : a = @identity(#16) in ret #17

let i_Monad_0#18/0 : Monad IO =
  let fn#19 (act#20 : IO a₁, f#21 : a₁ → IO b) : IO b =
    let app#22 : a₁ = #15(#20)
    let app#23 : IO b = #21(#22) in ret #23
  let con#24 : Monad IO = Monad⟦#12, #19⟧ in ret #24

let ioref#25/0 : IO (Ref (List α)) =
  let con#26 : List α = Nil⟦⟧
  let app#27 : IO (Ref (List α)) = #2(#26) in ret #27

let rec f#28/1 (_#30 : α) : IO Unit =
  let pr#31 : IO ?m.10 → (?m.10 → IO ?m.11) → IO ?m.11 = #18@Monad[1]
  let fn#32 (ref#33 : Ref (List Int)) : IO Unit =
    let con#34 : List Int = Nil⟦⟧
    let con#35 : List Int = Cons⟦1, #34⟧
    let app#36 : IO Unit = #8(#33, #35) in ret #36
  let app#37 : IO ?m.11 = #31(#25, #32) in ret #37

let rec g#29/1 (_#38 : α) : IO Bool =
  let pr#39 : IO ?m.10 → (?m.10 → IO ?m.11) → IO ?m.11 = #18@Monad[1]
  let fn#40 (ref#41 : Ref (List ?m.48)) : IO Bool =
    let pr#42 : IO ?m.10 → (?m.10 → IO ?m.11) → IO ?m.11 = #18@Monad[1]
    let app#43 : IO (List ?m.48) = #5(#41)
    let fn#44 (?x₀#45 : List ?m.48) : IO Bool =
      join fail#46 : IO Bool = let fail#47 : IO Bool = #0(#45) in ret #47
      case #45 of
        Nil =>
          let pr#48 : ?m.9 → IO ?m.9 = #18@Monad[0]
          let app#49 : IO ?m.9 = #48(true) in ret #49;
        _ => jump #46()
    let app#50 : IO ?m.11 = #42(#43, #44) in ret #50
  let app#51 : IO ?m.11 = #39(#25, #40) in ret #51

let main#52/0 : IO Bool =
  let app#53 : IO Unit = #28(())
  let app#54 : IO Bool = #29(()) in ret #54
;; == TCNF CC & Optimize'd ==

let fn#55/2 (act#20 : IO a₁, f#21 : a₁ → IO b) : IO b =
  let app#22 : a₁ = #15(#20)
  let app#23 : IO b = #21(#22) in ret #23

let fn#56/1 (ref#33 : Ref (List Int)) : IO Unit =
  let con#34 : List Int = Nil⟦⟧
  let con#35 : List Int = Cons⟦1, #34⟧
  let app#36 : IO Unit = #8(#33, #35) in ret #36

let fn#58/1 (?x₀#45 : List ?m.48) : IO Bool =
  join fail#46 : IO Bool = let fail#47 : IO Bool = #0(#45) in ret #47
  case #45 of
    Nil => let app#49 : IO ?m.9 = #12(true) in ret #49;
    _ => jump #46()

let fn#57/1 (ref#41 : Ref (List ?m.48)) : IO Bool =
  let app#43 : IO (List ?m.48) = #5(#41)
  let fn#44 : List ?m.48 → IO Bool = 𝐂⟦58⟧
  let app#50 : IO ?m.11 = #55(#43, #44) in ret #50

let mkref#2/1 (η#3 : a) : IO (Ref a) =
  let ffi#4 : IO (Ref a) = @quote(#3) in ret #4

let deref#5/1 (η#6 : Ref a) : IO a = let ffi#7 : IO a = @eval(#6) in ret #7

let setf#8/2 (η#9 : Ref a, η#10 : a) : IO Unit =
  let ffi#11 : IO Unit = @set(#9, #10) in ret #11

let pureIO#12/1 (η#13 : a) : IO a =
  let ffi#14 : IO a = @identity(#13) in ret #14

let unsafeIO#15/1 (η#16 : IO a) : a = let ffi#17 : a = @identity(#16) in ret #17

let i_Monad_0#18/0 : Monad IO =
  let fn#19 : IO a₁ → (a₁ → IO b) → IO b = 𝐂⟦55⟧
  let con#24 : Monad IO = Monad⟦#12, #19⟧ in ret #24

let ioref#25/0 : IO (Ref (List α)) =
  let con#26 : List α = Nil⟦⟧
  let app#27 : IO (Ref (List α)) = #2(#26) in ret #27

let rec f#28/1 (_#30 : α) : IO Unit =
  let fn#32 : Ref (List Int) → IO Unit = 𝐂⟦56⟧
  let app#37 : IO ?m.11 = #55(#25, #32) in ret #37

let rec g#29/1 (_#38 : α) : IO Bool =
  let fn#40 : Ref (List ?m.48) → IO Bool = 𝐂⟦57⟧
  let app#51 : IO ?m.11 = #55(#25, #40) in ret #51

let main#52/0 : IO Bool =
  let app#53 : IO Unit = #28(())
  let app#54 : IO Bool = #29(()) in ret #54
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
(declaim (ftype (function (t clos) t) |fn-55|))

(declaim (ftype (function (|List|) t) |fn-58|))

(declaim (type |Monad| |i_Monad_0-18|))

; body
(defun |fn-55| (|act-20| |f-21|)
  (let* ((|app-22| (|unsafeIO-15| |act-20|))) (gapply1 |f-21| |app-22|)))

(defun |fn-56| (|ref-33|)
  (let* ((|con-34| (|mk/Nil|))
         (|con-35| (|mk/Cons| 1 |con-34|)))
     (|setf-8| |ref-33| |con-35|)))

(defun |fn-58| (|?x₀-45|)
  (labels ((|fail-46| () (error 'match-failure :discr (list |?x₀-45|))))
     (case (|List/tag| |?x₀-45|)
       (0
         (|pureIO-12| t))
       (t (|fail-46|)))))

(defun |fn-57| (|ref-41|)
  (let* ((|app-43| (|deref-5| |ref-41|))
         (|fn-44| (%clos (function |fn-58|) 1)))
     (|fn-55| |app-43| |fn-44|)))

(defun |mkref-2| (|η-3|)
  (quote |η-3|))

(defun |deref-5| (|η-6|)
  (eval |η-6|))

(defun |setf-8| (|η-9| |η-10|)
  (set |η-9| |η-10|))

(defun |pureIO-12| (|η-13|)
  (identity |η-13|))

(defun |unsafeIO-15| (|η-16|)
  (identity |η-16|))

(defun |f-28| (|_-30|)
  (let* ((|fn-32| (%clos (function |fn-56|) 1))) (|fn-55| |ioref-25| |fn-32|)))

(defun |g-29| (|_-38|)
  (let* ((|fn-40| (%clos (function |fn-57|) 1))) (|fn-55| |ioref-25| |fn-40|)))

(defparameter |i_Monad_0-18|
  (let* ((|fn-19| (%clos (function |fn-55|) 2)))
     (|mk/Monad| (%clos (function |pureIO-12|) 1) |fn-19|)))

(defparameter |ioref-25|
  (let* ((|con-26| (|mk/Nil|))) (|mkref-2| |con-26|)))

(defparameter |main-52|
  (let* ((|app-53| (|f-28| nil))) (|g-29| nil)))
