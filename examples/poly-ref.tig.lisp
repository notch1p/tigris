;; == System F IR ==

let (::) : ∀α, α → List α → List α = Λ α. Cons@α

let mkref : ∀a, a → Ref a = Λ a. quote

let deref : ∀a, Ref a → a = Λ a. eval

let setf : ∀a, Ref a → a → a = Λ a. set

let (ₚ') : ∀α, α → Ref α = Λ α. mkref@α

let ref : ∀α, Ref (List α) = Λ α. mkref@(List α) Nil@α

let main : Int =
  let _ : List Bool = setf@(List Bool) ref@Bool (Cons@Bool true Nil@Bool)
  in match deref@(List Int) ref@Int with
     | Cons x _ => add x 1
;; == TCNF IR ==

let mkref#2/1 (η#3 : a) : a → Ref a = let ffi#4 : Ref a = @quote(#3); ret #4

let deref#5/1 (η#6 : Ref a) : Ref a → a = let ffi#7 : a = @eval(#6); ret #7

let setf#8/2 (η#9 : Ref a, η#10 : a) : Ref a → a → a =
  let ffi#11 : a = @set(#9, #10); ret #11

let ref#12/0 : Ref (List α) =
  let con#13 : List α = Nil⟦⟧; let app#14 : Ref (List α) = #2(#13); ret #14

let main#15/0 : Int =
  let con#16 : List Bool = Nil⟦⟧;
  let con#17 : List Bool = Cons⟦true, #16⟧;
  let app#18 : List Bool = #8(#12, #17);
  let app#19 : List Int = #5(#12);
  join fail#20 : Int = let fail#21 : Int = #0(#19); ret #21;
  case #19 of
    Cons⟦f#22 : Int, f#23 : List Int⟧ => let π#24 : Int = ADD(#22, 1); ret #24;
    _ => jump #20()
;; == TCNF CC & Optimize'd ==

let mkref#2/1 (η#3 : a) : a → Ref a = let ffi#4 : Ref a = @quote(#3); ret #4

let deref#5/1 (η#6 : Ref a) : Ref a → a = let ffi#7 : a = @eval(#6); ret #7

let setf#8/2 (η#9 : Ref a, η#10 : a) : Ref a → a → a =
  let ffi#11 : a = @set(#9, #10); ret #11

let ref#12/0 : Ref (List α) =
  let con#13 : List α = Nil⟦⟧; let app#14 : Ref (List α) = #2(#13); ret #14

let main#15/0 : Int =
  let con#16 : List Bool = Nil⟦⟧;
  let con#17 : List Bool = Cons⟦true, #16⟧;
  let app#18 : List Bool = #8(#12, #17);
  let app#19 : List Int = #5(#12);
  join fail#20 : Int = let fail#21 : Int = #0(#19); ret #21;
  case #19 of
    Cons⟦f#22 : Int, f#23 : List Int⟧ => let π#24 : Int = ADD(#22, 1); ret #24;
    _ => jump #20()
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

; ftype
(declaim (type integer |main-15|))

; body
(defun |mkref-2| (|η-3|)
  (quote |η-3|))

(defun |deref-5| (|η-6|)
  (eval |η-6|))

(defun |setf-8| (|η-9| |η-10|)
  (set |η-9| |η-10|))

(defparameter |ref-12|
  (let* ((|con-13| (|mk/Nil|))) (|mkref-2| |con-13|)))

(defparameter |main-15|
  (let* ((|con-16| (|mk/Nil|))
         (|con-17| (|mk/Cons| t |con-16|))
         (|app-18| (|setf-8| |ref-12| |con-17|))
         (|app-19| (|deref-5| |ref-12|)))
     (labels ((|fail-20| () (error 'match-failure :discr (list |app-19|))))
        (case (|List/tag| |app-19|)
          (1
            (let* ((|f-22| (|Cons/f0| |app-19|))
                   (|f-23| (|Cons/f1| |app-19|)))
               (%int+ |f-22| 1)))
          (t (|fail-20|))))))
