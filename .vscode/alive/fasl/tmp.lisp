;; == System F IR ==

let rec eval : Expr Int → Int =
  fun ?x₀ : Expr Int =>
    match ?x₀ with
    | Atom a => a
    | Add e1 e2 => add (eval e1) (eval e2)
    | Sub e1 e2 => sub (eval e1) (eval e2)
    | Mul e1 e2 => mul (eval e1) (eval e2)
    | Div e1 e2 => div (eval e1) (eval e2)

let prog : Expr Int =
  Mul@Int
    (Atom@Int
       20)
    (Sub@Int
       (Mul@Int
          (Atom@Int
             10)
          (Atom@Int
             20))
       (Div@Int
          (Atom@Int
             2400)
          (Add@Int
             (Atom@Int
                120)
             (Add@Int (Mul@Int (Atom@Int 10) (Atom@Int 20)) (Atom@Int 0)))))

let 3860 =
  eval prog
;; == Optimized IR ==

main (arg) {
  letω 
    label eval(args0):
      let _pL#?x₀ = args0[0]
      case _pL#?x₀ of
        «Add/2» →
          let p1 = _pL#?x₀[0]
          let p2 = _pL#?x₀[1]
          letι u3 = ()
          let pair4 = ⟨p1, u3⟩
          let call5 = eval(pair4)
          letι u6 = ()
          let pair7 = ⟨p2, u6⟩
          let call8 = eval(pair7)
          let p9 = ADD(call5, call8)
          RET p9
        «Div/2» →
          let p10 = _pL#?x₀[0]
          let p11 = _pL#?x₀[1]
          letι u12 = ()
          let pair13 = ⟨p10, u12⟩
          let call14 = eval(pair13)
          letι u15 = ()
          let pair16 = ⟨p11, u15⟩
          let call17 = eval(pair16)
          let p18 = DIV(call14, call17)
          RET p18
        «Mul/2» →
          let p19 = _pL#?x₀[0]
          let p20 = _pL#?x₀[1]
          letι u21 = ()
          let pair22 = ⟨p19, u21⟩
          let call23 = eval(pair22)
          letι u24 = ()
          let pair25 = ⟨p20, u24⟩
          let call26 = eval(pair25)
          let p27 = MUL(call23, call26)
          RET p27
        «Atom/1» →
          let p28 = _pL#?x₀[0]
          RET p28
        «Sub/2» →
          let p29 = _pL#?x₀[0]
          let p30 = _pL#?x₀[1]
          letι u31 = ()
          let pair32 = ⟨p29, u31⟩
          let call33 = eval(pair32)
          letι u34 = ()
          let pair35 = ⟨p30, u34⟩
          let call36 = eval(pair35)
          let p37 = SUB(call33, call36)
          RET p37
  in
  letι c38 = 20
  let con39 = Atom⟦c38⟧
  letι c40 = 10
  let con41 = Atom⟦c40⟧
  letι c42 = 20
  let con43 = Atom⟦c42⟧
  let con44 = Mul⟦con41, con43⟧
  letι c45 = 2400
  let con46 = Atom⟦c45⟧
  letι c47 = 120
  let con48 = Atom⟦c47⟧
  letι c49 = 10
  let con50 = Atom⟦c49⟧
  letι c51 = 20
  let con52 = Atom⟦c51⟧
  let con53 = Mul⟦con50, con52⟧
  letι c54 = 0
  let con55 = Atom⟦c54⟧
  let con56 = Add⟦con53, con55⟧
  let con57 = Add⟦con48, con56⟧
  let con58 = Div⟦con46, con57⟧
  let con59 = Sub⟦con44, con58⟧
  let con60 = Mul⟦con39, con59⟧
  letι u61 = ()
  let pair62 = ⟨con60, u61⟩
  let call63 = eval(pair62)
  letι c64 = 3860
  let cmp65 = EQⁱ(call63, c64)
  if cmp65 then RET con60 else MATCHFAILURE
}
;; == Optimized IR CC'd ==

eval (payload) {
  let α = payload[0]
  let Γ = payload[1]
  let _pL#?x₀ = α[0]
  case _pL#?x₀ of
    «Add/2» →
      let p1 = _pL#?x₀[0]
      let p2 = _pL#?x₀[1]
      letι u3 = ()
      let pair4 = ⟨p1, u3⟩
      let ρ1001 = ⟨pair4, Γ⟩
      let call5 = eval(ρ1001)
      letι u6 = ()
      let pair7 = ⟨p2, u6⟩
      let ρ1000 = ⟨pair7, Γ⟩
      let call8 = eval(ρ1000)
      let p9 = ADD(call5, call8)
      RET p9
    «Div/2» →
      let p10 = _pL#?x₀[0]
      let p11 = _pL#?x₀[1]
      letι u12 = ()
      let pair13 = ⟨p10, u12⟩
      let ρ1003 = ⟨pair13, Γ⟩
      let call14 = eval(ρ1003)
      letι u15 = ()
      let pair16 = ⟨p11, u15⟩
      let ρ1002 = ⟨pair16, Γ⟩
      let call17 = eval(ρ1002)
      let p18 = DIV(call14, call17)
      RET p18
    «Mul/2» →
      let p19 = _pL#?x₀[0]
      let p20 = _pL#?x₀[1]
      letι u21 = ()
      let pair22 = ⟨p19, u21⟩
      let ρ1005 = ⟨pair22, Γ⟩
      let call23 = eval(ρ1005)
      letι u24 = ()
      let pair25 = ⟨p20, u24⟩
      let ρ1004 = ⟨pair25, Γ⟩
      let call26 = eval(ρ1004)
      let p27 = MUL(call23, call26)
      RET p27
    «Atom/1» →
      let p28 = _pL#?x₀[0]
      RET p28
    «Sub/2» →
      let p29 = _pL#?x₀[0]
      let p30 = _pL#?x₀[1]
      letι u31 = ()
      let pair32 = ⟨p29, u31⟩
      let ρ1007 = ⟨pair32, Γ⟩
      let call33 = eval(ρ1007)
      letι u34 = ()
      let pair35 = ⟨p30, u34⟩
      let ρ1006 = ⟨pair35, Γ⟩
      let call36 = eval(ρ1006)
      let p37 = SUB(call33, call36)
      RET p37
}

main (payload) {
  let Γ = 𝐄⟦⟧
  letι c38 = 20
  let con39 = Atom⟦c38⟧
  letι c40 = 10
  let con41 = Atom⟦c40⟧
  letι c42 = 20
  let con43 = Atom⟦c42⟧
  let con44 = Mul⟦con41, con43⟧
  letι c45 = 2400
  let con46 = Atom⟦c45⟧
  letι c47 = 120
  let con48 = Atom⟦c47⟧
  letι c49 = 10
  let con50 = Atom⟦c49⟧
  letι c51 = 20
  let con52 = Atom⟦c51⟧
  let con53 = Mul⟦con50, con52⟧
  letι c54 = 0
  let con55 = Atom⟦c54⟧
  let con56 = Add⟦con53, con55⟧
  let con57 = Add⟦con48, con56⟧
  let con58 = Div⟦con46, con57⟧
  let con59 = Sub⟦con44, con58⟧
  let con60 = Mul⟦con39, con59⟧
  letι u61 = ()
  let pair62 = ⟨con60, u61⟩
  let ρc1010 = ⟨pair62, Γ⟩
  let call63 = eval(ρc1010)
  letι c64 = 3860
  let cmp65 = EQⁱ(call63, c64)
  if cmp65 then RET con60 else MATCHFAILURE
}
;; == CPS IR ==

eval (payload, k) {
  let α = payload[0]
  let Γ = payload[1]
  let _pL#?x₀ = α[0]
  case _pL#?x₀ of
    «Add/2» →
      let p1 = _pL#?x₀[0]
      let p2 = _pL#?x₀[1]
      let u3 = ()
      let pair4 = ⟨p1, u3⟩
      let ρ1001 = ⟨pair4, Γ⟩
      letκ k1 v0 =
        let u6 = ()
        let pair7 = ⟨p2, u6⟩
        let ρ1000 = ⟨pair7, Γ⟩
        letκ k3 v2 =
          let p9 = ADD(v0, v2)
          APPLY k(p9)
        eval(ρ1000, k3)
      eval(ρ1001, k1)
    «Div/2» →
      let p10 = _pL#?x₀[0]
      let p11 = _pL#?x₀[1]
      let u12 = ()
      let pair13 = ⟨p10, u12⟩
      let ρ1003 = ⟨pair13, Γ⟩
      letκ k5 v4 =
        let u15 = ()
        let pair16 = ⟨p11, u15⟩
        let ρ1002 = ⟨pair16, Γ⟩
        letκ k7 v6 =
          let p18 = DIV(v4, v6)
          APPLY k(p18)
        eval(ρ1002, k7)
      eval(ρ1003, k5)
    «Mul/2» →
      let p19 = _pL#?x₀[0]
      let p20 = _pL#?x₀[1]
      let u21 = ()
      let pair22 = ⟨p19, u21⟩
      let ρ1005 = ⟨pair22, Γ⟩
      letκ k9 v8 =
        let u24 = ()
        let pair25 = ⟨p20, u24⟩
        let ρ1004 = ⟨pair25, Γ⟩
        letκ k11 v10 =
          let p27 = MUL(v8, v10)
          APPLY k(p27)
        eval(ρ1004, k11)
      eval(ρ1005, k9)
    «Atom/1» →
      let p28 = _pL#?x₀[0]
      APPLY k(p28)
    «Sub/2» →
      let p29 = _pL#?x₀[0]
      let p30 = _pL#?x₀[1]
      let u31 = ()
      let pair32 = ⟨p29, u31⟩
      let ρ1007 = ⟨pair32, Γ⟩
      letκ k13 v12 =
        let u34 = ()
        let pair35 = ⟨p30, u34⟩
        let ρ1006 = ⟨pair35, Γ⟩
        letκ k15 v14 =
          let p37 = SUB(v12, v14)
          APPLY k(p37)
        eval(ρ1006, k15)
      eval(ρ1007, k13)
}

main (payload, k) {
  let Γ = 𝐄⟦⟧
  let c38 = 20
  let con39 = Atom⟦c38⟧
  let c40 = 10
  let con41 = Atom⟦c40⟧
  let c42 = 20
  let con43 = Atom⟦c42⟧
  let con44 = Mul⟦con41, con43⟧
  let c45 = 2400
  let con46 = Atom⟦c45⟧
  let c47 = 120
  let con48 = Atom⟦c47⟧
  let c49 = 10
  let con50 = Atom⟦c49⟧
  let c51 = 20
  let con52 = Atom⟦c51⟧
  let con53 = Mul⟦con50, con52⟧
  let c54 = 0
  let con55 = Atom⟦c54⟧
  let con56 = Add⟦con53, con55⟧
  let con57 = Add⟦con48, con56⟧
  let con58 = Div⟦con46, con57⟧
  let con59 = Sub⟦con44, con58⟧
  let con60 = Mul⟦con39, con59⟧
  let u61 = ()
  let pair62 = ⟨con60, u61⟩
  let ρc1010 = ⟨pair62, Γ⟩
  letκ k17 v16 =
    let c64 = 3860
    let cmp65 = EQⁱ(v16, c64)
    if cmp65 then APPLY k(con60) else MATCHFAILURE
  eval(ρc1010, k17)
}
;; == Runtime ==
(load "runtime.lisp")

;; == Linked Lisp Source ==
(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |eval| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α| (car |payload|)))
    (let ((|Γ| (cdr |payload|)))
      (let ((|_pL#?x₀| (car |α|)))
        (cond
          ((eq (car |_pL#?x₀|) '|Add|)
            (let ((|p1| (svref (cdr |_pL#?x₀|) 0)))
              (let ((|p2| (svref (cdr |_pL#?x₀|) 1)))
                (let ((|u3| nil))
                  (let ((|pair4| (cons |p1| |u3|)))
                    (let ((|ρ1001| (cons |pair4| |Γ|)))
                      (labels ((|k1| (|v0|)
                        (let ((|u6| nil))
                          (let ((|pair7| (cons |p2| |u6|)))
                            (let ((|ρ1000| (cons |pair7| |Γ|)))
                              (labels ((|k3| (|v2|)
                                (let ((|p9| (%int+ |v0| |v2|)))
                                  (funcall (the function |k|) |p9|))))
                                (funcall #'|eval| |ρ1000| #'|k3|)))))))
                        (funcall #'|eval| |ρ1001| #'|k1|))))))))
          ((eq (car |_pL#?x₀|) '|Div|)
            (let ((|p10| (svref (cdr |_pL#?x₀|) 0)))
              (let ((|p11| (svref (cdr |_pL#?x₀|) 1)))
                (let ((|u12| nil))
                  (let ((|pair13| (cons |p10| |u12|)))
                    (let ((|ρ1003| (cons |pair13| |Γ|)))
                      (labels ((|k5| (|v4|)
                        (let ((|u15| nil))
                          (let ((|pair16| (cons |p11| |u15|)))
                            (let ((|ρ1002| (cons |pair16| |Γ|)))
                              (labels ((|k7| (|v6|)
                                (let ((|p18| (%int/ |v4| |v6|)))
                                  (funcall (the function |k|) |p18|))))
                                (funcall #'|eval| |ρ1002| #'|k7|)))))))
                        (funcall #'|eval| |ρ1003| #'|k5|))))))))
          ((eq (car |_pL#?x₀|) '|Mul|)
            (let ((|p19| (svref (cdr |_pL#?x₀|) 0)))
              (let ((|p20| (svref (cdr |_pL#?x₀|) 1)))
                (let ((|u21| nil))
                  (let ((|pair22| (cons |p19| |u21|)))
                    (let ((|ρ1005| (cons |pair22| |Γ|)))
                      (labels ((|k9| (|v8|)
                        (let ((|u24| nil))
                          (let ((|pair25| (cons |p20| |u24|)))
                            (let ((|ρ1004| (cons |pair25| |Γ|)))
                              (labels ((|k11| (|v10|)
                                (let ((|p27| (%int* |v8| |v10|)))
                                  (funcall (the function |k|) |p27|))))
                                (funcall #'|eval| |ρ1004| #'|k11|)))))))
                        (funcall #'|eval| |ρ1005| #'|k9|))))))))
          ((eq (car |_pL#?x₀|) '|Atom|)
            (let ((|p28| (svref (cdr |_pL#?x₀|) 0)))
              (funcall (the function |k|) |p28|)))
          ((eq (car |_pL#?x₀|) '|Sub|)
            (let ((|p29| (svref (cdr |_pL#?x₀|) 0)))
              (let ((|p30| (svref (cdr |_pL#?x₀|) 1)))
                (let ((|u31| nil))
                  (let ((|pair32| (cons |p29| |u31|)))
                    (let ((|ρ1007| (cons |pair32| |Γ|)))
                      (labels ((|k13| (|v12|)
                        (let ((|u34| nil))
                          (let ((|pair35| (cons |p30| |u34|)))
                            (let ((|ρ1006| (cons |pair35| |Γ|)))
                              (labels ((|k15| (|v14|)
                                (let ((|p37| (%int- |v12| |v14|)))
                                  (funcall (the function |k|) |p37|))))
                                (funcall #'|eval| |ρ1006| #'|k15|)))))))
                        (funcall #'|eval| |ρ1007| #'|k13|)))))))))))))

; entrypoint
(defun |main| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|Γ| (cons '|𝐄| (vector))))
    (let ((|c38| 20))
      (let ((|con39| (cons '|Atom| (vector |c38|))))
        (let ((|c40| 10))
          (let ((|con41| (cons '|Atom| (vector |c40|))))
            (let ((|c42| 20))
              (let ((|con43| (cons '|Atom| (vector |c42|))))
                (let ((|con44| (cons '|Mul| (vector |con41| |con43|))))
                  (let ((|c45| 2400))
                    (let ((|con46| (cons '|Atom| (vector |c45|))))
                      (let ((|c47| 120))
                        (let ((|con48| (cons '|Atom| (vector |c47|))))
                          (let ((|c49| 10))
                            (let ((|con50| (cons '|Atom| (vector |c49|))))
                              (let ((|c51| 20))
                                (let ((|con52| (cons '|Atom| (vector |c51|))))
                                  (let ((|con53| (cons '|Mul| (vector |con50| |con52|))))
                                    (let ((|c54| 0))
                                      (let ((|con55| (cons '|Atom| (vector |c54|))))
                                        (let ((|con56| (cons '|Add| (vector |con53| |con55|))))
                                          (let ((|con57| (cons '|Add| (vector |con48| |con56|))))
                                            (let ((|con58| (cons '|Div| (vector |con46| |con57|))))
                                              (let ((|con59| (cons '|Sub| (vector |con44| |con58|))))
                                                (let ((|con60| (cons '|Mul| (vector |con39| |con59|))))
                                                  (let ((|u61| nil))
                                                    (let ((|pair62| (cons |con60| |u61|)))
                                                      (let ((|ρc1010| (cons |pair62| |Γ|)))
                                                        (labels ((|k17| (|v16|)
                                                          (let ((|c64| 3860))
                                                            (let ((|cmp65| (%int= |v16| |c64|)))
                                                              (if |cmp65|
                                                                (funcall (the function |k|) |con60|)
                                                                (error +NOMATCH+ :discr "#[Toplevel]"))))))
                                                          (funcall #'|eval| |ρc1010| #'|k17|))))))))))))))))))))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

