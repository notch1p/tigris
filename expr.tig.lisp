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

let 3850 =
  eval prog
;; == Optimized IR ==

main (arg) {
  letω 
    label eval(args0):
      let _pL#?x₀ = args0[0]
      case _pL#?x₀ of
        «Add/2» →
          let p2 = _pL#?x₀[0]
          let p3 = _pL#?x₀[1]
          letι u4 = ()
          let pair5 = ⟨p2, u4⟩
          let call6 = eval(pair5)
          letι u7 = ()
          let pair8 = ⟨p3, u7⟩
          let call9 = eval(pair8)
          let p10 = ADD(call6, call9)
          RET p10
        «Div/2» →
          let p11 = _pL#?x₀[0]
          let p12 = _pL#?x₀[1]
          letι u13 = ()
          let pair14 = ⟨p11, u13⟩
          let call15 = eval(pair14)
          letι u16 = ()
          let pair17 = ⟨p12, u16⟩
          let call18 = eval(pair17)
          let p19 = DIV(call15, call18)
          RET p19
        «Mul/2» →
          let p20 = _pL#?x₀[0]
          let p21 = _pL#?x₀[1]
          letι u22 = ()
          let pair23 = ⟨p20, u22⟩
          let call24 = eval(pair23)
          letι u25 = ()
          let pair26 = ⟨p21, u25⟩
          let call27 = eval(pair26)
          let p28 = MUL(call24, call27)
          RET p28
        «Atom/1» →
          let p29 = _pL#?x₀[0]
          RET p29
        «Sub/2» →
          let p30 = _pL#?x₀[0]
          let p31 = _pL#?x₀[1]
          letι u32 = ()
          let pair33 = ⟨p30, u32⟩
          let call34 = eval(pair33)
          letι u35 = ()
          let pair36 = ⟨p31, u35⟩
          let call37 = eval(pair36)
          let p38 = SUB(call34, call37)
          RET p38
  in
  letι c39 = 20
  let con40 = Atom⟦c39⟧
  letι c41 = 10
  let con42 = Atom⟦c41⟧
  letι c43 = 20
  let con44 = Atom⟦c43⟧
  let con45 = Mul⟦con42, con44⟧
  letι c46 = 2400
  let con47 = Atom⟦c46⟧
  letι c48 = 120
  let con49 = Atom⟦c48⟧
  letι c50 = 10
  let con51 = Atom⟦c50⟧
  letι c52 = 20
  let con53 = Atom⟦c52⟧
  let con54 = Mul⟦con51, con53⟧
  letι c55 = 0
  let con56 = Atom⟦c55⟧
  let con57 = Add⟦con54, con56⟧
  let con58 = Add⟦con49, con57⟧
  let con59 = Div⟦con47, con58⟧
  let con60 = Sub⟦con45, con59⟧
  let con61 = Mul⟦con40, con60⟧
  letι u62 = ()
  let pair63 = ⟨con61, u62⟩
  let call64 = eval(pair63)
  letι c65 = 3850
  let cmp66 = EQⁱ(call64, c65)
  if cmp66 then
    RET con61
  else
    letι u67 = ()
    RET u67
}
;; == Optimized IR CC'd ==

eval (payload) {
  let α = payload[0]
  let Γ = payload[1]
  let _pL#?x₀ = α[0]
  case _pL#?x₀ of
    «Add/2» →
      let p2 = _pL#?x₀[0]
      let p3 = _pL#?x₀[1]
      letι u4 = ()
      let pair5 = ⟨p2, u4⟩
      let ρ1001 = ⟨pair5, Γ⟩
      let call6 = eval(ρ1001)
      letι u7 = ()
      let pair8 = ⟨p3, u7⟩
      let ρ1000 = ⟨pair8, Γ⟩
      let call9 = eval(ρ1000)
      let p10 = ADD(call6, call9)
      RET p10
    «Div/2» →
      let p11 = _pL#?x₀[0]
      let p12 = _pL#?x₀[1]
      letι u13 = ()
      let pair14 = ⟨p11, u13⟩
      let ρ1003 = ⟨pair14, Γ⟩
      let call15 = eval(ρ1003)
      letι u16 = ()
      let pair17 = ⟨p12, u16⟩
      let ρ1002 = ⟨pair17, Γ⟩
      let call18 = eval(ρ1002)
      let p19 = DIV(call15, call18)
      RET p19
    «Mul/2» →
      let p20 = _pL#?x₀[0]
      let p21 = _pL#?x₀[1]
      letι u22 = ()
      let pair23 = ⟨p20, u22⟩
      let ρ1005 = ⟨pair23, Γ⟩
      let call24 = eval(ρ1005)
      letι u25 = ()
      let pair26 = ⟨p21, u25⟩
      let ρ1004 = ⟨pair26, Γ⟩
      let call27 = eval(ρ1004)
      let p28 = MUL(call24, call27)
      RET p28
    «Atom/1» →
      let p29 = _pL#?x₀[0]
      RET p29
    «Sub/2» →
      let p30 = _pL#?x₀[0]
      let p31 = _pL#?x₀[1]
      letι u32 = ()
      let pair33 = ⟨p30, u32⟩
      let ρ1007 = ⟨pair33, Γ⟩
      let call34 = eval(ρ1007)
      letι u35 = ()
      let pair36 = ⟨p31, u35⟩
      let ρ1006 = ⟨pair36, Γ⟩
      let call37 = eval(ρ1006)
      let p38 = SUB(call34, call37)
      RET p38
}

main (payload) {
  let Γ = 𝐄⟦⟧
  let eval = 𝐂⟦eval, Γ⟧
  letι c39 = 20
  let con40 = Atom⟦c39⟧
  letι c41 = 10
  let con42 = Atom⟦c41⟧
  letι c43 = 20
  let con44 = Atom⟦c43⟧
  let con45 = Mul⟦con42, con44⟧
  letι c46 = 2400
  let con47 = Atom⟦c46⟧
  letι c48 = 120
  let con49 = Atom⟦c48⟧
  letι c50 = 10
  let con51 = Atom⟦c50⟧
  letι c52 = 20
  let con53 = Atom⟦c52⟧
  let con54 = Mul⟦con51, con53⟧
  letι c55 = 0
  let con56 = Atom⟦c55⟧
  let con57 = Add⟦con54, con56⟧
  let con58 = Add⟦con49, con57⟧
  let con59 = Div⟦con47, con58⟧
  let con60 = Sub⟦con45, con59⟧
  let con61 = Mul⟦con40, con60⟧
  letι u62 = ()
  let pair63 = ⟨con61, u62⟩
  let ρc1010 = ⟨pair63, Γ⟩
  let call64 = eval(ρc1010)
  letι c65 = 3850
  let cmp66 = EQⁱ(call64, c65)
  if cmp66 then
    RET con61
  else
    letι u67 = ()
    RET u67
}
;; == external FFI ==

(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |eval| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|Γ| (cdr |payload|)))
      (let ((|_pL#?x₀| (car |α|)))
        (cond
          ((eq (car |_pL#?x₀|) '|Add|)
            (let ((|p2| (svref (cdr |_pL#?x₀|) 0)))
              (let ((|p3| (svref (cdr |_pL#?x₀|) 1)))
                (let ((|u4| nil))
                  (let ((|pair5| (cons |p2| |u4|)))
                    (let ((|ρ1001| (cons |pair5| |Γ|)))
                      (labels ((|k1| (|v0|)
                        (let ((|u7| nil))
                          (let ((|pair8| (cons |p3| |u7|)))
                            (let ((|ρ1000| (cons |pair8| |Γ|)))
                              (labels ((|k3| (|v2|)
                                (let ((|p10| (sb-kernel:two-arg-+ |v0| |v2|)))
                                  (funcall |k| |p10|))))
                                (funcall #'|eval| |ρ1000| #'|k3|)))))))
                        (funcall #'|eval| |ρ1001| #'|k1|))))))))
          ((eq (car |_pL#?x₀|) '|Div|)
            (let ((|p11| (svref (cdr |_pL#?x₀|) 0)))
              (let ((|p12| (svref (cdr |_pL#?x₀|) 1)))
                (let ((|u13| nil))
                  (let ((|pair14| (cons |p11| |u13|)))
                    (let ((|ρ1003| (cons |pair14| |Γ|)))
                      (labels ((|k5| (|v4|)
                        (let ((|u16| nil))
                          (let ((|pair17| (cons |p12| |u16|)))
                            (let ((|ρ1002| (cons |pair17| |Γ|)))
                              (labels ((|k7| (|v6|)
                                (let ((|p19| (sb-kernel:two-arg-/ |v4| |v6|)))
                                  (funcall |k| |p19|))))
                                (funcall #'|eval| |ρ1002| #'|k7|)))))))
                        (funcall #'|eval| |ρ1003| #'|k5|))))))))
          ((eq (car |_pL#?x₀|) '|Mul|)
            (let ((|p20| (svref (cdr |_pL#?x₀|) 0)))
              (let ((|p21| (svref (cdr |_pL#?x₀|) 1)))
                (let ((|u22| nil))
                  (let ((|pair23| (cons |p20| |u22|)))
                    (let ((|ρ1005| (cons |pair23| |Γ|)))
                      (labels ((|k9| (|v8|)
                        (let ((|u25| nil))
                          (let ((|pair26| (cons |p21| |u25|)))
                            (let ((|ρ1004| (cons |pair26| |Γ|)))
                              (labels ((|k11| (|v10|)
                                (let ((|p28| (sb-kernel:two-arg-* |v8| |v10|)))
                                  (funcall |k| |p28|))))
                                (funcall #'|eval| |ρ1004| #'|k11|)))))))
                        (funcall #'|eval| |ρ1005| #'|k9|))))))))
          ((eq (car |_pL#?x₀|) '|Atom|)
            (let ((|p29| (svref (cdr |_pL#?x₀|) 0)))
              (funcall |k| |p29|)))
          ((eq (car |_pL#?x₀|) '|Sub|)
            (let ((|p30| (svref (cdr |_pL#?x₀|) 0)))
              (let ((|p31| (svref (cdr |_pL#?x₀|) 1)))
                (let ((|u32| nil))
                  (let ((|pair33| (cons |p30| |u32|)))
                    (let ((|ρ1007| (cons |pair33| |Γ|)))
                      (labels ((|k13| (|v12|)
                        (let ((|u35| nil))
                          (let ((|pair36| (cons |p31| |u35|)))
                            (let ((|ρ1006| (cons |pair36| |Γ|)))
                              (labels ((|k15| (|v14|)
                                (let ((|p38| (sb-kernel:two-arg-- |v12| |v14|)))
                                  (funcall |k| |p38|))))
                                (funcall #'|eval| |ρ1006| #'|k15|)))))))
                        (funcall #'|eval| |ρ1007| #'|k13|)))))))))))))

; entrypoint
(defun |main| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|Γ| (cons '|𝐄| (vector))))
    (let ((|eval| (cons '|𝐂| (vector #'|eval| |Γ|))))
      (let ((|c39| 20))
        (let ((|con40| (cons '|Atom| (vector |c39|))))
          (let ((|c41| 10))
            (let ((|con42| (cons '|Atom| (vector |c41|))))
              (let ((|c43| 20))
                (let ((|con44| (cons '|Atom| (vector |c43|))))
                  (let ((|con45| (cons '|Mul| (vector |con42| |con44|))))
                    (let ((|c46| 2400))
                      (let ((|con47| (cons '|Atom| (vector |c46|))))
                        (let ((|c48| 120))
                          (let ((|con49| (cons '|Atom| (vector |c48|))))
                            (let ((|c50| 10))
                              (let ((|con51| (cons '|Atom| (vector |c50|))))
                                (let ((|c52| 20))
                                  (let ((|con53| (cons '|Atom| (vector |c52|))))
                                    (let ((|con54| (cons '|Mul| (vector |con51| |con53|))))
                                      (let ((|c55| 0))
                                        (let ((|con56| (cons '|Atom| (vector |c55|))))
                                          (let ((|con57| (cons '|Add| (vector |con54| |con56|))))
                                            (let ((|con58| (cons '|Add| (vector |con49| |con57|))))
                                              (let ((|con59| (cons '|Div| (vector |con47| |con58|))))
                                                (let ((|con60| (cons '|Sub| (vector |con45| |con59|))))
                                                  (let ((|con61| (cons '|Mul| (vector |con40| |con60|))))
                                                    (let ((|u62| nil))
                                                      (let ((|pair63| (cons |con61| |u62|)))
                                                        (let ((|ρc1010| (cons |pair63| |Γ|)))
                                                          (labels ((|k17| (|v16|)
                                                            (let ((|c65| 3850))
                                                              (let ((|cmp66| (eql |v16| |c65|)))
                                                                (if |cmp66|
                                                                  (funcall |k| |con61|)
                                                                  (let ((|u67| nil))
                                                                    (funcall |k| |u67|)))))))
                                                            (funcall #'|eval| |ρc1010| #'|k17|)))))))))))))))))))))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

