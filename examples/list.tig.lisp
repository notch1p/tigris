;; == external FFI ==

(load "../ffi.lisp")

;; == Optimized IR ==

main (arg) {
  letω 
    label map(args0):
      let _pL#f = args0[0]
      let _pR#f = args0[1]
      case _pR#f of
        «Nil/0» →
          let con2 = Nil⟦⟧
          RET con2
        «Cons/2» →
          let p3 = _pR#f[0]
          let p4 = _pR#f[1]
          let call5 = _pL#f(p3)
          let pair6 = ⟨_pL#f, p4⟩
          let r7 = map(pair6)
          let con8 = Cons⟦call5, r7⟧
          RET con8
  in
  letω 
    label foldl(args9):
      let _pL#f = args9[0]
      let _pR#f = args9[1]
      let _pL#init = _pR#f[0]
      let _pR#init = _pR#f[1]
      case _pR#init of
        «Nil/0» →
          RET _pL#init
        «Cons/2» →
          let p11 = _pR#init[0]
          let p12 = _pR#init[1]
          let pair13 = ⟨_pL#init, p11⟩
          let r14 = _pL#f(pair13)
          let pair16 = ⟨r14, p12⟩
          let pair15 = ⟨_pL#f, pair16⟩
          foldl(pair15)ᵀ
  in
  letι lam20 =
    fun __?x₀ ↦
      case __?x₀ of
        «Cons/2» →
          let p19 = __?x₀[0]
          RET p19
        ∅ →
          letι u18 = ()
          RET u18
  letι c24 = 1
  letι c25 = 2
  letι c26 = 3
  letι c27 = 4
  let con28 = Nil⟦⟧
  let con29 = Cons⟦c27, con28⟧
  let con30 = Cons⟦c26, con29⟧
  let con31 = Cons⟦c25, con30⟧
  let con32 = Cons⟦c24, con31⟧
  letι lam35 =
    fun __?x₀ ↦
      letι c33 = 1
      let p34 = ADD(c33, __?x₀)
      RET p34
  let pair36 = ⟨lam35, con32⟩
  let r37 = map(pair36)
  letι lam40 =
    fun args38 ↦
      let _pL#__?x₀ = args38[0]
      let _pR#__?x₀ = args38[1]
      let p39 = ADD(_pL#__?x₀, _pR#__?x₀)
      RET p39
  letι c41 = 0
  let pair43 = ⟨c41, con32⟩
  let pair42 = ⟨lam40, pair43⟩
  let r44 = foldl(pair42)
  letι lam47 =
    fun args45 ↦
      let _pL#__?x₀ = args45[0]
      let _pR#__?x₀ = args45[1]
      let p46 = ADD(_pL#__?x₀, _pR#__?x₀)
      RET p46
  letι c48 = 0
  let pair50 = ⟨c48, r37⟩
  let pair49 = ⟨lam47, pair50⟩
  let r51 = foldl(pair49)
  let call52 = lam20(r37)
  let p53 = ⟨r51, call52⟩
  let p54 = ⟨r44, p53⟩
  let p55 = ⟨r37, p54⟩
  RET p55
}
;; == Optimized IR CC'd ==

map (payload) {
  let α = payload[0]
  let Γ = payload[1]
  let _pL#f = α[0]
  let _pR#f = α[1]
  case _pR#f of
    «Nil/0» →
      let con2 = Nil⟦⟧
      RET con2
    «Cons/2» →
      let p3 = _pR#f[0]
      let p4 = _pR#f[1]
      let _code = _pL#f[0]
      let Γc = _pL#f[1]
      let ρc = ⟨p3, Γc⟩
      let call5 = _code(ρc)
      let pair6 = ⟨_pL#f, p4⟩
      let ρ = ⟨pair6, Γ⟩
      let r7 = map(ρ)
      let con8 = Cons⟦call5, r7⟧
      RET con8
}

foldl (payload) {
  let α = payload[0]
  let Γ = payload[1]
  let _pL#f = α[0]
  let _pR#f = α[1]
  let _pL#init = _pR#f[0]
  let _pR#init = _pR#f[1]
  case _pR#init of
    «Nil/0» →
      RET _pL#init
    «Cons/2» →
      let p11 = _pR#init[0]
      let p12 = _pR#init[1]
      let pair13 = ⟨_pL#init, p11⟩
      let _code = _pL#f[0]
      let Γc = _pL#f[1]
      let ρc = ⟨pair13, Γc⟩
      let r14 = _code(ρc)
      let pair16 = ⟨r14, p12⟩
      let pair15 = ⟨_pL#f, pair16⟩
      ρ := ⟨pair15, Γ⟩
      foldl(ρ)ᵀ
}

fn1000 (payload) {
  let α = payload[0]
  case α of
    «Cons/2» →
      let p19 = α[0]
      RET p19
    ∅ →
      letι u18 = ()
      RET u18
}

fn1001 (payload) {
  let α = payload[0]
  letι c33 = 1
  let p34 = ADD(c33, α)
  RET p34
}

fn1005 (payload) {
  let α = payload[0]
  let _pL#__?x₀ = α[0]
  let _pR#__?x₀ = α[1]
  let p39 = ADD(_pL#__?x₀, _pR#__?x₀)
  RET p39
}

fn1009 (payload) {
  let α = payload[0]
  let _pL#__?x₀ = α[0]
  let _pR#__?x₀ = α[1]
  let p46 = ADD(_pL#__?x₀, _pR#__?x₀)
  RET p46
}

main (arg) {
  let Γ = 𝐄⟦⟧
  let map = 𝐂⟦map, Γ⟧
  let Γ = 𝐄⟦⟧
  let foldl = 𝐂⟦foldl, Γ⟧
  letι c24 = 1
  letι c25 = 2
  letι c26 = 3
  letι c27 = 4
  let con28 = Nil⟦⟧
  let con29 = Cons⟦c27, con28⟧
  let con30 = Cons⟦c26, con29⟧
  let con31 = Cons⟦c25, con30⟧
  let con32 = Cons⟦c24, con31⟧
  let Γ = 𝐄⟦⟧
  let lam35 = 𝐂⟦fn1001, Γ⟧
  let pair36 = ⟨lam35, con32⟩
  let ρc1004 = ⟨pair36, Γ⟩
  let r37 = map(ρc1004)
  let Γ = 𝐄⟦⟧
  let lam40 = 𝐂⟦fn1005, Γ⟧
  letι c41 = 0
  let pair43 = ⟨c41, con32⟩
  let pair42 = ⟨lam40, pair43⟩
  let ρc1008 = ⟨pair42, Γ⟩
  let r44 = foldl(ρc1008)
  let Γ = 𝐄⟦⟧
  let lam47 = 𝐂⟦fn1009, Γ⟧
  letι c48 = 0
  let pair50 = ⟨c48, r37⟩
  let pair49 = ⟨lam47, pair50⟩
  let ρc1012 = ⟨pair49, Γ⟩
  let r51 = foldl(ρc1012)
  let ρc1015 = ⟨r37, Γ⟩
  let call52 = fn1000(ρc1015)
  let p53 = ⟨r51, call52⟩
  let p54 = ⟨r44, p53⟩
  let p55 = ⟨r37, p54⟩
  RET p55
}
;; == CPS IR ==

map (payload, k) {
  let α = payload[0]
  let Γ = payload[1]
  let _pL#f = α[0]
  let _pR#f = α[1]
  case _pR#f of
    «Nil/0» →
      let con2 = Nil⟦⟧
      APPLY k(con2)
    «Cons/2» →
      let p3 = _pR#f[0]
      let p4 = _pR#f[1]
      let _code = _pL#f[0]
      let Γc = _pL#f[1]
      let ρc = ⟨p3, Γc⟩
      letκ k1 v0 =
        let pair6 = ⟨_pL#f, p4⟩
        let ρ = ⟨pair6, Γ⟩
        letκ k3 v2 =
          let con8 = Cons⟦v0, v2⟧
          APPLY k(con8)
        map(ρ, k3)
      _code(ρc, k1)
}

foldl (payload, k) {
  let α = payload[0]
  let Γ = payload[1]
  let _pL#f = α[0]
  let _pR#f = α[1]
  let _pL#init = _pR#f[0]
  let _pR#init = _pR#f[1]
  case _pR#init of
    «Nil/0» →
      APPLY k(_pL#init)
    «Cons/2» →
      let p11 = _pR#init[0]
      let p12 = _pR#init[1]
      let pair13 = ⟨_pL#init, p11⟩
      let _code = _pL#f[0]
      let Γc = _pL#f[1]
      let ρc = ⟨pair13, Γc⟩
      letκ k5 v4 =
        let pair16 = ⟨v4, p12⟩
        let pair15 = ⟨_pL#f, pair16⟩
        let ρ = ⟨pair15, Γ⟩
        foldl(ρ, k)
      _code(ρc, k5)
}

fn1000 (payload, k) {
  let α = payload[0]
  case α of
    «Cons/2» →
      let p19 = α[0]
      APPLY k(p19)
    ∅ →
      let u18 = ()
      APPLY k(u18)
}

fn1001 (payload, k) {
  let α = payload[0]
  let c33 = 1
  let p34 = ADD(c33, α)
  APPLY k(p34)
}

fn1005 (payload, k) {
  let α = payload[0]
  let _pL#__?x₀ = α[0]
  let _pR#__?x₀ = α[1]
  let p39 = ADD(_pL#__?x₀, _pR#__?x₀)
  APPLY k(p39)
}

fn1009 (payload, k) {
  let α = payload[0]
  let _pL#__?x₀ = α[0]
  let _pR#__?x₀ = α[1]
  let p46 = ADD(_pL#__?x₀, _pR#__?x₀)
  APPLY k(p46)
}

main (arg, k) {
  let Γ = 𝐄⟦⟧
  let map = 𝐂⟦map, Γ⟧
  let Γ = 𝐄⟦⟧
  let foldl = 𝐂⟦foldl, Γ⟧
  let c24 = 1
  let c25 = 2
  let c26 = 3
  let c27 = 4
  let con28 = Nil⟦⟧
  let con29 = Cons⟦c27, con28⟧
  let con30 = Cons⟦c26, con29⟧
  let con31 = Cons⟦c25, con30⟧
  let con32 = Cons⟦c24, con31⟧
  let Γ = 𝐄⟦⟧
  let lam35 = 𝐂⟦fn1001, Γ⟧
  let pair36 = ⟨lam35, con32⟩
  let ρc1004 = ⟨pair36, Γ⟩
  letκ k7 v6 =
    let Γ = 𝐄⟦⟧
    let lam40 = 𝐂⟦fn1005, Γ⟧
    let c41 = 0
    let pair43 = ⟨c41, con32⟩
    let pair42 = ⟨lam40, pair43⟩
    let ρc1008 = ⟨pair42, Γ⟩
    letκ k9 v8 =
      let Γ = 𝐄⟦⟧
      let lam47 = 𝐂⟦fn1009, Γ⟧
      let c48 = 0
      let pair50 = ⟨c48, v6⟩
      let pair49 = ⟨lam47, pair50⟩
      let ρc1012 = ⟨pair49, Γ⟩
      letκ k11 v10 =
        let ρc1015 = ⟨v6, Γ⟩
        letκ k13 v12 =
          let p53 = ⟨v10, v12⟩
          let p54 = ⟨v8, p53⟩
          let p55 = ⟨v6, p54⟩
          APPLY k(p55)
        fn1000(ρc1015, k13)
      foldl(ρc1012, k11)
    foldl(ρc1008, k9)
  map(ρc1004, k7)
}
;; == Common Lisp ==

; hoisted functions

(defun |map| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|Γ| (cdr |payload|)))
      (let ((|_pL#f| (car |α|)))
        (let ((|_pR#f| (cdr |α|)))
          (cond
            ((eq (car |_pR#f|) '|Nil|)
              (let ((|con2| (cons '|Nil| (vector))))
                (funcall |k| |con2|)))
            ((eq (car |_pR#f|) '|Cons|)
              (let ((|p3| (svref (cdr |_pR#f|) 0)))
                (let ((|p4| (svref (cdr |_pR#f|) 1)))
                  (let ((|_code| (svref (cdr |_pL#f|) 0)))
                    (let ((|Γc| (svref (cdr |_pL#f|) 1)))
                      (let ((|ρc| (cons |p3| |Γc|)))
                        (labels ((|k1| (|v0|)
                          (let ((|pair6| (cons |_pL#f| |p4|)))
                            (let ((|ρ| (cons |pair6| |Γ|)))
                              (labels ((|k3| (|v2|)
                                (let ((|con8| (cons '|Cons| (vector |v0| |v2|))))
                                  (funcall |k| |con8|))))
                                (funcall #'|map| |ρ| #'|k3|))))))
                          (funcall |_code| |ρc| #'|k1|))))))))))))))

(defun |foldl| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|Γ| (cdr |payload|)))
      (let ((|_pL#f| (car |α|)))
        (let ((|_pR#f| (cdr |α|)))
          (let ((|_pL#init| (car |_pR#f|)))
            (let ((|_pR#init| (cdr |_pR#f|)))
              (cond
                ((eq (car |_pR#init|) '|Nil|)
                  (funcall |k| |_pL#init|))
                ((eq (car |_pR#init|) '|Cons|)
                  (let ((|p11| (svref (cdr |_pR#init|) 0)))
                    (let ((|p12| (svref (cdr |_pR#init|) 1)))
                      (let ((|pair13| (cons |_pL#init| |p11|)))
                        (let ((|_code| (svref (cdr |_pL#f|) 0)))
                          (let ((|Γc| (svref (cdr |_pL#f|) 1)))
                            (let ((|ρc| (cons |pair13| |Γc|)))
                              (labels ((|k5| (|v4|)
                                (let ((|pair16| (cons |v4| |p12|)))
                                  (let ((|pair15| (cons |_pL#f| |pair16|)))
                                    (let ((|ρ| (cons |pair15| |Γ|)))
                                      (funcall #'|foldl| |ρ| |k|))))))
                                (funcall |_code| |ρc| #'|k5|)))))))))))))))))

(defun |fn1000| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (cond
      ((eq (car |α|) '|Cons|)
        (let ((|p19| (svref (cdr |α|) 0)))
          (funcall |k| |p19|)))
      (t
        (let ((|u18| nil))
          (funcall |k| |u18|))))))

(defun |fn1001| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|c33| 1))
      (let ((|p34| (+ |c33| |α|)))
        (funcall |k| |p34|)))))

(defun |fn1005| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|_pL#__?x₀| (car |α|)))
      (let ((|_pR#__?x₀| (cdr |α|)))
        (let ((|p39| (+ |_pL#__?x₀| |_pR#__?x₀|)))
          (funcall |k| |p39|))))))

(defun |fn1009| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|_pL#__?x₀| (car |α|)))
      (let ((|_pR#__?x₀| (cdr |α|)))
        (let ((|p46| (+ |_pL#__?x₀| |_pR#__?x₀|)))
          (funcall |k| |p46|))))))

; entrypoint
(defun |main| (|arg| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|Γ| (cons '|𝐄| (vector))))
    (let ((|map| (cons '|𝐂| (vector #'|map| |Γ|))))
      (let ((|Γ| (cons '|𝐄| (vector))))
        (let ((|foldl| (cons '|𝐂| (vector #'|foldl| |Γ|))))
          (let ((|c24| 1))
            (let ((|c25| 2))
              (let ((|c26| 3))
                (let ((|c27| 4))
                  (let ((|con28| (cons '|Nil| (vector))))
                    (let ((|con29| (cons '|Cons| (vector |c27| |con28|))))
                      (let ((|con30| (cons '|Cons| (vector |c26| |con29|))))
                        (let ((|con31| (cons '|Cons| (vector |c25| |con30|))))
                          (let ((|con32| (cons '|Cons| (vector |c24| |con31|))))
                            (let ((|Γ| (cons '|𝐄| (vector))))
                              (let ((|lam35| (cons '|𝐂| (vector #'|fn1001| |Γ|))))
                                (let ((|pair36| (cons |lam35| |con32|)))
                                  (let ((|ρc1004| (cons |pair36| |Γ|)))
                                    (labels ((|k7| (|v6|)
                                      (let ((|Γ| (cons '|𝐄| (vector))))
                                        (let ((|lam40| (cons '|𝐂| (vector #'|fn1005| |Γ|))))
                                          (let ((|c41| 0))
                                            (let ((|pair43| (cons |c41| |con32|)))
                                              (let ((|pair42| (cons |lam40| |pair43|)))
                                                (let ((|ρc1008| (cons |pair42| |Γ|)))
                                                  (labels ((|k9| (|v8|)
                                                    (let ((|Γ| (cons '|𝐄| (vector))))
                                                      (let ((|lam47| (cons '|𝐂| (vector #'|fn1009| |Γ|))))
                                                        (let ((|c48| 0))
                                                          (let ((|pair50| (cons |c48| |v6|)))
                                                            (let ((|pair49| (cons |lam47| |pair50|)))
                                                              (let ((|ρc1012| (cons |pair49| |Γ|)))
                                                                (labels ((|k11| (|v10|)
                                                                  (let ((|ρc1015| (cons |v6| |Γ|)))
                                                                    (labels ((|k13| (|v12|)
                                                                      (let ((|p53| (cons |v10| |v12|)))
                                                                        (let ((|p54| (cons |v8| |p53|)))
                                                                          (let ((|p55| (cons |v6| |p54|)))
                                                                            (funcall |k| |p55|))))))
                                                                      (funcall #'|fn1000| |ρc1015| #'|k13|)))))
                                                                  (funcall #'|foldl| |ρc1012| #'|k11|))))))))))
                                                    (funcall #'|foldl| |ρc1008| #'|k9|))))))))))
                                      (funcall #'|map| |ρc1004| #'|k7|))))))))))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

