;; == external FFI ==

(load "../ffi.lisp")

;; == Optimized IR ==

main (arg) {
  letι lam21 =
    fun n ↦
      letω 
        label go(args0):
          let _pL#acc = args0[0]
          let _pR#acc = args0[1]
          caseᶜ _pR#acc of
            0 →
              RET _pL#acc
            ∅ →
              let p2 = MUL(_pL#acc, _pR#acc)
              letι c3 = "fact "
              let call4 = %to-string(n)
              let pair5 = ⟨c3, call4⟩
              let r6 = %string-append(pair5)
              letι c7 = " = "
              let pair8 = ⟨r6, c7⟩
              let r9 = %string-append(pair8)
              let call10 = %to-string(p2)
              let pair11 = ⟨r9, call10⟩
              let r12 = %string-append(pair11)
              let call13 = %println(r12)
              letι c14 = 1
              let p15 = SUB(_pR#acc, c14)
              let pair16 = ⟨p2, p15⟩
              go(pair16)ᵀ
      in
      letι c18 = 1
      let pair19 = ⟨c18, n⟩
      go(pair19)ᵀ
  letι c22 = 5
  lam21(c22)ᵀ
}
;; == Optimized IR CC'd ==

go (payload) {
  let α = payload[0]
  let Γ = payload[1]
  let n = Γ[3]
  let %to-string = Γ[2]
  let %string-append = Γ[1]
  let %println = Γ[0]
  let _pL#acc = α[0]
  let _pR#acc = α[1]
  caseᶜ _pR#acc of
    0 →
      RET _pL#acc
    ∅ →
      let p2 = MUL(_pL#acc, _pR#acc)
      letι c3 = "fact "
      let _code = %to-string[0]
      let Γc = %to-string[1]
      let ρc = ⟨n, Γc⟩
      let call4 = _code(ρc)
      let pair5 = ⟨c3, call4⟩
      let _code = %string-append[0]
      let Γc = %string-append[1]
      let ρc = ⟨pair5, Γc⟩
      let r6 = _code(ρc)
      letι c7 = " = "
      let pair8 = ⟨r6, c7⟩
      let _code = %string-append[0]
      let Γc = %string-append[1]
      let ρc = ⟨pair8, Γc⟩
      let r9 = _code(ρc)
      let _code = %to-string[0]
      let Γc = %to-string[1]
      let ρc = ⟨p2, Γc⟩
      let call10 = _code(ρc)
      let pair11 = ⟨r9, call10⟩
      let _code = %string-append[0]
      let Γc = %string-append[1]
      let ρc = ⟨pair11, Γc⟩
      let r12 = _code(ρc)
      let _code = %println[0]
      let Γc = %println[1]
      let ρc = ⟨r12, Γc⟩
      let call13 = _code(ρc)
      letι c14 = 1
      let p15 = SUB(_pR#acc, c14)
      let pair16 = ⟨p2, p15⟩
      ρ := ⟨pair16, Γ⟩
      go(ρ)ᵀ
}

fn1000 (payload) {
  let α = payload[0]
  let Γ = payload[1]
  let go = Γ[3]
  let %to-string = Γ[2]
  let %string-append = Γ[1]
  let %println = Γ[0]
  let Γ = 𝐄⟦%println, %string-append, %to-string, α⟧
  let go = 𝐂⟦go, Γ⟧
  letι c18 = 1
  let pair19 = ⟨c18, α⟩
  _code := go[0]
  Γc := go[1]
  ρc := ⟨pair19, Γc⟩
  _code(ρc)ᵀ
}

main (arg) {
  let Γ = 𝐄⟦%println, %string-append, %to-string, go⟧
  let lam21 = 𝐂⟦fn1000, Γ⟧
  letι c22 = 5
  _code := lam21[0]
  Γc := lam21[1]
  ρc := ⟨c22, Γc⟩
  _code(ρc)ᵀ
}
;; == CPS IR ==

go (payload, k) {
  let α = payload[0]
  let Γ = payload[1]
  let n = Γ[3]
  let %to-string = Γ[2]
  let %string-append = Γ[1]
  let %println = Γ[0]
  let _pL#acc = α[0]
  let _pR#acc = α[1]
  caseᶜ _pR#acc of
    0 →
      APPLY k(_pL#acc)
    ∅ →
      let p2 = MUL(_pL#acc, _pR#acc)
      let c3 = "fact "
      let _code = %to-string[0]
      let Γc = %to-string[1]
      let ρc = ⟨n, Γc⟩
      letκ k1 v0 =
        let pair5 = ⟨c3, v0⟩
        let _code = %string-append[0]
        let Γc = %string-append[1]
        let ρc = ⟨pair5, Γc⟩
        letκ k3 v2 =
          let c7 = " = "
          let pair8 = ⟨v2, c7⟩
          let _code = %string-append[0]
          let Γc = %string-append[1]
          let ρc = ⟨pair8, Γc⟩
          letκ k5 v4 =
            let _code = %to-string[0]
            let Γc = %to-string[1]
            let ρc = ⟨p2, Γc⟩
            letκ k7 v6 =
              let pair11 = ⟨v4, v6⟩
              let _code = %string-append[0]
              let Γc = %string-append[1]
              let ρc = ⟨pair11, Γc⟩
              letκ k9 v8 =
                let _code = %println[0]
                let Γc = %println[1]
                let ρc = ⟨v8, Γc⟩
                letκ k11 v10 =
                  let c14 = 1
                  let p15 = SUB(_pR#acc, c14)
                  let pair16 = ⟨p2, p15⟩
                  let ρ = ⟨pair16, Γ⟩
                  go(ρ, k)
                _code(ρc, k11)
              _code(ρc, k9)
            _code(ρc, k7)
          _code(ρc, k5)
        _code(ρc, k3)
      _code(ρc, k1)
}

fn1000 (payload, k) {
  let α = payload[0]
  let Γ = payload[1]
  let go = Γ[3]
  let %to-string = Γ[2]
  let %string-append = Γ[1]
  let %println = Γ[0]
  let Γ = 𝐄⟦%println, %string-append, %to-string, α⟧
  let go = 𝐂⟦go, Γ⟧
  let c18 = 1
  let pair19 = ⟨c18, α⟩
  let _code = go[0]
  let Γc = go[1]
  let ρc = ⟨pair19, Γc⟩
  _code(ρc, k)
}

main (arg, k) {
  let Γ = 𝐄⟦%println, %string-append, %to-string, go⟧
  let lam21 = 𝐂⟦fn1000, Γ⟧
  let c22 = 5
  let _code = lam21[0]
  let Γc = lam21[1]
  let ρc = ⟨c22, Γc⟩
  _code(ρc, k)
}
;; == Common Lisp ==

; hoisted functions

(defun |go| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|Γ| (cdr |payload|)))
      (let ((|n| (svref (cdr |Γ|) 3)))
        (let ((|%to-string| (svref (cdr |Γ|) 2)))
          (let ((|%string-append| (svref (cdr |Γ|) 1)))
            (let ((|%println| (svref (cdr |Γ|) 0)))
              (let ((|_pL#acc| (car |α|)))
                (let ((|_pR#acc| (cdr |α|)))
                  (cond
                    ((equal |_pR#acc| 0)
                      (funcall |k| |_pL#acc|))
                    (t
                      (let ((|p2| (* |_pL#acc| |_pR#acc|)))
                        (let ((|c3| "fact "))
                          (let ((|_code| (svref (cdr |%to-string|) 0)))
                            (let ((|Γc| (svref (cdr |%to-string|) 1)))
                              (let ((|ρc| (cons |n| |Γc|)))
                                (labels ((|k1| (|v0|)
                                  (let ((|pair5| (cons |c3| |v0|)))
                                    (let ((|_code| (svref (cdr |%string-append|) 0)))
                                      (let ((|Γc| (svref (cdr |%string-append|) 1)))
                                        (let ((|ρc| (cons |pair5| |Γc|)))
                                          (labels ((|k3| (|v2|)
                                            (let ((|c7| " = "))
                                              (let ((|pair8| (cons |v2| |c7|)))
                                                (let ((|_code| (svref (cdr |%string-append|) 0)))
                                                  (let ((|Γc| (svref (cdr |%string-append|) 1)))
                                                    (let ((|ρc| (cons |pair8| |Γc|)))
                                                      (labels ((|k5| (|v4|)
                                                        (let ((|_code| (svref (cdr |%to-string|) 0)))
                                                          (let ((|Γc| (svref (cdr |%to-string|) 1)))
                                                            (let ((|ρc| (cons |p2| |Γc|)))
                                                              (labels ((|k7| (|v6|)
                                                                (let ((|pair11| (cons |v4| |v6|)))
                                                                  (let ((|_code| (svref (cdr |%string-append|) 0)))
                                                                    (let ((|Γc| (svref (cdr |%string-append|) 1)))
                                                                      (let ((|ρc| (cons |pair11| |Γc|)))
                                                                        (labels ((|k9| (|v8|)
                                                                          (let ((|_code| (svref (cdr |%println|) 0)))
                                                                            (let ((|Γc| (svref (cdr |%println|) 1)))
                                                                              (let ((|ρc| (cons |v8| |Γc|)))
                                                                                (labels ((|k11| (|v10|)
                                                                                  (let ((|c14| 1))
                                                                                    (let ((|p15| (- |_pR#acc| |c14|)))
                                                                                      (let ((|pair16| (cons |p2| |p15|)))
                                                                                        (let ((|ρ| (cons |pair16| |Γ|)))
                                                                                          (funcall #'|go| |ρ| |k|)))))))
                                                                                  (funcall |_code| |ρc| #'|k11|)))))))
                                                                          (funcall |_code| |ρc| #'|k9|))))))))
                                                                (funcall |_code| |ρc| #'|k7|)))))))
                                                        (funcall |_code| |ρc| #'|k5|)))))))))
                                            (funcall |_code| |ρc| #'|k3|))))))))
                                  (funcall |_code| |ρc| #'|k1|))))))))))))))))))

(defun |fn1000| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|Γ| (cdr |payload|)))
      (let ((|go| (svref (cdr |Γ|) 3)))
        (let ((|%to-string| (svref (cdr |Γ|) 2)))
          (let ((|%string-append| (svref (cdr |Γ|) 1)))
            (let ((|%println| (svref (cdr |Γ|) 0)))
              (let ((|Γ| (cons '|𝐄| (vector |%println| |%string-append| |%to-string| |α|))))
                (let ((|go| (cons '|𝐂| (vector #'|go| |Γ|))))
                  (let ((|c18| 1))
                    (let ((|pair19| (cons |c18| |α|)))
                      (let ((|_code| (svref (cdr |go|) 0)))
                        (let ((|Γc| (svref (cdr |go|) 1)))
                          (let ((|ρc| (cons |pair19| |Γc|)))
                            (funcall |_code| |ρc| |k|)))))))))))))))

; entrypoint
(defun |main| (|arg| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|Γ| (cons '|𝐄| (vector |%println| |%string-append| |%to-string| #'|go|))))
    (let ((|lam21| (cons '|𝐂| (vector #'|fn1000| |Γ|))))
      (let ((|c22| 5))
        (let ((|_code| (svref (cdr |lam21|) 0)))
          (let ((|Γc| (svref (cdr |lam21|) 1)))
            (let ((|ρc| (cons |c22| |Γc|)))
              (funcall |_code| |ρc| |k|))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

