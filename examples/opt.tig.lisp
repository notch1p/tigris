;; == external FFI ==

(load "../ffi.lisp")

;; == Optimized IR ==

main (arg) {
  letι lam2 =
    fun __?x₀ ↦
      case __?x₀ of
        «Some/1» →
          let p1 = __?x₀[0]
          RET p1
        ∅ →
          letι u0 = ()
          RET u0
  letι lam9 =
    fun args3 ↦
      let _pL#f = args3[0]
      let _pR#f = args3[1]
      case _pR#f of
        «None/0» →
          let con5 = None⟦⟧
          RET con5
        «Some/1» →
          let p6 = _pR#f[0]
          let call7 = _pL#f(p6)
          let con8 = Some⟦call7⟧
          RET con8
  letι c10 = 20
  let con11 = Some⟦c10⟧
  let call12 = lam2(con11)
  letι lam15 =
    fun __?x₀ ↦
      letι c13 = 1
      let p14 = ADD(c13, __?x₀)
      RET p14
  let pair16 = ⟨lam15, con11⟩
  let r17 = lam9(pair16)
  let p18 = ⟨call12, r17⟩
  RET p18
}
;; == Optimized IR CC'd ==

fn1000 (payload) {
  let α = payload[0]
  case α of
    «Some/1» →
      let p1 = α[0]
      RET p1
    ∅ →
      letι u0 = ()
      RET u0
}

fn1001 (payload) {
  let α = payload[0]
  let _pL#f = α[0]
  let _pR#f = α[1]
  case _pR#f of
    «None/0» →
      let con5 = None⟦⟧
      RET con5
    «Some/1» →
      let p6 = _pR#f[0]
      let _code = _pL#f[0]
      let Γc = _pL#f[1]
      let ρc = ⟨p6, Γc⟩
      let call7 = _code(ρc)
      let con8 = Some⟦call7⟧
      RET con8
}

fn1005 (payload) {
  let α = payload[0]
  letι c13 = 1
  let p14 = ADD(c13, α)
  RET p14
}

main (arg) {
  let Γ = 𝐄⟦⟧
  letι c10 = 20
  let con11 = Some⟦c10⟧
  let ρc1004 = ⟨con11, Γ⟩
  let call12 = fn1000(ρc1004)
  let Γ = 𝐄⟦⟧
  let lam15 = 𝐂⟦fn1005, Γ⟧
  let pair16 = ⟨lam15, con11⟩
  let ρc1008 = ⟨pair16, Γ⟩
  let r17 = fn1001(ρc1008)
  let p18 = ⟨call12, r17⟩
  RET p18
}
;; == CPS IR ==

fn1000 (payload, k) {
  let α = payload[0]
  case α of
    «Some/1» →
      let p1 = α[0]
      APPLY k(p1)
    ∅ →
      let u0 = ()
      APPLY k(u0)
}

fn1001 (payload, k) {
  let α = payload[0]
  let _pL#f = α[0]
  let _pR#f = α[1]
  case _pR#f of
    «None/0» →
      let con5 = None⟦⟧
      APPLY k(con5)
    «Some/1» →
      let p6 = _pR#f[0]
      let _code = _pL#f[0]
      let Γc = _pL#f[1]
      let ρc = ⟨p6, Γc⟩
      letκ k1 v0 =
        let con8 = Some⟦v0⟧
        APPLY k(con8)
      _code(ρc, k1)
}

fn1005 (payload, k) {
  let α = payload[0]
  let c13 = 1
  let p14 = ADD(c13, α)
  APPLY k(p14)
}

main (arg, k) {
  let Γ = 𝐄⟦⟧
  let c10 = 20
  let con11 = Some⟦c10⟧
  let ρc1004 = ⟨con11, Γ⟩
  letκ k3 v2 =
    let Γ = 𝐄⟦⟧
    let lam15 = 𝐂⟦fn1005, Γ⟧
    let pair16 = ⟨lam15, con11⟩
    let ρc1008 = ⟨pair16, Γ⟩
    letκ k5 v4 =
      let p18 = ⟨v2, v4⟩
      APPLY k(p18)
    fn1001(ρc1008, k5)
  fn1000(ρc1004, k3)
}
;; == Common Lisp ==

; hoisted functions

(defun |fn1000| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (cond
      ((eq (car |α|) '|Some|)
        (let ((|p1| (svref (cdr |α|) 0)))
          (funcall |k| |p1|)))
      (t
        (let ((|u0| nil))
          (funcall |k| |u0|))))))

(defun |fn1001| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|_pL#f| (car |α|)))
      (let ((|_pR#f| (cdr |α|)))
        (cond
          ((eq (car |_pR#f|) '|None|)
            (let ((|con5| (cons '|None| (vector))))
              (funcall |k| |con5|)))
          ((eq (car |_pR#f|) '|Some|)
            (let ((|p6| (svref (cdr |_pR#f|) 0)))
              (let ((|_code| (svref (cdr |_pL#f|) 0)))
                (let ((|Γc| (svref (cdr |_pL#f|) 1)))
                  (let ((|ρc| (cons |p6| |Γc|)))
                    (labels ((|k1| (|v0|)
                      (let ((|con8| (cons '|Some| (vector |v0|))))
                        (funcall |k| |con8|))))
                      (funcall |_code| |ρc| #'|k1|))))))))))))

(defun |fn1005| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|c13| 1))
      (let ((|p14| (+ |c13| |α|)))
        (funcall |k| |p14|)))))

; entrypoint
(defun |main| (|arg| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|Γ| (cons '|𝐄| (vector))))
    (let ((|c10| 20))
      (let ((|con11| (cons '|Some| (vector |c10|))))
        (let ((|ρc1004| (cons |con11| |Γ|)))
          (labels ((|k3| (|v2|)
            (let ((|Γ| (cons '|𝐄| (vector))))
              (let ((|lam15| (cons '|𝐂| (vector #'|fn1005| |Γ|))))
                (let ((|pair16| (cons |lam15| |con11|)))
                  (let ((|ρc1008| (cons |pair16| |Γ|)))
                    (labels ((|k5| (|v4|)
                      (let ((|p18| (cons |v2| |v4|)))
                        (funcall |k| |p18|))))
                      (funcall #'|fn1001| |ρc1008| #'|k5|))))))))
            (funcall #'|fn1000| |ρc1004| #'|k3|)))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

