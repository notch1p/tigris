;; == Optimized IR CC'd ==

fn1000 (payload) {
  let α = payload[0]
  let _pL#?x₀ = α[0]
  let p1 = _pL#?x₀[0]
  let p2 = _pL#?x₀[1]
  let p3 = ADD(p1, p2)
  RET p3
}

main (payload) {
  let Γ = 𝐄⟦⟧
  let lam4 = 𝐂⟦fn1000, Γ⟧
  letι c5 = 1
  letι c6 = 2
  let p7 = ⟨c5, c6⟩
  letι u8 = ()
  let pair9 = ⟨p7, u8⟩
  _code1001 := lam4[0];
  Γc1002 := lam4[1];
  ρc1003 := ⟨pair9, Γc1002⟩;
  _code1001(ρc1003)ᵀ
}
;; == Runtime ==
(load "runtime.lisp")

;; == Linked Lisp Source ==
(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |fn1000| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α| (car |payload|)))
    (let ((|_pL#?x₀| (car |α|)))
      (let ((|p1| (svref (cdr |_pL#?x₀|) 0)))
        (let ((|p2| (svref (cdr |_pL#?x₀|) 1)))
          (let ((|p3| (%int+ |p1| |p2|)))
            (funcall (the function |k|) |p3|)))))))

; entrypoint
(defun |main| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|Γ| (cons '|𝐄| (vector))))
    (let ((|lam4| (cons '|𝐂| (vector #'|fn1000| |Γ|))))
      (let ((|c5| 1))
        (let ((|c6| 2))
          (let ((|p7| (cons |c5| |c6|)))
            (let ((|u8| nil))
              (let ((|pair9| (cons |p7| |u8|)))
                (let ((|_code1001| (svref (cdr |lam4|) 0)))
                  (let ((|Γc1002| (svref (cdr |lam4|) 1)))
                    (let ((|ρc1003| (cons |pair9| |Γc1002|)))
                      (funcall (the function |_code1001|) |ρc1003| |k|))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

