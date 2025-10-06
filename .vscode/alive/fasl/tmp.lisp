;; == external FFI ==

(load "ffi.lisp")

;; == Optimized IR ==

main (arg) {
  letι lam5 =
    fun args0 ↦
      let _pL#x = args0[0]
      let _pR#x = args0[1]
      let p1 = ⟨_pL#x, _pR#x⟩
      letι u2 = ()
      let pair3 = ⟨p1, u2⟩
      __eq(pair3)ᵀ
  letι lam12 =
    fun args7 ↦
      let _pL#x = args7[0]
      let _pR#x = args7[1]
      let pair10 = ⟨_pL#x, _pR#x⟩
      lam5(pair10)ᵀ
  RET lam12
}
;; == Common Lisp ==

; hoisted functions

(defun |fn1000| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|Γ| (cdr |payload|)))
      (let ((|__eq| (svref (cdr |Γ|) 0)))
        (let ((|_pL#x| (car |α|)))
          (let ((|_pR#x| (cdr |α|)))
            (let ((|p1| (cons |_pL#x| |_pR#x|)))
              (let ((|u2| nil))
                (let ((|pair3| (cons |p1| |u2|)))
                  (let ((|_code| (svref (cdr |__eq|) 0)))
                    (let ((|Γc| (svref (cdr |__eq|) 1)))
                      (let ((|ρc| (cons |pair3| |Γc|)))
                        (funcall |_code| |ρc| |k|)))))))))))))

(defun |fn1001| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|Γ| (cdr |payload|)))
      (let ((|lam5| (svref (cdr |Γ|) 0)))
        (let ((|_pL#x| (car |α|)))
          (let ((|_pR#x| (cdr |α|)))
            (let ((|pair10| (cons |_pL#x| |_pR#x|)))
              (let ((|_code| (svref (cdr |lam5|) 0)))
                (let ((|Γc| (svref (cdr |lam5|) 1)))
                  (let ((|ρc| (cons |pair10| |Γc|)))
                    (funcall |_code| |ρc| |k|)))))))))))

; entrypoint
(defun |main| (|arg| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|Γ| (cons '|𝐄| (vector |__eq|))))
    (let ((|lam5| (cons '|𝐂| (vector #'|fn1000| |Γ|))))
      (let ((|Γ| (cons '|𝐄| (vector |lam5|))))
        (let ((|lam12| (cons '|𝐂| (vector #'|fn1001| |Γ|))))
          (funcall |k| |lam12|))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

