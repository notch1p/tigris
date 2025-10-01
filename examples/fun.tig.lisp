;; == external FFI ==

(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |fn1000| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|_pL#__?x₀| (car |α|)))
      (let ((|_pR#__?x₀| (cdr |α|)))
        (let ((|p1| (= |_pL#__?x₀| |_pR#__?x₀|)))
          (funcall |k| |p1|))))))

(defun |fn1001| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|_pL#__?x₀| (car |α|)))
      (let ((|_pR#__?x₀| (cdr |α|)))
        (let ((|_pL#η0| (car |_pR#__?x₀|)))
          (let ((|_pR#η0| (cdr |_pR#__?x₀|)))
            (cond
              ((eq (car |_pL#__?x₀|) '|Boxed|)
                (let ((|p6| (svref (cdr |_pL#__?x₀|) 0)))
                  (let ((|pair7| (cons |_pL#η0| |_pR#η0|)))
                    (let ((|_code| (svref (cdr |p6|) 0)))
                      (let ((|Γc| (svref (cdr |p6|) 1)))
                        (let ((|ρc| (cons |pair7| |Γc|)))
                          (funcall |_code| |ρc| |k|))))))))))))))

; entrypoint
(defun |main| (|arg| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|Γ| (cons '|𝐄| (vector))))
    (let ((|lam2| (cons '|𝐂| (vector #'|fn1000| |Γ|))))
      (let ((|con3| (cons '|Boxed| (vector |lam2|))))
        (let ((|Γ| (cons '|𝐄| (vector))))
          (let ((|lam9| (cons '|𝐂| (vector #'|fn1001| |Γ|))))
            (let ((|c10| 20))
              (let ((|c11| 20))
                (let ((|pair13| (cons |c10| |c11|)))
                  (let ((|pair12| (cons |con3| |pair13|)))
                    (let ((|_code| (svref (cdr |lam9|) 0)))
                      (let ((|Γc| (svref (cdr |lam9|) 1)))
                        (let ((|ρc| (cons |pair12| |Γc|)))
                          (funcall |_code| |ρc| |k|))))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

