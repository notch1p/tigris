;; == external FFI ==

(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |fn1000| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|_pL#?x₀| (car |α|)))
      (let ((|_pR#?x₀| (cdr |α|)))
        (let ((|p1| (+ |_pL#?x₀| |_pR#?x₀|)))
          (funcall |k| |p1|))))))

(defun |fn1001| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|_pL#?x₀| (car |α|)))
      (let ((|_pR#?x₀| (cdr |α|)))
        (let ((|_pL#η0| (car |_pR#?x₀|)))
          (let ((|_pR#η0| (cdr |_pR#?x₀|)))
            (cond
              ((eq (car |_pL#?x₀|) '|Boxed|)
                (let ((|p6| (svref (cdr |_pL#?x₀|) 0)))
                  (let ((|pair7| (cons |_pL#η0| |_pR#η0|)))
                    (let ((|_code1002| (svref (cdr |p6|) 0)))
                      (let ((|Γc1003| (svref (cdr |p6|) 1)))
                        (let ((|ρc1004| (cons |pair7| |Γc1003|)))
                          (funcall |_code1002| |ρc1004| |k|))))))))))))))

; entrypoint
(defun |main| (|arg| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|Γ| (cons '|𝐄| (vector))))
    (let ((|lam2| (cons '|𝐂| (vector #'|fn1000| |Γ|))))
      (let ((|con3| (cons '|Boxed| (vector |lam2|))))
        (let ((|Γ| (cons '|𝐄| (vector))))
          (let ((|c12| 20))
            (let ((|c13| 20))
              (let ((|pair15| (cons |c12| |c13|)))
                (let ((|pair14| (cons |con3| |pair15|)))
                  (let ((|ρc1007| (cons |pair14| |Γ|)))
                    (labels ((|k1| (|v0|)
                      (let ((|c17| 30))
                        (let ((|c18| 30))
                          (let ((|pair19| (cons |c17| |c18|)))
                            (let ((|ρc1010| (cons |pair19| |Γ|)))
                              (labels ((|k3| (|v2|)
                                (let ((|p21| (cons |v0| |v2|)))
                                  (funcall |k| |p21|))))
                                (funcall #'|fn1000| |ρc1010| #'|k3|))))))))
                      (funcall #'|fn1001| |ρc1007| #'|k1|))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

