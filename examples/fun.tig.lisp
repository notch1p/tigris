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
      (let ((|_pR#?x₀| (cdr |α|)))
        (let ((|p1| (%int+ |_pL#?x₀| |_pR#?x₀|)))
          (funcall (the function |k|) |p1|))))))

(defun |fn1001| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α| (car |payload|)))
    (let ((|_pL#?x₀| (car |α|)))
      (let ((|_pR#?x₀| (cdr |α|)))
        (let ((|_pL#η0| (car |_pR#?x₀|)))
          (let ((|_pR#η0| (cdr |_pR#?x₀|)))
            (cond
              ((eq (car |_pL#?x₀|) '|Boxed|)
                (let ((|p5| (svref (cdr |_pL#?x₀|) 0)))
                  (let ((|pair6| (cons |_pL#η0| |_pR#η0|)))
                    (let ((|_code1002| (svref (cdr |p5|) 0)))
                      (let ((|Γc1003| (svref (cdr |p5|) 1)))
                        (let ((|ρc1004| (cons |pair6| |Γc1003|)))
                          (funcall (the function |_code1002|) |ρc1004| |k|))))))))))))))

; entrypoint
(defun |main| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|Γ| (cons '|𝐄| (vector))))
    (let ((|lam2| (cons '|𝐂| (vector #'|fn1000| |Γ|))))
      (let ((|con3| (cons '|Boxed| (vector |lam2|))))
        (let ((|Γ| (cons '|𝐄| (vector))))
          (let ((|c11| 20))
            (let ((|c12| 20))
              (let ((|pair14| (cons |c11| |c12|)))
                (let ((|pair13| (cons |con3| |pair14|)))
                  (let ((|ρc1010| (cons |pair13| |Γ|)))
                    (labels ((|k1| (|v0|)
                      (let ((|c16| 30))
                        (let ((|c17| 30))
                          (let ((|pair18| (cons |c16| |c17|)))
                            (let ((|ρc1007| (cons |pair18| |Γ|)))
                              (labels ((|k3| (|v2|)
                                (let ((|p20| (cons |v0| |v2|)))
                                  (funcall (the function |k|) |p20|))))
                                (funcall #'|fn1000| |ρc1007| #'|k3|))))))))
                      (funcall #'|fn1001| |ρc1010| #'|k1|))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

