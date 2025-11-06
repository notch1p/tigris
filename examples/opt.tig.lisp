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
      (cond
        ((eq (car |_pL#?x₀|) '|Some|)
          (let ((|p1| (svref (cdr |_pL#?x₀|) 0)))
            (funcall (the function |k|) |p1|)))
        (t
          (error +NOMATCH+ :discr "#[?x₀]"))))))

(defun |fn1001| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α| (car |payload|)))
    (let ((|_pL#f| (car |α|)))
      (let ((|_pR#f| (cdr |α|)))
        (cond
          ((eq (car |_pR#f|) '|None|)
            (let ((|con4| (cons '|None| (vector))))
              (funcall (the function |k|) |con4|)))
          ((eq (car |_pR#f|) '|Some|)
            (let ((|p5| (svref (cdr |_pR#f|) 0)))
              (let ((|u6| nil))
                (let ((|pair7| (cons |p5| |u6|)))
                  (let ((|_code1002| (svref (cdr |_pL#f|) 0)))
                    (let ((|Γc1003| (svref (cdr |_pL#f|) 1)))
                      (let ((|ρc1004| (cons |pair7| |Γc1003|)))
                        (labels ((|k1| (|v0|)
                          (let ((|con9| (cons '|Some| (vector |v0|))))
                            (funcall (the function |k|) |con9|))))
                          (funcall (the function |_code1002|) |ρc1004| #'|k1|))))))))))))))

(defun |fn1005| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α| (car |payload|)))
    (let ((|_pL#?x₀| (car |α|)))
      (let ((|c17| 1))
        (let ((|p18| (%int+ |c17| |_pL#?x₀|)))
          (funcall (the function |k|) |p18|))))))

; entrypoint
(defun |main| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|Γ| (cons '|𝐄| (vector))))
    (let ((|c11| 20))
      (let ((|con12| (cons '|Some| (vector |c11|))))
        (let ((|u13| nil))
          (let ((|pair14| (cons |con12| |u13|)))
            (let ((|ρc1011| (cons |pair14| |Γ|)))
              (labels ((|k3| (|v2|)
                (let ((|Γ| (cons '|𝐄| (vector))))
                  (let ((|lam19| (cons '|𝐂| (vector #'|fn1005| |Γ|))))
                    (let ((|pair20| (cons |lam19| |con12|)))
                      (let ((|ρc1008| (cons |pair20| |Γ|)))
                        (labels ((|k5| (|v4|)
                          (let ((|p22| (cons |v2| |v4|)))
                            (funcall (the function |k|) |p22|))))
                          (funcall #'|fn1001| |ρc1008| #'|k5|))))))))
                (funcall #'|fn1000| |ρc1011| #'|k3|)))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

