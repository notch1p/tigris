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
                (let ((|Γ| (svref (cdr |_pL#f|) 1)))
                  (let ((|ρ| (cons |p6| |Γ|)))
                    (labels ((|k1| (|v0|)
                      (let ((|con8| (cons '|Some| (vector |v0|))))
                        (funcall |k| |con8|))))
                      (funcall |_code| |ρ| #'|k1|))))))))))))

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
        (let ((|ρ1004| (cons |con11| |Γ|)))
          (labels ((|k3| (|v2|)
            (let ((|Γ| (cons '|𝐄| (vector))))
              (let ((|lam15| (cons '|𝐂| (vector #'|fn1005| |Γ|))))
                (let ((|pair16| (cons |lam15| |con11|)))
                  (let ((|ρ1008| (cons |pair16| |Γ|)))
                    (labels ((|k5| (|v4|)
                      (let ((|p18| (cons |v2| |v4|)))
                        (funcall |k| |p18|))))
                      (funcall #'|fn1001| |ρ1008| #'|k5|))))))))
            (funcall #'|fn1000| |ρ1004| #'|k3|)))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

