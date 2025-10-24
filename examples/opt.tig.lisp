;; == external FFI ==

(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |fn1000| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|_pL#?x₀| (car |α|)))
      (cond
        ((eq (car |_pL#?x₀|) '|Some|)
          (let ((|p2| (svref (cdr |_pL#?x₀|) 0)))
            (funcall |k| |p2|)))
        (t
          (let ((|u1| nil))
            (funcall |k| |u1|)))))))

(defun |fn1001| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|_pL#f| (car |α|)))
      (let ((|_pR#f| (cdr |α|)))
        (cond
          ((eq (car |_pR#f|) '|None|)
            (let ((|con6| (cons '|None| (vector))))
              (funcall |k| |con6|)))
          ((eq (car |_pR#f|) '|Some|)
            (let ((|p7| (svref (cdr |_pR#f|) 0)))
              (let ((|u8| nil))
                (let ((|pair9| (cons |p7| |u8|)))
                  (let ((|_code1002| (svref (cdr |_pL#f|) 0)))
                    (let ((|Γc1003| (svref (cdr |_pL#f|) 1)))
                      (let ((|ρc1004| (cons |pair9| |Γc1003|)))
                        (labels ((|k1| (|v0|)
                          (let ((|con11| (cons '|Some| (vector |v0|))))
                            (funcall |k| |con11|))))
                          (funcall |_code1002| |ρc1004| #'|k1|))))))))))))))

(defun |fn1005| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|_pL#?x₀| (car |α|)))
      (let ((|c19| 1))
        (let ((|p20| (sb-kernel:two-arg-+ |c19| |_pL#?x₀|)))
          (funcall |k| |p20|))))))

; entrypoint
(defun |main| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|Γ| (cons '|𝐄| (vector))))
    (let ((|c13| 20))
      (let ((|con14| (cons '|Some| (vector |c13|))))
        (let ((|u15| nil))
          (let ((|pair16| (cons |con14| |u15|)))
            (let ((|ρc1011| (cons |pair16| |Γ|)))
              (labels ((|k3| (|v2|)
                (let ((|Γ| (cons '|𝐄| (vector))))
                  (let ((|lam21| (cons '|𝐂| (vector #'|fn1005| |Γ|))))
                    (let ((|pair22| (cons |lam21| |con14|)))
                      (let ((|ρc1008| (cons |pair22| |Γ|)))
                        (labels ((|k5| (|v4|)
                          (let ((|p24| (cons |v2| |v4|)))
                            (funcall |k| |p24|))))
                          (funcall #'|fn1001| |ρc1008| #'|k5|))))))))
                (funcall #'|fn1000| |ρc1011| #'|k3|)))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

