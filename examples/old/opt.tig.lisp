;; == Runtime ==
(load "runtime.lisp")

;; == Linked Lisp Source ==
(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |fn1003| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α1004| (car |payload|)))
  (let ((|_pL#?x₀| (car |α1004|)))
  (cond
    ((eq (car |_pL#?x₀|) '|Some|)
      (let ((|p1| (svref (cdr |_pL#?x₀|) 0)))
      (funcall (the function |k|) |p1|)))
    (t
      (error +NOMATCH+ :discr "#[?x₀]"))))))

(defun |fn1006| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α1007| (car |payload|)))
  (let ((|_pL#f| (car |α1007|)))
  (let ((|_pR#f| (cdr |α1007|)))
  (cond
    ((eq (car |_pR#f|) '|None|)
      (let ((|con4| (cons '|None| (vector))))
      (funcall (the function |k|) |con4|)))
    ((eq (car |_pR#f|) '|Some|)
      (let ((|p5| (svref (cdr |_pR#f|) 0)))
      (let ((|u6| nil))
      (let ((|pair7| (cons |p5| |u6|)))
      (let ((|_code1009| (svref (cdr |_pL#f|) 0)))
      (let ((|Γc1010| (svref (cdr |_pL#f|) 1)))
      (let ((|ρc1011| (cons |pair7| |Γc1010|)))
      (labels
        ((|k1| (|v0|)
          (let ((|con9| (cons '|Some| (vector |v0|))))
          (funcall (the function |k|) |con9|))))
        (funcall (the function |_code1009|) |ρc1011| #'|k1|))))))))))))))

(defun |fn1012| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α1013| (car |payload|)))
  (let ((|_pL#?x₀| (car |α1013|)))
  (let ((|c17| 1))
  (let ((|p18| (%int+ |c17| |_pL#?x₀|)))
  (funcall (the function |k|) |p18|))))))

; entrypoint
(defun |main| (|payload1000| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload1000|))
  (let ((|Γ1023| (cons '|𝐄| (vector))))
  (let ((|Γ1022| (cons '|𝐄| (vector))))
  (let ((|c11| 20))
  (let ((|con12| (cons '|Some| (vector |c11|))))
  (let ((|u13| nil))
  (let ((|pair14| (cons |con12| |u13|)))
  (let ((|ρc1021| (cons |pair14| |Γ1023|)))
  (labels
    ((|k3| (|v2|)
      (let ((|Γ1018| (cons '|𝐄| (vector))))
      (let ((|lam19| (cons '|𝐂| (vector #'|fn1012| |Γ1018|))))
      (let ((|pair20| (cons |lam19| |con12|)))
      (let ((|ρc1017| (cons |pair20| |Γ1022|)))
      (labels
        ((|k5| (|v4|)
          (let ((|p22| (cons |v2| |v4|)))
          (funcall (the function |k|) |p22|))))
        (funcall #'|fn1006| |ρc1017| #'|k5|))))))))
    (funcall #'|fn1003| |ρc1021| #'|k3|))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

