;; == Runtime ==
(load "runtime.lisp")

;; == Linked Lisp Source ==
(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |fn1003| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α1004| (car |payload|)))
  (let ((|_pL#f| (car |α1004|)))
  (let ((|_pR#f| (cdr |α1004|)))
  (cond
    ((eq (car |_pR#f|) '|Inl|)
      (let ((|p1| (svref (cdr |_pR#f|) 0)))
      (let ((|con2| (cons '|Inl| (vector |p1|))))
      (funcall (the function |k|) |con2|))))
    ((eq (car |_pR#f|) '|Inr|)
      (let ((|p3| (svref (cdr |_pR#f|) 0)))
      (let ((|u4| nil))
      (let ((|pair5| (cons |p3| |u4|)))
      (let ((|_code1006| (svref (cdr |_pL#f|) 0)))
      (let ((|Γc1007| (svref (cdr |_pL#f|) 1)))
      (let ((|ρc1008| (cons |pair5| |Γc1007|)))
      (labels
        ((|k1| (|v0|)
          (let ((|con7| (cons '|Inr| (vector |v0|))))
          (funcall (the function |k|) |con7|))))
        (funcall (the function |_code1006|) |ρc1008| #'|k1|))))))))))))))

(defun |fn1009| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α1010| (car |payload|)))
  (let ((|_pL#?x₀| (car |α1010|)))
  (let ((|c16| 2))
  (let ((|p17| (%int* |c16| |_pL#?x₀|)))
  (funcall (the function |k|) |p17|))))))

(defun |fn1012| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α1013| (car |payload|)))
  (let ((|_pL#?x₀| (car |α1013|)))
  (let ((|c23| 1))
  (let ((|p24| (%int+ |c23| |_pL#?x₀|)))
  (funcall (the function |k|) |p24|))))))

; entrypoint
(defun |main| (|payload1000| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload1000|))
  (let ((|Γ1023| (cons '|𝐄| (vector))))
  (let ((|c10| 2))
  (let ((|con11| (cons '|Inl| (vector |c10|))))
  (let ((|c12| 1))
  (let ((|con13| (cons '|Inr| (vector |c12|))))
  (let ((|Γ1022| (cons '|𝐄| (vector))))
  (let ((|lam18| (cons '|𝐂| (vector #'|fn1009| |Γ1022|))))
  (let ((|pair19| (cons |lam18| |con11|)))
  (let ((|ρc1021| (cons |pair19| |Γ1023|)))
  (labels
    ((|k3| (|v2|)
      (let ((|Γ1018| (cons '|𝐄| (vector))))
      (let ((|lam25| (cons '|𝐂| (vector #'|fn1012| |Γ1018|))))
      (let ((|pair26| (cons |lam25| |con13|)))
      (let ((|ρc1017| (cons |pair26| |Γ1023|)))
      (labels
        ((|k5| (|v4|)
          (let ((|p28| (cons |v2| |v4|)))
          (funcall (the function |k|) |p28|))))
        (funcall #'|fn1003| |ρc1017| #'|k5|))))))))
    (funcall #'|fn1003| |ρc1021| #'|k3|))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

