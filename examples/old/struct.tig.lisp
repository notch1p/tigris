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
    ((eq (car |_pL#?x₀|) '|Point|)
      (let ((|p1| (svref (cdr |_pL#?x₀|) 0)))
      (let ((|p2| (svref (cdr |_pL#?x₀|) 1)))
      (let ((|p3| (%int* |p1| |p1|)))
      (let ((|p4| (%int* |p2| |p2|)))
      (let ((|p5| (%int+ |p3| |p4|)))
      (funcall (the function |k|) |p5|)))))))))))

(defun |fn1006| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α1007| (car |payload|)))
  (let ((|_pL#x| (car |α1007|)))
  (let ((|_pR#x| (cdr |α1007|)))
  (let ((|p8| (%int= |_pL#x| |_pR#x|)))
  (funcall (the function |k|) |p8|))))))

(defun |fn1009| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α1010| (car |payload|)))
  (let ((|_pL#?x₀| (car |α1010|)))
  (let ((|_pR#?x₀| (cdr |α1010|)))
  (let ((|_pL#η0| (car |_pR#?x₀|)))
  (let ((|_pR#η0| (cdr |_pR#?x₀|)))
  (cond
    ((eq (car |_pL#?x₀|) '|Eq|)
      (let ((|p12| (svref (cdr |_pL#?x₀|) 0)))
      (let ((|pair13| (cons |_pL#η0| |_pR#η0|)))
      (let ((|_code1012| (svref (cdr |p12|) 0)))
      (let ((|Γc1013| (svref (cdr |p12|) 1)))
      (let ((|ρc1014| (cons |pair13| |Γc1013|)))
      (funcall (the function |_code1012|) |ρc1014| |k|))))))))))))))

; entrypoint
(defun |main| (|payload1000| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload1000|))
  (let ((|Γ1029| (cons '|𝐄| (vector))))
  (let ((|Γ1028| (cons '|𝐄| (vector))))
  (let ((|lam9| (cons '|𝐂| (vector #'|fn1006| |Γ1028|))))
  (let ((|con10| (cons '|Eq| (vector |lam9|))))
  (let ((|Γ1027| (cons '|𝐄| (vector))))
  (let ((|c16| 10))
  (let ((|c17| 10))
  (let ((|pair19| (cons |c16| |c17|)))
  (let ((|pair18| (cons |con10| |pair19|)))
  (let ((|ρc1026| (cons |pair18| |Γ1027|)))
  (labels
    ((|k1| (|v0|)
      (let ((|u21| nil))
      (let ((|pair22| (cons |v0| |u21|)))
      (let ((|_code1021| (svref (cdr |%println|) 0)))
      (let ((|Γc1022| (svref (cdr |%println|) 1)))
      (let ((|ρc1023| (cons |pair22| |Γc1022|)))
      (labels
        ((|k3| (|v2|)
          (let ((|c24| 6))
          (let ((|c25| 8))
          (let ((|con26| (cons '|Point| (vector |c24| |c25|))))
          (let ((|u27| nil))
          (let ((|pair28| (cons |con26| |u27|)))
          (let ((|ρc1020| (cons |pair28| |Γ1029|)))
          (labels
            ((|k5| (|v4|)
              (let ((|u30| nil))
              (let ((|pair31| (cons |v4| |u30|)))
              (let ((|_code1015| (svref (cdr |%println|) 0)))
              (let ((|Γc1016| (svref (cdr |%println|) 1)))
              (let ((|ρc1017| (cons |pair31| |Γc1016|)))
              (labels
                ((|k7| (|v6|)
                  (let ((|p33| (cons |v2| |v6|)))
                  (funcall (the function |k|) |p33|))))
                (funcall (the function |_code1015|) |ρc1017| #'|k7|)))))))))
            (funcall #'|fn1003| |ρc1020| #'|k5|))))))))))
        (funcall (the function |_code1021|) |ρc1023| #'|k3|)))))))))
    (funcall #'|fn1009| |ρc1026| #'|k1|)))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

