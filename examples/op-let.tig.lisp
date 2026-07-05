;; == Runtime ==
(load "runtime.lisp")

;; == Linked Lisp Source ==
(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |«<+>»| (|payload1003| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload1003|))
  (let ((|α1004| (car |payload1003|)))
  (let ((|Γ1005| (cdr |payload1003|)))
  (let ((|_pL#xs| (car |α1004|)))
  (let ((|_pR#xs| (cdr |α1004|)))
  (cond
    ((eq (car |_pL#xs|) '|Nil|)
      (cond
      ((eq (car |_pR#xs|) '|Nil|)
        (let ((|c1| 0))
        (funcall (the function |k|) |c1|)))
      (t
        (let ((|c2| 0))
          (funcall (the function |k|) |c2|)))))
    ((eq (car |_pL#xs|) '|Cons|)
      (cond
      ((eq (car |_pR#xs|) '|Cons|)
        (let ((|p3| (svref (cdr |_pL#xs|) 0)))
        (let ((|p4| (svref (cdr |_pL#xs|) 1)))
        (let ((|p5| (svref (cdr |_pR#xs|) 0)))
        (let ((|p6| (svref (cdr |_pR#xs|) 1)))
        (let ((|p7| (%int+ |p3| |p5|)))
        (let ((|pair8| (cons |p4| |p6|)))
        (let ((|ρ1006| (cons |pair8| |Γ1005|)))
        (labels
          ((|k1| (|v0|)
            (let ((|p10| (%int+ |p7| |v0|)))
            (funcall (the function |k|) |p10|))))
          (funcall #'|«<+>»| |ρ1006| #'|k1|))))))))))
      (t
        (let ((|c11| 0))
          (funcall (the function |k|) |c11|)))))
    (t
      (let ((|c12| 0))
        (funcall (the function |k|) |c12|)))))))))

(defun |fn1007| (|payload1008| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload1008|))
  (let ((|α1009| (car |payload1008|)))
  (let ((|_pL#?x₀| (car |α1009|)))
  (let ((|_pR#?x₀| (cdr |α1009|)))
  (cond
    ((eq (car |_pL#?x₀|) '|Some|)
      (cond
      ((eq (car |_pR#?x₀|) '|Some|)
        (let ((|p14| (svref (cdr |_pL#?x₀|) 0)))
        (let ((|p15| (svref (cdr |_pR#?x₀|) 0)))
        (let ((|p16| (%int* |p14| |p15|)))
        (let ((|con17| (cons '|Some| (vector |p16|))))
        (funcall (the function |k|) |con17|))))))
      (t
        (error +NOMATCH+ :discr "#[?x₀, ?x₁]"))))
    (t
      (error +NOMATCH+ :discr "#[?x₀, ?x₁]")))))))

; entrypoint
(defun |main| (|payload1000| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload1000|))
  (let ((|Γ1022| (cons '|𝐄| (vector))))
  (let ((|Γ1020| (cons '|𝐄| (vector))))
  (let ((|c19| 123))
  (let ((|c20| 456))
  (let ((|con21| (cons '|Nil| (vector))))
  (let ((|con22| (cons '|Cons| (vector |c20| |con21|))))
  (let ((|con23| (cons '|Cons| (vector |c19| |con22|))))
  (let ((|c24| 374))
  (let ((|c25| 290))
  (let ((|con26| (cons '|Nil| (vector))))
  (let ((|con27| (cons '|Cons| (vector |c25| |con26|))))
  (let ((|con28| (cons '|Cons| (vector |c24| |con27|))))
  (let ((|pair29| (cons |con23| |con28|)))
  (let ((|ρc1013| (cons |pair29| |Γ1022|)))
  (labels
    ((|k3| (|v2|)
      (let ((|c31| 2))
      (let ((|con32| (cons '|Some| (vector |c31|))))
      (let ((|c33| 3))
      (let ((|con34| (cons '|Some| (vector |c33|))))
      (let ((|pair35| (cons |con32| |con34|)))
      (let ((|ρc1016| (cons |pair35| |Γ1020|)))
      (labels
        ((|k5| (|v4|)
          (let ((|c37| 4))
          (let ((|con38| (cons '|Some| (vector |c37|))))
          (let ((|pair39| (cons |v4| |con38|)))
          (let ((|ρc1019| (cons |pair39| |Γ1020|)))
          (labels
            ((|k7| (|v6|)
              (let ((|p41| (cons |v2| |v6|)))
              (funcall (the function |k|) |p41|))))
            (funcall #'|fn1007| |ρc1019| #'|k7|))))))))
        (funcall #'|fn1007| |ρc1016| #'|k5|))))))))))
    (funcall #'|«<+>»| |ρc1013| #'|k3|)))))))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

