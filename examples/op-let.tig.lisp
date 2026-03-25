;; == Runtime ==
(load "runtime.lisp")

;; == Linked Lisp Source ==
(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |«<+>»| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α| (car |payload|)))
    (let ((|Γ| (cdr |payload|)))
      (let ((|_pL#xs| (car |α|)))
        (let ((|_pR#xs| (cdr |α|)))
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
                              (let ((|ρ1000| (cons |pair8| |Γ|)))
                                (labels ((|k1| (|v0|)
                                  (let ((|p10| (%int+ |p7| |v0|)))
                                    (funcall (the function |k|) |p10|))))
                                  (funcall #'|«<+>»| |ρ1000| #'|k1|))))))))))
                (t
                  (let ((|c11| 0))
                    (funcall (the function |k|) |c11|)))))
            (t
              (let ((|c12| 0))
                (funcall (the function |k|) |c12|)))))))))

(defun |fn1001| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α| (car |payload|)))
    (let ((|_pL#?x₀| (car |α|)))
      (let ((|_pR#?x₀| (cdr |α|)))
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
(defun |main| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|Γ| (cons '|𝐄| (vector))))
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
                          (let ((|ρc1004| (cons |pair29| |Γ|)))
                            (labels ((|k3| (|v2|)
                              (let ((|c31| 2))
                                (let ((|con32| (cons '|Some| (vector |c31|))))
                                  (let ((|c33| 3))
                                    (let ((|con34| (cons '|Some| (vector |c33|))))
                                      (let ((|pair35| (cons |con32| |con34|)))
                                        (let ((|ρc1007| (cons |pair35| |Γ|)))
                                          (labels ((|k5| (|v4|)
                                            (let ((|c37| 4))
                                              (let ((|con38| (cons '|Some| (vector |c37|))))
                                                (let ((|pair39| (cons |v4| |con38|)))
                                                  (let ((|ρc1010| (cons |pair39| |Γ|)))
                                                    (labels ((|k7| (|v6|)
                                                      (let ((|p41| (cons |v2| |v6|)))
                                                        (funcall (the function |k|) |p41|))))
                                                      (funcall #'|fn1001| |ρc1010| #'|k7|))))))))
                                            (funcall #'|fn1001| |ρc1007| #'|k5|))))))))))
                              (funcall #'|«<+>»| |ρc1004| #'|k3|))))))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

