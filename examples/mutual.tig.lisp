;; == external FFI ==

(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |countTree| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|Γ| (cdr |payload|)))
      (cond
        ((eq (car |α|) '|Empty|)
          (let ((|c1| 0))
            (funcall |k| |c1|)))
        ((eq (car |α|) '|Node|)
          (let ((|p2| (svref (cdr |α|) 1)))
            (let ((|c3| 1))
              (let ((|ρ| (cons |p2| |Γ|)))
                (labels ((|k1| (|v0|)
                  (let ((|p5| (+ |c3| |v0|)))
                    (funcall |k| |p5|))))
                  (funcall #'|countForest| |ρ| #'|k1|))))))))))

(defun |countForest| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|Γ| (cdr |payload|)))
      (cond
        ((eq (car |α|) '|Nil|)
          (let ((|c7| 0))
            (funcall |k| |c7|)))
        ((eq (car |α|) '|Cons|)
          (let ((|p8| (svref (cdr |α|) 0)))
            (let ((|p9| (svref (cdr |α|) 1)))
              (let ((|ρ| (cons |p8| |Γ|)))
                (labels ((|k3| (|v2|)
                  (let ((|ρ| (cons |p9| |Γ|)))
                    (labels ((|k5| (|v4|)
                      (let ((|p12| (+ |v2| |v4|)))
                        (funcall |k| |p12|))))
                      (funcall #'|countForest| |ρ| #'|k5|)))))
                  (funcall #'|countTree| |ρ| #'|k3|))))))))))

; entrypoint
(defun |main| (|arg| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|Γ| (cons '|𝐄| (vector))))
    (let ((|countTree| (cons '|𝐂| (vector #'|countTree| |Γ|))))
      (let ((|c13| 1))
        (let ((|c14| 2))
          (let ((|c15| 5))
            (let ((|con16| (cons '|Nil| (vector))))
              (let ((|con17| (cons '|Node| (vector |c15| |con16|))))
                (let ((|con18| (cons '|Nil| (vector))))
                  (let ((|con19| (cons '|Cons| (vector |con17| |con18|))))
                    (let ((|con20| (cons '|Node| (vector |c14| |con19|))))
                      (let ((|c21| 3))
                        (let ((|c22| 4))
                          (let ((|con23| (cons '|Nil| (vector))))
                            (let ((|con24| (cons '|Node| (vector |c22| |con23|))))
                              (let ((|con25| (cons '|Nil| (vector))))
                                (let ((|con26| (cons '|Cons| (vector |con24| |con25|))))
                                  (let ((|con27| (cons '|Node| (vector |c21| |con26|))))
                                    (let ((|con28| (cons '|Empty| (vector))))
                                      (let ((|con29| (cons '|Nil| (vector))))
                                        (let ((|con30| (cons '|Cons| (vector |con28| |con29|))))
                                          (let ((|con31| (cons '|Cons| (vector |con27| |con30|))))
                                            (let ((|con32| (cons '|Cons| (vector |con20| |con31|))))
                                              (let ((|con33| (cons '|Node| (vector |c13| |con32|))))
                                                (let ((|_code| (svref (cdr |countTree|) 0)))
                                                  (let ((|Γc| (svref (cdr |countTree|) 1)))
                                                    (let ((|ρc| (cons |con33| |Γc|)))
                                                      (funcall |_code| |ρc| |k|))))))))))))))))))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

