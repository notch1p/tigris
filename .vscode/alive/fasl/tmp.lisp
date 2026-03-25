;; == Runtime ==
(load "runtime.lisp")

;; == Linked Lisp Source ==
(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |«<++>»| (|payload| |k|)
  (let ((|α| (car |payload|)))
    (let ((|Γ| (cdr |payload|)))
      (let ((|_pL#x| (car |α|)))
        (let ((|_pR#x| (cdr |α|)))
          (cond
            ((eq (car |_pL#x|) '|Nil|)
              (cond
                ((eq (car |_pR#x|) '|Nil|)
                  (let ((|c6| 0))
                    (funcall (the function |k|) |c6|)))
                (t
                  (let ((|c7| 0))
                    (funcall (the function |k|) |c7|)))))
            ((eq (car |_pL#x|) '|Cons|)
              (cond
                ((eq (car |_pR#x|) '|Cons|)
                  (format nil "~A" |_pL#x|)
                  (let ((|p8| (svref (cdr |_pL#x|) 0)))
                    (let ((|p9| (svref (cdr |p8|) 1)))
                      (let ((|p10| (svref (cdr |_pR#x|) 0)))
                        (let ((|p11| (svref (cdr |p10|) 1)))
                          (let ((|p12| 0))
                            (let ((|pair13| (cons |p9| |p11|)))
                              (let ((|ρ1000| (cons |pair13| |Γ|)))
                                (labels ((|k1| (|v0|)
                                  (let ((|p15| (%int+ |p12| |v0|)))
                                    (funcall (the function |k|) |p15|))))
                                  (funcall #'|«<++>»| |ρ1000| #'|k1|))))))))))
                (t
                  (let ((|c16| 0))
                    (funcall (the function |k|) |c16|)))))
            (t
              (let ((|c17| 0))
                (funcall (the function |k|) |c17|)))))))))

; entrypoint
(defun |main| (|payload| |k|)
  (let ((|Γ| (cons '|𝐄| (vector))))
    (let ((|«<++>»#clo1004| (cons '|𝐂| (vector #'|«<++>»| |Γ|))))
      (let ((|c18| 123))
        (let ((|c19| 456))
          (let ((|con20| (cons '|Nil| (vector))))
            (let ((|con21| (cons '|Cons| (vector |c19| |con20|))))
              (let ((|con22| (cons '|Cons| (vector |c18| |con21|))))
                (let ((|c23| 374))
                  (let ((|c24| 290))
                    (let ((|con25| (cons '|Nil| (vector))))
                      (let ((|con26| (cons '|Cons| (vector |c24| |con25|))))
                        (let ((|con27| (cons '|Cons| (vector |c23| |con26|))))
                          (let ((|pair28| (cons |con22| |con27|)))
                            (let ((|_code1001| (svref (cdr |«<++>»#clo1004|) 0)))
                              (let ((|Γc1002| (svref (cdr |«<++>»#clo1004|) 1)))
                                (let ((|ρc1003| (cons |pair28| |Γc1002|)))
                                  (funcall (the function |_code1001|) |ρc1003| |k|))))))))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

