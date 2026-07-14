;; == Runtime ==
(load "runtime.lisp")

;; == Linked Lisp Source ==
(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |countTree| (|payload1003| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload1003|))
  (let ((|α1004| (car |payload1003|)))
  (let ((|Γ1005| (cdr |payload1003|)))
  (let ((|_pL#?x₀| (car |α1004|)))
  (cond
    ((eq (car |_pL#?x₀|) '|Empty|)
      (let ((|c1| 0))
      (funcall (the function |k|) |c1|)))
    ((eq (car |_pL#?x₀|) '|Node|)
      (let ((|p2| (svref (cdr |_pL#?x₀|) 1)))
      (let ((|c3| 1))
      (let ((|u4| nil))
      (let ((|pair5| (cons |p2| |u4|)))
      (let ((|ρ1006| (cons |pair5| |Γ1005|)))
      (labels
        ((|k1| (|v0|)
          (let ((|p7| (%int+ |c3| |v0|)))
          (funcall (the function |k|) |p7|))))
        (funcall #'|countForest| |ρ1006| #'|k1|)))))))))))))

(defun |countForest| (|payload1007| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload1007|))
  (let ((|α1008| (car |payload1007|)))
  (let ((|Γ1009| (cdr |payload1007|)))
  (let ((|_pL#?x₀| (car |α1008|)))
  (cond
    ((eq (car |_pL#?x₀|) '|Nil|)
      (let ((|c9| 0))
      (funcall (the function |k|) |c9|)))
    ((eq (car |_pL#?x₀|) '|Cons|)
      (let ((|p10| (svref (cdr |_pL#?x₀|) 0)))
      (let ((|p11| (svref (cdr |_pL#?x₀|) 1)))
      (let ((|u12| nil))
      (let ((|pair13| (cons |p10| |u12|)))
      (let ((|ρ1011| (cons |pair13| |Γ1009|)))
      (labels
        ((|k3| (|v2|)
          (let ((|u15| nil))
          (let ((|pair16| (cons |p11| |u15|)))
          (let ((|ρ1010| (cons |pair16| |Γ1009|)))
          (labels
            ((|k5| (|v4|)
              (let ((|p18| (%int+ |v2| |v4|)))
              (funcall (the function |k|) |p18|))))
            (funcall #'|countForest| |ρ1010| #'|k5|)))))))
        (funcall #'|countTree| |ρ1011| #'|k3|)))))))))))))

; entrypoint
(defun |main| (|payload1000| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload1000|))
  (let ((|Γ1017| (cons '|𝐄| (vector))))
  (let ((|countTree#clo1015| (cons '|𝐂| (vector #'|countTree| |Γ1017|))))
  (let ((|c19| 1))
  (let ((|c20| 2))
  (let ((|c21| 5))
  (let ((|con22| (cons '|Nil| (vector))))
  (let ((|con23| (cons '|Node| (vector |c21| |con22|))))
  (let ((|con24| (cons '|Nil| (vector))))
  (let ((|con25| (cons '|Cons| (vector |con23| |con24|))))
  (let ((|con26| (cons '|Node| (vector |c20| |con25|))))
  (let ((|c27| 3))
  (let ((|c28| 4))
  (let ((|con29| (cons '|Nil| (vector))))
  (let ((|con30| (cons '|Node| (vector |c28| |con29|))))
  (let ((|con31| (cons '|Nil| (vector))))
  (let ((|con32| (cons '|Cons| (vector |con30| |con31|))))
  (let ((|con33| (cons '|Node| (vector |c27| |con32|))))
  (let ((|con34| (cons '|Empty| (vector))))
  (let ((|con35| (cons '|Nil| (vector))))
  (let ((|con36| (cons '|Cons| (vector |con34| |con35|))))
  (let ((|con37| (cons '|Cons| (vector |con33| |con36|))))
  (let ((|con38| (cons '|Cons| (vector |con26| |con37|))))
  (let ((|con39| (cons '|Node| (vector |c19| |con38|))))
  (let ((|u40| nil))
  (let ((|pair41| (cons |con39| |u40|)))
  (let ((|_code1012| (svref (cdr |countTree#clo1015|) 0)))
  (let ((|Γc1013| (svref (cdr |countTree#clo1015|) 1)))
  (let ((|ρc1014| (cons |pair41| |Γc1013|)))
  (funcall (the function |_code1012|) |ρc1014| |k|))))))))))))))))))))))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

