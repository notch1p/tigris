;; == System F IR ==

let i_Functor_0 : ∀ a, Functor (Sum a) =
  (Λ a.
     Functor@(Sum a)
       (Λ a b.
          fun f : a → b =>
            fun ?x₀ : Sum a a =>
              match ?x₀ with | Inl a => Inl@a@b a | Inr b => Inr@a@b (f b)))

let main : ∀ α [Functor Sum α], Sum Int Int × Sum α Int =
  (Λ α.
     let rd_Functor_0 : Functor (Sum Int) = i_Functor_0@Int
     in fun d_Functor_0 : Functor (Sum α) =>
       let a : ∀ α, Sum Int α = (Λ α. Inl@Int@α 2)
       and b : ∀ α, Sum α Int = (Λ α. Inr@α@Int 1)
       in (rd_Functor_0[0, fmap]@(Sum Int)
          (fun ?x₀ : Int =>
             mul
               2
               ?x₀)
          a@Int , d_Functor_0[0, fmap]@(Sum α)
          (fun ?x₀ : Int => add 1 ?x₀) b@α))
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
                        (labels ((|k1| (|v0|)
                          (let ((|con7| (cons '|Inr| (vector |v0|))))
                            (funcall (the function |k|) |con7|))))
                          (funcall (the function |_code1006|) |ρc1008| #'|k1|))))))))))))))

(defun |fn1012| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α1013| (car |payload|)))
    (let ((|_pL#?x₀| (car |α1013|)))
      (let ((|c17| 2))
        (let ((|p18| (%int* |c17| |_pL#?x₀|)))
          (funcall (the function |k|) |p18|))))))

(defun |fn1015| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α1016| (car |payload|)))
    (let ((|_pL#?x₀| (car |α1016|)))
      (let ((|c24| 1))
        (let ((|p25| (%int+ |c24| |_pL#?x₀|)))
          (funcall (the function |k|) |p25|))))))

(defun |fn1009| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload|))
  (let ((|α1010| (car |payload|)))
    (let ((|Γ1011| (cdr |payload|)))
      (let ((|lam8| (svref (cdr |Γ1011|) 0)))
        (let ((|_pL#d_Functor_0| (car |α1010|)))
          (let ((|c11| 2))
            (let ((|con12| (cons '|Inl| (vector |c11|))))
              (let ((|c13| 1))
                (let ((|con14| (cons '|Inr| (vector |c13|))))
                  (let ((|Γ1025| (cons '|𝐄| (vector))))
                    (let ((|lam19| (cons '|𝐂| (vector #'|fn1012| |Γ1025|))))
                      (let ((|pair20| (cons |lam19| |con12|)))
                        (let ((|_code1022| (svref (cdr |lam8|) 0)))
                          (let ((|Γc1023| (svref (cdr |lam8|) 1)))
                            (let ((|ρc1024| (cons |pair20| |Γc1023|)))
                              (labels ((|k3| (|v2|)
                                (let ((|p22| (svref (cdr |_pL#d_Functor_0|) 0)))
                                  (let ((|Γ1021| (cons '|𝐄| (vector))))
                                    (let ((|lam26| (cons '|𝐂| (vector #'|fn1015| |Γ1021|))))
                                      (let ((|pair27| (cons |lam26| |con14|)))
                                        (let ((|_code1018| (svref (cdr |p22|) 0)))
                                          (let ((|Γc1019| (svref (cdr |p22|) 1)))
                                            (let ((|ρc1020| (cons |pair27| |Γc1019|)))
                                              (labels ((|k5| (|v4|)
                                                (let ((|p29| (cons |v2| |v4|)))
                                                  (funcall (the function |k|) |p29|))))
                                                (funcall (the function |_code1018|) |ρc1020| #'|k5|)))))))))))
                                (funcall (the function |_code1022|) |ρc1024| #'|k3|)))))))))))))))))

; entrypoint
(defun |main| (|payload1000| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)) (ignorable |payload1000|))
  (let ((|Γ1027| (cons '|𝐄| (vector))))
    (let ((|lam8| (cons '|𝐂| (vector #'|fn1003| |Γ1027|))))
      (let ((|Γ1026| (cons '|𝐄| (vector |lam8|))))
        (let ((|lam30| (cons '|𝐂| (vector #'|fn1009| |Γ1026|))))
          (funcall (the function |k|) |lam30|))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

