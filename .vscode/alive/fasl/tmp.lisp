;; == Common Lisp ==

; hoisted functions

(defun |fact| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|Γ| (cdr |payload|)))
      (let ((|_pL#acc| (car |α|)))
        (let ((|_pR#acc| (cdr |α|)))
          (cond
            ((equal |_pR#acc| 0)
              (funcall |k| |_pL#acc|))            
            (t
              (let ((|p2| (* |_pL#acc| |_pR#acc|)))
                (let ((|c3| 1))
                  (let ((|p4| (- |_pR#acc| |c3|)))
                    (let ((|pair5| (cons |p2| |p4|)))
                      (let ((|ρ| (cons |pair5| |Γ|)))
                        (funcall #'|fact| |ρ| |k|)))))))))))))

; entrypoint
(defun |main| (|arg| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|Γ| (cons '|𝐄| (vector))))
    (let ((|fact| (cons '|𝐂| (vector #'|fact| |Γ|))))
      (let ((|c7| 1))
        (let ((|c8| 25))
          (let ((|pair9| (cons |c7| |c8|)))
            (let ((|_code| (svref (cdr |fact|) 0)))
              (let ((|Γ| (svref (cdr |fact|) 1)))
                (let ((|ρ| (cons |pair9| |Γ|)))
                  (funcall |_code| |ρ| |k|))))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

