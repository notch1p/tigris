;; == external FFI ==

(load "ffi.lisp")

;; == Common Lisp ==

; hoisted functions

(defun |fn1000| (|payload| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|α| (car |payload|)))
    (let ((|_pL#x| (car |α|)))
      (funcall |k| |_pL#x|))))

; entrypoint
(defun |main| (|arg| |k|)
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (let ((|c0| 1))
    (let ((|Γ| (cons '|𝐄| (vector))))
      (let ((|u3| nil))
        (let ((|pair4| (cons |c0| |u3|)))
          (let ((|ρc1003| (cons |pair4| |Γ|)))
            (labels ((|k1| (|v0|)
              (let ((|c6| 2))
                (let ((|u7| nil))
                  (let ((|pair8| (cons |c6| |u7|)))
                    (let ((|ρc1006| (cons |pair8| |Γ|)))
                      (labels ((|k3| (|v2|)
                        (let ((|p10| (cons |v0| |v2|)))
                          (funcall |k| |p10|))))
                        (funcall #'|fn1000| |ρc1006| #'|k3|))))))))
              (funcall #'|fn1000| |ρc1003| #'|k1|))))))))

; driver
(defun |__start| ()
  (format t "~A"
    (funcall #'|main| nil #'identity)))

