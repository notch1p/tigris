;;;; * Gadgets for defining FFI functions
;;;; - Entry: ~(defun fname (payload k))~
;;;; - payload = ~(cons α Γ)~
;;;;    - α: user args (unit = ~nil~ | value | nested pair = ~(cons arg1 (cons ...))~)
;;;;    - Γ: captured env = ~(cons '𝐄 (simple-vector ...captured...))~
;;;; - return via ~(funcall k value)~

(defun with-arg0 (payload k kont)
  "α is unit, call (kont Γ)"
  (let ((alpha (car payload))
        (gamma (cdr payload)))
    (declare (ignore alpha))
    (funcall kont gamma)))

(defun with-arg1 (payload k kont)
  "α is single-valued; call (kont α Γ)"
  (let ((alpha (car payload))
        (gamma (cdr payload)))
    (funcall kont alpha gamma)))

(defun with-arg2 (payload k kont)
  "α is ⟨a0, a1⟩; call (kont a0 a1 Γ)"
  (let* ((alpha (car payload))
         (a0    (car alpha))
         (a1    (cdr alpha))
         (gamma (cdr payload)))
    (funcall kont a0 a1 gamma)))

(defparameter empty-gamma (cons '|𝐄| (vector)))
(defparameter empty-𝐄 empty-gamma)

(defun make-closure (f &optional (gamma empty-gamma))
  (cons '|𝐂| (vector f gamma)))

;; e.g. println, print : ∀a, a -> Unit
(defun %println (payload k)
  (with-arg1 payload k
             (lambda (x gamma)
               (declare (ignore gamma))
               (princ x)
               (terpri)
               (funcall k nil))))
(defun %print (payload k)
  (with-arg1 payload k
             (lambda (x gamma)
               (declare (ignore gamma))
               (princ x)
               (funcall k nil))))
;; e.g. toString : ∀a, a -> String
(defun %to-string (payload k)
  (with-arg1 payload k
             (lambda (x gamma)
               (declare (ignore gamma))
               (funcall k (princ-to-string x)))))
;; e.g. string-append : String -> String -> String
(defun %string-append (payload k)
  (with-arg2 payload k
             (lambda (x y gamma)
               (declare (ignore gamma) (type string x) (type string y))
               (funcall k (concatenate 'string x y)))))

;; the closure object of println, print ...
(defparameter |%println| (make-closure #'%println))
(defparameter |%print| (make-closure #'%print))
(defparameter |%to-string| (make-closure #'%to-string))
(defparameter |%string-append| (make-closure #'%string-append))
