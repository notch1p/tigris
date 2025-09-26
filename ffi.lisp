;;;; * Gadgets for defining FFI functions
;;;; - Entry: ~(defun fname (payload k))~
;;;; - payload = ~(cons α Γ)~
;;;;    - α: user args (unit = ~nil~ | value | nested pair = ~(cons arg1 (cons ...))~)
;;;;    - Γ: captured env = ~(cons '𝐄 (simple-vector ...captured...))~
;;;; - return via ~(funcall k value)~
;;;;
;;;; * WARN: Compiler assumes pure environment, statements may get reordered.
;;;;         FFI with actual side effects shouldn't be relied on

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
  (with-arg2 payload k
             (lambda (x _ gamma)
               (declare (ignore gamma) (ignore _))
               (princ x)
               (terpri)
               (funcall k nil))))
(defun %print (payload k)
  (with-arg2 payload k
             (lambda (x _ gamma)
               (declare (ignore gamma) (ignore _))
               (princ x)
               (funcall k nil))))
;; e.g. toString : ∀a, a -> String
(defun %to-string (payload k)
  (with-arg2 payload k
             (lambda (x _ gamma)
               (declare (ignore gamma) (ignore _))
               (funcall k (princ-to-string x)))))
;; e.g. string-append : String -> String -> String
(defun %string-append (payload k)
  (with-arg2 payload k
             (lambda (x y gamma)
               (declare (ignore gamma) (type string x) (type string y))
               (funcall k (concatenate 'string x y)))))

;; e.g. read (unsafe) : ∀a, Unit -> a
(defun %read (payload k)
  (with-arg2 payload k
             (lambda (_ __ gamma)
               (declare (ignore gamma) (ignore _) (ignore __))
               (funcall k (read)))))

;; e.g. read-line : Unit -> String
(defun %read-line (payload k)
  (with-arg2 payload k
             (lambda (_ __ gamma)
               (declare (ignore gamma) (ignore _) (ignore __))
               (funcall k (read-line)))))

;; the closure object of println, print ...
(defparameter |%println| (make-closure #'%println))
(defparameter |%print| (make-closure #'%print))
(defparameter |%to-string| (make-closure #'%to-string))
(defparameter |%string-append| (make-closure #'%string-append))
(defparameter |%read| (make-closure #'%read))
(defparameter |%read-line| (make-closure #'%read-line))
