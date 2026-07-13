;;;; * Gadgets for defining FFI functions
;;;; Also served as a prelude.
;;;; - Entry: ~(defun fname (payload k))~
;;;; - payload = ~(cons α Γ)~
;;;;    - α: user args where
;;;;      - args = ~(args, ())~, if ~|args| = 1~
;;;;      - args = ~(args[0], args[1])~, if ~|args| = 2~
;;;;      - args = ~(cons ...nested pairs...)~, if ~|args| > 2~
;;;;    - Γ: captured env = ~(cons '𝐄 (simple-vector ...captured...))~
;;;; - return via ~(funcall k value)~
;;;;
;;;; * WARN: Compiler assumes pure environment, statements may get reordered.
;;;;         FFI with actual side effects shouldn't be relied on

(defparameter empty-gamma (cons '|𝐄| (vector)))
(defparameter empty-𝐄 empty-gamma)

(defun make-closure (f &optional (gamma empty-gamma))
  (cons '|𝐂| (vector (the function f) gamma)))

(defun with-arg2 (payload kont)
  "α is ⟨a0, a1⟩; call (kont a0 a1 Γ); deprecated, use with-args instead"
  (let* ((alpha (car payload))
         (a0    (car alpha))
         (a1    (cdr alpha))
         (gamma (cdr payload)))
    (funcall (the function kont) a0 a1 gamma)))

(defmacro with-args (payload arg-list &body body)
  "The macro WITH-ARGS destructures (payload = (cons α Γ)) and binds:
    - each user argument to the symbols provided,
    - a special variable GAMMA to the captured environment."
  (let* ((alpha (gensym "ALPHA"))
         (tmp   (gensym "TMP")))
    (labels ((build-binds (args)
                          (cond
                           ((null args) '())
                           ((null (cdr args)) `((,(car args) (car ,tmp))))
                           (t
                             (let ((head (car args))
                                   (rest (cdr args)))
                               (append `((,head (car ,tmp))
                                         (,tmp  (cdr ,tmp)))
                                 (if (null (cdr rest))
                                     `((,(car rest) ,tmp))
                                     (build-binds rest))))))))
      `(let* ((,alpha (car ,payload))
              (gamma  (cdr ,payload))
              (,tmp   ,alpha)
              ,@(build-binds arg-list))
         (declare (ignorable gamma))
         ,@body))))

(defmacro defforeign (name arg-list &body body)
  "Define a tigris-callable foreign function (combines `defun`/`defparameter`).
NAME can be:
  - a string: \"%println\" (preserves case)
  - a symbol: |%println|
    - also preserves case if
      1. escaped
      2. readtable-case set to `:preserve`
  "
  (flet ((name-to-string (x)
                           (etypecase x
                             (string x)
                             (symbol (symbol-name x))))
         (escape-bar (s)
                     (with-output-to-string (out)
                       (loop for c across s do
                               (case c
                                 (#\| (write-string "\\|" out))
                                 (#\\ (write-string "\\\\" out))
                                 (t (write-char c out))))))
         (make-closure (f)
                       `(cons '|𝐂| (vector
                                     (function ,f)
                                     (cons '|𝐄| (vector))))))
    (let* ((ns     (name-to-string name))
           (fn-sym (intern (escape-bar ns)))
           (cell   (intern ns))
           (clos   (make-closure fn-sym)))
      `(eval-when (:compile-toplevel :load-toplevel :execute)
         (defun ,fn-sym (payload k)
           (with-args payload ,arg-list ,@body))
         (defparameter ,cell ,clos)))))

;; e.g. println : ∀a, a -> Unit
(defforeign |%println| (x _)
  (declare (ignore gamma _))
  (princ x)
  (terpri)
  (funcall k nil))
;; e.g. print : ∀a, a -> Unit, using old `with-arg2`
(defun %print (payload k)
  (with-arg2 payload
             (lambda (x _ gamma)
               (declare (ignore gamma _))
               (princ x)
               (funcall k nil))))
;; the closure object of print
(defparameter |%print| (make-closure #'%print))

;; e.g. toString : ∀a, a -> String
(defforeign |%to-string| (x _)
  (declare (ignore gamma _))
  (funcall k (princ-to-string x)))
;; e.g. string-append : String -> String -> String
(defforeign "%string-append" (x y)
  (declare (ignore gamma) (type string x y))
  (funcall k (concatenate 'string x y)))

;; e.g. read (unsafe) : ∀a, Unit -> a
(defforeign |%read| (_ __)
  (declare (ignore gamma _ __))
  (funcall k (read)))
;; e.g. read-line : Unit -> String
(defforeign |%read-line| (_ __)
  (declare (ignore gamma _ __))
  (funcall k (read-line)))

;; e.g. modulus: Int -> Int -> Int
(defforeign |%int-mod| (x y)
  (declare (type integer x y))
  (funcall k (mod x y)))
