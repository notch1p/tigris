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

(defun with-arg2 (payload kont)
  "α is ⟨a0, a1⟩; call (kont a0 a1 Γ)"
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
                              (,tmp (cdr ,tmp)))
                            (if (null (cdr rest))
                                `((,(car rest) ,tmp))
                                (build-binds rest))))))))
      `(let* ((,alpha (car ,payload))
              (gamma  (cdr ,payload))
              (,tmp   ,alpha)
              ,@(build-binds arg-list))
         (declare (ignorable gamma))
         ,@body))))

(defparameter empty-gamma (cons '|𝐄| (vector)))
(defparameter empty-𝐄 empty-gamma)

(defun make-closure (f &optional (gamma empty-gamma))
  (cons '|𝐂| (vector (the function f) gamma)))

;; e.g. println, print : ∀a, a -> Unit
(defun %println (payload k)
  (with-arg2 payload
             (lambda (x _ gamma)
               (declare (ignore gamma _))
               (princ x)
               (terpri)
               (funcall k nil))))
(defun %print (payload k)
  (with-arg2 payload
             (lambda (x _ gamma)
               (declare (ignore gamma _))
               (princ x)
               (funcall k nil))))
;; e.g. toString : ∀a, a -> String
(defun %to-string (payload k)
  (with-arg2 payload
             (lambda (x _ gamma)
               (declare (ignore gamma _))
               (funcall k (princ-to-string x)))))
;; e.g. string-append : String -> String -> String
(defun %string-append (payload k)
  (with-arg2 payload
             (lambda (x y gamma)
               (declare (ignore gamma) (type string x y))
               (funcall k (concatenate 'string x y)))))

;; e.g. read (unsafe) : ∀a, Unit -> a
(defun %read (payload k)
  (with-arg2 payload
             (lambda (_ __ gamma)
               (declare (ignore gamma _ __))
               (funcall k (read)))))

;; e.g. read-line : Unit -> String
(defun %read-line (payload k)
  (with-arg2 payload
             (lambda (_ __ gamma)
               (declare (ignore gamma _ __))
               (funcall k (read-line)))))

;; e.g. modulus: Int -> Int -> Int
(defun %int-mod (payload k)
  (with-args payload (x y)
    (declare (type integer x y))
    (funcall k (mod x y))))

(declaim (inline %string=))
(defun %string= (s1 s2)
  (declare (type simple-string s1) (type simple-string s2))
  (the boolean (sb-kernel:%sp-string= s1 s2 0 nil 0 nil)))

(declaim (ftype (function (integer integer) integer) %int+)
         (inline %int+))
(defun %int+ (a b)
  (declare (optimize (speed 3) (debug 0) (safety 0)))
  (sb-kernel:two-arg-+ a b))

(declaim (ftype (function (integer integer) integer) %int-)
         (inline %int-))
(defun %int- (a b)
  (declare (optimize (speed 3) (debug 0) (safety 0)))
  (sb-kernel:two-arg-- a b))

(declaim (ftype (function (integer integer) integer) %int*)
         (inline %int*))
(defun %int* (a b)
  (declare (optimize (speed 3) (debug 0) (safety 0)))
  (sb-kernel:two-arg-* a b))

(declaim (ftype (function (integer fixnum) integer) %int/)
         (inline %int/))
(defun %int/ (a b)
  (declare (optimize (speed 3) (debug 0) (safety 0)))
  (if (zerop b) 0
      (floor a b)))

(declaim (ftype (function (integer integer) boolean) %int=)
         (inline %int=))
(defun %int= (a b)
  (declare (optimize (speed 3) (debug 0) (safety 0)))
  (sb-kernel:two-arg-= a b))

(define-condition match-failure (error)
  ((discrminant
      :initarg :discr
      :reader discrminant
      :type string))
  (:report
   (lambda (condition stream)
     (format stream "No branch can be matched against ~A" (discrminant condition)))))

;; the closure object of println, print ...
(defconstant +NOMATCH+ 'match-failure)
(defparameter |%println| (make-closure #'%println))
(defparameter |%print| (make-closure #'%print))
(defparameter |%to-string| (make-closure #'%to-string))
(defparameter |%string-append| (make-closure #'%string-append))
(defparameter |%read| (make-closure #'%read))
(defparameter |%read-line| (make-closure #'%read-line))
(defparameter |%int-mod| (make-closure #'%int-mod))
