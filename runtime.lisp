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

(defconstant +NOMATCH+ 'match-failure)
