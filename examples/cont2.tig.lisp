;; == Linked Lisp Source ==
(load "ffi.lisp")

; Prelude
(declaim (optimize (speed 3) (safety 0) (debug 0)))
(load "runtime.lisp")
(defstruct (clos (:constructor %clos (fn arity)))
  (fn #'identity :type function)
  (arity 0 :type fixnum))
(defun %apply-slow (c args)
  (declare (type list args))
  (let ((n (length args)) (k (clos-arity c)))
    (cond
      ((= n k) (apply (clos-fn c) args))
      ((< n k) (%clos (lambda (&rest more)
                        (apply (clos-fn c)
                               (append args more)))
                      (- k n)))
      (t (%apply-slow (apply (clos-fn c)
                             (subseq args 0 k))
                      (nthcdr k args))))))


; gapply
(defun gapply1 (c a1)
  (if (eql (clos-arity c) 1)
    (funcall (clos-fn c) a1)
    (%apply-slow c (list a1))))

(defun gapply2 (c a1 a2)
  (if (eql (clos-arity c) 2)
    (funcall (clos-fn c) a1 a2)
    (%apply-slow c (list a1 a2))))

; ftype
(declaim (ftype (function (clos t clos) t) |fn-57|))

(declaim (ftype (function (clos t t) t) |fn-58|))

(declaim (ftype (function (string) clos) |fn-60|))

(declaim (ftype (function (clos) clos) |fn-59|))

(declaim (ftype (function (string) null) |fn-61|))

(declaim (ftype (function (string string) string) |append-2|))

(declaim (ftype (function (t) null) |signal-6|))

(declaim (ftype (function (t) null) |println-9|))

(declaim (ftype (function (string) boolean) |y-or-n-12|))

(declaim (ftype (function (t clos) t) |cont/pure-15|))

(declaim (ftype (function (clos clos) t) |call/cc-19|))

(declaim (ftype (function (clos clos t) t) |>>=-27|))

(declaim (ftype (function (clos) clos) |get-name-35|))

(declaim (type null |greet-40|))

(declaim (type null |main-56|))

; body
(defun |fn-57| (|k-21| |a-23| |_-24|)
  (gapply1 |k-21| |a-23|))

(defun |fn-58| (|f-29| |k-30| |a-32|)
  (gapply2 |f-29| |a-32| |k-30|))

(defun |fn-60| (|name-45|)
  (let* ((|app-46| (|append-2| "welcome, " |name-45|))
         (|app-47| (|append-2| |app-46| "!")))
     (%clos (lambda (|g0|)
         (|cont/pure-15| |app-47| |g0|))
       1)))

(defun |fn-59| (|exitK-42|)
  (let* ((|app-43| (|get-name-35| |exitK-42|))
         (|fn-44| (%clos (function |fn-60|) 1)))
     (%clos (lambda (|g1|)
         (|>>=-27| |app-43| |fn-44| |g1|))
       1)))

(defun |fn-61| (|?x₀-52|)
  (cond
    ((%string= |?x₀-52| "robot")
      (|signal-6| "You are not welcomed."))
    (t (|println-9| |?x₀-52|))))

(defun |append-2| (|η-3| |η-4|)
  (%string-append |η-3| |η-4|))

(defun |signal-6| (|η-7|)
  (error |η-7|))

(defun |println-9| (|η-10|)
  (%println |η-10|))

(defun |y-or-n-12| (|η-13|)
  (y-or-n-p |η-13|))

(defun |cont/pure-15| (|x-16| |k-17|)
  (gapply1 |k-17| |x-16|))

(defun |call/cc-19| (|f-20| |k-21|)
  (let* ((|fn-22| (%clos (lambda (|g2| |g3|)
               (|fn-57| |k-21| |g2| |g3|))
             2)))
     (gapply2 |f-20| |fn-22| |k-21|)))

(defun |>>=-27| (|c-28| |f-29| |k-30|)
  (let* ((|fn-31| (%clos (lambda (|g4|)
               (|fn-58| |f-29| |k-30| |g4|))
             1)))
     (gapply1 |c-28| |fn-31|)))

(defun |get-name-35| (|exit-with-36|)
  (let* ((|app-37| (|y-or-n-12| "Are you a human?")))
     (if |app-37|
       (%clos (lambda (|g5|)
           (|cont/pure-15| "some human" |g5|))
         1)
       (gapply1 |exit-with-36| "robot"))))

(defparameter |greet-40|
  (let* ((|fn-41| (%clos (function |fn-59|) 1))
         (|fn-51| (%clos (function |fn-61|) 1)))
     (|call/cc-19| |fn-41| |fn-51|)))

(defparameter |main-56|
  |greet-40|)

(format t "~S~%" |main-56|)
