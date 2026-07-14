;; == Linked Lisp Source ==
(load "ffi.lisp")

; Prelude
(declaim (optimize (speed 3) (safety 0) (debug 0)))
(load "runtime.lisp")
(defstruct (clos (:constructor %clos (fn arity)))
  (fn #'identity :type function)
  (arity 0 :type fixnum))
(defun %apply-slow (c args)
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


; ftype
(declaim (ftype (function (t) null) |println-2|))

(declaim (ftype (function (string string) string) |append-3|))

(declaim (ftype (function (t) string) |toString-4|))

(declaim (ftype (function (null) t) |read-5|))

(declaim (ftype (function (integer) integer) |fact-6|))

(declaim (ftype (function (integer integer integer) integer) |go-35|))

(declaim (type integer |main-7|))

; body
(defun |println-2| (|η-8|)
  (let* ((|ffi-9| (%println |η-8|))) |ffi-9|))

(defun |append-3| (|η-10| |η-11|)
  (let* ((|ffi-12| (%string-append |η-10| |η-11|))) |ffi-12|))

(defun |toString-4| (|η-13|)
  (let* ((|ffi-14| (%to-string |η-13|))) |ffi-14|))

(defun |read-5| (|η-15|)
  (let* ((|ffi-16| (%read |η-15|))) |ffi-16|))

(defun |fact-6| (|n-17|)
  (let* ((|app-31| (|go-35| |n-17| 1 |n-17|))) |app-31|))

(defun |go-35| (|n-17| |acc-19| |?x₀-20|)
  (case |?x₀-20|
    (0
      |acc-19|)
    (t
     (let* ((|π-21| (%int* |acc-19| |?x₀-20|))
               (|π-22| (%int- |n-17| |?x₀-20|))
               (|app-23| (|toString-4| |π-22|))
               (|app-24| (|append-3| "fact " |app-23|))
               (|app-25| (|append-3| |app-24| " = "))
               (|app-26| (|toString-4| |π-21|))
               (|app-27| (|append-3| |app-25| |app-26|))
               (|app-28| (|println-2| |app-27|))
               (|π-29| (%int- |?x₀-20| 1))
               (|app-30| (|go-35| |n-17| |π-21| |π-29|)))
           |app-30|))))

(defparameter |main-7|
  (let* ((|app-32| (|println-2| "Enter a number:"))
         (|app-33| (|read-5| nil))
         (|app-34| (|fact-6| |app-33|)))
     |app-34|))

(format t "~S~%" |main-7|)
