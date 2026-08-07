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


; ftype
(declaim (ftype (function (integer integer integer) integer) |go-35|))

(declaim (ftype (function (t) null) |println-2|))

(declaim (ftype (function (string string) string) |append-5|))

(declaim (ftype (function (t) string) |toString-9|))

(declaim (ftype (function (null) t) |read-12|))

(declaim (ftype (function (integer) integer) |fact-15|))

(declaim (type integer |main-31|))

; body
(defun |go-35| (|n-16| |acc-18| |?x₀-19|)
  (case |?x₀-19|
    (0
      |acc-18|)
    (t (let* ((|π-20| (%int* |acc-18| |?x₀-19|))
             (|π-21| (%int- |n-16| |?x₀-19|))
             (|app-22| (|toString-9| |π-21|))
             (|app-23| (|append-5| "fact " |app-22|))
             (|app-24| (|append-5| |app-23| " = "))
             (|app-25| (|toString-9| |π-20|))
             (|app-26| (|append-5| |app-24| |app-25|))
             (|app-27| (|println-2| |app-26|))
             (|π-28| (%int- |?x₀-19| 1)))
         (|go-35| |n-16| |π-20| |π-28|)))))

(defun |println-2| (|η-3|)
  (%println |η-3|))

(defun |append-5| (|η-6| |η-7|)
  (%string-append |η-6| |η-7|))

(defun |toString-9| (|η-10|)
  (%to-string |η-10|))

(defun |read-12| (|η-13|)
  (%read |η-13|))

(defun |fact-15| (|n-16|)
  (|go-35| |n-16| 1 |n-16|))

(defparameter |main-31|
  (let* ((|app-32| (|println-2| "Enter a number:"))
         (|app-33| (|read-12| nil)))
     (|fact-15| |app-33|)))
