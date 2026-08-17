;; == TCNF CC & Optimize'd ==

let fn#12/1 (x#5 : ?sk.a) : ?sk.a → ?sk.a = ret #5

let fn#13/1 (g#9 : a → a) : (∀a, a → a) → Int =
  let app#10 : Int = #9(1); ret #10

let apply2#2/1 (h#3 : (∀a, a → a) → Int) : ((∀a, a → a) → Int) → Int =
  let fn#4 : ?sk.a → ?sk.a = 𝐂⟦12⟧; let app#6 : Int = #3(#4); ret #6

let main#7/0 : Int =
  let fn#8 : (∀a, a → a) → Int = 𝐂⟦13⟧; let app#11 : Int = #2(#8); ret #11
;; == Runtime ==
(load "runtime.lisp")

;; == Linked Lisp Source ==
(load "ffi.lisp")

;; == Common Lisp ==

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

; ftype
(declaim (ftype (function (clos) integer) |fn-13|))

(declaim (ftype (function (clos) integer) |apply2-2|))

(declaim (type integer |main-7|))

; body
(defun |fn-12| (|x-5|)
  |x-5|)

(defun |fn-13| (|g-9|)
  (gapply1 |g-9| 1))

(defun |apply2-2| (|h-3|)
  (let* ((|fn-4| (%clos (function |fn-12|) 1))) (gapply1 |h-3| |fn-4|)))

(defparameter |main-7|
  (let* ((|fn-8| (%clos (function |fn-13|) 1))) (|apply2-2| |fn-8|)))
