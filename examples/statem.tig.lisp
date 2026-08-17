;; == System F IR ==

let i_Monad_0 : ∀s, Monad (Λa. s → s × a) =
  Λ s.
    Monad@(Λa. s → s × a) Λ a. fun x : a => fun st : s => ⟨st, x⟩
      Λ a b.
        fun m : s → s × a =>
          fun f : a → s → s × b =>
            fun st : s =>
              match m st with
              | (st2, x) => f x st2

let main : Int × Int =
  let rd_Monad_0 : Monad (Λa. Int → Int × Int) = i_Monad_0@Int
  and rd_Monad_1 : Monad (Λa. Int → Int × a) = i_Monad_0@Int
  in rd_Monad_0[1, bind]@(Λa. Int → Int × Int)
       (rd_Monad_0[0, pure]@(Λa. Int → Int × Int) 1)
       fun x : Int => rd_Monad_1[0, pure]@(Λa. Int → Int × a) (add x 1)
       42
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


; struct
(defstruct (|Monad| (:conc-name |Monad/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Monad| (:include |Monad| (|tag| 0))
  (:conc-name |Monad/|)
  (:constructor |mk/Monad| (|f0| |f1|))
  (:predicate |Monad?|))
  (|f0| nil)
  (|f1| nil))

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
(declaim (ftype (function (t t) cons) |fn-26|))

(declaim (ftype (function (clos clos t) cons) |fn-27|))

(declaim (ftype (function (integer) clos) |fn-28|))

(declaim (type |Monad| |i_Monad_0-2|))

(declaim (type cons |main-16|))

; body
(defun |fn-26| (|x-4| |st-5|)
  (cons |st-5| |x-4|))

(defun |fn-27| (|m-8| |f-9| |st-10|)
  (let* ((|app-11| (gapply1 |m-8| |st-10|))
         (|fst-12| (car |app-11|))
         (|snd-13| (cdr |app-11|)))
     (gapply2 |f-9| |snd-13| |fst-12|)))

(defun |fn-28| (|x-21|)
  (let* ((|π-23| (%int+ |x-21| 1)))
     (%clos (lambda (|g0|)
         (|fn-26| |π-23| |g0|))
       1)))

(defparameter |i_Monad_0-2|
  (let* ((|fn-3| (%clos (function |fn-26|) 2))
         (|fn-7| (%clos (function |fn-27|) 3)))
     (|mk/Monad| |fn-3| |fn-7|)))

(defparameter |main-16|
  (let* ((|app-19| (%clos (lambda (|g1|)
               (|fn-26| 1 |g1|))
             1))
         (|fn-20| (%clos (function |fn-28|) 1)))
     (|fn-27| |app-19| |fn-20| 42)))

(format t "~S~%" |main-16|)
