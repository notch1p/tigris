;; == System F IR ==

let (::) : ∀α, α → List α → List α = Λ α. Cons@α

let reverse/go : ∀α, List α → List α → List α =
  Λ α.
    rec fun reverse/go : List α → List α → List α =>
      fun acc : List α =>
        fun ?x₀ : List α =>
          match ?x₀ with
          | Cons x xs => reverse/go xs (Cons@α x acc)
          | _ => acc
and reverse : ∀α, List α → List α =
  Λ α.
    rec fun reverse : List α → List α =>
      fun xs : List α => reverse/go@α xs Nil@α

let foo : List Bool × List String =
  let 😋 : Bool = true
  and 😱 : Bool = false
  and f : (∀α, List α → List α) → List Bool × List String =
    fun x : ∀α, List α → List α =>
      ⟨x (Cons@Bool 😋 (Cons@Bool 😱 Nil@Bool)),
       x (Cons@String "😋" (Cons@String "😱" Nil@String))⟩
  in f reverse@?sk.20
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
(defstruct (|List| (:conc-name |List/|) (:constructor nil) (:predicate nil))
  (|tag| 0 :type (unsigned-byte 8)))

(defstruct (|c/Nil| (:include |List| (|tag| 0))
  (:conc-name |Nil/|)
  (:constructor |mk/Nil| ())
  (:predicate |Nil?|)))

(defstruct (|c/Cons| (:include |List| (|tag| 1))
  (:conc-name |Cons/|)
  (:constructor |mk/Cons| (|f0| |f1|))
  (:predicate |Cons?|))
  (|f0| nil)
  (|f1| nil))

; gapply
(defun gapply1 (c a1)
  (if (eql (clos-arity c) 1)
    (funcall (clos-fn c) a1)
    (%apply-slow c (list a1))))

; ftype
(declaim (ftype (function (boolean boolean clos) cons) |fn-29|))

(declaim (ftype (function (|List| |List|) |List|) |reverse/go-2|))

(declaim (ftype (function (|List|) |List|) |reverse-3|))

(declaim (type cons |foo-13|))

(declaim (type null |main-28|))

; body
(defun |fn-29| (|v-14| |v-15| |x-17|)
  (let* ((|con-18| (|mk/Nil|))
         (|con-19| (|mk/Cons| |v-15| |con-18|))
         (|con-20| (|mk/Cons| |v-14| |con-19|))
         (|app-21| (gapply1 |x-17| |con-20|))
         (|con-22| (|mk/Nil|))
         (|con-23| (|mk/Cons| "😱" |con-22|))
         (|con-24| (|mk/Cons| "😋" |con-23|))
         (|app-25| (gapply1 |x-17| |con-24|)))
     (cons |app-21| |app-25|)))

(defun |reverse/go-2| (|acc-4| |?x₀-5|)
  (case (|List/tag| |?x₀-5|)
    (1
      (let* ((|f-6| (|Cons/f0| |?x₀-5|))
             (|f-7| (|Cons/f1| |?x₀-5|)))
         (let* ((|con-8| (|mk/Cons| |f-6| |acc-4|)))
            (|reverse/go-2| |f-7| |con-8|))))
    (t |acc-4|)))

(defun |reverse-3| (|xs-10|)
  (let* ((|con-11| (|mk/Nil|))) (|reverse/go-2| |xs-10| |con-11|)))

(defparameter |foo-13|
  (let* ((|v-14| t)
         (|v-15| nil))
     (|fn-29| |v-14| |v-15| (%clos (function |reverse-3|) 1))))

(defparameter |main-28|
  nil)
