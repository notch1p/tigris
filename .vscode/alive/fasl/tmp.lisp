;; == System F IR ==

let main : Int → Int → Int =
  fun ?x₀ : Int => fun ?x₁ : Int => add ?x₀ (div (mul 1 2) ?x₁)
;; == Runtime ==
(load "runtime.lisp")

;; == Linked Lisp Source ==
(load "ffi.lisp")

