;; == System F IR ==

let i_C_0 : C Int = C@Int fun x : Int => x

let i_D_0 : D Int = D@Int fun x : Int => x

let i_C_1 : ∀a [C a, D a], C (Box a) =
  Λ a.
    fun d_D_1 : D a =>
      C@(Box a)
        fun ?x₀ : Box a =>
          match ?x₀ with
          | Box x => d_D_1[0, d]@a x

let i_D_1 : ∀a [C a, D a], D (Box a) =
  Λ a.
    fun d_C_0 : C a =>
      D@(Box a)
        fun ?x₀ : Box a =>
          match ?x₀ with
          | Box x => d_C_0[0, c]@a x

let main : Int =
  let rd_C_0 : C Int = i_C_0
  and rd_D_1 : D Int = i_D_0
  and rd_C_2 : C (Box Int) = Λ α. i_C_1@Int rd_C_0 rd_D_1
  and rd_D_3 : D (Box Int) = Λ α. i_D_1@Int rd_C_0 rd_D_1
  and rd_C_4 : C (Box (Box Int)) = Λ α. i_C_1@(Box Int) rd_C_2 rd_D_3
  and rd_D_5 : D (Box (Box Int)) = Λ α. i_D_1@(Box Int) rd_C_2 rd_D_3
  and rd_C_6 : C (Box (Box (Box Int))) =
    Λ α. i_C_1@(Box (Box Int)) rd_C_4 rd_D_5
  and rd_D_7 : D (Box (Box (Box Int))) =
    Λ α. i_D_1@(Box (Box Int)) rd_C_4 rd_D_5
  and rd_C_8 : C (Box (Box (Box (Box Int)))) =
    Λ α. i_C_1@(Box (Box (Box Int))) rd_C_6 rd_D_7
  and rd_D_9 : D (Box (Box (Box (Box Int)))) =
    Λ α. i_D_1@(Box (Box (Box Int))) rd_C_6 rd_D_7
  and rd_C_10 : C (Box (Box (Box (Box (Box Int))))) =
    Λ α. i_C_1@(Box (Box (Box (Box Int)))) rd_C_8 rd_D_9
  and rd_D_11 : D (Box (Box (Box (Box (Box Int))))) =
    Λ α. i_D_1@(Box (Box (Box (Box Int)))) rd_C_8 rd_D_9
  and rd_C_12 : C (Box (Box (Box (Box (Box (Box Int)))))) =
    Λ α. i_C_1@(Box (Box (Box (Box (Box Int))))) rd_C_10 rd_D_11
  and rd_D_13 : D (Box (Box (Box (Box (Box (Box Int)))))) =
    Λ α. i_D_1@(Box (Box (Box (Box (Box Int))))) rd_C_10 rd_D_11
  and rd_C_14 : C (Box (Box (Box (Box (Box (Box (Box Int))))))) =
    Λ α. i_C_1@(Box (Box (Box (Box (Box (Box Int)))))) rd_C_12 rd_D_13
  and rd_D_15 : D (Box (Box (Box (Box (Box (Box (Box Int))))))) =
    Λ α. i_D_1@(Box (Box (Box (Box (Box (Box Int)))))) rd_C_12 rd_D_13
  and rd_C_16 : C (Box (Box (Box (Box (Box (Box (Box (Box Int)))))))) =
    Λ α. i_C_1@(Box (Box (Box (Box (Box (Box (Box Int))))))) rd_C_14 rd_D_15
  and rd_D_17 : D (Box (Box (Box (Box (Box (Box (Box (Box Int)))))))) =
    Λ α. i_D_1@(Box (Box (Box (Box (Box (Box (Box Int))))))) rd_C_14 rd_D_15
  and rd_C_18 : C (Box (Box (Box (Box (Box (Box (Box (Box (Box Int))))))))) =
    Λ α.
      i_C_1@(Box (Box (Box (Box (Box (Box (Box (Box Int)))))))) rd_C_16 rd_D_17
  and rd_D_19 : D (Box (Box (Box (Box (Box (Box (Box (Box (Box Int))))))))) =
    Λ α.
      i_D_1@(Box (Box (Box (Box (Box (Box (Box (Box Int)))))))) rd_C_16 rd_D_17
  and rd_C_20
    : C (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box Int)))))))))) =
    Λ α.
      i_C_1@(Box (Box (Box (Box (Box (Box (Box (Box (Box Int))))))))) rd_C_18
        rd_D_19
  and rd_D_21
    : D (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box Int)))))))))) =
    Λ α.
      i_D_1@(Box (Box (Box (Box (Box (Box (Box (Box (Box Int))))))))) rd_C_18
        rd_D_19
  and rd_C_22
    : C (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box Int))))))))))) =
    Λ α.
      i_C_1@(Box (Box (Box (Box (Box (Box (Box (Box (Box (Box Int))))))))))
        rd_C_20
        rd_D_21
  and rd_D_23
    : D (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box Int))))))))))) =
    Λ α.
      i_D_1@(Box (Box (Box (Box (Box (Box (Box (Box (Box (Box Int))))))))))
        rd_C_20
        rd_D_21
  and rd_C_24
    : C
      (Box
         (Box
            (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box Int)))))))))))) =
    Λ α.
      i_C_1@(Box
         (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box Int)))))))))))
        rd_C_22
        rd_D_23
  and rd_D_25
    : D
      (Box
         (Box
            (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box Int)))))))))))) =
    Λ α.
      i_D_1@(Box
         (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box Int)))))))))))
        rd_C_22
        rd_D_23
  and rd_C_26
    : C
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box (Box (Box (Box (Box (Box (Box (Box Int))))))))))))) =
    Λ α.
      i_C_1@(Box
         (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box Int))))))))))))
        rd_C_24
        rd_D_25
  and rd_D_27
    : D
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box (Box (Box (Box (Box (Box (Box (Box Int))))))))))))) =
    Λ α.
      i_D_1@(Box
         (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box (Box Int))))))))))))
        rd_C_24
        rd_D_25
  and rd_C_28
    : C
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box (Box (Box (Box (Box (Box Int)))))))))))))) =
    Λ α.
      i_C_1@(Box
         (Box
            (Box
               (Box
                  (Box (Box (Box (Box (Box (Box (Box (Box (Box Int)))))))))))))
        rd_C_26
        rd_D_27
  and rd_D_29
    : D
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box (Box (Box (Box (Box (Box Int)))))))))))))) =
    Λ α.
      i_D_1@(Box
         (Box
            (Box
               (Box
                  (Box (Box (Box (Box (Box (Box (Box (Box (Box Int)))))))))))))
        rd_C_26
        rd_D_27
  and rd_C_30
    : C
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box (Box (Box (Box Int))))))))))))))) =
    Λ α.
      i_C_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box (Box (Box (Box (Box (Box (Box Int))))))))))))))
        rd_C_28
        rd_D_29
  and rd_D_31
    : D
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box (Box (Box (Box Int))))))))))))))) =
    Λ α.
      i_D_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box (Box (Box (Box (Box (Box (Box Int))))))))))))))
        rd_C_28
        rd_D_29
  and rd_C_32
    : C
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box (Box Int)))))))))))))))) =
    Λ α.
      i_C_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box (Box (Box (Box (Box Int)))))))))))))))
        rd_C_30
        rd_D_31
  and rd_D_33
    : D
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box (Box Int)))))))))))))))) =
    Λ α.
      i_D_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box (Box (Box (Box (Box Int)))))))))))))))
        rd_C_30
        rd_D_31
  and rd_C_34
    : C
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         Int))))))))))))))))) =
    Λ α.
      i_C_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box (Box (Box Int))))))))))))))))
        rd_C_32
        rd_D_33
  and rd_D_35
    : D
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         Int))))))))))))))))) =
    Λ α.
      i_D_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box (Box (Box Int))))))))))))))))
        rd_C_32
        rd_D_33
  and rd_C_36
    : C
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            Int)))))))))))))))))) =
    Λ α.
      i_C_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box Int)))))))))))))))))
        rd_C_34
        rd_D_35
  and rd_D_37
    : D
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            Int)))))))))))))))))) =
    Λ α.
      i_D_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box Int)))))))))))))))))
        rd_C_34
        rd_D_35
  and rd_C_38
    : C
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            (Box
                                                               Int))))))))))))))))))) =
    Λ α.
      i_C_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            Int))))))))))))))))))
        rd_C_36
        rd_D_37
  and rd_D_39
    : D
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            (Box
                                                               Int))))))))))))))))))) =
    Λ α.
      i_D_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            Int))))))))))))))))))
        rd_C_36
        rd_D_37
  and rd_C_40
    : C
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            (Box
                                                               (Box
                                                                  Int)))))))))))))))))))) =
    Λ α.
      i_C_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            (Box
                                                               Int)))))))))))))))))))
        rd_C_38
        rd_D_39
  and rd_D_41
    : D
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            (Box
                                                               (Box
                                                                  Int)))))))))))))))))))) =
    Λ α.
      i_D_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            (Box
                                                               Int)))))))))))))))))))
        rd_C_38
        rd_D_39
  and rd_C_42
    : C
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            (Box
                                                               (Box
                                                                  (Box
                                                                     Int))))))))))))))))))))) =
    Λ α.
      i_C_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            (Box
                                                               (Box
                                                                  Int))))))))))))))))))))
        rd_C_40
        rd_D_41
  and rd_D_43
    : D
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            (Box
                                                               (Box
                                                                  (Box
                                                                     Int))))))))))))))))))))) =
    Λ α.
      i_D_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            (Box
                                                               (Box
                                                                  Int))))))))))))))))))))
        rd_C_40
        rd_D_41
  and rd_C_44
    : C
      (Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            (Box
                                                               (Box
                                                                  (Box
                                                                     (Box
                                                                        Int)))))))))))))))))))))) =
    Λ α.
      i_C_1@(Box
         (Box
            (Box
               (Box
                  (Box
                     (Box
                        (Box
                           (Box
                              (Box
                                 (Box
                                    (Box
                                       (Box
                                          (Box
                                             (Box
                                                (Box
                                                   (Box
                                                      (Box
                                                         (Box
                                                            (Box
                                                               (Box
                                                                  (Box
                                                                     Int)))))))))))))))))))))
        rd_C_42
        rd_D_43
  in rd_C_44[0, c]@(Box
        (Box
           (Box
              (Box
                 (Box
                    (Box
                       (Box
                          (Box
                             (Box
                                (Box
                                   (Box
                                      (Box
                                         (Box
                                            (Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int))))))))))))))))))))))
       (Box@(Box
           (Box
              (Box
                 (Box
                    (Box
                       (Box
                          (Box
                             (Box
                                (Box
                                   (Box
                                      (Box
                                         (Box
                                            (Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int)))))))))))))))))))))
          (Box@(Box
              (Box
                 (Box
                    (Box
                       (Box
                          (Box
                             (Box
                                (Box
                                   (Box
                                      (Box
                                         (Box
                                            (Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int))))))))))))))))))))
             (Box@(Box
                 (Box
                    (Box
                       (Box
                          (Box
                             (Box
                                (Box
                                   (Box
                                      (Box
                                         (Box
                                            (Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int)))))))))))))))))))
                (Box@(Box
                    (Box
                       (Box
                          (Box
                             (Box
                                (Box
                                   (Box
                                      (Box
                                         (Box
                                            (Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int))))))))))))))))))
                   (Box@(Box
                       (Box
                          (Box
                             (Box
                                (Box
                                   (Box
                                      (Box
                                         (Box
                                            (Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int)))))))))))))))))
                      (Box@(Box
                          (Box
                             (Box
                                (Box
                                   (Box
                                      (Box
                                         (Box
                                            (Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int))))))))))))))))
                         (Box@(Box
                             (Box
                                (Box
                                   (Box
                                      (Box
                                         (Box
                                            (Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int)))))))))))))))
                            (Box@(Box
                                (Box
                                   (Box
                                      (Box
                                         (Box
                                            (Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int))))))))))))))
                               (Box@(Box
                                   (Box
                                      (Box
                                         (Box
                                            (Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int)))))))))))))
                                  (Box@(Box
                                      (Box
                                         (Box
                                            (Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int))))))))))))
                                     (Box@(Box
                                         (Box
                                            (Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int)))))))))))
                                        (Box@(Box
                                            (Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int))))))))))
                                           (Box@(Box
                                               (Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int)))))))))
                                              (Box@(Box
                                                  (Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int))))))))
                                                 (Box@(Box
                                                     (Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int)))))))
                                                    (Box@(Box
                                                        (Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int))))))
                                                       (Box@(Box
                                                           (Box
                                                              (Box
                                                                 (Box
                                                                    (Box
                                                                       Int)))))
                                                          (Box@(Box
                                                              (Box
                                                                 (Box
                                                                    (Box Int))))
                                                             (Box@(Box
                                                                 (Box
                                                                    (Box Int)))
                                                                (Box@(Box
                                                                    (Box Int))
                                                                   (Box@(Box
                                                                       Int)
                                                                      (Box@Int
                                                                         1))))))))))))))))))))))
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
(declaim (ftype (function (integer) integer) |fn-137|))

(declaim (ftype (function (integer) integer) |fn-138|))

(declaim (ftype (function (t t) integer) |fn-139|))

(declaim (ftype (function (t t) integer) |fn-140|))

(declaim (ftype (function (t) clos) |i_D_1-18|))

(declaim (type integer |main-26|))

; body
(defun |fn-137| (|x-4|)
  |x-4|)

(defun |fn-138| (|x-8|)
  |x-8|)

(defun |fn-139| (|d_D_1-11| |?x₀-13|)
  (gapply1 |d_D_1-11| |?x₀-13|))

(defun |fn-140| (|d_C_0-19| |?x₀-21|)
  (gapply1 |d_C_0-19| |?x₀-21|))

(defun |i_C_1-10| (|d_D_1-11|)
  (%clos (lambda (|g0|)
      (|fn-139| |d_D_1-11| |g0|))
    1))

(defun |i_D_1-18| (|d_C_0-19|)
  (%clos (lambda (|g1|)
      (|fn-140| |d_C_0-19| |g1|))
    1))

(defparameter |i_C_0-2|
  (%clos (function |fn-137|) 1))

(defparameter |i_D_0-6|
  (%clos (function |fn-138|) 1))

(defparameter |main-26|
  (let* ((|app-27| (|i_C_1-10| |i_C_0-2|))
         (|app-28| (gapply1 |app-27| |i_D_0-6|))
         (|app-29| (|i_D_1-18| |i_C_0-2|))
         (|app-30| (gapply1 |app-29| |i_D_0-6|))
         (|app-31| (|i_C_1-10| |app-28|))
         (|app-32| (gapply1 |app-31| |app-30|))
         (|app-33| (|i_D_1-18| |app-28|))
         (|app-34| (gapply1 |app-33| |app-30|))
         (|app-35| (|i_C_1-10| |app-32|))
         (|app-36| (gapply1 |app-35| |app-34|))
         (|app-37| (|i_D_1-18| |app-32|))
         (|app-38| (gapply1 |app-37| |app-34|))
         (|app-39| (|i_C_1-10| |app-36|))
         (|app-40| (gapply1 |app-39| |app-38|))
         (|app-41| (|i_D_1-18| |app-36|))
         (|app-42| (gapply1 |app-41| |app-38|))
         (|app-43| (|i_C_1-10| |app-40|))
         (|app-44| (gapply1 |app-43| |app-42|))
         (|app-45| (|i_D_1-18| |app-40|))
         (|app-46| (gapply1 |app-45| |app-42|))
         (|app-47| (|i_C_1-10| |app-44|))
         (|app-48| (gapply1 |app-47| |app-46|))
         (|app-49| (|i_D_1-18| |app-44|))
         (|app-50| (gapply1 |app-49| |app-46|))
         (|app-51| (|i_C_1-10| |app-48|))
         (|app-52| (gapply1 |app-51| |app-50|))
         (|app-53| (|i_D_1-18| |app-48|))
         (|app-54| (gapply1 |app-53| |app-50|))
         (|app-55| (|i_C_1-10| |app-52|))
         (|app-56| (gapply1 |app-55| |app-54|))
         (|app-57| (|i_D_1-18| |app-52|))
         (|app-58| (gapply1 |app-57| |app-54|))
         (|app-59| (|i_C_1-10| |app-56|))
         (|app-60| (gapply1 |app-59| |app-58|))
         (|app-61| (|i_D_1-18| |app-56|))
         (|app-62| (gapply1 |app-61| |app-58|))
         (|app-63| (|i_C_1-10| |app-60|))
         (|app-64| (gapply1 |app-63| |app-62|))
         (|app-65| (|i_D_1-18| |app-60|))
         (|app-66| (gapply1 |app-65| |app-62|))
         (|app-67| (|i_C_1-10| |app-64|))
         (|app-68| (gapply1 |app-67| |app-66|))
         (|app-69| (|i_D_1-18| |app-64|))
         (|app-70| (gapply1 |app-69| |app-66|))
         (|app-71| (|i_C_1-10| |app-68|))
         (|app-72| (gapply1 |app-71| |app-70|))
         (|app-73| (|i_D_1-18| |app-68|))
         (|app-74| (gapply1 |app-73| |app-70|))
         (|app-75| (|i_C_1-10| |app-72|))
         (|app-76| (gapply1 |app-75| |app-74|))
         (|app-77| (|i_D_1-18| |app-72|))
         (|app-78| (gapply1 |app-77| |app-74|))
         (|app-79| (|i_C_1-10| |app-76|))
         (|app-80| (gapply1 |app-79| |app-78|))
         (|app-81| (|i_D_1-18| |app-76|))
         (|app-82| (gapply1 |app-81| |app-78|))
         (|app-83| (|i_C_1-10| |app-80|))
         (|app-84| (gapply1 |app-83| |app-82|))
         (|app-85| (|i_D_1-18| |app-80|))
         (|app-86| (gapply1 |app-85| |app-82|))
         (|app-87| (|i_C_1-10| |app-84|))
         (|app-88| (gapply1 |app-87| |app-86|))
         (|app-89| (|i_D_1-18| |app-84|))
         (|app-90| (gapply1 |app-89| |app-86|))
         (|app-91| (|i_C_1-10| |app-88|))
         (|app-92| (gapply1 |app-91| |app-90|))
         (|app-93| (|i_D_1-18| |app-88|))
         (|app-94| (gapply1 |app-93| |app-90|))
         (|app-95| (|i_C_1-10| |app-92|))
         (|app-96| (gapply1 |app-95| |app-94|))
         (|app-97| (|i_D_1-18| |app-92|))
         (|app-98| (gapply1 |app-97| |app-94|))
         (|app-99| (|i_C_1-10| |app-96|))
         (|app-100| (gapply1 |app-99| |app-98|))
         (|app-101| (|i_D_1-18| |app-96|))
         (|app-102| (gapply1 |app-101| |app-98|))
         (|app-103| (|i_C_1-10| |app-100|))
         (|app-104| (gapply1 |app-103| |app-102|))
         (|app-105| (|i_D_1-18| |app-100|))
         (|app-106| (gapply1 |app-105| |app-102|))
         (|app-107| (|i_C_1-10| |app-104|))
         (|app-108| (gapply1 |app-107| |app-106|))
         (|app-109| (|i_D_1-18| |app-104|))
         (|app-110| (gapply1 |app-109| |app-106|))
         (|app-111| (|i_C_1-10| |app-108|))
         (|app-112| (gapply1 |app-111| |app-110|))
         (|con-114| 1))
     (gapply1 |app-112| |con-114|)))
