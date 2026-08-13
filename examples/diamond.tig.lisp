;; == System F IR ==

let i_C_0 : C Int = C@Int fun x : Int => x

let i_D_0 : D Int = D@Int fun x : Int => x

let i_C_1 : [C a, D a] C (Box a) =
  Λ a.
    fun d_D_1 : D a =>
      C@(Box a)
        fun ?x₀ : Box a =>
          match ?x₀ with
          | Box x => d_D_1[0, d]@a x

let i_D_1 : [C a, D a] D (Box a) =
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
