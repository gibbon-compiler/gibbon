#lang gibbon

(require "rkt-typechecker.rkt")

(let ([e : Expr
(App
 (App
  (App
   (App
    (App
     (Lam
      (CONSPARAM
       (P
        (S 'g8067)
        (Lamt
         (CONSTYPE (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Bool_)) (NULLTYPE))
         (Lamt
          (CONSTYPE (Bool_) (NULLTYPE))
          (Lamt
           (CONSTYPE
            (Lamt
             (CONSTYPE (Lamt (CONSTYPE (Bool_) (NULLTYPE)) (Int_)) (NULLTYPE))
             (Lamt (CONSTYPE (Lamt (CONSTYPE (Bool_) (NULLTYPE)) (Bool_)) (NULLTYPE)) (Bool_)))
            (NULLTYPE))
           (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Int_))))))
       (CONSPARAM
        (P (S 'g8068) (Int_))
        (CONSPARAM
         (P (S 'g8069) (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Int_)))
         (CONSPARAM
          (P (S 'g8070) (Int_))
          (CONSPARAM
           (P
            (S 'g8071)
            (Lamt (CONSTYPE (Lamt (CONSTYPE (Bool_) (NULLTYPE)) (Bool_)) (NULLTYPE)) (Int_)))
           (NULLPARAM))))))
      (Lam
       (CONSPARAM
        (P
         (S 'g8072)
         (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Lamt (CONSTYPE (Bool_) (NULLTYPE)) (Bool_))))
        (CONSPARAM
         (P (S 'g8073) (Lamt (CONSTYPE (Bool_) (NULLTYPE)) (Int_)))
         (CONSPARAM
          (P (S 'g8074) (Int_))
          (CONSPARAM
           (P (S 'g8075) (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Bool_)))
           (CONSPARAM (P (S 'g8076) (Bool_)) (NULLPARAM))))))
       (Lam
        (CONSPARAM
         (P (S 'g8077) (Int_))
         (CONSPARAM
          (P
           (S 'g8078)
           (Lamt
            (CONSTYPE
             (Lamt
              (CONSTYPE (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Int_)) (NULLTYPE))
              (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Bool_)))
             (NULLTYPE))
            (Bool_)))
          (CONSPARAM
           (P (S 'g8079) (Bool_))
           (CONSPARAM (P (S 'g8080) (Bool_)) (CONSPARAM (P (S 'g8081) (Bool_)) (NULLPARAM))))))
        (Lam
         (CONSPARAM
          (P (S 'g8082) (Bool_))
          (CONSPARAM
           (P
            (S 'g8083)
            (Lamt (CONSTYPE (Lamt (CONSTYPE (Bool_) (NULLTYPE)) (Int_)) (NULLTYPE)) (Bool_)))
           (CONSPARAM
            (P (S 'g8084) (Int_))
            (CONSPARAM (P (S 'g8085) (Bool_)) (CONSPARAM (P (S 'g8086) (Int_)) (NULLPARAM))))))
         (Lam
          (CONSPARAM
           (P (S 'g8087) (Bool_))
           (CONSPARAM
            (P (S 'g8088) (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Bool_)))
            (CONSPARAM
             (P (S 'g8089) (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Bool_)))
             (CONSPARAM
              (P (S 'g8090) (Bool_))
              (CONSPARAM
               (P
                (S 'g8091)
                (Lamt
                 (CONSTYPE (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Bool_)) (NULLTYPE))
                 (Bool_)))
               (NULLPARAM))))))
          (Begin
           (CONSEXPR
            (B #t)
            (CONSEXPR
             (N 66)
             (CONSEXPR
              (B #t)
              (CONSEXPR
               (N 71)
               (CONSEXPR
                (N 95)
                (CONSEXPR
                 (N 58)
                 (CONSEXPR
                  (B #t)
                  (CONSEXPR
                   (B #f)
                   (CONSEXPR
                    (B #f)
                    (CONSEXPR
                     (N 36)
                     (CONSEXPR
                      (B #t)
                      (CONSEXPR
                       (N 85)
                       (CONSEXPR
                        (B #t)
                        (CONSEXPR
                         (B #t)
                         (CONSEXPR
                          (N 17)
                          (CONSEXPR
                           (B #t)
                           (CONSEXPR
                            (N 99)
                            (CONSEXPR
                             (B #f)
                             (CONSEXPR
                              (B #t)
                              (CONSEXPR (B #f) (NULLEXPR)))))))))))))))))))))))))))
     (CONSEXPR
      (Lam
       (CONSPARAM (P (S 'g8092) (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Bool_))) (NULLPARAM))
       (Lam
        (CONSPARAM (P (S 'g8093) (Bool_)) (NULLPARAM))
        (Lam
         (CONSPARAM
          (P
           (S 'g8094)
           (Lamt
            (CONSTYPE (Lamt (CONSTYPE (Bool_) (NULLTYPE)) (Int_)) (NULLTYPE))
            (Lamt (CONSTYPE (Lamt (CONSTYPE (Bool_) (NULLTYPE)) (Bool_)) (NULLTYPE)) (Bool_))))
          (NULLPARAM))
         (Lam (CONSPARAM (P (S 'g8095) (Int_)) (NULLPARAM)) (N 40)))))
      (CONSEXPR
       (N 1)
       (CONSEXPR
        (Lam (CONSPARAM (P (S 'g8096) (Int_)) (NULLPARAM)) (N 31))
        (CONSEXPR
         (N 14)
         (CONSEXPR
          (Lam
           (CONSPARAM (P (S 'g8097) (Lamt (CONSTYPE (Bool_) (NULLTYPE)) (Bool_))) (NULLPARAM))
           (N 62))
          (NULLEXPR)))))))
    (CONSEXPR
     (Lam
      (CONSPARAM (P (S 'g8098) (Int_)) (NULLPARAM))
      (Lam (CONSPARAM (P (S 'g8099) (Bool_)) (NULLPARAM)) (B #t)))
     (CONSEXPR
      (Lam (CONSPARAM (P (S 'g8100) (Bool_)) (NULLPARAM)) (N 83))
      (CONSEXPR
       (N 47)
       (CONSEXPR
        (Lam (CONSPARAM (P (S 'g8101) (Int_)) (NULLPARAM)) (B #f))
        (CONSEXPR (B #t) (NULLEXPR)))))))
   (CONSEXPR
    (N 65)
    (CONSEXPR
     (Lam
      (CONSPARAM
       (P
        (S 'g8102)
        (Lamt
         (CONSTYPE (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Int_)) (NULLTYPE))
         (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Bool_))))
       (NULLPARAM))
      (B #t))
     (CONSEXPR (B #f) (CONSEXPR (B #f) (CONSEXPR (B #f) (NULLEXPR)))))))
  (CONSEXPR
   (B #f)
   (CONSEXPR
    (Lam
     (CONSPARAM (P (S 'g8103) (Lamt (CONSTYPE (Bool_) (NULLTYPE)) (Int_))) (NULLPARAM))
     (B #t))
    (CONSEXPR (N 41) (CONSEXPR (B #t) (CONSEXPR (N 6) (NULLEXPR)))))))
 (CONSEXPR
  (B #f)
  (CONSEXPR
   (Lam (CONSPARAM (P (S 'g8104) (Int_)) (NULLPARAM)) (B #t))
   (CONSEXPR
    (Lam (CONSPARAM (P (S 'g8105) (Int_)) (NULLPARAM)) (B #f))
    (CONSEXPR
     (B #f)
     (CONSEXPR
      (Lam
       (CONSPARAM (P (S 'g8106) (Lamt (CONSTYPE (Int_) (NULLTYPE)) (Bool_))) (NULLPARAM))
       (B #f))
      (NULLEXPR)))))))
])
  (iterate (test-typecheck e)))
   ;; (Begin (CONSEXPR e (CONSEXPR e (CONSEXPR e
   ;; 					    (CONSEXPR e (CONSEXPR e (CONSEXPR e (NULLEXPR))))))))


