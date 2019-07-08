#lang gibbon

(require "rkt-typechecker.rkt")

;(let ([e : Expr (Lam (CONSPARAM (P (S 'g) (Bool_)) (NULLPARAM)) (B True))])
;  (test-typecheck e))

;(let ([e : Expr (App
;  (Lam
;   (CONSPARAM
;    (P (S 'g19857) (Int_))
;    (CONSPARAM
;     (P (S 'g19858) (Int_))
;     (NULLPARAM)))
;   (B True))
;  (CONSEXPR
;   (N 6)
;   (CONSEXPR (N 8) (NULLEXPR))))])
;  (test-typecheck e))

(let ([e : Expr (App
  (Lam
   (CONSPARAM
    (P (S 'g23657) (NullT))
    (CONSPARAM
     (P (S 'g23658) (NullT))
     (NULLPARAM)))
   (App
    (Lam
     (NULLPARAM)
     (App
      (Lam
       (NULLPARAM)
       (App
        (Lam
         (NULLPARAM)
         (App
          (Lam (NULLPARAM) (Null))
          (NULLEXPR)))
        (NULLEXPR)))
      (NULLEXPR)))
    (NULLEXPR)))
  (CONSEXPR
   (App
    (Lam
     (CONSPARAM
      (P (S 'g23659) (NullT))
      (NULLPARAM))
     (App
      (Lam
       (CONSPARAM
        (P (S 'g23660) (NullT))
        (CONSPARAM
         (P (S 'g23661) (Bool_))
         (CONSPARAM
          (P (S 'g23662) (Int_))
          (CONSPARAM
           (P (S 'g23663) (Int_))
           (NULLPARAM)))))
       (App
        (Lam
         (CONSPARAM
          (P (S 'g23664) (NullT))
          (CONSPARAM
           (P (S 'g23665) (Int_))
           (NULLPARAM)))
         (App
          (Lam
           (CONSPARAM
            (P (S 'g23666) (NullT))
            (CONSPARAM
             (P (S 'g23667) (Bool_))
             (CONSPARAM
              (P (S 'g23668) (Int_))
              (NULLPARAM))))
           (N 5))
          (CONSEXPR
           (Null)
           (CONSEXPR
            (B False)
            (CONSEXPR
             (N 4)
             (NULLEXPR))))))
        (CONSEXPR
         (App
          (Lam
           (CONSPARAM
            (P (S 'g23669) (Int_))
            (CONSPARAM
             (P (S 'g23670) (NullT))
             (NULLPARAM)))
           (Null))
          (CONSEXPR
           (N 1)
           (CONSEXPR (Null) (NULLEXPR))))
         (CONSEXPR
          (App
           (Lam
            (CONSPARAM
             (P (S 'g23671) (Int_))
             (CONSPARAM
              (P (S 'g23672) (Int_))
              (NULLPARAM)))
            (N 1))
           (CONSEXPR
            (N 5)
            (CONSEXPR (N 1) (NULLEXPR))))
          (NULLEXPR)))))
      (CONSEXPR
       (App
        (Lam
         (CONSPARAM
          (P (S 'g23673) (NullT))
          (CONSPARAM
           (P (S 'g23674) (Int_))
           (CONSPARAM
            (P (S 'g23675) (Bool_))
            (NULLPARAM))))
         (App
          (Lam
           (CONSPARAM
            (P (S 'g23676) (Int_))
            (CONSPARAM
             (P (S 'g23677) (Int_))
             (CONSPARAM
              (P (S 'g23678) (NullT))
              (CONSPARAM
               (P (S 'g23679) (Int_))
               (NULLPARAM)))))
           (B True))
          (CONSEXPR
           (N 2)
           (CONSEXPR
            (N 7)
            (CONSEXPR
             (Null)
             (CONSEXPR
              (N 4)
              (NULLEXPR)))))))
        (CONSEXPR
         (App
          (Lam (NULLPARAM) (N 0))
          (NULLEXPR))
         (CONSEXPR
          (App
           (Lam (NULLPARAM) (N 7))
           (NULLEXPR))
          (CONSEXPR
           (App
            (Lam
             (CONSPARAM
              (P (S 'g23680) (Bool_))
              (CONSPARAM
               (P (S 'g23681) (Int_))
               (CONSPARAM
                (P (S 'g23682) (Int_))
                (NULLPARAM))))
             (Null))
            (CONSEXPR
             (B False)
             (CONSEXPR
              (N 3)
              (CONSEXPR
               (N 6)
               (NULLEXPR)))))
           (NULLEXPR)))))
       (CONSEXPR
        (App
         (Lam
          (CONSPARAM
           (P (S 'g23683) (Int_))
           (CONSPARAM
            (P (S 'g23684) (Bool_))
            (CONSPARAM
             (P (S 'g23685) (NullT))
             (NULLPARAM))))
          (App
           (Lam
            (CONSPARAM
             (P (S 'g23686) (NullT))
             (CONSPARAM
              (P (S 'g23687) (Int_))
              (CONSPARAM
               (P (S 'g23688) (Bool_))
               (CONSPARAM
                (P (S 'g23689) (Bool_))
                (NULLPARAM)))))
            (N 5))
           (CONSEXPR
            (Null)
            (CONSEXPR
             (N 7)
             (CONSEXPR
              (B True)
              (CONSEXPR
               (B False)
               (NULLEXPR)))))))
         (CONSEXPR
          (App
           (Lam (NULLPARAM) (Null))
           (NULLEXPR))
          (CONSEXPR
           (App
            (Lam
             (CONSPARAM
              (P (S 'g23690) (Int_))
              (CONSPARAM
               (P (S 'g23691) (Bool_))
               (CONSPARAM
                (P (S 'g23692) (Bool_))
                (NULLPARAM))))
             (Null))
            (CONSEXPR
             (N 3)
             (CONSEXPR
              (B False)
              (CONSEXPR
               (B False)
               (NULLEXPR)))))
           (CONSEXPR
            (App
             (Lam (NULLPARAM) (Null))
             (NULLEXPR))
            (NULLEXPR)))))
        (CONSEXPR
         (App
          (Lam
           (CONSPARAM
            (P (S 'g23693) (Bool_))
            (CONSPARAM
             (P (S 'g23694) (NullT))
             (CONSPARAM
              (P (S 'g23695) (Bool_))
              (CONSPARAM
               (P (S 'g23696) (NullT))
               (NULLPARAM)))))
           (App
            (Lam
             (CONSPARAM
              (P (S 'g23697) (Bool_))
              (CONSPARAM
               (P (S 'g23698) (Int_))
               (CONSPARAM
                (P (S 'g23699) (NullT))
                (CONSPARAM
                 (P (S 'g23700) (Int_))
                 (NULLPARAM)))))
             (Null))
            (CONSEXPR
             (B True)
             (CONSEXPR
              (N 8)
              (CONSEXPR
               (Null)
               (CONSEXPR
                (N 9)
                (NULLEXPR)))))))
          (CONSEXPR
           (App
            (Lam
             (CONSPARAM
              (P (S 'g23701) (NullT))
              (CONSPARAM
               (P (S 'g23702) (Bool_))
               (NULLPARAM)))
             (Null))
            (CONSEXPR
             (Null)
             (CONSEXPR
              (B False)
              (NULLEXPR))))
           (CONSEXPR
            (App
             (Lam
              (CONSPARAM
               (P (S 'g23703) (NullT))
               (CONSPARAM
                (P (S 'g23704) (Int_))
                (NULLPARAM)))
              (N 3))
             (CONSEXPR
              (Null)
              (CONSEXPR
               (N 4)
               (NULLEXPR))))
            (CONSEXPR
             (App
              (Lam (NULLPARAM) (Null))
              (NULLEXPR))
             (CONSEXPR
              (App
               (Lam (NULLPARAM) (N 1))
               (NULLEXPR))
              (NULLEXPR))))))
         (CONSEXPR
          (App
           (Lam
            (NULLPARAM)
            (App
             (Lam
              (CONSPARAM
               (P (S 'g23705) (NullT))
               (CONSPARAM
                (P (S 'g23706) (Bool_))
                (CONSPARAM
                 (P (S 'g23707) (Int_))
                 (NULLPARAM))))
              (N 9))
             (CONSEXPR
              (Null)
              (CONSEXPR
               (B False)
               (CONSEXPR
                (N 3)
                (NULLEXPR))))))
           (NULLEXPR))
          (NULLEXPR)))))))
    (CONSEXPR
     (App
      (Lam
       (CONSPARAM
        (P (S 'g23708) (Bool_))
        (CONSPARAM
         (P (S 'g23709) (Bool_))
         (CONSPARAM
          (P (S 'g23710) (Bool_))
          (CONSPARAM
           (P (S 'g23711) (Bool_))
           (NULLPARAM)))))
       (App
        (Lam
         (NULLPARAM)
         (App
          (Lam
           (CONSPARAM
            (P (S 'g23712) (NullT))
            (CONSPARAM
             (P (S 'g23713) (NullT))
             (NULLPARAM)))
           (N 5))
          (CONSEXPR
           (Null)
           (CONSEXPR
            (Null)
            (NULLEXPR)))))
        (NULLEXPR)))
      (CONSEXPR
       (App
        (Lam
         (NULLPARAM)
         (App
          (Lam
           (CONSPARAM
            (P (S 'g23714) (NullT))
            (CONSPARAM
             (P (S 'g23715) (Int_))
             (NULLPARAM)))
           (Null))
          (CONSEXPR
           (Null)
           (CONSEXPR (N 5) (NULLEXPR)))))
        (NULLEXPR))
       (CONSEXPR
        (App
         (Lam
          (CONSPARAM
           (P (S 'g23716) (NullT))
           (CONSPARAM
            (P (S 'g23717) (NullT))
            (CONSPARAM
             (P (S 'g23718) (NullT))
             (CONSPARAM
              (P (S 'g23719) (Bool_))
              (NULLPARAM)))))
          (App
           (Lam (NULLPARAM) (Null))
           (NULLEXPR)))
         (CONSEXPR
          (App
           (Lam
            (CONSPARAM
             (P (S 'g23720) (Bool_))
             (CONSPARAM
              (P (S 'g23721) (NullT))
              (CONSPARAM
               (P (S 'g23722) (Bool_))
               (CONSPARAM
                (P (S 'g23723) (Bool_))
                (NULLPARAM)))))
            (N 0))
           (CONSEXPR
            (B False)
            (CONSEXPR
             (Null)
             (CONSEXPR
              (B False)
              (CONSEXPR
               (B False)
               (NULLEXPR))))))
          (CONSEXPR
           (App
            (Lam
             (CONSPARAM
              (P (S 'g23724) (NullT))
              (NULLPARAM))
             (N 9))
            (CONSEXPR (Null) (NULLEXPR)))
           (CONSEXPR
            (App
             (Lam
              (CONSPARAM
               (P (S 'g23725) (Int_))
               (NULLPARAM))
              (Null))
             (CONSEXPR (N 0) (NULLEXPR)))
            (CONSEXPR
             (App
              (Lam
               (CONSPARAM
                (P (S 'g23726) (Bool_))
                (NULLPARAM))
               (N 8))
              (CONSEXPR
               (B True)
               (NULLEXPR)))
             (NULLEXPR))))))
        (CONSEXPR
         (App
          (Lam
           (CONSPARAM
            (P (S 'g23727) (Bool_))
            (NULLPARAM))
           (App
            (Lam (NULLPARAM) (B True))
            (NULLEXPR)))
          (CONSEXPR
           (App
            (Lam
             (CONSPARAM
              (P (S 'g23728) (Bool_))
              (CONSPARAM
               (P (S 'g23729) (Int_))
               (NULLPARAM)))
             (N 0))
            (CONSEXPR
             (B False)
             (CONSEXPR
              (N 6)
              (NULLEXPR))))
           (NULLEXPR)))
         (CONSEXPR
          (App
           (Lam
            (CONSPARAM
             (P (S 'g23730) (Int_))
             (CONSPARAM
              (P (S 'g23731) (Int_))
              (CONSPARAM
               (P (S 'g23732) (NullT))
               (NULLPARAM))))
            (App
             (Lam
              (CONSPARAM
               (P (S 'g23733) (Bool_))
               (CONSPARAM
                (P (S 'g23734) (NullT))
                (CONSPARAM
                 (P (S 'g23735) (Bool_))
                 (CONSPARAM
                  (P (S 'g23736) (NullT))
                  (NULLPARAM)))))
              (N 5))
             (CONSEXPR
              (B True)
              (CONSEXPR
               (Null)
               (CONSEXPR
                (B True)
                (CONSEXPR
                 (Null)
                 (NULLEXPR)))))))
           (CONSEXPR
            (App
             (Lam
              (CONSPARAM
               (P (S 'g23737) (NullT))
               (CONSPARAM
                (P (S 'g23738) (Bool_))
                (NULLPARAM)))
              (N 5))
             (CONSEXPR
              (Null)
              (CONSEXPR
               (B True)
               (NULLEXPR))))
            (CONSEXPR
             (App
              (Lam
               (CONSPARAM
                (P (S 'g23739) (Bool_))
                (CONSPARAM
                 (P (S 'g23740) (Bool_))
                 (NULLPARAM)))
               (N 2))
              (CONSEXPR
               (B False)
               (CONSEXPR
                (B True)
                (NULLEXPR))))
             (CONSEXPR
              (App
               (Lam
                (CONSPARAM
                 (P (S 'g23741) (Int_))
                 (CONSPARAM
                  (P (S 'g23742) (Bool_))
                  (NULLPARAM)))
                (Null))
               (CONSEXPR
                (N 8)
                (CONSEXPR
                 (B False)
                 (NULLEXPR))))
              (NULLEXPR)))))
          (NULLEXPR))))))
     (NULLEXPR)))
   (CONSEXPR
    (App
     (Lam
      (CONSPARAM
       (P (S 'g23743) (Int_))
       (NULLPARAM))
      (App
       (Lam
        (CONSPARAM
         (P (S 'g23744) (Bool_))
         (CONSPARAM
          (P (S 'g23745) (NullT))
          (CONSPARAM
           (P (S 'g23746) (Bool_))
           (NULLPARAM))))
        (App
         (Lam
          (CONSPARAM
           (P (S 'g23747) (NullT))
           (CONSPARAM
            (P (S 'g23748) (NullT))
            (CONSPARAM
             (P (S 'g23749) (NullT))
             (CONSPARAM
              (P (S 'g23750) (Int_))
              (NULLPARAM)))))
          (App
           (Lam
            (CONSPARAM
             (P (S 'g23751) (Bool_))
             (NULLPARAM))
            (N 0))
           (CONSEXPR
            (B False)
            (NULLEXPR))))
         (CONSEXPR
          (App
           (Lam
            (CONSPARAM
             (P (S 'g23752) (Int_))
             (NULLPARAM))
            (N 6))
           (CONSEXPR (N 5) (NULLEXPR)))
          (CONSEXPR
           (App
            (Lam
             (CONSPARAM
              (P (S 'g23753) (NullT))
              (CONSPARAM
               (P (S 'g23754) (Bool_))
               (CONSPARAM
                (P (S 'g23755) (NullT))
                (NULLPARAM))))
             (B False))
            (CONSEXPR
             (Null)
             (CONSEXPR
              (B False)
              (CONSEXPR
               (Null)
               (NULLEXPR)))))
           (CONSEXPR
            (App
             (Lam
              (CONSPARAM
               (P (S 'g23756) (Bool_))
               (NULLPARAM))
              (Null))
             (CONSEXPR
              (B True)
              (NULLEXPR)))
            (CONSEXPR
             (App
              (Lam
               (CONSPARAM
                (P (S 'g23757) (NullT))
                (CONSPARAM
                 (P (S 'g23758) (NullT))
                 (CONSPARAM
                  (P (S 'g23759) (Bool_))
                  (NULLPARAM))))
               (B True))
              (CONSEXPR
               (Null)
               (CONSEXPR
                (Null)
                (CONSEXPR
                 (B False)
                 (NULLEXPR)))))
             (NULLEXPR)))))))
       (CONSEXPR
        (App
         (Lam
          (NULLPARAM)
          (App
           (Lam (NULLPARAM) (N 3))
           (NULLEXPR)))
         (NULLEXPR))
        (CONSEXPR
         (App
          (Lam
           (CONSPARAM
            (P (S 'g23760) (Bool_))
            (NULLPARAM))
           (App
            (Lam
             (CONSPARAM
              (P (S 'g23761) (Bool_))
              (CONSPARAM
               (P (S 'g23762) (Int_))
               (CONSPARAM
                (P (S 'g23763) (Bool_))
                (NULLPARAM))))
             (B False))
            (CONSEXPR
             (B False)
             (CONSEXPR
              (N 6)
              (CONSEXPR
               (B True)
               (NULLEXPR))))))
          (CONSEXPR
           (App
            (Lam
             (CONSPARAM
              (P (S 'g23764) (Bool_))
              (CONSPARAM
               (P (S 'g23765) (NullT))
               (CONSPARAM
                (P (S 'g23766) (Bool_))
                (CONSPARAM
                 (P (S 'g23767) (NullT))
                 (NULLPARAM)))))
             (Null))
            (CONSEXPR
             (B False)
             (CONSEXPR
              (Null)
              (CONSEXPR
               (B False)
               (CONSEXPR
                (Null)
                (NULLEXPR))))))
           (NULLEXPR)))
         (CONSEXPR
          (App
           (Lam
            (CONSPARAM
             (P (S 'g23768) (Bool_))
             (CONSPARAM
              (P (S 'g23769) (Bool_))
              (CONSPARAM
               (P (S 'g23770) (NullT))
               (NULLPARAM))))
            (App
             (Lam
              (CONSPARAM
               (P (S 'g23771) (Bool_))
               (CONSPARAM
                (P (S 'g23772) (Int_))
                (CONSPARAM
                 (P (S 'g23773) (Bool_))
                 (NULLPARAM))))
              (Null))
             (CONSEXPR
              (B False)
              (CONSEXPR
               (N 3)
               (CONSEXPR
                (B False)
                (NULLEXPR))))))
           (CONSEXPR
            (App
             (Lam
              (CONSPARAM
               (P (S 'g23774) (Int_))
               (CONSPARAM
                (P (S 'g23775) (NullT))
                (CONSPARAM
                 (P (S 'g23776) (NullT))
                 (NULLPARAM))))
              (N 7))
             (CONSEXPR
              (N 4)
              (CONSEXPR
               (Null)
               (CONSEXPR
                (Null)
                (NULLEXPR)))))
            (CONSEXPR
             (App
              (Lam
               (CONSPARAM
                (P (S 'g23777) (Int_))
                (CONSPARAM
                 (P (S 'g23778) (Bool_))
                 (NULLPARAM)))
               (Null))
              (CONSEXPR
               (N 5)
               (CONSEXPR
                (B True)
                (NULLEXPR))))
             (CONSEXPR
              (App
               (Lam
                (CONSPARAM
                 (P (S 'g23779) (Int_))
                 (CONSPARAM
                  (P (S 'g23780) (NullT))
                  (NULLPARAM)))
                (Null))
               (CONSEXPR
                (N 2)
                (CONSEXPR
                 (Null)
                 (NULLEXPR))))
              (NULLEXPR)))))
          (NULLEXPR))))))
     (CONSEXPR
      (App
       (Lam
        (CONSPARAM
         (P (S 'g23781) (NullT))
         (CONSPARAM
          (P (S 'g23782) (NullT))
          (NULLPARAM)))
        (App
         (Lam
          (NULLPARAM)
          (App
           (Lam
            (CONSPARAM
             (P (S 'g23783) (Int_))
             (CONSPARAM
              (P (S 'g23784) (Bool_))
              (CONSPARAM
               (P (S 'g23785) (Int_))
               (CONSPARAM
                (P (S 'g23786) (Bool_))
                (NULLPARAM)))))
            (Null))
           (CONSEXPR
            (N 7)
            (CONSEXPR
             (B True)
             (CONSEXPR
              (N 8)
              (CONSEXPR
               (B True)
               (NULLEXPR)))))))
         (NULLEXPR)))
       (CONSEXPR
        (App
         (Lam
          (CONSPARAM
           (P (S 'g23787) (Int_))
           (NULLPARAM))
          (App
           (Lam
            (CONSPARAM
             (P (S 'g23788) (NullT))
             (CONSPARAM
              (P (S 'g23789) (Int_))
              (NULLPARAM)))
            (B False))
           (CONSEXPR
            (Null)
            (CONSEXPR
             (N 2)
             (NULLEXPR)))))
         (CONSEXPR
          (App
           (Lam
            (CONSPARAM
             (P (S 'g23790) (NullT))
             (NULLPARAM))
            (B False))
           (CONSEXPR (Null) (NULLEXPR)))
          (NULLEXPR)))
        (CONSEXPR
         (App
          (Lam
           (CONSPARAM
            (P (S 'g23791) (NullT))
            (NULLPARAM))
           (App
            (Lam
             (CONSPARAM
              (P (S 'g23792) (Int_))
              (CONSPARAM
               (P (S 'g23793) (NullT))
               (NULLPARAM)))
             (N 9))
            (CONSEXPR
             (N 3)
             (CONSEXPR
              (Null)
              (NULLEXPR)))))
          (CONSEXPR
           (App
            (Lam
             (CONSPARAM
              (P (S 'g23794) (Bool_))
              (CONSPARAM
               (P (S 'g23795) (Int_))
               (CONSPARAM
                (P (S 'g23796) (Int_))
                (CONSPARAM
                 (P (S 'g23797) (Bool_))
                 (NULLPARAM)))))
             (Null))
            (CONSEXPR
             (B False)
             (CONSEXPR
              (N 0)
              (CONSEXPR
               (N 9)
               (CONSEXPR
                (B True)
                (NULLEXPR))))))
           (NULLEXPR)))
         (NULLEXPR))))
      (NULLEXPR)))
    (NULLEXPR))))])
  (test-typecheck e))
