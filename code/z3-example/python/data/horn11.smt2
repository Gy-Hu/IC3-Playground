(declare-rel k!0 ())
(declare-rel Invariant (Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool))
(declare-rel Goal ())
(declare-var A Bool)
(declare-var B Bool)
(declare-var C Bool)
(declare-var D Bool)
(declare-var E Bool)
(declare-var F Bool)
(declare-var G Bool)
(declare-var H Bool)
(declare-var I Bool)
(declare-var J Bool)
(declare-var K Bool)
(declare-var L Bool)
(declare-var M Bool)
(declare-var N Bool)
(declare-var O Bool)
(declare-var P Bool)
(declare-var Q Bool)
(declare-var R Bool)
(declare-var S Bool)
(declare-var T Bool)
(declare-var U Bool)
(declare-var V Bool)
(declare-var W Bool)
(declare-var X Bool)
(declare-var Y Bool)
(declare-var Z Bool)
(declare-var A1 Bool)
(declare-var B1 Bool)
(declare-var C1 Bool)
(declare-var D1 Bool)
(declare-var E1 Bool)
(declare-var F1 Bool)
(declare-var G1 Bool)
(declare-var H1 Bool)
(declare-var I1 Bool)
(declare-var J1 Bool)
(declare-var K1 Bool)
(declare-var L1 Bool)
(declare-var M1 Bool)
(declare-var N1 Bool)
(declare-var O1 Bool)
(declare-var P1 Bool)
(declare-var Q1 Bool)
(declare-var R1 Bool)
(declare-var S1 Bool)
(declare-var T1 Bool)
(declare-var U1 Bool)
(declare-var V1 Bool)
(declare-var W1 Bool)
(declare-var X1 Bool)
(declare-var Y1 Bool)
(declare-var Z1 Bool)
(declare-var A2 Bool)
(declare-var B2 Bool)
(declare-var C2 Bool)
(declare-var D2 Bool)
(declare-var E2 Bool)
(declare-var F2 Bool)
(declare-var G2 Bool)
(declare-var H2 Bool)
(declare-var I2 Bool)
(declare-var J2 Bool)
(declare-var K2 Bool)
(declare-var L2 Bool)
(declare-var M2 Bool)
(declare-var N2 Bool)
(declare-var O2 Bool)
(declare-var P2 Bool)
(declare-var Q2 Bool)
(declare-var R2 Bool)
(declare-var S2 Bool)
(declare-var T2 Bool)
(declare-var U2 Bool)
(declare-var V2 Bool)
(declare-var W2 Bool)
(declare-var X2 Bool)
(declare-var Y2 Bool)
(declare-var Z2 Bool)
(declare-var A3 Bool)
(declare-var B3 Bool)
(declare-var C3 Bool)
(declare-var D3 Bool)
(declare-var E3 Bool)
(rule (=> (not (or A B C D E F G H I J K L M N O P Q R S T U V W X Y))
    (Invariant A B C D E F G H I J K L M N O P Q R S T U V W X Y)))
(rule (let ((a!1 (and (not (and (not A) R2)) (not (and A C))))
      (a!3 (and (not (and (not A) W2)) (not (and A K))))
      (a!4 (and (not (and (not A) N2)) (not (and A L))))
      (a!7 (and (not (and (not A) X2)) (not (and A M))))
      (a!8 (and (not (and (not A) S2)) (not (and A E))))
      (a!10 (and (not (and (not A) O2)) (not (and A N))))
      (a!13 (and (not (and (not A) Y2)) (not (and A O))))
      (a!14 (and (not (and (not A) T2)) (not (and A G))))
      (a!16 (and (not (and (not A) P2)) (not (and A P))))
      (a!19 (and (not (and (not A) Z2)) (not (and A Q))))
      (a!20 (and (not (and (not A) U2)) (not (and A I))))
      (a!22 (and (not (and (not A) Q2)) (not (and A R))))
      (a!25 (and (not (and (not A) V2)) (not (and A T))))
      (a!27 (and (not (and (not A) N2)) (not (and A L)) Z1))
      (a!29 (and (not (and (not A) J2)) (not (and A U))))
      (a!32 (and (not (and (not A) K2)) (not (and A V))))
      (a!35 (and (not (and (not A) L2)) (not (and A W))))
      (a!38 (and (not (and (not A) V2))
                 (not (and A T))
                 (not (and (not A) R2))
                 (not (and A C)))))
(let ((a!2 (and (not (and (not A) W2)) (not (and A K)) (not a!1)))
      (a!9 (and (not (and (not A) W2)) (not (and A K)) (not a!8)))
      (a!15 (and (not (and (not A) W2)) (not (and A K)) (not a!14)))
      (a!21 (and (not (and (not A) W2)) (not (and A K)) (not a!20)))
      (a!26 (and (not (and (not a!25) (not Z1))) (not (and (not a!3) Z1))))
      (a!28 (and (not (and (not a!7) (not Z1))) (not (and E2 Z1))))
      (a!30 (and (not (and (not a!29) (not Z1))) (not (and (not a!10) Z1))))
      (a!31 (and (not (and (not a!13) (not Z1))) (not (and F2 Z1))))
      (a!33 (and (not (and (not a!32) (not Z1))) (not (and (not a!16) Z1))))
      (a!34 (and (not (and (not a!19) (not Z1))) (not (and G2 Z1))))
      (a!36 (and (not (and (not a!35) (not Z1))) (not (and (not a!22) Z1))))
      (a!37 (and (not (and I2 (not Z1))) (not (and (not a!25) Z1))))
      (a!39 (and (not (and (not a!38) (not Z1))) (not (and (not a!29) Z1))))
      (a!40 (and (not (and (not A) V2)) (not (and A T)) (not a!8)))
      (a!43 (and (not (and (not A) V2)) (not (and A T)) (not a!14))))
(let ((a!5 (and (not a!2) (not (and (not a!3) (not a!4)))))
      (a!11 (and (not a!9) (not (and (not a!3) (not a!10)))))
      (a!17 (and (not a!15) (not (and (not a!3) (not a!16)))))
      (a!23 (and (not a!21) (not (and (not a!3) (not a!22)))))
      (a!41 (and (not a!40) (not (and (not a!25) (not a!29)))))
      (a!44 (and (not a!43) (not (and (not a!25) (not a!32))))))
(let ((a!6 (and (not (and (not a!5) (not Z1))) (not (and (not a!1) Z1))))
      (a!12 (and (not (and (not a!11) (not Z1))) (not (and (not a!8) Z1))))
      (a!18 (and (not (and (not a!17) (not Z1))) (not (and (not a!14) Z1))))
      (a!24 (and (not (and (not a!23) (not Z1))) (not (and (not a!20) Z1))))
      (a!42 (and (not (and (not a!41) (not Z1))) (not (and (not a!32) Z1))))
      (a!45 (and (not (and (not a!44) (not Z1))) (not (and (not a!35) Z1)))))
(let ((a!46 (and (Invariant A B C D E F G H I J K L M N O P Q R S T U V W X Y)
                 Z
                 A1
                 (= B1 (not a!6))
                 (= C1 (not a!7))
                 (= D1 (not a!12))
                 (= E1 (not a!13))
                 (= F1 (not a!18))
                 (= G1 (not a!19))
                 (= H1 (not a!24))
                 (= I1 (and S (not Z1)))
                 (= J1 (not a!26))
                 (= K1 (not a!27))
                 (= L1 (not a!28))
                 (= M1 (not a!30))
                 (= N1 (not a!31))
                 (= O1 (not a!33))
                 (= P1 (not a!34))
                 (= Q1 (not a!36))
                 (= R1 (and X (not Z1)))
                 (= S1 (not a!37))
                 (= T1 (not a!39))
                 (= U1 (not a!42))
                 (= V1 (not a!45))
                 (= W1 (and (not Y) (not Z1)))
                 (= X1 (not Z1)))))
  (=> a!46
      (Invariant Z
           A1
           B1
           C1
           D1
           E1
           F1
           G1
           H1
           I1
           J1
           K1
           L1
           M1
           N1
           O1
           P1
           Q1
           R1
           S1
           T1
           U1
           V1
           W1
           X1))))))))
(rule (=> (and (Invariant E3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2)
         k!0)
    Goal))
(query Goal)
