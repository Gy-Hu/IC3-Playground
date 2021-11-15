(declare-rel Invariant (Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool))
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
(declare-var F3 Bool)
(declare-var G3 Bool)
(declare-var H3 Bool)
(declare-var I3 Bool)
(declare-var J3 Bool)
(rule (=> false (Invariant A B C D E F G H I J K L M N O P Q R S T U V W X Y Z A1)))
(rule (let ((a!1 (and (not (and B C)) (not (and M2 (not C)))))
      (a!2 (and (not (and T C)) (not (and Q2 (not C)))))
      (a!3 (and (not (and L C)) (not (and K2 (not C)))))
      (a!7 (and (not (and D C)) (not (and G2 (not C)))))
      (a!9 (and (not (and E C)) (not (and N2 (not C)))))
      (a!10 (and (not (and U C)) (not (and R2 (not C)))))
      (a!14 (and (not H3) (or (and F C) (and H2 (not C)))))
      (a!15 (and (not (and G C)) (not (and O2 (not C)))))
      (a!16 (and (not (and V C)) (not (and S2 (not C)))))
      (a!20 (and (not H3) (or (and H C) (and I2 (not C)))))
      (a!21 (and (not (and I C)) (not (and P2 (not C)))))
      (a!22 (and (not (and W C)) (not (and T2 (not C)))))
      (a!26 (and (not H3) (or (and J C) (and J2 (not C)))))
      (a!27 (and (not (and K C)) (not (and L2 (not C)))))
      (a!30 (= O1 (or (and F C) (and H2 (not C)))))
      (a!31 (= P1 (or (and H C) (and I2 (not C)))))
      (a!32 (= Q1 (or (and J C) (and J2 (not C)))))
      (a!33 (and (not (and X C)) (not (and V2 (not C)))))
      (a!35 (and (not (and Y C)) (not (and W2 (not C)))))
      (a!37 (and (not (and Z C)) (not (and X2 (not C)))))
      (a!45 (and (not (and I C))
                 (not (and P2 (not C)))
                 (not (and K C))
                 (not (and L2 (not C)))))
      (a!47 (and (not (and A1 C)) (not (and U2 (not C)))))
      (a!53 (and (not (and E C))
                 (not (and N2 (not C)))
                 (or (and F C) (and H2 (not C)))))
      (a!54 (not (or (and F C) (and H2 (not C)))))
      (a!55 (and (not (and G C))
                 (not (and O2 (not C)))
                 (or (and H C) (and I2 (not C)))))
      (a!56 (not (or (and H C) (and I2 (not C)))))
      (a!57 (and (not (and I C))
                 (not (and P2 (not C)))
                 (or (and J C) (and J2 (not C)))))
      (a!58 (not (or (and J C) (and J2 (not C))))))
(let ((a!4 (and (not a!1) (not (and L C)) (not (and K2 (not C)))))
      (a!8 (= E1 (or (and H3 Z2) (and (not H3) (not a!7)))))
      (a!11 (and (not a!9) (not (and L C)) (not (and K2 (not C)))))
      (a!17 (and (not a!15) (not (and L C)) (not (and K2 (not C)))))
      (a!23 (and (not a!21) (not (and L C)) (not (and K2 (not C)))))
      (a!28 (= L1 (or (and H3 (not a!27)) (and (not H3) Y2))))
      (a!29 (= M1 (or (and H3 (not a!3)) (and (not H3) (not a!27)))))
      (a!34 (= U1 (or (and H3 (not a!2)) (and (not H3) (not a!33)))))
      (a!36 (= V1 (or (and H3 (not a!10)) (and (not H3) (not a!35)))))
      (a!38 (= W1 (or (and H3 (not a!16)) (and (not H3) (not a!37)))))
      (a!39 (and (not a!9) (not (and K C)) (not (and L2 (not C)))))
      (a!42 (and (not a!15) (not (and K C)) (not (and L2 (not C)))))
      (a!46 (= A2 (or (and H3 (not a!37)) (and (not H3) (not a!45)))))
      (a!48 (and (not a!1) (not (and K C)) (not (and L2 (not C)))))
      (a!51 (and (not (and B C)) (not (and M2 (not C))) (not a!7)))
      (a!52 (and (not a!1) (not (and D C)) (not (and G2 (not C))))))
(let ((a!5 (and (not (and (not a!2) (not a!3))) (not a!4)))
      (a!12 (and (not (and (not a!10) (not a!3))) (not a!11)))
      (a!18 (and (not (and (not a!16) (not a!3))) (not a!17)))
      (a!24 (and (not (and (not a!22) (not a!3))) (not a!23)))
      (a!40 (and (not (and (not a!35) (not a!27))) (not a!39)))
      (a!43 (and (not (and (not a!37) (not a!27))) (not a!42)))
      (a!49 (and (not (and (not a!33) (not a!27))) (not a!48)))
      (a!59 (and (not a!51)
                 (not a!52)
                 (not a!53)
                 (not (and (not a!9) a!54))
                 (not a!55)
                 (not (and (not a!15) a!56))
                 (not a!57)
                 (not (and (not a!21) a!58)))))
(let ((a!6 (= C1 (or (and H3 (not a!1)) (and (not H3) (not a!5)))))
      (a!13 (= F1 (or (and H3 (not a!9)) (and (not H3) (not a!12)))))
      (a!19 (= H1 (or (and H3 (not a!15)) (and (not H3) (not a!18)))))
      (a!25 (= J1 (or (and H3 (not a!21)) (and (not H3) (not a!24)))))
      (a!41 (= Y1 (or (and H3 (not a!33)) (and (not H3) (not a!40)))))
      (a!44 (= Z1 (or (and H3 (not a!35)) (and (not H3) (not a!43)))))
      (a!50 (= B2 (or (and H3 (not a!47)) (and (not H3) (not a!49))))))
(let ((a!60 (and (Invariant A B C D E F G H I J K L M N O P Q R S T U V W X Y Z A1)
                 (= B1 (and (not H3) R))
                 a!6
                 D1
                 a!8
                 a!13
                 (= G1 (or (and H3 A3) a!14))
                 a!19
                 (= I1 (or (and H3 B3) a!20))
                 a!25
                 (= K1 (or (and H3 C3) a!26))
                 a!28
                 a!29
                 (= N1 (and (not H3) A))
                 a!30
                 a!31
                 a!32
                 R1
                 (= S1 (and (not H3) (not S)))
                 (= T1 (not H3))
                 a!34
                 a!36
                 a!38
                 (= X1 (or (not H3) (not a!22)))
                 a!41
                 a!44
                 a!46
                 a!50
                 A
                 (not a!59)
                 (not (and K C))
                 (not (and L2 (not C)))
                 (not a!3)
                 (not Y2))))
  (=> a!60
      (Invariant B1
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
           X1
           Y1
           Z1
           A2
           B2))))))))
(rule (let ((a!1 (and (not (and W2 H3)) (not (and H1 (not H3)))))
      (a!3 (and (not (and I3 H3)) (not (and X (not H3)))))
      (a!5 (and (not (and V2 H3)) (not (and G1 (not H3)))))
      (a!7 (and (not (and F3 H3)) (not (and W (not H3)))))
      (a!9 (and (not (and U2 H3)) (not (and F1 (not H3)))))
      (a!11 (and (not (and D3 H3)) (not (and V (not H3)))))
      (a!13 (and (not (and T2 H3)) (not (and E1 (not H3)))))
      (a!15 (and (not (and B3 H3)) (not (and U (not H3)))))
      (a!17 (and (not (and G3 H3)) (not (and D1 (not H3)))))
      (a!20 (and (not (and F3 H3))
                 (not (and W (not H3)))
                 (or (and E3 H3) (and C1 (not H3)))))
      (a!21 (not (or (and E3 H3) (and C1 (not H3)))))
      (a!22 (and (not (and D3 H3))
                 (not (and V (not H3)))
                 (or (and C3 H3) (and B1 (not H3)))))
      (a!23 (not (or (and C3 H3) (and B1 (not H3)))))
      (a!24 (and (not (and B3 H3))
                 (not (and U (not H3)))
                 (or (and A3 H3) (and A1 (not H3)))))
      (a!25 (not (or (and A3 H3) (and A1 (not H3)))))
      (a!27 (and (not (and Y2 H3)) (not (and Z (not H3))))))
(let ((a!2 (and (not (and I3 H3)) (not (and X (not H3))) (not a!1)))
      (a!4 (and (not a!3) (not (and W2 H3)) (not (and H1 (not H3)))))
      (a!6 (and (not (and F3 H3)) (not (and W (not H3))) (not a!5)))
      (a!8 (and (not a!7) (not (and V2 H3)) (not (and G1 (not H3)))))
      (a!10 (and (not (and D3 H3)) (not (and V (not H3))) (not a!9)))
      (a!12 (and (not a!11) (not (and U2 H3)) (not (and F1 (not H3)))))
      (a!14 (and (not (and B3 H3)) (not (and U (not H3))) (not a!13)))
      (a!16 (and (not a!15) (not (and T2 H3)) (not (and E1 (not H3)))))
      (a!18 (and (not (and I3 H3)) (not (and X (not H3))) (not a!17)))
      (a!19 (and (not a!3) (not (and G3 H3)) (not (and D1 (not H3))))))
(let ((a!26 (and (not a!18)
                 (not a!19)
                 (not a!20)
                 (not (and (not a!7) a!21))
                 (not a!22)
                 (not (and (not a!11) a!23))
                 (not a!24)
                 (not (and (not a!15) a!25)))))
(let ((a!28 (and (Invariant J3
                      I3
                      H3
                      G3
                      F3
                      E3
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
                      J2)
                 X2
                 (not (and (not a!2)
                           (not a!4)
                           (not a!6)
                           (not a!8)
                           (not a!10)
                           (not a!12)
                           (not a!14)
                           (not a!16)))
                 J3
                 (not a!26)
                 (not (and Z2 H3))
                 (not (and Y (not H3)))
                 (not a!27)
                 (not L))))
  (=> a!28 Goal))))))
(query Goal)
