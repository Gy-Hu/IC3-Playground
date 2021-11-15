(declare-rel Goal ())
(declare-rel Invariant (Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool))
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
(declare-var K3 Bool)
(declare-var L3 Bool)
(declare-var M3 Bool)
(declare-var N3 Bool)
(declare-var O3 Bool)
(declare-var P3 Bool)
(declare-var Q3 Bool)
(declare-var R3 Bool)
(declare-var S3 Bool)
(declare-var T3 Bool)
(declare-var U3 Bool)
(declare-var V3 Bool)
(declare-var W3 Bool)
(declare-var X3 Bool)
(declare-var Y3 Bool)
(declare-var Z3 Bool)
(declare-var A4 Bool)
(declare-var B4 Bool)
(declare-var C4 Bool)
(declare-var D4 Bool)
(declare-var E4 Bool)
(declare-var F4 Bool)
(declare-var G4 Bool)
(declare-var H4 Bool)
(declare-var I4 Bool)
(declare-var J4 Bool)
(declare-var K4 Bool)
(declare-var L4 Bool)
(declare-var M4 Bool)
(rule (=> (not (or A B C D E F G H I J K L M N O P Q R S T U V W X Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 K1 L1 M1 N1 O1 P1 Q1 R1 S1 T1 U1 V1 W1 X1 Y1 Z1 A2 B2 C2))
    (Invariant A
         B
         C
         D
         E
         F
         G
         H
         I
         J
         K
         L
         M
         N
         O
         P
         Q
         R
         S
         T
         U
         V
         W
         X
         Y
         Z
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
         X1
         Y1
         Z1
         A2
         B2
         C2)))
(rule (let ((a!1 (and (not H4) (not (and (not G4) (not I1)))))
      (a!2 (and (not L4) (not (and (not H4) (not C2)))))
      (a!6 (and (not L4) (not (and (not G4) (not B2)))))
      (a!8 (and (not J4) (not (and (not I4) (not R)))))
      (a!9 (and (not K4) (not (and (not J4) (not Z1)))))
      (a!13 (and (not K4) (not (and (not I4) (not A2)))))
      (a!15 (and C2 (not (and B2 (not I1)))))
      (a!16 (and Z1 (not (and A2 (not R)))))
      (a!17 (and L4 (not (and (not H4) (not G4) (not K4) (not J4) (not I4)))))
      (a!18 (and H4 (not (and (not G4) (not K4) (not J4) (not I4)))))
      (a!19 (and G4 (not (and (not K4) (not J4) (not I4)))))
      (a!20 (and K4 (not (and (not J4) (not I4)))))
      (a!21 (and L C D E F (not (and (not I) (not J)))))
      (a!25 (and (not (and K4 Y1)) (not (and (not K4) B))))
      (a!27 (and (not (and K4 Q1)) (not (and (not K4) C))))
      (a!29 (and (not (and K4 P1)) (not (and (not K4) D))))
      (a!31 (and (not (and K4 O1)) (not (and (not K4) E))))
      (a!33 (and (not (and K4 N1)) (not (and (not K4) F))))
      (a!35 (and (not (and K4 J1)) (not (and (not K4) (not G)))))
      (a!37 (and (not (and K4 K1)) (not (and (not K4) H))))
      (a!39 (and (not (and K4 M1)) (not (and (not K4) I))))
      (a!41 (and (not (and K4 L1)) (not (and (not K4) J))))
      (a!43 (and (not (and K4 S1)) (not (and (not K4) K))))
      (a!45 (and (not (and K4 R1)) (not (and (not K4) L))))
      (a!47 (and (not (and K4 T1)) (not (and (not K4) M))))
      (a!49 (and (not (and K4 U1)) (not (and (not K4) N))))
      (a!51 (and (not (and K4 V1)) (not (and (not K4) O))))
      (a!53 (and (not (and K4 W1)) (not (and (not K4) P))))
      (a!55 (and (not (and K4 X1)) (not (and (not K4) Q))))
      (a!57 (and (not (and G4 (not G))) (not (and (not G4) S))))
      (a!58 (and H4 (not (and (not G) S)) (not (and G (not S)))))
      (a!60 (and (not (and G4 H)) (not (and (not G4) T))))
      (a!61 (and (not G) S (not (and H T)) (not (and (not H) (not T)))))
      (a!62 (and (not (and H T)) (not (and (not H) (not T)))))
      (a!65 (and (not (and G4 J)) (not (and (not G4) U))))
      (a!68 (and (not (and J U)) (not (and (not J) (not U)))))
      (a!71 (and (not (and G4 I)) (not (and (not G4) V))))
      (a!74 (and (not (and I V)) (not (and (not I) (not V)))))
      (a!77 (and (not (and G4 F)) (not (and (not G4) W))))
      (a!80 (and (not (and F W)) (not (and (not F) (not W)))))
      (a!83 (and (not (and G4 E)) (not (and (not G4) X))))
      (a!86 (and (not (and E X)) (not (and (not E) (not X)))))
      (a!89 (and (not (and G4 D)) (not (and (not G4) Y))))
      (a!92 (and (not (and D Y)) (not (and (not D) (not Y)))))
      (a!95 (and (not (and G4 C)) (not (and (not G4) Z))))
      (a!98 (and (not (and C Z)) (not (and (not C) (not Z)))))
      (a!101 (and (not (and G4 L)) (not (and (not G4) A1))))
      (a!104 (and (not (and L A1)) (not (and (not L) (not A1)))))
      (a!107 (and (not (and G4 K)) (not (and (not G4) B1))))
      (a!110 (and (not (and K B1)) (not (and (not K) (not B1)))))
      (a!113 (and (not (and G4 M)) (not (and (not G4) C1))))
      (a!116 (and (not (and M C1)) (not (and (not M) (not C1)))))
      (a!119 (and (not (and G4 N)) (not (and (not G4) D1))))
      (a!122 (and (not (and N D1)) (not (and (not N) (not D1)))))
      (a!125 (and (not (and G4 O)) (not (and (not G4) E1))))
      (a!128 (and (not (and O E1)) (not (and (not O) (not E1)))))
      (a!131 (and (not (and G4 P)) (not (and (not G4) F1))))
      (a!134 (and (not (and P F1)) (not (and (not P) (not F1)))))
      (a!137 (and (not (and G4 Q)) (not (and (not G4) G1))))
      (a!140 (and (not (and Q G1)) (not (and (not Q) (not G1)))))
      (a!143 (and (not (and G4 B)) (not (and (not G4) H1))))
      (a!146 (and (not (and B H1)) (not (and (not B) (not H1)))))
      (a!149 (and (not (and I4 (not G))) (not (and (not I4) J1))))
      (a!150 (and J4 (not (and J1 (not G))) (not (and (not J1) G))))
      (a!152 (and (not (and I4 H)) (not (and (not I4) K1))))
      (a!153 (and J1 (not G) (not (and K1 H)) (not (and (not K1) (not H)))))
      (a!154 (and (not (and K1 H)) (not (and (not K1) (not H)))))
      (a!157 (and (not (and I4 J)) (not (and (not I4) L1))))
      (a!160 (and (not (and L1 J)) (not (and (not L1) (not J)))))
      (a!163 (and (not (and I4 I)) (not (and (not I4) M1))))
      (a!166 (and (not (and M1 I)) (not (and (not M1) (not I)))))
      (a!169 (and (not (and I4 F)) (not (and (not I4) N1))))
      (a!172 (and (not (and N1 F)) (not (and (not N1) (not F)))))
      (a!175 (and (not (and I4 E)) (not (and (not I4) O1))))
      (a!178 (and (not (and O1 E)) (not (and (not O1) (not E)))))
      (a!181 (and (not (and I4 D)) (not (and (not I4) P1))))
      (a!184 (and (not (and P1 D)) (not (and (not P1) (not D)))))
      (a!187 (and (not (and I4 C)) (not (and (not I4) Q1))))
      (a!190 (and (not (and Q1 C)) (not (and (not Q1) (not C)))))
      (a!193 (and (not (and I4 L)) (not (and (not I4) R1))))
      (a!196 (and (not (and R1 L)) (not (and (not R1) (not L)))))
      (a!199 (and (not (and I4 K)) (not (and (not I4) S1))))
      (a!202 (and (not (and S1 K)) (not (and (not S1) (not K)))))
      (a!205 (and (not (and I4 M)) (not (and (not I4) T1))))
      (a!208 (and (not (and T1 M)) (not (and (not T1) (not M)))))
      (a!211 (and (not (and I4 N)) (not (and (not I4) U1))))
      (a!214 (and (not (and U1 N)) (not (and (not U1) (not N)))))
      (a!217 (and (not (and I4 O)) (not (and (not I4) V1))))
      (a!220 (and (not (and V1 O)) (not (and (not V1) (not O)))))
      (a!223 (and (not (and I4 P)) (not (and (not I4) W1))))
      (a!226 (and (not (and W1 P)) (not (and (not W1) (not P)))))
      (a!229 (and (not (and I4 Q)) (not (and (not I4) X1))))
      (a!232 (and (not (and X1 Q)) (not (and (not X1) (not Q)))))
      (a!235 (and (not (and I4 B)) (not (and (not I4) Y1))))
      (a!238 (and (not (and Y1 B)) (not (and (not Y1) (not B))))))
(let ((a!3 (and (not a!1) (not L4) (not (and (not G4) (not B2))) (not a!2)))
      (a!4 (and (not a!1) (not L4) (not (and (not G4) (not B2)))))
      (a!7 (and (not H4) (not (and (not G4) (not I1))) (not a!6)))
      (a!10 (and (not a!8) (not K4) (not (and (not I4) (not A2))) (not a!9)))
      (a!11 (and (not a!8) (not K4) (not (and (not I4) (not A2)))))
      (a!14 (and (not J4) (not (and (not I4) (not R))) (not a!13)))
      (a!22 (and G4
                 (not (and (not B2)
                           (not B)
                           (not Q)
                           (not P)
                           (not O)
                           (not N)
                           (not M)
                           (not K)
                           (not a!21)))))
      (a!23 (and I4
                 (not (and (not A2)
                           (not B)
                           (not Q)
                           (not P)
                           (not O)
                           (not N)
                           (not M)
                           (not K)
                           (not a!21)))))
      (a!26 (= E2 (or (and L4 H1) (and (not L4) (not a!25)))))
      (a!28 (= F2 (or (and L4 Z) (and (not L4) (not a!27)))))
      (a!30 (= G2 (or (and L4 Y) (and (not L4) (not a!29)))))
      (a!32 (= H2 (or (and L4 X) (and (not L4) (not a!31)))))
      (a!34 (= I2 (or (and L4 W) (and (not L4) (not a!33)))))
      (a!36 (and (not (and L4 S)) (not (and (not L4) (not a!35)))))
      (a!38 (= K2 (or (and L4 T) (and (not L4) (not a!37)))))
      (a!40 (= L2 (or (and L4 V) (and (not L4) (not a!39)))))
      (a!42 (= M2 (or (and L4 U) (and (not L4) (not a!41)))))
      (a!44 (= N2 (or (and L4 B1) (and (not L4) (not a!43)))))
      (a!46 (= O2 (or (and L4 A1) (and (not L4) (not a!45)))))
      (a!48 (= P2 (or (and L4 C1) (and (not L4) (not a!47)))))
      (a!50 (= Q2 (or (and L4 D1) (and (not L4) (not a!49)))))
      (a!52 (= R2 (or (and L4 E1) (and (not L4) (not a!51)))))
      (a!54 (= S2 (or (and L4 F1) (and (not L4) (not a!53)))))
      (a!56 (= T2 (or (and L4 G1) (and (not L4) (not a!55)))))
      (a!59 (= V2 (or (and (not H4) (not a!57)) a!58)))
      (a!63 (and (not (and (not G) S)) (not a!62)))
      (a!66 (not (and (not (and H T)) (not a!61))))
      (a!69 (not (and (not (and H T)) (not a!61) (not a!68))))
      (a!151 (= M3 (or (and (not J4) (not a!149)) a!150)))
      (a!155 (and (not (and J1 (not G))) (not a!154)))
      (a!158 (not (and (not (and K1 H)) (not a!153))))
      (a!161 (not (and (not (and K1 H)) (not a!153) (not a!160)))))
(let ((a!5 (and (not a!4) (not L4) (not (and (not H4) (not C2)))))
      (a!12 (and (not a!11) (not K4) (not (and (not J4) (not Z1)))))
      (a!64 (= W2 (or (and (not H4) (not a!60)) (and H4 (not a!61) (not a!63)))))
      (a!67 (and a!66 (not (and J U)) (not (and (not J) (not U)))))
      (a!156 (= N3
                (or (and (not J4) (not a!152)) (and J4 (not a!153) (not a!155)))))
      (a!159 (and a!158 (not (and L1 J)) (not (and (not L1) (not J))))))
(let ((a!24 (and (not a!3)
                 (not a!5)
                 (not a!7)
                 (not a!10)
                 (not a!12)
                 (not a!14)
                 (not (and (not C2) B2 (not I1)))
                 (not a!15)
                 (not (and (not B2) I1))
                 (not (and (not Z1) A2 (not R)))
                 (not a!16)
                 (not (and (not A2) R))
                 (not a!17)
                 (not a!18)
                 (not a!19)
                 (not a!20)
                 (not (and J4 I4))
                 (not (and (not L4)
                           (not H4)
                           (not G4)
                           (not K4)
                           (not J4)
                           (not I4)))
                 (not (and L4 (not C2)))
                 (not (and H4 (not I1)))
                 (not a!22)
                 (not (and K4 (not Z1)))
                 (not (and J4 (not R)))
                 (not a!23)))
      (a!70 (= X2 (or (and (not H4) (not a!65)) (and H4 (not a!67) a!69))))
      (a!72 (not (and (not (and J U)) (not a!67))))
      (a!75 (not (and (not (and J U)) (not a!67) (not a!74))))
      (a!162 (= O3 (or (and (not J4) (not a!157)) (and J4 (not a!159) a!161))))
      (a!164 (not (and (not (and L1 J)) (not a!159))))
      (a!167 (not (and (not (and L1 J)) (not a!159) (not a!166)))))
(let ((a!73 (and a!72 (not (and I V)) (not (and (not I) (not V)))))
      (a!165 (and a!164 (not (and M1 I)) (not (and (not M1) (not I))))))
(let ((a!76 (= Y2 (or (and (not H4) (not a!71)) (and H4 (not a!73) a!75))))
      (a!78 (not (and (not (and I V)) (not a!73))))
      (a!81 (not (and (not (and I V)) (not a!73) (not a!80))))
      (a!168 (= P3 (or (and (not J4) (not a!163)) (and J4 (not a!165) a!167))))
      (a!170 (not (and (not (and M1 I)) (not a!165))))
      (a!173 (not (and (not (and M1 I)) (not a!165) (not a!172)))))
(let ((a!79 (and a!78 (not (and F W)) (not (and (not F) (not W)))))
      (a!171 (and a!170 (not (and N1 F)) (not (and (not N1) (not F))))))
(let ((a!82 (= Z2 (or (and (not H4) (not a!77)) (and H4 (not a!79) a!81))))
      (a!84 (not (and (not (and F W)) (not a!79))))
      (a!87 (not (and (not (and F W)) (not a!79) (not a!86))))
      (a!174 (= Q3 (or (and (not J4) (not a!169)) (and J4 (not a!171) a!173))))
      (a!176 (not (and (not (and N1 F)) (not a!171))))
      (a!179 (not (and (not (and N1 F)) (not a!171) (not a!178)))))
(let ((a!85 (and a!84 (not (and E X)) (not (and (not E) (not X)))))
      (a!177 (and a!176 (not (and O1 E)) (not (and (not O1) (not E))))))
(let ((a!88 (= A3 (or (and (not H4) (not a!83)) (and H4 (not a!85) a!87))))
      (a!90 (not (and (not (and E X)) (not a!85))))
      (a!93 (not (and (not (and E X)) (not a!85) (not a!92))))
      (a!180 (= R3 (or (and (not J4) (not a!175)) (and J4 (not a!177) a!179))))
      (a!182 (not (and (not (and O1 E)) (not a!177))))
      (a!185 (not (and (not (and O1 E)) (not a!177) (not a!184)))))
(let ((a!91 (and a!90 (not (and D Y)) (not (and (not D) (not Y)))))
      (a!183 (and a!182 (not (and P1 D)) (not (and (not P1) (not D))))))
(let ((a!94 (= B3 (or (and (not H4) (not a!89)) (and H4 (not a!91) a!93))))
      (a!96 (not (and (not (and D Y)) (not a!91))))
      (a!99 (not (and (not (and D Y)) (not a!91) (not a!98))))
      (a!186 (= S3 (or (and (not J4) (not a!181)) (and J4 (not a!183) a!185))))
      (a!188 (not (and (not (and P1 D)) (not a!183))))
      (a!191 (not (and (not (and P1 D)) (not a!183) (not a!190)))))
(let ((a!97 (and a!96 (not (and C Z)) (not (and (not C) (not Z)))))
      (a!189 (and a!188 (not (and Q1 C)) (not (and (not Q1) (not C))))))
(let ((a!100 (= C3 (or (and (not H4) (not a!95)) (and H4 (not a!97) a!99))))
      (a!102 (not (and (not (and C Z)) (not a!97))))
      (a!105 (not (and (not (and C Z)) (not a!97) (not a!104))))
      (a!192 (= T3 (or (and (not J4) (not a!187)) (and J4 (not a!189) a!191))))
      (a!194 (not (and (not (and Q1 C)) (not a!189))))
      (a!197 (not (and (not (and Q1 C)) (not a!189) (not a!196)))))
(let ((a!103 (and a!102 (not (and L A1)) (not (and (not L) (not A1)))))
      (a!195 (and a!194 (not (and R1 L)) (not (and (not R1) (not L))))))
(let ((a!106 (= D3 (or (and (not H4) (not a!101)) (and H4 (not a!103) a!105))))
      (a!108 (not (and (not (and L A1)) (not a!103))))
      (a!111 (not (and (not (and L A1)) (not a!103) (not a!110))))
      (a!198 (= U3 (or (and (not J4) (not a!193)) (and J4 (not a!195) a!197))))
      (a!200 (not (and (not (and R1 L)) (not a!195))))
      (a!203 (not (and (not (and R1 L)) (not a!195) (not a!202)))))
(let ((a!109 (and a!108 (not (and K B1)) (not (and (not K) (not B1)))))
      (a!201 (and a!200 (not (and S1 K)) (not (and (not S1) (not K))))))
(let ((a!112 (= E3 (or (and (not H4) (not a!107)) (and H4 (not a!109) a!111))))
      (a!114 (not (and (not (and K B1)) (not a!109))))
      (a!117 (not (and (not (and K B1)) (not a!109) (not a!116))))
      (a!204 (= V3 (or (and (not J4) (not a!199)) (and J4 (not a!201) a!203))))
      (a!206 (not (and (not (and S1 K)) (not a!201))))
      (a!209 (not (and (not (and S1 K)) (not a!201) (not a!208)))))
(let ((a!115 (and a!114 (not (and M C1)) (not (and (not M) (not C1)))))
      (a!207 (and a!206 (not (and T1 M)) (not (and (not T1) (not M))))))
(let ((a!118 (= F3 (or (and (not H4) (not a!113)) (and H4 (not a!115) a!117))))
      (a!120 (not (and (not (and M C1)) (not a!115))))
      (a!123 (not (and (not (and M C1)) (not a!115) (not a!122))))
      (a!210 (= W3 (or (and (not J4) (not a!205)) (and J4 (not a!207) a!209))))
      (a!212 (not (and (not (and T1 M)) (not a!207))))
      (a!215 (not (and (not (and T1 M)) (not a!207) (not a!214)))))
(let ((a!121 (and a!120 (not (and N D1)) (not (and (not N) (not D1)))))
      (a!213 (and a!212 (not (and U1 N)) (not (and (not U1) (not N))))))
(let ((a!124 (= G3 (or (and (not H4) (not a!119)) (and H4 (not a!121) a!123))))
      (a!126 (not (and (not (and N D1)) (not a!121))))
      (a!129 (not (and (not (and N D1)) (not a!121) (not a!128))))
      (a!216 (= X3 (or (and (not J4) (not a!211)) (and J4 (not a!213) a!215))))
      (a!218 (not (and (not (and U1 N)) (not a!213))))
      (a!221 (not (and (not (and U1 N)) (not a!213) (not a!220)))))
(let ((a!127 (and a!126 (not (and O E1)) (not (and (not O) (not E1)))))
      (a!219 (and a!218 (not (and V1 O)) (not (and (not V1) (not O))))))
(let ((a!130 (= H3 (or (and (not H4) (not a!125)) (and H4 (not a!127) a!129))))
      (a!132 (not (and (not (and O E1)) (not a!127))))
      (a!135 (not (and (not (and O E1)) (not a!127) (not a!134))))
      (a!222 (= Y3 (or (and (not J4) (not a!217)) (and J4 (not a!219) a!221))))
      (a!224 (not (and (not (and V1 O)) (not a!219))))
      (a!227 (not (and (not (and V1 O)) (not a!219) (not a!226)))))
(let ((a!133 (and a!132 (not (and P F1)) (not (and (not P) (not F1)))))
      (a!225 (and a!224 (not (and W1 P)) (not (and (not W1) (not P))))))
(let ((a!136 (= I3 (or (and (not H4) (not a!131)) (and H4 (not a!133) a!135))))
      (a!138 (not (and (not (and P F1)) (not a!133))))
      (a!141 (not (and (not (and P F1)) (not a!133) (not a!140))))
      (a!228 (= Z3 (or (and (not J4) (not a!223)) (and J4 (not a!225) a!227))))
      (a!230 (not (and (not (and W1 P)) (not a!225))))
      (a!233 (not (and (not (and W1 P)) (not a!225) (not a!232)))))
(let ((a!139 (and a!138 (not (and Q G1)) (not (and (not Q) (not G1)))))
      (a!231 (and a!230 (not (and X1 Q)) (not (and (not X1) (not Q))))))
(let ((a!142 (= J3 (or (and (not H4) (not a!137)) (and H4 (not a!139) a!141))))
      (a!144 (not (and (not (and Q G1)) (not a!139))))
      (a!147 (not (and (not (and Q G1)) (not a!139) (not a!146))))
      (a!234 (= A4 (or (and (not J4) (not a!229)) (and J4 (not a!231) a!233))))
      (a!236 (not (and (not (and X1 Q)) (not a!231))))
      (a!239 (not (and (not (and X1 Q)) (not a!231) (not a!238)))))
(let ((a!145 (and a!144 (not (and B H1)) (not (and (not B) (not H1)))))
      (a!237 (and a!236 (not (and Y1 B)) (not (and (not Y1) (not B))))))
(let ((a!148 (= K3 (or (and (not H4) (not a!143)) (and H4 (not a!145) a!147))))
      (a!240 (= B4 (or (and (not J4) (not a!235)) (and J4 (not a!237) a!239)))))
(let ((a!241 (and (Invariant A
                       B
                       C
                       D
                       E
                       F
                       G
                       H
                       I
                       J
                       K
                       L
                       M
                       N
                       O
                       P
                       Q
                       R
                       S
                       T
                       U
                       V
                       W
                       X
                       Y
                       Z
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
                       X1
                       Y1
                       Z1
                       A2
                       B2
                       C2)
                  (= D2 (or A (not a!24)))
                  a!26
                  a!28
                  a!30
                  a!32
                  a!34
                  (= J2 a!36)
                  a!38
                  a!40
                  a!42
                  a!44
                  a!46
                  a!48
                  a!50
                  a!52
                  a!54
                  a!56
                  (= U2 a!8)
                  a!59
                  a!64
                  a!70
                  a!76
                  a!82
                  a!88
                  a!94
                  a!100
                  a!106
                  a!112
                  a!118
                  a!124
                  a!130
                  a!136
                  a!142
                  a!148
                  (= L3 a!1)
                  a!151
                  a!156
                  a!162
                  a!168
                  a!174
                  a!180
                  a!186
                  a!192
                  a!198
                  a!204
                  a!210
                  a!216
                  a!222
                  a!228
                  a!234
                  a!240
                  (= C4 a!9)
                  (= D4 a!13)
                  (= E4 a!6)
                  (= F4 a!2))))
  (=> a!241
      (Invariant D2
           E2
           F2
           G2
           H2
           I2
           J2
           K2
           L2
           M2
           N2
           O2
           P2
           Q2
           R2
           S2
           T2
           U2
           V2
           W2
           X2
           Y2
           Z2
           A3
           B3
           C3
           D3
           E3
           F3
           G3
           H3
           I3
           J3
           K3
           L3
           M3
           N3
           O3
           P3
           Q3
           R3
           S3
           T3
           U3
           V3
           W3
           X3
           Y3
           Z3
           A4
           B4
           C4
           D4
           E4
           F4))))))))))))))))))))))))))))))))))
(rule (=> (and (Invariant M4
              L4
              K4
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              L3
              K3
              J3
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
              K2)
         (not M4)
         (not L4)
         (not K4)
         J4
         (not I4)
         H4
         (not G4)
         (not F4)
         (not E4)
         (not D4)
         C4
         B4
         (not A4)
         (not Z3)
         (not Y3)
         (not X3)
         (not W3))
    Goal))
(query Goal)
