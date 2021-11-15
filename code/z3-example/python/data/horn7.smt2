(set-option :fp.engine spacer)
(set-logic HORN)
(set-option :fp.engine spacer)
(declare-fun Inv
             ((_ BitVec 4)
              Bool
              (_ BitVec 4)
              Bool
              Bool
              Bool
              (_ BitVec 4)
              (_ BitVec 4)
              (_ BitVec 4)
              Bool
              Bool)
             Bool)
(assert (forall ((vi!5 (_ BitVec 4))
         (vi!7 Bool)
         (vi!9 (_ BitVec 4))
         (vi!11 Bool)
         (vi!13 Bool)
         (vi!15 Bool)
         (vi!17 (_ BitVec 4))
         (vi!19 (_ BitVec 4))
         (vi!21 (_ BitVec 4))
         (vi!23 Bool)
         (vi!25 Bool)
         (vo!6 (_ BitVec 4))
         (vo!8 Bool)
         (vo!10 (_ BitVec 4))
         (vo!12 Bool)
         (vo!14 Bool)
         (vo!16 Bool)
         (vo!18 (_ BitVec 4))
         (vo!20 (_ BitVec 4))
         (vo!22 (_ BitVec 4))
         (vo!24 Bool)
         (vo!26 Bool)
         (i!0 Bool)
         (i!1 (_ BitVec 4))
         (i!2 Bool)
         (i!3 (_ BitVec 4))
         (i!4 Bool))
  (let ((a!1 (and (not vi!7)
                  (not vi!15)
                  vi!23
                  (not vi!25)
                  i!4
                  (not (and vi!11 (not vi!13)))
                  (or (not vi!15) (= vi!17 vi!5)))))
    (=> a!1
        (Inv vi!5 vi!7 vi!9 vi!11 vi!13 vi!15 vi!17 vi!19 vi!21 vi!23 vi!25)))))
(assert (forall ((vi!5 (_ BitVec 4))
         (vi!7 Bool)
         (vi!9 (_ BitVec 4))
         (vi!11 Bool)
         (vi!13 Bool)
         (vi!15 Bool)
         (vi!17 (_ BitVec 4))
         (vi!19 (_ BitVec 4))
         (vi!21 (_ BitVec 4))
         (vi!23 Bool)
         (vi!25 Bool)
         (vo!6 (_ BitVec 4))
         (vo!8 Bool)
         (vo!10 (_ BitVec 4))
         (vo!12 Bool)
         (vo!14 Bool)
         (vo!16 Bool)
         (vo!18 (_ BitVec 4))
         (vo!20 (_ BitVec 4))
         (vo!22 (_ BitVec 4))
         (vo!24 Bool)
         (vo!26 Bool)
         (i!0 Bool)
         (i!1 (_ BitVec 4))
         (i!2 Bool)
         (i!3 (_ BitVec 4))
         (i!4 Bool))
  (let ((a!1 (ite i!2 vi!19 (ite vi!13 (bvadd #x1 (bvmul #x2 vi!19)) vi!5)))
        (a!2 (= vo!22 (ite i!2 vi!21 (bvadd #x1 (bvmul #x2 vi!19))))))
  (let ((a!3 (and (Inv vi!5
                       vi!7
                       vi!9
                       vi!11
                       vi!13
                       vi!15
                       vi!17
                       vi!19
                       vi!21
                       vi!23
                       vi!25)
                  (= vo!6 (ite i!2 vi!5 (ite vi!11 vi!21 vi!5)))
                  (= vo!8 (and (not i!2) vi!15))
                  (= vo!10 (bvadd #x1 (bvmul #x2 vi!17)))
                  (= vo!12 (ite i!2 vi!11 vi!13))
                  (= vo!14 (ite i!2 vi!13 i!4))
                  (= vo!16 (and (not i!2) vi!25))
                  (= vo!18 (ite i!2 i!1 vi!17))
                  (= vo!20 a!1)
                  a!2
                  (= vo!24 i!2)
                  (= vo!26 (and (not i!2) vi!23))
                  i!4
                  (not (and vi!11 (not vi!13)))
                  (or (not vi!15) (= vi!17 vi!5)))))
    (=> a!3
        (Inv vo!6 vo!8 vo!10 vo!12 vo!14 vo!16 vo!18 vo!20 vo!22 vo!24 vo!26))))))
(assert (forall ((vi!5 (_ BitVec 4))
         (vi!7 Bool)
         (vi!9 (_ BitVec 4))
         (vi!11 Bool)
         (vi!13 Bool)
         (vi!15 Bool)
         (vi!17 (_ BitVec 4))
         (vi!19 (_ BitVec 4))
         (vi!21 (_ BitVec 4))
         (vi!23 Bool)
         (vi!25 Bool)
         (vo!6 (_ BitVec 4))
         (vo!8 Bool)
         (vo!10 (_ BitVec 4))
         (vo!12 Bool)
         (vo!14 Bool)
         (vo!16 Bool)
         (vo!18 (_ BitVec 4))
         (vo!20 (_ BitVec 4))
         (vo!22 (_ BitVec 4))
         (vo!24 Bool)
         (vo!26 Bool)
         (i!0 Bool)
         (i!1 (_ BitVec 4))
         (i!2 Bool)
         (i!3 (_ BitVec 4))
         (i!4 Bool))
  (let ((a!1 (and (Inv vi!5
                       vi!7
                       vi!9
                       vi!11
                       vi!13
                       vi!15
                       vi!17
                       vi!19
                       vi!21
                       vi!23
                       vi!25)
                  (not (or (not vi!7) (= vi!9 vi!5)))
                  i!4
                  (not (and vi!11 (not vi!13)))
                  (or (not vi!15) (= vi!17 vi!5)))))
    (=> a!1 false))))
(check-sat)
(exit)
