(declare-rel Invariant (Bool Bool Bool Bool Bool Bool Bool Bool Bool))
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
(rule (=> (not (or A B C D E F G H I))
    (Invariant A B C D E F G H I)))
(rule (let ((a!1 (not (and B C D E F G H S I)))
      (a!3 (not (and C D E F G H S I)))
      (a!5 (not (and (not C) (not (and D E F G H S I)))))
      (a!6 (not (and (not D) (not (and E F G H S I)))))
      (a!8 (not (and (not E) (not (and F G H S I)))))
      (a!10 (not (and (not F) (not (and G H S I)))))
      (a!12 (not (and (not G) (not (and H S I)))))
      (a!14 (not (and (not H) (not (and S I)))))
      (a!16 (and (not (and S I)) (not (and (not S) (not I))))))
(let ((a!2 (and (not (and A B C D E F G H S I)) (not (and (not A) a!1))))
      (a!4 (and a!1 (not (and (not B) a!3))))
      (a!7 (= M (and (not (and D E F G H S I)) a!6)))
      (a!9 (= N (and (not (and E F G H S I)) a!8)))
      (a!11 (= O (and (not (and F G H S I)) a!10)))
      (a!13 (= P (and (not (and G H S I)) a!12)))
      (a!15 (= Q (and (not (and H S I)) a!14))))
  (=> (and (Invariant A B C D E F G H I)
           (= J a!2)
           (= K a!4)
           (= L (and a!3 a!5))
           a!7
           a!9
           a!11
           a!13
           a!15
           (= R a!16))
      (Invariant J K L M N O P Q R)))))
(rule (let ((a!1 (and P (not (and (not O) (not N))))))
(let ((a!2 (or U (not (and (not T) (not S) (not R) (not Q) (not a!1))))))
  (=> (and (Invariant U T S R Q P O N M) a!2) Goal))))
(query Goal)
