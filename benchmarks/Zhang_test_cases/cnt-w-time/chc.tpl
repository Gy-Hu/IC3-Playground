(set-option :fp.engine spacer)

%%



(declare-rel INV (|cnt_s|))
(declare-rel fail ())


(declare-var |__S__| |cnt_s|)
(declare-var |__S'__| |cnt_s|)


; init => inv
(rule (=> (|cnt_i| |__S__|)
  (INV |__S__|)))

; inv /\ T => inv
(rule (=> (and 
  (INV |__S__|)   
  (|cnt_t| |__S__| |__S'__|)) 
  (INV |__S'__|)))

; inv /\ ~p => \bot
(rule (=> (and 
  (INV |__S__|)   
  (not (|cnt_a| |__S__|)))
  fail))


(query fail :print-certificate true)
