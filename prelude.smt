(set-logic HO_ALL)
(set-option :produce-unsat-cores true)
(declare-datatype Pair (par (T1 T2) ((pair (fst T1) (snd T2)))))
(declare-datatype Option (par (T) ((some (the T)) (none))))