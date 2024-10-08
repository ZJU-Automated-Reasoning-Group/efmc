(declare-rel Invariant (Bool))
(declare-rel Goal ())
(declare-var l0 Bool)
(declare-var l2 Bool)
(declare-var l4 Bool)
(declare-var l6 Bool)
(declare-var l8 Bool)
(declare-var l10 Bool)
(rule (=> (not l4) (Invariant l4)))
(rule (=> (and (Invariant l4)
  (= (and (not l4) (not l2)) l6)
  (= (and l4 l2) l8)
  (= (and (not l8) (not l6)) l10)
  ) (Invariant l10)))
(rule (=> (and (Invariant l4)
  l4) Goal))
(query Goal)