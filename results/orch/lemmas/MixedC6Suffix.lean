namespace PEqualNP.Outside.L_meta_2592_aux.PairSeparation

def neighborMask (v : Fin 10) : Nat :=
  (![50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : Fin 10 → Nat) v

def closedNeighborhoodZero (v : Fin 10) (x : Fin 10 → Bool) : Fin 10 → Bool :=
  fun i => if i = v then false else if (neighborMask v).testBit i.val then false else x i

def closedNeighborhoodOne (v : Fin 10) (x : Fin 10 → Bool) : Fin 10 → Bool :=
  fun i => if i = v then true else if (neighborMask v).testBit i.val then false else x i

lemma pet_closedNeighborhoodOne : ∀ (v : Fin 10) (x : Fin 10 → Bool),
    pet (closedNeighborhoodOne v x) = pet (closedNeighborhoodZero v x) := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.PairSeparation
