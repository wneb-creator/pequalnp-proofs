import PublicPR18338
#print axioms PEqualNP.Outside.L_meta_9777

example : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 24 ∧
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 14, (u.val, v.val) ∈
        ([(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,13),(3,7),(3,11),(3,12),
          (4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] : List (Nat × Nat)) ∧
        x u = true ∧ x v = true)) := PEqualNP.Outside.L_meta_9777
