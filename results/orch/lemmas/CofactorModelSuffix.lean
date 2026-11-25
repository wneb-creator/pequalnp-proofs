namespace PEqualNP.Outside.L_meta_2592

lemma cofactorModelInputSupply (i : Fin 10) :
    Available true (inputs.map observe) (fun r : Row => Extended.assign (embed r) i) := by
  change Available true (inputs.map observe)
    (restrictRows embed (Extended.observe (Extended.pins.getD i.val Extended.zero)))
  rw [observe_projected]
  have permitted : ∀ j : Fin 10,
      projected (Extended.pins.getD j.val Extended.zero) = zero ∨
      projected (Extended.pins.getD j.val Extended.zero) ∈ inputs := by
    decide +kernel
  rcases permitted i with hz | hm
  · refine Or.inr (Or.inl ⟨false, ?_⟩)
    rw [hz]
    funext r
    simp [observe, bit, zero]
  · exact Or.inl (List.mem_map.mpr ⟨_, hm, rfl⟩)

lemma cofactorModelInputZero : ∀ r : Row, Extended.assign (embed r) 0 = false := by
  decide +kernel

lemma cofactorModelTarget :
    (fun r : Row => Extended.f10 (Extended.assign (embed r))) = observe graph := by
  have same : restrictRows embed (Extended.observe Extended.target) = observe graph := by
    rw [observe_projected]
    exact congrArg observe (by decide +kernel)
  funext r
  rw [← Extended.rowTarget]
  exact congrFun same r

lemma cofactorModelFloor (k : Nat) (bank : List (Wire Row))
    (run : Reach true (inputs.map observe) k bank)
    (hit : Available true bank (fun r : Row => Extended.f10 (Extended.assign (embed r)))) :
    15 ≤ k := by
  rw [cofactorModelTarget] at hit
  exact nineFloor k bank run hit

lemma signedFalseCofactorFloor (v : Fin 10) (s : Nat)
    (small : Signed.HasU2Size
      (fun x => PEqualNP.Outside.L_meta_2592_aux.PairSeparation.pet (Function.update x v false)) s) :
    15 ≤ s := by
  exact Signed.false_cofactor_floor_of_model
    (fun r : Row => Extended.assign (embed r)) (inputs.map observe)
    cofactorModelInputSupply cofactorModelInputZero cofactorModelFloor v s small

end PEqualNP.Outside.L_meta_2592
