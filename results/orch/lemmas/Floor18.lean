import Floor17Proof

namespace PEqualNP.Outside.L_meta_2592.Full

def positiveOperand (d : Fin 4) (a b : Fin 10) : Fin 10 :=
  if d.val = 3 then b else a

lemma project_nonor_zero (d : Fin 4) (a b : Fin 10) (nonor : d.val ≠ 1) :
    restrictRows (projectRow (positiveOperand d a b))
      (comb d.val (raw a) (raw b)) = fun _ => false := by
  have hcases : d.val = 0 ∨ d.val = 2 ∨ d.val = 3 := by omega
  rcases hcases with hd | hd | hd
  · have vp : positiveOperand d a b = a := by simp [positiveOperand, hd]
    rw [vp, restrict_comb, project_zero]
    simp [hd, comb, combine]
  · have vp : positiveOperand d a b = a := by simp [positiveOperand, hd]
    rw [vp, restrict_comb, project_zero]
    simp [hd, comb, combine]
  · have vp : positiveOperand d a b = b := by simp [positiveOperand, hd]
    rw [vp, restrict_comb, project_zero]
    simp [hd, comb, combine]

lemma project_nonor_mass (d : Fin 4) (a b : Fin 10) (nonor : d.val ≠ 1) :
    2 ≤ mass ((comb d.val (raw a) (raw b) :: inputs.map observe).map
      (restrictRows (projectRow (positiveOperand d a b)))) := by
  have zeroMem : (fun _ : Deleted.Row => false) ∈
      (inputs.map observe).map (restrictRows (projectRow (positiveOperand d a b))) := by
    rw [← project_zero (positiveOperand d a b)]
    exact List.mem_map_of_mem (raw_mem (positiveOperand d a b))
  have massLo := cost_le_mass _ _ zeroMem
  have cz : cost (fun _ : Deleted.Row => false) = 1 := by
    classical
    simp [cost, Constant]
  rw [cz] at massLo
  rw [List.map_cons, mass_cons, project_nonor_zero d a b nonor, cz]
  omega

lemma first_nonor_suffix_floor {k : Nat} (d : Fin 4) (a b : Fin 10)
    (nonor : d.val ≠ 1)
    (run : Run true (observe graph) k
      (comb d.val (raw a) (raw b) :: inputs.map observe)) : 17 ≤ k := by
  let v := positiveOperand d a b
  have nc : ¬ Constant (restrictRows (projectRow v) (observe graph)) := by
    rw [project_graph]
    exact Deleted.observe_proper Deleted.graph_proper
  have supplied : supply true (Deleted.inputs.map Deleted.observe)
      ((comb d.val (raw a) (raw b) :: inputs.map observe).map
        (restrictRows (projectRow v))) := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
    rcases List.mem_cons.mp hz with rfl | hz
    · rw [show v = positiveOperand d a b from rfl, project_nonor_zero d a b nonor]
      exact Or.inr (Or.inl ⟨false, rfl⟩)
    · rw [raw_bank] at hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact project_available v i
  have low : ∀ q bs, Reach true (Deleted.inputs.map Deleted.observe) q bs →
      Available true bs (restrictRows (projectRow v) (observe graph)) → 15 ≤ q := by
    intro q bs hq hit
    rw [project_graph] at hit
    exact Deleted.signed_lower q bs (reach_deleted hq) hit
  have bound := projected_bound (projectRow v) run nc Reach.start supplied low
  have massLo := project_nonor_mass d a b nonor
  change 2 ≤ mass ((comb d.val (raw a) (raw b) :: inputs.map observe).map
    (restrictRows (projectRow v))) at massLo
  omega

lemma small_first_is_or {k : Nat} (d : Fin 4) (a b : Fin 10)
    (run : Run true (observe graph) k
      (comb d.val (raw a) (raw b) :: inputs.map observe))
    (small : k ≤ 16) : d.val = 1 := by
  by_contra nonor
  have bound := first_nonor_suffix_floor d a b nonor run
  omega

lemma seventeen_run_first_or {k : Nat}
    (run : Run true (observe graph) k (inputs.map observe)) (small : k ≤ 17) :
    ∃ (s : Nat) (a b : Fin 10), k = s + 1 ∧ a ≠ b ∧
      Run true (observe graph) s (comb 1 (raw a) (raw b) :: inputs.map observe) := by
  obtain ⟨s, d, a, b, heq, hab, tail⟩ := first_split run
  have op := small_first_is_or d a b tail (by omega)
  refine ⟨s, a, b, heq, hab, ?_⟩
  rwa [op] at tail

end PEqualNP.Outside.L_meta_2592.Full
