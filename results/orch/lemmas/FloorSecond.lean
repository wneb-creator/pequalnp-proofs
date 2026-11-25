import Floor18

namespace PEqualNP.Outside.L_meta_2592.Full

lemma projected_or_available (a b v : Fin 10) (overlap : v = a ∨ v = b) :
    Available true (Deleted.inputs.map Deleted.observe)
      (restrictRows (projectRow v) (comb 1 (raw a) (raw b))) := by
  rcases overlap with ha | hb
  · subst v
    rw [restrict_comb, project_zero]
    simpa [comb, combine] using project_available a b
  · subst v
    rw [restrict_comb, project_zero]
    simpa [comb, combine] using project_available b a

lemma projected_absorbing_raw (d : Nat) (p q : Wire Row) (v : Fin 10)
    (positive : (d = 0 ∧ (p = raw v ∨ q = raw v)) ∨
      (d = 2 ∧ p = raw v) ∨ (d = 3 ∧ q = raw v)) :
    restrictRows (projectRow v) (comb d p q) = fun _ => false := by
  rcases positive with ⟨rfl, hp | hq⟩ | ⟨rfl, hp⟩ | ⟨rfl, hq⟩
  · rw [hp, restrict_comb, project_zero]
    simp [comb, combine]
  · rw [hq, restrict_comb, project_zero]
    simp [comb, combine]
  · rw [hp, restrict_comb, project_zero]
    simp [comb, combine]
  · rw [hq, restrict_comb, project_zero]
    simp [comb, combine]

lemma second_overlap_suffix_floor {k : Nat} (a b v : Fin 10)
    (overlap : v = a ∨ v = b) (z : Wire Row) (rest : List (Wire Row))
    (zeroed : restrictRows (projectRow v) z = fun _ => false)
    (roots : ∀ w ∈ rest, w ∈ inputs.map observe ∨ w = comb 1 (raw a) (raw b))
    (run : Run true (observe graph) k (z :: rest)) : 16 ≤ k := by
  have nc : ¬ Constant (restrictRows (projectRow v) (observe graph)) := by
    rw [project_graph]
    exact Deleted.observe_proper Deleted.graph_proper
  have supplied : supply true (Deleted.inputs.map Deleted.observe)
      ((z :: rest).map (restrictRows (projectRow v))) := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [zeroed]
      exact Or.inr (Or.inl ⟨false, rfl⟩)
    · rcases roots q hq with hraw | rfl
      · rw [raw_bank] at hraw
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hraw
        exact project_available v i
      · exact projected_or_available a b v overlap
  have low : ∀ q bs, Reach true (Deleted.inputs.map Deleted.observe) q bs →
      Available true bs (restrictRows (projectRow v) (observe graph)) → 15 ≤ q := by
    intro q bs hq hit
    rw [project_graph] at hit
    exact Deleted.signed_lower q bs (reach_deleted hq) hit
  have bound := projected_bound (projectRow v) run nc Reach.start supplied low
  have cz : cost (fun _ : Deleted.Row => false) = 1 := by
    classical
    simp [cost, Constant]
  have massLo : 1 ≤ mass ((z :: rest).map (restrictRows (projectRow v))) := by
    rw [List.map_cons, mass_cons, zeroed, cz]
    omega
  omega

lemma second_positive_overlap_floor {k : Nat} (a b v : Fin 10)
    (overlap : v = a ∨ v = b) (d : Nat) (p q : Wire Row) (rest : List (Wire Row))
    (positive : (d = 0 ∧ (p = raw v ∨ q = raw v)) ∨
      (d = 2 ∧ p = raw v) ∨ (d = 3 ∧ q = raw v))
    (roots : ∀ w ∈ rest, w ∈ inputs.map observe ∨ w = comb 1 (raw a) (raw b))
    (run : Run true (observe graph) k (comb d p q :: rest)) : 18 ≤ k + 2 := by
  have bound := second_overlap_suffix_floor a b v overlap (comb d p q) rest
    (projected_absorbing_raw d p q v positive) roots run
  omega

end PEqualNP.Outside.L_meta_2592.Full
