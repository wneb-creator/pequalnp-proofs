import OneNotFirstAnd

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

lemma projected_mono_lower_one (rows : NineSigned.Row → Live1024.Row)
    (goal : projected rows Live1024.graph = NineSigned.observe NineSigned.graph)
    (S : Finset Live1024.Sig) (k : Nat) (run : Live1024.Live false Live1024.graph k S)
    (covered : ∀ a ∈ S, Live1024.Available false (NineSigned.inputs.map NineSigned.observe)
      (projected rows a))
    (constant : ∃ a ∈ S, Live1024.Constant (projected rows a)) : 17 ≤ k := by
  have trace := Live1024.list_run run S.toList (Finset.nodup_toList S) (by simp)
  have nc : ¬ Live1024.Constant (Live1024.restrictRows rows (Live1024.observe Live1024.graph)) := by
    change ¬ Live1024.Constant (projected rows Live1024.graph)
    rw [goal]
    exact NineSigned.observe_proper NineSigned.graph_proper
  have supply : Live1024.supply false (NineSigned.inputs.map NineSigned.observe)
      ((S.toList.map Live1024.observe).map (Live1024.restrictRows rows)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact covered a (Finset.mem_toList.mp ha)
  have prior (q : Nat) (bank : List (Live1024.Wire NineSigned.Row))
      (h : Live1024.Reach false (NineSigned.inputs.map NineSigned.observe) q bank)
      (hv : Live1024.Available false bank
        (Live1024.restrictRows rows (Live1024.observe Live1024.graph))) : 16 ≤ q := by
    change Live1024.Available false bank (projected rows Live1024.graph) at hv
    rw [goal] at hv
    exact NineSigned.nine_monotone_reach_lower q bank (mono_reach_bridge h) hv
  have bound := Live1024.projected_bound rows trace nc Live1024.Reach.start supply prior
  obtain ⟨a, ha, hc⟩ := constant
  have mem : projected rows a ∈
      ((S.toList.map Live1024.observe).map (Live1024.restrictRows rows)) :=
    List.mem_map.mpr ⟨Live1024.observe a,
      List.mem_map.mpr ⟨a, Finset.mem_toList.mpr ha, rfl⟩, rfl⟩
  have mass := mass_positive mem hc
  omega

lemma live_monotone_lower
    (rows : Fin 10 → NineSigned.Row → Live1024.Row)
    (goal : ∀ i, projected (rows i) Live1024.graph = NineSigned.observe NineSigned.graph)
    (fixed : ∀ i, projected (rows i) (input i) = (fun _ => false))
    (covered : ∀ i j, Live1024.Available false (NineSigned.inputs.map NineSigned.observe)
      (projected (rows i) (input j)))
    (noOr : ∀ a b : Fin 10, a ≠ b → ∃ r s : Live1024.Row,
      (∀ i, i ≠ a → i ≠ b → Live1024.bit r (input i) = Live1024.bit s (input i)) ∧
      Live1024.bit r (Live1024.bin 1 (input a) (input b)) =
        Live1024.bit s (Live1024.bin 1 (input a) (input b)) ∧
      Live1024.bit r Live1024.graph ≠ Live1024.bit s Live1024.graph)
    {k : Nat} (run : Live1024.Live false Live1024.graph k Live1024.inputs.toFinset) : 18 ≤ k := by
  cases k with
  | zero =>
    obtain ⟨eq, _⟩ := run
    have count : Live1024.inputs.toFinset.card = 10 := by decide +kernel
    have h := congrArg Finset.card eq
    rw [count, Finset.card_singleton] at h
    omega
  | succ k =>
    obtain ⟨U, a, b, d, hd, eq, ha, hb, hab, fresh, tail⟩ := run
    have ma : a ∈ Live1024.inputs := List.mem_toFinset.mp (by rw [eq]; simp)
    have mb : b ∈ Live1024.inputs := List.mem_toFinset.mp (by rw [eq]; simp)
    have sub (w : Live1024.Sig) (hw : w ∈ U) : w ∈ Live1024.inputs :=
      List.mem_toFinset.mp (by rw [eq]; simp [hw])
    obtain ⟨i, rfl⟩ := input_index a ma
    obtain ⟨j, rfl⟩ := input_index b mb
    have ij : i ≠ j := by rintro rfl; exact hab rfl
    have finish (p : Fin 10)
        (new : Live1024.Available false (NineSigned.inputs.map NineSigned.observe)
          (projected (rows p) (Live1024.bin d (input i) (input j))))
        (constant : ∃ w ∈ insert (Live1024.bin d (input i) (input j)) U,
          Live1024.Constant (projected (rows p) w)) : 18 ≤ k + 1 := by
      have lower := projected_mono_lower_one (rows p) (goal p)
        (insert (Live1024.bin d (input i) (input j)) U) k tail (fun w hw => by
          rcases Finset.mem_insert.mp hw with rfl | old
          · exact new
          · obtain ⟨t, rfl⟩ := input_index w (sub w old)
            exact covered p t) constant
      omega
    rcases Live1024.allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · have hz : projected (rows i) (Live1024.bin 0 (input i) (input j)) = (fun _ => false) := by
        rw [projected_bin, fixed i]
        funext r
        simp [Live1024.comb, Live1024.combine]
      exact finish i (Or.inr (Or.inl ⟨false, hz⟩))
        ⟨_, Finset.mem_insert_self _ _, ⟨false, hz⟩⟩
    · have retained : input i ∈ U ∨ input j ∈ U := by
        by_contra missing
        push Not at missing
        obtain ⟨r, s, oldSame, newSame, different⟩ := noOr i j ij
        obtain ⟨w, hw, diff⟩ := Live1024.live_row_difference tail different
        rcases Finset.mem_insert.mp hw with rfl | old
        · exact diff newSame
        · obtain ⟨t, rfl⟩ := input_index w (sub w old)
          have hi : t ≠ i := by rintro rfl; exact missing.1 old
          have hj : t ≠ j := by rintro rfl; exact missing.2 old
          exact diff (oldSame t hi hj)
      rcases retained with hi | hj
      · have hz : projected (rows i) (Live1024.bin 1 (input i) (input j)) =
            projected (rows i) (input j) := by
          rw [projected_bin, fixed i]
          funext r
          simp [Live1024.comb, Live1024.combine]
        apply finish i (hz.symm ▸ covered i j)
        exact ⟨input i, Finset.mem_insert_of_mem hi, ⟨false, fixed i⟩⟩
      · have hz : projected (rows j) (Live1024.bin 1 (input i) (input j)) =
            projected (rows j) (input i) := by
          rw [projected_bin, fixed j]
          funext r
          simp [Live1024.comb, Live1024.combine]
        apply finish j (hz.symm ▸ covered j i)
        exact ⟨input j, Finset.mem_insert_of_mem hj, ⟨false, fixed j⟩⟩
    · have hz : projected (rows i) (Live1024.bin 2 (input i) (input j)) = (fun _ => false) := by
        rw [projected_bin, fixed i]
        funext r
        simp [Live1024.comb, Live1024.combine]
      exact finish i (Or.inr (Or.inl ⟨false, hz⟩))
        ⟨_, Finset.mem_insert_self _ _, ⟨false, hz⟩⟩
    · have hz : projected (rows j) (Live1024.bin 3 (input i) (input j)) = (fun _ => false) := by
        rw [projected_bin, fixed j]
        funext r
        simp [Live1024.comb, Live1024.combine, Live1024.inv]
      exact finish j (Or.inr (Or.inl ⟨false, hz⟩))
        ⟨_, Finset.mem_insert_self _ _, ⟨false, hz⟩⟩

lemma monotone_rt_lower {k : Nat}
    (run : Live1024.Live false Live1024.graph k Live1024.inputs.toFinset) : 18 ≤ k :=
  live_monotone_lower rowMap (fun i => funext (rowMap_graph i))
    (fun i => funext (rowMap_missing i))
    (fun i j => ZeroProfiles.rows_available i j)
    Live1024.no_or_identification_rows run

end PEqualNP.Outside.L_meta_2373.LiftSeventeen

namespace PEqualNP.Outside.L_meta_2373.Live1024.OneNotFirstAnd

open LiftSeventeen

lemma all_positive_tail_lower (a b : Fin 10) (ab : a ≠ b) {S : Finset Sig} {k : Nat}
    (sub : S ⊆ bank a b) (run : Live false graph k S) : 18 ≤ k := by
  by_cases used : andColumn a b ∈ S ∨ neg (andColumn a b) ∈ S
  · exact positive_tail_lower a b ab sub used run
  have subset : ∀ w ∈ S, w ∈ inputs := by
    intro w hw
    have mem := sub hw
    rcases Finset.mem_insert.mp mem with eq | mem
    · exact False.elim (used (Or.inl (eq ▸ hw)))
    rcases Finset.mem_insert.mp mem with eq | mem
    · exact False.elim (used (Or.inr (eq ▸ hw)))
    · exact List.mem_toFinset.mp mem
  have eq : S = inputs.toFinset := by
    ext w
    constructor
    · exact fun h => List.mem_toFinset.mpr (subset w h)
    · intro hw
      obtain ⟨i, rfl⟩ := input_index w (List.mem_toFinset.mp hw)
      apply raw_required run inputs (input i) subset (absentRow i) (presentRow i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j, rfl⟩ := input_index v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact monotone_rt_lower (eq ▸ run)

lemma all_prefix_exclusion (a b : Fin 10) (ab : a ≠ b) {S : Finset Sig} {k : Nat}
    (sub : S ⊆ bank a b) (budget : k + 2 ≤ 19) : ¬ Live false graph k S := by
  intro run
  have lower := all_positive_tail_lower a b ab sub run
  omega

end PEqualNP.Outside.L_meta_2373.Live1024.OneNotFirstAnd
