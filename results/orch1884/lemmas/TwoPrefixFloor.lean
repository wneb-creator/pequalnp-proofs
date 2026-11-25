import Binary17

namespace PEqualNP.Outside.L_meta_1884.TwoPrefixFloor

open PEqualNP.Outside.L_meta_2592.Binary17
open PEqualNP.Outside.L_meta_2592.Binary17.Geometry

lemma suffix_sixteen (v a b : Fin 10) (r : Extended.Sig)
    {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ z ∈ S, z ∈ Extended.initial ∨
      z = Extended.bin 1 (pin a) (pin b) ∨ z = r)
    (hv : pin v ∈ S) (hr : r ∈ S) (hne : r ≠ pin v)
    (hz : projectV v r = zero) : 16 ≤ k := by
  classical
  let q := Extended.bin 1 (pin a) (pin b)
  let front := pin v :: r :: ((S.erase (pin v)).erase r).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, ?_⟩
    · simp [Ne.symm hne]
    · apply List.nodup_cons.mpr
      exact ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext z
    by_cases hvz : z = pin v <;> by_cases hrz : z = r <;>
      simp [front, hvz, hrz, hv, hr]
  have hrun := Extended.list_run run front nd eqS
  let base := inputs.map observe
  let qa := observe (projectV v (pin a))
  let qb := observe (projectV v (pin b))
  let pq := combine true qa qb
  let bank := pq :: base
  have pa : Available true base qa := by
    rcases project_pin v a with he | hm
    · exact projected_available _ (Or.inl he)
    · exact projected_available _ (Or.inr (Or.inr (Or.inl hm)))
  have pb : Available true base qb := by
    rcases project_pin v b with he | hm
    · exact projected_available _ (Or.inl he)
    · exact projected_available _ (Or.inr (Or.inr (Or.inl hm)))
  have reach : Reach true base 1 bank := Reach.two true Reach.start pa pb
  have pqeq : observe (projectV v q) = pq := by
    rw [show q = Extended.bin 1 (pin a) (pin b) from rfl,
      project_bin_commute, obs_bin]
    rfl
  have same : restrictRows (embedV v) (Extended.observe Extended.target) =
      observe graph := by
    rw [observe_projectV, project_target]
  have roots : supply true bank
      ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    intro z hzmem
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hzmem
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
    rw [observe_projectV]
    rcases raw w (eqS ▸ List.mem_toFinset.mpr hw) with hp | hq | hrr
    · obtain ⟨i, rfl⟩ := (pin_mem_iff w).mp hp
      apply available_cons
      rcases project_pin v i with he | hm
      · exact projected_available _ (Or.inl he)
      · exact projected_available _ (Or.inr (Or.inr (Or.inl hm)))
    · change w = q at hq
      rw [hq, pqeq]
      exact Or.inl (by simp [bank])
    · rw [hrr, hz]
      exact Or.inr (Or.inl ⟨false, by funext t; simp [observe, bit, zero]⟩)
  have bound := projected_bound (embedV v) hrun
    (same ▸ observe_proper graph_proper) reach roots
    (L := 15) (same ▸ nineFloor)
  have cp : Constant (restrictRows (embedV v) (Extended.observe (pin v))) := by
    rw [observe_projectV, project_self]
    exact ⟨false, by funext t; simp [observe, bit, zero]⟩
  have cr : Constant (restrictRows (embedV v) (Extended.observe r)) := by
    rw [observe_projectV, hz]
    exact ⟨false, by funext t; simp [observe, bit, zero]⟩
  have charge : 2 ≤ mass
      ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    simp [front, mass_cons, cost, cp, cr]
    omega
  omega

def neighborOutside (v a b : Fin 10) : Fin 10 :=
  ((List.finRange 10).find? fun t =>
    (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List Nat).getD v.val 0).testBit t.val &&
      decide (t ≠ a ∧ t ≠ b)).getD 0

def andOrRows (v a b : Fin 10) : Extended.Row × Extended.Row :=
  let t := neighborOutside v a b
  (Fin.ofNat 1024 (2 ^ position t), Fin.ofNat 1024 (2 ^ position t + 2 ^ position v))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma and_or_rows : ∀ v a b : Fin 10, v ≠ a → v ≠ b →
    Extended.bit (andOrRows v a b).1 Extended.target ≠
      Extended.bit (andOrRows v a b).2 Extended.target ∧
    Extended.bit (andOrRows v a b).1 (Extended.bin 1 (pin a) (pin b)) =
      Extended.bit (andOrRows v a b).2 (Extended.bin 1 (pin a) (pin b)) ∧
    Extended.bit (andOrRows v a b).1
        (Extended.bin 0 (pin v) (Extended.bin 1 (pin a) (pin b))) =
      Extended.bit (andOrRows v a b).2
        (Extended.bin 0 (pin v) (Extended.bin 1 (pin a) (pin b))) ∧
    ∀ i : Fin 10, i ≠ v →
      Extended.bit (andOrRows v a b).1 (pin i) =
        Extended.bit (andOrRows v a b).2 (pin i) := by
  decide +kernel

lemma second_and_or_eighteen (v a b : Fin 10) (hva : v ≠ a) (hvb : v ≠ b)
    {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ z ∈ S, z ∈ Extended.initial ∨
      z = Extended.bin 1 (pin a) (pin b) ∨
      z = Extended.bin 0 (pin v) (Extended.bin 1 (pin a) (pin b)))
    (hr : Extended.bin 0 (pin v) (Extended.bin 1 (pin a) (pin b)) ∈ S)
    (hne : Extended.bin 0 (pin v) (Extended.bin 1 (pin a) (pin b)) ≠ pin v) :
    18 ≤ k + 2 := by
  have props := and_or_rows v a b hva hvb
  have hv : pin v ∈ S := by
    obtain ⟨z, hz, diff⟩ := Extended.live_row_difference run props.1
    rcases raw z hz with hp | hq | hrr
    · obtain ⟨i, rfl⟩ := (pin_mem_iff z).mp hp
      by_cases hi : i = v
      · simpa [hi] using hz
      · exact False.elim (diff (props.2.2.2 i hi))
    · rw [hq] at diff
      exact False.elim (diff props.2.1)
    · rw [hrr] at diff
      exact False.elim (diff props.2.2.1)
  have hz : projectV v
      (Extended.bin 0 (pin v) (Extended.bin 1 (pin a) (pin b))) = zero := by
    rw [project_bin_commute, project_self]
    simp [bin, zero]
  have bound := suffix_sixteen v a b _ run raw hv hr hne hz
  omega

end PEqualNP.Outside.L_meta_1884.TwoPrefixFloor
