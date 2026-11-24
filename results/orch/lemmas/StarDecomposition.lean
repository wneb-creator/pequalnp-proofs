import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.StarDecomposition

lemma directed_stars {n : ℕ} (R : Finset (Fin n × Fin n)) (T : Finset (Fin n))
    (hne : R.Nonempty) (hT : ∀ e ∈ R, e.1 ∈ T) :
    ∃ ss : List (Fin n × List (Fin n)), ss ≠ [] ∧
      (∀ s ∈ ss, s.2 ≠ []) ∧ ss.length ≤ T.card ∧
      (ss.map fun s => s.2.length).sum = R.card ∧
      (∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ R) ∧
      (∀ e ∈ R, ∃ s ∈ ss, s.1 = e.1 ∧ e.2 ∈ s.2) := by
  classical
  let S := R.image Prod.fst
  let N : Fin n → Finset (Fin n) := fun c => (R.filter (fun e => e.1 = c)).image Prod.snd
  let ss : List (Fin n × List (Fin n)) := S.toList.map (fun c => (c, (N c).toList))
  have hNm (c v : Fin n) : v ∈ N c ↔ (c, v) ∈ R := by
    constructor
    · intro hv
      obtain ⟨⟨a, b⟩, he, hv⟩ := Finset.mem_image.mp hv
      obtain ⟨he, ha⟩ := Finset.mem_filter.mp he
      dsimp at ha hv
      subst a
      subst b
      exact he
    · intro hv
      exact Finset.mem_image.mpr ⟨(c, v), Finset.mem_filter.mpr ⟨hv, rfl⟩, rfl⟩
  have hNcard (c : Fin n) : (N c).card = (R.filter (fun e => e.1 = c)).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab
  have hlen : ss.length = S.card := by simp [ss]
  have hScard : S.card ≤ T.card := Finset.card_le_card (by
    intro c hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
    exact hT e he)
  have hssne : ss ≠ [] := by
    intro he
    obtain ⟨e, heR⟩ := hne
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e.1, Finset.mem_image.mpr ⟨e, heR, rfl⟩⟩
    simp only [he, List.length_nil] at hlen
    omega
  have hentry : ∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ R := by
    intro s hs v hv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    exact (hNm c v).mp (by simpa using hv)
  have hall : ∀ e ∈ R, ∃ s ∈ ss, s.1 = e.1 ∧ e.2 ∈ s.2 := by
    intro e he
    refine ⟨(e.1, (N e.1).toList), ?_, rfl, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨e.1, Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨e, he, rfl⟩), rfl⟩
    · exact Finset.mem_toList.mpr ((hNm e.1 e.2).mpr he)
  have hnonempty : ∀ s ∈ ss, s.2 ≠ [] := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    have hcS : c ∈ S := by simpa using hc
    obtain ⟨e, he, hc⟩ := Finset.mem_image.mp hcS
    have hmem : e.2 ∈ (N c).toList := Finset.mem_toList.mpr ((hNm c e.2).mpr (by rw [← hc]; exact he))
    intro hn
    change (N c).toList = [] at hn
    rw [hn] at hmem
    simp at hmem
  have hcost : (ss.map fun s => s.2.length).sum = R.card := by
    simp only [ss, List.map_map, Function.comp_def, Finset.length_toList]
    rw [Finset.sum_map_toList]
    simp_rw [hNcard]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    apply Finset.filter_eq_self.mpr
    intro e he
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  exact ⟨ss, hssne, hnonempty, hlen.trans_le hScard, hcost, hentry, hall⟩

lemma oriented_stars {n : ℕ} (E : Finset (Fin n × Fin n)) (T : Finset (Fin n))
    (hne : E.Nonempty) (hT : ∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) :
    ∃ ss : List (Fin n × List (Fin n)), ss ≠ [] ∧
      (∀ s ∈ ss, s.2 ≠ []) ∧ ss.length ≤ T.card ∧
      (ss.map fun s => s.2.length).sum ≤ E.card ∧
      (∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ E ∨ (v, s.1) ∈ E) ∧
      (∀ x : Fin n → Bool,
        (ss.any fun s => x s.1 && s.2.any x) =
          decide (∃ e ∈ E, x e.1 = true ∧ x e.2 = true)) := by
  classical
  let orient : (Fin n × Fin n) → (Fin n × Fin n) := fun e =>
    if e.1 ∈ T then e else (e.2, e.1)
  let R := E.image orient
  have hRne : R.Nonempty := Finset.Nonempty.image hne orient
  have hRT : ∀ e ∈ R, e.1 ∈ T := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    by_cases hh : f.1 ∈ T
    · simpa [orient, hh] using hh
    · simpa [orient, hh] using (hT f hf).resolve_left hh
  obtain ⟨ss, hss, hneigh, hlen, hcost, hentry, hall⟩ := directed_stars R T hRne hRT
  have hedges : ∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ E ∨ (v, s.1) ∈ E := by
    intro s hs v hv
    obtain ⟨e, he, hor⟩ := Finset.mem_image.mp (hentry s hs v hv)
    by_cases hh : e.1 ∈ T
    · have heq : e = (s.1, v) := by simpa [orient, hh] using hor
      exact Or.inl (heq ▸ he)
    · have heq : (e.2, e.1) = (s.1, v) := by simpa [orient, hh] using hor
      have heq' : e = (v, s.1) := by
        apply Prod.ext
        · exact congrArg Prod.snd heq
        · exact congrArg Prod.fst heq
      exact Or.inr (heq' ▸ he)
  refine ⟨ss, hss, hneigh, hlen, hcost.trans_le (Finset.card_image_le), hedges, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, hxs, v, hv, hxv⟩
    rcases hedges s hs v hv with he | he
    · exact ⟨(s.1, v), he, hxs, hxv⟩
    · exact ⟨(v, s.1), he, hxv, hxs⟩
  · rintro ⟨e, he, hx1, hx2⟩
    have heR : orient e ∈ R := Finset.mem_image.mpr ⟨e, he, rfl⟩
    obtain ⟨s, hs, hs1, hv⟩ := hall (orient e) heR
    refine ⟨s, hs, ?_, (orient e).2, hv, ?_⟩
    · rw [hs1]
      by_cases hh : e.1 ∈ T
      · simpa [orient, hh] using hx1
      · simpa [orient, hh] using hx2
    · by_cases hh : e.1 ∈ T
      · simpa [orient, hh] using hx2
      · simpa [orient, hh] using hx1

end PEqualNP.Outside.L_meta_1477.StarDecomposition
