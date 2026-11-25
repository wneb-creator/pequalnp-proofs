import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Iterate

namespace PEqualNP.Outside.L_meta_2602_aux

abbrev incident (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

lemma point_degree : ∀ p : Fin 13,
    (Finset.univ.filter fun l => incident p l).card = 4 := by
  decide

lemma line_degree : ∀ l : Fin 13,
    (Finset.univ.filter fun p => incident p l).card = 4 := by
  decide

lemma diagonal_incident (p : Fin 13) : incident p p := Or.inl rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma no_rectangle : ∀ p q l m : Fin 13,
    p ≠ q → incident p l → incident p m → incident q l → incident q m → l = m := by
  decide

lemma incidence_card :
    (Finset.univ.filter fun e : Fin 13 × Fin 13 => incident e.1 e.2).card = 52 := by
  decide

lemma deleted_incidence_card :
    (Finset.univ.filter fun e : Fin 13 × Fin 13 =>
      incident e.1 e.2 ∧ e.1 ≠ 0 ∧ e.2 ≠ 0).card = 45 := by
  decide

lemma vertex_cover_card (S T : Finset (Fin 13))
    (h : ∀ p l, incident p l → p ∈ S ∨ l ∈ T) :
    13 ≤ S.card + T.card := by
  have cover : (Finset.univ : Finset (Fin 13)) ⊆ S ∪ T := by
    intro i _
    exact Finset.mem_union.mpr (h i i (diagonal_incident i))
  have hc := Finset.card_le_card cover
  have hu := Finset.card_union_le S T
  have hn : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
  omega

lemma deleted_vertex_cover_card (S T : Finset (Fin 13))
    (h : ∀ p l, incident p l → p ≠ 0 → l ≠ 0 → p ∈ S ∨ l ∈ T) :
    12 ≤ S.card + T.card := by
  have cover : (Finset.univ.erase 0 : Finset (Fin 13)) ⊆ S ∪ T := by
    intro i hi
    have hn : i ≠ 0 := (Finset.mem_erase.mp hi).1
    exact Finset.mem_union.mpr (h i i (diagonal_incident i) hn hn)
  have hc := Finset.card_le_card cover
  have hu := Finset.card_union_le S T
  have hn : (Finset.univ.erase 0 : Finset (Fin 13)).card = 12 := by decide
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma successor_orbit : ∀ i j : Fin 13, ∃ k : Fin 13,
    (fun p : Fin 13 => p + 1)^[k.val] i = j := by
  decide

lemma minimum_vertex_cover (S T : Finset (Fin 13))
    (h : ∀ p l, incident p l → p ∈ S ∨ l ∈ T)
    (hsz : S.card + T.card ≤ 13) :
    (S = ∅ ∧ T = Finset.univ) ∨ (S = Finset.univ ∧ T = ∅) := by
  have hu : S ∪ T = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact h i i (diagonal_incident i)
  have hi : S ∩ T = ∅ := by
    apply Finset.card_eq_zero.mp
    have hc := Finset.card_union_add_card_inter S T
    have hn : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
    rw [hu, hn] at hc
    omega
  have disj (i : Fin 13) (hs : i ∈ S) (ht : i ∈ T) : False := by
    have hm := Finset.mem_inter.mpr ⟨hs, ht⟩
    simpa [hi] using hm
  by_cases he : S = ∅
  · left
    refine ⟨he, ?_⟩
    ext i
    simp only [Finset.mem_univ, iff_true]
    simpa [he] using h i i (diagonal_incident i)
  · right
    have step (i : Fin 13) (hs : i ∈ S) : i + 1 ∈ S := by
      rcases h (i + 1) i (Or.inr (Or.inl rfl)) with hs' | ht
      · exact hs'
      · exact (disj i hs ht).elim
    obtain ⟨i, hiS⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have walk (k : ℕ) : (fun p : Fin 13 => p + 1)^[k] i ∈ S := by
      induction k with
      | zero => exact hiS
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact step _ ih
    have all (j : Fin 13) : j ∈ S := by
      obtain ⟨k, hk⟩ := successor_orbit i j
      rw [← hk]
      exact walk k.val
    constructor
    · ext j
      simp only [Finset.mem_univ, iff_true]
      exact all j
    · apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      exact disj j (all j) hj

lemma rectangle_thin (S T : Finset (Fin 13))
    (h : ∀ p ∈ S, ∀ l ∈ T, incident p l) : S.card ≤ 1 ∨ T.card ≤ 1 := by
  by_cases hs : S.card ≤ 1
  · exact Or.inl hs
  by_cases ht : T.card ≤ 1
  · exact Or.inr ht
  exfalso
  apply hs
  apply Finset.card_le_one.mpr
  intro p hp q hq
  by_contra hpq
  apply ht
  apply Finset.card_le_one.mpr
  intro l hl m hm
  exact no_rectangle p q l m hpq (h p hp l hl) (h p hp m hm)
    (h q hq l hl) (h q hq m hm)

lemma rectangle_card_le_four (S T : Finset (Fin 13))
    (h : ∀ p ∈ S, ∀ l ∈ T, incident p l) : S.card * T.card ≤ 4 := by
  by_cases hs : S = ∅
  · simp [hs]
  by_cases ht : T = ∅
  · simp [ht]
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hs
  obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.mpr ht
  have hbS : S.card ≤ 4 := by
    have sub : S ⊆ Finset.univ.filter (fun q => incident q l) := by
      intro q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, h q hq l hl⟩
    simpa [line_degree l] using Finset.card_le_card sub
  have hbT : T.card ≤ 4 := by
    have sub : T ⊆ Finset.univ.filter (fun m => incident p m) := by
      intro m hm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ m, h p hp m hm⟩
    simpa [point_degree p] using Finset.card_le_card sub
  have hpS : 0 < S.card := Finset.card_pos.mpr ⟨p, hp⟩
  have hpT : 0 < T.card := Finset.card_pos.mpr ⟨l, hl⟩
  rcases rectangle_thin S T h with hS | hT
  · have he : S.card = 1 := by omega
    simpa [he] using hbT
  · have he : T.card = 1 := by omega
    simpa [he] using hbS

end PEqualNP.Outside.L_meta_2602_aux
