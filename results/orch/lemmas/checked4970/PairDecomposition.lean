import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.PairDecomposition

theorem list_pairs {A : Type} [DecidableEq A] (xs : List A) :
    xs.Nodup → Even xs.length →
    ∃ ps : List (A × A), 2 * ps.length = xs.length ∧
      (∀ t ∈ ps, t.1 ≠ t.2 ∧ t.1 ∈ xs ∧ t.2 ∈ xs) ∧
      ∀ a ∈ xs, ∃ t ∈ ps, a = t.1 ∨ a = t.2 := by
  induction xs using List.twoStepInduction with
  | nil =>
      intro _ _
      exact ⟨[], by simp, by simp, by simp⟩
  | singleton a =>
      intro _ h
      simp at h
  | cons_cons a b xs ih _ =>
      intro hn he
      have hab : a ≠ b := by
        exact fun h => (List.nodup_cons.mp hn).1 (by simp [h])
      have hxs : xs.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2
      have hexs : Even xs.length := by
        obtain ⟨k, hk⟩ := he
        refine ⟨k - 1, ?_⟩
        simp only [List.length_cons] at hk
        omega
      obtain ⟨ps, hlen, hvalid, hcover⟩ := ih hxs hexs
      refine ⟨(a, b) :: ps, ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨hab, by simp, by simp⟩
        · obtain ⟨h1, h2, h3⟩ := hvalid t ht
          exact ⟨h1, by simp [h2], by simp [h3]⟩
      · intro c hc
        rcases List.mem_cons.mp hc with hca | hc
        · exact ⟨(a, b), by simp, Or.inl hca⟩
        rcases List.mem_cons.mp hc with hcb | hc
        · exact ⟨(a, b), by simp, Or.inr hcb⟩
        obtain ⟨t, ht, hc⟩ := hcover c hc
        exact ⟨t, List.mem_cons_of_mem _ ht, hc⟩

def row {p l : Nat} (E : Finset (Fin p × Fin l)) (a : Fin p) : Finset (Fin l) :=
  Finset.univ.filter fun b => (a, b) ∈ E

theorem row_card_sum {p l : Nat} (E : Finset (Fin p × Fin l)) :
    ∑ a : Fin p, (row E a).card = E.card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := E) (t := Finset.univ)
    (f := fun t : Fin p × Fin l => t.1) (by simp)
  have hf : ∀ a : Fin p, E.filter (fun t => t.1 = a) =
      (row E a).image (fun b => (a, b)) := by
    intro a
    ext ⟨u, b⟩
    simp only [Finset.mem_filter, Finset.mem_image, row, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ht, rfl⟩
      exact ⟨b, ht, rfl⟩
    · rintro ⟨c, hc, he⟩
      have h1 : a = u := congrArg Prod.fst he
      have h2 : c = b := congrArg Prod.snd he
      subst u c
      exact ⟨hc, rfl⟩
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  rw [hf a, Finset.card_image_of_injective]
  exact fun b c h => congrArg Prod.snd h

theorem pairs_of_even_rows {p l : Nat} (E : Finset (Fin p × Fin l))
    (heven : ∀ a : Fin p, Even (row E a).card) :
    ∃ ps : List (Fin p × (Fin l × Fin l)),
      2 * ps.length = E.card ∧
      (∀ t ∈ ps, t.2.1 ≠ t.2.2 ∧ (t.1, t.2.1) ∈ E ∧ (t.1, t.2.2) ∈ E) ∧
      ∀ a b, (a, b) ∈ E → ∃ t ∈ ps, t.1 = a ∧ (t.2.1 = b ∨ t.2.2 = b) := by
  classical
  have hp : ∀ a : Fin p, ∃ qs : List (Fin l × Fin l),
      2 * qs.length = (row E a).card ∧
      (∀ t ∈ qs, t.1 ≠ t.2 ∧ t.1 ∈ row E a ∧ t.2 ∈ row E a) ∧
      ∀ b ∈ row E a, ∃ t ∈ qs, b = t.1 ∨ b = t.2 := by
    intro a
    simpa using list_pairs (row E a).toList (row E a).nodup_toList (by simpa using heven a)
  choose qs hlen hvalid hcover using hp
  let ps := (List.ofFn fun a : Fin p => (qs a).map fun t => (a, t)).flatten
  have hmem : ∀ t, t ∈ ps ↔ t.2 ∈ qs t.1 := by
    intro t
    constructor
    · intro ht
      obtain ⟨s, hs, ht⟩ := List.mem_flatten.mp ht
      obtain ⟨a, ha⟩ := List.mem_ofFn.mp hs
      rw [← ha] at ht
      obtain ⟨u, hu, he⟩ := List.mem_map.mp ht
      have h1 : a = t.1 := congrArg Prod.fst he
      have h2 : u = t.2 := congrArg Prod.snd he
      simpa only [h1, h2] using hu
    · intro ht
      exact List.mem_flatten.mpr ⟨(qs t.1).map fun u => (t.1, u),
        List.mem_ofFn.mpr ⟨t.1, rfl⟩, List.mem_map.mpr ⟨t.2, ht, Prod.eta t⟩⟩
  refine ⟨ps, ?_, ?_, ?_⟩
  · simp only [ps, List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def,
      List.length_map]
    rw [Finset.mul_sum]
    simpa only [hlen] using row_card_sum E
  · intro t ht
    obtain ⟨hn, h1, h2⟩ := hvalid t.1 t.2 ((hmem t).mp ht)
    exact ⟨hn, (Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2⟩
  · intro a b hab
    obtain ⟨u, hu, hb⟩ := hcover a b (by simpa [row] using hab)
    refine ⟨(a, u), (hmem _).mpr hu, rfl, ?_⟩
    exact hb.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

end PEqualNP.Outside.L_meta_4970_aux.PairDecomposition
