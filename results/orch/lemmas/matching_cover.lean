import PEqualNP.Defs
import Mathlib.Combinatorics.Hall.Finite

namespace PEqualNP.Outside.L_meta_5012.MatchingCover

lemma relation_cover_two {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → Prop)
    (hthree : ∀ (a : Fin 3 → α) (b : Fin 3 → β),
      Function.Injective a → Function.Injective b →
      (∀ i, R (a i) (b i)) → False) :
    ∃ A : Finset α, ∃ B : Finset β,
      A.card + B.card ≤ 2 ∧ ∀ a b, R a b → a ∈ A ∨ b ∈ B := by
  classical
  by_cases hn : Fintype.card α ≤ 2
  · exact ⟨Finset.univ, ∅, by simpa, fun _ _ _ => Or.inl (Finset.mem_univ _)⟩
  have hn3 : 3 ≤ Fintype.card α := by omega
  by_contra hnone
  have hbound (A : Finset α) (B : Finset β)
      (hcover : ∀ a b, R a b → a ∈ A ∨ b ∈ B) : 3 ≤ A.card + B.card := by
    by_contra hlt
    exact hnone ⟨A, B, by omega, hcover⟩
  let N (S : Finset α) : Finset β := Finset.univ.filter fun b => ∃ a ∈ S, R a b
  have hdef (S : Finset α) : S.card ≤ (N S).card + (Fintype.card α - 3) := by
    have hcov : ∀ a b, R a b → a ∈ Finset.univ \ S ∨ b ∈ N S := by
      intro a b hab
      by_cases ha : a ∈ S
      · apply Or.inr
        simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨a, ha, hab⟩
      · exact Or.inl (by simp [ha])
    have hb := hbound (Finset.univ \ S) (N S) hcov
    have he : (Finset.univ \ S).card = Fintype.card α - S.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
    have hS : S.card ≤ Fintype.card α := Finset.card_le_univ S
    omega
  let T (a : α) : Finset (β ⊕ Fin (Fintype.card α - 3)) :=
    (Finset.univ.filter (R a)).disjSum Finset.univ
  have hhall (S : Finset α) : S.card ≤ (S.biUnion T).card := by
    by_cases hs : S = ∅
    · simp [hs]
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
    have he : S.biUnion T = (N S).disjSum Finset.univ := by
      ext y
      cases y with
      | inl b => simp [T, N]
      | inr k => simpa [T, Finset.Nonempty] using hne
    rw [he, Finset.card_disjSum, Finset.card_univ, Fintype.card_fin]
    exact hdef S
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' T).mp hhall
  let E : Finset α := Finset.univ.filter fun a => ∃ k, f a = Sum.inr k
  have he (a : E) : ∃ k, f a = Sum.inr k := (Finset.mem_filter.mp a.property).2
  let d : E → Fin (Fintype.card α - 3) := fun a => Classical.choose (he a)
  have hd (a : E) : f a = Sum.inr (d a) := Classical.choose_spec (he a)
  have hdi : Function.Injective d := by
    intro a b hab
    apply Subtype.ext
    apply hf
    rw [hd a, hd b, hab]
  have hE : E.card ≤ Fintype.card α - 3 := by
    simpa using Fintype.card_le_of_injective d hdi
  let D : Finset α := Finset.univ \ E
  have hD : 3 ≤ D.card := by
    have heq : D.card = Fintype.card α - E.card := by
      dsimp only [D]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ E), Finset.card_univ]
    omega
  have hreal (a : D) : ∃ b, f a = Sum.inl b := by
    have ha : a.val ∉ E := (Finset.mem_sdiff.mp a.property).2
    cases hfa : f a.val with
    | inl b => exact ⟨b, rfl⟩
    | inr k => exact False.elim (ha (by simp [E, hfa]))
  have hDcard : 3 ≤ Fintype.card D := by simpa using hD
  let e : Fin 3 ↪ D :=
    { toFun := fun i => (Fintype.equivFin D).symm ⟨i.val, lt_of_lt_of_le i.isLt hDcard⟩
      inj' := by
        intro i j hij
        have hh := congrArg (Fintype.equivFin D) hij
        simp only [Equiv.apply_symm_apply] at hh
        exact Fin.ext (congrArg (fun k : Fin (Fintype.card D) => k.val) hh) }
  let a : Fin 3 → α := fun i => (e i).val
  let b : Fin 3 → β := fun i => Classical.choose (hreal (e i))
  have hab (i : Fin 3) : f (a i) = Sum.inl (b i) := Classical.choose_spec (hreal (e i))
  have hai : Function.Injective a := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hbi : Function.Injective b := by
    intro i j hij
    apply hai
    apply hf
    rw [hab i, hab j, hij]
  apply hthree a b hai hbi
  intro i
  have hm := hmem (a i)
  rw [hab i] at hm
  simpa [T] using hm

lemma graph_cover_two {n : ℕ} (G : SimpleGraph (Fin n)) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hthree : ∀ (a b : Fin 3 → Fin n),
      Function.Injective a → Function.Injective b →
      (∀ i, s (a i) = false) → (∀ i, s (b i) = true) →
      (∀ i, G.Adj (a i) (b i)) → False) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧ G.IsVertexCover (↑K) := by
  classical
  let α := {v : Fin n // s v = false}
  let β := {v : Fin n // s v = true}
  have hrel : ∀ (a : Fin 3 → α) (b : Fin 3 → β),
      Function.Injective a → Function.Injective b →
      (∀ i, G.Adj (a i).val (b i).val) → False := by
    intro a b ha hb he
    exact hthree (fun i => (a i).val) (fun i => (b i).val)
      (Subtype.val_injective.comp ha) (Subtype.val_injective.comp hb)
      (fun i => (a i).property) (fun i => (b i).property) he
  obtain ⟨A, B, hcard, hcov⟩ :=
    relation_cover_two (fun (a : α) (b : β) => G.Adj a.val b.val) hrel
  let K : Finset (Fin n) := A.image Subtype.val ∪ B.image Subtype.val
  have hKA (a : α) (ha : a ∈ A) : a.val ∈ K :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hKB (b : β) (hb : b ∈ B) : b.val ∈ K :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  refine ⟨K, ?_, ?_⟩
  · exact (Finset.card_union_le _ _).trans
      ((Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)).trans hcard)
  · intro u v huv
    change u ∈ K ∨ v ∈ K
    cases hu : s u with
    | false =>
        have hv : s v = true := by
          cases hv : s v with
          | false => exact False.elim ((hbip u v huv) (hu.trans hv.symm))
          | true => rfl
        rcases hcov ⟨u, hu⟩ ⟨v, hv⟩ huv with ha | hb
        · exact Or.inl (hKA ⟨u, hu⟩ ha)
        · exact Or.inr (hKB ⟨v, hv⟩ hb)
    | true =>
        have hv : s v = false := by
          cases hv : s v with
          | false => rfl
          | true => exact False.elim ((hbip u v huv) (hu.trans hv.symm))
        rcases hcov ⟨v, hv⟩ ⟨u, hu⟩ huv.symm with ha | hb
        · exact Or.inr (hKA ⟨v, hv⟩ ha)
        · exact Or.inl (hKB ⟨u, hu⟩ hb)

end PEqualNP.Outside.L_meta_5012.MatchingCover
