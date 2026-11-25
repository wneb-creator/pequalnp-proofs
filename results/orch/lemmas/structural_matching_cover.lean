import PEqualNP.Defs
import Mathlib.Combinatorics.Hall.Finite


namespace PEqualNP.Outside.L_meta_5012

def threeByThreeCode (E : Fin 3 → Fin 3 → Bool) : Fin 512 :=
  (if E 0 0 then 1 else 0) + (if E 0 1 then 2 else 0) + (if E 0 2 then 4 else 0) +
  (if E 1 0 then 8 else 0) + (if E 1 1 then 16 else 0) + (if E 1 2 then 32 else 0) +
  (if E 2 0 then 64 else 0) + (if E 2 1 then 128 else 0) + (if E 2 2 then 256 else 0)

def fiveIndependentMasks (E : Fin 3 → Fin 3 → Bool) : List ℕ :=
  match (threeByThreeCode E).val with
  | 273 => [7, 14, 21, 28, 35]
  | 275 => [7, 14, 28, 35, 42]
  | 277 => [7, 14, 21, 28, 42]
  | 279 => [7, 14, 28, 42, 56]
  | 281 => [7, 21, 28, 35, 49]
  | 285 => [7, 21, 28, 34, 56]
  | 305 => [7, 14, 21, 28, 49]
  | 307 => [7, 14, 28, 33, 56]
  | 309 => [7, 14, 21, 28, 56]
  | 313 => [7, 21, 28, 49, 56]
  | 337 => [7, 21, 35, 42, 49]
  | 339 => [7, 20, 35, 42, 56]
  | 345 => [7, 21, 35, 49, 56]
  | 369 => [7, 10, 21, 49, 56]
  | 371 => [7, 10, 20, 33, 56]
  | 401 => [7, 14, 35, 42, 49]
  | 403 => [7, 14, 35, 42, 56]
  | 405 => [7, 14, 17, 42, 56]
  | 409 => [7, 12, 35, 49, 56]
  | 413 => [7, 12, 17, 34, 56]
  | 465 => [7, 35, 42, 49, 56]
  | _ => []

def fiveIndependentWitness (E : Fin 3 → Fin 3 → Bool)
    (r : Fin 5) (v : Fin 6) : Bool :=
  ((fiveIndependentMasks E).getD r.val 0).testBit v.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma finiteFiveCertificates :
    ∀ E : Fin 3 → Fin 3 → Bool,
      (∀ i : Fin 3, E i i = true) →
      (∀ i j a b : Fin 3, i ≠ j → a ≠ b →
        ¬ (E i a = true ∧ E i b = true ∧ E j a = true ∧ E j b = true)) →
      (∀ r : Fin 5, ∀ i j : Fin 3, E i j = true →
        ¬ (fiveIndependentWitness E r (Fin.castAdd 3 i) = true ∧
          fiveIndependentWitness E r (Fin.natAdd 3 j) = true)) ∧
      (∀ r s : Fin 5, r ≠ s → ∃ i : Fin 3,
        (fiveIndependentWitness E r (Fin.castAdd 3 i) = true ∧
          fiveIndependentWitness E s (Fin.natAdd 3 i) = true) ∨
        (fiveIndependentWitness E s (Fin.castAdd 3 i) = true ∧
          fiveIndependentWitness E r (Fin.natAdd 3 i) = true)) := by
  decide

lemma fiveIndependentCertificate (E : Fin 3 → Fin 3 → Bool)
    (hd : ∀ i : Fin 3, E i i = true)
    (h4 : ∀ i j a b : Fin 3, i ≠ j → a ≠ b →
      ¬ (E i a = true ∧ E i b = true ∧ E j a = true ∧ E j b = true)) :
    ∃ t : Fin 5 → Fin 6 → Bool,
      (∀ r : Fin 5, ∀ i j : Fin 3, E i j = true →
        ¬ (t r (Fin.castAdd 3 i) = true ∧ t r (Fin.natAdd 3 j) = true)) ∧
      (∀ r s : Fin 5, r ≠ s → ∃ i : Fin 3,
        (t r (Fin.castAdd 3 i) = true ∧ t s (Fin.natAdd 3 i) = true) ∨
        (t s (Fin.castAdd 3 i) = true ∧ t r (Fin.natAdd 3 i) = true)) := by
  exact ⟨fiveIndependentWitness E, finiteFiveCertificates E hd h4⟩

end PEqualNP.Outside.L_meta_5012

namespace PEqualNP.Outside.L_meta_5012.FourClause

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma five_witness_clause_obstruction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Fin 4 → Finset (Fin n)) (W : Fin 5 → Finset (Fin n)) (a b : Fin 3 → Fin n)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ c : Fin 4, ∃ u ∈ A c, x u = true) → graphFun G ∅ x = true)
    (hindependent : ∀ r : Fin 5, ∀ u ∈ W r, ∀ v ∈ W r, ¬ G.Adj u v)
    (haccept : ∀ c : Fin 4, ∀ i : Fin 3, a i ∈ A c ∨ b i ∈ A c)
    (hconflict : ∀ r s : Fin 5, r ≠ s →
      ∃ i : Fin 3, (a i ∈ W r ∧ b i ∈ W s) ∨ (a i ∈ W s ∧ b i ∈ W r)) : False := by
  classical
  have hmiss : ∀ r : Fin 5, ∃ c : Fin 4, Disjoint (A c) (W r) := by
    intro r
    by_contra hnone
    push Not at hnone
    let x : Fin n → Bool := fun u => decide (u ∈ W r)
    have hall : ∀ c : Fin 4, ∃ u ∈ A c, x u = true := by
      intro c
      obtain ⟨u, huA, huW⟩ := Finset.not_disjoint_iff.mp (hnone c)
      exact ⟨u, huA, by simpa [x] using huW⟩
    have hf := hsafe x hall
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hf
    obtain ⟨u, v, huv, hu, hv⟩ := hf
    exact hindependent r u (by simpa [x] using hu) v (by simpa [x] using hv) huv
  choose f hf using hmiss
  have hinj : Function.Injective f := by
    intro r s hrs
    by_contra hne
    obtain ⟨i, hi⟩ := hconflict r s hne
    have hfr := Finset.disjoint_left.mp (hf r)
    have hfs := Finset.disjoint_left.mp (hf s)
    rcases haccept (f r) i with ha | hb
    · rcases hi with ⟨har, _⟩ | ⟨has, _⟩
      · exact hfr ha har
      · exact hfs (hrs ▸ ha) has
    · rcases hi with ⟨_, hbs⟩ | ⟨_, hbr⟩
      · exact hfs (hrs ▸ hb) hbs
      · exact hfr hb hbr
  have hcard := Fintype.card_le_of_injective f hinj
  simp at hcard

end PEqualNP.Outside.L_meta_5012.FourClause

namespace PEqualNP.Outside.L_meta_5012.FourClause

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma no_three_accepted_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (hfour : NoFourCycle G)
    (A : Fin 4 → Finset (Fin n))
    (hsafe : ∀ x : Fin n → Bool,
      (∀ c : Fin 4, ∃ u ∈ A c, x u = true) → graphFun G ∅ x = true)
    (a b : Fin 3 → Fin n) (ha : Function.Injective a) (hb : Function.Injective b)
    (hla : ∀ i, s (a i) = false) (hrb : ∀ i, s (b i) = true)
    (hedge : ∀ i, G.Adj (a i) (b i))
    (haccept : ∀ c : Fin 4, ∀ i : Fin 3, a i ∈ A c ∨ b i ∈ A c) : False := by
  classical
  let E : Fin 3 → Fin 3 → Bool := fun i j => decide (G.Adj (a i) (b j))
  have hdiag : ∀ i, E i i = true := by
    intro i
    simpa [E] using hedge i
  have hEfour : ∀ i j c d : Fin 3, i ≠ j → c ≠ d →
      ¬ (E i c = true ∧ E i d = true ∧ E j c = true ∧ E j d = true) := by
    intro i j c d hij hcd hh
    have hne : a i ≠ a j := fun he => hij (ha he)
    have hbound := hfour (a i) (a j) hne
    have hc : b c ∈ Finset.univ.filter (fun v => G.Adj (a i) v ∧ G.Adj (a j) v) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simpa [E] using hh.1, by simpa [E] using hh.2.2.1⟩
    have hd : b d ∈ Finset.univ.filter (fun v => G.Adj (a i) v ∧ G.Adj (a j) v) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simpa [E] using hh.2.1, by simpa [E] using hh.2.2.2⟩
    exact hcd (hb (Finset.card_le_one.mp hbound _ hc _ hd))
  obtain ⟨t, htind, htconf⟩ := fiveIndependentCertificate E hdiag hEfour
  let W : Fin 5 → Finset (Fin n) := fun r => Finset.univ.filter (fun v =>
    (∃ i : Fin 3, t r (Fin.castAdd 3 i) = true ∧ a i = v) ∨
    (∃ i : Fin 3, t r (Fin.natAdd 3 i) = true ∧ b i = v))
  have memW : ∀ r v, v ∈ W r ↔
      (∃ i : Fin 3, t r (Fin.castAdd 3 i) = true ∧ a i = v) ∨
      (∃ i : Fin 3, t r (Fin.natAdd 3 i) = true ∧ b i = v) := by
    intro r v
    simp [W]
  have leftW : ∀ r i, t r (Fin.castAdd 3 i) = true → a i ∈ W r := by
    intro r i hi
    exact (memW r _).mpr (Or.inl ⟨i, hi, rfl⟩)
  have rightW : ∀ r i, t r (Fin.natAdd 3 i) = true → b i ∈ W r := by
    intro r i hi
    exact (memW r _).mpr (Or.inr ⟨i, hi, rfl⟩)
  have hWind : ∀ r : Fin 5, ∀ u ∈ W r, ∀ v ∈ W r, ¬ G.Adj u v := by
    intro r u hu v hv huv
    rw [memW] at hu hv
    rcases hu with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · rcases hv with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · exact hbip _ _ huv (by rw [hla i, hla j])
      · exact htind r i j (by simpa [E] using huv) ⟨hi, hj⟩
    · rcases hv with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · exact htind r j i (by simpa [E] using huv.symm) ⟨hj, hi⟩
      · exact hbip _ _ huv (by rw [hrb i, hrb j])
  have hWconf : ∀ r s : Fin 5, r ≠ s →
      ∃ i : Fin 3, (a i ∈ W r ∧ b i ∈ W s) ∨ (a i ∈ W s ∧ b i ∈ W r) := by
    intro r s hrs
    obtain ⟨i, hi⟩ := htconf r s hrs
    refine ⟨i, ?_⟩
    exact hi.imp (fun h => ⟨leftW r i h.1, rightW s i h.2⟩)
      (fun h => ⟨leftW s i h.1, rightW r i h.2⟩)
  exact five_witness_clause_obstruction G A W a b hsafe hWind haccept hWconf

end PEqualNP.Outside.L_meta_5012.FourClause


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

namespace PEqualNP.Outside.L_meta_5012.FourClause

lemma four_clause_vertex_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hfour : PEqualNP.TopForm.NoFourCycle G) (A : Fin 4 → Finset (Fin n))
    (hsafe : ∀ x : Fin n → Bool,
      (∀ c : Fin 4, ∃ u ∈ A c, x u = true) →
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧
      ∀ u v, G.Adj u v → (∀ c : Fin 4, u ∈ A c ∨ v ∈ A c) → u ∈ K ∨ v ∈ K := by
  classical
  let H : SimpleGraph (Fin n) :=
    { Adj := fun u v => G.Adj u v ∧ ∀ c : Fin 4, u ∈ A c ∨ v ∈ A c
      symm.symm := by
        intro u v h
        exact ⟨h.1.symm, fun c => (h.2 c).symm⟩
      loopless.irrefl := by
        intro u h
        exact G.irrefl h.1 }
  have hH : ∀ u v, H.Adj u v → s u ≠ s v := fun u v h => hbip u v h.1
  obtain ⟨K, hK, hcov⟩ := MatchingCover.graph_cover_two H s hH (by
    intro a b ha hb hla hrb he
    exact no_three_accepted_edges G s hbip hfour A hsafe a b ha hb hla hrb
      (fun i => (he i).1) (fun c i => (he i).2 c))
  exact ⟨K, hK, fun u v huv hA => hcov ⟨huv, hA⟩⟩

end PEqualNP.Outside.L_meta_5012.FourClause
