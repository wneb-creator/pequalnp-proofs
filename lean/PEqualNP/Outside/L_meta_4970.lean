import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Find
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi

namespace PEqualNP.Outside.L_meta_4970

lemma star_centre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q : Finset (Fin l)} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : a = a' := by
  by_cases h : a = a'
  · exact h
  · obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp
      (lt_of_lt_of_le (by decide : 1 < 2) hQ)
    exact False.elim (hE a a' b b' h hbb' ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩)

lemma distinct_centres_intersection_card {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q Q' : Finset (Fin l)} (haa' : a ≠ a')
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q', (a', b) ∈ E) :
    (Q ∩ Q').card ≤ 1 := by
  by_cases h : (Q ∩ Q').card ≤ 1
  · exact h
  · have hQ : 2 ≤ (Q ∩ Q').card := Nat.lt_of_not_ge h
    exact False.elim (haa' (star_centre_unique E hE hQ
      (fun b hb => ha b (Finset.mem_inter.mp hb).1)
      (fun b hb => ha' b (Finset.mem_inter.mp hb).2)))

lemma or_function_determines_leaves {α : Type*} [DecidableEq α]
    (Q R : Finset α)
    (h : ∀ x : α → Bool, decide (∃ b ∈ Q, x b = true) =
      decide (∃ b ∈ R, x b = true)) : Q = R := by
  ext b
  have hb := h (fun a => decide (a = b))
  simpa using hb

lemma line_or_function_determines_leaves {p l : ℕ} (Q R : Finset (Fin l))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) =
        decide (∃ b ∈ R, x (Fin.natAdd p b) = true)) : Q = R := by
  apply or_function_determines_leaves
  intro x
  simpa using h (Fin.addCases (fun _ => false) x)

lemma point_or_function_determines_leaves {p l : ℕ} (P R : Finset (Fin p))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
        decide (∃ a ∈ R, x (Fin.castAdd l a) = true)) : P = R := by
  apply or_function_determines_leaves
  intro x
  simpa using h (Fin.addCases x (fun _ => false))

lemma point_or_ne_line_or {p l : ℕ} (P : Finset (Fin p)) (Q : Finset (Fin l))
    (hP : P.Nonempty) :
    ¬ (∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
        decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) := by
  intro h
  have heq := h (Fin.addCases (fun _ => true) (fun _ => false))
  have hnot : ∀ a, a ∉ P := by simpa using heq
  obtain ⟨a, ha⟩ := hP
  exact hnot a ha

lemma star_family_cover_card {p l : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Finset (Fin p × Fin l)) (I : Finset ι)
    (B : ι → Finset (Fin p × Fin l)) (c : ι → Fin (p + l))
    (hcover : ∀ e ∈ E, ∃ i ∈ I, e ∈ B i)
    (hstar : ∀ i ∈ I, ∀ e ∈ B i, Fin.castAdd l e.1 = c i ∨ Fin.natAdd p e.2 = c i) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      S.card ≤ I.card ∧ E.card ≤ ∑ i ∈ I, (B i).card := by
  refine ⟨I.image c, ?_, Finset.card_image_le, ?_⟩
  · intro a b hab
    obtain ⟨i, hi, hib⟩ := hcover (a, b) hab
    have hci : c i ∈ I.image c := Finset.mem_image_of_mem c hi
    rcases hstar i hi (a, b) hib with h | h
    · exact Or.inl (h ▸ hci)
    · exact Or.inr (h ▸ hci)
  · have hsub : E ⊆ I.biUnion B := by
      intro e he
      obtain ⟨i, hi, hib⟩ := hcover e he
      exact Finset.mem_biUnion.mpr ⟨i, hi, hib⟩
    exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

lemma star_family_ledger {p l s : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Finset (Fin p × Fin l)) (I : Finset ι)
    (B : ι → Finset (Fin p × Fin l)) (c : ι → Fin (p + l))
    (hcover : ∀ e ∈ E, ∃ i ∈ I, e ∈ B i)
    (hstar : ∀ i ∈ I, ∀ e ∈ B i, Fin.castAdd l e.1 = c i ∨ Fin.natAdd p e.2 = c i)
    (hsize : (∑ i ∈ I, (B i).card) + I.card ≤ s + 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧ E.card + S.card ≤ s + 1 := by
  obtain ⟨S, hS, hScard, hEcard⟩ := star_family_cover_card E I B c hcover hstar
  exact ⟨S, hS, (Nat.add_le_add hEcard hScard).trans hsize⟩

lemma star_line_centre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} {P : Finset (Fin p)} (hP : 2 ≤ P.card)
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P, (a, b') ∈ E) : b = b' := by
  by_cases h : b = b'
  · exact h
  · obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp
      (lt_of_lt_of_le (by decide : 1 < 2) hP)
    exact False.elim (hE a a' b b' haa' h ⟨hb a ha, hb' a ha, hb a' ha', hb' a' ha'⟩)

lemma point_centre_unique_of_same_function {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q Q' : Finset (Fin l)} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q', (a', b) ∈ E)
    (f : (Fin (p + l) → Bool) → Bool)
    (hf : ∀ x, f x = decide (∃ b ∈ Q, x (Fin.natAdd p b) = true))
    (hf' : ∀ x, f x = decide (∃ b ∈ Q', x (Fin.natAdd p b) = true)) : a = a' := by
  have heq : Q = Q' := line_or_function_determines_leaves Q Q'
    (fun x => (hf x).symm.trans (hf' x))
  apply star_centre_unique E hE hQ ha
  intro b hb
  exact ha' b (heq ▸ hb)

lemma line_centre_unique_of_same_function {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} {P P' : Finset (Fin p)} (hP : 2 ≤ P.card)
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P', (a, b') ∈ E)
    (f : (Fin (p + l) → Bool) → Bool)
    (hf : ∀ x, f x = decide (∃ a ∈ P, x (Fin.castAdd l a) = true))
    (hf' : ∀ x, f x = decide (∃ a ∈ P', x (Fin.castAdd l a) = true)) : b = b' := by
  have heq : P = P' := point_or_function_determines_leaves P P'
    (fun x => (hf x).symm.trans (hf' x))
  apply star_line_centre_unique E hE hP hb
  intro a ha
  exact hb' a (heq ▸ ha)

lemma exists_private_edge_subfamily {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (E : Finset α) (I : Finset ι) (B : ι → Finset α)
    (hcover : E ⊆ I.biUnion B) :
    ∃ J : Finset ι, J ⊆ I ∧ E ⊆ J.biUnion B ∧
      ∀ i ∈ J, ∃ e ∈ E, e ∈ B i ∧ ∀ j ∈ J, j ≠ i → e ∉ B j := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ J : Finset ι, J ⊆ I ∧ E ⊆ J.biUnion B ∧ J.card = n
  have hex : ∃ n, P n := ⟨I.card, I, Finset.Subset.refl _, hcover, rfl⟩
  obtain ⟨J, hJI, hEJ, hJcard⟩ := Nat.find_spec hex
  refine ⟨J, hJI, hEJ, ?_⟩
  intro i hi
  have hnot : ¬ E ⊆ (J.erase i).biUnion B := by
    intro hsub
    have hmin : Nat.find hex ≤ (J.erase i).card := Nat.find_min' hex
      ⟨J.erase i, (Finset.erase_subset i J).trans hJI, hsub, rfl⟩
    rw [← hJcard] at hmin
    exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem hi)) hmin
  obtain ⟨e, he, hne⟩ := Finset.not_subset.mp hnot
  have hie : e ∈ B i := by
    obtain ⟨j, hj, heb⟩ := Finset.mem_biUnion.mp (hEJ he)
    by_cases hji : j = i
    · exact hji ▸ heb
    · exact False.elim (hne (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩, heb⟩))
  refine ⟨e, he, hie, ?_⟩
  intro j hj hji heb
  exact hne (Finset.mem_biUnion.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩, heb⟩)

lemma singleton_support_subset_of_below {α : Type*} [DecidableEq α]
    (S U : Finset α) (f : (α → Bool) → Bool)
    (hsupport : ∀ i, i ∈ S ↔ f (fun j => decide (j = i)) = true)
    (hbelow : ∀ x, f x = true → ∃ i ∈ U, x i = true) : S ⊆ U := by
  intro i hi
  obtain ⟨j, hj, hji⟩ := hbelow _ ((hsupport i).mp hi)
  have heq : j = i := of_decide_eq_true hji
  exact heq ▸ hj

lemma linear_family_support_unique {α ι : Type*} [DecidableEq α]
    (I : Finset ι) (U : ι → Finset α)
    (hlinear : ∀ c ∈ I, ∀ d ∈ I, c ≠ d → (U c ∩ U d).card ≤ 1)
    {c d : ι} (hc : c ∈ I) (hd : d ∈ I) (S : Finset α)
    (hlarge : 1 < S.card) (hSc : S ⊆ U c) (hSd : S ⊆ U d) : c = d := by
  by_cases hcd : c = d
  · exact hcd
  · have hsub : S ⊆ U c ∩ U d := by
      intro i hi
      exact Finset.mem_inter.mpr ⟨hSc hi, hSd hi⟩
    exact False.elim (Nat.not_lt_of_ge
      ((Finset.card_le_card hsub).trans (hlinear c hc d hd hcd)) hlarge)

lemma linear_family_paid_disjoint {α ι γ : Type*} [DecidableEq α]
    (I : Finset ι) (U : ι → Finset α) (P : ι → Finset γ) (S : γ → Finset α)
    (hlinear : ∀ c ∈ I, ∀ d ∈ I, c ≠ d → (U c ∩ U d).card ≤ 1)
    (hpaid : ∀ c ∈ I, ∀ g ∈ P c, 1 < (S g).card ∧ S g ⊆ U c) :
    (I : Set ι).PairwiseDisjoint P := by
  intro c hc d hd hcd
  apply Finset.disjoint_left.mpr
  intro g hgc hgd
  have hcg := hpaid c hc g hgc
  have hdg := hpaid d hd g hgd
  exact hcd (linear_family_support_unique I U hlinear hc hd (S g)
    hcg.1 hcg.2 hdg.2)

lemma linear_family_paid_sum_le {α ι γ : Type*} [DecidableEq α] [DecidableEq γ]
    (I : Finset ι) (U : ι → Finset α) (P : ι → Finset γ) (S : γ → Finset α)
    (G : Finset γ)
    (hlinear : ∀ c ∈ I, ∀ d ∈ I, c ≠ d → (U c ∩ U d).card ≤ 1)
    (hpaid : ∀ c ∈ I, ∀ g ∈ P c, 1 < (S g).card ∧ S g ⊆ U c)
    (hpool : ∀ c ∈ I, P c ⊆ G) : (∑ c ∈ I, (P c).card) ≤ G.card := by
  have hdisjoint := linear_family_paid_disjoint I U P S hlinear hpaid
  rw [← Finset.card_biUnion hdisjoint]
  apply Finset.card_le_card
  intro g hg
  obtain ⟨c, hc, hgc⟩ := Finset.mem_biUnion.mp hg
  exact hpool c hc hgc

lemma linear_family_aggregate {α β ι γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ]
    (E : Finset β) (I : Finset ι) (B : ι → Finset β) (U : ι → Finset α)
    (R : ι → Finset δ) (P : ι → Finset γ) (S : γ → Finset α)
    (hcover : E ⊆ I.biUnion B)
    (hlinear : ∀ c ∈ I, ∀ d ∈ I, c ≠ d → (U c ∩ U d).card ≤ 1)
    (hpaid : ∀ c ∈ I, ∀ g ∈ P c, 1 < (S g).card ∧ S g ⊆ U c)
    (hleaves : ∀ c ∈ I, (B c).card ≤ (U c).card)
    (hcount : ∀ c ∈ I, (U c).card ≤ (R c).card + (P c).card) :
    E.card ≤ (∑ c ∈ I, (R c).card) + (I.biUnion P).card := by
  have hdisjoint := linear_family_paid_disjoint I U P S hlinear hpaid
  calc
    E.card ≤ ∑ c ∈ I, (B c).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    _ ≤ ∑ c ∈ I, ((R c).card + (P c).card) :=
      Finset.sum_le_sum (fun c hc => (hleaves c hc).trans (hcount c hc))
    _ = (∑ c ∈ I, (R c).card) + (∑ c ∈ I, (P c).card) :=
      Finset.sum_add_distrib
    _ = (∑ c ∈ I, (R c).card) + (I.biUnion P).card := by
      rw [Finset.card_biUnion hdisjoint]

lemma linear_family_aggregate_pool {α β ι γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ]
    (E : Finset β) (I : Finset ι) (B : ι → Finset β) (U : ι → Finset α)
    (R : ι → Finset δ) (P : ι → Finset γ) (S : γ → Finset α) (G : Finset γ)
    (hcover : E ⊆ I.biUnion B)
    (hlinear : ∀ c ∈ I, ∀ d ∈ I, c ≠ d → (U c ∩ U d).card ≤ 1)
    (hpaid : ∀ c ∈ I, ∀ g ∈ P c, 1 < (S g).card ∧ S g ⊆ U c)
    (hpool : ∀ c ∈ I, P c ⊆ G)
    (hleaves : ∀ c ∈ I, (B c).card ≤ (U c).card)
    (hcount : ∀ c ∈ I, (U c).card ≤ (R c).card + (P c).card) :
    E.card ≤ (∑ c ∈ I, (R c).card) + G.card := by
  have hsum := linear_family_aggregate E I B U R P S hcover hlinear hpaid hleaves hcount
  have hsub : I.biUnion P ⊆ G := by
    intro g hg
    obtain ⟨c, hc, hgc⟩ := Finset.mem_biUnion.mp hg
    exact hpool c hc hgc
  exact hsum.trans (Nat.add_le_add_left (Finset.card_le_card hsub) _)

lemma linear_family_component_aggregate {α β ι γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ]
    (E : Finset β) (I : Finset ι) (B : ι → Finset β) (U : ι → Finset α)
    (K : ι → ℕ) (P : ι → Finset γ) (S : γ → Finset α)
    (hcover : E ⊆ I.biUnion B)
    (hlinear : ∀ c ∈ I, ∀ d ∈ I, c ≠ d → (U c ∩ U d).card ≤ 1)
    (hpaid : ∀ c ∈ I, ∀ g ∈ P c, 1 < (S g).card ∧ S g ⊆ U c)
    (hleaves : ∀ c ∈ I, (B c).card ≤ (U c).card)
    (hcount : ∀ c ∈ I, (U c).card ≤ K c + (P c).card) :
    E.card ≤ (∑ c ∈ I, K c) + (I.biUnion P).card := by
  have hdisjoint := linear_family_paid_disjoint I U P S hlinear hpaid
  calc
    E.card ≤ ∑ c ∈ I, (B c).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    _ ≤ ∑ c ∈ I, (K c + (P c).card) :=
      Finset.sum_le_sum (fun c hc => (hleaves c hc).trans (hcount c hc))
    _ = (∑ c ∈ I, K c) + (∑ c ∈ I, (P c).card) := Finset.sum_add_distrib
    _ = (∑ c ∈ I, K c) + (I.biUnion P).card := by
      rw [Finset.card_biUnion hdisjoint]

lemma linear_family_component_aggregate_pool {α β ι γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (E : Finset β) (I : Finset ι) (B : ι → Finset β) (U : ι → Finset α)
    (K : ι → ℕ) (P : ι → Finset γ) (S : γ → Finset α) (G : Finset γ)
    (hcover : E ⊆ I.biUnion B)
    (hlinear : ∀ c ∈ I, ∀ d ∈ I, c ≠ d → (U c ∩ U d).card ≤ 1)
    (hpaid : ∀ c ∈ I, ∀ g ∈ P c, 1 < (S g).card ∧ S g ⊆ U c)
    (hpool : ∀ c ∈ I, P c ⊆ G)
    (hleaves : ∀ c ∈ I, (B c).card ≤ (U c).card)
    (hcount : ∀ c ∈ I, (U c).card ≤ K c + (P c).card) :
    E.card ≤ (∑ c ∈ I, K c) + G.card := by
  have hsum := linear_family_component_aggregate E I B U K P S
    hcover hlinear hpaid hleaves hcount
  have hsub : I.biUnion P ⊆ G := by
    intro g hg
    obtain ⟨c, hc, hgc⟩ := Finset.mem_biUnion.mp hg
    exact hpool c hc hgc
  exact hsum.trans (Nat.add_le_add_left (Finset.card_le_card hsub) _)

lemma reverse_star_centre_unique {p l : ℕ} {E : Finset (Fin p × Fin l)}
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} {P : Finset (Fin p)} (hP : 2 ≤ P.card)
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P, (a, b') ∈ E) : b = b' := by
  by_contra hne
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by decide : 1 < 2) hP)
  exact hfour a a' b b' haa' hne ⟨hb a ha, hb' a ha, hb a' ha', hb' a' ha'⟩

end PEqualNP.Outside.L_meta_4970

namespace PEqualNP.Outside.L_meta_4970

lemma graph_card_le_edges_add_components {V : Type*} [Finite V] (G : SimpleGraph V) :
    Nat.card V ≤ G.edgeSet.ncard + Nat.card G.ConnectedComponent := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite G.ConnectedComponent
  calc
    Nat.card V = ∑ c : G.ConnectedComponent, c.supp.ncard :=
      G.sum_connectedComponent_ncard_supp.symm
    _ ≤ ∑ c : G.ConnectedComponent, (c.toSimpleGraph.edgeSet.ncard + 1) := by
      apply Finset.sum_le_sum
      intro c hc
      exact c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
    _ = G.edgeSet.ncard + Nat.card G.ConnectedComponent := by
      rw [Finset.sum_add_distrib, G.sum_connectedComponent_ncard_edgeSet]
      simp [Nat.card_eq_fintype_card]

lemma component_card_le_of_reachable {V : Type*} [Finite V] (G H : SimpleGraph V)
    (h : ∀ u v, H.Reachable u v → G.Reachable u v) :
    Nat.card G.ConnectedComponent ≤ Nat.card H.ConnectedComponent := by
  let f : H.ConnectedComponent → G.ConnectedComponent :=
    Quot.map id (fun u v huv => h u v huv)
  apply Nat.card_le_card_of_surjective f
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v => exact ⟨H.connectedComponentMk v, rfl⟩

lemma graph_card_le_edges_add_larger_components {V : Type*} [Finite V]
    (G H : SimpleGraph V) (h : ∀ u v, H.Reachable u v → G.Reachable u v) :
    Nat.card V ≤ G.edgeSet.ncard + Nat.card H.ConnectedComponent := by
  exact (graph_card_le_edges_add_components G).trans
    (Nat.add_le_add_left (component_card_le_of_reachable G H h) _)

lemma graph_from_pairs_edge_count {V : Type*} [DecidableEq V] (E : Finset (V × V)) :
    (SimpleGraph.fromRel (fun a b => (a, b) ∈ E)).edgeSet.ncard ≤ E.card := by
  classical
  let F : Finset (Sym2 V) := E.image (fun p => s(p.1, p.2))
  have hsub : (SimpleGraph.fromRel (fun a b => (a, b) ∈ E)).edgeSet ⊆ (F : Set (Sym2 V)) := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      intro he
      change a ≠ b ∧ ((a, b) ∈ E ∨ (b, a) ∈ E) at he
      rcases he.2 with hab | hba
      · exact Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩
      · exact Finset.mem_image.mpr ⟨(b, a), hba, Sym2.eq_swap⟩
  calc
    (SimpleGraph.fromRel (fun a b => (a, b) ∈ E)).edgeSet.ncard ≤ (F : Set (Sym2 V)).ncard :=
      Set.ncard_le_ncard hsub F.finite_toSet
    _ = F.card := by simp
    _ ≤ E.card := Finset.card_image_le

lemma induced_edge_count_le {V : Type*} [Finite V] (G : SimpleGraph V) (U : Set V) :
    (G.induce U).edgeSet.ncard ≤ G.edgeSet.ncard := by
  apply Set.ncard_le_ncard_of_injOn (Sym2.map (fun v : U => v.val))
  · intro e he
    rw [G.edgeSet_induce] at he
    exact he
  · exact (Sym2.map.injective Subtype.val_injective).injOn

lemma reachable_induce_of_closed {V : Type*} (G : SimpleGraph V) (U : Set V)
    (hclosed : ∀ a b, G.Adj a b → a ∈ U → b ∈ U)
    {a b : V} (ha : a ∈ U) (hb : b ∈ U) (h : G.Reachable a b) :
    (G.induce U).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  have hpath : ∀ {u v : V} (p : G.Walk u v), u ∈ U → ∀ w ∈ p.support, w ∈ U := by
    intro u v p
    induction p with
    | nil =>
      intro hu w hw
      simpa using (show w ∈ U from (List.mem_singleton.mp hw) ▸ hu)
    | @cons u v w huv p ih =>
      intro hu z hz
      rcases List.mem_cons.mp hz with hzu | hzp
      · exact hzu ▸ hu
      · exact ih (hclosed u v huv hu) z hzp
  obtain ⟨p⟩ := h
  exact ⟨p.induce U (hpath p ha)⟩

lemma pair_graph_reachable_induce {V : Type*} [DecidableEq V]
    (U : Finset V) (E : Finset (V × V)) (hE : E ⊆ U ×ˢ U)
    {a b : V} (ha : a ∈ U) (hb : b ∈ U)
    (h : (SimpleGraph.fromRel (fun a b => (a, b) ∈ E)).Reachable a b) :
    ((SimpleGraph.fromRel (fun a b => (a, b) ∈ E)).induce (U : Set V)).Reachable
      ⟨a, ha⟩ ⟨b, hb⟩ := by
  apply reachable_induce_of_closed _ (U : Set V) ?_ ha hb h
  intro x y hxy hx
  rcases hxy.2 with hxy | hyx
  · exact (Finset.mem_product.mp (hE hxy)).2
  · exact (Finset.mem_product.mp (hE hyx)).1

lemma pair_graph_card_bound {V : Type*} [DecidableEq V] [Finite V]
    (U : Finset V) (E : Finset (V × V)) (hE : E ⊆ U ×ˢ U)
    (H : SimpleGraph (U : Set V))
    (hH : ∀ a b : (U : Set V), H.Reachable a b →
      (SimpleGraph.fromRel (fun a b => (a, b) ∈ E)).Reachable a.val b.val) :
    U.card ≤ E.card + Nat.card H.ConnectedComponent := by
  let G := SimpleGraph.fromRel (fun a b => (a, b) ∈ E)
  have hreach : ∀ a b : (U : Set V), H.Reachable a b →
      (G.induce (U : Set V)).Reachable a b := by
    intro a b hab
    exact pair_graph_reachable_induce U E hE a.prop b.prop (hH a b hab)
  have hcore := graph_card_le_edges_add_larger_components (G.induce (U : Set V)) H hreach
  have hedges : (G.induce (U : Set V)).edgeSet.ncard ≤ E.card :=
    (induced_edge_count_le G _).trans (graph_from_pairs_edge_count E)
  have hfinal := hcore.trans (Nat.add_le_add_right hedges _)
  simpa using hfinal

lemma reachable_of_adj_reachable {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W)
    (f : V → W) (h : ∀ a b, H.Adj a b → G.Reachable (f a) (f b)) :
    ∀ a b, H.Reachable a b → G.Reachable (f a) (f b) := by
  intro a b hab
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w huv p ih => exact (h u v huv).trans ih

lemma pair_graph_card_bound_of_adj {V : Type*} [DecidableEq V] [Finite V]
    (U : Finset V) (E : Finset (V × V)) (hE : E ⊆ U ×ˢ U)
    (H : SimpleGraph (U : Set V))
    (hH : ∀ a b : (U : Set V), H.Adj a b →
      (SimpleGraph.fromRel (fun a b => (a, b) ∈ E)).Reachable a.val b.val) :
    U.card ≤ E.card + Nat.card H.ConnectedComponent := by
  apply pair_graph_card_bound U E hE H
  exact reachable_of_adj_reachable H _ Subtype.val hH

end PEqualNP.Outside.L_meta_4970

namespace PEqualNP.Outside.L_meta_4970_aux.Structural

def IsIncreasing {α : Type*} (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

lemma below_or_of_complement {α : Type*} [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool)
    (hf : IsIncreasing f)
    (hzero : f (fun i => decide (i ∉ Q)) ≠ true) :
    ∀ x, f x = true → ∃ i ∈ Q, x i = true := by
  intro x hx
  by_contra hn
  apply hzero
  apply hf x (fun i => decide (i ∉ Q)) _ hx
  intro i hi
  simp only [decide_eq_true_eq]
  intro hiQ
  exact hn ⟨i, hiQ, hi⟩

lemma and_below_or_child {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : IsIncreasing f) (hg : IsIncreasing g)
    (hbound : ∀ x, (f x && g x) = true → ∃ i ∈ Q, x i = true) :
    (∀ x, f x = true → ∃ i ∈ Q, x i = true) ∨
      (∀ x, g x = true → ∃ i ∈ Q, x i = true) := by
  let z : α → Bool := fun i => decide (i ∉ Q)
  have hz : ¬ (f z = true ∧ g z = true) := by
    intro h
    obtain ⟨i, hiQ, hiz⟩ := hbound z (by simp [h.1, h.2])
    simp [z, hiQ] at hiz
  by_cases h : f z = true
  · exact Or.inr (below_or_of_complement Q g hg (fun h' => hz ⟨h, h'⟩))
  · exact Or.inl (below_or_of_complement Q f hf h)

lemma and_eq_or_child {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : IsIncreasing f) (hg : IsIncreasing g)
    (heq : ∀ x, (f x && g x) = decide (∃ i ∈ Q, x i = true)) :
    (∀ x, f x = decide (∃ i ∈ Q, x i = true)) ∨
      (∀ x, g x = decide (∃ i ∈ Q, x i = true)) := by
  have hb : ∀ x, (f x && g x) = true → ∃ i ∈ Q, x i = true := by
    intro x hx
    rw [heq x] at hx
    exact of_decide_eq_true hx
  rcases and_below_or_child Q f g hf hg hb with h | h
  · left
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · exact h x
    · intro hx
      have hx' : (f x && g x) = true := by
        rw [heq x]
        exact decide_eq_true hx
      rw [Bool.and_eq_true] at hx'
      exact hx'.1
  · right
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · exact h x
    · intro hx
      have hx' : (f x && g x) = true := by
        rw [heq x]
        exact decide_eq_true hx
      rw [Bool.and_eq_true] at hx'
      exact hx'.2

lemma countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

lemma pure_or_rt_count {α : Type*} [DecidableEq α] [Fintype α]
    (k N : ℕ) (Q : Finset α)
    (W : ℕ → (α → Bool) → Bool) (S : ℕ → Finset α)
    (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (hmono : ∀ w < N, IsIncreasing (W w))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hsupport : ∀ w < N, ∀ i,
      i ∈ S w ↔ W w (fun j => decide (j = i)) = true)
    (heval : ∀ w, k ≤ w → w < N → ∀ x,
      W w x = if isAnd w then (W (a w) x && W (b w) x)
        else (W (a w) x || W (b w) x))
    (R : Finset ℕ)
    (hR : ∀ w ∈ R, w < N ∧ (∀ x, W w x = true → ∃ i ∈ Q, x i = true)) :
    (R.biUnion S).card ≤ R.card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ isAnd w = false ∧
        1 < (S w).card ∧ ∀ x, W w x = true → ∃ i ∈ Q, x i = true)).card := by
  classical
  let below (w : ℕ) := ∀ x, W w x = true → ∃ i ∈ Q, x i = true
  let F (w : ℕ) := if w < N ∧ below w then S w else ∅
  let paid := (Finset.range N).filter fun w =>
    k ≤ w ∧ isAnd w = false ∧ 1 < (S w).card ∧ below w
  have hstep : ∀ w < N, 1 < (F w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ F w ⊆ cs.biUnion F ∧
        cs.card ≤ 1 + (if w ∈ paid then 1 else 0) := by
    intro w hw hlarge
    have hgood : w < N ∧ below w := by
      by_contra hn
      simp [F, hn] at hlarge
    have hF : F w = S w := ite_eq_left hgood
    have hk : k ≤ w := by
      by_contra hn
      have ht := hsmall w (by omega)
      rw [hF] at hlarge
      omega
    have ⟨ha, hb⟩ := hparents w hk hw
    cases hop : isAnd w with
    | true =>
      have hbound : ∀ x, (W (a w) x && W (b w) x) = true → ∃ i ∈ Q, x i = true := by
        intro x hx
        apply hgood.2 x
        simpa [heval w hk hw x, hop] using hx
      have hchoice := and_below_or_child Q (W (a w)) (W (b w))
        (hmono _ (ha.trans hw)) (hmono _ (hb.trans hw)) hbound
      have hsubA : S w ⊆ S (a w) := by
        intro i hi
        apply (hsupport _ (ha.trans hw) i).mpr
        have ht := (hsupport w hw i).mp hi
        rw [heval w hk hw, hop] at ht
        simp only [ite_true, Bool.and_eq_true] at ht
        exact ht.1
      have hsubB : S w ⊆ S (b w) := by
        intro i hi
        apply (hsupport _ (hb.trans hw) i).mpr
        have ht := (hsupport w hw i).mp hi
        rw [heval w hk hw, hop] at ht
        simp only [ite_true, Bool.and_eq_true] at ht
        exact ht.2
      rcases hchoice with hA | hB
      · have hFA : F (a w) = S (a w) := ite_eq_left ⟨ha.trans hw, hA⟩
        refine ⟨{a w}, by simpa using ha, ?_, by simp⟩
        simpa [hF, hFA] using hsubA
      · have hFB : F (b w) = S (b w) := ite_eq_left ⟨hb.trans hw, hB⟩
        refine ⟨{b w}, by simpa using hb, ?_, by simp⟩
        simpa [hF, hFB] using hsubB
    | false =>
      have hA : below (a w) := by
        intro x hx
        apply hgood.2 x
        simp [heval w hk hw x, hop, hx]
      have hB : below (b w) := by
        intro x hx
        apply hgood.2 x
        simp [heval w hk hw x, hop, hx]
      have hFA : F (a w) = S (a w) := ite_eq_left ⟨ha.trans hw, hA⟩
      have hFB : F (b w) = S (b w) := ite_eq_left ⟨hb.trans hw, hB⟩
      have hsub : S w ⊆ S (a w) ∪ S (b w) := by
        intro i hi
        have ht := (hsupport w hw i).mp hi
        rw [heval w hk hw, hop] at ht
        simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true] at ht
        rcases ht with ht | ht
        · exact Finset.mem_union_left _ ((hsupport _ (ha.trans hw) i).mpr ht)
        · exact Finset.mem_union_right _ ((hsupport _ (hb.trans hw) i).mpr ht)
      have hp : w ∈ paid := by
        simp only [paid, Finset.mem_filter, Finset.mem_range]
        exact ⟨hw, hk, hop, hF ▸ hlarge, hgood.2⟩
      refine ⟨{a w, b w}, ?_, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hv]
          exact Finset.mem_range.mpr hb
      · simpa [hF, hFA, hFB] using hsub
      · simp only [hp, ite_true]
        exact Finset.card_le_two
  have hRrange : R ⊆ Finset.range N := by
    intro w hw
    exact Finset.mem_range.mpr (hR w hw).1
  have hroots : R.biUnion F = R.biUnion S := by
    apply Finset.biUnion_congr rfl
    intro w hw
    exact ite_eq_left (hR w hw)
  have hpaid : Finset.range N ∩ paid = paid := by
    exact Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
  have hc := countUnion F paid N hstep R hRrange
  simpa only [hroots, hpaid] using hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

def wireValue (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireValue_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n)
    (x : Fin n → Bool) : wireValue n C w x = x ⟨w, hw⟩ := by
  change (wiresFrom C.gates (List.ofFn x)).getD w false = _
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_ofFn]

lemma wireValue_increasing (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (w : ℕ) :
    IsIncreasing (wireValue n C w) := by
  intro x y hxy htrue
  change (wiresFrom C.gates (List.ofFn y)).getD w false = true
  apply wiresFrom_mono C.gates hC.1 (List.ofFn x) (List.ofFn y) (by simp) _ w htrue
  intro i hi
  by_cases hin : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hin), List.getElem_ofFn] at hi ⊢
    exact hxy _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    contradiction

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma gateAt_inputs_two (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen := hC.2.2 (gateAt C j) (gateAt_mem C j hj)
  obtain ⟨a, b, heq⟩ := List.length_eq_two.mp hlen
  simp [opnd, heq]

lemma gateAt_ops (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
  hC.1 _ (gateAt_mem C j hj)

lemma wireValue_parents (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hread := hC.2.1 j hj
  have hi := gateAt_inputs_two n C hC j hj
  constructor
  · exact hread _ (by rw [hi]; simp)
  · exact hread _ (by rw [hi]; simp)

lemma wireValue_gate (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    wireValue n C (n + j) x = (gateAt C j).op.eval
      [wireValue n C (opnd C j 0) x, wireValue n C (opnd C j 1) x] := by
  have h := getD_wiresFrom_gate C.gates (List.ofFn x) j hj
  have hgate : C.gates[j] = gateAt C j := by
    unfold gateAt
    exact (List.getD_eq_getElem _ _ hj).symm
  have hs := gateAt_inputs_two n C hC j hj
  have hp := wireValue_parents n C hC j hj
  simpa only [List.length_ofFn, hgate, hs, List.map_cons, List.map_nil,
    ite_eq_left hp.1, ite_eq_left hp.2, wireValue, Circuit.wires, wiresFrom] using h

lemma wireValue_gate_and (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireValue n C (n + j) x =
      (wireValue n C (opnd C j 0) x && wireValue n C (opnd C j 1) x) := by
  rw [wireValue_gate n C hC j hj, hop]
  simp [GateOp.eval]

lemma wireValue_gate_or (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireValue n C (n + j) x =
      (wireValue n C (opnd C j 0) x || wireValue n C (opnd C j 1) x) := by
  rw [wireValue_gate n C hC j hj, hop]
  simp [GateOp.eval]

def wireSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => wireValue n C w (fun j => decide (j = i)) = true

lemma wireSupport_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ wireSupport n C w ↔ wireValue n C w (fun j => decide (j = i)) = true := by
  simp [wireSupport]

lemma wireSupport_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    wireSupport n C w = {⟨w, hw⟩} := by
  ext i
  simp [wireSupport_mem, wireValue_input n C w hw, eq_comm]

def wireAnd (n : ℕ) (C : Circuit) (w : ℕ) : Bool :=
  match (gateAt C (w - n)).op with
  | GateOp.and => true
  | _ => false

def wireLeft (n : ℕ) (C : Circuit) (w : ℕ) : ℕ := opnd C (w - n) 0

def wireRight (n : ℕ) (C : Circuit) (w : ℕ) : ℕ := opnd C (w - n) 1

lemma wireModel_parents (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    wireLeft n C w < w ∧ wireRight n C w < w := by
  have hj : w - n < C.gates.length := by change w - n < C.size; omega
  have hp := wireValue_parents n C hC (w - n) hj
  simpa only [wireLeft, wireRight, Nat.add_sub_of_le hn] using hp

lemma wireModel_eval (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) (x : Fin n → Bool) :
    wireValue n C w x = if wireAnd n C w then
      (wireValue n C (wireLeft n C w) x && wireValue n C (wireRight n C w) x)
      else (wireValue n C (wireLeft n C w) x || wireValue n C (wireRight n C w) x) := by
  have hj : w - n < C.gates.length := by change w - n < C.size; omega
  rcases gateAt_ops n C hC (w - n) hj with hop | hop
  · have he := wireValue_gate_and n C hC (w - n) hj hop x
    simpa only [wireAnd, hop, ite_true, wireLeft, wireRight, Nat.add_sub_of_le hn] using he
  · have he := wireValue_gate_or n C hC (w - n) hj hop x
    simpa only [wireAnd, hop, Bool.false_eq_true, ite_false, wireLeft, wireRight,
      Nat.add_sub_of_le hn] using he

def pureOrPaid (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + C.size)).filter fun w =>
    n ≤ w ∧ wireAnd n C w = false ∧ 1 < (wireSupport n C w).card ∧
      ∀ x, wireValue n C w x = true → ∃ i ∈ Q, x i = true

lemma circuit_pure_or_count (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (R : Finset ℕ)
    (hR : ∀ w ∈ R, w < n + C.size ∧
      ∀ x, wireValue n C w x = true → ∃ i ∈ Q, x i = true) :
    (R.biUnion (wireSupport n C)).card ≤ R.card + (pureOrPaid n C Q).card := by
  have hs : ∀ w < n, (wireSupport n C w).card ≤ 1 := by
    intro w hw
    simp [wireSupport_input n C w hw]
  have hc := pure_or_rt_count n (n + C.size) Q (wireValue n C) (wireSupport n C)
    (wireLeft n C) (wireRight n C) (wireAnd n C)
    (fun w _ => wireValue_increasing n C hC w) hs
    (fun w hn hw => wireModel_parents n C hC w hn hw)
    (fun w _ i => wireSupport_mem n C w i)
    (fun w hn hw x => wireModel_eval n C hC w hn hw x) R hR
  convert hc using 2
  congr 1
  ext w
  simp only [pureOrPaid, Finset.mem_filter, Finset.mem_range]

lemma wireSupport_below (n : ℕ) (C : Circuit) (w : ℕ) (Q : Finset (Fin n))
    (hbelow : ∀ x, wireValue n C w x = true → ∃ i ∈ Q, x i = true) :
    wireSupport n C w ⊆ Q := by
  intro i hi
  obtain ⟨j, hj, hji⟩ := hbelow (fun k => decide (k = i)) ((wireSupport_mem n C w i).mp hi)
  have heq : j = i := of_decide_eq_true hji
  exact heq ▸ hj

lemma wireValue_of_support (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (w : ℕ) (i : Fin n) (hi : i ∈ wireSupport n C w)
    (x : Fin n → Bool) (hxi : x i = true) : wireValue n C w x = true := by
  apply wireValue_increasing n C hC w (fun j => decide (j = i)) x
  · intro j hj
    have heq : j = i := of_decide_eq_true hj
    exact heq ▸ hxi
  · exact (wireSupport_mem n C w i).mp hi

lemma pureOrPaid_true (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (x : Fin n → Bool) (hx : ∀ i ∈ Q, x i = true)
    (w : ℕ) (hw : w ∈ pureOrPaid n C Q) : wireValue n C w x = true := by
  have hp := (Finset.mem_filter.mp hw).2
  have hne : (wireSupport n C w).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hne
  apply wireValue_of_support n C hC w i hi x
  exact hx i (wireSupport_below n C w Q hp.2.2.2 hi)

lemma pureOrPaid_disjoint_false (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (x : Fin n → Bool) (hx : ∀ i ∈ Q, x i = true)
    (A : Finset ℕ) (hA : ∀ w ∈ A, wireValue n C w x = false) :
    Disjoint (pureOrPaid n C Q) A := by
  apply Finset.disjoint_left.mpr
  intro w hw hwA
  have ht := pureOrPaid_true n C hC Q x hx w hw
  rw [hA w hwA] at ht
  contradiction

lemma pureOrPaid_sub_gates (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) :
    pureOrPaid n C Q ⊆ Finset.Ico n (n + C.size) := by
  intro w hw
  have hp := Finset.mem_filter.mp hw
  exact Finset.mem_Ico.mpr ⟨hp.2.1, Finset.mem_range.mp hp.1⟩

lemma pureOrPaid_card_le_size (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) :
    (pureOrPaid n C Q).card ≤ C.size := by
  have h := Finset.card_le_card (pureOrPaid_sub_gates n C Q)
  simpa using h

def edgeGraph {α : Type*} (E : Finset (α × α)) : SimpleGraph α :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ E

lemma edgeGraph_mono {α : Type*} {E F : Finset (α × α)} (h : E ⊆ F) :
    edgeGraph E ≤ edgeGraph F := by
  intro a b hab
  exact ⟨hab.1, hab.2.imp (fun h' => h h') (fun h' => h h')⟩

lemma edgeGraph_link {α : Type*} [DecidableEq α] (E : Finset (α × α))
    (a b : α) : (edgeGraph (insert (a,b) E)).Reachable a b := by
  by_cases h : a = b
  · subst b
    exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    exact ⟨h, Or.inl (Finset.mem_insert_self _ _)⟩

lemma edgeGraph_union_connected {α : Type*} [DecidableEq α]
    (E : Finset (α × α)) (A B : Finset α)
    (hA : ∀ x ∈ A, ∀ y ∈ A, (edgeGraph E).Reachable x y)
    (hB : ∀ x ∈ B, ∀ y ∈ B, (edgeGraph E).Reachable x y)
    (a : α) (ha : a ∈ A) (b : α) (hb : b ∈ B) :
    ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B,
      (edgeGraph (insert (a,b) E)).Reachable x y := by
  have hmono := edgeGraph_mono (Finset.subset_insert (a,b) E)
  have hleg : ∀ x ∈ A ∪ B, (edgeGraph (insert (a,b) E)).Reachable x a := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (hA x hx a ha).mono hmono
    · exact ((hB x hx b hb).mono hmono).trans (edgeGraph_link E a b).symm
  intro x hx y hy
  exact (hleg x hx).trans (hleg y hy).symm

lemma support_connected_edges {α : Type*} [DecidableEq α]
    (U : Finset α) (S : ℕ → Finset α) (paid : Finset ℕ) (N : ℕ)
    (hU : ∀ w < N, S w ⊆ U)
    (step : ∀ w < N, 1 < (S w).card →
      (∃ a < w, S w ⊆ S a) ∨
        (w ∈ paid ∧ ∃ a < w, ∃ b < w, S w ⊆ S a ∪ S b)) :
    ∃ E : Finset (α × α), E ⊆ U ×ˢ U ∧ E.card ≤ (Finset.range N ∩ paid).card ∧
      ∀ w < N, ∀ x ∈ S w, ∀ y ∈ S w, (edgeGraph E).Reachable x y := by
  classical
  induction N with
  | zero =>
    refine ⟨∅, by simp, by simp, ?_⟩
    intro w hw
    omega
  | succ N ih =>
    obtain ⟨E, hEU, hcard, hconn⟩ := ih (fun w hw => hU w (by omega))
      (fun w hw => step w (by omega))
    have hcard' : E.card ≤ (Finset.range (N + 1) ∩ paid).card := by
      apply hcard.trans
      apply Finset.card_le_card
      intro w hw
      have hm := Finset.mem_inter.mp hw
      exact Finset.mem_inter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hm.1; omega), hm.2⟩
    have extend (F : Finset (α × α)) (hEF : E ⊆ F)
        (hnew : ∀ x ∈ S N, ∀ y ∈ S N, (edgeGraph F).Reachable x y) :
        ∀ w < N + 1, ∀ x ∈ S w, ∀ y ∈ S w, (edgeGraph F).Reachable x y := by
      intro w hw x hx y hy
      by_cases h : w < N
      · exact (hconn w h x hx y hy).mono (edgeGraph_mono hEF)
      · have he : w = N := by omega
        subst w
        exact hnew x hx y hy
    by_cases hlarge : 1 < (S N).card
    · rcases step N (by omega) hlarge with ⟨a, ha, hsub⟩ | ⟨hp, a, ha, b, hb, hsub⟩
      · refine ⟨E, hEU, hcard', extend E (fun _ h => h) ?_⟩
        exact fun x hx y hy => hconn a ha x (hsub hx) y (hsub hy)
      · by_cases hA : (S a).Nonempty
        · by_cases hB : (S b).Nonempty
          · obtain ⟨u, hu⟩ := hA
            obtain ⟨v, hv⟩ := hB
            have hpaid : (Finset.range (N + 1) ∩ paid).card =
                (Finset.range N ∩ paid).card + 1 := by
              have heq : Finset.range (N + 1) ∩ paid = insert N (Finset.range N ∩ paid) := by
                ext j
                by_cases hj : j = N <;> simp [Finset.range_add_one, hj, hp]
              rw [heq]
              simp
            refine ⟨insert (u,v) E, ?_, ?_, extend _ (Finset.subset_insert _ _) ?_⟩
            · intro z hz
              rcases Finset.mem_insert.mp hz with rfl | hz
              · exact Finset.mem_product.mpr ⟨hU a (by omega) hu, hU b (by omega) hv⟩
              · exact hEU hz
            · have hi := Finset.card_insert_le (u,v) E
              omega
            · intro x hx y hy
              exact edgeGraph_union_connected E (S a) (S b) (hconn a ha) (hconn b hb)
                u hu v hv x (hsub hx) y (hsub hy)
          · have hB' : S b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
            have hs : S N ⊆ S a := by simpa [hB'] using hsub
            exact ⟨E, hEU, hcard', extend E (fun _ h => h)
              (fun x hx y hy => hconn a ha x (hs hx) y (hs hy))⟩
        · have hA' : S a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
          have hs : S N ⊆ S b := by simpa [hA'] using hsub
          exact ⟨E, hEU, hcard', extend E (fun _ h => h)
            (fun x hx y hy => hconn b hb x (hs hx) y (hs hy))⟩
    · have hsmall : (S N).card ≤ 1 := by omega
      refine ⟨E, hEU, hcard', extend E (fun _ h => h) ?_⟩
      intro x hx y hy
      have heq : x = y := Finset.card_le_one.mp hsmall x hx y hy
      subst y
      exact SimpleGraph.Reachable.refl _

lemma circuit_pure_or_graph (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) :
    ∃ E : Finset (Fin n × Fin n), E ⊆ Q ×ˢ Q ∧ E.card ≤ (pureOrPaid n C Q).card ∧
      ∀ w < n + C.size, (∀ x, wireValue n C w x = true → ∃ i ∈ Q, x i = true) →
        ∀ u ∈ wireSupport n C w, ∀ v ∈ wireSupport n C w, (edgeGraph E).Reachable u v := by
  classical
  let below (w : ℕ) := ∀ x, wireValue n C w x = true → ∃ i ∈ Q, x i = true
  let F (w : ℕ) := if w < n + C.size ∧ below w then wireSupport n C w else ∅
  have hFsub : ∀ w < n + C.size, F w ⊆ Q := by
    intro w hw
    by_cases hg : w < n + C.size ∧ below w
    · simpa only [F, ite_eq_left hg] using wireSupport_below n C w Q hg.2
    · simp [F, hg]
  have step : ∀ w < n + C.size, 1 < (F w).card →
      (∃ a < w, F w ⊆ F a) ∨
        (w ∈ pureOrPaid n C Q ∧ ∃ a < w, ∃ b < w, F w ⊆ F a ∪ F b) := by
    intro w hw hlarge
    have hg : w < n + C.size ∧ below w := by
      by_contra hn
      simp [F, hn] at hlarge
    have hF : F w = wireSupport n C w := ite_eq_left hg
    have hn : n ≤ w := by
      by_contra! hn
      rw [hF, wireSupport_input n C w hn] at hlarge
      simp at hlarge
    have hp := wireModel_parents n C hC w hn hw
    cases hop : wireAnd n C w with
    | true =>
      have hbound : ∀ x,
          (wireValue n C (wireLeft n C w) x && wireValue n C (wireRight n C w) x) = true →
            ∃ i ∈ Q, x i = true := by
        intro x hx
        apply hg.2 x
        rw [wireModel_eval n C hC w hn hw, hop]
        exact hx
      have hchoice := and_below_or_child Q
        (wireValue n C (wireLeft n C w)) (wireValue n C (wireRight n C w))
        (wireValue_increasing n C hC _) (wireValue_increasing n C hC _) hbound
      have hsub : wireSupport n C w ⊆ wireSupport n C (wireLeft n C w) ∩
          wireSupport n C (wireRight n C w) := by
        intro i hi
        have ht := (wireSupport_mem n C w i).mp hi
        rw [wireModel_eval n C hC w hn hw, hop] at ht
        simp only [ite_true, Bool.and_eq_true] at ht
        exact Finset.mem_inter.mpr ⟨(wireSupport_mem n C _ i).mpr ht.1,
          (wireSupport_mem n C _ i).mpr ht.2⟩
      left
      rcases hchoice with hA | hB
      · refine ⟨wireLeft n C w, hp.1, ?_⟩
        have hFA : F (wireLeft n C w) = wireSupport n C (wireLeft n C w) :=
          ite_eq_left ⟨hp.1.trans hw, hA⟩
        rw [hF, hFA]
        exact hsub.trans Finset.inter_subset_left
      · refine ⟨wireRight n C w, hp.2, ?_⟩
        have hFB : F (wireRight n C w) = wireSupport n C (wireRight n C w) :=
          ite_eq_left ⟨hp.2.trans hw, hB⟩
        rw [hF, hFB]
        exact hsub.trans Finset.inter_subset_right
    | false =>
      have hA : below (wireLeft n C w) := by
        intro x hx
        apply hg.2 x
        simp [wireModel_eval n C hC w hn hw, hop, hx]
      have hB : below (wireRight n C w) := by
        intro x hx
        apply hg.2 x
        simp [wireModel_eval n C hC w hn hw, hop, hx]
      have hFA : F (wireLeft n C w) = wireSupport n C (wireLeft n C w) :=
        ite_eq_left ⟨hp.1.trans hw, hA⟩
      have hFB : F (wireRight n C w) = wireSupport n C (wireRight n C w) :=
        ite_eq_left ⟨hp.2.trans hw, hB⟩
      right
      refine ⟨?_, wireLeft n C w, hp.1, wireRight n C w, hp.2, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw, hn, hop, hF ▸ hlarge, hg.2⟩
      · rw [hF, hFA, hFB]
        intro i hi
        have ht := (wireSupport_mem n C w i).mp hi
        rw [wireModel_eval n C hC w hn hw, hop] at ht
        simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true] at ht
        rcases ht with ht | ht
        · exact Finset.mem_union_left _ ((wireSupport_mem n C _ i).mpr ht)
        · exact Finset.mem_union_right _ ((wireSupport_mem n C _ i).mpr ht)
  obtain ⟨E, hEQ, hcard, hconn⟩ := support_connected_edges Q F (pureOrPaid n C Q)
    (n + C.size) hFsub step
  have hcard' : E.card ≤ (pureOrPaid n C Q).card := by
    exact hcard.trans (Finset.card_le_card Finset.inter_subset_right)
  refine ⟨E, hEQ, hcard', ?_⟩
  intro w hw hbelow u hu v hv
  have heq : F w = wireSupport n C w := ite_eq_left ⟨hw, hbelow⟩
  apply hconn w hw u _ v _
  · simpa only [heq] using hu
  · simpa only [heq] using hv

lemma wireSupport_eq_pure (n : ℕ) (C : Circuit) (w : ℕ) (Q : Finset (Fin n))
    (heq : ∀ x, wireValue n C w x = decide (∃ i ∈ Q, x i = true)) :
    wireSupport n C w = Q := by
  ext i
  rw [wireSupport_mem, heq]
  simp

end PEqualNP.Outside.L_meta_4970_aux.Structural

namespace PEqualNP.Outside.L_meta_4970.Pruning

lemma pruning_countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

lemma selected_dag_cover
    {A B V : Type*} [DecidableEq V]
    (left : A → V) (right : B → V) (edges : Finset (A × B))
    (base total root : ℕ) (support : ℕ → Finset V)
    (hit : ℕ → A → B → Prop) (paid : Finset ℕ)
    (hroot : root < total)
    (haccepted : ∀ a b, (a, b) ∈ edges → hit root a b)
    (hbase : ∀ w < base, (support w).card ≤ 1 ∧
      ∀ a b, hit w a b → left a ∈ support w ∨ right b ∈ support w)
    (hstep : ∀ w, base ≤ w → w < total →
      (∃ j < w, support w = support j ∧ ∀ a b, hit w a b → hit j a b) ∨
      (w ∈ paid ∧ ∃ i < w, ∃ j < w, support w = support i ∪ support j ∧
        ∀ a b, hit w a b → hit i a b ∨ hit j a b) ∨
      (support w = ∅ ∧ ∀ a b, ¬ hit w a b)) :
    (∀ a b, (a, b) ∈ edges → left a ∈ support root ∨ right b ∈ support root) ∧
      (support root).card ≤ 1 + (Finset.range total ∩ paid).card := by
  classical
  have covers : ∀ w < total, ∀ a b, hit w a b →
      left a ∈ support w ∨ right b ∈ support w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw a b hab
      by_cases hlow : w < base
      · exact (hbase w hlow).2 a b hab
      · rcases hstep w (Nat.le_of_not_gt hlow) hw with
          ⟨j, hj, he, hh⟩ | ⟨hp, i, hi, j, hj, he, hh⟩ | ⟨he, hh⟩
        · rw [he]
          exact ih j hj (hj.trans hw) a b (hh a b hab)
        · rw [he]
          rcases hh a b hab with ha | hb
          · rcases ih i hi (hi.trans hw) a b ha with ha | hb
            · exact Or.inl (Finset.mem_union_left _ ha)
            · exact Or.inr (Finset.mem_union_left _ hb)
          · rcases ih j hj (hj.trans hw) a b hb with ha | hb
            · exact Or.inl (Finset.mem_union_right _ ha)
            · exact Or.inr (Finset.mem_union_right _ hb)
        · exact False.elim (hh a b hab)
  refine ⟨fun a b hab => covers root hroot a b (haccepted a b hab), ?_⟩
  have hc := pruning_countUnion support paid total ?_ {root} ?_
  · simpa using hc
  · intro w hw hcard
    by_cases hlow : w < base
    · exact False.elim ((Nat.not_lt_of_ge (hbase w hlow).1) hcard)
    · rcases hstep w (Nat.le_of_not_gt hlow) hw with
        ⟨j, hj, he, hh⟩ | ⟨hp, i, hi, j, hj, he, hh⟩ | ⟨he, hh⟩
      · refine ⟨{j}, ?_, ?_, ?_⟩
        · simpa using hj
        · simp [he]
        · simp
      · refine ⟨{i, j}, ?_, ?_, ?_⟩
        · intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk
          · exact Finset.mem_range.mpr hi
          · rw [Finset.mem_singleton.mp hk]
            exact Finset.mem_range.mpr hj
        · simp [he]
        · simp only [hp, ite_true]
          exact Finset.card_le_two
      · simp [he] at hcard
  · simpa using hroot

def selectedSupport (n : ℕ) (a b : ℕ → ℕ) (fork chooseLeft : ℕ → Bool)
    (w : ℕ) : Finset (Fin n) :=
  if hw : w < n then {⟨w, hw⟩}
  else if h : a w < w ∧ b w < w then
    if fork w = true then selectedSupport n a b fork chooseLeft (a w) ∪
      selectedSupport n a b fork chooseLeft (b w)
    else if chooseLeft w = true then selectedSupport n a b fork chooseLeft (a w)
      else selectedSupport n a b fork chooseLeft (b w)
  else ∅
termination_by w
decreasing_by all_goals first | exact h.1 | exact h.2

def selectedStep (n total : ℕ) (a b : ℕ → ℕ) (fork chooseLeft : ℕ → Bool)
    (w v : ℕ) : Prop :=
  n ≤ w ∧ w < total ∧
    if fork w = true then v = a w ∨ v = b w
    else if chooseLeft w = true then v = a w else v = b w

def follows (step : ℕ → ℕ → Prop) (root w : ℕ) : Prop :=
  ∀ S : Set ℕ, root ∈ S → (∀ u ∈ S, ∀ v, step u v → v ∈ S) → w ∈ S

lemma follows_refl (step : ℕ → ℕ → Prop) (root : ℕ) : follows step root root := by
  intro S hS _
  exact hS

lemma follows_step (step : ℕ → ℕ → Prop) (root w v : ℕ)
    (hw : follows step root w) (hv : step w v) : follows step root v := by
  intro S hS hclosed
  exact hclosed w (hw S hS hclosed) v hv

noncomputable def selectedActive (n total : ℕ) (a b : ℕ → ℕ)
    (fork chooseLeft : ℕ → Bool) (root : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range total).filter (follows (selectedStep n total a b fork chooseLeft) root)

noncomputable def selectedUnions (n total : ℕ) (a b : ℕ → ℕ)
    (fork chooseLeft : ℕ → Bool) (root : ℕ) : Finset ℕ := by
  classical
  exact (selectedActive n total a b fork chooseLeft root).filter
    (fun w => n ≤ w ∧ fork w = true)

lemma selectedSupport_input (n : ℕ) (a b : ℕ → ℕ) (fork chooseLeft : ℕ → Bool)
    (w : ℕ) (hw : w < n) : selectedSupport n a b fork chooseLeft w = {⟨w, hw⟩} := by
  rw [selectedSupport, dite_eq_left hw]

lemma selectedSupport_gate (n : ℕ) (a b : ℕ → ℕ) (fork chooseLeft : ℕ → Bool)
    (w : ℕ) (hw : n ≤ w) (hp : a w < w ∧ b w < w) :
    selectedSupport n a b fork chooseLeft w =
      if fork w = true then selectedSupport n a b fork chooseLeft (a w) ∪
        selectedSupport n a b fork chooseLeft (b w)
      else if chooseLeft w = true then selectedSupport n a b fork chooseLeft (a w)
        else selectedSupport n a b fork chooseLeft (b w) := by
  rw [selectedSupport, dite_eq_right (Nat.not_lt.mpr hw), dite_eq_left hp]

lemma selected_cover
    {A B : Type*} (n total root : ℕ) (left : A → Fin n) (right : B → Fin n)
    (edges : Finset (A × B)) (a b : ℕ → ℕ) (fork chooseLeft : ℕ → Bool)
    (hit : ℕ → A → B → Prop)
    (hroot : root < total)
    (hparents : ∀ w, n ≤ w → w < total → a w < w ∧ b w < w)
    (hinput : ∀ w (hw : w < n), ∀ u v, hit w u v → left u = ⟨w, hw⟩ ∨ right v = ⟨w, hw⟩)
    (hfork : ∀ w, n ≤ w → w < total → fork w = true →
      ∀ u v, hit w u v → hit (a w) u v ∨ hit (b w) u v)
    (hchoose : ∀ w, n ≤ w → w < total → fork w ≠ true →
      ∀ u v, hit w u v → hit (a w) u v ∧ hit (b w) u v)
    (haccepted : ∀ u v, (u, v) ∈ edges → hit root u v) :
    (∀ u v, (u, v) ∈ edges →
      left u ∈ selectedSupport n a b fork chooseLeft root ∨
      right v ∈ selectedSupport n a b fork chooseLeft root) ∧
    (selectedSupport n a b fork chooseLeft root).card ≤
      1 + (selectedUnions n total a b fork chooseLeft root).card := by
  classical
  let active := selectedActive n total a b fork chooseLeft root
  let paid := selectedUnions n total a b fork chooseLeft root
  let supp := selectedSupport n a b fork chooseLeft
  let support : ℕ → Finset (Fin n) := fun w => if w ∈ active then supp w else ∅
  let hits : ℕ → A → B → Prop := fun w u v => w ∈ active ∧ hit w u v
  have root_mem : root ∈ active := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hroot, follows_refl _ _⟩
  have mem_next (w v : ℕ) (hw : w ∈ active)
      (hv : selectedStep n total a b fork chooseLeft w v) (hvw : v < w) : v ∈ active := by
    have hs := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hvw.trans (Finset.mem_range.mp hs.1)),
      follows_step _ root w v hs.2 hv⟩
  have hpaid : Finset.range total ∩ paid = paid := by
    apply Finset.inter_eq_right.mpr
    intro w hw
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  have result := selected_dag_cover left right edges n total root support hits paid hroot
    (fun u v huv => ⟨root_mem, haccepted u v huv⟩) ?_ ?_
  · simpa only [support, root_mem, ite_eq_left, hpaid] using result
  · intro w hw
    constructor
    · dsimp only [support, supp]
      split_ifs
      · rw [selectedSupport_input n a b fork chooseLeft w hw]
        simp
      · simp
    · intro u v ⟨hactive, hhit⟩
      dsimp only [support]
      rw [ite_eq_left hactive]
      change left u ∈ selectedSupport n a b fork chooseLeft w ∨
        right v ∈ selectedSupport n a b fork chooseLeft w
      rw [selectedSupport_input n a b fork chooseLeft w hw]
      simpa using hinput w hw u v hhit
  · intro w hn hw
    by_cases hactive : w ∈ active
    · have hp := hparents w hn hw
      have hs : supp w = if fork w = true then supp (a w) ∪ supp (b w)
          else if chooseLeft w = true then supp (a w) else supp (b w) :=
        selectedSupport_gate n a b fork chooseLeft w hn hp
      by_cases hor : fork w = true
      · have ha : a w ∈ active := mem_next w (a w) hactive
          ⟨hn, hw, by simp only [hor, ite_eq_left, true_or]⟩ hp.1
        have hb : b w ∈ active := mem_next w (b w) hactive
          ⟨hn, hw, by simp only [hor, ite_eq_left, or_true]⟩ hp.2
        right
        left
        refine ⟨Finset.mem_filter.mpr ⟨hactive, hn, hor⟩, a w, hp.1, b w, hp.2, ?_, ?_⟩
        · simp only [support, hactive, ha, hb, ite_eq_left, hor] at hs ⊢
          exact hs
        · intro u v ⟨_, hv⟩
          rcases hfork w hn hw hor u v hv with h | h
          · exact Or.inl ⟨ha, h⟩
          · exact Or.inr ⟨hb, h⟩
      · left
        by_cases hl : chooseLeft w = true
        · have ha : a w ∈ active := mem_next w (a w) hactive
            ⟨hn, hw, by simp [hor, hl]⟩ hp.1
          refine ⟨a w, hp.1, ?_, ?_⟩
          · simp only [support, hactive, ha, ite_eq_left, hor, ite_eq_right, hl] at hs ⊢
            exact hs
          · intro u v ⟨_, hv⟩
            exact ⟨ha, (hchoose w hn hw hor u v hv).1⟩
        · have hb : b w ∈ active := mem_next w (b w) hactive
            ⟨hn, hw, by simp [hor, hl]⟩ hp.2
          refine ⟨b w, hp.2, ?_, ?_⟩
          · simp only [support, hactive, hb, ite_eq_left, hor, ite_eq_right, hl] at hs ⊢
            exact hs
          · intro u v ⟨_, hv⟩
            exact ⟨hb, (hchoose w hn hw hor u v hv).2⟩
    · right
      right
      refine ⟨by simp [support, hactive], ?_⟩
      intro u v hv
      exact hactive hv.1



lemma selectedSupport_zero (n total : ℕ) (a b : ℕ → ℕ)
    (fork chooseLeft : ℕ → Bool) (value : ℕ → Bool)
    (hparents : ∀ w, n ≤ w → w < total → a w < w ∧ b w < w)
    (hfork : ∀ w, n ≤ w → w < total → fork w = true → value w = false →
      value (a w) = false ∧ value (b w) = false)
    (hchoose : ∀ w, n ≤ w → w < total → fork w ≠ true → value w = false →
      (if chooseLeft w = true then value (a w) else value (b w)) = false) :
    ∀ w, w < total → value w = false →
      ∀ i ∈ selectedSupport n a b fork chooseLeft w, value i.val = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hv i hi
    by_cases hin : w < n
    · rw [selectedSupport_input n a b fork chooseLeft w hin] at hi
      have hi1 : i = ⟨w, hin⟩ := by simpa using hi
      subst i
      exact hv
    · have hn : n ≤ w := Nat.le_of_not_lt hin
      have hp := hparents w hn hw
      rw [selectedSupport_gate n a b fork chooseLeft w hn hp] at hi
      by_cases hor : fork w = true
      · simp only [hor, ite_eq_left, Finset.mem_union] at hi
        rcases hi with hi | hi
        · exact ih _ hp.1 (hp.1.trans hw) (hfork w hn hw hor hv).1 i hi
        · exact ih _ hp.2 (hp.2.trans hw) (hfork w hn hw hor hv).2 i hi
      · have hc := hchoose w hn hw hor hv
        by_cases hl : chooseLeft w = true
        · simp [hor, hl] at hi hc
          exact ih _ hp.1 (hp.1.trans hw) hc i hi
        · simp [hor, hl] at hi hc
          exact ih _ hp.2 (hp.2.trans hw) hc i hi

lemma selectedActive_zero (n total root : ℕ) (a b : ℕ → ℕ)
    (fork chooseLeft : ℕ → Bool) (value : ℕ → Bool)
    (hzero : value root = false)
    (hfork : ∀ w, n ≤ w → w < total → fork w = true → value w = false →
      value (a w) = false ∧ value (b w) = false)
    (hchoose : ∀ w, n ≤ w → w < total → fork w ≠ true → value w = false →
      (if chooseLeft w = true then value (a w) else value (b w)) = false) :
    ∀ w ∈ selectedActive n total a b fork chooseLeft root, value w = false := by
  classical
  intro w hw
  have hr := (Finset.mem_filter.mp hw).2
  apply hr {v | value v = false} hzero
  intro u hu v ⟨hn, ht, hv⟩
  change value v = false
  by_cases hor : fork u = true
  · simp only [hor, ite_eq_left] at hv
    rcases hv with rfl | rfl
    · exact (hfork u hn ht hor hu).1
    · exact (hfork u hn ht hor hu).2
  · have hc := hchoose u hn ht hor hu
    by_cases hl : chooseLeft u = true
    · simp [hor, hl] at hv hc
      rw [hv]
      exact hc
    · simp [hor, hl] at hv hc
      rw [hv]
      exact hc

end PEqualNP.Outside.L_meta_4970.Pruning

namespace PEqualNP.Outside.L_meta_4970.Pruning
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970_aux.Structural

def circuitFork (n : ℕ) (C : Circuit) (w : ℕ) : Bool := !(wireAnd n C w)

def zeroChoice (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  !(wireValue n C (wireLeft n C w) x)

def pairInput {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun i => decide (i = u ∨ i = v)

lemma circuit_selected_cover {A B : Type*} (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (root : ℕ) (left : A → Fin n) (right : B → Fin n)
    (edges : Finset (A × B)) (chooseLeft : ℕ → Bool)
    (hroot : root < n + C.size)
    (haccepted : ∀ u v, (u, v) ∈ edges →
      wireValue n C root (pairInput (left u) (right v)) = true) :
    (∀ u v, (u, v) ∈ edges →
      left u ∈ selectedSupport n (wireLeft n C) (wireRight n C) (circuitFork n C) chooseLeft root ∨
      right v ∈ selectedSupport n (wireLeft n C) (wireRight n C) (circuitFork n C) chooseLeft root) ∧
    (selectedSupport n (wireLeft n C) (wireRight n C) (circuitFork n C) chooseLeft root).card ≤
      1 + (selectedUnions n (n + C.size) (wireLeft n C) (wireRight n C)
        (circuitFork n C) chooseLeft root).card := by
  apply selected_cover n (n + C.size) root left right edges (wireLeft n C) (wireRight n C)
    (circuitFork n C) chooseLeft
    (fun w u v => wireValue n C w (pairInput (left u) (right v)) = true) hroot
    (wireModel_parents n C hC)
  · intro w hw u v hh
    rw [wireValue_input n C w hw] at hh
    change decide ((⟨w, hw⟩ : Fin n) = left u ∨ (⟨w, hw⟩ : Fin n) = right v) = true at hh
    rcases of_decide_eq_true hh with hh | hh
    · exact Or.inl hh.symm
    · exact Or.inr hh.symm
  · intro w hn hw hor u v hh
    have hnot : wireAnd n C w = false := by simpa [circuitFork] using hor
    rw [wireModel_eval n C hC w hn hw, hnot] at hh
    simpa using hh
  · intro w hn hw hor u v hh
    have hnot : wireAnd n C w = true := by simpa [circuitFork] using hor
    rw [wireModel_eval n C hC w hn hw, hnot] at hh
    simpa using hh
  · exact haccepted

lemma circuit_zero_policy (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (x : Fin n → Bool) (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hz : wireValue n C w x = false) :
    (circuitFork n C w = true →
      wireValue n C (wireLeft n C w) x = false ∧ wireValue n C (wireRight n C w) x = false) ∧
    (circuitFork n C w ≠ true →
      (if zeroChoice n C x w = true then wireValue n C (wireLeft n C w) x
        else wireValue n C (wireRight n C w) x) = false) := by
  rw [wireModel_eval n C hC w hn hw] at hz
  constructor
  · intro hor
    have hnot : wireAnd n C w = false := by simpa [circuitFork] using hor
    simpa [hnot] using hz
  · intro hor
    have hnot : wireAnd n C w = true := by simpa [circuitFork] using hor
    simp only [hnot, ite_eq_left, Bool.and_eq_false_iff] at hz
    by_cases hl : wireValue n C (wireLeft n C w) x = false
    · simp [zeroChoice, hl]
    · have hr := hz.resolve_left hl
      have hl1 : wireValue n C (wireLeft n C w) x = true := Bool.eq_true_of_ne_false hl
      simp [zeroChoice, hl1, hr]

lemma circuit_selected_zero (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (root : ℕ) (x : Fin n → Bool) (hroot : root < n + C.size)
    (hz : wireValue n C root x = false) :
    (∀ i ∈ selectedSupport n (wireLeft n C) (wireRight n C) (circuitFork n C)
      (zeroChoice n C x) root, x i = false) ∧
    (∀ w ∈ selectedActive n (n + C.size) (wireLeft n C) (wireRight n C)
      (circuitFork n C) (zeroChoice n C x) root, wireValue n C w x = false) := by
  have hf := fun w hn hw hor hz => (circuit_zero_policy n C hC x w hn hw hz).1 hor
  have hc := fun w hn hw hor hz => (circuit_zero_policy n C hC x w hn hw hz).2 hor
  constructor
  · intro i hi
    have he := selectedSupport_zero n (n + C.size) (wireLeft n C) (wireRight n C)
      (circuitFork n C) (zeroChoice n C x) (fun w => wireValue n C w x)
      (wireModel_parents n C hC) hf hc root hroot hz i hi
    simpa only [wireValue_input n C i.val i.isLt x] using he
  · exact selectedActive_zero n (n + C.size) root (wireLeft n C) (wireRight n C)
      (circuitFork n C) (zeroChoice n C x) (fun w => wireValue n C w x) hz hf hc

lemma wireValue_true_bound (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool)
    (hw : wireValue n C w x = true) : w < n + C.size := by
  by_contra hn
  have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
    change (wiresFrom C.gates (List.ofFn x)).length = _
    simpa only [List.length_ofFn, Circuit.size] using length_wiresFrom C.gates (List.ofFn x)
  have hfalse : wireValue n C w x = false := by
    unfold PEqualNP.Outside.L_meta_4970_aux.Structural.wireValue
    rw [List.getD_eq_default _ _ (by omega)]
  rw [hfalse] at hw
  contradiction

lemma bipartite_selected_cover (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : IsAO2 (p + l) C) (hE : E.Nonempty)
    (hcomp : ∀ x : Fin (p + l) → Bool,
      PEqualNP.MetaComplexity.circuitFun (p + l) C x =
        decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (choice : ℕ → Bool) :
    (∀ a b, (a, b) ∈ E →
      Fin.castAdd l a ∈ selectedSupport (p + l) (wireLeft (p + l) C) (wireRight (p + l) C)
        (circuitFork (p + l) C) choice C.output ∨
      Fin.natAdd p b ∈ selectedSupport (p + l) (wireLeft (p + l) C) (wireRight (p + l) C)
        (circuitFork (p + l) C) choice C.output) ∧
    (selectedSupport (p + l) (wireLeft (p + l) C) (wireRight (p + l) C)
      (circuitFork (p + l) C) choice C.output).card ≤
      1 + (selectedUnions (p + l) (p + l + C.size) (wireLeft (p + l) C) (wireRight (p + l) C)
        (circuitFork (p + l) C) choice C.output).card := by
  have hacc : ∀ a b, (a, b) ∈ E → wireValue (p + l) C C.output
      (pairInput (Fin.castAdd l a) (Fin.natAdd p b)) = true := by
    intro a b he
    have h := hcomp (pairInput (Fin.castAdd l a) (Fin.natAdd p b))
    change wireValue (p + l) C C.output _ = _ at h
    rw [h]
    apply decide_eq_true
    exact ⟨a, b, he, by simp [pairInput], by simp [pairInput]⟩
  obtain ⟨⟨a, b⟩, hab⟩ := hE
  have hroot := wireValue_true_bound (p + l) C C.output _ (hacc a b hab)
  exact circuit_selected_cover (p + l) C hC C.output (Fin.castAdd l) (Fin.natAdd p)
    E choice hroot hacc

lemma selected_unions_disjoint_true (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (root : ℕ) (x : Fin n → Bool) (hroot : root < n + C.size)
    (hz : wireValue n C root x = false) (P : Finset ℕ)
    (hP : ∀ w ∈ P, wireValue n C w x = true) :
    Disjoint P (selectedUnions n (n + C.size) (wireLeft n C) (wireRight n C)
      (circuitFork n C) (zeroChoice n C x) root) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hw hu
  have hf := (circuit_selected_zero n C hC root x hroot hz).2 w (Finset.mem_filter.mp hu).1
  have ht := hP w hw
  rw [hf] at ht
  contradiction

lemma bipartite_minimum_cover_pruning (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : IsAO2 (p + l) C) (hE : E.Nonempty)
    (hcomp : ∀ x : Fin (p + l) → Bool,
      PEqualNP.MetaComplexity.circuitFun (p + l) C x =
        decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (S : Finset (Fin (p + l)))
    (hcover : ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S)
    (hminimum : ∀ R : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ R ∨ Fin.natAdd p b ∈ R) → S.card ≤ R.card) :
    let x : Fin (p + l) → Bool := fun i => decide (i ∉ S)
    let choice := zeroChoice (p + l) C x
    selectedSupport (p + l) (wireLeft (p + l) C) (wireRight (p + l) C)
      (circuitFork (p + l) C) choice C.output = S ∧
    S.card ≤ 1 + (selectedUnions (p + l) (p + l + C.size) (wireLeft (p + l) C)
      (wireRight (p + l) C) (circuitFork (p + l) C) choice C.output).card := by
  classical
  dsimp only
  let x : Fin (p + l) → Bool := fun i => decide (i ∉ S)
  let choice := zeroChoice (p + l) C x
  let support := selectedSupport (p + l) (wireLeft (p + l) C) (wireRight (p + l) C)
    (circuitFork (p + l) C) choice C.output
  have hz : wireValue (p + l) C C.output x = false := by
    change PEqualNP.MetaComplexity.circuitFun (p + l) C x = false
    rw [hcomp]
    apply decide_eq_false
    rintro ⟨a, b, hab, ha, hb⟩
    have hna : Fin.castAdd l a ∉ S := of_decide_eq_true ha
    have hnb : Fin.natAdd p b ∉ S := of_decide_eq_true hb
    exact (hcover a b hab).elim hna hnb
  obtain ⟨⟨a, b⟩, hab⟩ := hE
  have htrue : wireValue (p + l) C C.output (fun _ => true) = true := by
    change PEqualNP.MetaComplexity.circuitFun (p + l) C (fun _ => true) = true
    rw [hcomp]
    exact decide_eq_true ⟨a, b, hab, rfl, rfl⟩
  have hroot := wireValue_true_bound (p + l) C C.output _ htrue
  have hs := bipartite_selected_cover p l E C hC ⟨(a, b), hab⟩ hcomp choice
  have hsub : support ⊆ S := by
    intro i hi
    have hf := (circuit_selected_zero (p + l) C hC C.output x hroot hz).1 i hi
    simpa [x] using hf
  have heq : support = S := Finset.eq_of_subset_of_card_le hsub (hminimum support hs.1)
  constructor
  · exact heq
  · have hc := hs.2
    change support.card ≤ _ at hc
    rw [heq] at hc
    exact hc

end PEqualNP.Outside.L_meta_4970.Pruning
