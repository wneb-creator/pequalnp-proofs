import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Find
import PEqualNP.Defs
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

end PEqualNP.Outside.L_meta_4970.Pruning

