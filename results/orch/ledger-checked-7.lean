import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Find
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

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
