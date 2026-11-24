import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Outside.L_meta_5324_aux

open scoped BigOperators

lemma rectangle_is_star {n m : ℕ} (E : Finset (Fin n × Fin m))
    (h4 : ∀ a b : Fin n, ∀ c d : Fin m, a ≠ b → c ≠ d →
      ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E))
    (A : Finset (Fin n)) (B : Finset (Fin m))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra h
  simp only [not_or, not_le] at h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp h.2
  exact h4 a b c d hab hcd
    ⟨hAB a ha c hc, hAB a ha d hd, hAB b hb c hc, hAB b hb d hd⟩

lemma shared_two_leaves_same_center {n m : ℕ} (E : Finset (Fin n × Fin m))
    (h4 : ∀ a b : Fin n, ∀ c d : Fin m, a ≠ b → c ≠ d →
      ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E))
    (a b : Fin n) (L : Finset (Fin m)) (hL : 1 < L.card)
    (ha : ∀ c ∈ L, (a, c) ∈ E) (hb : ∀ c ∈ L, (b, c) ∈ E) :
    a = b := by
  by_contra hab
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hL
  exact h4 a b c d hab hcd ⟨ha c hc, ha d hd, hb c hc, hb d hd⟩

lemma distinct_centers_overlap_le_one {n m : ℕ} (E : Finset (Fin n × Fin m))
    (h4 : ∀ a b : Fin n, ∀ c d : Fin m, a ≠ b → c ≠ d →
      ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E))
    (a b : Fin n) (hab : a ≠ b) (A B : Finset (Fin m))
    (ha : ∀ c ∈ A, (a, c) ∈ E) (hb : ∀ c ∈ B, (b, c) ∈ E) :
    (A ∩ B).card ≤ 1 := by
  by_contra h
  have hlt : 1 < (A ∩ B).card := Nat.lt_of_not_ge h
  exact hab (shared_two_leaves_same_center E h4 a b (A ∩ B) hlt
    (fun c hc => ha c (Finset.mem_inter.mp hc).1)
    (fun c hc => hb c (Finset.mem_inter.mp hc).2))

lemma binary_dag_leaf_count {α : Type*} [DecidableEq α]
    (leaves gates roots : Finset α) (children : α → Finset α)
    (hdisj : Disjoint leaves gates)
    (hcover : leaves ∪ gates ⊆ roots ∪ gates.biUnion children)
    (hbinary : ∀ g ∈ gates, (children g).card ≤ 2) :
    leaves.card ≤ gates.card + roots.card := by
  have h : leaves.card + gates.card ≤ roots.card + 2 * gates.card := by
    calc
      leaves.card + gates.card = (leaves ∪ gates).card :=
        (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (roots ∪ gates.biUnion children).card := Finset.card_le_card hcover
      _ ≤ roots.card + (gates.biUnion children).card := Finset.card_union_le _ _
      _ ≤ roots.card + ∑ g ∈ gates, (children g).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ roots.card + ∑ _g ∈ gates, 2 :=
        Nat.add_le_add_left (Finset.sum_le_sum hbinary) _
      _ = roots.card + 2 * gates.card := by simp [Nat.mul_comm]
  have h' : leaves.card + gates.card ≤ (gates.card + roots.card) + gates.card := by
    simpa [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  exact Nat.le_of_add_le_add_right h'

lemma safe_pair_covers_at_most_one_matching {n m : ℕ}
    (E M : Finset (Fin n × Fin m))
    (h4 : ∀ a b : Fin n, ∀ c d : Fin m, a ≠ b → c ≠ d →
      ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E))
    (hrow : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hcol : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (A C : Finset (Fin n)) (B D : Finset (Fin m))
    (hleft : ∀ a ∈ A, ∀ c ∈ C, False)
    (hAD : ∀ a ∈ A, ∀ d ∈ D, (a, d) ∈ E)
    (hCB : ∀ c ∈ C, ∀ b ∈ B, (c, b) ∈ E) :
    (M.filter fun e => (e.1 ∈ A ∧ e.2 ∈ D) ∨
      (e.1 ∈ C ∧ e.2 ∈ B)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨heM,he⟩ := Finset.mem_filter.mp he
  obtain ⟨hfM,hf⟩ := Finset.mem_filter.mp hf
  by_contra hef
  have hr : e.1 ≠ f.1 := fun h => hef (hrow e heM f hfM h)
  have hc : e.2 ≠ f.2 := fun h => hef (hcol e heM f hfM h)
  rcases he with ⟨hea,hed⟩ | ⟨hec,heb⟩
  · rcases hf with ⟨hfa,hfd⟩ | ⟨hfc,hfb⟩
    · exact h4 e.1 f.1 e.2 f.2 hr hc
        ⟨hAD _ hea _ hed,hAD _ hea _ hfd,hAD _ hfa _ hed,hAD _ hfa _ hfd⟩
    · exact hleft _ hea _ hfc
  · rcases hf with ⟨hfa,hfd⟩ | ⟨hfc,hfb⟩
    · exact hleft _ hfa _ hec
    · exact h4 e.1 f.1 e.2 f.2 hr hc
        ⟨hCB _ hec _ heb,hCB _ hec _ hfb,hCB _ hfc _ heb,hCB _ hfc _ hfb⟩

lemma safe_pair_family_matching_bound {n m : ℕ} {ι : Type*} [DecidableEq ι]
    (E M : Finset (Fin n × Fin m)) (T : Finset ι)
    (h4 : ∀ a b : Fin n, ∀ c d : Fin m, a ≠ b → c ≠ d →
      ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E))
    (hrow : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hcol : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (A C : ι → Finset (Fin n)) (B D : ι → Finset (Fin m))
    (hleft : ∀ t ∈ T, ∀ a ∈ A t, ∀ c ∈ C t, False)
    (hAD : ∀ t ∈ T, ∀ a ∈ A t, ∀ d ∈ D t, (a, d) ∈ E)
    (hCB : ∀ t ∈ T, ∀ c ∈ C t, ∀ b ∈ B t, (c, b) ∈ E)
    (hcover : ∀ e ∈ M, ∃ t ∈ T,
      (e.1 ∈ A t ∧ e.2 ∈ D t) ∨ (e.1 ∈ C t ∧ e.2 ∈ B t)) :
    M.card ≤ T.card := by
  let U (t : ι) := M.filter fun e =>
    (e.1 ∈ A t ∧ e.2 ∈ D t) ∨ (e.1 ∈ C t ∧ e.2 ∈ B t)
  have hsub : M ⊆ T.biUnion U := by
    intro e he
    obtain ⟨t,ht,hcov⟩ := hcover e he
    exact Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_filter.mpr ⟨he,hcov⟩⟩
  have hcard : ∀ t ∈ T, (U t).card ≤ 1 := by
    intro t ht
    exact safe_pair_covers_at_most_one_matching E M h4 hrow hcol
      (A t) (C t) (B t) (D t) (hleft t ht) (hAD t ht) (hCB t ht)
  calc
    M.card ≤ (T.biUnion U).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ T, (U t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ T, 1 := Finset.sum_le_sum hcard
    _ = T.card := by simp

end PEqualNP.Outside.L_meta_5324_aux
