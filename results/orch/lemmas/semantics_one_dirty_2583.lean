import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.OneDirty

open PEqualNP.ReadK

def orOn {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def block {n : ℕ} (A B R : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  orOn A x && orOn B x && orOn R x

lemma orOn_pair {n : ℕ} (A : Finset (Fin n)) (u v : Fin n) :
    orOn A (setInput {u, v}) = true ↔ u ∈ A ∨ v ∈ A := by
  simp only [orOn, decide_eq_true_eq, setInput, Finset.mem_insert, Finset.mem_singleton]
  aesop

lemma block_pair {n : ℕ} (A B R : Finset (Fin n)) (hAB : Disjoint A B)
    (u v : Fin n) :
    block A B R (setInput {u, v}) = true ↔
      (u ∈ A ∧ v ∈ B ∧ (u ∈ R ∨ v ∈ R)) ∨
      (v ∈ A ∧ u ∈ B ∧ (u ∈ R ∨ v ∈ R)) := by
  have hu : ¬(u ∈ A ∧ u ∈ B) := fun h => Finset.disjoint_left.mp hAB h.1 h.2
  have hv : ¬(v ∈ A ∧ v ∈ B) := fun h => Finset.disjoint_left.mp hAB h.1 h.2
  simp only [block, Bool.and_eq_true, orOn_pair]
  tauto

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (∃ s t : Fin n, G.Adj s t ∧ setInput {u, v} s = true ∧
      setInput {u, v} t = true) ↔ G.Adj u v := by
  simp only [setInput, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨s, t, hst, hs, ht⟩
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact (hst.ne rfl).elim
    · exact hst
    · exact hst.symm
    · exact (hst.ne rfl).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma block_cross_safe {n : ℕ} (G : SimpleGraph (Fin n)) (A B R : Finset (Fin n))
    (below : ∀ x : Fin n → Bool, block A B R x = true →
      ∃ s t : Fin n, G.Adj s t ∧ x s = true ∧ x t = true) :
    ∀ u ∈ A, ∀ v ∈ B, u ∈ R ∨ v ∈ R → G.Adj u v := by
  intro u hu v hv hR
  apply (graph_pair G u v).mp
  apply below (setInput {u, v})
  simp only [block, Bool.and_eq_true, orOn_pair]
  exact ⟨⟨Or.inl hu, Or.inr hv⟩, hR⟩

def pairEdges {n : ℕ} (A B R : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  ((A ∩ R) ×ˢ B) ∪ (A ×ˢ (B ∩ R))

lemma family_pairEdges {n k : ℕ} (A B : Finset (Fin n))
    (R : Fin k → Finset (Fin n)) :
    Finset.univ.biUnion (fun i => pairEdges A B (R i)) =
      ((A ∩ Finset.univ.biUnion R) ×ˢ B) ∪
        (A ×ˢ (B ∩ Finset.univ.biUnion R)) := by
  ext e
  rcases e with ⟨u, v⟩
  simp only [pairEdges, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_product, Finset.mem_inter]
  aesop

lemma rectangle_side_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (noFour : PEqualNP.TopForm.NoFourCycle G)
    (U B : Finset (Fin n)) (hB : 2 ≤ B.card)
    (cross : ∀ u ∈ U, ∀ b ∈ B, G.Adj u b) : U.card ≤ 1 := by
  by_contra hU
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < U.card by omega)
  have hsub : B ⊆ Finset.univ.filter (fun b => G.Adj u b ∧ G.Adj v b) := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cross u hu b hb, cross v hv b hb⟩
  have hcard := Finset.card_le_card hsub
  have hbound := noFour u v huv
  omega

lemma family_centres_bound {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (noFour : PEqualNP.TopForm.NoFourCycle G)
    (A B : Finset (Fin n)) (R : Fin k → Finset (Fin n))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (below : ∀ i : Fin k, ∀ x : Fin n → Bool, block A B (R i) x = true →
      ∃ s t : Fin n, G.Adj s t ∧ x s = true ∧ x t = true) :
    (A ∩ Finset.univ.biUnion R).card ≤ 1 ∧
      (B ∩ Finset.univ.biUnion R).card ≤ 1 := by
  constructor
  · apply rectangle_side_bound G noFour _ B hB
    intro u hu v hv
    obtain ⟨huA, huR⟩ := Finset.mem_inter.mp hu
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp huR
    exact block_cross_safe G A B (R i) (below i) u huA v hv (Or.inl hi)
  · apply rectangle_side_bound G noFour _ A hA
    intro v hv u hu
    obtain ⟨hvB, hvR⟩ := Finset.mem_inter.mp hv
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hvR
    exact (block_cross_safe G A B (R i) (below i) u hu v hvB (Or.inr hi)).symm

end PEqualNP.Outside.L_meta_2583_aux.OneDirty
