import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.FactoryBoundaryBudget

open PEqualNP.TopForm

lemma input_union_card_le (inputs : ℕ → Finset ℕ) (M : Finset ℕ)
    (fanin : ∀ i ∈ M, (inputs i).card ≤ 2) :
    (M.biUnion inputs).card ≤ 2 * M.card := by
  induction M using Finset.induction_on with
  | empty => simp
  | @insert a M notMem ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem notMem]
    calc
      (inputs a ∪ M.biUnion inputs).card ≤ (inputs a).card + (M.biUnion inputs).card :=
        Finset.card_union_le _ _
      _ ≤ 2 + 2 * M.card := Nat.add_le_add (fanin a (by simp))
        (ih (fun i hi => fanin i (by simp [hi])))
      _ = 2 * (M.card + 1) := by omega

lemma binary_boundary_card_le (inputs : ℕ → Finset ℕ) (M : Finset ℕ) (r : ℕ)
    (rootMem : r ∈ M) (fanin : ∀ i ∈ M, (inputs i).card ≤ 2)
    (connected : ∀ i ∈ M, i ≠ r → i ∈ M.biUnion inputs) :
    ((M.biUnion inputs) \ M).card ≤ M.card + 1 := by
  have disjoint : Disjoint (M.erase r) ((M.biUnion inputs) \ M) := by
    apply Finset.disjoint_left.mpr
    intro i hi hb
    exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_of_mem_erase hi)
  have subset : M.erase r ∪ ((M.biUnion inputs) \ M) ⊆ M.biUnion inputs := by
    intro i hi
    rcases Finset.mem_union.mp hi with hm | hb
    · exact connected i (Finset.mem_of_mem_erase hm) (Finset.mem_erase.mp hm).1
    · exact (Finset.mem_sdiff.mp hb).1
  have bound := (Finset.card_le_card subset).trans (input_union_card_le inputs M fanin)
  rw [Finset.card_union_of_disjoint disjoint, Finset.card_erase_of_mem rootMem] at bound
  have positive : 0 < M.card := Finset.card_pos.mpr ⟨r, rootMem⟩
  omega

lemma splitting_budget (m t q : ℕ) (boundary : t + q ≤ m + 1)
    (nontrivial : 2 ≤ t + q) :
    t + 2 * q - 2 + 1 ≤ m + q := by omega

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) {a b p q : Fin n} (hab : a ≠ b)
    (hap : G.Adj a p) (hbp : G.Adj b p) (haq : G.Adj a q) (hbq : G.Adj b q) :
    p = q := by
  apply Finset.card_le_one.mp (hfour a b hab)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hap, hbp⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, haq, hbq⟩

lemma mixed_support_unique_at_center {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hfour : NoFourCycle G)
    (u v w : Fin n) (wu : w ≠ u) (wv : w ≠ v)
    (a b c d : Fin n) (ua : G.Adj u a) (uc : G.Adj u c)
    (vb : G.Adj v b) (vd : G.Adj v d)
    (wa : G.Adj w a) (wb : G.Adj w b) (wc : G.Adj w c) (wd : G.Adj w d) :
    (a, b) = (c, d) := by
  have ac := common_neighbor_unique G hfour wu wa ua wc uc
  have bd := common_neighbor_unique G hfour wv wb vb wd vd
  exact Prod.ext ac bd

lemma outside_centers_injective {n : ℕ} {ι : Type} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hfour : NoFourCycle G) (u v : Fin n)
    (pairs : ι → Fin n × Fin n) (centers : ι → Fin n)
    (distinctPairs : Function.Injective pairs)
    (outside : ∀ i, centers i ≠ u ∧ centers i ≠ v)
    (starLeaves : ∀ i, G.Adj u (pairs i).1 ∧ G.Adj v (pairs i).2)
    (reader : ∀ i, G.Adj (centers i) (pairs i).1 ∧ G.Adj (centers i) (pairs i).2) :
    Function.Injective centers := by
  intro i j same
  apply distinctPairs
  apply mixed_support_unique_at_center G hfour u v (centers i)
    (outside i).1 (outside i).2 (pairs i).1 (pairs i).2 (pairs j).1 (pairs j).2
    (starLeaves i).1 (starLeaves j).1 (starLeaves i).2 (starLeaves j).2
    (reader i).1 (reader i).2
  · rw [same]
    exact (reader j).1
  · rw [same]
    exact (reader j).2

end PEqualNP.Outside.L_meta_1772_aux.FactoryBoundaryBudget
