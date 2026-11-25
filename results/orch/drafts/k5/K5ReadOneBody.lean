import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.K5ReadOne

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev endpoints : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

abbrev I (p : Fin 5) (l : Fin 10) : Prop :=
  p = (endpoints l).1 ∨ p = (endpoints l).2

abbrev edgePairs : Finset (Fin 15 × Fin 15) :=
  {(0,5), (1,5), (0,6), (2,6), (0,7), (3,7), (0,8), (4,8),
   (1,9), (2,9), (1,10), (3,10), (1,11), (4,11), (2,12), (3,12),
   (2,13), (4,13), (3,14), (4,14)}

abbrev G : SimpleGraph (Fin 15) where
  Adj u v := (u, v) ∈ edgePairs ∨ (v, u) ∈ edgePairs
  symm := fun _ _ h => h.symm
  loopless := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma no_four_cycle : PEqualNP.TopForm.NoFourCycle G := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma edge_count : G.edgeFinset.card = 20 := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma adj_incidence : ∀ u v : Fin 15, G.Adj u v ↔
    (∃ p : Fin 5, ∃ l : Fin 10, I p l ∧ u = Fin.castAdd 10 p ∧ v = Fin.natAdd 5 l) ∨
    (∃ p : Fin 5, ∃ l : Fin 10, I p l ∧ v = Fin.castAdd 10 p ∧ u = Fin.natAdd 5 l) := by
  decide

lemma graph_incidence (z : Fin 15 → Bool) :
    (∃ u v : Fin 15, G.Adj u v ∧ z u = true ∧ z v = true) ↔
      ∃ p : Fin 5, ∃ l : Fin 10, I p l ∧
        z (Fin.castAdd 10 p) = true ∧ z (Fin.natAdd 5 l) = true := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases (adj_incidence u v).mp huv with ⟨p, l, hi, rfl, rfl⟩ | ⟨p, l, hi, rfl, rfl⟩
    · exact ⟨p, l, hi, hu, hv⟩
    · exact ⟨p, l, hi, hv, hu⟩
  · rintro ⟨p, l, hi, hp, hl⟩
    exact ⟨Fin.castAdd 10 p, Fin.natAdd 5 l,
      (adj_incidence _ _).mpr (Or.inl ⟨p, l, hi, rfl, rfl⟩), hp, hl⟩

abbrev matchLeft (i : Fin 5) : Fin 15 := Fin.castAdd 10 i
abbrev matchRight : Fin 5 → Fin 15 := ![5, 9, 12, 14, 8]

lemma cover_card (S : Finset (Fin 15))
    (hS : ∀ u v : Fin 15, G.Adj u v → u ∈ S ∨ v ∈ S) : 5 ≤ S.card := by
  classical
  have hmatch : ∀ i : Fin 5, G.Adj (matchLeft i) (matchRight i) := by decide
  have hselect : ∀ i : Fin 5, ∃ v : Fin 15, v ∈ S ∧
      (v = matchLeft i ∨ v = matchRight i) := by
    intro i
    rcases hS _ _ (hmatch i) with hl | hr
    · exact ⟨matchLeft i, hl, Or.inl rfl⟩
    · exact ⟨matchRight i, hr, Or.inr rfl⟩
  choose pick hpick hpair using hselect
  have hseparate : ∀ i j : Fin 5, i ≠ j → ∀ v : Fin 15,
      (v = matchLeft i ∨ v = matchRight i) →
      ¬ (v = matchLeft j ∨ v = matchRight j) := by decide
  let f : Fin 5 → S := fun i => ⟨pick i, hpick i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have heq : pick i = pick j := congrArg Subtype.val hij
    by_contra hne
    apply hseparate i j hne (pick i) (hpair i)
    rw [heq]
    exact hpair j
  have hcard := Fintype.card_le_of_injective f hinj
  simpa using hcard

lemma read_one_lower_bound (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 15 C)
    (hcomp : ∀ z : Fin 15 → Bool, circuitFun 15 C z =
      decide (∃ p : Fin 5, ∃ l : Fin 10, I p l ∧
        z (Fin.castAdd 10 p) = true ∧ z (Fin.natAdd 5 l) = true))
    (hread : PEqualNP.ReadK.IsReadK 15 C 1) : 24 ≤ C.size := by
  have hg : ∀ z : Fin 15 → Bool, circuitFun 15 C z =
      decide (∃ u v : Fin 15, G.Adj u v ∧ z u = true ∧ z v = true) := by
    intro z
    rw [hcomp, graph_incidence]
  obtain ⟨S, hS, hc⟩ := PEqualNP.Outside.L_meta_2585.ReadOneCost.main_theorem
    15 G C no_four_cycle hAO hg hread
  have hs := cover_card S hS
  rw [edge_count] at hc
  omega

end PEqualNP.Outside.L_meta_2585.K5ReadOne
