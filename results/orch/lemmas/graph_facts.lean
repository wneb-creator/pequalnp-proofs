import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ptEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
    (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

def ptFun (x : Fin 10 → Bool) : Bool :=
  ptEdges.any fun e => x e.1 && x e.2

lemma ptFun_eq (x : Fin 10 → Bool) :
    ptFun x = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
      x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
      x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 ||
      x 8 && x 5) := by
  simp [ptFun, ptEdges, Bool.or_assoc]

def pt20 : Circuit :=
  ⟨[⟨.or, [0, 2]⟩,
    ⟨.or, [10, 6]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [13, 8]⟩,
    ⟨.and, [3, 14]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [4, 16]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [18, 8]⟩,
    ⟨.and, [5, 19]⟩,
    ⟨.or, [9, 8]⟩,
    ⟨.and, [6, 21]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.and, [7, 23]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [25, 17]⟩,
    ⟨.or, [26, 20]⟩,
    ⟨.or, [27, 22]⟩,
    ⟨.or, [28, 24]⟩], 29⟩

lemma pt20_size : pt20.size = 20 := rfl

lemma pt20_monotone : Monotone2 pt20 := by
  simp [Monotone2, pt20]

lemma pt20_fanInTwo : FanInTwo pt20 := by
  simp [FanInTwo, pt20]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma pt20_eval : ∀ x : Fin 10 → Bool, pt20.eval (List.ofFn x) = ptFun x := by
  intro x
  have hinput : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := rfl
  have distrib (a b c : Bool) : (a && (b || c)) = (a && b || a && c) := by
    cases a <;> cases b <;> cases c <;> rfl
  rw [hinput]
  simp [pt20, Circuit.eval, Circuit.wires, GateOp.eval, ptFun, ptEdges, distrib]
  ac_rfl

lemma pt20_witness : HasCircuitSize 10 ptFun 20 :=
  ⟨pt20, pt20_fanInTwo, Nat.le_of_eq pt20_size, pt20_eval⟩

def ptIndependent (S : Finset (Fin 10)) : Prop :=
  ∀ e ∈ ptEdges, ¬ (e.1 ∈ S ∧ e.2 ∈ S)

def ptCover (S : Finset (Fin 10)) : Prop :=
  ∀ e ∈ ptEdges, e.1 ∈ S ∨ e.2 ∈ S

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma pt_independent_bound : ∀ S : Finset (Fin 10), ptIndependent S → S.card ≤ 4 := by
  unfold ptIndependent
  decide

lemma pt_independent_four :
    ptIndependent ({0, 2, 8, 9} : Finset (Fin 10)) ∧
      ({0, 2, 8, 9} : Finset (Fin 10)).card = 4 := by
  unfold ptIndependent
  decide

lemma pt_cover_bound (S : Finset (Fin 10)) (hS : ptCover S) : 6 ≤ S.card := by
  have hI : ptIndependent Sᶜ := by
    intro e he hmem
    rcases hS e he with h | h
    · exact (Finset.mem_compl.mp hmem.1) h
    · exact (Finset.mem_compl.mp hmem.2) h
  have hb := pt_independent_bound Sᶜ hI
  have hc : Sᶜ.card = 10 - S.card := by simpa using Finset.card_compl S
  have hs : S.card ≤ 10 := by simpa using Finset.card_le_univ S
  omega

lemma pt_cover_six :
    ptCover ({1, 3, 4, 5, 6, 7} : Finset (Fin 10)) ∧
      ({1, 3, 4, 5, 6, 7} : Finset (Fin 10)).card = 6 := by
  unfold ptCover
  decide

end PEqualNP.Outside.L_meta_2592
