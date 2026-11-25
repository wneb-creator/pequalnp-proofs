import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9775.CircuitHarness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Fin 14 × Fin 14) := [(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def postedEdges : List (Nat × Nat) := [(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def target (x : Fin 14 → Bool) : Bool := edges.any (fun e => x e.1 && x e.2)

lemma edge_iff : ∀ u v : Fin 14, (u, v) ∈ edges ↔ (u.val, v.val) ∈ postedEdges := by decide

lemma target_spec (x : Fin 14 → Bool) : target x = true ↔
    ∃ u v : Fin 14, (u.val, v.val) ∈ postedEdges ∧ x u = true ∧ x v = true := by
  simp only [target, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨u, v⟩, he, hu, hv⟩
    exact ⟨u, v, (edge_iff u v).mp he, hu, hv⟩
  · rintro ⟨u, v, he, hu, hv⟩
    exact ⟨(u, v), (edge_iff u v).mpr he, hu, hv⟩

theorem validated (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 24)
    (hc : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = target x) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 24 ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 14, (u.val, v.val) ∈ postedEdges ∧ x u = true ∧ x v = true) := by
  refine ⟨C, hm, hs, ?_⟩
  intro x
  rw [hc x]
  exact target_spec x

def baseline : Circuit :=
  ⟨[⟨.or, [8, 10]⟩,
    ⟨.and, [0, 14]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [16, 13]⟩,
    ⟨.and, [1, 17]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.and, [2, 19]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [21, 12]⟩,
    ⟨.and, [3, 22]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [24, 13]⟩,
    ⟨.and, [4, 25]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [27, 12]⟩,
    ⟨.and, [5, 28]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [30, 11]⟩,
    ⟨.and, [6, 31]⟩,
    ⟨.or, [15, 18]⟩,
    ⟨.or, [33, 20]⟩,
    ⟨.or, [34, 23]⟩,
    ⟨.or, [35, 26]⟩,
    ⟨.or, [36, 29]⟩,
    ⟨.or, [37, 32]⟩], 38⟩

lemma baseline_size : baseline.size = 25 := rfl

lemma baseline_monotone : Monotone2 baseline := by
  simp [Monotone2, baseline]

lemma and_or (a b c : Bool) : (a && (b || c)) = ((a && b) || (a && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma baseline_correct (x : Fin 14 → Bool) : baseline.eval (List.ofFn x) = target x := by
  simp [baseline, Circuit.eval, Circuit.wires, GateOp.eval, target, edges,
    List.getD_eq_getElem?_getD, and_or, Bool.or_assoc]

lemma baseline_spec (x : Fin 14 → Bool) : baseline.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 14, (u.val, v.val) ∈ postedEdges ∧ x u = true ∧ x v = true := by
  rw [baseline_correct]
  exact target_spec x

end PEqualNP.Outside.L_meta_9775.CircuitHarness
