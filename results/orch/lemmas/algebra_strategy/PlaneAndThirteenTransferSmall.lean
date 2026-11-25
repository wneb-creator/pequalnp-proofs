import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.PermInputs

namespace PEqualNP.Outside.L_meta_650_aux.PlaneAndThirteenTransferSmall

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs

def DifferenceAndLowerBound : Prop :=
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (13 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard

def edges : List (ℕ × ℕ) :=
[(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]

abbrev sumInc (p l : Fin 13) : Prop := p + l = 0 ∨ p + l = 1 ∨ p + l = 3 ∨ p + l = 9

abbrev diffInc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def flip : Fin 26 → Fin 26 :=
  ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,25,24,23,22,21,20,19,18,17,16,15,14]

theorem flip_point : ∀ p : Fin 13, flip (Fin.castAdd 13 p) = Fin.castAdd 13 p := by
  decide +kernel

theorem flip_line : ∀ l : Fin 13, flip (Fin.natAdd 13 l) = Fin.natAdd 13 (-l) := by
  decide +kernel

theorem neg_neg_line : ∀ l : Fin 13, -(-l) = l := by decide +kernel

theorem incidence_negation : ∀ p l : Fin 13, sumInc p (-l) ↔ diffInc p l := by
  decide +kernel

theorem coordinates_edge : ∀ p l : Fin 13,
    (p.val, 13 + l.val) ∈ edges ↔ sumInc p l := by
  decide +kernel

theorem edge_bounds : ∀ e ∈ edges, e.1 < 13 ∧ 13 ≤ e.2 ∧ e.2 < 26 := by
  decide +kernel

theorem edge_coordinates : ∀ u v : Fin 26,
    (u.val, v.val) ∈ edges ↔ ∃ p l : Fin 13,
      u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l ∧ sumInc p l := by
  intro u v
  constructor
  · intro he
    have hb := edge_bounds (u.val, v.val) he
    let p : Fin 13 := ⟨u.val, hb.1⟩
    let l : Fin 13 := ⟨v.val - 13, by omega⟩
    have hp : u = Fin.castAdd 13 p := by apply Fin.ext; rfl
    have hl : v = Fin.natAdd 13 l := by apply Fin.ext; dsimp [l]; omega
    refine ⟨p, l, hp, hl, (coordinates_edge p l).mp ?_⟩
    simpa only [hp, hl, Fin.val_castAdd, Fin.val_natAdd] using he
  · rintro ⟨p, l, rfl, rfl, hinc⟩
    exact (coordinates_edge p l).mpr hinc

theorem point_inj (p q : Fin 13) : Fin.castAdd 13 p = Fin.castAdd 13 q ↔ p = q := by
  constructor
  · intro h; exact Fin.ext (congrArg (fun z : Fin 26 => z.val) h)
  · exact congrArg (Fin.castAdd 13)

theorem line_inj (p q : Fin 13) : Fin.natAdd 13 p = Fin.natAdd 13 q ↔ p = q := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg (fun z : Fin 26 => z.val) h
    simp only [Fin.val_natAdd] at hv
    omega
  · exact congrArg (Fin.natAdd 13)

theorem point_ne_line (p q : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 q := by
  intro h
  have hv := congrArg (fun z : Fin 26 => z.val) h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

theorem line_ne_point (p q : Fin 13) : Fin.natAdd 13 p ≠ Fin.castAdd 13 q :=
  (point_ne_line q p).symm

theorem relabeled_eval (C : Circuit) (x : Fin 26 → Bool) :
    (relabel 26 26 flip C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ flip)) :=
  (rel_fold 26 26 flip C.gates _ _ (rel_init 26 26 flip x)).2.2 C.output

theorem relabel_and_count (C : Circuit) :
    {j : Fin (relabel 26 26 flip C).gates.length |
      ((relabel 26 26 flip C).gates.get j).op = GateOp.and}.ncard =
    {j : Fin C.gates.length | (C.gates.get j).op = GateOp.and}.ncard := by
  change {j : Fin (C.gates.map (relGate 26 26 flip)).length |
    ((C.gates.map (relGate 26 26 flip)).get j).op = GateOp.and}.ncard = _
  apply Set.ncard_congr
    (fun j _ => (⟨j.val, by simpa only [List.length_map] using j.isLt⟩ : Fin C.gates.length))
  · intro j hj
    change (C.gates.get ⟨j.val, _⟩).op = GateOp.and
    change ((C.gates.map (relGate 26 26 flip)).get j).op = GateOp.and at hj
    rw [List.get_eq_getElem, List.getElem_map] at hj
    exact hj
  · intro a b ha hb hab
    exact Fin.ext (congrArg (fun j : Fin C.gates.length => j.val) hab)
  · intro j hj
    let k : Fin (C.gates.map (relGate 26 26 flip)).length :=
      ⟨j.val, by simpa only [List.length_map] using j.isLt⟩
    refine ⟨k, ?_, ?_⟩
    · change ((C.gates.map (relGate 26 26 flip)).get k).op = GateOp.and
      change (C.gates.get j).op = GateOp.and at hj
      rw [List.get_eq_getElem, List.getElem_map]
      exact hj
    · exact Fin.ext rfl

theorem thirteen_ands (hBase : DifferenceAndLowerBound) (C : Circuit) (hm : Monotone2 C)
    (hcorrect : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true) :
    13 ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.and}.ncard := by
  let D := relabel 26 26 flip C
  have hdmono : Monotone2 D := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hm g0 hg0).1, by simpa [relGate] using (hm g0 hg0).2⟩
  have hdcorrect : ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, diffInc p l ∧ x (Fin.castAdd 13 p) = true ∧
        x (Fin.natAdd 13 l) = true := by
    intro x
    change (relabel 26 26 flip C).eval (List.ofFn x) = true ↔ _
    rw [relabeled_eval, hcorrect]
    constructor
    · rintro ⟨u, v, he, hu, hv⟩
      obtain ⟨p, l, rfl, rfl, hinc⟩ := (edge_coordinates u v).mp he
      refine ⟨p, -l, (incidence_negation p (-l)).mp ?_, ?_, ?_⟩
      · simpa only [neg_neg_line] using hinc
      · simpa only [Function.comp_apply, flip_point] using hu
      · simpa only [Function.comp_apply, flip_line] using hv
    · rintro ⟨p, l, hinc, hp, hl⟩
      refine ⟨Fin.castAdd 13 p, Fin.natAdd 13 (-l),
        (edge_coordinates _ _).mpr ⟨p, -l, rfl, rfl, (incidence_negation p l).mpr hinc⟩,
        ?_, ?_⟩
      · simpa only [Function.comp_apply, flip_point] using hp
      · simpa only [Function.comp_apply, flip_line, neg_neg_line] using hl
  have h13 := hBase D hdmono
    (by
      intro p l hinc
      apply (hdcorrect _).mpr
      refine ⟨p, l, hinc, ?_, ?_⟩ <;> simp)
    (by
      intro P _ _
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨p, l, hinc, hp, hl⟩ := (hdcorrect _).mp ht
      have hpP : p ∈ P := by
        simp only [decide_eq_true_eq, point_inj, point_ne_line,
          false_and, exists_false, or_false] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        exact hq
      have hlP : ∀ q ∈ P, ¬ diffInc q l := by
        simp only [decide_eq_true_eq, line_inj, line_ne_point,
          and_false, exists_false, false_or] at hl
        obtain ⟨q, rfl, hq⟩ := hl
        exact hq
      exact hlP p hpP hinc)
  rw [← relabel_and_count C]
  exact h13

end PEqualNP.Outside.L_meta_650_aux.PlaneAndThirteenTransferSmall
