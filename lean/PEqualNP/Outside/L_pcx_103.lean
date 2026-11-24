import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Multiset.Fold
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_103

open PEqualNP.ProofComplexity

def resolution_check {V : Type} [DecidableEq V] (w : ℕ) (acc : List (Clause V)) :
    List (ℕ × ℕ × V) → Bool
  | [] => decide ((∅ : Clause V) ∈ acc)
  | (i, j, v) :: steps =>
    match acc[i]?, acc[j]? with
    | some C, some D =>
      let R := C.erase (v, true) ∪ D.erase (v, false)
      if (v, true) ∈ C ∧ (v, false) ∈ D ∧ R.card ≤ w then
        resolution_check w (R :: acc) steps
      else false
    | _, _ => false

lemma resolution_bases {V : Type} [DecidableEq V] (F : Set (Clause V)) (base : List (Clause V))
    (hb : ∀ C ∈ base, C ∈ F) : IsDerivation F base := by
  induction base with
  | nil => exact .nil
  | cons C cs ih =>
    exact .ax (ih (fun D hD => hb D (List.mem_cons_of_mem _ hD))) (hb C List.mem_cons_self)

lemma resolution_check_sound {V : Type} [DecidableEq V] (F : Set (Clause V)) (w : ℕ)
    (acc : List (Clause V)) (steps : List (ℕ × ℕ × V)) (hd : IsDerivation F acc)
    (hw : ∀ C ∈ acc, C.card ≤ w) (hc : resolution_check w acc steps = true) :
    ∃ π, IsRefutation F π ∧ ∀ C ∈ π, C.card ≤ w := by
  induction steps generalizing acc with
  | nil =>
    exact ⟨acc, ⟨hd, of_decide_eq_true hc⟩, hw⟩
  | cons s steps ih =>
    obtain ⟨i, j, v⟩ := s
    cases hi : acc[i]? with
    | none => simp [resolution_check, hi] at hc
    | some C =>
      cases hj : acc[j]? with
      | none => simp [resolution_check, hi, hj] at hc
      | some D =>
        let R := C.erase (v, true) ∪ D.erase (v, false)
        simp only [resolution_check, hi, hj] at hc
        change (if (v, true) ∈ C ∧ (v, false) ∈ D ∧ R.card ≤ w then
          resolution_check w (R :: acc) steps else false) = true at hc
        by_cases h : (v, true) ∈ C ∧ (v, false) ∈ D ∧ R.card ≤ w
        · rw [ite_eq_left h] at hc
          have hC : C ∈ acc := List.mem_of_getElem? hi
          have hD : D ∈ acc := List.mem_of_getElem? hj
          have hr : IsResolvent C D R := ⟨v, h.1, h.2.1, rfl⟩
          refine ih (R :: acc) (.res hd hC hD hr) ?_ hc
          intro E hE
          rcases List.mem_cons.mp hE with rfl | he
          · exact h.2.2
          · exact hw E he
        · rw [ite_eq_right h] at hc
          contradiction

theorem resolution_certificate {V : Type} [DecidableEq V] (F : Set (Clause V)) (w : ℕ)
    (base : List (Clause V)) (steps : List (ℕ × ℕ × V))
    (hb : ∀ C ∈ base, C ∈ F) (hw : ∀ C ∈ base, C.card ≤ w)
    (hc : resolution_check w base steps = true) :
    ∃ π, IsRefutation F π ∧ ∀ C ∈ π, C.card ≤ w :=
  resolution_check_sound F w base steps (resolution_bases F base hb) hw hc

abbrev CV (n : ℕ) := Fin n ⊕ (ℕ × ℕ)

def counter_formula (n k : ℕ) (edges : List (Fin n × Fin n)) : Set (Clause (CV n)) :=
  {C | ∃ e ∈ edges, C = {(Sum.inl e.1, true), (Sum.inl e.2, true)}} ∪
  {C | ∃ i : Fin n, i.val + 1 < n ∧ C = {(Sum.inl i, false), (Sum.inr (i.val,0), true)}} ∪
  {C | ∃ (i : Fin n) (h j : ℕ), i.val = h+1 ∧ i.val+1 < n ∧ j < k ∧
    C = {(Sum.inr (h,j), false), (Sum.inr (i.val,j), true)}} ∪
  {C | ∃ (i : Fin n) (h j : ℕ), i.val = h+1 ∧ i.val+1 < n ∧ j+1 < k ∧
    C = {(Sum.inl i, false), (Sum.inr (h,j), false), (Sum.inr (i.val,j+1), true)}} ∪
  {C | ∃ (i : Fin n) (h : ℕ), i.val = h+1 ∧ C = {(Sum.inl i, false), (Sum.inr (h,k-1), false)}} ∪
  {C | ∃ j : ℕ, 1 ≤ j ∧ j < k ∧ C = {(Sum.inr (0,j), false)}}

def sourceClause {n : ℕ} (k : ℕ) (s : ℕ × Fin n × Fin n) : Clause (CV n) :=
  let i := s.2.1
  let j := s.2.2
  match s.1 with
  | 0 => {(Sum.inl i, true), (Sum.inl j, true)}
  | 1 => {(Sum.inl i, false), (Sum.inr (i.val,0), true)}
  | 2 => {(Sum.inr (i.val-1,j.val), false), (Sum.inr (i.val,j.val), true)}
  | 3 => {(Sum.inl i, false), (Sum.inr (i.val-1,j.val), false), (Sum.inr (i.val,j.val+1), true)}
  | 4 => {(Sum.inl i, false), (Sum.inr (i.val-1,k-1), false)}
  | _ => {(Sum.inr (0,j.val), false)}

def sourceOK {n : ℕ} (k : ℕ) (edges : List (Fin n × Fin n)) (s : ℕ × Fin n × Fin n) : Bool :=
  let i := s.2.1
  let j := s.2.2
  match s.1 with
  | 0 => decide ((i,j) ∈ edges)
  | 1 => decide (i.val+1 < n)
  | 2 => decide (0 < i.val ∧ i.val+1 < n ∧ j.val < k)
  | 3 => decide (0 < i.val ∧ i.val+1 < n ∧ j.val+1 < k)
  | 4 => decide (0 < i.val)
  | _ => decide (1 ≤ j.val ∧ j.val < k)

lemma source_member {n k : ℕ} (edges : List (Fin n × Fin n)) (s : ℕ × Fin n × Fin n)
    (hs : sourceOK k edges s = true) : sourceClause k s ∈ counter_formula n k edges := by
  obtain ⟨tag, i, j⟩ := s
  rcases tag with _|tag
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(i,j), of_decide_eq_true hs, rfl⟩))))
  rcases tag with _|tag
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, of_decide_eq_true hs, rfl⟩))))
  rcases tag with _|tag
  · have h : 0 < i.val ∧ i.val+1 < n ∧ j.val < k := of_decide_eq_true hs
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨i, i.val-1, j.val, by omega, h.2.1, h.2.2, rfl⟩)))
  rcases tag with _|tag
  · have h : 0 < i.val ∧ i.val+1 < n ∧ j.val+1 < k := of_decide_eq_true hs
    exact Or.inl (Or.inl (Or.inr ⟨i, i.val-1, j.val, by omega, h.2.1, h.2.2, rfl⟩))
  rcases tag with _|tag
  · have h : 0 < i.val := of_decide_eq_true hs
    exact Or.inl (Or.inr ⟨i, i.val-1, by omega, rfl⟩)
  · have h : 1 ≤ j.val ∧ j.val < k := of_decide_eq_true hs
    exact Or.inr ⟨j.val, h.1, h.2, rfl⟩


def upperEdges10 : List (Fin 10 × Fin 10) := [
    (0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6),
    (2,7), (3,8), (4,9), (5,7), (7,9), (9,6), (6,8),
    (8,5)]

def upperSources10 : List (ℕ × Fin 10 × Fin 10) := [
    (0,0,1), (0,1,2), (0,2,3), (0,3,4), (0,4,0),
    (0,5,7), (0,7,9), (0,9,6), (0,6,8), (0,8,5),
    (1,0,0), (1,1,0), (2,1,0), (2,2,0), (2,2,1),
    (2,3,1), (2,4,2), (2,5,2), (2,6,2), (2,6,3),
    (2,7,3), (2,7,4), (2,8,4), (3,1,0), (3,2,0),
    (3,3,0), (3,3,1), (3,4,1), (3,5,2), (3,6,2),
    (3,6,3), (3,7,2), (3,7,3), (3,8,3), (4,7,0),
    (4,8,0), (4,9,0)]

def upperSteps10 : List (ℕ × ℕ × CV 10) := [
    (36,25,Sum.inl 1), (27,25,Sum.inr (0,0)), (21,20,Sum.inr (5,2)),
    (20,19,Sum.inr (6,3)), (19,18,Sum.inr (7,4)), (31,18,Sum.inr (0,0)),
    (41,18,Sum.inl 2), (41,19,Sum.inl 2), (31,19,Sum.inr (2,0)),
    (42,19,Sum.inl 3), (43,19,Sum.inl 4), (43,20,Sum.inl 4),
    (33,21,Sum.inr (3,1)), (44,21,Sum.inl 5), (41,22,Sum.inl 5),
    (34,22,Sum.inr (5,2)), (44,22,Sum.inl 6), (47,21,Sum.inl 7),
    (46,21,Sum.inl 8), (35,22,Sum.inr (7,3)), (50,22,Sum.inl 7),
    (50,21,Sum.inl 9), (19,27,Sum.inr (6,2)), (18,23,Sum.inr (8,4)),
    (18,46,Sum.inr (1,1)), (23,18,Sum.inr (1,0)), (25,18,Sum.inr (1,0)),
    (26,18,Sum.inr (1,0)), (18,48,Sum.inr (3,2)), (50,18,Sum.inr (3,1)),
    (16,26,Sum.inr (5,3)), (16,14,Sum.inr (5,3)), (14,33,Sum.inr (7,4)),
    (13,33,Sum.inr (8,4)), (15,12,Sum.inr (8,4)), (14,11,Sum.inl 9),
    (10,11,Sum.inl 1), (9,25,Sum.inr (3,1)), (9,25,Sum.inl 4),
    (12,9,Sum.inr (2,1)), (9,17,Sum.inl 7), (8,7,Sum.inl 9),
    (7,26,Sum.inl 6), (11,7,Sum.inr (6,4)), (7,5,Sum.inr (2,1)),
    (5,7,Sum.inl 3), (5,3,Sum.inr (7,3)), (3,5,Sum.inl 8),
    (2,3,Sum.inl 0), (2,1,Sum.inr (6,3)), (1,0,Sum.inr (4,2))]

def upperBase10 : List (Clause (CV 10)) := (upperSources10.map (sourceClause 5)).reverse

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
lemma width_three_10 : ∃ π,
    IsRefutation (counter_formula 10 5 upperEdges10) π ∧ ∀ C ∈ π, C.card ≤ 3 := by
  apply resolution_certificate _ 3 upperBase10 upperSteps10
  · intro C hC
    rw [upperBase10, List.mem_reverse] at hC
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hC
    have h : upperSources10.all (sourceOK 5 upperEdges10) = true := by decide
    exact source_member _ s (List.all_eq_true.mp h s hs)
  · have h : upperBase10.all (fun C => decide (C.card ≤ 3)) = true := by decide
    exact fun C hC => of_decide_eq_true (List.all_eq_true.mp h C hC)
  · decide

def upperEdges8 : List (Fin 8 × Fin 8) := [
    (0,4), (0,5), (0,6), (0,7), (1,4), (1,5), (1,6),
    (1,7), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5),
    (3,6), (3,7)]

def upperSources8 : List (ℕ × Fin 8 × Fin 8) := [
    (0,0,5), (0,0,6), (0,0,7), (0,1,5), (0,1,6),
    (0,1,7), (0,2,4), (0,3,4), (0,3,5), (1,0,0),
    (1,3,0), (1,4,0), (2,2,1), (2,3,1), (2,4,0),
    (3,1,0), (3,2,1), (3,3,1), (3,4,1), (3,5,0),
    (3,6,1), (4,3,0), (4,4,0), (4,5,0), (4,7,0)]

def upperSteps8 : List (ℕ × ℕ × CV 8) := [
    (24,15,Sum.inl 0), (24,16,Sum.inl 0), (24,17,Sum.inl 0),
    (20,16,Sum.inl 4), (16,15,Sum.inr (2,1)), (19,15,Sum.inr (3,0)),
    (27,15,Sum.inl 1), (27,16,Sum.inl 1), (27,17,Sum.inl 1),
    (27,17,Sum.inl 2), (22,17,Sum.inr (2,1)), (28,17,Sum.inl 4),
    (28,13,Sum.inl 5), (17,13,Sum.inr (6,2)), (10,8,Sum.inl 3),
    (14,8,Sum.inr (0,0)), (14,8,Sum.inr (0,0)), (14,8,Sum.inr (0,0)),
    (8,21,Sum.inr (2,2)), (8,21,Sum.inr (3,2)), (15,8,Sum.inr (3,1)),
    (6,26,Sum.inr (4,0)), (5,8,Sum.inl 6), (4,3,Sum.inl 4),
    (3,11,Sum.inr (4,2)), (9,3,Sum.inl 5), (8,3,Sum.inl 7),
    (2,3,Sum.inl 3), (2,1,Sum.inr (5,1)), (0,1,Sum.inr (1,1))]

def upperBase8 : List (Clause (CV 8)) := (upperSources8.map (sourceClause 3)).reverse

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
lemma width_three_8 : ∃ π,
    IsRefutation (counter_formula 8 3 upperEdges8) π ∧ ∀ C ∈ π, C.card ≤ 3 := by
  apply resolution_certificate _ 3 upperBase8 upperSteps8
  · intro C hC
    rw [upperBase8, List.mem_reverse] at hC
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hC
    have h : upperSources8.all (sourceOK 3 upperEdges8) = true := by decide
    exact source_member _ s (List.all_eq_true.mp h s hs)
  · have h : upperBase8.all (fun C => decide (C.card ≤ 3)) = true := by decide
    exact fun C hC => of_decide_eq_true (List.all_eq_true.mp h C hC)
  · decide

end PEqualNP.Outside.L_pcx_103

namespace PEqualNP.Outside.L_pcx_103

open PEqualNP.ProofComplexity

private lemma narrow_resolvent_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : Clause V}
    (h : IsResolvent C D R) (hC : ClauseSat a C) (hD : ClauseSat a D) : ClauseSat a R := by
  obtain ⟨v, _, _, rfl⟩ := h
  obtain ⟨l, hl, hal⟩ := hC
  obtain ⟨l', hl', hal'⟩ := hD
  by_cases h : l = (v, true)
  · subst l
    refine ⟨l', Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hl'⟩), hal'⟩
    rintro rfl
    simp_all
  · exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hl⟩), hal⟩

lemma narrow_sound {V : Type} [DecidableEq V] (a : V → Bool) {F : Set (Clause V)}
    {π : List (Clause V)} {w : ℕ} (der : IsDerivation F π)
    (axs : ∀ C ∈ F, C.card ≤ w → ClauseSat a C) (bounded : ∀ C ∈ π, C.card ≤ w) :
    ∀ C ∈ π, ClauseSat a C := by
  induction der with
  | nil =>
    intro C hC
    simp at hC
  | ax _ ha ih =>
    intro C hC
    rcases List.mem_cons.mp hC with rfl | ht
    · exact axs _ ha (bounded _ (by simp))
    · exact ih (fun D hD => bounded D (List.mem_cons_of_mem _ hD)) C ht
  | res _ hC hD hr ih =>
    have tail := ih (fun D hD => bounded D (List.mem_cons_of_mem _ hD))
    intro E hE
    rcases List.mem_cons.mp hE with rfl | ht
    · exact narrow_resolvent_sound a hr (tail _ hC) (tail _ hD)
    · exact tail E ht

def counter_assignment {n : ℕ} : CV n → Bool
  | Sum.inl _ => true
  | Sum.inr (_,j) => decide (j = 0)

lemma counter_narrow_sat {n k : ℕ} (edges : List (Fin n × Fin n)) (hk : 2 ≤ k) :
    ∀ C ∈ counter_formula n k edges, C.card ≤ 2 → ClauseSat counter_assignment C := by
  intro C hC hsize
  rcases hC with (((((h | h) | h) | h) | h) | h)
  · obtain ⟨e, _, rfl⟩ := h
    exact ⟨(Sum.inl e.1,true), by simp, rfl⟩
  · obtain ⟨i, _, rfl⟩ := h
    exact ⟨(Sum.inr (i.val,0),true), by simp, rfl⟩
  · obtain ⟨i, h, j, _, _, _, rfl⟩ := h
    by_cases he : j = 0
    · exact ⟨(Sum.inr (i.val,j),true), by simp, by simp [counter_assignment,he]⟩
    · exact ⟨(Sum.inr (h,j),false), by simp, by simp [counter_assignment,he]⟩
  · obtain ⟨i, h, j, _, _, _, rfl⟩ := h
    simp at hsize
  · obtain ⟨i, h, _, rfl⟩ := h
    refine ⟨(Sum.inr (h,k-1), false), by simp, ?_⟩
    have hn : k-1 ≠ 0 := by omega
    simp [counter_assignment,hn]
  · obtain ⟨j, hj, _, rfl⟩ := h
    refine ⟨(Sum.inr (0,j),false), by simp, ?_⟩
    have hn : j ≠ 0 := by omega
    simp [counter_assignment,hn]

open MvPolynomial

lemma clause_exact_degree {V : Type} (C : Clause V) :
    (clausePoly C).totalDegree = C.card := by
  classical
  let f : Literal V → MvPolynomial V (ZMod 2) := fun l => if l.2 then 1 + X l.1 else X l.1
  have fd : ∀ l, (f l).totalDegree = 1 := by
    intro l
    rcases l with ⟨v,b⟩
    cases b
    · simp [f]
    · change (1 + X v : MvPolynomial V (ZMod 2)).totalDegree = 1
      rw [totalDegree_add_eq_right_of_totalDegree_lt
        (by rw [totalDegree_one,totalDegree_X]; exact Nat.zero_lt_one),totalDegree_X]
  have fnz : ∀ l, f l ≠ 0 := by
    intro l hz
    have := fd l
    simp [hz] at this
  change (∏ l ∈ C, f l).totalDegree = _
  induction C using Finset.induction_on with
  | empty => simp
  | insert l C hl ih =>
    rw [Finset.prod_insert hl, Finset.card_insert_of_notMem hl,
      totalDegree_mul_of_isDomain (fnz l) (Finset.prod_ne_zero_iff.mpr fun l _ => fnz l),
      ih,fd,add_comm]

lemma clause_eval_zero {V : Type} (a : V → Bool) (C : Clause V) (hs : ClauseSat a C) :
    eval (fun v => if a v then (1 : ZMod 2) else 0) (clausePoly C) = 0 := by
  obtain ⟨⟨v,b⟩, hl, hab⟩ := hs
  change a v = b at hab
  unfold clausePoly
  rw [map_prod]
  apply Finset.prod_eq_zero hl
  cases b
  · simp [hab]
  · simp [hab]
    decide

lemma no_low_pc_model {V : Type} (F : Set (Clause V)) (b : ℕ) (a : V → Bool)
    (hs : ∀ C ∈ F, C.card ≤ b → ClauseSat a C) : ¬ PCRefutable (cnfSystem F) b := by
  intro hf
  let ev := eval (fun v => if a v then (1 : ZMod 2) else 0)
  have vanish {p : MvPolynomial V (ZMod 2)} (hp : PCDerivable (cnfSystem F) b p) : ev p = 0 := by
    induction hp with
    | ax hp hd =>
      rcases hp with ⟨v,rfl⟩ | ⟨C,hC,rfl⟩
      · change eval _ _ = 0
        simp only [map_add,map_mul,eval_X]
        cases a v <;> decide
      · rw [clause_exact_degree] at hd
        exact clause_eval_zero a C (hs C hC hd)
    | zero => exact map_zero _
    | add _ _ ih ih' => rw [map_add,ih,ih',add_zero]
    | mulX _ _ _ ih => rw [map_mul,ih,mul_zero]
  have hno := vanish hf
  change eval _ (1 : MvPolynomial V (ZMod 2)) = 0 at hno
  simp at hno

lemma counter_lower {n k : ℕ} (edges : List (Fin n × Fin n)) (hk : 2 ≤ k) :
    (¬ ∃ π, IsRefutation (counter_formula n k edges) π ∧ ∀ C ∈ π, C.card ≤ 2) ∧
    ¬ PCRefutable (cnfSystem (counter_formula n k edges)) 2 := by
  have hs := counter_narrow_sat edges hk
  refine ⟨?_, no_low_pc_model _ _ _ hs⟩
  rintro ⟨π,⟨hπ,hE⟩,hw⟩
  obtain ⟨l,hl,_⟩ := narrow_sound counter_assignment hπ hs hw ∅ hE
  simp at hl

end PEqualNP.Outside.L_pcx_103

namespace PEqualNP.Outside.L_pcx_103

open PEqualNP.ProofComplexity MvPolynomial

noncomputable def pcFactor {V : Type} (l : Literal V) : MvPolynomial V (ZMod 2) :=
  if l.2 = true then 1 + X l.1 else X l.1

lemma degFactor {V : Type} (l : Literal V) : (pcFactor l).totalDegree ≤ 1 := by
  unfold pcFactor
  split
  · exact (totalDegree_add _ _).trans (by simp [totalDegree_X])
  · simp [totalDegree_X]

lemma clause_insert {V : Type} [DecidableEq V] (l : Literal V) (C : Clause V) (hl : l ∉ C) :
    clausePoly (insert l C) = pcFactor l * clausePoly C := by
  simp [clausePoly, pcFactor, Finset.prod_insert hl]

lemma degClause {V : Type} (C : Clause V) : (clausePoly C).totalDegree ≤ C.card := by
  classical
  induction C using Finset.induction_on with
  | empty => simp [clausePoly]
  | insert l C hl ih =>
    rw [clause_insert l C hl, Finset.card_insert_of_notMem hl]
    exact (totalDegree_mul _ _).trans (by have h := degFactor l; omega)

lemma pc_multiply_clause {V : Type} {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (C : Clause V) (p : MvPolynomial V (ZMod 2)) (hp : PCDerivable F B p)
    (hb : C.card + p.totalDegree ≤ B) : PCDerivable F B (clausePoly C * p) := by
  classical
  induction C using Finset.induction_on with
  | empty => simpa [clausePoly] using hp
  | insert l C hl ih =>
    rw [Finset.card_insert_of_notMem hl] at hb
    have hq := ih (by omega)
    let q := clausePoly C * p
    have hdq : q.totalDegree ≤ C.card + p.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_right (degClause C) _)
    have hdx : ((X l.1) * q).totalDegree ≤ B := by
      apply (totalDegree_mul _ _).trans
      rw [totalDegree_X]
      omega
    have hx := PCDerivable.mulX l.1 hq hdx
    rw [clause_insert l C hl, mul_assoc]
    change PCDerivable F B (pcFactor l * q)
    unfold pcFactor
    split
    · simpa only [add_mul, one_mul] using PCDerivable.add hq hx
    · exact hx

lemma extend_res_parent {V : Type} [DecidableEq V] {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (C R : Clause V) (l : Literal V) (hl : l ∈ C) (hs : C.erase l ⊆ R)
    (hc : PCDerivable F B (clausePoly C)) (hr : R.card + 1 ≤ B) :
    PCDerivable F B (pcFactor l * clausePoly R) := by
  classical
  let A := C.erase l
  have hpol : clausePoly C = pcFactor l * clausePoly A := by
    simpa [A, Finset.insert_erase hl] using clause_insert l (C.erase l) (Finset.notMem_erase l C)
  have hsize : C.card = A.card + 1 := by
    simpa [A, Finset.insert_erase hl] using
      Finset.card_insert_of_notMem (Finset.notMem_erase l C)
  have hd : (R \ A).card + (clausePoly C).totalDegree ≤ B := by
    have hca := Finset.card_sdiff_add_card_eq_card hs
    have hcdeg := degClause C
    change (R \ A).card + A.card = R.card at hca
    omega
  have hstep := pc_multiply_clause (R \ A) (clausePoly C) hc hd
  have hprod : clausePoly (R \ A) * clausePoly A = clausePoly R :=
    Finset.prod_sdiff hs
  rw [hpol, mul_left_comm, hprod] at hstep
  exact hstep

lemma resolution_pc_step {V : Type} [DecidableEq V] {F : Set (MvPolynomial V (ZMod 2))}
    {B : ℕ} (C D R : Clause V) (h : IsResolvent C D R) (hr : R.card + 1 ≤ B)
    (hc : PCDerivable F B (clausePoly C)) (hd : PCDerivable F B (clausePoly D)) :
    PCDerivable F B (clausePoly R) := by
  obtain ⟨v, hvC, hvD, hR⟩ := h
  have hpos := extend_res_parent C R (v,true) hvC
    (hR ▸ Finset.subset_union_left) hc hr
  have hneg := extend_res_parent D R (v,false) hvD
    (hR ▸ Finset.subset_union_right) hd hr
  have hsum := PCDerivable.add hpos hneg
  change PCDerivable F B (((1 + X v) * clausePoly R) + X v * clausePoly R) at hsum
  rw [add_mul, one_mul, add_assoc, CharTwo.add_self_eq_zero (X v * clausePoly R), add_zero] at hsum
  exact hsum

theorem width_to_pc_degree {V : Type} [DecidableEq V] (F : Set (Clause V)) (k : ℕ)
    (π : List (Clause V)) (href : IsRefutation F π) (hw : ∀ C ∈ π, C.card ≤ k) :
    PCRefutable (cnfSystem F) (k + 1) := by
  have hder : ∀ ps : List (Clause V), IsDerivation F ps → (∀ C ∈ ps, C.card ≤ k) →
      ∀ C ∈ ps, PCDerivable (cnfSystem F) (k+1) (clausePoly C) := by
    intro ps hps
    induction hps with
    | nil => simp
    | @ax ps C _ hCF ih =>
      intro hp E hE
      have ht := ih (fun D hD => hp D (List.mem_cons_of_mem _ hD))
      rcases List.mem_cons.mp hE with he | he
      · subst E
        exact .ax (Or.inr ⟨C, hCF, rfl⟩)
          ((degClause C).trans (by have h := hp C List.mem_cons_self; omega))
      · exact ht E he
    | @res ps C D R _ hC hD hres ih =>
      intro hp E hE
      have ht := ih (fun G hG => hp G (List.mem_cons_of_mem _ hG))
      rcases List.mem_cons.mp hE with he | he
      · subst E
        exact resolution_pc_step C D R hres (Nat.add_le_add_right (hp R List.mem_cons_self) 1)
          (ht C hC) (ht D hD)
      · exact ht E he
  have h := hder π href.1 hw ∅ href.2
  simpa [PCRefutable, clausePoly] using h

end PEqualNP.Outside.L_pcx_103

namespace PEqualNP.Outside.L_pcx_103

open PEqualNP.ProofComplexity MvPolynomial

abbrev Sparse := List (List ℕ)

def pcToggle (m : List ℕ) : Sparse → Sparse
  | [] => [m]
  | t :: rest => if m = t then rest else t :: pcToggle m rest

def pcPlus : Sparse → Sparse → Sparse
  | [], q => q
  | m :: rest, q => pcToggle m (pcPlus rest q)

def pcInsert (v : ℕ) : List ℕ → List ℕ
  | [] => [v]
  | a :: rest => if v ≤ a then v :: a :: rest else a :: pcInsert v rest

def pcMul (v : ℕ) (p : Sparse) : Sparse := p.map (pcInsert v)

noncomputable def pcMon {V : Type} (rho : ℕ → V) : List ℕ → MvPolynomial V (ZMod 2)
  | [] => 1
  | i :: rest => X (rho i) * pcMon rho rest

noncomputable def pcValue {V : Type} (rho : ℕ → V) : Sparse → MvPolynomial V (ZMod 2)
  | [] => 0
  | m :: rest => pcMon rho m + pcValue rho rest

lemma pcValue_toggle {V : Type} (rho : ℕ → V) (m : List ℕ) (q : Sparse) :
    pcValue rho (pcToggle m q) = pcMon rho m + pcValue rho q := by
  induction q with
  | nil => simp [pcToggle,pcValue]
  | cons t rest ih =>
    by_cases h : m = t
    · subst t
      simp [pcToggle,pcValue,←add_assoc,CharTwo.add_self_eq_zero]
    · simp [pcToggle,pcValue,h,ih,add_left_comm]

lemma pcValue_plus {V : Type} (rho : ℕ → V) (p q : Sparse) :
    pcValue rho (pcPlus p q) = pcValue rho p + pcValue rho q := by
  induction p with
  | nil => simp [pcPlus,pcValue]
  | cons m rest ih => simp [pcPlus,pcValue,pcValue_toggle,ih,add_assoc]

lemma pcMon_insert {V : Type} (rho : ℕ → V) (v : ℕ) (t : List ℕ) :
    pcMon rho (pcInsert v t) = X (rho v) * pcMon rho t := by
  induction t with
  | nil => simp [pcInsert,pcMon]
  | cons a rest ih =>
    by_cases h : v ≤ a <;> simp [pcInsert,pcMon,h,ih,mul_left_comm]

lemma pcValue_mul {V : Type} (rho : ℕ → V) (v : ℕ) (p : Sparse) :
    pcValue rho (pcMul v p) = X (rho v) * pcValue rho p := by
  induction p with
  | nil => simp [pcMul,pcValue]
  | cons m rest ih =>
    change pcMon rho (pcInsert v m) + pcValue rho (pcMul v rest) =
      X (rho v) * (pcMon rho m + pcValue rho rest)
    rw [pcMon_insert,ih,mul_add]

lemma pcMon_degree {V : Type} (rho : ℕ → V) (m : List ℕ) :
    (pcMon rho m).totalDegree ≤ m.length := by
  induction m with
  | nil => simp [pcMon]
  | cons i t ih =>
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_X]
    simp
    omega

lemma pcValue_degree {V : Type} (rho : ℕ → V) (p : Sparse) (d : ℕ)
    (h : p.all (fun m => decide (m.length ≤ d)) = true) :
    (pcValue rho p).totalDegree ≤ d := by
  induction p with
  | nil => simp [pcValue]
  | cons m t ih =>
    have hc := List.all_eq_true.mp h m List.mem_cons_self
    have ht : t.all (fun m => decide (m.length ≤ d)) = true :=
      List.all_eq_true.mpr (fun m hm => List.all_eq_true.mp h m (List.mem_cons_of_mem _ hm))
    exact (totalDegree_add _ _).trans (max_le ((pcMon_degree rho m).trans (of_decide_eq_true hc)) (ih ht))

def pcSource : List (ℕ × Bool) → Sparse
  | [] => [[]]
  | (v,b) :: rest =>
    let p := pcSource rest
    if b then pcPlus p (pcMul v p) else pcMul v p

def pcDecode {V : Type} (rho : ℕ → V) (l : ℕ × Bool) : V × Bool := (rho l.1,l.2)

lemma pcValue_source {V : Type} [DecidableEq V] (rho : ℕ → V) (ls : List (ℕ × Bool))
    (nd : (ls.map (pcDecode rho)).Nodup) :
    pcValue rho (pcSource ls) = clausePoly (ls.map (pcDecode rho)).toFinset := by
  induction ls with
  | nil => simp [pcSource,pcValue,pcMon,clausePoly]
  | cons l ls ih =>
    obtain ⟨v,b⟩ := l
    have hn := List.nodup_cons.mp nd
    have hnot : pcDecode rho (v,b) ∉ (ls.map (pcDecode rho)).toFinset := by simpa using hn.1
    have hr := ih hn.2
    simp only [List.map_cons, List.toFinset_cons]
    change _ = ∏ l ∈ insert (pcDecode rho (v,b)) (ls.map (pcDecode rho)).toFinset,
       (if l.2 = true then 1 + X l.1 else X l.1 : MvPolynomial V (ZMod 2))
    rw [Finset.prod_insert hnot]
    change _ = (if b = true then 1 + X (rho v) else X (rho v) : MvPolynomial V (ZMod 2)) * clausePoly (ls.map (pcDecode rho)).toFinset
    cases b <;> simp [pcSource,pcValue_plus,pcValue_mul,hr,add_mul]

end PEqualNP.Outside.L_pcx_103

namespace PEqualNP.Outside.L_pcx_103

open PEqualNP.ProofComplexity MvPolynomial

abbrev PCStep := Bool × ℕ × ℕ × Sparse

def pcCheck (B : ℕ) (acc : List Sparse) : List PCStep → Bool
  | [] => decide (([[]] : Sparse) ∈ acc)
  | (mul,i,j,next) :: rest =>
    match acc[i]? with
    | none => false
    | some p =>
      if mul then
        if next = pcMul j p ∧ next.all (fun m => decide (m.length ≤ B)) = true then
          pcCheck B (next :: acc) rest
        else false
      else
        match acc[j]? with
        | none => false
        | some q =>
          if next = pcPlus p q then pcCheck B (next :: acc) rest else false

lemma pcCheck_sound {V : Type} (F : Set (MvPolynomial V (ZMod 2))) (rho : ℕ → V)
    (B : ℕ) (acc : List Sparse) (steps : List PCStep)
    (derived : ∀ p ∈ acc, PCDerivable F B (pcValue rho p))
    (checks : pcCheck B acc steps = true) : PCRefutable F B := by
  induction steps generalizing acc with
  | nil =>
    have h := derived [[]] (of_decide_eq_true checks)
    simpa [PCRefutable,pcValue,pcMon] using h
  | cons s rest ih =>
    obtain ⟨mul,i,j,next⟩ := s
    cases hi : acc[i]? with
    | none => simp [pcCheck,hi] at checks
    | some p =>
      have hp := derived p (List.mem_of_getElem? hi)
      have extend (hn : PCDerivable F B (pcValue rho next)) (hc : pcCheck B (next::acc) rest = true) :
          PCRefutable F B := by
        apply ih (next::acc) _ hc
        intro t ht
        rcases List.mem_cons.mp ht with rfl | h
        · exact hn
        · exact derived _ h
      cases mul with
      | false =>
        cases hj : acc[j]? with
        | none => simp [pcCheck,hi,hj] at checks
        | some q =>
          by_cases h : next = pcPlus p q
          · apply extend _ (by simpa only [pcCheck,hi,hj,Bool.false_eq_true,ite_false,ite_eq_left h] using checks)
            rw [h,pcValue_plus]
            exact .add hp (derived q (List.mem_of_getElem? hj))
          · simp [pcCheck,hi,hj,h] at checks
      | true =>
        by_cases h : next = pcMul j p ∧ next.all (fun m => decide (m.length ≤ B)) = true
        · apply extend _ (by simpa only [pcCheck,hi,ite_true,ite_eq_left h] using checks)
          have hd := pcValue_degree rho next B h.2
          rw [h.1,pcValue_mul] at hd ⊢
          exact .mulX (rho j) hp hd
        · simp only [pcCheck,hi,ite_true,ite_eq_right h,Bool.false_eq_true] at checks

lemma pcInitial {V : Type} [DecidableEq V] (F : Set (Clause V)) (rho : ℕ → V) (B : ℕ)
    (ls : List (ℕ × Bool)) (hNodup : (ls.map (pcDecode rho)).Nodup)
    (hMem : (ls.map (pcDecode rho)).toFinset ∈ F)
    (hBound : (pcSource ls).all (fun m => decide (m.length ≤ B)) = true) :
    PCDerivable (cnfSystem F) B (pcValue rho (pcSource ls)) := by
  have hv := pcValue_source rho ls hNodup
  exact .ax (Or.inr ⟨_,hMem,hv⟩) (pcValue_degree rho _ B hBound)

end PEqualNP.Outside.L_pcx_103

namespace PEqualNP.Outside.L_pcx_103

open PEqualNP.ProofComplexity MvPolynomial

def pcLabel (n k t : ℕ) : CV n :=
  if h : t < n then Sum.inl ⟨t,h⟩ else Sum.inr ((t-n)/k,(t-n)%k)

abbrev PCSourceRow (n : ℕ) := (ℕ × Fin n × Fin n) × List (ℕ × Bool)

def pcGood {n : ℕ} (k B : ℕ) (edges : List (Fin n × Fin n)) (r : PCSourceRow n) : Bool :=
  decide (sourceOK k edges r.1 = true ∧
    (r.2.map (pcDecode (pcLabel n k))).toFinset = sourceClause k r.1 ∧
    (r.2.map (pcDecode (pcLabel n k))).Nodup ∧
    (pcSource r.2).all (fun m => decide (m.length ≤ B)) = true)

def pcBase {n : ℕ} (rows : List (PCSourceRow n)) : List Sparse :=
  rows.reverse.map (fun r => pcSource r.2)

lemma pcFromGround {n k B : ℕ} (edges : List (Fin n × Fin n)) (rows : List (PCSourceRow n))
    (steps : List PCStep) (hg : rows.all (pcGood k B edges) = true)
    (hc : pcCheck B (pcBase rows) steps = true) :
    PCRefutable (cnfSystem (counter_formula n k edges)) B := by
  apply pcCheck_sound _ (pcLabel n k) B (pcBase rows) steps _ hc
  intro p hp
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hp
  have h := of_decide_eq_true (List.all_eq_true.mp hg row (List.mem_reverse.mp hr))
  apply pcInitial _ _ _ _ h.2.2.1 _ h.2.2.2
  rw [h.2.1]
  exact source_member edges _ h.1

end PEqualNP.Outside.L_pcx_103

namespace PEqualNP.Outside.L_pcx_103

open PEqualNP.ProofComplexity MvPolynomial

def pcRows10Block0 : List (PCSourceRow 10) := [
    ((0,0,1),[(0,true),(1,true)]),
    ((0,1,2),[(1,true),(2,true)]),
    ((0,2,3),[(2,true),(3,true)]),
    ((0,3,4),[(3,true),(4,true)]),
    ((0,4,0),[(4,true),(0,true)]),
    ((0,0,5),[(0,true),(5,true)]),
    ((0,1,6),[(1,true),(6,true)]),
    ((0,2,7),[(2,true),(7,true)]),
    ((0,3,8),[(3,true),(8,true)]),
    ((0,4,9),[(4,true),(9,true)]),
    ((0,5,7),[(5,true),(7,true)]),
    ((0,7,9),[(7,true),(9,true)]),
    ((0,9,6),[(9,true),(6,true)]),
    ((0,6,8),[(6,true),(8,true)]),
    ((0,8,5),[(8,true),(5,true)]),
    ((1,0,0),[(0,false),(10,true)]),
    ((1,1,0),[(1,false),(15,true)]),
    ((1,2,0),[(2,false),(20,true)]),
    ((1,3,0),[(3,false),(25,true)]),
    ((2,1,0),[(10,false),(15,true)]),
    ((2,2,0),[(15,false),(20,true)]),
    ((2,2,1),[(16,false),(21,true)]),
    ((2,3,0),[(20,false),(25,true)]),
    ((2,3,1),[(21,false),(26,true)]),
    ((2,4,1),[(26,false),(31,true)]),
    ((2,4,2),[(27,false),(32,true)]),
    ((2,5,2),[(32,false),(37,true)]),
    ((2,6,2),[(37,false),(42,true)]),
    ((2,6,3),[(38,false),(43,true)]),
    ((2,7,3),[(43,false),(48,true)]),
    ((2,7,4),[(44,false),(49,true)]),
    ((2,8,4),[(49,false),(54,true)]),
    ((3,1,0),[(1,false),(10,false),(16,true)]),
    ((3,2,0),[(2,false),(15,false),(21,true)]),
    ((3,3,0),[(3,false),(20,false),(26,true)]),
    ((3,3,1),[(3,false),(21,false),(27,true)]),
    ((3,4,0),[(4,false),(25,false),(31,true)]),
    ((3,4,1),[(4,false),(26,false),(32,true)]),
    ((3,5,1),[(5,false),(31,false),(37,true)]),
    ((3,5,2),[(5,false),(32,false),(38,true)]),
    ((3,6,2),[(6,false),(37,false),(43,true)]),
    ((3,6,3),[(6,false),(38,false),(44,true)]),
    ((3,7,2),[(7,false),(42,false),(48,true)]),
    ((3,7,3),[(7,false),(43,false),(49,true)]),
    ((3,8,3),[(8,false),(48,false),(54,true)]),
    ((4,7,0),[(7,false),(44,false)]),
    ((4,8,0),[(8,false),(49,false)]),
    ((4,9,0),[(9,false),(54,false)])]

def pcRows10 : List (PCSourceRow 10) := pcRows10Block0

def pcSteps10Block0 : List (PCStep) := [
    (true,47,4,[[0,1,4],[0,4],[4],[1,4]]),
    (true,48,5,[[0,1,5],[0,5],[5],[1,5]]),
    (true,49,10,[[0,1,10],[0,10],[10],[1,10]]),
    (true,50,15,[[0,1,15],[0,15],[15],[1,15]]),
    (true,51,16,[[0,1,16],[0,16],[16],[1,16]]),
    (true,52,21,[[0,1,21],[0,21],[21],[1,21]]),
    (true,53,27,[[0,1,27],[0,27],[27],[1,27]]),
    (true,54,32,[[0,1,32],[0,32],[32],[1,32]]),
    (true,55,37,[[0,1,37],[0,37],[37],[1,37]]),
    (true,56,42,[[0,1,42],[0,42],[42],[1,42]]),
    (true,56,15,[[1,2,15],[1,15],[15],[2,15]]),
    (true,57,20,[[1,2,20],[1,20],[20],[2,20]]),
    (true,58,21,[[1,2,21],[1,21],[21],[2,21]]),
    (true,59,26,[[1,2,26],[1,26],[26],[2,26]]),
    (true,60,31,[[1,2,31],[1,31],[31],[2,31]]),
    (true,60,5,[[2,3,5],[2,5],[5],[3,5]]),
    (true,61,7,[[2,3,7],[2,7],[7],[3,7]]),
    (true,62,15,[[2,3,15],[2,15],[15],[3,15]]),
    (true,63,20,[[2,3,20],[2,20],[20],[3,20]]),
    (true,64,21,[[2,3,21],[2,21],[21],[3,21]]),
    (true,65,25,[[2,3,25],[2,25],[25],[3,25]]),
    (true,66,26,[[2,3,26],[2,26],[26],[3,26]]),
    (true,67,31,[[2,3,31],[2,31],[31],[3,31]]),
    (true,67,20,[[3,4,20],[3,20],[20],[4,20]]),
    (true,68,21,[[3,4,21],[3,21],[21],[4,21]]),
    (true,69,25,[[3,4,25],[3,25],[25],[4,25]]),
    (true,70,26,[[3,4,26],[3,26],[26],[4,26]]),
    (true,71,27,[[3,4,27],[3,27],[27],[4,27]]),
    (true,72,31,[[3,4,31],[3,31],[31],[4,31]]),
    (true,73,32,[[3,4,32],[3,32],[32],[4,32]]),
    (true,74,49,[[3,4,49],[3,49],[49],[4,49]]),
    (true,74,10,[[0,4,10],[4,10],[10],[0,10]]),
    (true,75,15,[[0,4,15],[4,15],[15],[0,15]]),
    (true,76,21,[[0,4,21],[4,21],[21],[0,21]]),
    (true,77,27,[[0,4,27],[4,27],[27],[0,27]]),
    (true,77,3,[[0,3,5],[0,3],[3],[3,5]]),
    (true,78,10,[[0,5,10],[0,10],[10],[5,10]]),
    (true,79,15,[[0,5,15],[0,15],[15],[5,15]]),
    (true,80,21,[[0,5,21],[0,21],[21],[5,21]]),
    (true,81,32,[[0,5,32],[0,32],[32],[5,32]]),
    (true,81,7,[[1,6,7],[1,7],[7],[6,7]]),
    (true,82,15,[[1,6,15],[1,15],[15],[6,15]]),
    (true,82,15,[[2,7,15],[2,15],[15],[7,15]]),
    (true,83,20,[[2,7,20],[2,20],[20],[7,20]]),
    (true,84,21,[[2,7,21],[2,21],[21],[7,21]]),
    (true,85,26,[[2,7,26],[2,26],[26],[7,26]]),
    (true,86,31,[[2,7,31],[2,31],[31],[7,31]]),
    (true,86,20,[[3,8,20],[3,20],[20],[8,20]]),
    (true,87,25,[[3,8,25],[3,25],[25],[8,25]]),
    (true,88,26,[[3,8,26],[3,26],[26],[8,26]]),
    (true,89,49,[[3,8,49],[3,49],[49],[8,49]]),
    (true,89,26,[[4,9,26],[4,26],[26],[9,26]]),
    (true,90,32,[[4,9,32],[4,32],[32],[9,32]]),
    (true,91,54,[[4,9,54],[4,54],[54],[9,54]]),
    (true,91,31,[[5,7,31],[5,31],[31],[7,31]]),
    (true,92,37,[[5,7,37],[5,37],[37],[7,37]]),
    (true,93,43,[[5,7,43],[5,43],[43],[7,43]]),
    (true,93,43,[[7,9,43],[7,43],[43],[9,43]]),
    (true,94,44,[[7,9,44],[7,44],[44],[9,44]]),
    (true,95,54,[[7,9,54],[7,54],[54],[9,54]]),
    (true,95,37,[[6,9,37],[9,37],[37],[6,37]]),
    (true,96,43,[[6,9,43],[9,43],[43],[6,43]]),
    (true,97,54,[[6,9,54],[9,54],[54],[6,54]]),
    (true,97,38,[[6,8,38],[6,38],[38],[8,38]]),
    (true,98,49,[[6,8,49],[6,49],[49],[8,49]]),
    (true,98,49,[[5,8,49],[8,49],[49],[5,49]]),
    (true,98,1,[[0,1,10],[0,1]]),
    (false,0,64,[[0,10],[10],[1,10],[0,1]]),
    (true,100,3,[[0,3,10],[0,3]]),
    (true,101,4,[[0,4,10],[0,4]]),
    (false,0,38,[[4,10],[10],[0,10],[0,4]]),
    (true,103,5,[[0,5,10],[0,5]]),
    (false,0,35,[[0,10],[10],[5,10],[0,5]]),
    (true,105,15,[[0,10,15],[0,15]]),
    (true,106,16,[[0,10,16],[0,16]]),
    (true,107,21,[[0,10,21],[0,21]]),
    (true,108,32,[[0,10,32],[0,32]]),
    (true,109,37,[[0,10,37],[0,37]]),
    (true,110,42,[[0,10,42],[0,42]]),
    (true,110,0,[[0,1,15],[0,1]]),
    (false,0,76,[[0,15],[15],[1,15],[0,1]]),
    (false,0,112,[[1],[0,1],[15],[0,15]]),
    (true,113,2,[[1,2,15],[1,2]]),
    (false,0,72,[[1,15],[15],[2,15],[1,2]]),
    (true,115,4,[[1,4,15],[1,4]]),
    (true,116,5,[[1,5,15],[1,5]]),
    (true,117,6,[[1,6,15],[1,6]]),
    (false,0,45,[[1,15],[15],[6,15],[1,6]]),
    (true,119,7,[[1,7,15],[1,7]]),
    (true,120,20,[[1,15,20],[1,20]]),
    (true,121,21,[[1,15,21],[1,21]]),
    (true,122,26,[[1,15,26],[1,26]]),
    (true,123,27,[[1,15,27],[1,27]]),
    (true,124,31,[[1,15,31],[1,31]]),
    (true,125,32,[[1,15,32],[1,32]]),
    (true,126,37,[[1,15,37],[1,37]]),
    (true,127,42,[[1,15,42],[1,42]]),
    (true,127,1,[[1,2,20],[1,2]]),
    (false,0,86,[[1,20],[20],[2,20],[1,2]]),
    (false,0,129,[[2],[1,2],[20],[1,20]])]

def pcSteps10Block1 : List (PCStep) := [
    (true,130,3,[[2,3,20],[2,3]]),
    (false,0,82,[[2,20],[20],[3,20],[2,3]]),
    (true,132,5,[[2,5,20],[2,5]]),
    (true,133,7,[[2,7,20],[2,7]]),
    (false,0,60,[[2,20],[20],[7,20],[2,7]]),
    (true,135,25,[[2,20,25],[2,25]]),
    (true,136,26,[[2,20,26],[2,26]]),
    (true,137,31,[[2,20,31],[2,31]]),
    (true,137,2,[[2,3,25],[2,3]]),
    (false,0,88,[[2,25],[25],[3,25],[2,3]]),
    (false,0,139,[[3],[2,3],[25],[2,25]]),
    (true,140,4,[[3,4,25],[3,4]]),
    (false,0,86,[[3,25],[25],[4,25],[3,4]]),
    (true,142,8,[[3,8,25],[3,8]]),
    (false,0,65,[[3,25],[25],[8,25],[3,8]]),
    (true,144,31,[[3,25,31],[3,31]]),
    (true,145,49,[[3,25,49],[3,49]]),
    (true,145,0,[[0,10,15],[0,10]]),
    (false,0,44,[[0,15],[0,10]]),
    (false,0,37,[[1],[0,1],[15],[0,10]]),
    (false,0,152,[[0],[15],[0,1],[1]]),
    (false,0,168,[[],[15]]),
    (true,150,4,[[4,10,15],[4,10]]),
    (true,151,5,[[5,10,15],[5,10]]),
    (true,151,1,[[1,15,20],[1,15]]),
    (false,0,35,[[1,20],[1,15]]),
    (false,0,26,[[2],[1,2],[20],[1,15]]),
    (false,0,158,[[1],[20],[1,2],[2]]),
    (false,0,174,[[],[20]]),
    (true,155,1,[[1,16,21],[1,16]]),
    (true,156,10,[[10,16,21],[10,16]]),
    (true,156,2,[[2,20,25],[2,20]]),
    (false,0,26,[[2,25],[2,20]]),
    (false,0,22,[[3],[2,3],[25],[2,20]]),
    (false,0,164,[[2],[25],[2,3],[3]]),
    (false,0,180,[[],[25]]),
    (true,160,2,[[2,21,26],[2,21]]),
    (true,161,4,[[4,21,26],[4,21]]),
    (true,162,15,[[15,21,26],[15,21]]),
    (true,163,31,[[21,26,31],[21,31]]),
    (true,163,3,[[3,26,31],[3,26]]),
    (true,164,20,[[20,26,31],[20,26]]),
    (true,165,21,[[21,26,31],[21,26]]),
    (false,0,3,[[21,31],[21,26]]),
    (true,166,3,[[3,27,32],[3,27]]),
    (true,167,4,[[4,27,32],[4,27]]),
    (true,168,15,[[15,27,32],[15,27]]),
    (true,169,21,[[21,27,32],[21,27]]),
    (true,170,37,[[27,32,37],[27,37]]),
    (true,171,42,[[27,32,42],[27,42]]),
    (true,171,4,[[4,32,37],[4,32]]),
    (true,172,9,[[9,32,37],[9,32]]),
    (true,173,27,[[27,32,37],[27,32]]),
    (false,0,4,[[27,37],[27,32]]),
    (true,175,42,[[32,37,42],[32,42]]),
    (true,175,5,[[5,37,42],[5,37]]),
    (true,176,7,[[7,37,42],[7,37]]),
    (true,177,27,[[27,37,42],[27,37]]),
    (true,178,32,[[32,37,42],[32,37]]),
    (false,0,4,[[32,42],[32,37]]),
    (true,179,5,[[5,38,43],[5,38]]),
    (true,180,7,[[7,38,43],[7,38]]),
    (true,181,48,[[38,43,48],[38,48]]),
    (true,182,49,[[38,43,49],[38,49]]),
    (true,182,38,[[38,43,48],[38,43]]),
    (false,0,2,[[38,48],[38,43]]),
    (true,183,6,[[6,44,49],[6,44]]),
    (true,184,9,[[9,44,49],[9,44]]),
    (true,185,54,[[44,49,54],[44,54]]),
    (true,185,4,[[4,49,54],[4,49]]),
    (true,186,7,[[7,49,54],[7,49]]),
    (true,187,9,[[9,49,54],[9,49]]),
    (true,188,43,[[43,49,54],[43,49]]),
    (true,189,44,[[44,49,54],[44,49]]),
    (false,0,5,[[44,54],[44,49]]),
    (true,177,9,[[7,9,44]]),
    (false,0,117,[[7,44],[44],[9,44]]),
    (true,178,5,[[5,8,49]]),
    (false,0,112,[[8,49],[49],[5,49]]),
    (false,0,180,[[5,49],[49]]),
    (true,181,6,[[6,8,49]]),
    (false,0,116,[[6,49],[49],[8,49]]),
    (false,0,183,[[49],[6,49]]),
    (true,184,25,[[8,25,49]]),
    (true,185,31,[[8,31,49]]),
    (true,185,4,[[4,9,54]]),
    (false,0,132,[[4,54],[54],[9,54]]),
    (false,0,187,[[54],[4,54]]),
    (true,188,6,[[6,9,54]]),
    (false,0,126,[[9,54],[54],[6,54]]),
    (false,0,190,[[6,54],[54]]),
    (true,191,7,[[7,9,54]]),
    (false,0,132,[[7,54],[54],[9,54]]),
    (false,0,193,[[54],[7,54]]),
    (true,194,44,[[9,44,54]]),
    (true,195,49,[[9,49,54]]),
    (false,0,24,[[9,49]]),
    (true,129,4,[[0,4,10],[4,10],[1,4,10],[0,1,4]]),
    (true,130,5,[[0,5,10],[5,10],[1,5,10],[0,1,5]]),
    (true,131,16,[[0,10,16],[10,16],[1,10,16],[0,1,16]])]

def pcSteps10Block2 : List (PCStep) := [
    (false,0,215,[[1,10],[0,1,16],[10,16],[0,10,16]]),
    (false,0,126,[[0,16],[10,16],[0,1,16],[1,10]]),
    (false,0,197,[[16],[1,16],[1,10],[10,16]]),
    (true,135,21,[[0,10,21],[10,21],[1,10,21],[0,1,21]]),
    (true,136,27,[[0,10,27],[10,27],[1,10,27],[0,1,27]]),
    (true,137,32,[[0,10,32],[10,32],[1,10,32],[0,1,32]]),
    (true,138,37,[[0,10,37],[10,37],[1,10,37],[0,1,37]]),
    (true,139,42,[[0,10,42],[10,42],[1,10,42],[0,1,42]]),
    (true,137,15,[[4,10,15],[10,15],[0,10,15],[0,4,15]]),
    (false,0,86,[[4,10],[0,4,15],[0,10,15],[10,15]]),
    (false,0,136,[[0,15],[10,15],[0,4,15],[4,10]]),
    (false,0,178,[[4,15],[15],[4,10],[10,15]]),
    (false,0,240,[[10],[4,10],[15],[4,15]]),
    (true,142,16,[[4,10,16],[10,16],[0,10,16],[0,4,16]]),
    (true,143,21,[[4,10,21],[10,21],[0,10,21],[0,4,21]]),
    (true,144,32,[[4,10,32],[10,32],[0,10,32],[0,4,32]]),
    (true,145,37,[[4,10,37],[10,37],[0,10,37],[0,4,37]]),
    (true,146,42,[[4,10,42],[10,42],[0,10,42],[0,4,42]]),
    (true,145,3,[[0,3,10],[3,10],[3,5,10],[0,3,5]]),
    (true,146,15,[[0,10,15],[10,15],[5,10,15],[0,5,15]]),
    (false,0,96,[[5,10],[0,5,15],[10,15],[0,10,15]]),
    (false,0,147,[[0,15],[10,15],[0,5,15],[5,10]]),
    (false,0,184,[[15],[5,15],[5,10],[10,15]]),
    (false,0,251,[[10],[5,10],[5,15],[15]]),
    (true,151,16,[[0,10,16],[10,16],[5,10,16],[0,5,16]]),
    (true,152,21,[[0,10,21],[10,21],[5,10,21],[0,5,21]]),
    (true,142,21,[[1,15,21],[15,21],[2,15,21],[1,2,21]]),
    (false,0,241,[[2,15],[1,2,21],[15,21],[1,15,21]]),
    (false,0,137,[[1,21],[15,21],[1,2,21],[2,15]]),
    (false,0,216,[[21],[2,21],[2,15],[15,21]]),
    (true,146,26,[[1,15,26],[15,26],[2,15,26],[1,2,26]]),
    (true,147,31,[[1,15,31],[15,31],[2,15,31],[1,2,31]]),
    (true,144,7,[[1,7,15],[7,15],[6,7,15],[1,6,7]]),
    (true,131,5,[[2,5,20],[5,20],[3,5,20],[2,3,5]]),
    (true,132,7,[[2,7,20],[7,20],[3,7,20],[2,3,7]]),
    (true,133,26,[[2,20,26],[20,26],[3,20,26],[2,3,26]]),
    (false,0,249,[[3,20],[2,3,26],[20,26],[2,20,26]]),
    (false,0,130,[[2,26],[20,26],[2,3,26],[3,20]]),
    (false,0,216,[[26],[3,26],[3,20],[20,26]]),
    (true,137,31,[[2,20,31],[20,31],[3,20,31],[2,3,31]]),
    (true,135,26,[[2,20,26],[20,26],[7,20,26],[2,7,26]]),
    (true,128,31,[[3,25,31],[25,31],[4,25,31],[3,4,31]]),
    (false,0,253,[[4,25],[3,4,31],[25,31],[3,25,31]]),
    (false,0,127,[[3,31],[25,31],[3,4,31],[4,25]]),
    (false,0,215,[[31],[4,31],[4,25],[25,31]]),
    (true,132,49,[[3,25,49],[25,49],[4,25,49],[3,4,49]]),
    (true,131,49,[[3,25,49],[25,49],[8,25,49],[3,8,49]]),
    (false,0,63,[[3,8,49],[25,49],[3,25,49]]),
    (false,0,131,[[3,49],[25,49],[3,8,49]]),
    (false,0,198,[[49],[8,49],[25,49]]),
    (true,128,3,[[3],[3,15]]),
    (true,129,7,[[7],[7,15]]),
    (true,130,9,[[9],[9,15]]),
    (true,131,21,[[21],[15,21]]),
    (false,0,24,[[2,21],[2,15]]),
    (true,133,26,[[26],[15,26]]),
    (true,134,31,[[31],[15,31]]),
    (true,135,32,[[32],[15,32]]),
    (true,136,37,[[37],[15,37]]),
    (true,137,38,[[38],[15,38]]),
    (true,138,42,[[42],[15,42]]),
    (true,139,48,[[48],[15,48]]),
    (true,140,49,[[49],[15,49]]),
    (true,141,54,[[54],[15,54]]),
    (true,135,4,[[4],[4,20]]),
    (true,136,5,[[5],[5,20]]),
    (true,137,8,[[8],[8,20]]),
    (true,138,9,[[9],[9,20]]),
    (true,139,26,[[26],[20,26]]),
    (false,0,30,[[3,26],[3,20]]),
    (true,141,31,[[31],[20,31]]),
    (true,142,37,[[37],[20,37]]),
    (true,143,49,[[49],[20,49]]),
    (true,144,54,[[54],[20,54]]),
    (true,138,5,[[5],[5,25]]),
    (true,139,31,[[31],[25,31]]),
    (false,0,31,[[4,31],[4,25]]),
    (true,133,2,[[2,21,31],[2,21,26]]),
    (true,134,15,[[15,21,31],[15,21,26]]),
    (true,125,4,[[4,27,37],[4,27,32]]),
    (true,126,42,[[27,37,42],[27,32,42]]),
    (false,0,123,[[27,37],[27,32,42]]),
    (false,0,132,[[27,42],[27,37]]),
    (true,123,4,[[4,32,42],[4,32,37]]),
    (true,109,9,[[9,44,54],[9,44,49]]),
    (false,0,90,[[9,44,49]]),
    (false,0,118,[[9,44]]),
    (false,0,110,[[7,44],[44]]),
    (false,0,290,[[44]]),
    (true,109,31,[[5,31,49],[31,49]]),
    (true,110,37,[[5,37,49],[37,49]]),
    (true,111,43,[[5,43,49],[43,49]]),
    (true,109,37,[[37,49],[6,37,49]]),
    (true,110,38,[[38,49],[6,38,49]]),
    (true,111,43,[[43,49],[6,43,49]]),
    (true,112,44,[[44,49],[6,44,49]]),
    (false,0,129,[[6,44],[44,49]]),
    (false,0,314,[[44],[6,44]]),
    (true,110,26,[[26,54],[4,26,54]]),
    (true,111,32,[[32,54],[4,32,54]])]

def pcSteps10Block3 : List (PCStep) := [
    (true,112,37,[[37,54],[4,37,54]]),
    (true,113,42,[[42,54],[4,42,54]]),
    (true,114,49,[[49,54],[4,49,54]]),
    (false,0,133,[[4,49],[49,54]]),
    (false,0,320,[[49],[4,49]]),
    (true,114,37,[[6,37,54],[37,54]]),
    (true,115,43,[[6,43,54],[43,54]]),
    (true,113,42,[[42,54],[7,42,54]]),
    (true,114,43,[[43,54],[7,43,54]]),
    (true,115,48,[[48,54],[7,48,54]]),
    (true,116,49,[[49,54],[7,49,54]]),
    (false,0,140,[[7,49],[49,54]]),
    (false,0,328,[[49],[7,49]]),
    (true,116,43,[[9,43,49]]),
    (true,111,4,[[4,16],[1,4,16],[1,4,10],[4,10,16]]),
    (false,0,101,[[10,16],[0,10,16],[0,4,16],[1,4,10],[1,4,16],[4,16]]),
    (true,113,5,[[5,16],[1,5,16],[1,5,10],[5,10,16]]),
    (false,0,92,[[0,10,16],[10,16],[0,5,16],[1,5,10],[1,5,16],[5,16]]),
    (true,115,21,[[16,21],[1,16,21],[1,10,21],[10,16,21]]),
    (false,0,188,[[10,16],[1,10,21],[1,16,21],[16,21]]),
    (false,0,190,[[1,16],[16,21],[1,10,21],[10,16]]),
    (false,0,117,[[0,10,21],[10,21],[0,1,21],[10,16],[16,21],[1,16]]),
    (false,0,246,[[0,21],[1,16],[16,21],[10,16],[0,1,21],[10,21]]),
    (false,0,317,[[21],[1,21],[10,21],[10,16],[16,21],[1,16]]),
    (false,0,350,[[16],[1,16],[10,16],[10,21],[1,21],[21]]),
    (true,112,32,[[10,32],[4,10,32],[15,32],[4,15,32]]),
    (true,113,37,[[10,37],[4,10,37],[15,37],[4,15,37]]),
    (true,114,42,[[10,42],[4,10,42],[15,42],[4,15,42]]),
    (true,104,3,[[3,10],[3,5,10],[3,5,15],[3,15]]),
    (true,105,21,[[10,21],[5,10,21],[5,15,21],[15,21]]),
    (true,100,1,[[1,21],[1,2,21],[1,2,15],[1,15,21]]),
    (false,0,240,[[1,2,15],[1,2,21]]),
    (false,0,319,[[1,21],[21],[2,21],[1,2,15]]),
    (false,0,322,[[1,15],[15],[2,15],[2,21],[21],[1,21]]),
    (false,0,79,[[1,21],[21],[15],[1,15]]),
    (true,105,3,[[3,21],[2,3,21],[2,3,15],[3,15,21]]),
    (true,106,5,[[5,21],[2,5,21],[2,5,15],[5,15,21]]),
    (false,0,7,[[10,21],[5,10,21],[15,21],[2,5,15],[2,5,21],[5,21]]),
    (false,0,112,[[0,10,21],[0,5,21],[5,21],[2,5,21],[2,5,15],[15,21]]),
    (true,109,7,[[7,21],[2,7,21],[2,7,15],[7,15,21]]),
    (true,110,26,[[21,26],[2,21,26],[2,15,26],[15,21,26]]),
    (false,0,202,[[15,21],[2,15,26],[2,21,26],[21,26]]),
    (false,0,205,[[2,21],[21,26],[2,15,26],[15,21]]),
    (false,0,112,[[1,15,26],[15,26],[1,2,26],[15,21],[21,26],[2,21]]),
    (false,0,252,[[1,26],[2,21],[21,26],[15,21],[1,2,26],[15,26]]),
    (false,0,331,[[26],[2,26],[15,26],[15,21],[21,26],[2,21]]),
    (false,0,370,[[21],[2,21],[15,21],[15,26],[2,26],[26]]),
    (false,0,91,[[2,26],[15,21],[2,21],[21]]),
    (false,0,118,[[2,15],[2,26]]),
    (true,119,31,[[21,31],[2,21,31],[2,15,31],[15,21,31]]),
    (false,0,71,[[15,21,26],[2,15,31],[2,21,31],[21,31]]),
    (false,0,212,[[15,21],[21,31],[2,21,31],[2,15,31]]),
    (false,0,74,[[2,21,26],[2,15,31],[21,31],[15,21]]),
    (false,0,216,[[2,21],[15,21],[21,31],[2,15,31]]),
    (false,0,122,[[1,15,31],[15,31],[1,2,31],[21,31],[15,21],[2,21]]),
    (false,0,261,[[1,31],[2,21],[15,21],[21,31],[1,2,31],[15,31]]),
    (false,0,341,[[31],[2,31],[15,31],[21,31],[15,21],[2,21]]),
    (false,0,213,[[21,26],[2,21],[15,21],[15,31],[2,31],[31]]),
    (false,0,382,[[21],[31],[2,31],[15,31],[15,21],[2,21]]),
    (false,0,102,[[2,21],[15,21],[2,31],[21]]),
    (false,0,130,[[2,15],[2,31]]),
    (true,122,2,[[2,26],[2,3,26],[2,3,20],[2,20,26]]),
    (false,0,255,[[2,3,20],[2,3,26]]),
    (false,0,341,[[2,26],[26],[3,26],[2,3,20]]),
    (false,0,345,[[2,20],[20],[3,20],[3,26],[26],[2,26]]),
    (false,0,95,[[2,26],[26],[20],[2,20]]),
    (false,0,17,[[2,15],[2,20],[20],[26]]),
    (false,0,397,[[2],[26],[20],[2,15]]),
    (false,0,284,[[1,15],[15],[1,2],[20],[26],[2]]),
    (false,0,400,[[1],[2],[26],[20],[1,2],[15]]),
    (false,0,416,[[],[15],[20],[26]]),
    (true,132,4,[[4,26],[3,4,26],[3,4,20],[4,20,26]]),
    (true,133,5,[[5,26],[3,5,26],[3,5,20],[5,20,26]]),
    (true,134,7,[[7,26],[3,7,26],[3,7,20],[7,20,26]]),
    (false,0,133,[[2,20,26],[20,26],[2,7,26],[3,7,20],[3,7,26],[7,26]]),
    (true,136,8,[[8,26],[3,8,26],[3,8,20],[8,20,26]]),
    (true,137,31,[[26,31],[3,26,31],[3,20,31],[20,26,31]]),
    (false,0,235,[[20,26],[3,20,31],[3,26,31],[26,31]]),
    (false,0,237,[[3,26],[26,31],[3,20,31],[20,26]]),
    (false,0,139,[[2,20,31],[20,31],[2,3,31],[20,26],[26,31],[3,26]]),
    (false,0,272,[[2,31],[3,26],[26,31],[20,26],[2,3,31],[20,31]]),
    (false,0,358,[[31],[3,31],[20,31],[20,26],[26,31],[3,26]]),
    (false,0,405,[[26],[3,26],[20,26],[20,31],[3,31],[31]]),
    (false,0,112,[[3,31],[20,26],[3,26],[26]]),
    (false,0,145,[[3,20],[3,31]]),
    (true,140,3,[[3,31],[3,4,31],[3,4,25],[3,25,31]]),
    (false,0,270,[[3,4,25],[3,4,31]]),
    (false,0,358,[[3,31],[31],[4,31],[3,4,25]]),
    (false,0,362,[[3,25],[25],[4,25],[4,31],[31],[3,31]]),
    (false,0,112,[[3,31],[31],[25],[3,25]]),
    (false,0,5,[[3,20],[3,25],[25],[31]]),
    (false,0,420,[[3],[31],[25],[3,20]]),
    (false,0,290,[[2,20],[20],[2,3],[25],[31],[3]]),
    (false,0,423,[[2],[3],[31],[25],[2,3],[20]]),
    (false,0,439,[[],[20],[25],[31]]),
    (true,150,49,[[31,49],[4,31,49],[4,25,49],[25,31,49]]),
    (true,146,31,[[31,49],[8,31,49],[25,31,49]]),
    (false,0,1,[[4,31,49],[4,25,49],[8,31,49]]),
    (false,0,213,[[4,25,49],[4,31,49]]),
    (true,148,7,[[3,7],[3,7,15]])]

def pcSteps10Block4 : List (PCStep) := [
    (true,149,21,[[3,21],[3,15,21]]),
    (false,0,65,[[2,3,21],[2,3,15]]),
    (false,0,382,[[2,21],[21],[3,21],[2,3,15]]),
    (false,0,385,[[2,15],[15],[3,15],[3,21],[21],[2,21]]),
    (true,153,27,[[3,27],[3,15,27]]),
    (true,154,32,[[3,32],[3,15,32]]),
    (true,154,21,[[7,21],[7,15,21]]),
    (false,0,67,[[2,7,21],[2,7,15]]),
    (false,0,363,[[2,21],[21],[7,21],[2,7,15]]),
    (false,0,366,[[2,15],[15],[7,15],[7,21],[21],[2,21]]),
    (true,158,42,[[7,42],[7,15,42]]),
    (true,159,48,[[7,48],[7,15,48]]),
    (true,159,37,[[9,37],[9,15,37]]),
    (true,158,27,[[2,21,27],[2,15,27]]),
    (true,159,32,[[2,21,32],[2,15,32]]),
    (true,150,26,[[4,26],[4,20,26]]),
    (false,0,44,[[3,4,26],[3,4,20]]),
    (false,0,390,[[3,26],[26],[4,26],[3,4,20]]),
    (false,0,394,[[3,20],[20],[4,20],[4,26],[26],[3,26]]),
    (true,154,32,[[4,32],[4,20,32]]),
    (true,155,37,[[4,37],[4,20,37]]),
    (true,156,42,[[4,42],[4,20,42]]),
    (true,156,26,[[5,26],[5,20,26]]),
    (false,0,50,[[3,5,26],[3,5,20]]),
    (true,158,37,[[5,37],[5,20,37]]),
    (true,159,42,[[5,42],[5,20,42]]),
    (true,160,43,[[5,43],[5,20,43]]),
    (true,160,26,[[8,26],[8,20,26]]),
    (false,0,52,[[3,8,26],[3,8,20]]),
    (false,0,379,[[3,26],[26],[8,26],[3,8,20]]),
    (false,0,382,[[3,20],[20],[8,20],[8,26],[26],[3,26]]),
    (true,163,37,[[9,37],[9,20,37]]),
    (true,162,32,[[3,26,32],[3,20,32]]),
    (true,163,37,[[3,26,37],[3,20,37]]),
    (true,164,42,[[3,26,42],[3,20,42]]),
    (true,160,37,[[5,37],[5,25,37]]),
    (true,161,42,[[5,42],[5,25,42]]),
    (true,162,43,[[5,43],[5,25,43]]),
    (true,155,4,[[4,27,42],[4,27,37]]),
    (true,150,38,[[38,44]]),
    (true,142,38,[[38,44],[6,38,44]]),
    (false,0,447,[[6,38],[38,44]]),
    (false,0,2,[[6,38]]),
    (true,138,26,[[26,49],[4,26,49]]),
    (true,139,31,[[31,49],[4,31,49]]),
    (false,0,46,[[4,25,49],[31,49]]),
    (false,0,200,[[3,25,49],[25,49],[3,4,49],[31,49]]),
    (false,0,330,[[3,49],[31,49],[3,4,49],[25,49]]),
    (false,0,417,[[49],[4,49],[25,49],[31,49]]),
    (true,144,32,[[32,49],[4,32,49]]),
    (true,137,43,[[43,49],[7,43,49]]),
    (false,0,455,[[7,43],[43,49]]),
    (true,127,4,[[4,16],[1,4,16],[4,10,16],[4,10,21],[1,4,21],[4,21]]),
    (false,0,238,[[10,21],[0,10,21],[0,4,21],[4,21],[1,4,21],[4,10,16],[1,4,16],[4,16]]),
    (false,0,240,[[10,16],[0,10,16],[0,4,16],[4,16],[1,4,16],[1,4,21],[4,21],[0,4,21],[0,10,21],[10,21]]),
    (true,130,5,[[5,16],[1,5,16],[5,10,16],[5,10,21],[1,5,21],[5,21]]),
    (false,0,230,[[0,10,21],[10,21],[0,5,21],[5,21],[1,5,21],[5,10,16],[1,5,16],[5,16]]),
    (false,0,232,[[0,10,16],[10,16],[0,5,16],[5,16],[1,5,16],[1,5,21],[5,21],[0,5,21],[10,21],[0,10,21]]),
    (true,123,4,[[1,4,21],[4,21],[4,15],[1,4,15]]),
    (false,0,4,[[10,16],[0,10,16],[0,4,16],[4,16],[1,4,16],[0,4,21],[0,10,21],[10,21],[1,4,15],[4,15]]),
    (false,0,144,[[1,4,10],[4,15],[1,4,15],[10,21],[0,10,21],[0,4,21]]),
    (false,0,376,[[1,4],[0,4,21],[0,10,21],[10,21],[4,15],[1,4,10]]),
    (false,0,264,[[0,4,10],[4,10],[0,1,4],[4,15],[10,21],[0,10,21],[0,4,21],[1,4]]),
    (false,0,387,[[0,21],[1,4],[0,4,21],[10,21],[4,15],[0,1,4],[4,10],[0,4,10]]),
    (false,0,430,[[4,21],[21],[0,4,10],[4,10],[0,1,4],[4,15],[10,21],[1,4]]),
    (false,0,433,[[10],[0,10],[1,4],[10,21],[4,15],[0,1,4],[21],[4,21]]),
    (false,0,465,[[0,4],[4],[4,21],[21],[4,15],[10,21],[0,10],[10]]),
    (false,0,142,[[16],[1,16],[10,16],[1,21],[10],[0,10],[4,15],[4,21],[4],[0,4]]),
    (false,0,265,[[1,10],[0,4],[4],[4,21],[4,15],[0,10],[10],[1,21]]),
    (true,134,5,[[1,5,21],[5,21],[5,15],[1,5,15]]),
    (false,0,12,[[0,10,16],[10,16],[0,5,16],[5,16],[1,5,16],[0,5,21],[10,21],[0,10,21],[1,5,15],[5,15]]),
    (false,0,153,[[1,5,10],[5,15],[1,5,15],[0,10,21],[10,21],[0,5,21]]),
    (false,0,386,[[1,5],[0,5,21],[10,21],[0,10,21],[5,15],[1,5,10]]),
    (false,0,274,[[0,5,10],[5,10],[0,1,5],[5,15],[0,10,21],[10,21],[0,5,21],[1,5]]),
    (false,0,398,[[0,21],[1,5],[0,5,21],[10,21],[5,15],[0,1,5],[5,10],[0,5,10]]),
    (false,0,436,[[21],[5,21],[0,5,10],[5,10],[0,1,5],[5,15],[10,21],[1,5]]),
    (false,0,439,[[0,10],[10],[1,5],[10,21],[5,15],[0,1,5],[5,21],[21]]),
    (false,0,475,[[0,5],[5],[21],[5,21],[5,15],[10,21],[10],[0,10]]),
    (false,0,153,[[16],[1,16],[10,16],[1,21],[0,10],[10],[5,15],[5,21],[5],[0,5]]),
    (false,0,276,[[1,10],[0,5],[5],[5,21],[5,15],[10],[0,10],[1,21]]),
    (true,145,27,[[1,21,27],[21,27],[15,27],[1,15,27]]),
    (true,146,32,[[1,21,32],[21,32],[15,32],[1,15,32]]),
    (true,147,37,[[1,21,37],[21,37],[15,37],[1,15,37]]),
    (true,148,42,[[1,21,42],[21,42],[15,42],[1,15,42]]),
    (true,123,6,[[2,6,15],[2,6,31]]),
    (true,124,7,[[2,7,15],[2,7,31]]),
    (false,0,439,[[2,31],[31],[7,31],[2,7,15]]),
    (false,0,444,[[2,15],[15],[7,15],[7,31],[31],[2,31]]),
    (true,127,42,[[2,15,42],[2,31,42]]),
    (true,128,48,[[2,15,48],[2,31,48]]),
    (true,119,5,[[5],[5,15],[5,20],[5,26]]),
    (true,120,6,[[6],[6,15],[6,20],[6,26]]),
    (true,121,9,[[9],[9,15],[9,20],[9,26]]),
    (true,122,32,[[32],[15,32],[20,32],[26,32]]),
    (true,123,37,[[37],[15,37],[20,37],[26,37]]),
    (true,124,42,[[42],[15,42],[20,42],[26,42]]),
    (true,125,48,[[48],[15,48],[20,48],[26,48]]),
    (true,126,54,[[54],[15,54],[20,54],[26,54]]),
    (true,103,5,[[5],[5,20],[5,25],[5,31]]),
    (true,95,5,[[2,5,15],[5,15],[3,5,15],[3,5,21],[5,21],[2,5,21]])]

def pcSteps10Block5 : List (PCStep) := [
    (true,96,7,[[2,7,15],[7,15],[3,7,15],[3,7,21],[7,21],[2,7,21]]),
    (true,97,27,[[2,15,27],[15,27],[3,15,27],[3,21,27],[21,27],[2,21,27]]),
    (false,0,514,[[3,21],[2,21,27],[21,27],[3,15,27],[15,27],[2,15,27]]),
    (false,0,98,[[3,27],[2,15,27],[15,27],[21,27],[2,21,27],[3,21]]),
    (false,0,90,[[3,21],[21,27],[15,27],[3,27]]),
    (true,101,32,[[2,15,32],[15,32],[3,15,32],[3,21,32],[21,32],[2,21,32]]),
    (true,96,27,[[2,15,27],[15,27],[7,15,27],[7,21,27],[21,27],[2,21,27]]),
    (true,97,32,[[2,15,32],[15,32],[7,15,32],[7,21,32],[21,32],[2,21,32]]),
    (true,89,32,[[3,20,32],[20,32],[4,20,32],[4,26,32],[26,32],[3,26,32]]),
    (false,0,519,[[4,26],[3,26,32],[26,32],[4,20,32],[20,32],[3,20,32]]),
    (false,0,90,[[4,32],[3,20,32],[20,32],[26,32],[3,26,32],[4,26]]),
    (false,0,78,[[4,26],[26,32],[20,32],[4,32]]),
    (false,0,18,[[32],[15,32],[4,32],[4,26]]),
    (false,0,255,[[4,26],[4,32]]),
    (true,95,37,[[3,20,37],[20,37],[4,20,37],[4,26,37],[26,37],[3,26,37]]),
    (true,96,42,[[3,20,42],[20,42],[4,20,42],[4,26,42],[26,42],[3,26,42]]),
    (true,73,8,[[6,8,38]]),
    (false,0,453,[[6,38],[38],[8,38]]),
    (true,75,49,[[6,38,49]]),
    (false,0,225,[[38,49]]),
    (true,68,5,[[5,7,43],[5,43,49]]),
    (false,0,229,[[43,49],[5,7,43]]),
    (false,0,465,[[5,43],[43],[7,43],[43,49]]),
    (false,0,71,[[43],[5,43]]),
    (true,72,6,[[6,7,43],[6,43,49]]),
    (false,0,230,[[43,49],[6,7,43]]),
    (true,74,9,[[7,9,43],[9,43,49]]),
    (false,0,213,[[7,9,43]]),
    (false,0,470,[[7,43],[43],[9,43]]),
    (true,77,38,[[7,38,43],[38,43,49]]),
    (false,0,366,[[38,49],[7,38,43]]),
    (false,0,369,[[7,38],[38,49]]),
    (false,0,12,[[7,38]]),
    (true,81,54,[[7,43,54],[43,49,54]]),
    (false,0,361,[[43,49],[7,43,54]]),
    (false,0,226,[[43,54],[43,49]]),
    (true,67,27,[[1,10,27],[0,4,27],[4,27],[4,21,27],[4,15,27],[0,10,27],[10,27],[1,21,27]]),
    (true,68,32,[[1,10,32],[0,4,32],[4,32],[4,21,32],[4,15,32],[0,10,32],[10,32],[1,21,32]]),
    (true,69,37,[[1,10,37],[0,4,37],[4,37],[4,21,37],[4,15,37],[0,10,37],[10,37],[1,21,37]]),
    (true,70,42,[[1,10,42],[0,4,42],[4,42],[4,21,42],[4,15,42],[0,10,42],[10,42],[1,21,42]]),
    (true,60,27,[[1,10,27],[0,5,27],[5,27],[5,21,27],[5,15,27],[10,27],[0,10,27],[1,21,27]]),
    (true,61,32,[[1,10,32],[0,5,32],[5,32],[5,21,32],[5,15,32],[10,32],[0,10,32],[1,21,32]]),
    (true,54,6,[[2,6,15],[6,15],[6,7,15],[6,7,31],[6,31],[2,6,31]]),
    (true,55,42,[[2,15,42],[15,42],[7,15,42],[7,31,42],[31,42],[2,31,42]]),
    (true,56,48,[[2,15,48],[15,48],[7,15,48],[7,31,48],[31,48],[2,31,48]]),
    (true,52,37,[[9,37],[9,15,37],[9,20,37],[9,26,37]]),
    (true,47,37,[[5,37],[5,20,37],[5,25,37],[5,31,37]]),
    (false,0,556,[[5,31],[5,25,37],[5,20,37],[5,37]]),
    (false,0,112,[[5,20,37],[5,31]]),
    (false,0,124,[[5,37],[5,31]]),
    (true,51,42,[[5,42],[5,20,42],[5,25,42],[5,31,42]]),
    (true,52,43,[[5,43],[5,20,43],[5,25,43],[5,31,43]]),
    (true,47,4,[[3,4,21],[4,21,27],[4,15,27],[3,4,27]]),
    (false,0,16,[[1,10,27],[0,4,27],[4,27],[0,10,27],[10,27],[1,21,27],[3,4,27],[3,4,21]]),
    (false,0,526,[[3,27],[27],[3,4,21],[1,21,27],[10,27],[0,10,27],[0,4,27],[1,10,27]]),
    (false,0,530,[[3,21],[21],[4,21],[1,10,27],[0,4,27],[0,10,27],[10,27],[1,21,27],[27],[3,27]]),
    (false,0,75,[[21,27],[15,27],[1,15,27],[3,27],[27],[10,27],[0,10,27],[0,4,27],[1,10,27],[4,21],[21],[3,21]]),
    (false,0,464,[[1,27],[3,21],[21],[4,21],[1,10,27],[0,4,27],[0,10,27],[10,27],[27],[3,27],[15,27],[21,27]]),
    (false,0,353,[[0,1,27],[21,27],[15,27],[3,27],[27],[0,4,27],[4,21],[21],[3,21],[1,27]]),
    (false,0,524,[[4,27],[0,27],[1,27],[3,21],[21],[4,21],[3,27],[15,27],[21,27],[0,1,27]]),
    (false,0,553,[[27],[21,27],[15,27],[3,27],[4,21],[21],[3,21],[4,27]]),
    (false,0,56,[[4,27],[21],[4,21],[27]]),
    (true,57,5,[[3,5,21],[5,21,27],[5,15,27],[3,5,27]]),
    (false,0,22,[[1,10,27],[0,5,27],[5,27],[10,27],[0,10,27],[1,21,27],[3,5,27],[3,5,21]]),
    (true,59,7,[[3,7,21],[7,21,27],[7,15,27],[3,7,27]]),
    (false,0,58,[[2,15,27],[15,27],[21,27],[2,21,27],[3,7,27],[3,7,21]]),
    (true,61,32,[[3,21,32],[21,27,32],[15,27,32],[3,27,32]]),
    (false,0,419,[[21,27],[3,27,32],[15,27,32],[3,21,32]]),
    (false,0,421,[[15,27],[3,21,32],[3,27,32],[21,27]]),
    (false,0,424,[[3,27],[21,27],[3,21,32],[15,27]]),
    (false,0,64,[[2,15,32],[15,32],[3,15,32],[21,32],[2,21,32],[15,27],[21,27],[3,27]]),
    (false,0,165,[[3,32],[3,27],[21,27],[15,27],[2,21,32],[21,32],[15,32],[2,15,32]]),
    (false,0,157,[[15,32],[21,32],[15,27],[21,27],[3,27],[3,32]]),
    (true,59,3,[[3,4,26],[3,4,32]]),
    (false,0,544,[[3,32],[32],[4,32],[3,4,26]]),
    (false,0,548,[[3,26],[26],[4,26],[4,32],[32],[3,32]]),
    (false,0,62,[[3,32],[32],[26],[3,26]]),
    (true,63,9,[[4,9,26],[4,9,32]]),
    (false,0,525,[[4,32],[32],[9,32],[4,9,26]]),
    (false,0,527,[[4,26],[26],[9,26],[9,32],[32],[4,32]]),
    (true,66,21,[[4,21,26],[4,21,32]]),
    (false,0,43,[[1,10,32],[0,4,32],[4,32],[4,15,32],[0,10,32],[10,32],[1,21,32],[4,21,26]]),
    (false,0,444,[[4,21],[1,21,32],[10,32],[0,10,32],[4,15,32],[4,32],[0,4,32],[1,10,32]]),
    (false,0,257,[[4,10,32],[15,32],[1,10,32],[0,4,32],[4,32],[0,10,32],[1,21,32],[4,21]]),
    (false,0,368,[[10,32],[4,21],[1,21,32],[4,32],[1,10,32],[15,32]]),
    (false,0,103,[[21,32],[1,15,32],[1,10,32],[4,32],[4,21],[10,32]]),
    (false,0,491,[[1,32],[10,32],[4,21],[4,32],[1,10,32],[21,32]]),
    (false,0,381,[[0,10,32],[0,1,32],[21,32],[4,32],[4,21],[1,32]]),
    (false,0,511,[[0,32],[1,32],[4,21],[4,32],[21,32],[0,1,32]]),
    (false,0,581,[[32],[21,32],[4,32],[4,21]]),
    (false,0,17,[[15,32],[15,27],[21,27],[3,27],[3,32],[4,21],[4,32],[32]]),
    (false,0,86,[[3,21],[32],[4,32],[4,21],[3,32],[15,32]]),
    (false,0,334,[[3,32],[4,21],[4,32],[3,21]]),
    (false,0,79,[[4,26],[3,21],[4,21],[3,32]]),
    (false,0,175,[[3,20],[20],[4,20],[26],[3,26],[3,32],[4,21],[3,21]]),
    (false,0,126,[[1,10],[0,4],[4],[4,15],[0,10],[10],[1,21],[3,21],[3,32],[3,26],[26],[4,20],[20],[3,20]]),
    (false,0,331,[[3,20],[20],[26],[3,26],[3,32],[3,21],[1,21],[10],[0,10],[4,15],[0,4],[1,10]]),
    (false,0,384,[[4,10],[15],[1,10],[0,4],[0,10],[1,21],[3,21],[3,32],[3,26],[26],[20],[3,20]]),
    (false,0,527,[[10],[3,20],[20],[26],[3,26],[3,32],[3,21],[1,21],[1,10],[15]]),
    (false,0,22,[[32],[15],[1,10],[1,21],[3,21],[20],[3,20],[10]])]

def pcSteps10Block6 : List (PCStep) := [
    (false,0,196,[[2,15],[3,15],[21],[2,21],[10],[3,20],[20],[1,21],[1,10],[32]]),
    (false,0,499,[[2,20],[2,3],[32],[1,10],[1,21],[10],[2,21],[21],[3,15],[2,15]]),
    (false,0,351,[[3],[2,15],[21],[2,21],[10],[1,21],[1,10],[32],[2,3],[2,20]]),
    (false,0,348,[[2,20],[2,3],[32],[1,10],[1,21],[10],[21],[3]]),
    (false,0,634,[[2],[3],[21],[10],[1,21],[1,10],[32],[2,3]]),
    (false,0,650,[[],[32],[1,10],[1,21],[10],[21]]),
    (false,0,271,[[15],[1,15],[10],[1,10],[32],[]]),
    (false,0,638,[[1],[],[32],[1,10],[10],[15]]),
    (false,0,540,[[0,10],[0,1],[15],[32],[],[1]]),
    (false,0,641,[[0],[1],[],[32],[15],[0,1]]),
    (false,0,657,[[15],[32]]),
    (true,97,37,[[4,26,37],[4,32,37]]),
    (false,0,461,[[4,32],[4,26,37]]),
    (false,0,98,[[3,20,37],[20,37],[4,20,37],[26,37],[3,26,37],[4,32]]),
    (false,0,193,[[4,37],[4,32],[3,26,37],[26,37],[20,37],[3,20,37]]),
    (false,0,181,[[20,37],[26,37],[4,32],[4,37]]),
    (false,0,121,[[37],[15,37],[4,37],[4,32]]),
    (false,0,358,[[4,32],[4,37]]),
    (true,104,42,[[4,26,42],[4,32,42]]),
    (false,0,335,[[4,32,37],[4,26,42]]),
    (false,0,469,[[4,32],[4,26,42]]),
    (false,0,105,[[3,20,42],[20,42],[4,20,42],[26,42],[3,26,42],[4,32]]),
    (false,0,200,[[4,42],[4,32],[3,26,42],[26,42],[20,42],[3,20,42]]),
    (false,0,188,[[20,42],[26,42],[4,32],[4,42]]),
    (false,0,128,[[42],[15,42],[4,42],[4,32]]),
    (false,0,364,[[4,32],[4,42]]),
    (true,112,49,[[4,26,49],[4,32,49]]),
    (false,0,177,[[32,49],[4,26,49]]),
    (false,0,184,[[26,49],[32,49]]),
    (true,115,54,[[4,26,54],[4,32,54]]),
    (false,0,330,[[32,54],[4,26,54]]),
    (false,0,332,[[26,54],[32,54]]),
    (true,108,6,[[6,43],[5,6,43]]),
    (true,109,37,[[37,43],[5,37,43]]),
    (true,110,38,[[38,43],[5,38,43]]),
    (false,0,474,[[5,38],[38,43]]),
    (false,0,655,[[38],[5,38]]),
    (true,87,6,[[5,6,37],[5,6,31]]),
    (true,88,7,[[5,7,37],[5,7,31]]),
    (false,0,583,[[5,37],[37],[7,37],[5,7,31]]),
    (false,0,585,[[5,31],[31],[7,31],[7,37],[37],[5,37]]),
    (true,91,42,[[5,37,42],[5,31,42]]),
    (false,0,486,[[5,37],[5,31,42]]),
    (false,0,92,[[5,42],[5,20,42],[5,25,42],[5,37]]),
    (false,0,207,[[5,37],[5,20,42]]),
    (false,0,219,[[5,42],[5,37]]),
    (true,96,43,[[5,37,43],[5,31,43]]),
    (false,0,13,[[37,43],[5,31,43]]),
    (false,0,96,[[5,43],[5,20,43],[5,25,43],[37,43]]),
    (false,0,211,[[37,43],[5,20,43]]),
    (false,0,223,[[5,43],[37,43]]),
    (true,101,48,[[5,37,48],[5,31,48]]),
    (true,102,49,[[5,37,49],[5,31,49]]),
    (false,0,362,[[37,49],[5,31,49]]),
    (false,0,364,[[31,49],[37,49]]),
    (true,93,37,[[4,27,37],[21,37],[4,21,37],[27,37]]),
    (false,0,376,[[4,27,32],[27,37],[4,21,37],[21,37]]),
    (false,0,511,[[4,27],[21,37],[4,21,37],[27,37]]),
    (false,0,119,[[1,10,37],[0,4,37],[4,37],[4,15,37],[0,10,37],[10,37],[1,21,37],[27,37],[21,37],[4,27]]),
    (false,0,332,[[4,10,37],[15,37],[4,27],[21,37],[27,37],[1,21,37],[0,10,37],[4,37],[0,4,37],[1,10,37]]),
    (false,0,443,[[10,37],[1,10,37],[4,37],[1,21,37],[27,37],[21,37],[4,27],[15,37]]),
    (false,0,178,[[1,15,37],[4,27],[27,37],[4,37],[1,10,37],[10,37]]),
    (false,0,566,[[1,37],[10,37],[1,10,37],[4,37],[27,37],[4,27]]),
    (false,0,456,[[0,10,37],[0,1,37],[4,27],[27,37],[4,37],[1,37]]),
    (false,0,586,[[0,37],[1,37],[4,37],[27,37],[4,27],[0,1,37]]),
    (false,0,656,[[37],[4,27],[27,37],[4,37]]),
    (false,0,512,[[27,32],[4,37],[4,27],[37]]),
    (false,0,689,[[27],[37],[4,27],[4,37]]),
    (false,0,50,[[4,32],[4,27],[37],[27]]),
    (false,0,155,[[4,26],[27],[37],[4,27]]),
    (false,0,108,[[21],[4,21],[37],[4,26]]),
    (false,0,252,[[3,20],[20],[4,20],[26],[3,26],[37],[4,21],[21]]),
    (false,0,203,[[1,10],[0,4],[4],[4,15],[0,10],[10],[1,21],[21],[37],[3,26],[26],[4,20],[20],[3,20]]),
    (false,0,408,[[3,20],[20],[26],[3,26],[37],[21],[1,21],[10],[0,10],[4,15],[0,4],[1,10]]),
    (false,0,461,[[4,10],[15],[1,10],[0,4],[0,10],[1,21],[21],[37],[3,26],[26],[20],[3,20]]),
    (false,0,604,[[10],[3,20],[20],[26],[3,26],[37],[21],[1,21],[1,10],[15]]),
    (false,0,406,[[15],[1,10],[1,21],[21],[37],[26],[20],[10]]),
    (false,0,342,[[1,15],[10],[20],[26],[37],[1,10]]),
    (false,0,709,[[1],[1,10],[37],[26],[20],[10]]),
    (false,0,611,[[0,10],[0,1],[20],[26],[37],[1]]),
    (false,0,712,[[0],[1],[37],[26],[20],[0,1]]),
    (false,0,728,[[],[20],[26],[37]]),
    (true,120,42,[[4,27,42],[21,42],[4,21,42],[27,42]]),
    (false,0,244,[[4,27,37],[27,42],[4,21,42],[21,42]]),
    (false,0,404,[[4,27,32],[21,42],[4,21,42],[27,42]]),
    (false,0,539,[[4,27],[27,42],[4,21,42],[21,42]]),
    (false,0,146,[[1,10,42],[0,4,42],[4,42],[4,15,42],[0,10,42],[10,42],[1,21,42],[21,42],[27,42],[4,27]]),
    (false,0,359,[[4,10,42],[15,42],[4,27],[27,42],[21,42],[1,21,42],[0,10,42],[4,42],[0,4,42],[1,10,42]]),
    (false,0,470,[[10,42],[1,10,42],[4,42],[1,21,42],[21,42],[27,42],[4,27],[15,42]]),
    (false,0,205,[[1,15,42],[4,27],[27,42],[4,42],[1,10,42],[10,42]]),
    (false,0,593,[[1,42],[10,42],[1,10,42],[4,42],[27,42],[4,27]]),
    (false,0,483,[[0,10,42],[0,1,42],[4,27],[27,42],[4,42],[1,42]]),
    (false,0,613,[[0,42],[1,42],[4,42],[27,42],[4,27],[0,1,42]]),
    (false,0,683,[[42],[4,27],[27,42],[4,42]]),
    (false,0,411,[[27,37],[4,42],[4,27],[42]]),
    (false,0,541,[[27,32],[42],[4,27],[4,42]]),
    (false,0,718,[[27],[4,42],[4,27],[42]]),
    (false,0,71,[[4,32],[42],[4,27],[27]]),
    (false,0,184,[[4,26],[27],[4,27],[42]]),
    (false,0,137,[[21],[4,21],[42],[4,26]])]

def pcSteps10Block7 : List (PCStep) := [
    (false,0,281,[[3,20],[20],[4,20],[26],[3,26],[42],[4,21],[21]]),
    (false,0,232,[[1,10],[0,4],[4],[4,15],[0,10],[10],[1,21],[21],[42],[3,26],[26],[4,20],[20],[3,20]]),
    (false,0,437,[[3,20],[20],[26],[3,26],[42],[21],[1,21],[10],[0,10],[4,15],[0,4],[1,10]]),
    (false,0,490,[[4,10],[15],[1,10],[0,4],[0,10],[1,21],[21],[42],[3,26],[26],[20],[3,20]]),
    (false,0,633,[[10],[3,20],[20],[26],[3,26],[42],[21],[1,21],[1,10],[15]]),
    (false,0,435,[[15],[1,10],[1,21],[21],[42],[26],[20],[10]]),
    (false,0,371,[[1,15],[10],[20],[26],[42],[1,10]]),
    (false,0,738,[[1],[1,10],[42],[26],[20],[10]]),
    (false,0,640,[[0,10],[0,1],[20],[26],[42],[1]]),
    (false,0,741,[[0],[1],[42],[26],[20],[0,1]]),
    (false,0,757,[[],[20],[26],[42]]),
    (true,138,5,[[5,15,32],[5,21,32],[5,15,27],[5,21,27],[3,5,27],[3,5,32]]),
    (false,0,170,[[1,10,32],[0,5,32],[5,32],[10,32],[0,10,32],[1,21,32],[3,5,32],[3,5,27],[5,21,27],[5,15,27]]),
    (false,0,172,[[1,10,27],[0,5,27],[5,27],[10,27],[0,10,27],[1,21,27],[3,5,27],[3,5,32],[1,21,32],[0,10,32],[10,32],[5,32],[0,5,32],[1,10,32]]),
    (true,141,7,[[7,15,32],[7,21,32],[7,15,27],[7,21,27],[3,7,27],[3,7,32]]),
    (false,0,207,[[2,15,32],[15,32],[21,32],[2,21,32],[3,7,32],[3,7,27],[7,21,27],[7,15,27]]),
    (false,0,209,[[2,15,27],[15,27],[21,27],[2,21,27],[3,7,27],[3,7,32],[2,21,32],[21,32],[15,32],[2,15,32]]),
    (true,140,5,[[3,5,32],[5,32],[5,26],[3,5,26]]),
    (false,0,4,[[1,10,27],[0,5,27],[5,27],[10,27],[0,10,27],[1,21,27],[3,5,27],[1,21,32],[0,10,32],[10,32],[0,5,32],[1,10,32],[3,5,26],[5,26]]),
    (false,0,155,[[3,5,21],[5,26],[3,5,26],[1,10,32],[0,5,32],[10,32],[0,10,32],[1,21,32]]),
    (false,0,296,[[3,5,20],[1,21,32],[0,10,32],[10,32],[0,5,32],[1,10,32],[5,26],[3,5,21]]),
    (false,0,221,[[2,5,15],[5,15],[3,5,15],[5,21],[2,5,21],[5,26],[1,10,32],[0,5,32],[10,32],[0,10,32],[1,21,32],[3,5,20]]),
    (false,0,488,[[2,5,20],[5,20],[2,3,5],[1,21,32],[0,10,32],[10,32],[0,5,32],[1,10,32],[5,26],[2,5,21],[5,21],[3,5,15],[5,15],[2,5,15]]),
    (false,0,394,[[3,10],[3,5,10],[3,15],[2,5,15],[5,15],[5,21],[2,5,21],[5,26],[1,10,32],[0,5,32],[10,32],[0,10,32],[1,21,32],[2,3,5],[5,20],[2,5,20]]),
    (false,0,505,[[0,3,10],[0,3,5],[2,5,20],[5,20],[2,3,5],[1,21,32],[0,10,32],[10,32],[0,5,32],[1,10,32],[5,26],[2,5,21],[5,21],[5,15],[2,5,15],[3,15]]),
    (false,0,386,[[0,10,21],[0,5,21],[15,21],[3,15],[5,15],[5,26],[1,10,32],[0,5,32],[10,32],[0,10,32],[1,21,32],[2,3,5],[5,20],[2,5,20],[0,3,5],[0,3,10]]),
    (false,0,623,[[2,5],[0,3,10],[0,3,5],[5,20],[2,3,5],[1,21,32],[0,10,32],[10,32],[0,5,32],[1,10,32],[5,26],[5,15],[3,15],[15,21],[0,5,21],[0,10,21]]),
    (false,0,711,[[5],[3,5],[0,10,21],[0,5,21],[15,21],[3,15],[5,15],[5,26],[1,10,32],[0,5,32],[10,32],[0,10,32],[1,21,32],[5,20],[0,3,5],[0,3,10]]),
    (false,0,246,[[21,32],[15,32],[1,15,32],[0,3,10],[0,3,5],[5,20],[0,10,32],[10,32],[0,5,32],[1,10,32],[5,26],[5,15],[3,15],[15,21],[0,5,21],[0,10,21],[3,5],[5]]),
    (false,0,634,[[1,32],[5],[3,5],[0,10,21],[0,5,21],[15,21],[3,15],[5,15],[5,26],[1,10,32],[0,5,32],[10,32],[0,10,32],[5,20],[0,3,5],[0,3,10],[15,32],[21,32]]),
    (false,0,524,[[0,1,32],[21,32],[15,32],[0,3,10],[0,3,5],[5,20],[0,5,32],[5,26],[5,15],[3,15],[15,21],[0,5,21],[0,10,21],[3,5],[5],[1,32]]),
    (false,0,655,[[0,21],[1,32],[5],[3,5],[0,5,21],[15,21],[3,15],[5,15],[5,26],[0,5,32],[5,20],[0,3,5],[0,3,10],[15,32],[21,32],[0,1,32]]),
    (false,0,692,[[0,32],[32],[5,32],[0,1,32],[21,32],[15,32],[0,3,10],[0,3,5],[5,20],[5,26],[5,15],[3,15],[15,21],[0,5,21],[3,5],[5],[1,32],[0,21]]),
    (false,0,694,[[21],[5,21],[1,32],[5],[3,5],[15,21],[3,15],[5,15],[5,26],[5,20],[0,3,5],[0,3,10],[15,32],[21,32],[0,1,32],[5,32],[32],[0,32]]),
    (false,0,665,[[0,3],[0,32],[32],[5,32],[0,1,32],[21,32],[15,32],[0,3,5],[5,20],[5,26],[5,15],[3,15],[15,21],[3,5],[5],[1,32],[5,21],[21]]),
    (false,0,699,[[3],[21],[5,21],[1,32],[5],[15,21],[3,15],[5,15],[5,26],[5,20],[15,32],[21,32],[0,1,32],[5,32],[32],[0,32]]),
    (false,0,728,[[5,32],[21,32],[15,32],[5,20],[5,26],[5,15],[3,15],[15,21],[5],[5,21],[21],[3]]),
    (false,0,164,[[15,27],[21,27],[3,27],[3,32],[3],[21],[5,21],[5],[15,21],[3,15],[5,15],[5,26],[5,20],[5,32]]),
    (false,0,233,[[3,21],[5,32],[5,20],[5,26],[5,15],[3,15],[15,21],[5],[5,21],[21],[3],[3,32]]),
    (false,0,509,[[2,21],[2,15],[3,32],[3],[5,21],[5],[3,15],[5,15],[5,26],[5,20],[5,32],[3,21]]),
    (true,163,7,[[3,7,32],[7,32],[7,26],[3,7,26]]),
    (false,0,24,[[2,15,27],[15,27],[21,27],[2,21,27],[3,7,27],[2,21,32],[21,32],[15,32],[2,15,32],[3,7,26],[7,26],[7,32]]),
    (false,0,176,[[3,7,21],[7,32],[7,26],[3,7,26],[2,15,32],[15,32],[21,32],[2,21,32]]),
    (false,0,368,[[2,20,26],[20,26],[2,7,26],[3,7,20],[2,21,32],[21,32],[15,32],[2,15,32],[7,32],[3,7,21]]),
    (false,0,243,[[2,7,15],[7,15],[3,7,15],[7,21],[2,7,21],[7,32],[2,15,32],[15,32],[21,32],[2,21,32],[3,7,20],[2,7,26],[20,26],[2,20,26]]),
    (false,0,510,[[2,7,20],[7,20],[2,3,7],[2,20,26],[20,26],[2,7,26],[2,21,32],[21,32],[15,32],[2,15,32],[7,32],[2,7,21],[7,21],[3,7,15],[7,15],[2,7,15]]),
    (false,0,346,[[3,7],[2,7,15],[7,15],[7,21],[2,7,21],[7,32],[2,15,32],[15,32],[21,32],[2,21,32],[2,7,26],[20,26],[2,20,26],[2,3,7],[7,20],[2,7,20]]),
    (false,0,332,[[2,7,20],[7,20],[2,3,7],[2,20,26],[20,26],[2,7,26],[21,32],[15,32],[7,32],[2,7,21],[7,21],[7,15],[2,7,15],[3,7]]),
    (false,0,641,[[2,26],[3,7],[2,7,15],[7,15],[7,21],[2,7,21],[7,32],[15,32],[21,32],[2,7,26],[20,26],[2,3,7],[7,20],[2,7,20]]),
    (false,0,703,[[26],[7,26],[2,7,20],[7,20],[2,3,7],[20,26],[21,32],[15,32],[7,32],[2,7,21],[7,21],[7,15],[2,7,15],[3,7]]),
    (false,0,705,[[2,21],[21],[3,7],[2,7,15],[7,15],[7,32],[15,32],[21,32],[20,26],[2,3,7],[7,20],[2,7,20],[7,26],[26]]),
    (false,0,707,[[2,20],[20],[26],[7,26],[2,3,7],[20,26],[21,32],[15,32],[7,32],[7,15],[2,7,15],[3,7],[21],[2,21]]),
    (false,0,709,[[2,15],[15],[2,21],[21],[3,7],[7,32],[15,32],[21,32],[20,26],[2,3,7],[7,26],[26],[20],[2,20]]),
    (false,0,736,[[2,7],[7],[2,20],[20],[26],[7,26],[20,26],[21,32],[15,32],[7,32],[21],[2,21],[15],[2,15]]),
    (false,0,181,[[15,27],[21,27],[3,27],[3,32],[2,15],[15],[2,21],[21],[7,32],[20,26],[7,26],[26],[20],[2,20],[7],[2,7]]),
    (false,0,250,[[3,21],[2,7],[7],[2,20],[20],[26],[7,26],[20,26],[7,32],[21],[2,21],[15],[2,15],[3,32]]),
    (false,0,517,[[3,26],[3,20],[3,32],[2,15],[15],[2,21],[21],[7,32],[7,26],[20],[2,20],[7],[2,7],[3,21]]),
    (true,177,37,[[4,26,37],[26,37],[9,26,37],[9,32,37],[32,37],[4,32,37]]),
    (false,0,606,[[9,32],[4,32,37],[32,37],[9,26,37],[26,37],[4,26,37]]),
    (false,0,213,[[9,37],[9,15,37],[9,20,37],[4,26,37],[26,37],[32,37],[4,32,37],[9,32]]),
    (false,0,328,[[9,32],[4,32,37],[32,37],[26,37],[4,26,37],[9,15,37]]),
    (false,0,348,[[9,37],[4,26,37],[26,37],[32,37],[4,32,37],[9,32]]),
    (false,0,611,[[4,32],[9,32],[32,37],[26,37],[4,26,37],[9,37]]),
    (false,0,248,[[3,20,37],[20,37],[4,20,37],[3,26,37],[9,37],[32,37],[9,32],[4,32]]),
    (false,0,343,[[4,37],[4,32],[9,32],[32,37],[9,37],[3,26,37],[20,37],[3,20,37]]),
    (false,0,331,[[20,37],[9,37],[32,37],[9,32],[4,32],[4,37]]),
    (false,0,787,[[32],[4,37],[4,32],[9,32],[9,37],[20,37]]),
    (false,0,495,[[37],[9,37],[9,32],[4,32],[4,37],[32]]),
    (true,157,8,[[8,15],[8,32]]),
    (true,158,38,[[15,38],[32,38]]),
    (true,159,48,[[15,48],[32,48]]),
    (true,153,54,[[4,32,54],[4,37,54]]),
    (false,0,471,[[37,54],[4,32,54]]),
    (false,0,473,[[32,54],[37,54]]),
    (true,148,54,[[4,32,54],[4,42,54]]),
    (false,0,473,[[42,54],[4,32,54]]),
    (false,0,476,[[32,54],[42,54]]),
    (true,140,32,[[32,38],[5,32,38]]),
    (false,0,786,[[5,32],[32,38]]),
    (false,0,9,[[15,38],[5,32]]),
    (false,0,520,[[38],[5,32]]),
    (false,0,41,[[2,21],[2,15],[3,32],[3],[5,21],[5],[3,15],[5,15],[5,26],[5,20],[3,21],[38]]),
    (false,0,291,[[38],[3,21],[3,15],[5,21],[3],[3,32],[2,15],[2,21]]),
    (false,0,303,[[1,10],[0,5],[5],[5,15],[10],[0,10],[1,21],[2,21],[2,15],[3,32],[3],[3,15],[3,21],[38]]),
    (false,0,560,[[5,10],[15],[38],[3,21],[3,15],[3],[3,32],[2,15],[2,21],[1,21],[0,10],[5],[0,5],[1,10]]),
    (false,0,712,[[10],[1,10],[5],[1,21],[2,21],[2,15],[3,32],[3],[3,15],[3,21],[38],[15]]),
    (false,0,209,[[32],[26],[3,26],[15],[38],[3,21],[3,15],[3],[2,15],[2,21],[1,21],[5],[1,10],[10]]),
    (false,0,517,[[3,20],[10],[1,10],[5],[1,21],[2,21],[2,15],[3],[3,15],[3,21],[38],[15],[26],[32]]),
    (false,0,384,[[21],[32],[26],[38],[3],[1,21],[5],[1,10],[10],[3,20]]),
    (false,0,687,[[2,20],[20],[2,3],[10],[1,10],[5],[1,21],[3],[38],[26],[32],[21]]),
    (false,0,820,[[2],[21],[32],[26],[38],[3],[1,21],[5],[1,10],[10],[2,3],[20]]),
    (false,0,836,[[],[20],[10],[1,10],[5],[1,21],[38],[26],[32],[21]]),
    (false,0,457,[[15],[1,15],[32],[26],[38],[5],[1,10],[10],[20],[]]),
    (false,0,824,[[1],[],[20],[10],[1,10],[5],[38],[26],[32],[15]]),
    (false,0,726,[[0,10],[0,1],[15],[32],[26],[38],[5],[20],[],[1]]),
    (false,0,827,[[0],[1],[],[20],[5],[38],[26],[32],[15],[0,1]]),
    (false,0,843,[[15],[32],[26],[38],[5],[20]]),
    (true,156,6,[[5,6,31],[6,31],[6,7,31],[6,7,37],[6,37],[5,6,37]]),
    (true,157,42,[[5,31,42],[31,42],[7,31,42],[7,37,42],[37,42],[5,37,42]]),
    (false,0,642,[[7,37],[5,37,42],[37,42],[7,31,42],[31,42],[5,31,42]])]

def pcSteps10Block8 : List (PCStep) := [
    (false,0,256,[[2,15,42],[15,42],[7,15,42],[2,31,42],[5,31,42],[37,42],[5,37,42],[7,37]]),
    (false,0,390,[[7,42],[7,37],[5,37,42],[37,42],[5,31,42],[2,31,42],[15,42],[2,15,42]]),
    (false,0,646,[[5,37],[2,15,42],[15,42],[2,31,42],[5,31,42],[37,42],[7,37],[7,42]]),
    (false,0,252,[[5,42],[5,20,42],[5,25,42],[7,42],[7,37],[37,42],[2,31,42],[15,42],[2,15,42],[5,37]]),
    (false,0,367,[[5,37],[2,15,42],[15,42],[2,31,42],[37,42],[7,37],[7,42],[5,20,42]]),
    (false,0,379,[[5,42],[7,42],[7,37],[37,42],[2,31,42],[15,42],[2,15,42],[5,37]]),
    (false,0,317,[[5,37],[15,42],[37,42],[7,37],[7,42],[5,42]]),
    (false,0,827,[[37],[5,42],[7,42],[7,37],[15,42],[5,37]]),
    (false,0,547,[[42],[5,37],[7,37],[7,42],[5,42],[37]]),
    (true,168,48,[[5,31,48],[31,48],[7,31,48],[7,37,48],[37,48],[5,37,48]]),
    (true,164,48,[[5,42,48],[5,37,48]]),
    (true,160,6,[[5,6,43],[6,37,43]]),
    (false,0,819,[[6,37],[5,6,43]]),
    (false,0,180,[[6,43],[6,37]]),
    (true,132,6,[[6],[6,20],[6,26],[6,37]]),
    (true,104,48,[[48],[20,48],[26,48],[42,48]]),
    (true,19,7,[[7,15],[7,32],[7,26],[7,38],[5,7],[7,20]]),
    (false,0,284,[[7,20],[5,7],[7,26],[7,32],[7,15]]),
    (false,0,61,[[3,26],[3,20],[3,32],[2,15],[15],[2,21],[21],[20],[2,20],[7],[2,7],[3,21],[7,15],[5,7],[7,20]]),
    (false,0,714,[[5,7],[7,15],[3,21],[7],[21],[2,21],[15],[2,15],[3,32],[3,20],[3,26]]),
    (false,0,568,[[3,26],[3,20],[3,32],[2,15],[15],[2,21],[21],[3,21],[5,7]]),
    (false,0,858,[[5],[],[7],[3,21],[21],[2,21],[15],[2,15],[3,32],[3,20],[3,26]]),
    (false,0,245,[[32],[26],[3,20],[2,15],[15],[2,21],[21],[3,21],[7],[],[5]]),
    (false,0,419,[[3,15],[5],[],[7],[3,20],[26],[32]]),
    (false,0,722,[[2,20],[20],[2,3],[32],[26],[7],[],[5],[3,15]]),
    (false,0,574,[[3],[5],[],[7],[26],[32],[2,3],[20],[2,20]]),
    (false,0,856,[[2],[20],[2,3],[32],[26],[7],[],[5],[3]]),
    (false,0,872,[[5],[7],[26],[32],[20]]),
    (false,0,217,[[15],[20],[26],[7],[5]]),
    (false,0,458,[[],[5],[7]]),
    (true,33,8,[[8,15],[8,32],[8,26],[8,38],[5,8],[8,20]]),
    (false,0,313,[[6,38],[38],[8,20],[5,8],[8,26],[8,32],[8,15]]),
    (false,0,63,[[8,26],[5,8],[8,20],[38],[6,38]]),
    (false,0,402,[[3,20],[20],[26],[3,26],[6,38],[38],[5,8]]),
    (false,0,391,[[5,8],[38],[3,26],[26],[20],[3,20]]),
    (false,0,868,[[8],[],[5],[3,20],[20],[26],[3,26],[38]]),
    (false,0,566,[[38],[26],[20],[5],[],[8]]),
    (false,0,40,[[15],[32],[8],[]]),
    (false,0,227,[[],[8]]),
    (true,42,48,[[15,48],[32,48],[26,48],[38,48],[5,48],[20,48]]),
    (false,0,674,[[38,43],[20,48],[5,48],[26,48],[32,48],[15,48]]),
    (false,0,860,[[38],[15,48],[32,48],[26,48],[5,48],[20,48]]),
    (false,0,71,[[20,48],[5,48],[26,48],[38]]),
    (false,0,346,[[48],[15,48],[38],[5,48]]),
    (false,0,582,[[5,48],[38]]),
    (true,48,49,[[15,49],[32,49],[26,49],[38,49],[5,49],[20,49]]),
    (false,0,326,[[20,49],[5,49],[26,49],[32,49],[15,49]]),
    (false,0,218,[[15,49],[5,49],[20,49]]),
    (false,0,575,[[49],[5,49],[15,49]]),
    (false,0,586,[[5,49]]),
    (false,0,670,[[49]]),
    (true,42,48,[[42,48],[5,37,48],[7,37,48],[7,42,48],[5,42,48],[37,48]]),
    (false,0,857,[[7,42],[37,48],[5,42,48],[7,37,48],[5,37,48],[42,48]]),
    (false,0,43,[[5,31,48],[31,48],[7,31,48],[42,48],[5,42,48],[7,42]]),
    (false,0,309,[[2,15,48],[15,48],[7,15,48],[2,31,48],[7,42],[5,42,48],[42,48],[5,31,48]]),
    (false,0,443,[[7,48],[5,31,48],[42,48],[5,42,48],[7,42],[2,31,48],[15,48],[2,15,48]]),
    (false,0,45,[[5,37,48],[2,15,48],[15,48],[2,31,48],[7,42],[42,48],[5,31,48],[7,48]]),
    (false,0,205,[[7,48],[42,48],[7,42],[2,31,48],[15,48],[2,15,48]]),
    (false,0,368,[[15,48],[7,42],[42,48],[7,48]]),
    (false,0,43,[[48],[20,48],[26,48],[7,48],[7,42],[15,48]]),
    (false,0,363,[[7,42],[7,48]]),
    (true,47,7,[[6,7,43],[6,7,37]]),
    (false,0,336,[[43,49],[6,7,37]]),
    (false,0,65,[[5,6,31],[6,31],[6,7,31],[6,37],[5,6,37],[43,49]]),
    (false,0,321,[[2,6,15],[6,15],[6,7,15],[2,6,31],[43,49],[5,6,37],[6,37],[5,6,31]]),
    (false,0,632,[[1,7,15],[7,15],[1,6,7],[5,6,31],[6,37],[5,6,37],[43,49],[2,6,31],[6,15],[2,6,15]]),
    (false,0,228,[[2,6,15],[6,15],[2,6,31],[43,49],[6,37],[1,6,7],[7,15],[1,7,15]]),
    (false,0,382,[[1,7,15],[7,15],[1,6,7],[6,37],[43,49],[6,15]]),
    (false,0,779,[[1,7],[6,15],[43,49],[6,37],[1,6,7],[7,15]]),
    (false,0,828,[[7],[6,7],[7,15],[6,37],[43,49],[6,15]]),
    (false,0,418,[[7,43],[6,15],[6,37],[7,15],[6,7],[7]]),
    (true,57,9,[[6,9,43],[6,9,37]]),
    (false,0,810,[[9,43],[43],[6,43],[6,9,37]]),
    (false,0,812,[[9,37],[37],[6,37],[6,43],[43],[9,43]]),
    (false,0,345,[[7,43],[6,43],[6,37],[37],[9,37]]),
    (false,0,107,[[9,32],[4,32],[4,37],[32],[6,37],[6,43],[7,43]]),
    (false,0,296,[[4,26],[26],[9,26],[7,43],[6,43],[6,37],[4,37]]),
    (false,0,384,[[9],[9,15],[9,20],[4,37],[6,37],[6,43],[7,43],[26],[4,26]]),
    (false,0,610,[[4,26],[26],[7,43],[6,43],[6,37],[4,37],[9,15]]),
    (false,0,626,[[9],[4,37],[6,37],[6,43],[7,43],[26],[4,26]]),
    (false,0,9,[[6,15],[7,15],[6,7],[7],[4,26],[26],[6,43],[4,37],[9]]),
    (false,0,629,[[9],[4,37],[6,43],[26],[4,26],[6,7],[6,15]]),
    (false,0,68,[[6,37],[6,15],[6,7],[4,26],[26],[4,37],[9]]),
    (false,0,68,[[6],[6,20],[6,26],[9],[4,37],[26],[4,26],[6,7],[6,15]]),
    (false,0,392,[[6,7],[4,26],[26],[4,37],[9]]),
    (true,71,49,[[6,43,49],[6,37,49]]),
    (false,0,591,[[43,49],[6,37,49]]),
    (false,0,594,[[37,49],[43,49]]),
    (false,0,436,[[7,43],[37,49]]),
    (false,0,234,[[31,49],[7,43]]),
    (false,0,441,[[49],[4,49],[25,49],[7,43]]),
    (false,0,641,[[8,49],[7,43],[4,49]]),
    (false,0,893,[[4,49],[7,43]]),
    (false,0,22,[[6,15],[6,37],[7,15],[6,7],[7],[4,49]]),
    (false,0,642,[[4,49],[6,7],[6,37],[6,15]]),
    (false,0,80,[[6],[6,20],[6,26],[6,15],[6,7],[4,49]]),
    (false,0,404,[[4,49],[6,7]]),
    (false,0,12,[[4,26],[26],[4,37],[9],[4,49]]),
    (false,0,593,[[49],[9],[4,37],[26],[4,26]]),
    (false,0,281,[[4,32],[4,26],[26],[9],[49]])]

def pcSteps10Block9 : List (PCStep) := [
    (false,0,386,[[49],[9],[26]]),
    (false,0,50,[[26],[9]]),
    (false,0,531,[[],[15],[20],[9]]),
    (false,0,774,[[9],[15]]),
    (false,0,782,[[],[9]]),
    (true,91,54,[[6,43,54],[6,37,54]]),
    (false,0,599,[[43,54],[6,37,54]]),
    (false,0,601,[[37,54],[43,54]]),
    (false,0,372,[[43,49],[37,54]]),
    (false,0,457,[[7,43],[37,54]]),
    (false,0,136,[[32,54],[7,43]]),
    (false,0,279,[[26,54],[7,43]]),
    (false,0,414,[[54],[15,54],[20,54],[7,43]]),
    (false,0,639,[[7,43],[15,54]]),
    (false,0,650,[[54],[7,43]]),
    (false,0,44,[[6,15],[6,37],[7,15],[6,7],[7],[54]]),
    (false,0,664,[[54],[6,7],[6,37],[6,15]]),
    (false,0,102,[[6],[6,20],[6,26],[6,15],[6,7],[54]]),
    (false,0,426,[[54],[6,7]]),
    (false,0,34,[[4,26],[26],[4,37],[9],[54]]),
    (false,0,302,[[4,32],[54],[9],[26],[4,26]]),
    (false,0,407,[[26],[9],[54]]),
    (true,92,48,[[48],[5,48],[7,48]]),
    (false,0,62,[[7,42],[5,48],[48]]),
    (false,0,115,[[42],[5,37],[7,37],[5,42],[37],[48],[5,48]]),
    (false,0,284,[[5,31],[31],[7,31],[5,48],[48],[5,42],[42]]),
    (false,0,438,[[2,15],[15],[7,15],[2,31],[42],[5,42],[48],[5,48],[5,31]]),
    (false,0,675,[[7],[5,31],[5,48],[48],[5,42],[42],[2,31],[15],[2,15]]),
    (false,0,83,[[38],[2,15],[15],[2,31],[42],[5,42],[48],[5,31],[7]]),
    (false,0,283,[[5,37],[7],[5,31],[48],[42],[2,31],[15],[2,15],[38]]),
    (false,0,380,[[38],[2,15],[15],[2,31],[42],[48],[7]]),
    (false,0,570,[[7],[48],[42],[15],[38]]),
    (true,93,48,[[48],[8,48]]),
    (true,72,54,[[7,42,54],[7,48,54]]),
    (false,0,624,[[48,54],[7,42,54]]),
    (false,0,627,[[42,54],[48,54]]),
    (true,3,54,[[48,54],[8,48,54]]),
    (false,0,940,[[8,48],[48,54]]),
    (false,0,2,[[42,54],[8,48]]),
    (false,0,162,[[32,54],[8,48]]),
    (false,0,308,[[26,54],[8,48]]),
    (false,0,443,[[54],[15,54],[20,54],[8,48]]),
    (false,0,668,[[8,48],[15,54]]),
    (false,0,679,[[54],[8,48]]),
    (false,0,11,[[48],[54]]),
    (false,0,23,[[26],[9],[48]]),
    (false,0,14,[[7],[42],[15],[38],[9],[26]]),
    (false,0,236,[[],[20],[9],[38],[15],[7]]),
    (false,0,151,[[32],[26],[5],[7],[9],[]]),
    (false,0,338,[[15],[],[9],[7],[5],[26]]),
    (false,0,579,[[20],[5],[7],[9]]),
    (false,0,822,[[],[9],[7],[5]]),
    (false,0,47,[[5],[7]]),
    (false,0,123,[[]])]

def pcSteps10 : List (PCStep) := pcSteps10Block0 ++ pcSteps10Block1 ++ pcSteps10Block2 ++ pcSteps10Block3 ++ pcSteps10Block4 ++ pcSteps10Block5 ++ pcSteps10Block6 ++ pcSteps10Block7 ++ pcSteps10Block8 ++ pcSteps10Block9

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
lemma pcUpper10 : PCRefutable (cnfSystem (counter_formula 10 5 upperEdges10)) 3 := by
  apply pcFromGround upperEdges10 pcRows10 pcSteps10 <;> decide

end PEqualNP.Outside.L_pcx_103

namespace PEqualNP.Outside.L_pcx_103

open PEqualNP.ProofComplexity MvPolynomial

variable {V E : Type} [AddCommGroup E] [Module (ZMod 2) E]

noncomputable def momentMap (m : (V →₀ ℕ) → E) : MvPolynomial V (ZMod 2) →ₗ[ZMod 2] E :=
  (Finsupp.lsum (ZMod 2) (fun d => (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2).smulRight (m d))).comp
    (AddMonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap

lemma moment_monomial (m : (V →₀ ℕ) → E) (d : V →₀ ℕ) (c : ZMod 2) :
    momentMap m (monomial d c) = c • m d := by
  change Finsupp.lsum (ZMod 2) (fun e : V →₀ ℕ =>
    (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2).smulRight (m e)) (Finsupp.single d c) = _
  rw [Finsupp.lsum_single]
  rfl

lemma moment_extend (L : MvPolynomial V (ZMod 2) →ₗ[ZMod 2] E) (T : V → E →ₗ[ZMod 2] E)
    (hcomp : ∀ (j : V) (d : V →₀ ℕ), (d.sum (fun _ k => k)) ≤ 2 →
      L (X j * monomial d (1 : ZMod 2)) = T j (L (monomial d (1 : ZMod 2))))
    (p : MvPolynomial V (ZMod 2)) (hp : p.totalDegree ≤ 2) (j : V) :
    L (X j * p) = T j (L p) := by
  classical
  have hb : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rw [p.as_sum]
  simp only [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hc := (hb (p.coeff m)).resolve_left (MvPolynomial.mem_support_iff.mp hm)
  rw [hc]
  exact hcomp j m ((MvPolynomial.le_totalDegree hm).trans hp)

lemma pc_obstruction {F : Set (MvPolynomial V (ZMod 2))}
    (L : MvPolynomial V (ZMod 2) →ₗ[ZMod 2] E) (T : V → E →ₗ[ZMod 2] E)
    (hcomp : ∀ (j : V) (d : V →₀ ℕ), (d.sum (fun _ k => k)) ≤ 2 →
      L (X j * monomial d (1 : ZMod 2)) = T j (L (monomial d (1 : ZMod 2))))
    (hax : ∀ p ∈ F, p.totalDegree ≤ 3 → L p = 0) (hone : L 1 ≠ 0) : ¬ PCRefutable F 3 := by
  intro h
  apply hone
  suffices hall : ∀ (p : MvPolynomial V (ZMod 2)), PCDerivable F 3 p → L p = 0 from hall 1 h
  intro p hd
  induction hd with
  | ax hm hdeg => exact hax _ hm hdeg
  | zero => exact map_zero _
  | add _ _ hp hq => simp [map_add, hp, hq]
  | mulX j hp hdeg ih =>
    rename_i p
    by_cases z : p = 0
    · simp [z]
    rw [MvPolynomial.totalDegree_mul_of_isDomain (X_ne_zero j) z, MvPolynomial.totalDegree_X] at hdeg
    rw [moment_extend L T hcomp p (by omega) j, ih, map_zero]

noncomputable def projectedMoment (label : V → Fin 29) (M : Multiset (Fin 29) → E) :
    MvPolynomial V (ZMod 2) →ₗ[ZMod 2] E :=
  momentMap fun d => M (d.toMultiset.map label)

lemma projected_compat (label : V → Fin 29) (M : Multiset (Fin 29) → E)
    (T : Fin 29 → E →ₗ[ZMod 2] E)
    (hc : ∀ (i : Fin 29) (s : Multiset (Fin 29)), s.card ≤ 2 → M (i ::ₘ s) = T i (M s))
    (j : V) (d : V →₀ ℕ) (hd : d.sum (fun _ k => k) ≤ 2) :
    projectedMoment label M (X j * monomial d (1 : ZMod 2)) =
      T (label j) (projectedMoment label M (monomial d (1 : ZMod 2))) := by
  simp only [projectedMoment, MvPolynomial.X, monomial_mul_monomial, one_mul,
    moment_monomial, one_smul, Finsupp.toMultiset_add, Finsupp.toMultiset_single,
    one_nsmul, Multiset.map_add, Multiset.map_singleton, Multiset.singleton_add, Multiset.map_cons]
  apply hc
  rw [Multiset.card_map, Finsupp.card_toMultiset]
  simpa only [Function.id_def] using hd

lemma moment_unit (label : V → Fin 29) (M : Multiset (Fin 29) → E) : projectedMoment label M 1 = M 0 := by
  change momentMap (fun d : V →₀ ℕ => M (d.toMultiset.map label)) (monomial 0 (1 : ZMod 2)) = M 0
  rw [moment_monomial, one_smul, Finsupp.toMultiset_zero, Multiset.map_zero]

lemma moment_x (label : V → Fin 29) (M : Multiset (Fin 29) → E) (j : V) :
    projectedMoment label M (X j) = M {label j} := by
  simp [projectedMoment, MvPolynomial.X, moment_monomial, Finsupp.toMultiset_single]

lemma moment_xx (label : V → Fin 29) (M : Multiset (Fin 29) → E) (i j : V) :
    projectedMoment label M (X i * X j) = M {label i, label j} := by
  simp [projectedMoment, MvPolynomial.X, monomial_mul_monomial, moment_monomial,
    Finsupp.toMultiset_add, Finsupp.toMultiset_single, Multiset.singleton_add]

lemma moment_xxx (label : V → Fin 29) (M : Multiset (Fin 29) → E) (i j k : V) :
    projectedMoment label M (X i * X j * X k) = M {label i, label j, label k} := by
  simp [projectedMoment, MvPolynomial.X, monomial_mul_monomial, moment_monomial,
    Finsupp.toMultiset_add, Finsupp.toMultiset_single, Multiset.singleton_add]


variable [DecidableEq V]

lemma moment_binary_pos (label : V → Fin 29) (M : Multiset (Fin 29) → E)
    (a b : V) (ne : a ≠ b) : projectedMoment label M (clausePoly {(a,true),(b,true)}) =
      M 0 + M {label a} + M {label b} + M {label a, label b} := by
  classical
  have hp : clausePoly ({(a,true),(b,true)} : Clause V) =
      (1 : MvPolynomial V (ZMod 2)) + X a + X b + X a * X b := by
    simp [clausePoly, ne] <;> ring
  rw [hp, map_add, map_add, map_add, moment_unit, moment_x, moment_x, moment_xx]

lemma moment_imp (label : V → Fin 29) (M : Multiset (Fin 29) → E) (a b : V) :
    projectedMoment label M (clausePoly {(a,false),(b,true)}) = M {label a} + M {label a,label b} := by
  classical
  have hp : clausePoly ({(a,false),(b,true)} : Clause V) =
      (X a : MvPolynomial V (ZMod 2)) + X a * X b := by simp [clausePoly] <;> ring
  rw [hp, map_add, moment_x, moment_xx]

lemma moment_two_imp (label : V → Fin 29) (M : Multiset (Fin 29) → E) (a b c : V) (ne : a ≠ b) :
    projectedMoment label M (clausePoly {(a,false),(b,false),(c,true)}) =
       M {label a,label b} + M {label a,label b,label c} := by
  classical
  have hp : clausePoly ({(a,false),(b,false),(c,true)} : Clause V) =
      (X a : MvPolynomial V (ZMod 2)) * X b + X a * X b * X c := by
    simp [clausePoly, ne] <;> ring
  rw [hp, map_add, moment_xx, moment_xxx]

lemma moment_nand (label : V → Fin 29) (M : Multiset (Fin 29) → E) (a b : V) (ne : a ≠ b) :
    projectedMoment label M (clausePoly {(a,false),(b,false)}) = M {label a,label b} := by
  classical
  have hp : clausePoly ({(a,false),(b,false)} : Clause V) =
      (X a : MvPolynomial V (ZMod 2)) * X b := by simp [clausePoly, ne]
  rw [hp, moment_xx]

lemma moment_uneg (label : V → Fin 29) (M : Multiset (Fin 29) → E) (a : V) :
    projectedMoment label M (clausePoly {(a,false)}) = M {label a} := by
  simpa [clausePoly] using moment_x label M a

def k104x (n : ℕ) : Fin 29 := Fin.ofNat 29 n

def k104s (i j : ℕ) : Fin 29 := Fin.ofNat 29 (8 + 3*i+j)

def k104label : Fin 8 ⊕ (ℕ × ℕ) → Fin 29
  | .inl i => k104x i.val
  | .inr (i,j) => k104s i j

def k104edges : List (Fin 8 × Fin 8) := [(0, 4), (0, 5), (0, 6), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7)]

def k104formula : Set (Clause (Fin 8 ⊕ (ℕ × ℕ))) :=
  {Cek | ∃ eek ∈ (k104edges : List (Fin 8 × Fin 8)), Cek = {(((Sum.inl eek.1) : Fin 8 ⊕ (ℕ × ℕ)), true), (((Sum.inl eek.2) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cak | ∃ iak : Fin 8, iak.val + 1 < 8 ∧ Cak = {(((Sum.inl iak) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (iak.val, 0)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbk | ∃ (ibk : Fin 8) (hbk jbk : ℕ), ibk.val = hbk + 1 ∧ ibk.val + 1 < 8 ∧ jbk < 3 ∧ Cbk = {(((Sum.inr (hbk, jbk)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibk.val, jbk)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cck | ∃ (ick : Fin 8) (hck gck : ℕ), ick.val = hck + 1 ∧ ick.val + 1 < 8 ∧ gck + 1 < 3 ∧ Cck = {(((Sum.inl ick) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hck, gck)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ick.val, gck + 1)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cdk | ∃ (idk : Fin 8) (hdk : ℕ), idk.val = hdk + 1 ∧ Cdk = {(((Sum.inl idk) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hdk, 2)) : Fin 8 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfk | ∃ jfk : ℕ, 1 ≤ jfk ∧ jfk < 3 ∧ Cfk = {(((Sum.inr (0, jfk)) : Fin 8 ⊕ (ℕ × ℕ)), false)}}

def k104values (M : Multiset (Fin 29) → E) : Prop :=
  (∀ e ∈ k104edges, M 0 + M {k104x e.1.val} + M {k104x e.2.val} + M {k104x e.1.val, k104x e.2.val} = 0) ∧
  (∀ i : Fin 7, M {k104x i.val} + M {k104x i.val,k104s i.val 0} = 0) ∧
  (∀ (h : Fin 6) (j : Fin 3), M {k104s h.val j.val} + M {k104s h.val j.val,k104s (h.val+1) j.val} = 0) ∧
  (∀ (h : Fin 6) (g : Fin 2), M {k104x (h.val+1),k104s h.val g.val} +
    M {k104x (h.val+1),k104s h.val g.val,k104s (h.val+1) (g.val+1)} = 0) ∧
  (∀ h : Fin 7, M {k104x (h.val+1),k104s h.val 2} = 0) ∧
  (∀ g : Fin 2, M {k104s 0 (g.val+1)} = 0)

lemma k104axioms (M : Multiset (Fin 29) → E) (hs : k104values M)
    (bo : ∀ i, M {i,i} + M {i} = 0) (p : MvPolynomial (Fin 8 ⊕ (ℕ × ℕ)) (ZMod 2)) (hp : p ∈ cnfSystem k104formula) : projectedMoment k104label M p = 0 := by
  classical
  obtain ⟨hE, h0, hM, hI, hC, hN⟩ := hs
  rcases hp with ⟨j,rfl⟩ | ⟨C,hC',rfl⟩
  · rw [map_add, moment_xx, moment_x]
    exact bo _
  · simp only [k104formula, Set.mem_union, Set.mem_setOf_eq] at hC'
    simp only [or_assoc] at hC'
    rcases hC' with ⟨e,he,rfl⟩ | ⟨i,hi,rfl⟩ | ⟨i,h,j,eqi,hi,hj,rfl⟩ |
      ⟨i,h,g,eqi,hi,hg,rfl⟩ | ⟨i,h,eqi,rfl⟩ | ⟨j,hj,hj',rfl⟩
    · have hn : e.1 ≠ e.2 := ((show ∀ e ∈ k104edges, e.1 ≠ e.2 by decide) e he)
      rw [moment_binary_pos k104label M _ _ (by simpa using hn)]
      exact hE e he
    · rw [moment_imp]
      exact h0 ⟨i.val,by omega⟩
    · rw [moment_imp]
      simp only [k104label, eqi]
      exact hM ⟨h,by omega⟩ ⟨j,hj⟩
    · rw [moment_two_imp k104label M _ _ _ (by simp)]
      simp only [k104label, eqi]
      exact hI ⟨h,by omega⟩ ⟨g,by omega⟩
    · rw [moment_nand k104label M _ _ (by simp)]
      simp only [k104label, eqi]
      exact hC ⟨h,by omega⟩
    · rw [moment_uneg]
      change M {k104s 0 j} = 0
      obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      exact hN ⟨g,by omega⟩

lemma k104nonref (M : Multiset (Fin 29) → E) (T : Fin 29 → E →ₗ[ZMod 2] E)
    (hc : ∀ (i : Fin 29) (s : Multiset (Fin 29)), s.card ≤ 2 → M (i ::ₘ s) = T i (M s))
    (bo : ∀ i, M {i,i} + M {i} = 0) (hne : M 0 ≠ 0) (hs : k104values M) :
    ¬ PCRefutable (cnfSystem k104formula) 3 := by
  apply pc_obstruction (projectedMoment k104label M) (fun j => T (k104label j))
  · exact projected_compat k104label M T hc
  · exact fun p hp _ => k104axioms M hs bo p hp
  · simpa [moment_unit] using hne

def k104words (M : Multiset (Fin 29) → ℕ) : Prop :=
  (∀ e ∈ k104edges, M 0 ^^^ M {k104x e.1.val} ^^^ M {k104x e.2.val} ^^^ M {k104x e.1.val, k104x e.2.val} = 0) ∧
  (∀ i : Fin 7, M {k104x i.val} ^^^ M {k104x i.val,k104s i.val 0} = 0) ∧
  (∀ (h : Fin 6) (j : Fin 3), M {k104s h.val j.val} ^^^ M {k104s h.val j.val,k104s (h.val+1) j.val} = 0) ∧
  (∀ (h : Fin 6) (g : Fin 2), M {k104x (h.val+1),k104s h.val g.val} ^^^
    M {k104x (h.val+1),k104s h.val g.val,k104s (h.val+1) (g.val+1)} = 0) ∧
  (∀ h : Fin 7, M {k104x (h.val+1),k104s h.val 2} = 0) ∧
  (∀ g : Fin 2, M {k104s 0 (g.val+1)} = 0)

lemma k104fromWords (N : Multiset (Fin 29) → ℕ) (G : ℕ → E) (gz : G 0 = 0)
    (gx : ∀ a b, G (a ^^^ b) = G a + G b) (h : k104words N) : k104values (fun s => G (N s)) := by
  obtain ⟨hE,h0,hM,hI,hC,hN⟩ := h
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro e he
    rw [← gx, ← gx, ← gx, hE e he, gz]
  · intro i
    rw [← gx, h0 i, gz]
  · intro i j
    rw [← gx, hM i j, gz]
  · intro i j
    rw [← gx, hI i j, gz]
  · intro i
    exact (congrArg G (hC i)).trans gz
  · intro i
    exact (congrArg G (hN i)).trans gz

end PEqualNP.Outside.L_pcx_103

namespace PEqualNP.Outside.L_pcx_103

abbrev SyndromeSpace := Fin 146 → ZMod 2

def syndromeWord (w : ℕ) : SyndromeSpace := fun k => if w.testBit k.val then 1 else 0

lemma syndromeWord_zero : syndromeWord 0 = 0 := by
  funext k
  simp [syndromeWord]

lemma syndromeWord_xor (a b : ℕ) : syndromeWord (a ^^^ b) = syndromeWord a + syndromeWord b := by
  funext k
  simp only [syndromeWord, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit k.val <;> cases b.testBit k.val <;> decide

private def synBasis (j : Fin 146) : SyndromeSpace := Pi.single j 1

private lemma synBasis_eq (j : Fin 146) : synBasis j = syndromeWord (2 ^ j.val) := by
  funext k
  by_cases h : j = k
  · subst k
    simp [synBasis, syndromeWord]
  · have h' : j.val ≠ k.val := fun e => h (Fin.ext e)
    simp [synBasis, syndromeWord, h', Ne.symm h]

private def synXors (f : Fin 146 → ℕ) (s : List (Fin 146)) : ℕ :=
  s.foldr (fun j t => f j ^^^ t) 0

private def synPack (s : List (Fin 146)) : ℕ := synXors (fun j => 2 ^ j.val) s

private def synMatrix (col : Fin 146 → ℕ) : SyndromeSpace →ₗ[ZMod 2] SyndromeSpace :=
  ∑ j : Fin 146, (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 146 => ZMod 2) j).smulRight (syndromeWord (col j))

private lemma synMatrix_basis (col : Fin 146 → ℕ) (j : Fin 146) :
    synMatrix col (synBasis j) = syndromeWord (col j) := by
  simp [synMatrix, synBasis, LinearMap.sum_apply, LinearMap.smulRight_apply, Pi.single_apply]

set_option maxRecDepth 8192 in
private lemma synMatrix_pack (col : Fin 146 → ℕ) (s : List (Fin 146)) :
    synMatrix col (syndromeWord (synPack s)) = syndromeWord (synXors col s) := by
  induction s with
  | nil => simp [synPack, synXors, syndromeWord_zero]
  | cons j s ih =>
    have h := congrArg (synMatrix col) (syndromeWord_xor (2 ^ j.val) (synPack s))
    rw [map_add, ← synBasis_eq j, synMatrix_basis, ih] at h
    exact h.trans (syndromeWord_xor (col j) (synXors col s)).symm


private def synMonCodes : Array (Array (ℕ)) := #[
  #[1,2,3,4,5,6,11,16,21,26,0,0,31,36,0,37,42,0,43,48,49,1,50,51,1,52,61,1,62,71,2,72],
  #[3,79,108,4,86,116,135,5,7,8,9,10,6,12,13,14,15,191,11,17,18,19,20,201,229,16,22,23,24,25,211,238],
  #[263,21,2,124,143,161,27,28,29,30,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[2,3,151,169,32,33,34,35,26,0,0,31,93,132,0,0,36,36,36,36,328,0,0,336,36,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,2,3,4,177,38,39,40,41,26,0,0,31,344,0,37,94,133,159,185,186,186,186,186,329,0],
  #[0,337,36,0,346,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,4,5,44,45,46,47,26],
  #[0,0,31,345,0,37,353,0,43,95,134,160,190,221,247,272,296,331,0,0,339,36,0,348,42,0,355,48,49,49,49,49],
  #[0,0,0,0,49,0,0,49,0,0,49,185,0,49,360,49,2,3,4,5,6,11,16,21,26,0,0,31,36,0,37,42],
  #[0,43,48,49,1,96,97,98,99,104,252,277,301,100,0,0,101,36,0,102,42,0,103,48,364,50,50,51,51,51,51,226],
  #[0,0,0,51,0,0,51,0,0,51,185,0,51,361,49,51,367,51,2,3,4,5,6,11,16,21,26,0,0,31,36,0],
  #[37,42,0,43,48,49,1,50,51,1,53,54,55,56,6,11,286,310,57,0,0,58,36,0,59,42,0,60,48,365,52,50],
  #[370,52,52,61,61,61,61,227,261,0,0,61,0,0,61,0,0,61,185,0,61,362,49,61,368,51,61,372,61,2,3,4],
  #[5,6,11,16,21,26,0,0,31,36,0,37,42,0,43,48,49,1,50,51,1,52,61,1,63,64,65,66,6,11,16,319],
  #[67,0,0,68,36,0,69,42,0,70,48,366,62,50,371,62,52,374,62,62,71,71,71,71,228,262,295,0,71,0,0,71],
  #[0,0,71,185,0,71,363,49,71,369,51,71,373,61,71,375,71,2,72,72,3,79,376,108,79,108,4,86,377,116,381,385],
  #[135,86,116,135,5,7,73,8,80,109,9,87,117,136,10,7,8,9,10,6,12,74,13,81,110,14,88,118,137,15,192,193],
  #[194,195,191,12,13,14,15,191,11,17,75,18,82,111,19,89,119,138,20,202,203,204,205,201,230,231,232,233,401,229,17,18],
  #[19,20,201,229,16,22,76,23,83,112,24,90,120,139,25,212,213,214,215,211,239,240,241,242,402,238,264,265,266,267,406,412],
  #[263,22,23,24,25,211,238,263,21,2,72,124,79,386,143,86,389,393,161,7,125,144,162,27,12,126,145,163,196,28,17,127],
  #[146,164,206,234,29,22,128,147,165,216,243,268,30,2,124,143,161,27,28,29,30,26,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,72,3,79,108,151,86,116,394,169,7,8,152,170,32,12,13],
  #[153,171,197,33,17,18,154,172,207,235,34,22,23,155,173,217,244,269,35,2,124,143,161,27,28,29,30,26,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,151,169,32,33,34,35,26,0,0,31,93,378,132],
  #[0,0,0,0,0,0,0,93,132,0,0,36,93,132,0,0,36,36,93,132,0,0,36,36,36,93,132,0,0,36,36,36],
  #[36,93,124,0,0,328,328,328,328,328,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,93],
  #[132,0,0,336,336,336,336,328,0,0,336,93,132,0,0,36,36,36,36,328,0,0,336,36,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,2,72,3,79,108,4,86,116,135,177,7,8,9,178,38,12,13,14,179,198,39,17,18,19,180,208,236,40,22,23,24],
  #[181,218,245,270,41,2,124,143,161,27,28,29,30,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,2,3,151,169,32,33,34,35,26,0,0,31,93,132,0,0,344,344,344,344,328,0,0,336,344,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,2,3,4,177,38,39,40,41,26,0,0,31,344,0,37,94,379,133,382,387,159,185],
  #[185,185,185,187,188,189,0,186,187,188,189,0,186,186,187,188,189,0,186,186,186,187,188,189,0,186,186,186,186,94,391,396],
  #[185,330,330,330,330,329,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,94,133,151,185,338],
  #[338,338,338,329,0,0,337,93,132,0,0,36,36,36,36,328,0,0,336,36,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,94,133,159,185,347,347,347,347,329,0,0,337,344,0,346,94,133,159,185,186,186,186,186,329,0,0,337,36,0,346],
  #[42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,72,3,79,108,4],
  #[86,116,135,5,7,8,9,10,44,12,13,14,15,199,45,17,18,19,20,209,237,46,22,23,24,25,219,246,271,47,2,124],
  #[143,161,27,28,29,30,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,151,169],
  #[32,33,34,35,26,0,0,31,93,132,0,0,345,345,345,345,328,0,0,336,345,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,2,3,4,177,38,39,40,41,26,0,0,31,344,0,37,94,133,159,185,354,354,354,354,329,0,0,337,345,0],
  #[346,353,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,4,5,44,45,46,47,26,0,0,31,345],
  #[0,37,353,0,43,95,380,134,383,388,160,384,390,395,190,222,223,224,225,221,248,249,250,251,403,247,273,274,275,276,407,413],
  #[272,297,298,299,300,409,416,421,296,95,392,397,399,332,333,334,335,331,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,95,134,398,400,340,341,342,343,331,0,0,339,93,132,0,0,36,36,36,36,328,0,0,336,36],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,95,134,160,177,349,350,351,352,331,0,0,339,344,0,348,94,133,159],
  #[185,186,186,186,186,329,0,0,337,36,0,346,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,95,134],
  #[160,190,356,357,358,359,331,0,0,339,345,0,348,353,0,355,95,134,160,190,221,247,272,296,331,0,0,339,36,0,348,42],
  #[0,355,48,49,49,49,49,49,49,49,49,49,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,49,49,49,49,0,0,0,0,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,49,49,49,49,0,0,0,0,49,0,0,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,49,49,49,49,0,0,0,0,49,0,0,49,0,0,49,185,185,185,185,0],
  #[0,0,0,185,0,0,185,0,0,185,185,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,49,49,49,49],
  #[0,0,0,0,49,0,0,49,0,0,49,185,0,49,360,360,360,360,0,0,0,0,360,0,0,360,0,0,360,185,0,360],
  #[360,49,49,49,49,0,0,0,0,49,0,0,49,0,0,49,185,0,49,360,49,2,72,3,79,108,4,86,116,135,5,7],
  #[8,9,10,6,12,13,14,15,191,11,17,18,19,20,201,229,16,22,23,24,25,211,238,263,21,2,124,143,161,27,28,29],
  #[30,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,151,169,32,33,34,35,26],
  #[0,0,31,93,132,0,0,36,36,36,36,328,0,0,336,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3],
  #[4,177,38,39,40,41,26,0,0,31,344,0,37,94,133,159,185,186,186,186,186,329,0,0,337,36,0,346,42,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,4,5,44,45,46,47,26,0,0,31,345,0,37,353,0,43],
  #[95,134,160,190,221,247,272,296,331,0,0,339,36,0,348,42,0,355,48,49,49,49,49,0,0,0,0,49,0,0,49,0],
  #[0,49,185,0,49,360,49,2,3,4,5,6,11,16,21,26,0,0,31,36,0,37,42,0,43,48,49,1,96,105,97,106],
  #[115,98,107,123,142,99,7,8,9,10,104,253,254,255,256,200,252,278,279,280,281,210,414,277,302,303,304,305,220,417,422,301],
  #[96,131,150,168,27,257,282,306,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,97],
  #[158,176,32,258,283,307,100,0,0,101,93,132,0,0,36,36,36,36,328,0,0,336,36,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,96,97,98,184,38,259,284,308,100,0,0,101,344,0,102,94,133,159,185,186,186,186,186,329,0,0,337],
  #[36,0,346,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,97,98,99,44,260,285,309,100,0,0],
  #[101,345,0,102,353,0,103,95,134,160,190,221,247,272,296,331,0,0,339,36,0,348,42,0,355,48,364,364,364,364,0,0],
  #[0,0,364,0,0,364,0,0,364,185,0,364,360,364,96,97,98,99,104,252,277,301,100,0,0,101,36,0,102,42,0,103],
  #[48,364,50,96,97,98,99,104,252,277,301,100,0,0,101,36,0,102,42,0,103,48,364,50,50,51,51,51,51,51,51,51],
  #[51,51,51,226,226,226,226,226,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,51,51,51],
  #[51,226,0,0,0,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,51,51,51,51,226],
  #[0,0,0,51,0,0,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,51,51,51,51,226,0,0,0,51,0,0,51,0,0,51,185,185,185,185,0,0,0,0,185,0,0,185,0,0,185],
  #[185,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,51,51,51,51,226,0,0,0,51,0,0,51,0,0],
  #[51,185,0,51,361,361,361,361,221,0,0,0,361,0,0,361,0,0,361,185,0,361,361,49,49,49,49,0,0,0,0,49],
  #[0,0,49,0,0,49,185,0,49,360,49,51,51,51,51,226,0,0,0,51,0,0,51,0,0,51,185,0,51,361,49,51],
  #[367,367,367,367,226,0,0,0,367,0,0,367,0,0,367,185,0,367,361,364,367,367,51,51,51,51,226,0,0,0,51,0],
  #[0,51,0,0,51,185,0,51,361,49,51,367,51,2,72,3,79,108,4,86,116,135,5,7,8,9,10,6,12,13,14,15],
  #[191,11,17,18,19,20,201,229,16,22,23,24,25,211,238,263,21,2,124,143,161,27,28,29,30,26,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,151,169,32,33,34,35,26,0,0,31,93,132,0,0,36],
  #[36,36,36,328,0,0,336,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,4,177,38,39,40,41,26,0],
  #[0,31,344,0,37,94,133,159,185,186,186,186,186,329,0,0,337,36,0,346,42,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,2,3,4,5,44,45,46,47,26,0,0,31,345,0,37,353,0,43,95,134,160,190,221,247,272,296],
  #[331,0,0,339,36,0,348,42,0,355,48,49,49,49,49,0,0,0,0,49,0,0,49,0,0,49,185,0,49,360,49,2],
  #[3,4,5,6,11,16,21,26,0,0,31,36,0,37,42,0,43,48,49,1,96,97,98,99,104,252,277,301,100,0,0,101],
  #[36,0,102,42,0,103,48,364,50,50,51,51,51,51,226,0,0,0,51,0,0,51,0,0,51,185,0,51,361,49,51,367],
  #[51,2,3,4,5,6,11,16,21,26,0,0,31,36,0,37,42,0,43,48,49,1,50,51,1,53,77,54,84,113,55,91],
  #[121,140,56,7,8,9,10,6,12,13,14,15,191,11,287,288,289,290,201,229,286,311,312,313,314,211,238,423,310,53,129,148],
  #[166,27,28,291,315,57,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,53,54,156,174,32],
  #[33,292,316,57,0,0,58,93,132,0,0,36,36,36,36,328,0,0,336,36,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,53,54,55,182,38,39,293,317,57,0,0,58,344,0,59,94,133,159,185,186,186,186,186,329,0,0,337,36,0,346],
  #[42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,53,54,55,56,44,45,294,318,57,0,0,58,345,0],
  #[59,353,0,60,95,134,160,190,221,247,272,296,331,0,0,339,36,0,348,42,0,355,48,365,365,365,365,0,0,0,0,365],
  #[0,0,365,0,0,365,185,0,365,360,365,53,54,55,56,6,11,286,310,57,0,0,58,36,0,59,42,0,60,48,365,52],
  #[96,97,98,99,104,252,277,301,100,0,0,101,36,0,102,42,0,103,48,364,50,50,370,370,370,370,226,0,0,0,370,0],
  #[0,370,0,0,370,185,0,370,361,365,370,367,370,53,54,55,56,6,11,286,310,57,0,0,58,36,0,59,42,0,60,48],
  #[365,52,50,370,52,53,54,55,56,6,11,286,310,57,0,0,58,36,0,59,42,0,60,48,365,52,50,370,52,52,61,61],
  #[61,61,61,61,61,61,61,61,227,227,227,227,227,261,261,261,261,404,261,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,61,61,61,61,227,261,0,0,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[61,61,61,61,227,261,0,0,61,0,0,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,61,61,61,61,227,261,0,0,61,0,0,61,0,0,61,185,185,185,185,0,0,0,0,185,0],
  #[0,185,0,0,185,185,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,61,61,61,61,227,261,0,0,61],
  #[0,0,61,0,0,61,185,0,61,362,362,362,362,410,418,0,0,362,0,0,362,0,0,362,185,0,362,362,49,49,49,49],
  #[0,0,0,0,49,0,0,49,0,0,49,185,0,49,360,49,61,61,61,61,227,261,0,0,61,0,0,61,0,0,61,185],
  #[0,61,362,49,61,368,368,368,368,227,252,0,0,368,0,0,368,0,0,368,185,0,368,362,364,368,368,51,51,51,51,226],
  #[0,0,0,51,0,0,51,0,0,51,185,0,51,361,49,51,367,51,61,61,61,61,227,261,0,0,61,0,0,61,0,0],
  #[61,185,0,61,362,49,61,368,51,61,372,372,372,372,227,261,0,0,372,0,0,372,0,0,372,185,0,372,362,365,372,368],
  #[370,372,372,61,61,61,61,227,261,0,0,61,0,0,61,0,0,61,185,0,61,362,49,61,368,51,61,372,61,2,72,3],
  #[79,108,4,86,116,135,5,7,8,9,10,6,12,13,14,15,191,11,17,18,19,20,201,229,16,22,23,24,25,211,238,263],
  #[21,2,124,143,161,27,28,29,30,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2],
  #[3,151,169,32,33,34,35,26,0,0,31,93,132,0,0,36,36,36,36,328,0,0,336,36,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,2,3,4,177,38,39,40,41,26,0,0,31,344,0,37,94,133,159,185,186,186,186,186,329,0,0],
  #[337,36,0,346,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,4,5,44,45,46,47,26,0],
  #[0,31,345,0,37,353,0,43,95,134,160,190,221,247,272,296,331,0,0,339,36,0,348,42,0,355,48,49,49,49,49,0],
  #[0,0,0,49,0,0,49,0,0,49,185,0,49,360,49,2,3,4,5,6,11,16,21,26,0,0,31,36,0,37,42,0],
  #[43,48,49,1,96,97,98,99,104,252,277,301,100,0,0,101,36,0,102,42,0,103,48,364,50,50,51,51,51,51,226,0],
  #[0,0,51,0,0,51,0,0,51,185,0,51,361,49,51,367,51,2,3,4,5,6,11,16,21,26,0,0,31,36,0,37],
  #[42,0,43,48,49,1,50,51,1,53,54,55,56,6,11,286,310,57,0,0,58,36,0,59,42,0,60,48,365,52,50,370],
  #[52,52,61,61,61,61,227,261,0,0,61,0,0,61,0,0,61,185,0,61,362,49,61,368,51,61,372,61,2,3,4,5],
  #[6,11,16,21,26,0,0,31,36,0,37,42,0,43,48,49,1,50,51,1,52,61,1,63,78,64,85,114,65,92,122,141],
  #[66,7,8,9,10,6,12,13,14,15,191,11,17,18,19,20,201,229,16,320,321,322,323,211,238,263,319,63,130,149,167,27],
  #[28,29,324,67,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,63,64,157,175,32,33,34],
  #[325,67,0,0,68,93,132,0,0,36,36,36,36,328,0,0,336,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[63,64,65,183,38,39,40,326,67,0,0,68,344,0,69,94,133,159,185,186,186,186,186,329,0,0,337,36,0,346,42,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,63,64,65,66,44,45,46,327,67,0,0,68,345,0,69,353],
  #[0,70,95,134,160,190,221,247,272,296,331,0,0,339,36,0,348,42,0,355,48,366,366,366,366,0,0,0,0,366,0,0],
  #[366,0,0,366,185,0,366,360,366,63,64,65,66,6,11,16,319,67,0,0,68,36,0,69,42,0,70,48,366,62,96,97],
  #[98,99,104,252,277,301,100,0,0,101,36,0,102,42,0,103,48,364,50,50,371,371,371,371,226,0,0,0,371,0,0,371],
  #[0,0,371,185,0,371,361,366,371,367,371,63,64,65,66,6,11,16,319,67,0,0,68,36,0,69,42,0,70,48,366,62],
  #[50,371,62,53,54,55,56,6,11,286,310,57,0,0,58,36,0,59,42,0,60,48,365,52,50,370,52,52,374,374,374,374],
  #[227,261,0,0,374,0,0,374,0,0,374,185,0,374,362,366,374,368,371,374,372,374,63,64,65,66,6,11,16,319,67,0],
  #[0,68,36,0,69,42,0,70,48,366,62,50,371,62,52,374,62,63,64,65,66,6,11,16,319,67,0,0,68,36,0,69],
  #[42,0,70,48,366,62,50,371,62,52,374,62,62,71,71,71,71,71,71,71,71,71,71,228,228,228,228,228,262,262,262,262],
  #[405,262,295,295,295,295,408,415,295,0,0,0,0,0,0,0,0,71,71,71,71,228,262,295,0,71,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,71,71,71,71,228,262,295,0,71,0,0,71,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,71,71,71,71,228,262,295,0,71,0],
  #[0,71,0,0,71,185,185,185,185,0,0,0,0,185,0,0,185,0,0,185,185,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,71,71,71,71,228,262,295,0,71,0,0,71,0,0,71,185,0,71,363,363,363,363,411,419,424,0],
  #[363,0,0,363,0,0,363,185,0,363,363,49,49,49,49,0,0,0,0,49,0,0,49,0,0,49,185,0,49,360,49,71],
  #[71,71,71,228,262,295,0,71,0,0,71,0,0,71,185,0,71,363,49,71,369,369,369,369,228,420,425,0,369,0,0,369],
  #[0,0,369,185,0,369,363,364,369,369,51,51,51,51,226,0,0,0,51,0,0,51,0,0,51,185,0,51,361,49,51,367],
  #[51,71,71,71,71,228,262,295,0,71,0,0,71,0,0,71,185,0,71,363,49,71,369,51,71,373,373,373,373,228,262,286],
  #[0,373,0,0,373,0,0,373,185,0,373,363,365,373,369,370,373,373,61,61,61,61,227,261,0,0,61,0,0,61,0,0],
  #[61,185,0,61,362,49,61,368,51,61,372,61,71,71,71,71,228,262,295,0,71,0,0,71,0,0,71,185,0,71,363,49],
  #[71,369,51,71,373,61,71,375,375,375,375,228,262,295,0,375,0,0,375,0,0,375,185,0,375,363,366,375,369,371,375,373],
  #[374,375,375,71,71,71,71,228,262,295,0,71,0,0,71,0,0,71,185,0,71,363,49,71,369,51,71,373,61,71,375,71]
]
private def synSparseWords : Array (Array (List (Fin 146))) := #[
  #[[],[0],[1],[2],[3],[4],[5],[0,1,5],[0,2,5],[0,3,5],[0,4,5],[6],[0,1,6],[0,2,6],[0,3,6],[0,4,6],[7],[0,1,7],[0,2,7],[0,3,7],[0,4,7],[8],[0,1,8],[0,2,8],[0,3,8],[0,4,8],[9],[0,5,9],[0,6,9],[0,7,9],[0,8,9],[10]],
  #[[0,5,10],[0,6,10],[0,7,10],[0,8,10],[11],[12],[0,5,12],[0,6,12],[0,7,12],[0,8,12],[13],[14],[0,5,14],[0,6,14],[0,7,14],[0,8,14],[15],[16],[17],[18],[19],[0,1,19],[0,2,19],[0,3,19],[0,4,19],[0,9,19],[0,10,19],[0,12,19],[0,14,19],[20],[21],[0,1,21]],
  #[[0,2,21],[0,3,21],[0,4,21],[0,9,21],[0,10,21],[0,12,21],[0,14,21],[22],[23],[0,5,23],[0,6,23],[0,7,23],[0,8,23],[0,19,23],[0,21,23],[24],[0,5,24],[0,6,24],[0,7,24],[0,8,24],[0,19,24],[0,21,24],[25],[0,5,25],[0,6,25],[0,7,25],[0,8,25],[0,19,25],[0,21,25],[26],[27],[28]],
  #[[29],[1,2,29],[1,3,29],[1,4,29],[1,9,29],[1,10,29],[1,12,29],[1,14,29],[0,1,5,17,29],[1,23,29],[1,24,29],[1,25,29],[30],[0,5,30],[0,6,30],[0,7,30],[0,8,30],[0,19,30],[0,21,30],[1,29,30],[31],[0,5,31],[0,6,31],[0,7,31],[0,8,31],[0,19,31],[0,21,31],[1,29,31],[32],[0,5,32],[0,6,32],[0,7,32]],
  #[[0,8,32],[0,19,32],[0,21,32],[1,29,32],[33],[34],[35],[36],[0,5,36],[0,6,36],[0,7,36],[0,8,36],[0,19,36],[0,21,36],[1,29,36],[37],[0,5,37],[0,6,37],[0,7,37],[0,8,37],[0,19,37],[0,21,37],[1,29,37],[38],[0,5,38],[0,6,38],[0,7,38],[0,8,38],[0,19,38],[0,21,38],[1,29,38],[39]],
  #[[40],[41],[0,5,41],[0,6,41],[0,7,41],[0,8,41],[0,19,41],[0,21,41],[1,29,41],[42],[0,5,42],[0,6,42],[0,7,42],[0,8,42],[0,19,42],[0,21,42],[1,29,42],[43],[0,5,43],[0,6,43],[0,7,43],[0,8,43],[0,19,43],[0,21,43],[1,29,43],[44],[13,44],[27,44],[34,44],[39,44],[45],[46]],
  #[[0,1,46],[0,2,46],[0,3,46],[0,4,46],[0,9,46],[0,10,46],[0,12,46],[0,14,46],[0,1,17,29,46],[47],[0,1,47],[0,2,47],[0,3,47],[0,4,47],[0,9,47],[0,10,47],[0,12,47],[0,14,47],[0,1,17,29,47],[48],[0,1,48],[0,2,48],[0,3,48],[0,4,48],[0,9,48],[0,10,48],[0,12,48],[0,14,48],[0,1,17,29,48],[49],[15,28,49],[15,35,49]],
  #[[15,40,49],[15,45,49],[50],[51],[52],[53],[0,1,53],[0,2,53],[0,3,53],[0,4,53],[0,9,53],[0,10,53],[0,12,53],[0,14,53],[54],[0,1,54],[0,2,54],[0,3,54],[0,4,54],[0,9,54],[0,10,54],[0,12,54],[0,14,54],[55],[15,28,55],[15,35,55],[15,40,55],[15,45,55],[56],[17,29,56],[1,2,17,29,56],[1,3,17,29,56]],
  #[[1,4,17,29,56],[1,9,17,29,56],[1,10,17,29,56],[1,12,17,29,56],[1,14,17,29,56],[57],[58],[59],[0,1,59],[0,2,59],[0,3,59],[0,4,59],[0,9,59],[0,10,59],[0,12,59],[0,14,59],[60],[15,28,60],[15,35,60],[15,40,60],[15,45,60],[61],[17,29,61],[1,2,17,29,61],[1,3,17,29,61],[1,4,17,29,61],[1,9,17,29,61],[1,10,17,29,61],[1,12,17,29,61],[1,14,17,29,61],[62],[0,1,62]],
  #[[0,2,62],[0,3,62],[0,4,62],[0,9,62],[0,10,62],[0,12,62],[0,14,62],[63],[64],[15,28,64],[15,35,64],[15,40,64],[15,45,64],[65],[17,29,65],[1,2,17,29,65],[1,3,17,29,65],[1,4,17,29,65],[1,9,17,29,65],[1,10,17,29,65],[1,12,17,29,65],[1,14,17,29,65],[66],[0,1,66],[0,2,66],[0,3,66],[0,4,66],[0,9,66],[0,10,66],[0,12,66],[0,14,66],[67]],
  #[[0,1,67],[0,2,67],[0,3,67],[0,4,67],[0,9,67],[0,10,67],[0,12,67],[0,14,67],[68],[69],[44,69],[70],[15,49,70],[15,55,70],[15,60,70],[15,64,70],[71],[72],[44,72],[73],[15,49,73],[15,55,73],[15,60,73],[15,64,73],[74],[75],[76],[44,76],[77],[15,49,77],[15,55,77],[15,60,77]],
  #[[15,64,77],[78],[44,78],[79],[15,49,79],[15,55,79],[15,60,79],[15,64,79],[80],[81],[82],[83],[84],[85],[86],[87],[88],[89],[90],[91],[92],[93],[94],[95],[96],[97],[98],[99],[100],[101],[102],[103]],
  #[[104],[105],[106],[107],[108],[109],[110],[111],[112],[113],[114],[115],[116],[117],[118],[119],[120],[121],[122],[123],[124],[125],[126],[127],[128],[129],[130],[131],[132],[133],[134],[135]],
  #[[136],[137],[138],[139],[140],[141],[142],[143],[144],[145]]
]
private def synMatrixWords : Array (Array (ℕ)) := #[
  #[2,2,8388608,16777216,33554432,35,67,131,259,2,2,67108864,2,134217728,2,268435456,65536,536870912,262144,524291,1048576,2097155,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,79228162514264337593543950336,158456325028528675187087900672],
  #[8388608,316912650057057350374175801344,633825300114114700748351602688,1267650600228229401496703205376,2535301200456458802993406410752,16777216,16777216,5070602400912917605986812821504,10141204801825835211973625643008,33554432,33554432,33554432,17592186044416,20282409603651670423947251286016,70368744177667,140737488355331,281474976710659,562950221889536,1125899906842624,2251799813685248,4503599627370496,9007199254740995,18014398509481987,36028797287432192,72057594574929920,144115188075855872,288230376151711744,576460752303423491,1152921504875315200,2305843009750695936,4611686018427387907,9223372036854775808],
  #[18446744073978019840,36893488147956105216,73786976294838206467,147573952589676412931,67108864,134217728,268435456,67108864,134217728,268435456,67108864,67108864,134217728,268435456,134217728,268435456,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168],
  #[4,8388608,4,1073741824,2147483648,37,69,133,261,4294967296,4,8589934592,4,17179869184,4,34359738368,65536,536870918,262144,524293,1048576,2097157,4194304,8388608,79228162514264337593543950336,158456325028528675187087900672,316912650057057350374175801344,633825300114114700748351602688,1267650600228229401496703205376,545259522,1073741824,2147483648],
  #[4294967296,8589934592,17179869184,34359738368,40564819207303340847894502572032,81129638414606681695789005144064,1073741824,162259276829213363391578010288128,324518553658426726783156020576256,649037107316853453566312041152512,2147483648,2147483648,17592186044416,1298074214633706907132624082305024,70368744177669,140737488355333,281474976710661,562984313192448,1125899906842624,2251799813685248,4503599627370496,9007199254740997,18014398509481989,36028831378735104,72057594574929926,144115188075855872,288230376151711744,576460752303423493,1152921538966618112,2305843009750695942,4611686018427387909,9223372036854775808],
  #[18446744108069322752,36893488147956105222,73786976294838206469,147573952589676412933,4294967296,2596148429267413814265248164610048,5192296858534827628530496329220096,8589934592,17179869184,34359738368,8589934592,8589934592,17179869184,34359738368,17179869184,34359738368,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168],
  #[8,16777216,1073741824,8,68719476736,41,73,137,265,137438953472,274877906944,0,8,549755813888,8,1099511627776,65536,536870922,262144,524297,1048576,2097161,4194304,79228162514264337593543950336,16777216,2535301200456458802993406410752,0,5070602400912917605986812821504,10141204801825835211973625643008,553648130,1073741824,40564819207303340847894502572032],
  #[81129638414606681695789005144064,0,162259276829213363391578010288128,324518553658426726783156020576256,68719476736,137438953472,274877906944,549755813888,1099511627776,10384593717069655257060992658440192,20769187434139310514121985316880384,68719476736,17592186044416,41538374868278621028243970633760768,70368744177673,140737488355337,281474976710665,564049465081856,1125899906842624,2251799813685248,4503599627370496,9007199254741001,18014398509481993,36029896530624512,72057594574929930,144115188075855872,288230376151711744,576460752303423497,1152922604118507520,2305843009750695946,4611686018427387913,9223372036854775808],
  #[18446745173221212160,36893488147956105226,73786976294838206473,147573952589676412937,0,83076749736557242056487941267521536,166153499473114484112975882535043072,0,274877906944,332306998946228968225951765070086144,0,0,549755813888,1099511627776,549755813888,1099511627776,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168],
  #[16,33554432,2147483648,68719476736,16,49,81,145,273,2199023255552,4398046511104,0,8796093022208,17592186044416,16,35184372088832,65536,536870930,262144,524305,1048576,2097169,4194304,158456325028528675187087900672,2535301200456458802993406410752,33554432,0,17592186044416,20282409603651670423947251286016,570425346,40564819207303340847894502572032,2147483648],
  #[649037107316853453566312041152512,0,17592186044416,1298074214633706907132624082305024,68719476736,10384593717069655257060992658440192,20769187434139310514121985316880384,17592186044416,41538374868278621028243970633760768,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177681,140737488355345,281474976710673,598134325542912,1125899906842624,2251799813685248,4503599627370496,9007199254741009,18014398509482001,36063981391085568,72057594574929938,144115188075855872,288230376151711744,576460752303423505,1152956688978968576,2305843009750695954,4611686018427387921,9223372036854775808],
  #[18446779258081673216,36893488147956105234,73786976294838206481,147573952589676412945,0,17592186044416,664613997892457936451903530140172288,0,17592186044416,1329227995784915872903807060280344576,0,0,17592186044416,8796093022208,17592186044416,35184372088832,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168],
  #[32,35,37,41,49,32,70368744177664,140737488355328,281474976710656,545,1057,2048,4129,17592186052608,16417,562949953421312,0,537002019,1125899906842624,32,2251799813685248,32,4503599627370496,8388641,16777249,33554465,67108864,17592320262144,562950221889536,35,1073741857,2147483681],
  #[4294967329,8589934592,17609365913600,562984313192448,68719476769,137438953505,274877906977,18141941858304,564049465081856,2199023255585,4398046511137,8796093022241,0,598134325542912,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,2658455991569831745807614120560689152,5316911983139663491615228241121378304,10633823966279326983230456482242756608,70369281179651,21267647932558653966460912964485513216,42535295865117307932921825928971026432,85070591730234615865843651857942052864,170141183460469231731687303715884105728,140738025357315,140737488355328,340282366920938463463374607431768211456],
  #[680564733841876926926749214863536422912,281475513712643,281474976710656,281474976710656,295147905179352825856,590295827950891696128,1180592183667364757504,2361183241434822606848,4722366500461831258112,9444733528689243881472,18889465931478580854784,37778931862957161709568,75557863743506509463552,151115728014778600292352,302231454921249479720960,604462910370264540807168,0,562949953421312,1361129467683753853853498429727072845824,2722258935367507707706996859454145691648,0,0,0,1125899906842624,2251799813685248,4503599627370496,1125899906842624,1125899906842624,2251799813685248,4503599627370496,2251799813685248,4503599627370496],
  #[64,67,69,73,81,70368744177664,64,9007199254740992,18014398509481984,577,1089,2048,4161,17592186052608,16449,36028797018963968,0,72057594037927936,0,64,144115188075855872,64,288230376151711744,8388673,16777281,33554497,67108864,17592320262144,36028797287432192,72057594574929920,1073741889,2147483713],
  #[4294967361,8589934592,17609365913600,36028831378735104,68719476801,137438953537,274877907009,18141941858304,36029896530624512,2199023255617,4398046511169,8796093022273,0,36063981391085568,70368744177664,2658455991569831745807614120560689152,5316911983139663491615228241121378304,10633823966279326983230456482242756608,0,21267647932558653966460912964485513216,42535295865117307932921825928971026432,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,5444517870735015415413993718908291383296,10889035741470030830827987437816582766592,21778071482940061661655974875633165533184,9007199254740992,43556142965880123323311949751266331066368],
  #[87112285931760246646623899502532662132736,174224571863520493293247799005065324265472,18014398509481984,18014398509481984,295147905179352825856,590295827950891696128,1180627649514430300160,2361183241434822606848,4722366500461831258112,9444768994536309424128,18889465931478580854784,37778931862957161709568,75557863743506509463552,151115763480625665835008,302231454921249479720960,604462945836111606349824,0,0,348449143727040986586495598010130648530944,696898287454081973172991196020261297061888,0,0,0,0,72057594037927936,1393796574908163946345982392040522594123776,0,0,144115188075855872,288230376151711744,144115188075855872,288230376151711744],
  #[128,131,133,137,145,140737488355328,9007199254740992,128,576460752303423488,641,1153,2048,4225,17592186052608,16513,1152921504606846976,0,2305843009213693952,0,4611686018427387904,0,128,9223372036854775808,8388737,16777345,33554561,67108864,17592320262144,1152921504875315200,2305843009750695936,1073741953,2147483777],
  #[4294967425,8589934592,17609365913600,1152921538966618112,68719476865,137438953601,274877907073,18141941858304,1152922604118507520,2199023255681,4398046511233,8796093022337,0,1152956688978968576,2658455991569831745807614120560689152,140737488355328,85070591730234615865843651857942052864,170141183460469231731687303715884105728,0,0,340282366920938463463374607431768211456,9007199254740992,5444517870735015415413993718908291383296,10889035741470030830827987437816582766592,21778071482940061661655974875633165533184,0,43556142965880123323311949751266331066368,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808],
  #[2787593149816327892691964784081045188247552,5575186299632655785383929568162090376495104,11150372599265311570767859136324180752990208,576460752303423488,295147905179352825856,590295827950891696128,1181744542222018183168,2361183241434822606848,4722366500461831258112,9445885887243897307136,18889465931478580854784,37778931862957161709568,75557863743506509463552,151116880373333253718016,302231454921249479720960,604464062728819194232832,0,0,0,22300745198530623141535718272648361505980416,0,0,0,0,0,44601490397061246283071436545296723011960832,0,0,0,4611686018427387904,0,9223372036854775808],
  #[256,259,261,265,273,281474976710656,18014398509481984,576460752303423488,256,769,1281,2048,4353,17592186052608,16641,18446744073709551616,0,36893488147419103232,0,73786976294838206464,0,147573952589676412928,0,8388865,16777473,33554689,67108864,17592320262144,18446744073978019840,36893488147956105216,1073742081,2147483905],
  #[4294967553,8589934592,17609365913600,18446744108069322752,68719476993,137438953729,274877907201,18141941858304,18446745173221212160,2199023255809,4398046511361,8796093022465,0,18446779258081673216,5316911983139663491615228241121378304,85070591730234615865843651857942052864,281474976710656,680564733841876926926749214863536422912,0,0,0,5444517870735015415413993718908291383296,18014398509481984,87112285931760246646623899502532662132736,174224571863520493293247799005065324265472,0,0,576460752303423488,2787593149816327892691964784081045188247552,5575186299632655785383929568162090376495104,11150372599265311570767859136324180752990208,0],
  #[18446744073709551616,36893488147419103232,73786976294838206464,147573952589676412928,295147905179352825856,590295827950891696128,1199038364791120887808,2361183241434822606848,4722366500461831258112,9463179709813000011776,18889465931478580854784,37778931862957161709568,75557863743506509463552,151134174195902356422656,302231454921249479720960,604481356551388296937472,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[512,2,4294967296,137438953472,2199023255552,545,577,641,769,512,512,295147905179352825856,512,590295810358705651712,512,1180591620717411303424,65536,536871426,262144,524801,1048576,2097665,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,81129638414606681695789005144064,649037107316853453566312041152512],
  #[4294967296,4294967296,2596148429267413814265248164610048,5192296858534827628530496329220096,10384593717069655257060992658440192,137438953472,137438953472,83076749736557242056487941267521536,166153499473114484112975882535043072,2199023255552,2199023255552,2199023255552,17592186044416,664613997892457936451903530140172288,70368744178177,140737488355841,281474976711169,1180592183667364757504,1125899906842624,2251799813685248,4503599627370496,9007199254741505,18014398509482497,1180627649514430300160,72057594574930434,144115188075855872,288230376151711744,576460752303424001,1181744542222018183168,2305843009750696450,4611686018427388417,9223372036854775808],
  #[1199038364791120887808,36893488147956105730,73786976294838206977,147573952589676413441,295147905179352825856,590295810358705651712,1180591620717411303424,295147905179352825856,590295810358705651712,1180591620717411303424,295147905179352825856,295147905179352825856,590295810358705651712,1180591620717411303424,590295810358705651712,1180591620717411303424,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[1024,2,4,274877906944,4398046511104,1057,1089,1153,1281,512,1024,2361183241434822606848,1024,4722366482869645213696,1024,9444732965739290427392,65536,536871938,262144,525313,1048576,2098177,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648],
  #[4294967296,8589934592,17179869184,34359738368,20769187434139310514121985316880384,137438953472,274877906944,274877906944,332306998946228968225951765070086144,2199023255552,4398046511104,4398046511104,17592186044416,1329227995784915872903807060280344576,70368744178689,140737488356353,281474976711681,9444733528689243881472,1125899906842624,2251799813685248,4503599627370496,9007199254742017,18014398509483009,9444768994536309424128,72057594574930946,144115188075855872,288230376151711744,576460752303424513,9445885887243897307136,2305843009750696962,4611686018427388929,9223372036854775808],
  #[9463179709813000011776,36893488147956106242,73786976294838207489,147573952589676413953,295147905179352825856,590295810358705651712,1180591620717411303424,2361183241434822606848,4722366482869645213696,9444732965739290427392,2361183241434822606848,2361183241434822606848,4722366482869645213696,9444732965739290427392,4722366482869645213696,9444732965739290427392,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168],
  #[2048,67108864,8589934592,0,0,2048,2048,2048,2048,295147905179352825856,2361183241434822606848,2048,18889465931478580854784,2048,37778931862957161709568,2048,0,2048,0,2048,0,2048,0,316912650057057350374175801344,0,0,67108864,67108864,67108864,67108864,0,0],
  #[4294967296,8589934592,8589934592,8589934592,0,0,0,0,0,0,0,0,0,0,2048,2048,2048,2048,0,0,0,2048,2048,2048,2048,0,0,2048,2048,2048,2048,0],
  #[2048,2048,2048,2048,295147905179352825856,295147905179352825856,295147905179352825856,2361183241434822606848,2361183241434822606848,2361183241434822606848,18889465931478580854784,37778931862957161709568,18889465931478580854784,18889465931478580854784,37778931862957161709568,37778931862957161709568,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[4096,2,4,8,8796093022208,4129,4161,4225,4353,512,1024,18889465931478580854784,4096,75557863725914323419136,4096,151115727451828646838272,65536,536875010,262144,528385,1048576,2101249,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648],
  #[4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,8796093022208,70368744181761,140737488359425,281474976714753,151115728014778600292352,1125899906842624,2251799813685248,4503599627370496,9007199254745089,18014398509486081,151115763480625665835008,72057594574934018,144115188075855872,288230376151711744,576460752303427585,151116880373333253718016,2305843009750700034,4611686018427392001,9223372036854775808],
  #[151134174195902356422656,36893488147956109314,73786976294838210561,147573952589676417025,295147905179352825856,590295810358705651712,1180591620717411303424,2361183241434822606848,4722366482869645213696,9444732965739290427392,18889465931478580854784,18889465931478580854784,75557863725914323419136,151115727451828646838272,75557863725914323419136,151115727451828646838272,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168],
  #[8192,134217728,17179869184,549755813888,17592186044416,17592186052608,17592186052608,17592186052608,17592186052608,590295810358705651712,4722366482869645213696,2048,75557863725914323419136,8192,302231454903657293676544,8192,17592186044416,8192,17592186044416,8192,17592186044416,8192,17592186044416,633825300114114700748351602688,5070602400912917605986812821504,17592186044416,67108864,134217728,134217728,134217728,162259276829213363391578010288128,17592186044416],
  #[2596148429267413814265248164610048,8589934592,17179869184,17179869184,17592186044416,83076749736557242056487941267521536,274877906944,549755813888,549755813888,17592186044416,17592186044416,17592186044416,17592186044416,17592186044416,17592186052608,17592186052608,17592186052608,17592186052608,0,0,0,17592186052608,17592186052608,17592186052608,17592186052608,0,0,17592186052608,17592186052608,17592186052608,17592186052608,0],
  #[17592186052608,17592186052608,17592186052608,17592186052608,295147905179352825856,590295810358705651712,590295810358705651712,2361183241434822606848,4722366482869645213696,4722366482869645213696,18889465931478580854784,37778931862957161709568,75557863725914323419136,75557863725914323419136,302231454903657293676544,302231454903657293676544,17592186044416,17592186044416,17592186044416,17592186044416,17592186044416,17592186044416,17592186044416,17592186044416,17592186044416,17592186044416,17592186044416,17592186044416,17592186044416,17592186044416,17592186044416,17592186044416],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[16384,2,4,8,16,16417,16449,16513,16641,512,1024,37778931862957161709568,4096,302231454903657293676544,16384,604462909807314587353088,65536,536887298,262144,540673,1048576,2113537,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648],
  #[4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744194049,140737488371713,281474976727041,604462910370264540807168,1125899906842624,2251799813685248,4503599627370496,9007199254757377,18014398509498369,604462945836111606349824,72057594574946306,144115188075855872,288230376151711744,576460752303439873,604464062728819194232832,2305843009750712322,4611686018427404289,9223372036854775808],
  #[604481356551388296937472,36893488147956121602,73786976294838222849,147573952589676429313,295147905179352825856,590295810358705651712,1180591620717411303424,2361183241434822606848,4722366482869645213696,9444732965739290427392,18889465931478580854784,37778931862957161709568,75557863725914323419136,151115727451828646838272,302231454903657293676544,604462909807314587353088,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168],
  #[32768,268435456,34359738368,1099511627776,35184372088832,562949953421312,36028797018963968,1152921504606846976,18446744073709551616,1180591620717411303424,9444732965739290427392,2048,151115727451828646838272,8192,604462909807314587353088,32768,1208925819614629174706176,32768,2417851639229258349412352,32768,4835703278458516698824704,32768,9671406556917033397649408,1267650600228229401496703205376,10141204801825835211973625643008,20282409603651670423947251286016,67108864,134217728,268435456,268435456,324518553658426726783156020576256,1298074214633706907132624082305024],
  #[5192296858534827628530496329220096,8589934592,17179869184,34359738368,41538374868278621028243970633760768,166153499473114484112975882535043072,332306998946228968225951765070086144,549755813888,1099511627776,664613997892457936451903530140172288,1329227995784915872903807060280344576,8796093022208,17592186044416,35184372088832,10633823966279326983230456482242756608,170141183460469231731687303715884105728,680564733841876926926749214863536422912,562949953421312,562949953421312,1361129467683753853853498429727072845824,2722258935367507707706996859454145691648,10889035741470030830827987437816582766592,87112285931760246646623899502532662132736,36028797018963968,36028797018963968,348449143727040986586495598010130648530944,696898287454081973172991196020261297061888,2787593149816327892691964784081045188247552,1152921504606846976,1152921504606846976,1152921504606846976,22300745198530623141535718272648361505980416],
  #[18446744073709551616,18446744073709551616,18446744073709551616,18446744073709551616,295147905179352825856,590295810358705651712,1180591620717411303424,2361183241434822606848,4722366482869645213696,9444732965739290427392,18889465931478580854784,37778931862957161709568,75557863725914323419136,151115727451828646838272,302231454903657293676544,604462909807314587353088,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,1208925819614629174706176,1208925819614629174706176,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,2417851639229258349412352,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,4835703278458516698824704,9671406556917033397649408],
  #[65536,65536,65536,65536,65536,0,0,0,0,65536,65536,0,65536,17592186044416,65536,1208925819614629174706176,65536,19342813113834066795298816,65536,38685626227668133590597632,65536,77371252455336267181195264,65536,65536,65536,65536,0,17592186044416,1208925819614629174706176,19342813113834066795298816,65536,65536],
  #[65536,0,17592186044416,1208925819614629174706176,65536,65536,65536,17592186044416,1208925819614629174706176,65536,65536,65536,17592186044416,1208925819614629174706176,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,17592186044416,1208925819614629174706176,0,17592186044416,1208925819614629174706176,0,0,17592186044416,1208925819614629174706176,17592186044416,1208925819614629174706176,1208925819614629174706176,1208925819614629174706176,1208925819614629174706176,1208925819614629174706176,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,19342813113834066795298816,19342813113834066795298816,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,38685626227668133590597632,38685626227668133590597632,77371252455336267181195264,77371252455336267181195264],
  #[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648],
  #[4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808],
  #[18446744073709551616,36893488147419103232,73786976294838206464,147573952589676412928,295147905179352825856,590295810358705651712,1180591620717411303424,2361183241434822606848,4722366482869645213696,9444732965739290427392,18889465931478580854784,37778931862957161709568,75557863725914323419136,151115727451828646838272,302231454903657293676544,604462909807314587353088,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168],
  #[131072,536870912,536870918,536870922,536870930,537002019,72057594037927936,2305843009213693952,36893488147419103232,536871426,536871938,2048,536875010,8192,536887298,32768,19342813113834066795298816,131072,154742504910672534362390528,131072,309485009821345068724781056,131072,618970019642690137449562112,545259522,553648130,570425346,67108864,134217728,268435456,536870912,1610612738,2684354562],
  #[4831838210,8589934592,17179869184,34359738368,69256347650,137975824386,275414777858,549755813888,1099511627776,2199560126466,4398583382018,8796629893122,17592186044416,35184372088832,70369281179651,140738025357315,281475513712643,562949953421312,1125899906842624,2251799813685248,4503599627370496,21778071482940061661655974875633165533184,174224571863520493293247799005065324265472,36028797018963968,72057594037927936,72057594037927936,1393796574908163946345982392040522594123776,5575186299632655785383929568162090376495104,1152921504606846976,2305843009213693952,2305843009213693952,44601490397061246283071436545296723011960832],
  #[18446744073709551616,36893488147419103232,36893488147419103232,36893488147419103232,295147905179352825856,590295810358705651712,1180591620717411303424,2361183241434822606848,4722366482869645213696,9444732965739290427392,18889465931478580854784,37778931862957161709568,75557863725914323419136,151115727451828646838272,302231454903657293676544,604462909807314587353088,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,19342813113834066795298816,19342813113834066795298816,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,154742504910672534362390528,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,309485009821345068724781056,618970019642690137449562112],
  #[262144,262144,262144,262144,262144,1125899906842624,0,0,0,262144,262144,0,262144,17592186044416,262144,2417851639229258349412352,65536,154742504910672534362390528,262144,1237940039285380274899124224,262144,2475880078570760549798248448,262144,262144,262144,262144,0,17592186044416,2417851639229258349412352,154742504910672534362390528,262144,262144],
  #[262144,0,17592186044416,2417851639229258349412352,262144,262144,262144,17592186044416,2417851639229258349412352,262144,262144,262144,17592186044416,2417851639229258349412352,0,0,0,562949953421312,1125899906842624,1125899906842624,1125899906842624,0,0,0,0,0,0,0,0,0,0,0],
  #[0,0,0,0,0,17592186044416,2417851639229258349412352,0,17592186044416,2417851639229258349412352,0,0,17592186044416,2417851639229258349412352,17592186044416,2417851639229258349412352,1208925819614629174706176,2417851639229258349412352,2417851639229258349412352,2417851639229258349412352,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,154742504910672534362390528,154742504910672534362390528,1237940039285380274899124224,2475880078570760549798248448,1237940039285380274899124224,1237940039285380274899124224,2475880078570760549798248448,2475880078570760549798248448],
  #[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648],
  #[4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808],
  #[18446744073709551616,36893488147419103232,73786976294838206464,147573952589676412928,295147905179352825856,590295810358705651712,1180591620717411303424,2361183241434822606848,4722366482869645213696,9444732965739290427392,18889465931478580854784,37778931862957161709568,75557863725914323419136,151115727451828646838272,302231454903657293676544,604462909807314587353088,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168],
  #[524288,524291,524293,524297,524305,32,64,4611686018427387904,73786976294838206464,524801,525313,2048,528385,8192,540673,32768,38685626227668133590597632,131072,1237940039285380274899124224,524288,4951760157141521099596496896,524288,9903520314283042199192993792,8912897,17301505,34078721,67108864,134217728,268435456,536870912,1074266113,2148007937],
  #[4295491585,8589934592,17179869184,34359738368,68720001025,137439477761,274878431233,549755813888,1099511627776,2199023779841,4398047035393,8796093546497,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,11150372599265311570767859136324180752990208,1152921504606846976,2305843009213693952,4611686018427387904,4611686018427387904],
  #[18446744073709551616,36893488147419103232,73786976294838206464,73786976294838206464,295147905179352825856,590295810358705651712,1180591620717411303424,2361183241434822606848,4722366482869645213696,9444732965739290427392,18889465931478580854784,37778931862957161709568,75557863725914323419136,151115727451828646838272,302231454903657293676544,604462909807314587353088,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,38685626227668133590597632,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,1237940039285380274899124224,4951760157141521099596496896,9903520314283042199192993792,4951760157141521099596496896,9903520314283042199192993792],
  #[1048576,1048576,1048576,1048576,1048576,2251799813685248,144115188075855872,0,0,1048576,1048576,0,1048576,17592186044416,1048576,4835703278458516698824704,65536,309485009821345068724781056,262144,4951760157141521099596496896,1048576,19807040628566084398385987584,1048576,1048576,1048576,1048576,0,17592186044416,4835703278458516698824704,309485009821345068724781056,1048576,1048576],
  #[1048576,0,17592186044416,4835703278458516698824704,1048576,1048576,1048576,17592186044416,4835703278458516698824704,1048576,1048576,1048576,17592186044416,4835703278458516698824704,21267647932558653966460912964485513216,0,0,1361129467683753853853498429727072845824,1125899906842624,2251799813685248,2251799813685248,0,0,348449143727040986586495598010130648530944,72057594037927936,144115188075855872,144115188075855872,0,0,0,0,0],
  #[0,0,0,0,0,17592186044416,4835703278458516698824704,0,17592186044416,4835703278458516698824704,0,0,17592186044416,4835703278458516698824704,17592186044416,4835703278458516698824704,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,4835703278458516698824704,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,309485009821345068724781056,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,4951760157141521099596496896,19807040628566084398385987584,19807040628566084398385987584],
  #[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648],
  #[4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808],
  #[18446744073709551616,36893488147419103232,73786976294838206464,147573952589676412928,295147905179352825856,590295810358705651712,1180591620717411303424,2361183241434822606848,4722366482869645213696,9444732965739290427392,18889465931478580854784,37778931862957161709568,75557863725914323419136,151115727451828646838272,302231454903657293676544,604462909807314587353088,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168],
  #[2097152,2097155,2097157,2097161,2097169,32,64,128,147573952589676412928,2097665,2098177,2048,2101249,8192,2113537,32768,77371252455336267181195264,131072,2475880078570760549798248448,524288,19807040628566084398385987584,2097152,39614081257132168796771975168,10485761,18874369,35651585,67108864,134217728,268435456,536870912,1075838977,2149580801],
  #[4297064449,8589934592,17179869184,34359738368,68721573889,137441050625,274880004097,549755813888,1099511627776,2199025352705,4398048608257,8796095119361,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808],
  #[18446744073709551616,36893488147419103232,73786976294838206464,147573952589676412928,295147905179352825856,590295810358705651712,1180591620717411303424,2361183241434822606848,4722366482869645213696,9444732965739290427392,18889465931478580854784,37778931862957161709568,75557863725914323419136,151115727451828646838272,302231454903657293676544,604462909807314587353088,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168],
  #[4194304,4194304,4194304,4194304,4194304,4503599627370496,288230376151711744,9223372036854775808,0,4194304,4194304,0,4194304,17592186044416,4194304,9671406556917033397649408,65536,618970019642690137449562112,262144,9903520314283042199192993792,1048576,39614081257132168796771975168,4194304,4194304,4194304,4194304,0,17592186044416,9671406556917033397649408,618970019642690137449562112,4194304,4194304],
  #[4194304,0,17592186044416,9671406556917033397649408,4194304,4194304,4194304,17592186044416,9671406556917033397649408,4194304,4194304,4194304,17592186044416,9671406556917033397649408,42535295865117307932921825928971026432,340282366920938463463374607431768211456,0,2722258935367507707706996859454145691648,1125899906842624,2251799813685248,4503599627370496,43556142965880123323311949751266331066368,0,696898287454081973172991196020261297061888,1393796574908163946345982392040522594123776,144115188075855872,288230376151711744,0,22300745198530623141535718272648361505980416,44601490397061246283071436545296723011960832,4611686018427387904,9223372036854775808],
  #[0,0,0,0,0,17592186044416,9671406556917033397649408,0,17592186044416,9671406556917033397649408,0,0,17592186044416,9671406556917033397649408,17592186044416,9671406556917033397649408,1208925819614629174706176,2417851639229258349412352,4835703278458516698824704,9671406556917033397649408,19342813113834066795298816,38685626227668133590597632,77371252455336267181195264,154742504910672534362390528,309485009821345068724781056,618970019642690137449562112,1237940039285380274899124224,2475880078570760549798248448,4951760157141521099596496896,9903520314283042199192993792,19807040628566084398385987584,39614081257132168796771975168]
]

private def synLookup {α : Type} [Inhabited α] (table : Array (Array α)) (k : ℕ) : α :=
  (table[k / 32]?.getD #[])[k % 32]?.getD default

private def synIndex (s : Multiset (Fin 29)) : ℕ :=
  let ns := s.map Fin.val
  let a := ns.fold min 29
  let c := ns.fold max 0
  match s.card with
  | 0 => 0
  | 1 => 1 + a
  | 2 => 30 + c * (c+1) / 2 + a
  | 3 =>
    let b := (@Multiset.fold ℕ Nat.add ⟨Nat.add_comm⟩ ⟨Nat.add_assoc⟩ 0 ns) - a - c
    465 + c * (c+1) * (c+2) / 6 + b * (b+1) / 2 + a
  | _ => 0

private def synDigits (s : Multiset (Fin 29)) : List (Fin 146) :=
  synLookup synSparseWords (synLookup synMonCodes (synIndex s))

def syndromeNat (s : Multiset (Fin 29)) : ℕ := synPack (synDigits s)

def M (s : Multiset (Fin 29)) : SyndromeSpace := syndromeWord (syndromeNat s)

private def synColumn (i : Fin 29) (j : Fin 146) : ℕ :=
  if j.val < 96 then synLookup synMatrixWords (96 * i.val + j.val) else 0

def T (i : Fin 29) : SyndromeSpace →ₗ[ZMod 2] SyndromeSpace := synMatrix (synColumn i)

private abbrev synTest (i : Fin 29) (s : Multiset (Fin 29)) : Prop :=
  syndromeNat (i ::ₘ s) = synXors (synColumn i) (synDigits s)

set_option maxRecDepth 8192 in
private lemma synTest_sound {i : Fin 29} {s : Multiset (Fin 29)} (h : synTest i s) :
    M (i ::ₘ s) = T i (M s) := by
  exact (congrArg syndromeWord h).trans (synMatrix_pack (synColumn i) (synDigits s)).symm

set_option maxRecDepth 16384 in
lemma syndrome_nonzero : M 0 ≠ 0 := by
  intro h
  have hd := congrFun h (0 : Fin 146)
  change (if (syndromeNat 0).testBit 0 then (1 : ZMod 2) else 0) = 0 at hd
  have hh : (syndromeNat 0).testBit 0 = true := by decide
  simpa only [hh, if_true, one_ne_zero] using hd

set_option maxRecDepth 16384 in
lemma syndrome_boolean (i : Fin 29) : M {i,i} + M {i} = 0 := by
  have hb : ∀ v : Fin 29, syndromeNat {v,v} ^^^ syndromeNat {v} = 0 := by decide
  change syndromeWord _ + syndromeWord _ = _
  rw [← syndromeWord_xor, hb, syndromeWord_zero]

set_option maxRecDepth 16384 in
private lemma synCheckEmpty : ∀ i : Fin 29, synTest i 0 := by decide

set_option maxRecDepth 16384 in
private lemma synCheckOne : ∀ i a : Fin 29, synTest i {a} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo0 : ∀ a b : Fin 29, a ≤ b → synTest 0 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo1 : ∀ a b : Fin 29, a ≤ b → synTest 1 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo2 : ∀ a b : Fin 29, a ≤ b → synTest 2 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo3 : ∀ a b : Fin 29, a ≤ b → synTest 3 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo4 : ∀ a b : Fin 29, a ≤ b → synTest 4 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo5 : ∀ a b : Fin 29, a ≤ b → synTest 5 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo6 : ∀ a b : Fin 29, a ≤ b → synTest 6 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo7 : ∀ a b : Fin 29, a ≤ b → synTest 7 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo8 : ∀ a b : Fin 29, a ≤ b → synTest 8 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo9 : ∀ a b : Fin 29, a ≤ b → synTest 9 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo10 : ∀ a b : Fin 29, a ≤ b → synTest 10 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo11 : ∀ a b : Fin 29, a ≤ b → synTest 11 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo12 : ∀ a b : Fin 29, a ≤ b → synTest 12 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo13 : ∀ a b : Fin 29, a ≤ b → synTest 13 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo14 : ∀ a b : Fin 29, a ≤ b → synTest 14 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo15 : ∀ a b : Fin 29, a ≤ b → synTest 15 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo16 : ∀ a b : Fin 29, a ≤ b → synTest 16 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo17 : ∀ a b : Fin 29, a ≤ b → synTest 17 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo18 : ∀ a b : Fin 29, a ≤ b → synTest 18 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo19 : ∀ a b : Fin 29, a ≤ b → synTest 19 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo20 : ∀ a b : Fin 29, a ≤ b → synTest 20 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo21 : ∀ a b : Fin 29, a ≤ b → synTest 21 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo22 : ∀ a b : Fin 29, a ≤ b → synTest 22 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo23 : ∀ a b : Fin 29, a ≤ b → synTest 23 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo24 : ∀ a b : Fin 29, a ≤ b → synTest 24 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo25 : ∀ a b : Fin 29, a ≤ b → synTest 25 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo26 : ∀ a b : Fin 29, a ≤ b → synTest 26 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo27 : ∀ a b : Fin 29, a ≤ b → synTest 27 {a,b} := by decide

set_option maxRecDepth 16384 in
private lemma synCheckTwo28 : ∀ a b : Fin 29, a ≤ b → synTest 28 {a,b} := by decide

private lemma synCheckPair (i a b : Fin 29) (h : a ≤ b) : synTest i {a,b} := by
  fin_cases i
  · exact synCheckTwo0 a b h
  · exact synCheckTwo1 a b h
  · exact synCheckTwo2 a b h
  · exact synCheckTwo3 a b h
  · exact synCheckTwo4 a b h
  · exact synCheckTwo5 a b h
  · exact synCheckTwo6 a b h
  · exact synCheckTwo7 a b h
  · exact synCheckTwo8 a b h
  · exact synCheckTwo9 a b h
  · exact synCheckTwo10 a b h
  · exact synCheckTwo11 a b h
  · exact synCheckTwo12 a b h
  · exact synCheckTwo13 a b h
  · exact synCheckTwo14 a b h
  · exact synCheckTwo15 a b h
  · exact synCheckTwo16 a b h
  · exact synCheckTwo17 a b h
  · exact synCheckTwo18 a b h
  · exact synCheckTwo19 a b h
  · exact synCheckTwo20 a b h
  · exact synCheckTwo21 a b h
  · exact synCheckTwo22 a b h
  · exact synCheckTwo23 a b h
  · exact synCheckTwo24 a b h
  · exact synCheckTwo25 a b h
  · exact synCheckTwo26 a b h
  · exact synCheckTwo27 a b h
  · exact synCheckTwo28 a b h

lemma syndrome_compat (i : Fin 29) (s : Multiset (Fin 29)) (hs : s.card ≤ 2) :
    M (i ::ₘ s) = T i (M s) := by
  apply synTest_sound
  rcases (show s.card = 0 ∨ s.card = 1 ∨ s.card = 2 by omega) with h | h | h
  · rw [Multiset.card_eq_zero.mp h]
    exact synCheckEmpty i
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h
    exact synCheckOne i a
  · obtain ⟨a,b,rfl⟩ := Multiset.card_eq_two.mp h
    rcases le_total a b with h | h
    · exact synCheckPair i a b h
    · rw [Multiset.pair_comm]
      exact synCheckPair i b a h

end PEqualNP.Outside.L_pcx_103

namespace PEqualNP.Outside.L_pcx_103

open PEqualNP.ProofComplexity

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
lemma k104numeric : k104words syndromeNat := by
  unfold k104words
  decide +kernel

lemma width_degree_separation : ¬ PCRefutable (cnfSystem (counter_formula 8 3 upperEdges8)) 3 := by
  exact k104nonref M T syndrome_compat syndrome_boolean syndrome_nonzero
    (k104fromWords syndromeNat syndromeWord syndromeWord_zero syndromeWord_xor k104numeric)

end PEqualNP.Outside.L_pcx_103

open PEqualNP.Outside.L_pcx_103

theorem PEqualNP.Outside.L_pcx_103 : (∀ Fp : Set (PEqualNP.ProofComplexity.Clause (Fin 10 ⊕ (ℕ × ℕ))), Fp = {Cep | ∃ eep ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)), Cep = {(((Sum.inl eep.1) : Fin 10 ⊕ (ℕ × ℕ)), true), (((Sum.inl eep.2) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪ {Cap | ∃ iap : Fin 10, iap.val + 1 < 10 ∧ Cap = {(((Sum.inl iap) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (iap.val, 0)) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbp | ∃ (ibp : Fin 10) (hbp jbp : ℕ), ibp.val = hbp + 1 ∧ ibp.val + 1 < 10 ∧ jbp < 5 ∧ Cbp = {(((Sum.inr (hbp, jbp)) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibp.val, jbp)) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪ {Ccp | ∃ (icp : Fin 10) (hcp gcp : ℕ), icp.val = hcp + 1 ∧ icp.val + 1 < 10 ∧ gcp + 1 < 5 ∧ Ccp = {(((Sum.inl icp) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hcp, gcp)) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (icp.val, gcp + 1)) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪ {Cdp | ∃ (idp : Fin 10) (hdp : ℕ), idp.val = hdp + 1 ∧ Cdp = {(((Sum.inl idp) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hdp, 4)) : Fin 10 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfp | ∃ jfp : ℕ, 1 ≤ jfp ∧ jfp < 5 ∧ Cfp = {(((Sum.inr (0, jfp)) : Fin 10 ⊕ (ℕ × ℕ)), false)}} → (∃ πap, PEqualNP.ProofComplexity.IsRefutation Fp πap ∧ ∀ Dap ∈ πap, Dap.card ≤ 3) ∧ (¬ ∃ πbp, PEqualNP.ProofComplexity.IsRefutation Fp πbp ∧ ∀ Dbp ∈ πbp, Dbp.card ≤ 2) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fp) 3 ∧ ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fp) 2) ∧ (∀ Fk : Set (PEqualNP.ProofComplexity.Clause (Fin 8 ⊕ (ℕ × ℕ))), Fk = {Cek | ∃ eek ∈ ([(0, 4), (0, 5), (0, 6), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7)] : List (Fin 8 × Fin 8)), Cek = {(((Sum.inl eek.1) : Fin 8 ⊕ (ℕ × ℕ)), true), (((Sum.inl eek.2) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cak | ∃ iak : Fin 8, iak.val + 1 < 8 ∧ Cak = {(((Sum.inl iak) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (iak.val, 0)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbk | ∃ (ibk : Fin 8) (hbk jbk : ℕ), ibk.val = hbk + 1 ∧ ibk.val + 1 < 8 ∧ jbk < 3 ∧ Cbk = {(((Sum.inr (hbk, jbk)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibk.val, jbk)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cck | ∃ (ick : Fin 8) (hck gck : ℕ), ick.val = hck + 1 ∧ ick.val + 1 < 8 ∧ gck + 1 < 3 ∧ Cck = {(((Sum.inl ick) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hck, gck)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ick.val, gck + 1)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cdk | ∃ (idk : Fin 8) (hdk : ℕ), idk.val = hdk + 1 ∧ Cdk = {(((Sum.inl idk) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hdk, 2)) : Fin 8 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfk | ∃ jfk : ℕ, 1 ≤ jfk ∧ jfk < 3 ∧ Cfk = {(((Sum.inr (0, jfk)) : Fin 8 ⊕ (ℕ × ℕ)), false)}} → (∃ πak, PEqualNP.ProofComplexity.IsRefutation Fk πak ∧ ∀ Dak ∈ πak, Dak.card ≤ 3) ∧ (¬ ∃ πbk, PEqualNP.ProofComplexity.IsRefutation Fk πbk ∧ ∀ Dbk ∈ πbk, Dbk.card ≤ 2) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fk) 4 ∧ ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fk) 3) := by
  constructor
  · intro F hF
    subst F
    obtain ⟨hw, hd⟩ := counter_lower (k := 5) upperEdges10 (by decide)
    exact ⟨width_three_10, hw, pcUpper10, hd⟩
  · intro F hF
    subst F
    obtain ⟨witness, proof, width⟩ := width_three_8
    exact ⟨width_three_8, (counter_lower (k := 3) upperEdges8 (by decide)).1,
      width_to_pc_degree _ 3 witness proof width, width_degree_separation⟩
