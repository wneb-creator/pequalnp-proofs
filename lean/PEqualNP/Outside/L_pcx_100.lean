import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_100_aux
open PEqualNP.ProofComplexity
abbrev V := (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))
def M (X : Finset (Fin 5)) : Prop := ((∀ umc ∈ X, ∀ wmc ∈ X, ¬ (wmc = umc + 1 ∨ umc = wmc + 1)) ∧ ∀ zmc : Fin 5, zmc ∉ X → ∃ ymc ∈ X, (zmc = ymc + 1 ∨ ymc = zmc + 1))
def Q (X : Finset (Fin 5)) : Prop := X.card = 3

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 4096 in
theorem qspec : ∀ X, Q X ↔ ∃ Iqc : Finset (Fin 5), M Iqc ∧ ∃ wqc : Fin 5, wqc ∉ Iqc ∧ X = insert wqc Iqc := by
  unfold M Q <;> decide

def formula : Set (Clause V) := {C1c | ∃ (X1c : Finset (Fin 5)) (i1c : Fin 2) (e1c : Bool) (j1c : Fin 2), (M X1c ∨ Q X1c) ∧ j1c < i1c ∧ (C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), false), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : V), true)} ∨ C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), false), ((((6, X1c), ((j1c, false), (0, 0))) : V), true)} ∨ C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), true), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : V), false), ((((6, X1c), ((j1c, false), (0, 0))) : V), false)})} ∪ {C2c | ∃ (X2c : Finset (Fin 5)) (i2c : Fin 2) (e2c : Bool), (M X2c ∨ Q X2c) ∧ C2c = insert ((((5, X2c), ((i2c, e2c), (0, 0))) : V), false) (X2c.image (fun v2c : Fin 5 => ((((0, ∅), ((i2c, e2c), (0, v2c))) : V), true)) ∪ (Finset.univ.filter (fun j2c : Fin 2 => j2c < i2c)).image (fun k2c : Fin 2 => ((((4, X2c), ((i2c, e2c), (k2c, 0))) : V), true)))} ∪ {C3c | ∃ (X3c : Finset (Fin 5)) (i3c : Fin 2) (e3c : Bool) (v3c : Fin 5), (M X3c ∨ Q X3c) ∧ v3c ∈ X3c ∧ C3c = {((((5, X3c), ((i3c, e3c), (0, 0))) : V), true), ((((0, ∅), ((i3c, e3c), (0, v3c))) : V), false)}} ∪ {C4c | ∃ (X4c : Finset (Fin 5)) (i4c : Fin 2) (e4c : Bool) (j4c : Fin 2), (M X4c ∨ Q X4c) ∧ j4c < i4c ∧ C4c = {((((5, X4c), ((i4c, e4c), (0, 0))) : V), true), ((((4, X4c), ((i4c, e4c), (j4c, 0))) : V), false)}} ∪ {C5c | ∃ (X5c : Finset (Fin 5)) (i5c : Fin 2), (M X5c ∨ Q X5c) ∧ (C5c = {((((6, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, false), (0, 0))) : V), true)} ∨ C5c = {((((6, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, true), (0, 0))) : V), true)} ∨ C5c = {((((6, X5c), ((i5c, false), (0, 0))) : V), true), ((((5, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, true), (0, 0))) : V), false)})} ∪ {C6c | ∃ (X6c : Finset (Fin 5)) (v6c : Fin 5), M X6c ∧ v6c ∈ X6c ∧ C6c = {((((2, ∅), ((0, false), (0, v6c))) : V), false)}} ∪ {C7c | ∃ (X7c : Finset (Fin 5)) (i7c : Fin 2), M X7c ∧ C7c = {((((3, ∅), ((i7c, false), (0, 0))) : V), false), ((((6, X7c), ((i7c, false), (0, 0))) : V), false)}} ∪ {C8c | ∃ (X8c : Finset (Fin 5)) (i8c : Fin 2), Q X8c ∧ (C8c = {((((7, X8c), ((i8c, false), (0, 0))) : V), false), ((((3, ∅), ((i8c, false), (0, 0))) : V), true)} ∨ C8c = {((((7, X8c), ((i8c, false), (0, 0))) : V), false), ((((6, X8c), ((i8c, false), (0, 0))) : V), true)})} ∪ {C9c | ∃ X9c : Finset (Fin 5), Q X9c ∧ C9c = X9c.image (fun v9c : Fin 5 => ((((2, ∅), ((0, false), (0, v9c))) : V), true)) ∪ Finset.univ.image (fun i9c : Fin 2 => ((((7, X9c), ((i9c, false), (0, 0))) : V), true))}
def rho (v : V) : Option Bool := if v.1.1 = 2 then some false else none
def model (v : V) : Bool := decide (v.2.1.1 = 1 ∧
  (v.1.1 = 3 ∨ ((v.1.1 = 5 ∨ v.1.1 = 6 ∨ v.1.1 = 7) ∧ v.1.2.card = 3)))
def good (c : Clause V) : Bool :=
  match restrictClause rho c with
  | none => true
  | some d => decide (4 < d.card) || decide (∃ l ∈ d, model l.1 = l.2)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem group1 : ∀ (X1c : Finset (Fin 5)) (i1c : Fin 2) (e1c : Bool) (j1c : Fin 2), (M X1c ∨ Q X1c) → j1c < i1c → good ({((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), false), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : V), true)}) = true ∧ good ({((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), false), ((((6, X1c), ((j1c, false), (0, 0))) : V), true)}) = true ∧ good ({((((4, X1c), ((i1c, e1c), (j1c, 0))) : V), true), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : V), false), ((((6, X1c), ((j1c, false), (0, 0))) : V), false)}) = true := by
  simp only [M, Q] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
theorem group2 : ∀ (X2c : Finset (Fin 5)) (i2c : Fin 2) (e2c : Bool), (M X2c ∨ Q X2c) → good (insert ((((5, X2c), ((i2c, e2c), (0, 0))) : V), false) (X2c.image (fun v2c : Fin 5 => ((((0, ∅), ((i2c, e2c), (0, v2c))) : V), true)) ∪ (Finset.univ.filter (fun j2c : Fin 2 => j2c < i2c)).image (fun k2c : Fin 2 => ((((4, X2c), ((i2c, e2c), (k2c, 0))) : V), true)))) = true := by
  simp only [M, Q] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem group3 : ∀ (X3c : Finset (Fin 5)) (i3c : Fin 2) (e3c : Bool) (v3c : Fin 5), (M X3c ∨ Q X3c) → v3c ∈ X3c → good ({((((5, X3c), ((i3c, e3c), (0, 0))) : V), true), ((((0, ∅), ((i3c, e3c), (0, v3c))) : V), false)}) = true := by
  simp only [M, Q] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem group4 : ∀ (X4c : Finset (Fin 5)) (i4c : Fin 2) (e4c : Bool) (j4c : Fin 2), (M X4c ∨ Q X4c) → j4c < i4c → good ({((((5, X4c), ((i4c, e4c), (0, 0))) : V), true), ((((4, X4c), ((i4c, e4c), (j4c, 0))) : V), false)}) = true := by
  simp only [M, Q] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem group5 : ∀ (X5c : Finset (Fin 5)) (i5c : Fin 2), (M X5c ∨ Q X5c) → good ({((((6, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, false), (0, 0))) : V), true)}) = true ∧ good ({((((6, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, true), (0, 0))) : V), true)}) = true ∧ good ({((((6, X5c), ((i5c, false), (0, 0))) : V), true), ((((5, X5c), ((i5c, false), (0, 0))) : V), false), ((((5, X5c), ((i5c, true), (0, 0))) : V), false)}) = true := by
  simp only [M, Q] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem group6 : ∀ (X6c : Finset (Fin 5)) (v6c : Fin 5), M X6c → v6c ∈ X6c → good ({((((2, ∅), ((0, false), (0, v6c))) : V), false)}) = true := by
  simp only [M, Q] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem group7 : ∀ (X7c : Finset (Fin 5)) (i7c : Fin 2), M X7c → good ({((((3, ∅), ((i7c, false), (0, 0))) : V), false), ((((6, X7c), ((i7c, false), (0, 0))) : V), false)}) = true := by
  simp only [M, Q] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem group8 : ∀ (X8c : Finset (Fin 5)) (i8c : Fin 2), Q X8c → good ({((((7, X8c), ((i8c, false), (0, 0))) : V), false), ((((3, ∅), ((i8c, false), (0, 0))) : V), true)}) = true ∧ good ({((((7, X8c), ((i8c, false), (0, 0))) : V), false), ((((6, X8c), ((i8c, false), (0, 0))) : V), true)}) = true := by
  simp only [M, Q] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem group9 : ∀ (X9c : Finset (Fin 5)), Q X9c → good (X9c.image (fun v9c : Fin 5 => ((((2, ∅), ((0, false), (0, v9c))) : V), true)) ∪ Finset.univ.image (fun i9c : Fin 2 => ((((7, X9c), ((i9c, false), (0, 0))) : V), true))) = true := by
  simp only [M, Q] <;> decide

theorem good_all (c : Clause V) (h : c ∈ formula) : good c = true := by
  unfold formula at h
  simp only [Set.mem_union, Set.mem_setOf_eq, or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h | h
  · obtain ⟨a0, a1, a2, a3, h0, h1, he⟩ := h
    have hh := group1 a0 a1 a2 a3 h0 h1
    rcases he with rfl | rfl | rfl
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
  · obtain ⟨a0, a1, a2, h0, he⟩ := h
    have hh := group2 a0 a1 a2 h0
    simpa only [he] using hh
  · obtain ⟨a0, a1, a2, a3, h0, h1, he⟩ := h
    have hh := group3 a0 a1 a2 a3 h0 h1
    simpa only [he] using hh
  · obtain ⟨a0, a1, a2, a3, h0, h1, he⟩ := h
    have hh := group4 a0 a1 a2 a3 h0 h1
    simpa only [he] using hh
  · obtain ⟨a0, a1, h0, he⟩ := h
    have hh := group5 a0 a1 h0
    rcases he with rfl | rfl | rfl
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
  · obtain ⟨a0, a1, h0, h1, he⟩ := h
    have hh := group6 a0 a1 h0 h1
    simpa only [he] using hh
  · obtain ⟨a0, a1, h0, he⟩ := h
    have hh := group7 a0 a1 h0
    simpa only [he] using hh
  · obtain ⟨a0, a1, h0, he⟩ := h
    have hh := group8 a0 a1 h0
    rcases he with rfl | rfl
    · exact hh.1
    · exact hh.2
  · obtain ⟨a0, h0, he⟩ := h
    have hh := group9 a0 h0
    simpa only [he] using hh
theorem resolvent_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : Clause V}
    (h : IsResolvent C D R) (hC : ClauseSat a C) (hD : ClauseSat a D) : ClauseSat a R := by
  obtain ⟨v, -, -, rfl⟩ := h
  obtain ⟨l, hl, hal⟩ := hC
  obtain ⟨l', hl', hal'⟩ := hD
  by_cases h : l = (v, true)
  · subst h
    refine ⟨l', Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hl'⟩), hal'⟩
    rintro rfl
    simp_all
  · exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hl⟩), hal⟩


theorem soundSmall {F : Set (Clause V)}
    (h : ∀ c ∈ F, c.card ≤ 4 → ClauseSat model c)
    {π : List (Clause V)} (der : IsDerivation F π) (width : ∀ d ∈ π, d.card ≤ 4) :
    ∀ d ∈ π, ClauseSat model d := by
  induction der with
  | nil => simp
  | ax _ hf ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h _ hf (width _ (List.mem_cons_self))
    · exact ih (fun d hd => width d (List.mem_cons_of_mem _ hd)) _ he
  | res _ hc hd hr ih =>
    have ih' := ih (fun d hh => width d (List.mem_cons_of_mem _ hh))
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact resolvent_sound _ hr (ih' _ hc) (ih' _ hd)
    · exact ih' _ he

theorem impossible {π : List (Clause V)} (hr : IsRefutation (restrictCNF formula rho) π)
    (hw : ∀ c ∈ π, c.card ≤ 4) : False := by
  have hh : ∀ d ∈ restrictCNF formula rho, d.card ≤ 4 → ClauseSat model d := by
    intro d hd hs
    obtain ⟨c, hc, he⟩ := hd
    have hg := good_all c hc
    simpa [good, he, Nat.not_lt_of_ge hs, ClauseSat] using hg
  obtain ⟨l, hl, _⟩ := soundSmall hh hr.1 hw _ hr.2
  exact Finset.notMem_empty l hl

end PEqualNP.Outside.L_pcx_100_aux

open PEqualNP.Outside.L_pcx_100_aux

theorem PEqualNP.Outside.L_pcx_100 : ¬ (∀ Mc : Finset (Fin 5) → Prop, (∀ Ymc : Finset (Fin 5), Mc Ymc ↔ ((∀ umc ∈ Ymc, ∀ wmc ∈ Ymc, ¬ (wmc = umc + 1 ∨ umc = wmc + 1)) ∧ ∀ zmc : Fin 5, zmc ∉ Ymc → ∃ ymc ∈ Ymc, (zmc = ymc + 1 ∨ ymc = zmc + 1))) → ∀ Qc : Finset (Fin 5) → Prop, (∀ Yqc : Finset (Fin 5), Qc Yqc ↔ ∃ Iqc : Finset (Fin 5), Mc Iqc ∧ ∃ wqc : Fin 5, wqc ∉ Iqc ∧ Yqc = insert wqc Iqc) → ∀ Fc : Set (PEqualNP.ProofComplexity.Clause ((Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5)))), Fc = {C1c | ∃ (X1c : Finset (Fin 5)) (i1c : Fin 2) (e1c : Bool) (j1c : Fin 2), (Mc X1c ∨ Qc X1c) ∧ j1c < i1c ∧ (C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((6, X1c), ((j1c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C1c = {((((4, X1c), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true), ((((1, ∅), ((i1c, e1c), (j1c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((6, X1c), ((j1c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)})} ∪ {C2c | ∃ (X2c : Finset (Fin 5)) (i2c : Fin 2) (e2c : Bool), (Mc X2c ∨ Qc X2c) ∧ C2c = insert ((((5, X2c), ((i2c, e2c), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false) (X2c.image (fun v2c : Fin 5 => ((((0, ∅), ((i2c, e2c), (0, v2c))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)) ∪ (Finset.univ.filter (fun j2c : Fin 2 => j2c < i2c)).image (fun k2c : Fin 2 => ((((4, X2c), ((i2c, e2c), (k2c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)))} ∪ {C3c | ∃ (X3c : Finset (Fin 5)) (i3c : Fin 2) (e3c : Bool) (v3c : Fin 5), (Mc X3c ∨ Qc X3c) ∧ v3c ∈ X3c ∧ C3c = {((((5, X3c), ((i3c, e3c), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true), ((((0, ∅), ((i3c, e3c), (0, v3c))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)}} ∪ {C4c | ∃ (X4c : Finset (Fin 5)) (i4c : Fin 2) (e4c : Bool) (j4c : Fin 2), (Mc X4c ∨ Qc X4c) ∧ j4c < i4c ∧ C4c = {((((5, X4c), ((i4c, e4c), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true), ((((4, X4c), ((i4c, e4c), (j4c, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)}} ∪ {C5c | ∃ (X5c : Finset (Fin 5)) (i5c : Fin 2), (Mc X5c ∨ Qc X5c) ∧ (C5c = {((((6, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((5, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C5c = {((((6, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((5, X5c), ((i5c, true), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C5c = {((((6, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true), ((((5, X5c), ((i5c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((5, X5c), ((i5c, true), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)})} ∪ {C6c | ∃ (X6c : Finset (Fin 5)) (v6c : Fin 5), Mc X6c ∧ v6c ∈ X6c ∧ C6c = {((((2, ∅), ((0, false), (0, v6c))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)}} ∪ {C7c | ∃ (X7c : Finset (Fin 5)) (i7c : Fin 2), Mc X7c ∧ C7c = {((((3, ∅), ((i7c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((6, X7c), ((i7c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false)}} ∪ {C8c | ∃ (X8c : Finset (Fin 5)) (i8c : Fin 2), Qc X8c ∧ (C8c = {((((7, X8c), ((i8c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((3, ∅), ((i8c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)} ∨ C8c = {((((7, X8c), ((i8c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), false), ((((6, X8c), ((i8c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)})} ∪ {C9c | ∃ X9c : Finset (Fin 5), Qc X9c ∧ C9c = X9c.image (fun v9c : Fin 5 => ((((2, ∅), ((0, false), (0, v9c))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true)) ∪ Finset.univ.image (fun i9c : Fin 2 => ((((7, X9c), ((i9c, false), (0, 0))) : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5))), true))} → ¬ (∃ πc1, PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.restrictCNF Fc (fun zc : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5)) => if zc.1.1 = 2 then (some false : Option Bool) else none)) πc1 ∧ ∀ Dc1 ∈ πc1, Dc1.card ≤ 3) ∧ (∃ πc2, PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.restrictCNF Fc (fun zc : (Fin 8 × Finset (Fin 5)) × ((Fin 2 × Bool) × (Fin 2 × Fin 5)) => if zc.1.1 = 2 then (some false : Option Bool) else none)) πc2 ∧ ∀ Dc2 ∈ πc2, Dc2.card ≤ 4)) := by
  intro h
  obtain ⟨π, hr, hw⟩ := (h M (fun _ => Iff.rfl) Q qspec formula rfl).2
  exact impossible hr hw
