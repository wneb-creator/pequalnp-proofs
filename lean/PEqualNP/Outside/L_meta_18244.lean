import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18244

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i < w.length then w.getD i false else if i = w.length then b else false := by
  rcases Nat.lt_or_ge i w.length with h | h
  · simp [h, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rcases Nat.eq_or_lt_of_le h with h | h
    · subst h; simp [List.getD_eq_getElem?_getD]
    · have h1 : ¬ i < w.length := by omega
      have h2 : i ≠ w.length := by omega
      simp only [h1, h2, if_false]
      rw [List.getD_eq_default]
      simp; omega

def Ag (c a b : ℕ) (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ (∀ i, i ≠ c → w.getD i false = w'.getD i false) ∧ w.getD a false = true ∧ w.getD b false = true

theorem fold_ag (c a b : ℕ) (hca : c ≠ a) (hcb : c ≠ b) : ∀ (gs : List Gate),
    (∀ g ∈ gs, c ∈ g.inputs → g.op = GateOp.or ∧ (a ∈ g.inputs ∨ b ∈ g.inputs)) →
    ∀ w w' : List Bool, c < w.length → Ag c a b w w' →
    Ag c a b (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w')
  | [], _, w, w', _, h => h
  | g :: gs, hg, w, w', hc, h => by
    simp only [List.foldl_cons]
    obtain ⟨hl, he, ha, hb⟩ := h
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false) = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      by_cases hci : c ∈ g.inputs
      · obtain ⟨hop, hab⟩ := hg g (List.mem_cons_self ..) hci
        rw [hop]
        have ha' : w'.getD a false = true := by rw [← he a (Ne.symm hca)]; exact ha
        have hb' : w'.getD b false = true := by rw [← he b (Ne.symm hcb)]; exact hb
        simp only [GateOp.eval, List.any_map, Function.comp]
        rcases hab with h1 | h1
        · rw [List.any_eq_true.2 ⟨a, h1, by simpa using ha⟩, List.any_eq_true.2 ⟨a, h1, by simpa using ha'⟩]
        · rw [List.any_eq_true.2 ⟨b, h1, by simpa using hb⟩, List.any_eq_true.2 ⟨b, h1, by simpa using hb'⟩]
      · congr 1
        apply List.map_congr_left
        intro i hi
        exact he i (fun e => hci (e ▸ hi))
    apply fold_ag c a b hca hcb gs (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    · simp; omega
    refine ⟨by simp [hl], ?_, ?_, ?_⟩
    · intro i hi
      rw [getD_snoc, getD_snoc, ← hl, hv]
      split_ifs <;> first | exact he i hi | rfl
    · rw [getD_snoc]; split_ifs with h1 h2
      · exact ha
      · exact absurd (h2 ▸ ha) (by rw [List.getD_eq_default _ _ (le_refl _)]; simp)
      · exact absurd ha (by rw [List.getD_eq_default _ _ (by omega)]; simp)
    · rw [getD_snoc]; split_ifs with h1 h2
      · exact hb
      · exact absurd (h2 ▸ hb) (by rw [List.getD_eq_default _ _ (le_refl _)]; simp)
      · exact absurd hb (by rw [List.getD_eq_default _ _ (by omega)]; simp)

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_18244

theorem PEqualNP.Outside.L_meta_18244 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → x3 ≠ x4 → x3 ≠ x5 → (∀ x9 < x2.size, ↑x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (↑x4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).inputs ∨ ↑x5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).inputs)) → (∀ (x10 : Fin x1 → Bool), x2.eval (List.ofFn x10) = x10 x3) ∨ ∀ (x10 x11 : Fin x1 → Bool), x10 x4 = Bool.true → x10 x5 = Bool.true → (∀ (x14 : Fin x1), x14 ≠ x3 → x10 x14 = x11 x14) → x2.eval (List.ofFn x10) = x2.eval (List.ofFn x11) := by
  intro x1 x2 x3 x4 x5 hao h34 h35 hr
  by_cases ho : x2.output = (x3 : ℕ)
  · left
    intro x10
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, ho]
    have hl : (x3 : ℕ) < (List.ofFn x10).length := by simp
    have : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), (x3 : ℕ) < w.length →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD x3 false = w.getD x3 false := by
      intro gs
      induction gs with
      | nil => intro w _; rfl
      | cons g gs ih =>
        intro w hw
        simp only [List.foldl_cons]
        rw [ih _ (by simp; omega), L_meta_18244.getD_snoc, if_pos hw]
    rw [PEqualNP.CircuitLowerBounds.Circuit.wires, this _ _ hl, List.getD_eq_getElem _ _ hl]
    simp
  · right
    intro x10 x11 h4 h5 heq
    have hg : ∀ g ∈ x2.gates, (x3 : ℕ) ∈ g.inputs → g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ((x4 : ℕ) ∈ g.inputs ∨ (x5 : ℕ) ∈ g.inputs) := by
      intro g hg hc
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt x2 k = x2.gates[k] := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hk]
      have := hr k hk (by rw [e]; exact hc)
      rwa [e] at this
    have hag : L_meta_18244.Ag x3 x4 x5 (List.ofFn x10) (List.ofFn x11) := by
      refine ⟨by simp, ?_, ?_, ?_⟩
      · intro i hi
        rcases Nat.lt_or_ge i x1 with h | h
        · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
          simp only [List.getElem_ofFn]
          exact heq ⟨i, h⟩ (fun e => hi (by rw [← e]))
        · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ (by simpa using h)]
      · rw [List.getD_eq_getElem _ _ (by simp)]; simpa using h4
      · rw [List.getD_eq_getElem _ _ (by simp)]; simpa using h5
    have := (L_meta_18244.fold_ag x3 x4 x5 (fun e => h34 (Fin.ext e)) (fun e => h35 (Fin.ext e)) x2.gates hg _ _ (by simp) hag).2.1 x2.output ho
    exact this
