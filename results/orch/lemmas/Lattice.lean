import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.Lattice

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def cut (k a : ℕ) : Bool := decide (k < a)

def gateN : GateOp → ℕ → ℕ → ℕ
  | .and, a, b => min a b
  | .or, a, b => max a b
  | _, _, _ => 0

def stepN (w : List ℕ) (g : Gate) : List ℕ :=
  w ++ [gateN g.op (w.getD (g.inputs.getD 0 0) 0) (w.getD (g.inputs.getD 1 0) 0)]

def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def natFun (n : ℕ) (C : Circuit) (x : Fin n → ℕ) : ℕ :=
  (C.gates.foldl stepN (List.ofFn x)).getD C.output 0

lemma cut_getD (w : List ℕ) (k i : ℕ) :
    (w.map (cut k)).getD i false = cut k (w.getD i 0) := by
  simpa [cut] using (List.getD_map w 0 (n := i) (cut k))

lemma step_threshold (w : List ℕ) (g : Gate) (k : ℕ)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2) :
    (stepN w g).map (cut k) = stepB (w.map (cut k)) g := by
  obtain ⟨i, j, hij⟩ := List.length_eq_two.mp hlen
  rcases hop with hop | hop <;>
    simp [stepN, stepB, hij, hop, gateN, cut, lt_min_iff, lt_max_iff]
  all_goals
    cases hi : w[i]? <;> cases hj : w[j]? <;> simp [GateOp.eval, cut]

lemma fold_threshold (gs : List Gate)
    (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : List ℕ) (k : ℕ) :
    (gs.foldl stepN w).map (cut k) = gs.foldl stepB (w.map (cut k)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g (by simp)
    have ht : ∀ a ∈ gs, (a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length = 2 :=
      fun a ha => h a (by simp [ha])
    simp only [List.foldl_cons]
    rw [ih ht, step_threshold w g k hg.1 hg.2]

lemma circuit_threshold (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (x : Fin n → ℕ) (k : ℕ) :
    PEqualNP.MetaComplexity.circuitFun n C (fun i => cut k (x i)) = cut k (natFun n C x) := by
  have h := fold_threshold C.gates (fun g hg => ⟨hC.1 g hg, hC.2.2 g hg⟩) (List.ofFn x) k
  have hh := congrArg (fun w : List Bool => w.getD C.output false) h
  rw [cut_getD] at hh
  unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval Circuit.wires natFun
  unfold stepB at hh
  simpa only [List.map_ofFn, Function.comp_def] using hh.symm

lemma edge_threshold (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hC : IsAO2 (p + l) C)
    (hfun : ∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (x : Fin (p + l) → ℕ) (k : ℕ) :
    k < natFun (p + l) C x ↔ ∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
      k < x (Fin.castAdd l a) ∧ k < x (Fin.natAdd p b) := by
  have h := hfun (fun i => cut k (x i))
  rw [circuit_threshold (p + l) C hC x k] at h
  have hh := congrArg (fun b : Bool => b = true) h
  simpa [cut] using (Iff.of_eq hh)

lemma edge_value (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hC : IsAO2 (p + l) C)
    (hfun : ∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (x : Fin (p + l) → ℕ) :
    natFun (p + l) C x =
      E.sup (fun e => min (x (Fin.castAdd l e.1)) (x (Fin.natAdd p e.2))) := by
  apply Nat.le_antisymm
  · by_contra h
    have hlt := Nat.lt_of_not_ge h
    obtain ⟨a, b, he, ha, hb⟩ := (edge_threshold p l E C hC hfun x _).mp hlt
    have hle : min (x (Fin.castAdd l a)) (x (Fin.natAdd p b)) ≤
        E.sup (fun e => min (x (Fin.castAdd l e.1)) (x (Fin.natAdd p e.2))) :=
      Finset.le_sup (f := fun e : Fin p × Fin l =>
        min (x (Fin.castAdd l e.1)) (x (Fin.natAdd p e.2))) he
    exact (not_lt_of_ge hle) (lt_min ha hb)
  · apply Finset.sup_le
    intro e he
    by_contra h
    have hlt := Nat.lt_of_not_ge h
    have heq : natFun (p + l) C x < natFun (p + l) C x :=
      (edge_threshold p l E C hC hfun x _).mpr
        ⟨e.1, e.2, he, (lt_min_iff.mp hlt).1, (lt_min_iff.mp hlt).2⟩
    exact (Nat.lt_irrefl _) heq

end PEqualNP.Outside.L_meta_4675.Lattice
