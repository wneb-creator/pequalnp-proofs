import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2028.CircuitMono

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def WireImp (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma wireImp_append {a b : List Bool} (h : WireImp a b)
    (u v : Bool) (huv : u = true → v = true) :
    WireImp (a ++ [u]) (b ++ [v]) := by
  obtain ⟨hab, h⟩ := h
  refine ⟨by simp [hab], ?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append a [u] false i hi,
      List.getD_append b [v] false i (by omega)]
    exact h i
  · rw [List.getD_append_right a [u] false i (by omega),
      List.getD_append_right b [v] false i (by omega), ← hab]
    cases hd : i - a.length with
    | zero => simpa using huv
    | succ k => simp

lemma gate_eval_mono {a b : List Bool} (h : WireImp a b) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, Function.comp_def, id_eq,
      List.all_eq_true]
    intro ha i hi
    exact h.2 i (ha i hi)
  · simp only [hop, GateOp.eval, List.any_map, Function.comp_def, id_eq,
      List.any_eq_true]
    rintro ⟨i, hi, ha⟩
    exact ⟨i, hi, h.2 i ha⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (h : WireImp a b) :
    WireImp (gs.foldl step a) (gs.foldl step b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun q hq => hgs q (List.mem_cons_of_mem _ hq))
    exact wireImp_append h _ _ (gate_eval_mono h g (hgs g (by simp)))

lemma circuit_eval_mono (n : ℕ) (C : Circuit) (hC : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have hin : WireImp (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i
    by_cases hi : i < n
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi] using hxy ⟨i, hi⟩
    · simp [List.getD_eq_getElem?_getD, hi]
  have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1
  exact (fold_mono C.gates hgs _ _ hin).2 C.output

end PEqualNP.Outside.L_meta_2028.CircuitMono
