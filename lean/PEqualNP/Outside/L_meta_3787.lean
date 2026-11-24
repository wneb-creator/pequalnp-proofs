import Mathlib.Data.List.OfFn
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3787.h6

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma getD_snoc_eq (W : List Bool) (v : Bool) :
    (W ++ [v]).getD W.length false = v := by
  simp [List.getD]

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_init_lists (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool)
    (hW : W.length = n) (hW' : W'.length = m)
    (hinputs : ∀ i : Fin n, W'.getD (π i).val false = W.getD i.val false) :
    Rel n m π W W' := by
  refine ⟨by omega, by omega, ?_⟩
  intro i
  unfold wmap
  split
  · exact hinputs ⟨i, by assumption⟩
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma relabel_eval_lists (n m : ℕ) (π : Fin n → Fin m) (C : Circuit)
    (W W' : List Bool) (hW : W.length = n) (hW' : W'.length = m)
    (hinputs : ∀ i : Fin n, W'.getD (π i).val false = W.getD i.val false) :
    (relabel n m π C).eval W' = C.eval W := by
  exact (rel_fold n m π C.gates _ _
    (rel_init_lists n m π W W' hW hW' hinputs)).2.2 C.output

lemma relabel_eval (n m : ℕ) (π : Fin n → Fin m) (C : Circuit)
    (x : Fin m → Bool) :
    (relabel n m π C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) := by
  exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

lemma relabel_size (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) :
    (relabel n m π C).size = C.size := by
  simp [relabel, Circuit.size]

lemma relabel_monotone (n m : ℕ) (π : Fin n → Fin m) (C : Circuit)
    (hC : Monotone2 C) : Monotone2 (relabel n m π C) := by
  intro g hg
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
  exact ⟨(hC g₀ hg₀).1, by simpa [relGate] using (hC g₀ hg₀).2⟩

lemma wmap_lt (n m : ℕ) (π : Fin n → Fin m) (i k : ℕ)
    (hi : i < n + k) : wmap n m π i < m + k := by
  unfold wmap
  split
  · have := (π ⟨i, by assumption⟩).isLt
    omega
  · omega

lemma relabel_output_lt (n m : ℕ) (π : Fin n → Fin m) (C : Circuit)
    (hC : C.output < n + C.size) :
    (relabel n m π C).output < m + (relabel n m π C).size := by
  rw [relabel_size]
  exact wmap_lt n m π C.output C.size hC

lemma relabel_list_eval (m : ℕ) (inputs : List (Fin m)) (C : Circuit)
    (x : Fin m → Bool) :
    (relabel inputs.length m inputs.get C).eval (List.ofFn x) =
      C.eval (inputs.map x) := by
  rw [relabel_eval]
  congr 1
  rw [← List.map_ofFn, List.ofFn_get]

end PEqualNP.Outside.L_meta_3787.h6
