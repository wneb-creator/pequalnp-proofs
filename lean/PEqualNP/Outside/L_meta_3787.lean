import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3787

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def h5run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma h5run_append (gs hs : List Gate) (w : List Bool) :
    h5run (gs ++ hs) w = h5run hs (h5run gs w) := by
  simp [h5run, List.foldl_append]

lemma h5run_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, h5run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [h5run], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change h5run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]
    simp

lemma h5run_length (gs : List Gate) (w : List Bool) :
    (h5run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := h5run_prefix gs w
  rw [ht]
  simp [hl]

lemma h5getD_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (h5run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := h5run_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma h5wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size :=
  h5run_length C.gates x

lemma h5wires_append (C : Circuit) (gs : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.mk (C.gates ++ gs) o).wires x = h5run gs (C.wires x) :=
  h5run_append C.gates gs x

lemma h5getD_wires_append (C : Circuit) (gs : List Gate) (o : ℕ) (x : List Bool)
    (i : ℕ) (hi : i < x.length + C.size) :
    ((Circuit.mk (C.gates ++ gs) o).wires x).getD i false =
      (C.wires x).getD i false := by
  rw [h5wires_append]
  apply h5getD_run
  simpa [h5wires_length] using hi

lemma h5eval_append_preserved (C : Circuit) (gs : List Gate) (x : List Bool)
    (ho : C.output < x.length + C.size) :
    (Circuit.mk (C.gates ++ gs) C.output).eval x = C.eval x :=
  h5getD_wires_append C gs C.output x C.output ho

lemma h5eval_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  h5getD_run C.gates x i hi

lemma h5monotone_append (C : Circuit) (gs : List Gate) (o : ℕ)
    (hC : Monotone2 C) (hgs : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Monotone2 (Circuit.mk (C.gates ++ gs) o) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hC g hg
  · exact hgs g hg

def h5appendGate (C : Circuit) (n : ℕ) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g], n + C.size⟩

lemma h5appendGate_size (C : Circuit) (n : ℕ) (g : Gate) :
    (h5appendGate C n g).size = C.size + 1 := by
  simp [h5appendGate, Circuit.size]

lemma h5appendGate_eval (C : Circuit) (n : ℕ) (g : Gate) (x : List Bool)
    (hx : x.length = n) :
    (h5appendGate C n g).eval x =
      g.op.eval (g.inputs.map fun i => (C.wires x).getD i false) := by
  change ((Circuit.mk (C.gates ++ [g]) (n + C.size)).wires x).getD
    (n + C.size) false = _
  rw [h5wires_append]
  change (C.wires x ++ [g.op.eval (g.inputs.map fun i => (C.wires x).getD i false)]).getD
    (n + C.size) false = _
  rw [← hx, ← h5wires_length]
  simp

lemma h5appendGate_mono (C : Circuit) (n : ℕ) (g : Gate)
    (hC : Monotone2 C)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : g.inputs.length ≤ 2) :
    Monotone2 (h5appendGate C n g) := by
  apply h5monotone_append C [g] (n + C.size) hC
  intro g' hg'
  have heq : g' = g := by simpa using hg'
  subst g'
  exact ⟨hop, hlen⟩

lemma h5appendAnd_mono (C : Circuit) (n i j : ℕ) (hC : Monotone2 C) :
    Monotone2 (h5appendGate C n ⟨GateOp.and, [i, j]⟩) := by
  apply h5appendGate_mono C n _ hC <;> simp

lemma h5appendOr_mono (C : Circuit) (n i j : ℕ) (hC : Monotone2 C) :
    Monotone2 (h5appendGate C n ⟨GateOp.or, [i, j]⟩) := by
  apply h5appendGate_mono C n _ hC <;> simp

lemma h5appendAnd_eval (C : Circuit) (n i j : ℕ) (x : List Bool) (hx : x.length = n) :
    (h5appendGate C n ⟨GateOp.and, [i, j]⟩).eval x =
      ((C.wires x).getD i false && (C.wires x).getD j false) := by
  rw [h5appendGate_eval C n _ x hx]
  simp [GateOp.eval]

lemma h5appendOr_eval (C : Circuit) (n i j : ℕ) (x : List Bool) (hx : x.length = n) :
    (h5appendGate C n ⟨GateOp.or, [i, j]⟩).eval x =
      ((C.wires x).getD i false || (C.wires x).getD j false) := by
  rw [h5appendGate_eval C n _ x hx]
  simp [GateOp.eval]

lemma h5appendOr_output_eval (C : Circuit) (n j : ℕ) (x : List Bool)
    (hx : x.length = n) :
    (h5appendGate C n ⟨GateOp.or, [C.output, j]⟩).eval x =
      (C.eval x || (C.wires x).getD j false) :=
  h5appendOr_eval C n C.output j x hx

end PEqualNP.Outside.L_meta_3787
