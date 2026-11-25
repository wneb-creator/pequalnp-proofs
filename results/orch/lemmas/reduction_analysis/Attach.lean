import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def attachRun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def shiftedGate (g : Gate) : Gate := ⟨g.op, g.inputs.map Nat.succ⟩

lemma attachRun_length (gs : List Gate) (x : List Bool) :
    (attachRun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [attachRun, List.foldl_cons] at *
    rw [ih]
    simp
    omega

lemma shiftedGate_run (gs : List Gate) (b : Bool) (x : List Bool) :
    attachRun (gs.map shiftedGate) (b :: x) = b :: attachRun gs x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [attachRun, List.map_cons, List.foldl_cons, shiftedGate,
      List.map_map, Function.comp_def, List.getD_cons_succ]
    exact ih _

end PEqualNP.Outside.L_meta_650
