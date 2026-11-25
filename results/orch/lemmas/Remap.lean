import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502.Remap

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wire (N M S : Nat) (f : Fin N → Option (Fin M)) (k : Nat) : Nat :=
  if h : k < N then (f ⟨k, h⟩).elim (M + S) Fin.val else M + (k - N)

def gate (N M S : Nat) (f : Fin N → Option (Fin M)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire N M S f)⟩

def circuit (N M : Nat) (f : Fin N → Option (Fin M)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gate N M C.size f), wire N M C.size f C.output⟩

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++
      [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => simp [run_snoc, ih, Nat.add_assoc]

lemma get_snoc (x : List Bool) (v : Bool) (k : Nat) :
    (x ++ [v]).getD k false = if k = x.length then v else x.getD k false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

lemma wire_hit (N M S : Nat) (f : Fin N → Option (Fin M)) (j k : Nat)
    (hj : j < S) : wire N M S f k = M + j ↔ k = N + j := by
  unfold wire
  split_ifs with hk
  · cases hf : f ⟨k, hk⟩ with
    | none => simp only [Option.elim_none]; omega
    | some v => simp only [Option.elim_some]; have hv := v.isLt; omega
  · omega

lemma run_correct (N M S : Nat) (f : Fin N → Option (Fin M))
    (x y : List Bool) (hx : x.length = N) (hy : y.length = M)
    (hinit : ∀ k, x.getD k false = y.getD (wire N M S f k) false)
    (gs : List Gate) (hgs : gs.length ≤ S) :
    ∀ k, (run gs x).getD k false =
      (run (gs.map (gate N M S f)) y).getD (wire N M S f k) false := by
  induction gs using List.reverseRecOn with
  | nil => exact hinit
  | append_singleton gs g ih =>
    have hlen : gs.length < S := by simp only [List.length_append,
      List.length_singleton] at hgs; omega
    have hprev := ih (by omega)
    intro k
    rw [List.map_append, List.map_cons, List.map_nil, run_snoc, run_snoc,
      get_snoc, get_snoc, run_length, run_length, List.length_map, hx, hy]
    simp only [wire_hit N M S f gs.length k hlen]
    split_ifs
    · change g.op.eval _ = g.op.eval _
      congr 1
      simp only [gate, List.map_map, Function.comp_apply]
      exact List.map_congr_left (fun a _ => hprev a)
    · exact hprev k

lemma circuit_correct (N M : Nat) (f : Fin N → Option (Fin M)) (C : Circuit)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = M)
    (hinit : ∀ k, x.getD k false = y.getD (wire N M C.size f k) false) :
    C.eval x = (circuit N M f C).eval y := by
  exact run_correct N M C.size f x y hx hy hinit C.gates (by rfl) C.output

lemma circuit_mono (N M : Nat) (f : Fin N → Option (Fin M)) (C : Circuit)
    (hmono : Monotone2 C) : Monotone2 (circuit N M f C) := by
  intro g hg
  change g ∈ C.gates.map (gate N M C.size f) at hg
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
  simpa only [gate, List.length_map] using hmono old hold

lemma circuit_size (N M : Nat) (f : Fin N → Option (Fin M)) (C : Circuit) :
    (circuit N M f C).size = C.size := by
  simp only [Circuit.size, circuit, List.length_map]

end PEqualNP.Outside.L_meta_9502.Remap
