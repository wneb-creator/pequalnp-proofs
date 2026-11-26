import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18063

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def pstep {N : ℕ} (w : List Bool) (p : Bool × Fin N × Fin N) : List Bool :=
  w ++ [bif p.1 then w.getD (p.2.1 : ℕ) false || w.getD (p.2.2 : ℕ) false
    else w.getD (p.2.1 : ℕ) false && w.getD (p.2.2 : ℕ) false]

def conv {N : ℕ} (p : Bool × Fin N × Fin N) : Gate :=
  ⟨bif p.1 then GateOp.or else GateOp.and, [(p.2.1 : ℕ), (p.2.2 : ℕ)]⟩

theorem step_conv {N : ℕ} (w : List Bool) (p : Bool × Fin N × Fin N) :
    step w (conv p) = pstep w p := by
  obtain ⟨b, i, j⟩ := p
  cases b <;> simp [step, conv, pstep, GateOp.eval]

theorem run_conv {N : ℕ} (l : List (Bool × Fin N × Fin N)) : ∀ w : List Bool,
    (l.map conv).foldl step w = l.foldl pstep w := by
  induction l with
  | nil => intro w; rfl
  | cons p l ih =>
    intro w
    simp only [List.map_cons, List.foldl_cons]
    rw [step_conv, ih]

theorem main (n m : ℕ) (P : Fin m → Bool × Fin (n + m) × Fin (n + m)) (o : ℕ)
    (h : ∀ j : Fin m, max ((P j).2.1 : ℕ) ((P j).2.2 : ℕ) < n + (j : ℕ)) :
    ∃ C : Circuit, Monotone2 C ∧ ReadsBack n C ∧ C.size = m ∧
      ∀ x : Fin n → Bool, circuitFun n C x = ((List.ofFn P).foldl pstep (List.ofFn x)).getD o false := by
  refine ⟨⟨(List.ofFn P).map conv, o⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hg
    obtain ⟨b, i, j⟩ := p
    cases b <;> simp [conv]
  · intro j hj i hi
    simp only [List.length_map, List.length_ofFn] at hj
    have e : gateAt ⟨(List.ofFn P).map conv, o⟩ j = conv (P ⟨j, hj⟩) := by
      simp [gateAt, hj]
    rw [e] at hi
    have hh := h ⟨j, hj⟩
    simp only [conv, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact lt_of_le_of_lt (le_max_left _ _) hh
    · exact lt_of_le_of_lt (le_max_right _ _) hh
  · simp [Circuit.size]
  · intro x
    show (((List.ofFn P).map conv).foldl step (List.ofFn x)).getD o false = _
    rw [run_conv]

end PEqualNP.Outside.L_meta_18063

theorem PEqualNP.Outside.L_meta_18063 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Bool × Fin (x1 + x2) × Fin (x1 + x2)) (x4 : ℕ),   (∀ (x5 : Fin x2), Max.max ↑(x3 x5).2.1 ↑(x3 x5).2.2 < x1 + ↑x5) →     ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.Monotone2 x6 ∧         PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x6 ∧           x6.size = x2 ∧             ∀ (x7 : Fin x1 → Bool),               PEqualNP.MetaComplexity.circuitFun x1 x6 x7 =                 (List.foldl                       (fun (x8 : List Bool) (x9 : Bool × Fin (x1 + x2) × Fin (x1 + x2)) =>                         have x10 : Bool := x8.getD (↑x9.2.1) Bool.false;                         have x11 : Bool := x8.getD (↑x9.2.2) Bool.false;                         x8 ++ [bif x9.1 then x10 || x11 else x10 && x11])                       (List.ofFn x7) (List.ofFn x3)).getD                   x4 Bool.false := by
  intro n m P o h
  exact PEqualNP.Outside.L_meta_18063.main n m P o h
