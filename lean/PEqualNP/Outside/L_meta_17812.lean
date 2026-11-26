import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17812

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def pstep (w : List Bool) (p : Bool × ℕ × ℕ) : List Bool :=
  w ++ [if p.1 = true then w.getD p.2.1 false && w.getD p.2.2 false
    else w.getD p.2.1 false || w.getD p.2.2 false]

def tau (L i : ℕ) : ℕ := if i < L then i + 2 else 0

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def args (L : ℕ) : List ℕ → Bool → ℕ × ℕ
  | [], b => if b = true then (1, 1) else (0, 0)
  | [a], _ => (tau L a, tau L a)
  | a :: b :: _, _ => (tau L a, tau L b)

def conv (L : ℕ) (g : Gate) : Bool × ℕ × ℕ := (isAnd g.op, args L g.inputs (isAnd g.op))

def prog : ℕ → List Gate → List (Bool × ℕ × ℕ)
  | _, [] => []
  | L, g :: gs => conv L g :: prog (L + 1) gs

theorem tau_lt (L i : ℕ) : tau L i < L + 2 := by
  unfold tau
  split_ifs <;> omega

theorem tau_val (w : List Bool) (i : ℕ) :
    (false :: true :: w).getD (tau w.length i) false = w.getD i false := by
  unfold tau
  split_ifs with h
  · simp
  · rw [List.getD_eq_default w false (by omega)]
    simp

theorem tau_val' (w : List Bool) (i : ℕ) :
    (false :: true :: w)[tau w.length i]?.getD false = w[i]?.getD false := by
  have h := tau_val w i
  simpa [List.getD_eq_getElem?_getD] using h

theorem conv_val (w : List Bool) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) :
    pstep (false :: true :: w) (conv w.length g) = false :: true :: step w g := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, ins⟩⟩⟩
    · simp [pstep, conv, isAnd, args, step, GateOp.eval]
    · simp [pstep, conv, isAnd, args, step, GateOp.eval, tau_val']
    · simp [pstep, conv, isAnd, args, step, GateOp.eval, tau_val']
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, ins⟩⟩⟩
    · simp [pstep, conv, isAnd, args, step, GateOp.eval]
    · simp [pstep, conv, isAnd, args, step, GateOp.eval, tau_val']
    · simp [pstep, conv, isAnd, args, step, GateOp.eval, tau_val']
    · simp at hlen

theorem conv_lt (L : ℕ) (g : Gate) : (conv L g).2.1 < L + 2 ∧ (conv L g).2.2 < L + 2 := by
  obtain ⟨op, ins⟩ := g
  rcases ins with _ | ⟨a, _ | ⟨b, ins⟩⟩
  · simp only [conv, args]
    split_ifs <;> constructor <;> simp <;> omega
  · exact ⟨tau_lt L a, tau_lt L a⟩
  · exact ⟨tau_lt L a, tau_lt L b⟩

theorem prog_len (gs : List Gate) : ∀ L, (prog L gs).length = gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih => intro L; simp [prog, ih]

theorem prog_lt (gs : List Gate) : ∀ (L k : ℕ) (p : Bool × ℕ × ℕ), (prog L gs)[k]? = some p →
    p.2.1 < L + 2 + k ∧ p.2.2 < L + 2 + k := by
  induction gs with
  | nil => intro L k p h; simp [prog] at h
  | cons g gs ih =>
    intro L k p h
    cases k with
    | zero =>
      simp only [prog, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact conv_lt L g
    | succ k =>
      simp only [prog, List.getElem?_cons_succ] at h
      have := ih (L + 1) k p h
      omega

theorem prog_run (gs : List Gate) : ∀ (w : List Bool),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    (prog w.length gs).foldl pstep (false :: true :: w) = false :: true :: gs.foldl step w := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w h
    have hg := h g List.mem_cons_self
    simp only [prog, List.foldl_cons]
    rw [conv_val w g hg.1 hg.2]
    have hl : (step w g).length = w.length + 1 := by simp [step]
    rw [← hl]
    exact ih (step w g) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

theorem run_len (gs : List Gate) : ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    rw [ih]
    simp [step]
    omega

theorem main (C : Circuit) (hC : Monotone2 C) (hs : C.size ≤ 18) :
    ∃ (P : List (Bool × ℕ × ℕ)) (o : ℕ), P.length ≤ 18 ∧ o < 13 + P.length ∧
      (∀ (k : ℕ) (p : Bool × ℕ × ℕ), P[k]? = some p → p.2.1 < 13 + k ∧ p.2.2 < 13 + k) ∧
      ∀ x : List Bool, x.length = 11 →
        (P.foldl pstep (false :: true :: x)).getD o false = C.eval x := by
  have hC' : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hC g hg
    refine ⟨?_, h.2⟩
    simpa using h.1
  refine ⟨prog 11 C.gates, tau (11 + C.gates.length) C.output, ?_, ?_, ?_, ?_⟩
  · rw [prog_len]
    exact hs
  · rw [prog_len]
    have := tau_lt (11 + C.gates.length) C.output
    omega
  · intro k p h
    have := prog_lt C.gates 11 k p h
    omega
  · intro x hx
    have h := prog_run C.gates x hC'
    rw [hx] at h
    rw [h]
    have hl := run_len C.gates x
    rw [hx] at hl
    have h2 := tau_val (C.gates.foldl step x) C.output
    rw [hl] at h2
    rw [h2]
    rfl

end PEqualNP.Outside.L_meta_17812

theorem PEqualNP.Outside.L_meta_17812 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (18 : ℕ) →       ∃ (x4 : List (Bool × ℕ × ℕ)) (x5 : ℕ),         x4.length ≤ (18 : ℕ) ∧           x5 < (13 : ℕ) + x4.length ∧             (∀ (x6 : ℕ) (x7 : Bool × ℕ × ℕ), x4[x6]? = Option.some x7 → x7.2.1 < (13 : ℕ) + x6 ∧ x7.2.2 < (13 : ℕ) + x6) ∧               ∀ (x6 : List Bool),                 x6.length = (11 : ℕ) →                   (List.foldl                           (fun (x8 : List Bool) (x9 : Bool × ℕ × ℕ) =>                             have x10 : Bool := x8.getD x9.2.1 Bool.false;                             have x11 : Bool := x8.getD x9.2.2 Bool.false;                             x8 ++ [if x9.1 = Bool.true then x10 && x11 else x10 || x11])                           (Bool.false :: Bool.true :: x6) x4).getD                       x5 Bool.false =                     x1.eval x6 := by
  intro C hC hs
  exact PEqualNP.Outside.L_meta_17812.main C hC hs
