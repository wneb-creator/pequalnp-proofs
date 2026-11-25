import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.ForcedGateSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def forcedEval (n : ℕ) (pre post : List Gate) (b : Bool) (out : ℕ)
    (x : Fin n → Bool) : Bool :=
  (run post (run pre (List.ofFn x) ++ [b])).getD out false

lemma getD_le {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys) (i : ℕ) :
    xs.getD i false ≤ ys.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab h ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

lemma and_mono : ∀ a b c d : Bool, a ≤ b → c ≤ d →
    (a && c) ≤ (b && d) := by decide

lemma or_mono : ∀ a b c d : Bool, a ≤ b → c ≤ d →
    (a || c) ≤ (b || d) := by decide

lemma all_le {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys) :
    xs.all id ≤ ys.all id := by
  induction h with
  | nil => simp
  | cons hab h ih =>
    simpa only [List.all_cons, id_eq] using and_mono _ _ _ _ hab ih

lemma any_le {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys) :
    xs.any id ≤ ys.any id := by
  induction h with
  | nil => simp
  | cons hab h ih =>
    simpa only [List.any_cons, id_eq] using or_mono _ _ _ _ hab ih

lemma snoc_le {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys)
    {a b : Bool} (hab : a ≤ b) :
    List.Forall₂ (· ≤ ·) (xs ++ [a]) (ys ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons hxy h ih => exact .cons hxy ih

lemma op_le (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) ≤
      g.op.eval (g.inputs.map fun i => ys.getD i false) := by
  have hm : List.Forall₂ (· ≤ ·) (g.inputs.map fun i => xs.getD i false)
      (g.inputs.map fun i => ys.getD i false) := by
    induction g.inputs with
    | nil => exact .nil
    | cons i is ih => exact .cons (getD_le h i) ih
  rcases hg with hg | hg
  · simpa [hg, GateOp.eval] using all_le hm
  · simpa [hg, GateOp.eval] using any_le hm

lemma step_le (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys) :
    List.Forall₂ (· ≤ ·) (step xs g) (step ys g) :=
  snoc_le h (op_le g hg h)

lemma run_le (gs : List Gate) (hk : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys) :
    List.Forall₂ (· ≤ ·) (run gs xs) (run gs ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun g' hg' => hk g' (by simp [hg']))
      (step_le g (hk g (by simp)) h)

lemma ofFn_le {n : ℕ} (x y : Fin n → Bool) (h : x ≤ y) :
    List.Forall₂ (· ≤ ·) (List.ofFn x) (List.ofFn y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (h 0) (ih _ _ (fun i => h i.succ))

lemma forced_monotone (n : ℕ) (pre post : List Gate) (b : Bool) (out : ℕ)
    (hp : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    (hs : ∀ g ∈ post, g.op = .and ∨ g.op = .or) :
    Monotone (forcedEval n pre post b out) := by
  intro x y hxy
  exact getD_le (run_le post hs
    (snoc_le (run_le pre hp (ofFn_le x y hxy)) le_rfl)) out

lemma forced_agrees (n : ℕ) (pre post : List Gate) (g : Gate) (b : Bool)
    (out : ℕ) (x : Fin n → Bool)
    (hv : g.op.eval (g.inputs.map fun i =>
      (run pre (List.ofFn x)).getD i false) = b) :
    forcedEval n pre post b out x =
      circuitFun n ⟨pre ++ g :: post, out⟩ x := by
  simp only [forcedEval, circuitFun, Circuit.eval, Circuit.wires,
    List.foldl_append, List.foldl_cons]
  change _ = (run post (step (run pre (List.ofFn x)) g)).getD out false
  rw [step, hv]

lemma forced_false_le (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hs : ∀ g' ∈ post, g'.op = .and ∨ g'.op = .or)
    (x : Fin n → Bool) :
    forcedEval n pre post false out x ≤
      circuitFun n ⟨pre ++ g :: post, out⟩ x := by
  have hsame : List.Forall₂ (· ≤ ·) (run pre (List.ofFn x))
      (run pre (List.ofFn x)) := List.forall₂_refl _
  have h := getD_le (run_le post hs (snoc_le hsame
    (show false ≤ g.op.eval (g.inputs.map fun i =>
      (run pre (List.ofFn x)).getD i false) from bot_le))) out
  simp only [circuitFun, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
  change _ ≤ (run post (step (run pre (List.ofFn x)) g)).getD out false
  exact h

lemma le_forced_true (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hs : ∀ g' ∈ post, g'.op = .and ∨ g'.op = .or)
    (x : Fin n → Bool) :
    circuitFun n ⟨pre ++ g :: post, out⟩ x ≤
      forcedEval n pre post true out x := by
  have hsame : List.Forall₂ (· ≤ ·) (run pre (List.ofFn x))
      (run pre (List.ofFn x)) := List.forall₂_refl _
  have h := getD_le (run_le post hs (snoc_le hsame
    (show g.op.eval (g.inputs.map fun i =>
      (run pre (List.ofFn x)).getD i false) ≤ true from le_top))) out
  simp only [circuitFun, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
  change (run post (step (run pre (List.ofFn x)) g)).getD out false ≤ _
  exact h

end PEqualNP.Outside.L_meta_2583_aux.ForcedGateSemantics
