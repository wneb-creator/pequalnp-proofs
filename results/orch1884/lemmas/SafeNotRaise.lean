import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.SafeNot

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def above (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false ≤ z.getD i false

lemma eval_mono (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    (w z : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false ≤ z.getD i false) :
    g.op.eval (g.inputs.map (fun i => w.getD i false)) ≤
      g.op.eval (g.inputs.map (fun i => z.getD i false)) := by
  apply Bool.le_iff_imp.mpr
  intro hw
  rcases hg with hg | hg
  · rw [hg] at hw ⊢
    change (g.inputs.map (fun i => z.getD i false)).all id = true
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    apply Bool.le_iff_imp.mp (h i hi)
    exact List.all_eq_true.mp hw _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · rw [hg] at hw ⊢
    obtain ⟨b, hb, ht⟩ := List.any_eq_true.mp hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    apply List.any_eq_true.mpr
    exact ⟨z.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩,
      Bool.le_iff_imp.mp (h i hi) ht⟩

lemma append_above {w z : List Bool} {a b : Bool} (h : above w z) (hab : a ≤ b) :
    above (w ++ [a]) (z ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi,
      List.getD_append _ _ _ _ (h.1 ▸ hi)]
    exact h.2 i
  · by_cases he : i = w.length
    · subst i
      simpa [List.getD_eq_getElem?_getD, h.1] using hab
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp [← h.1]; omega)]

lemma run_above (gs : List Gate) (w z : List Bool) (h : above w z)
    (allowed : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    above (run gs w) (run gs z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    apply ih (step w g) (step z g)
    · exact append_above h (eval_mono g (allowed g (by simp)) w z (fun i _ => h.2 i))
    · intro g' hg'
      exact allowed g' (by simp [hg'])

lemma replace_safe_not (pre post : List Gate) (ins : List Nat) (out : Nat)
    (input : List Bool)
    (allowed : ∀ g ∈ post, g.op = .and ∨ g.op = .or)
    (safe : ((ins.map fun i => (run pre input).getD i false).headD false) = true →
      (Circuit.mk (pre ++ Gate.mk .not ins :: post) out).eval input = true) :
    (Circuit.mk (pre ++ Gate.mk .and [] :: post) out).eval input =
      (Circuit.mk (pre ++ Gate.mk .not ins :: post) out).eval input := by
  have run_form (op : GateOp) (is : List Nat) :
      (Circuit.mk (pre ++ Gate.mk op is :: post) out).eval input =
        (run post (run pre input ++
          [op.eval (is.map fun i => (run pre input).getD i false)])).getD out false := by
    simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons, run]
    rfl
  cases hh : (ins.map fun i => (run pre input).getD i false).headD false with
  | false => simp only [run_form, GateOp.eval, List.map_nil, List.all_nil, hh, Bool.not_false]
  | true =>
    have ht := safe hh
    have hraise :
        (Circuit.mk (pre ++ Gate.mk .not ins :: post) out).eval input ≤
          (Circuit.mk (pre ++ Gate.mk .and [] :: post) out).eval input := by
      rw [run_form, run_form]
      apply (run_above post _ _ ?_ allowed).2 out
      exact append_above ⟨rfl, fun _ => le_rfl⟩ (by simp [GateOp.eval])
    rw [ht] at hraise ⊢
    exact Bool.le_iff_imp.mp hraise rfl

lemma replace_safe_not_function {α : Type} (pre post : List Gate) (ins : List Nat)
    (out : Nat) (input : α → List Bool) (f : α → Bool)
    (allowed : ∀ g ∈ post, g.op = .and ∨ g.op = .or)
    (computes : ∀ x, (Circuit.mk (pre ++ Gate.mk .not ins :: post) out).eval (input x) = f x)
    (safe : ∀ x, (ins.map fun i => (run pre (input x)).getD i false).headD false = true →
      f x = true) :
    ∀ x, (Circuit.mk (pre ++ Gate.mk .and [] :: post) out).eval (input x) = f x := by
  intro x
  rw [replace_safe_not pre post ins out (input x) allowed (by
    intro h; rw [computes]; exact safe x h), computes]


lemma replace_not_le (pre post : List Gate) (ins : List Nat) (out : Nat)
    (input : List Bool) (allowed : ∀ g ∈ post, g.op = .and ∨ g.op = .or) :
    (Circuit.mk (pre ++ Gate.mk .not ins :: post) out).eval input ≤
      (Circuit.mk (pre ++ Gate.mk .and [] :: post) out).eval input := by
  have h := (run_above post
    (run pre input ++ [GateOp.not.eval (ins.map fun i => (run pre input).getD i false)])
    (run pre input ++ [true])
    (append_above ⟨rfl, fun _ => le_rfl⟩ (Bool.le_true _)) allowed).2 out
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    List.map_nil, GateOp.eval, List.all_nil]
  exact h

lemma replace_not_false (pre post : List Gate) (ins : List Nat) (out : Nat)
    (input : List Bool)
    (hfalse : (ins.map fun i => (run pre input).getD i false).headD false = false) :
    (Circuit.mk (pre ++ Gate.mk .and [] :: post) out).eval input =
      (Circuit.mk (pre ++ Gate.mk .not ins :: post) out).eval input := by
  change (run (pre ++ Gate.mk .and [] :: post) input).getD out false =
    (run (pre ++ Gate.mk .not ins :: post) input).getD out false
  simp only [run, List.foldl_append, List.foldl_cons]
  change (run post (run pre input ++ [true])).getD out false =
    (run post (run pre input ++
      [!(ins.map fun i => (run pre input).getD i false).headD false])).getD out false
  rw [hfalse]
  rfl

end PEqualNP.Outside.L_meta_1884.SafeNot
