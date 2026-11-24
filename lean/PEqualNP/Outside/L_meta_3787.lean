import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3787

open PEqualNP.CircuitLowerBounds

def h8step (W : List Bool) (g : Gate) : List Bool :=
  W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

def h8rowGates (L acc c a b d e : ℕ) : List Gate :=
  [⟨GateOp.or, [a, b]⟩, ⟨GateOp.or, [L, d]⟩,
    ⟨GateOp.or, [L + 1, e]⟩, ⟨GateOp.and, [c, L + 2]⟩,
    ⟨GateOp.or, [acc, L + 3]⟩]

lemma h8row_length (L acc c a b d e : ℕ) :
    (h8rowGates L acc c a b d e).length = 5 := rfl

lemma h8row_monotone (L acc c a b d e : ℕ) :
    ∀ g ∈ h8rowGates L acc c a b d e,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [h8rowGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

lemma h8row_eval (W : List Bool) (acc c a b d e : ℕ)
    (hacc : acc < W.length) (hc : c < W.length) (ha : a < W.length)
    (hb : b < W.length) (hd : d < W.length) (he : e < W.length) :
    (h8rowGates W.length acc c a b d e).foldl h8step W =
      W ++ [W.getD a false || W.getD b false,
        W.getD a false || W.getD b false || W.getD d false,
        W.getD a false || W.getD b false || W.getD d false || W.getD e false,
        W.getD c false &&
          (W.getD a false || W.getD b false || W.getD d false || W.getD e false),
        W.getD acc false || (W.getD c false &&
          (W.getD a false || W.getD b false || W.getD d false || W.getD e false))] := by
  simp (disch := omega) [h8rowGates, h8step, GateOp.eval, List.getD_append,
    List.getD_append_right, List.getD_cons_zero, List.getD_cons_succ,
    List.append_assoc, -List.getD_eq_getElem?_getD]

lemma h8row_preserves (W : List Bool) (acc c a b d e : ℕ)
    (hacc : acc < W.length) (hc : c < W.length) (ha : a < W.length)
    (hb : b < W.length) (hd : d < W.length) (he : e < W.length)
    (i : ℕ) (hi : i < W.length) :
    ((h8rowGates W.length acc c a b d e).foldl h8step W).getD i false =
      W.getD i false := by
  rw [h8row_eval W acc c a b d e hacc hc ha hb hd he]
  exact List.getD_append _ _ _ _ hi

lemma h8row_output (W : List Bool) (acc c a b d e : ℕ)
    (hacc : acc < W.length) (hc : c < W.length) (ha : a < W.length)
    (hb : b < W.length) (hd : d < W.length) (he : e < W.length) :
    ((h8rowGates W.length acc c a b d e).foldl h8step W).getD
      (W.length + 4) false =
        (W.getD acc false || (W.getD c false &&
          (W.getD a false || W.getD b false || W.getD d false || W.getD e false))) := by
  rw [h8row_eval W acc c a b d e hacc hc ha hb hd he]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

lemma h8row_output_balanced (W : List Bool) (acc c a b d e : ℕ)
    (hacc : acc < W.length) (hc : c < W.length) (ha : a < W.length)
    (hb : b < W.length) (hd : d < W.length) (he : e < W.length) :
    ((h8rowGates W.length acc c a b d e).foldl h8step W).getD
      (W.length + 4) false =
        (W.getD acc false || (W.getD c false &&
          ((W.getD a false || W.getD b false) ||
            (W.getD d false || W.getD e false)))) := by
  simpa only [Bool.or_assoc] using h8row_output W acc c a b d e hacc hc ha hb hd he

end PEqualNP.Outside.L_meta_3787
