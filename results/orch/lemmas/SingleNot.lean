import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.SingleNot

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

lemma ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


lemma mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := hleg g (by simp)
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this


lemma not_output_value (n : ℕ) (pre post : List Gate) (ins : List ℕ)
    (x : Fin n → Bool) :
    Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, n + pre.length⟩ (List.ofFn x) =
      !((ins.map fun i => (wf pre (List.ofFn x)).getD i false).headD false) := by
  rw [eval_eq]
  have split : pre ++ ⟨GateOp.not, ins⟩ :: post =
      (pre ++ [⟨GateOp.not, ins⟩]) ++ post := by simp
  rw [split]
  have hp : (wf ((pre ++ [⟨GateOp.not, ins⟩]) ++ post) (List.ofFn x)).getD (n + pre.length) false =
      (wf (pre ++ [⟨GateOp.not, ins⟩]) (List.ofFn x)).getD (n + pre.length) false :=
    wf_prefix (pre ++ [({op := GateOp.not, inputs := ins} : Gate)]) post (List.ofFn x) (n + pre.length) (by simp)
  rw [hp]
  rw [wf_snoc]
  have len : (wf pre (List.ofFn x)).length = n + pre.length := by simp [wf_len]
  rw [← len, getD_snoc_eq]
  rfl

lemma first_not_output_impossible (n : ℕ) (pre post : List Gate) (ins : List ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (f : (Fin n → Bool) → Bool)
    (hzero : f (fun _ => false) = false) (hone : f (fun _ => true) = true) :
    ¬ ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, n + pre.length⟩ (List.ofFn x) = f x := by
  intro computes
  have hz := computes (fun _ => false)
  have ho := computes (fun _ => true)
  rw [not_output_value, hzero] at hz
  rw [not_output_value, hone] at ho
  cases ins with
  | nil => simp at hz
  | cons a rest =>
    simp only [List.map_cons, List.headD_cons, Bool.not_eq_false', Bool.not_eq_true'] at hz ho
    have hm := mono2 pre hpre
      (List.ofFn (fun _ : Fin n => false)) (List.ofFn (fun _ : Fin n => true))
      (by simp) (ofFn_mono n _ _ (by simp)) a hz
    rw [ho] at hm
    contradiction

lemma unique_not_prefix (pre post : List Gate) (ins : List ℕ)
    (hfan : PEqualNP.MetaComplexity.FanInTwo ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, 0⟩)
    (hone : PEqualNP.NotBracket.notCount ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, 0⟩ = 1) :
    ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or := by
  let _ : DecidableEq GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  intro g hg
  have legal := (hfan g (List.mem_append.mpr (Or.inl hg))).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at legal
  rcases legal with hop | hop | hop
  · exact Or.inl hop
  · exact Or.inr hop
  · have hcount : (pre.filter fun g => decide (g.op = GateOp.not)).length = 0 := by
      simp [PEqualNP.NotBracket.notCount, List.filter_append] at hone
      omega
    have kept : g ∈ pre.filter (fun g => decide (g.op = GateOp.not)) := by
      exact List.mem_filter.mpr ⟨hg, decide_eq_true hop⟩
    rw [List.length_eq_zero_iff.mp hcount] at kept
    contradiction

lemma unique_not_output_impossible (n : ℕ) (pre post : List Gate) (ins : List ℕ)
    (hfan : PEqualNP.MetaComplexity.FanInTwo ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, 0⟩)
    (hone : PEqualNP.NotBracket.notCount ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, 0⟩ = 1)
    (f : (Fin n → Bool) → Bool)
    (hzero : f (fun _ => false) = false) (hfull : f (fun _ => true) = true) :
    ¬ ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, n + pre.length⟩ (List.ofFn x) = f x :=
  first_not_output_impossible n pre post ins (unique_not_prefix pre post ins hfan hone)
    f hzero hfull

lemma and_not_redundant (n : ℕ) (g h : (Fin n → Bool) → Bool)
    (hm : Monotone h) (hfull : (g (fun _ => true) && (!(h (fun _ => true)))) = true) :
    ∀ x, (g x && (!(h x))) = g x := by
  have hf : h (fun _ => true) = false := by
    have hh := hfull
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hh
    exact hh.2
  intro x
  have hx := hm (show x ≤ (fun _ => true) from fun _ => by simp)
  rw [hf] at hx
  have heq : h x = false := by cases he : h x <;> simp_all [Bool.le_iff_imp]
  simp [heq]

lemma or_not_redundant (n : ℕ) (g h : (Fin n → Bool) → Bool)
    (hm : Monotone h) (hzero : (g (fun _ => false) || (!(h (fun _ => false)))) = false) :
    ∀ x, (g x || (!(h x))) = g x := by
  have hf : h (fun _ => false) = true := by
    cases hh : h (fun _ => false) <;> simp_all
  intro x
  have hx := hm (show (fun _ => false) ≤ x from fun _ => by simp)
  rw [hf] at hx
  have heq : h x = true := by cases he : h x <;> simp_all [Bool.le_iff_imp]
  simp [heq]

end PEqualNP.Outside.L_meta_2592.SingleNot
