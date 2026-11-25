import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2056_aux.SumAndCountTransport

open PEqualNP.CircuitLowerBounds

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

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


theorem relabel_mono {n m : ℕ} (π : Fin n → Fin m) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) : PEqualNP.MetaComplexity.Monotone2 (relabel n m π C) := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
  exact ⟨(hm h hh).1, by simpa [relGate] using (hm h hh).2⟩

theorem relabel_eval {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    (relabel n m π C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) :=
  (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output


lemma relabel_size {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) :
    (relabel n m π C).size = C.size := by simp [relabel, Circuit.size]


noncomputable def andCount (C : Circuit) : ℕ :=
  {i : Fin C.gates.length | (C.gates.get i).op = GateOp.and}.ncard

lemma relabel_andCount {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) :
    andCount (relabel n m π C) = andCount C := by
  unfold andCount
  refine Set.ncard_congr
    (fun i _ => (⟨i.val, by simpa only [relabel, List.length_map] using i.isLt⟩ :
      Fin C.gates.length)) ?_ ?_ ?_
  · intro i hi
    change ((relabel n m π C).gates.get i).op = GateOp.and at hi
    change (C.gates.get ⟨i.val, _⟩).op = GateOp.and
    have hi' : ((C.gates.map (relGate n m π)).get
        ⟨i.val, by simpa only [relabel] using i.isLt⟩).op = GateOp.and := hi
    rw [List.get_eq_getElem, List.getElem_map] at hi'
    exact hi'
  · intro a b ha hb he
    exact Fin.ext (congrArg (fun k : Fin C.gates.length => k.val) he)
  · intro b hb
    let a : Fin (relabel n m π C).gates.length :=
      ⟨b.val, by simpa only [relabel, List.length_map] using b.isLt⟩
    refine ⟨a, ?_, Fin.ext rfl⟩
    change (C.gates.get b).op = GateOp.and at hb
    change ((relabel n m π C).gates.get a).op = GateOp.and
    simpa only [a, relabel, relGate, List.get_eq_getElem, List.getElem_map] using hb

def negLine : Fin 26 → Fin 26 :=
  fun k => Fin.addCases (m := 13) (n := 13) (Fin.castAdd 13)
    (fun l : Fin 13 => Fin.natAdd 13 (-l)) k

lemma negLine_involutive : ∀ k, negLine (negLine k) = k := by decide

lemma negLine_point (p : Fin 13) : negLine (Fin.castAdd 13 p) = Fin.castAdd 13 p := by
  simp [negLine]

lemma negLine_line (l : Fin 13) : negLine (Fin.natAdd 13 l) = Fin.natAdd 13 (-l) := by
  change Fin.addCases (m := 13) (n := 13) (Fin.castAdd 13)
    (fun q : Fin 13 => Fin.natAdd 13 (-q)) (Fin.natAdd 13 l) = Fin.natAdd 13 (-l)
  rw [Fin.addCases_right]

abbrev sumI (p l : Fin 13) : Prop := (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
abbrev diffI (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

lemma sum_diff : ∀ p l, sumI p l ↔ diffI p (-l) := by decide

lemma neg_neg : ∀ l : Fin 13, -(-l) = l := by decide

def sumFun (x : Fin 26 → Bool) : Bool :=
  decide (∃ p l : Fin 13, sumI p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)

def diffFun (x : Fin 26 → Bool) : Bool :=
  decide (∃ p l : Fin 13, diffI p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)

lemma function_transport (x : Fin 26 → Bool) : sumFun (x ∘ negLine) = diffFun x := by
  unfold sumFun diffFun
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨p, l, hi, hp, hl⟩
    exact ⟨p, -l, (sum_diff p l).mp hi, by simpa [Function.comp_def, negLine_point] using hp,
      by simpa only [Function.comp_apply, negLine_line] using hl⟩
  · rintro ⟨p, l, hi, hp, hl⟩
    refine ⟨p, -l, (sum_diff p (-l)).mpr ?_, ?_, ?_⟩
    · simpa only [neg_neg] using hi
    · simpa only [Function.comp_apply, negLine_point] using hp
    · simpa only [Function.comp_apply, negLine_line, neg_neg] using hl

theorem sum_lower_of_difference
    (hDiff : ∀ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 C x = diffFun x) →
      13 ≤ andCount C)
    (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hF : ∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 C x = sumFun x) :
    13 ≤ andCount C := by
  have h := hDiff (relabel 26 26 negLine C) (relabel_mono negLine C hC) (fun x => by
    change (relabel 26 26 negLine C).eval (List.ofFn x) = diffFun x
    rw [relabel_eval]
    exact (hF (x ∘ negLine)).trans (function_transport x))
  simpa only [relabel_andCount] using h

end PEqualNP.Outside.L_meta_2056_aux.SumAndCountTransport
