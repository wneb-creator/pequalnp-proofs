import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_boundary

open PEqualNP.CircuitLowerBounds

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def mask (m : ℕ) (i : Fin 10) : Bool := m.testBit i.val

def edgeMasks : List ℕ :=
  [3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288]

def maximalMasks : List ℕ :=
  [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]

def InputLE (x y : Fin 10 → Bool) : Prop := ∀ i, x i = true → y i = true

set_option maxHeartbeats 0 in
lemma boundary_samples :
    (∀ x : Fin 10 → Bool, target x = false →
      ∃ m ∈ maximalMasks, InputLE x (mask m)) ∧
    (∀ x : Fin 10 → Bool, target x = true →
      ∃ m ∈ edgeMasks, InputLE (mask m) x) := by
  decide +kernel

set_option maxHeartbeats 0 in
lemma boundary_values :
    (∀ m ∈ maximalMasks, target (mask m) = false) ∧
    (∀ m ∈ edgeMasks, target (mask m) = true) := by
  decide +kernel

def MonoInput (h : (Fin 10 → Bool) → Bool) : Prop :=
  ∀ x y, InputLE x y → h x = true → h y = true

lemma independent_boundary {h : (Fin 10 → Bool) → Bool} (hm : MonoInput h)
    (hx : ∃ x, target x = false ∧ h x = true) :
    ∃ m ∈ maximalMasks, h (mask m) = true := by
  obtain ⟨x, hf, hh⟩ := hx
  obtain ⟨m, hmem, hle⟩ := boundary_samples.1 x hf
  exact ⟨m, hmem, hm x (mask m) hle hh⟩

lemma edge_boundary {h : (Fin 10 → Bool) → Bool} (hm : MonoInput h)
    (hx : ∃ x, target x = true ∧ h x = false) :
    ∃ m ∈ edgeMasks, h (mask m) = false := by
  obtain ⟨x, hf, hh⟩ := hx
  obtain ⟨m, hmem, hle⟩ := boundary_samples.2 x hf
  refine ⟨m, hmem, ?_⟩
  cases hmval : h (mask m) with
  | false => rfl
  | true => have := hm (mask m) x hle hmval; simp [hh] at this

lemma boundary_certificate {h : (Fin 10 → Bool) → Bool} (hm : MonoInput h)
    (hmax : ∀ m ∈ maximalMasks, h (mask m) = false)
    (hedge : ∀ m ∈ edgeMasks, h (mask m) = true) :
    ∀ x, h x = target x := by
  intro x
  cases ht : target x with
  | false =>
    cases hh : h x with
    | false => rfl
    | true =>
      obtain ⟨m, hmem, hval⟩ := independent_boundary hm ⟨x, ht, hh⟩
      simp [hmax m hmem] at hval
  | true =>
    obtain ⟨m, hmem, hle⟩ := boundary_samples.2 x ht
    exact hm (mask m) x hle (hedge m hmem)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def WireLE (v w : List Bool) : Prop :=
  v.length = w.length ∧ ∀ i, v.getD i false = true → w.getD i false = true

lemma getD_snoc_ne {α : Type} (v : List α) (a d : α) (i : ℕ) (hi : i ≠ v.length) :
    (v ++ [a]).getD i d = v.getD i d := by
  by_cases hv : i < v.length
  · exact List.getD_append _ _ _ _ hv
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

lemma wireLE_snoc {v w : List Bool} {a b : Bool} (h : WireLE v w)
    (hab : a = true → b = true) : WireLE (v ++ [a]) (w ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hiv : i = v.length
  · subst i
    have ha : a = true := by simpa using hi
    rw [h.1]
    simpa using hab ha
  · rw [getD_snoc_ne _ _ _ _ hiv] at hi
    rw [getD_snoc_ne _ _ _ _ (by rw [← h.1]; exact hiv)]
    exact h.2 i hi

lemma run_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ v w : List Bool, WireLE v w → WireLE (run gs v) (run gs w) := by
  induction gs with
  | nil => intro v w h; exact h
  | cons g gs ih =>
    intro v w h
    change WireLE (run gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]))
      (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]))
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    apply wireLE_snoc h
    rcases hgs g (by simp) with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro hall b hb
      obtain ⟨j, hj, rfl⟩ := hb
      exact h.2 j (hall _ ⟨j, hj, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
      exact ⟨_, ⟨j, hj, rfl⟩, h.2 j hb⟩

def preValue (pre : List Gate) (ins : List ℕ) (x : Fin 10 → Bool) : Bool :=
  (ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false).headD false

lemma preValue_mono (pre : List Gate) (ins : List ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or) :
    MonoInput (preValue pre ins) := by
  intro x y hxy
  have hin : WireLE (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hi10 : i < 10
    · simp [List.getD_eq_getElem?_getD, hi10] at hi ⊢
      exact hxy ⟨i, hi10⟩ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      contradiction
  have hout := run_mono pre hpre (List.ofFn x) (List.ofFn y) hin
  cases ins with
  | nil => simp [preValue]
  | cons j js =>
    simp only [preValue, List.map_cons, List.headD_cons]
    exact hout.2 j

def constGate (b : Bool) : Gate := if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩

def withConst (pre post : List Gate) (o : ℕ) (b : Bool) (x : Fin 10 → Bool) : Bool :=
  Circuit.eval ⟨pre ++ constGate b :: post, o⟩ (List.ofFn x)

def withNot (pre post : List Gate) (ins : List ℕ) (o : ℕ) (x : Fin 10 → Bool) : Bool :=
  Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, o⟩ (List.ofFn x)

lemma withConst_eval (pre post : List Gate) (o : ℕ) (b : Bool) (x : Fin 10 → Bool) :
    withConst pre post o b x =
      (run post (run pre (List.ofFn x) ++ [b])).getD o false := by
  cases b <;> simp [withConst, Circuit.eval, Circuit.wires, run,
    List.foldl_append, List.foldl_cons, constGate, GateOp.eval]

lemma withNot_eval (pre post : List Gate) (ins : List ℕ) (o : ℕ) (x : Fin 10 → Bool) :
    withNot pre post ins o x = withConst pre post o (!(preValue pre ins x)) x := by
  rw [withConst_eval]
  simp only [withNot, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    GateOp.eval]
  rfl

lemma withConst_mono (pre post : List Gate) (o : ℕ) (x : Fin 10 → Bool)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or) :
    withConst pre post o false x = true → withConst pre post o true x = true := by
  rw [withConst_eval, withConst_eval]
  apply (run_mono post hpost _ _ ?_).2 o
  apply wireLE_snoc
  · exact ⟨rfl, fun _ h => h⟩
  · simp

lemma changed_true (pre post : List Gate) (ins : List ℕ) (o : ℕ)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (correct : ∀ x, withNot pre post ins o x = target x)
    {x : Fin 10 → Bool} (changed : withConst pre post o true x ≠ target x) :
    target x = false ∧ preValue pre ins x = true := by
  have hc := correct x
  rw [withNot_eval] at hc
  have hm := withConst_mono pre post o x hpost
  cases hp : preValue pre ins x <;> cases ht : target x <;>
    cases h0 : withConst pre post o false x <;>
    cases h1 : withConst pre post o true x <;> simp_all

lemma changed_false (pre post : List Gate) (ins : List ℕ) (o : ℕ)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (correct : ∀ x, withNot pre post ins o x = target x)
    {x : Fin 10 → Bool} (changed : withConst pre post o false x ≠ target x) :
    target x = true ∧ preValue pre ins x = false := by
  have hc := correct x
  rw [withNot_eval] at hc
  have hm := withConst_mono pre post o x hpost
  cases hp : preValue pre ins x <;> cases ht : target x <;>
    cases h0 : withConst pre post o false x <;>
    cases h1 : withConst pre post o true x <;> simp_all

end PEqualNP.Outside.L_meta_2592_boundary

open PEqualNP.Outside.L_meta_2592_boundary
open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_2592_boundary (pre post : List Gate) (ins : List ℕ) (o : ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (correct : ∀ x, withNot pre post ins o x = target x)
    (essentialTrue : ∃ x, withConst pre post o true x ≠ target x)
    (essentialFalse : ∃ x, withConst pre post o false x ≠ target x) :
    (∃ m ∈ maximalMasks, preValue pre ins (mask m) = true) ∧
    (∃ m ∈ edgeMasks, preValue pre ins (mask m) = false) := by
  have hm := preValue_mono pre ins hpre
  constructor
  · apply independent_boundary hm
    obtain ⟨x, hx⟩ := essentialTrue
    exact ⟨x, changed_true pre post ins o hpost correct hx⟩
  · apply edge_boundary hm
    obtain ⟨x, hx⟩ := essentialFalse
    exact ⟨x, changed_false pre post ins o hpost correct hx⟩
