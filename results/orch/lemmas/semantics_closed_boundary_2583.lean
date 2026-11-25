import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.ClosedBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def target (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (x : Fin (N + N) → Bool) : Bool :=
  decide (∃ p l : Fin N, I p l ∧
    x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)

def boundary {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) : Fin (N + N) → Bool :=
  Fin.addCases (fun p => decide (p ∈ A)) (fun l => decide (∀ p ∈ A, ¬I p l))

def InputLE {n : ℕ} (x y : Fin n → Bool) : Prop :=
  ∀ i, x i = true → y i = true

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

lemma circuit_mono {n : ℕ} (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C)
    {x y : Fin n → Bool} (hxy : InputLE x y) :
    circuitFun n C x = true → circuitFun n C y = true := by
  have hin : WireLE (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hin : i < n
    · simp [List.getD_eq_getElem?_getD, hin] at hi ⊢
      exact hxy ⟨i, hin⟩ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      contradiction
  exact (run_mono C.gates hC (List.ofFn x) (List.ofFn y) hin).2 C.output

lemma boundary_point {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) (p : Fin N) :
    boundary I A (Fin.castAdd N p) = decide (p ∈ A) := by
  simp [boundary, Fin.addCases]

lemma boundary_line {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) (l : Fin N) :
    boundary I A (Fin.natAdd N l) = decide (∀ p ∈ A, ¬I p l) := by
  simp [boundary, Fin.addCases]

lemma boundary_false {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) : target N I (boundary I A) = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  obtain ⟨p, l, hi, hp, hl⟩ := of_decide_eq_true ht
  rw [boundary_point] at hp
  rw [boundary_line] at hl
  exact (of_decide_eq_true hl) p (of_decide_eq_true hp) hi

lemma negative_below_boundary {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (x : Fin (N + N) → Bool) (hx : target N I x = false) :
    InputLE x (boundary I (Finset.univ.filter fun p => x (Fin.castAdd N p) = true)) := by
  intro v
  refine Fin.addCases (fun p => ?_) (fun l => ?_) v
  · intro hp
    rw [boundary_point]
    exact decide_eq_true (by simp [hp])
  · intro hl
    rw [boundary_line]
    apply decide_eq_true
    intro p hp hi
    have hp' : x (Fin.castAdd N p) = true := (Finset.mem_filter.mp hp).2
    have ht : target N I x = true := decide_eq_true ⟨p, l, hi, hp', hl⟩
    exact Bool.false_ne_true (hx.symm.trans ht)

lemma edge_below_positive {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (x : Fin (N + N) → Bool) (hx : target N I x = true) :
    ∃ p l : Fin N, I p l ∧
      InputLE (setInput {Fin.castAdd N p, Fin.natAdd N l}) x := by
  obtain ⟨p, l, hi, hp, hl⟩ := of_decide_eq_true hx
  refine ⟨p, l, hi, ?_⟩
  intro v hv
  have hmem : v ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) :=
    of_decide_eq_true hv
  rcases Finset.mem_insert.mp hmem with rfl | hmem
  · exact hp
  · have heq := Finset.mem_singleton.mp hmem
    rw [heq]
    exact hl

lemma boundary_correct {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (positive : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C (setInput {Fin.castAdd N p, Fin.natAdd N l}) = true)
    (negative : ∀ A : Finset (Fin N), circuitFun (N + N) C (boundary I A) = false) :
    ∀ x : Fin (N + N) → Bool, circuitFun (N + N) C x = target N I x := by
  intro x
  cases ht : target N I x with
  | false =>
    apply Bool.eq_false_iff.mpr
    intro hc
    have hle := negative_below_boundary I x ht
    have hy := circuit_mono C hC.1 hle hc
    have hn := negative (Finset.univ.filter fun p => x (Fin.castAdd N p) = true)
    exact Bool.false_ne_true (hn.symm.trans hy)
  | true =>
    obtain ⟨p, l, hi, hle⟩ := edge_below_positive I x ht
    exact circuit_mono C hC.1 hle (positive p l hi)

def closure {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) : Finset (Fin N) :=
  Finset.univ.filter fun p => ∀ l : Fin N, (∀ a ∈ A, ¬I a l) → ¬I p l

lemma mem_closure {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) (p : Fin N) :
    p ∈ closure I A ↔ ∀ l : Fin N, (∀ a ∈ A, ¬I a l) → ¬I p l := by
  simp [closure]

lemma subset_closure {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) : A ⊆ closure I A := by
  intro p hp
  rw [mem_closure]
  intro l hl
  exact hl p hp

lemma avoid_closure {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) (l : Fin N) :
    (∀ p ∈ closure I A, ¬I p l) ↔ ∀ p ∈ A, ¬I p l := by
  constructor
  · intro h p hp
    exact h p (subset_closure I A hp)
  · intro h p hp
    exact (mem_closure I A p).mp hp l h

lemma closure_idempotent {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) : closure I (closure I A) = closure I A := by
  ext p
  rw [mem_closure I (closure I A) p, mem_closure I A p]
  constructor
  · intro h l hl
    exact h l ((avoid_closure I A l).mpr hl)
  · intro h l hl
    exact h l ((avoid_closure I A l).mp hl)

lemma boundary_le_closure {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) : InputLE (boundary I A) (boundary I (closure I A)) := by
  intro v
  refine Fin.addCases (fun p => ?_) (fun l => ?_) v
  · rw [boundary_point, boundary_point]
    intro hp
    exact decide_eq_true (subset_closure I A (of_decide_eq_true hp))
  · rw [boundary_line, boundary_line]
    intro hl
    exact decide_eq_true ((avoid_closure I A l).mpr (of_decide_eq_true hl))

lemma closed_boundary_correct {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (positive : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C (setInput {Fin.castAdd N p, Fin.natAdd N l}) = true)
    (negative : ∀ A : Finset (Fin N), closure I A = A →
      circuitFun (N + N) C (boundary I A) = false) :
    ∀ x : Fin (N + N) → Bool, circuitFun (N + N) C x = target N I x := by
  apply boundary_correct I C hC positive
  intro A
  apply Bool.eq_false_iff.mpr
  intro hc
  have hy := circuit_mono C hC.1 (boundary_le_closure I A) hc
  have hn := negative (closure I A) (closure_idempotent I A)
  exact Bool.false_ne_true (hn.symm.trans hy)

end PEqualNP.Outside.L_meta_2583_aux.ClosedBoundary
