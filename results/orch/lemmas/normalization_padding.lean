import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451_aux.Padding

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def padWire (N w : ℕ) : ℕ :=
  if w < N then w else if w < N + N then w + 1 else w + 2

def padGate (N : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (padWire N)⟩

def padCircuit (N : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (padGate N), padWire N C.output⟩

def padStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma padWire_lt (N s w : ℕ) (_hs : N + N ≤ s) (hw : w < s) :
    padWire N w < s + 2 := by
  unfold padWire
  split_ifs <;> omega

lemma padWire_ge (N s w : ℕ) (hs : N + N ≤ s) (hw : s ≤ w) :
    padWire N w = w + 2 := by
  unfold padWire
  split_ifs <;> omega

lemma append_agree (N : ℕ) (a b : List Bool) (hl : b.length = a.length + 2)
    (hn : N + N ≤ a.length)
    (h : ∀ i, b.getD (padWire N i) false = a.getD i false) (v : Bool) :
    ∀ i, (b ++ [v]).getD (padWire N i) false = (a ++ [v]).getD i false := by
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ (by rw [hl]; exact padWire_lt N _ i hn hi),
      List.getD_append _ _ _ _ hi]
    exact h i
  · rw [padWire_ge N a.length i hn (by omega),
      List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

lemma step_agree (N : ℕ) (g : Gate) (a b : List Bool) (hl : b.length = a.length + 2)
    (hn : N + N ≤ a.length)
    (h : ∀ i, b.getD (padWire N i) false = a.getD i false) :
    ∀ i, (padStep b (padGate N g)).getD (padWire N i) false =
      (padStep a g).getD i false := by
  have hg : (padGate N g).op.eval
      ((padGate N g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    simp only [padGate, List.map_map, Function.comp_def, h]
  unfold padStep
  rw [hg]
  exact append_agree N a b hl hn h _

lemma fold_agree (N : ℕ) (gs : List Gate) : ∀ (a b : List Bool),
    b.length = a.length + 2 → N + N ≤ a.length →
    (∀ i, b.getD (padWire N i) false = a.getD i false) →
    ∀ i, ((gs.map (padGate N)).foldl padStep b).getD (padWire N i) false =
      (gs.foldl padStep a).getD i false := by
  induction gs with
  | nil => intro a b hl hn h; exact h
  | cons g gs ih =>
    intro a b hl hn h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [padStep, hl]
    · simp only [padStep, List.length_append, List.length_singleton]
      omega
    · exact step_agree N g a b hl hn h

def restrictInput (N : ℕ) (z : Fin ((N + 1) + (N + 1)) → Bool) :
    Fin (N + N) → Bool :=
  fun i => z ⟨padWire N i.val, by
    have := padWire_lt N (N + N) i.val (by omega) i.isLt
    omega⟩

lemma wires_agree (N : ℕ) (C : Circuit) (z : Fin ((N + 1) + (N + 1)) → Bool) :
    ∀ i, ((padCircuit N C).wires (List.ofFn z)).getD (padWire N i) false =
      (C.wires (List.ofFn (restrictInput N z))).getD i false := by
  apply fold_agree N C.gates
  · simp
    omega
  · simp
  · intro i
    by_cases hi : i < N + N
    · have hp : padWire N i < (N + 1) + (N + 1) := by
        have := padWire_lt N (N + N) i (by omega) hi
        omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hp,
        dite_eq_left hi, Option.getD_some, restrictInput]
    · have hp : (N + 1) + (N + 1) ≤ padWire N i := by
        rw [padWire_ge N (N + N) i (by omega) (by omega)]
        omega
      rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using hp),
        List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hi)]

lemma circuitFun_agree (N : ℕ) (C : Circuit)
    (z : Fin ((N + 1) + (N + 1)) → Bool) :
    circuitFun ((N + 1) + (N + 1)) (padCircuit N C) z =
      circuitFun (N + N) C (restrictInput N z) :=
  wires_agree N C z C.output

lemma size_pad (N : ℕ) (C : Circuit) : (padCircuit N C).size = C.size := by
  simp [padCircuit, Circuit.size]

lemma monotone_pad (N : ℕ) (C : Circuit) (hC : Monotone2 C) :
    Monotone2 (padCircuit N C) := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  simpa [padGate] using hC q hq

lemma gateAt_pad (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    NestedCover.gateAt (padCircuit N C) j = padGate N (NestedCover.gateAt C j) := by
  simp [NestedCover.gateAt, padCircuit, List.getD_eq_getElem?_getD, hj]

lemma readsBack_pad (N : ℕ) (C : Circuit) (hC : NestedCover.ReadsBack (N + N) C) :
    NestedCover.ReadsBack ((N + 1) + (N + 1)) (padCircuit N C) := by
  intro j hj i hi
  have hj' : j < C.gates.length := by simpa [padCircuit] using hj
  rw [gateAt_pad N C j hj'] at hi
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
  have := padWire_lt N (N + N + j) w (by omega) (hC j hj' w hw)
  omega

def padIncidence (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin (N + 1)) : Prop :=
  ∃ hp : p.val < N, ∃ hl : l.val < N, I ⟨p.val, hp⟩ ⟨l.val, hl⟩

lemma point_misses (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin (N + 1)) :
    ∃ l : Fin (N + 1), ¬ padIncidence N I p l := by
  refine ⟨⟨N, by omega⟩, ?_⟩
  rintro ⟨hp, hl, hi⟩
  exact (Nat.lt_irrefl N) hl

lemma line_misses (N : ℕ) (I : Fin N → Fin N → Prop) (l : Fin (N + 1)) :
    ∃ p : Fin (N + 1), ¬ padIncidence N I p l := by
  refine ⟨⟨N, by omega⟩, ?_⟩
  rintro ⟨hp, hl, hi⟩
  exact (Nat.lt_irrefl N) hp

lemma noFourCycle_pad (N : ℕ) (I : Fin N → Fin N → Prop)
    (hI : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) :
    ∀ p p' l l' : Fin (N + 1), p ≠ p' → l ≠ l' →
      ¬ (padIncidence N I p l ∧ padIncidence N I p l' ∧
        padIncidence N I p' l ∧ padIncidence N I p' l') := by
  intro p p' l l' hpp hll h
  obtain ⟨hp, hl, hpl⟩ := h.1
  obtain ⟨_, hl', hpl'⟩ := h.2.1
  obtain ⟨hp', _, hp'l⟩ := h.2.2.1
  obtain ⟨_, _, hp'l'⟩ := h.2.2.2
  apply hI ⟨p.val, hp⟩ ⟨p'.val, hp'⟩ ⟨l.val, hl⟩ ⟨l'.val, hl'⟩
  · intro he
    apply hpp
    exact Fin.ext (congrArg (fun x : Fin N => x.val) he)
  · intro he
    apply hll
    exact Fin.ext (congrArg (fun x : Fin N => x.val) he)
  · exact ⟨hpl, hpl', hp'l, hp'l'⟩

lemma restrict_point (N : ℕ) (z : Fin ((N + 1) + (N + 1)) → Bool) (p : Fin N) :
    restrictInput N z (Fin.castAdd N p) =
      z (Fin.castAdd (N + 1) p.castSucc) := by
  unfold restrictInput
  congr 1
  apply Fin.ext
  simp [padWire, p.isLt]

lemma restrict_line (N : ℕ) (z : Fin ((N + 1) + (N + 1)) → Bool) (l : Fin N) :
    restrictInput N z (Fin.natAdd N l) =
      z (Fin.natAdd (N + 1) l.castSucc) := by
  unfold restrictInput
  congr 1
  apply Fin.ext
  change padWire N (N + l.val) = N + 1 + l.val
  unfold padWire
  split_ifs <;> omega

lemma computes_pad (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∀ z : Fin ((N + 1) + (N + 1)) → Bool,
      circuitFun ((N + 1) + (N + 1)) (padCircuit N C) z = true ↔
      ∃ p l : Fin (N + 1), padIncidence N I p l ∧
        z (Fin.castAdd (N + 1) p) = true ∧ z (Fin.natAdd (N + 1) l) = true := by
  intro z
  rw [circuitFun_agree, sem]
  constructor
  · rintro ⟨p, l, hi, hp, hl⟩
    refine ⟨p.castSucc, l.castSucc, ⟨p.isLt, l.isLt, hi⟩, ?_, ?_⟩
    · simpa only [restrict_point] using hp
    · simpa only [restrict_line] using hl
  · rintro ⟨p, l, ⟨hp, hl, hi⟩, hz, hw⟩
    refine ⟨⟨p.val, hp⟩, ⟨l.val, hl⟩, hi, ?_, ?_⟩
    · rw [restrict_point]
      exact hz
    · rw [restrict_line]
      exact hw

end PEqualNP.Outside.L_meta_3451_aux.Padding
