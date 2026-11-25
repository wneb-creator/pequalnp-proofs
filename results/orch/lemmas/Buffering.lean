import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.Buffering

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def copyGate (i : ℕ) : Gate := ⟨GateOp.and, [i, i]⟩

def shiftedGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (n + ·)⟩

def buffered (n : ℕ) (C : Circuit) : Circuit :=
  ⟨(List.range n).map copyGate ++ C.gates.map (shiftedGate n), n + C.output⟩

lemma getD_append_left (xs ys : List Bool) (i : ℕ) (hi : i < xs.length) :
    (xs ++ ys).getD i false = xs.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right (xs ys : List Bool) (i : ℕ) :
    (xs ++ ys).getD (xs.length + i) false = ys.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

lemma copy_step (xs acc : List Bool) (i : ℕ) (hi : i < xs.length) :
    step (xs ++ acc) (copyGate i) = xs ++ (acc ++ [xs.getD i false]) := by
  have hd := getD_append_left xs acc i hi
  simp only [step, copyGate, List.map_cons, List.map_nil, hd]
  have hb (b : Bool) : GateOp.and.eval [b, b] = b := by cases b <;> rfl
  rw [hb]
  simp [List.append_assoc]

lemma copy_fold (xs : List Bool) (ids : List ℕ)
    (hids : ∀ i ∈ ids, i < xs.length) (acc : List Bool) :
    ((ids.map copyGate).foldl step (xs ++ acc)) =
      xs ++ (acc ++ ids.map (fun i => xs.getD i false)) := by
  induction ids generalizing acc with
  | nil => simp
  | cons i ids ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [copy_step xs acc i (hids i (by simp))]
    rw [ih (fun j hj => hids j (by simp [hj]))]
    simp [List.append_assoc]

lemma range_lookup (xs : List Bool) :
    (List.range xs.length).map (fun i => xs.getD i false) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hil : i < xs.length := by simpa using hi
    simp [List.getD_eq_getElem?_getD, hil]

lemma copies_wires (n : ℕ) (xs : List Bool) (hx : xs.length = n) :
    (((List.range n).map copyGate).foldl step xs) = xs ++ xs := by
  rw [← hx]
  have h := copy_fold xs (List.range xs.length) (by intro i hi; exact List.mem_range.mp hi) []
  simpa only [List.append_nil, List.nil_append, range_lookup] using h

lemma shifted_step (n : ℕ) (pref xs : List Bool) (hp : pref.length = n) (g : Gate) :
    step (pref ++ xs) (shiftedGate n g) = pref ++ step xs g := by
  have he (i : ℕ) : (pref ++ xs).getD (n + i) false = xs.getD i false := by
    rw [← hp]
    exact getD_append_right pref xs i
  simp only [step, shiftedGate, List.map_map]
  simp only [Function.comp_def, he, List.append_assoc]

lemma shifted_fold (n : ℕ) (pref : List Bool) (hp : pref.length = n) (gs : List Gate)
    (xs : List Bool) :
    ((gs.map (shiftedGate n)).foldl step (pref ++ xs)) = pref ++ gs.foldl step xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, shifted_step n pref xs hp g]
    exact ih (step xs g)

lemma buffered_wires (n : ℕ) (C : Circuit) (xs : List Bool) (hx : xs.length = n) :
    (buffered n C).wires xs = xs ++ C.wires xs := by
  change ((List.range n).map copyGate ++ C.gates.map (shiftedGate n)).foldl step xs =
    xs ++ C.gates.foldl step xs
  rw [List.foldl_append, copies_wires n xs hx, shifted_fold n xs hx C.gates xs]

lemma buffered_eval (n : ℕ) (C : Circuit) (xs : List Bool) (hx : xs.length = n) :
    (buffered n C).eval xs = C.eval xs := by
  unfold Circuit.eval
  rw [buffered_wires n C xs hx]
  change (xs ++ C.wires xs).getD (n + C.output) false = (C.wires xs).getD C.output false
  rw [← hx]
  exact getD_append_right xs (C.wires xs) C.output

lemma buffered_size (n : ℕ) (C : Circuit) : (buffered n C).size = C.size + n := by
  simp [buffered, Circuit.size, Nat.add_comm]

lemma buffered_gate_early (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < n) :
    gateAt (buffered n C) j = copyGate j := by
  simp [gateAt, buffered, List.getD_eq_getElem?_getD, List.getElem?_append_left, hj]

lemma buffered_gate_late (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (buffered n C) (n + j) = shiftedGate n (gateAt C j) := by
  simp [gateAt, buffered, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

lemma buffered_ao (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) : IsAO2 n (buffered n C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [buffered, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
    · exact Or.inl rfl
    · exact hAO.1 g hg
  · intro j hj w hw
    have hj' : j < n + C.gates.length := by simpa [buffered] using hj
    by_cases hjn : j < n
    · rw [buffered_gate_early n C j hjn] at hw
      simp only [copyGate, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, j = n + k := ⟨j - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rw [buffered_gate_late n C k hk] at hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      have hul := hAO.2.1 k hk u hu
      omega
  · intro g hg
    simp only [buffered, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
    · rfl
    · simpa [shiftedGate] using hAO.2.2 g hg

lemma buffered_or_inputs (n : ℕ) (C : Circuit) (g : Gate)
    (hg : g ∈ (buffered n C).gates) (hop : g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) : n ≤ w := by
  simp only [buffered, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
  · cases hop
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    omega

lemma buffered_orIn_empty (n : ℕ) (C : Circuit) (g : ℕ) :
    orIn n (buffered n C) (n + g) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with hi | ⟨k, hk, hr, hop, hin⟩
  · have hil := i.isLt
    omega
  · have hlo := buffered_or_inputs n C (gateAt (buffered n C) k)
      (gateAt_mem (buffered n C) k hk) hop i hin
    have hil := i.isLt
    omega

lemma buffered_count_zero (n : ℕ) (C : Circuit) (s : ℕ → Bool) :
    tCount n (buffered n C) s = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have h : IsTwoColour n (buffered n C) s g := (Finset.mem_filter.mp hg).2
  obtain ⟨i, hi, hs⟩ := h.2.2.1
  rw [buffered_orIn_empty n C g] at hi
  simp at hi

lemma additive_buffering (n : ℕ) (C : Circuit) (s : ℕ → Bool) (hAO : IsAO2 n C) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size + n ∧
      circuitFun n D = circuitFun n C ∧ tCount n D s = 0 := by
  refine ⟨buffered n C, buffered_ao n C hAO, buffered_size n C, ?_, buffered_count_zero n C s⟩
  funext x
  exact buffered_eval n C (List.ofFn x) (by simp)

end PEqualNP.Outside.L_meta_4675.Buffering
