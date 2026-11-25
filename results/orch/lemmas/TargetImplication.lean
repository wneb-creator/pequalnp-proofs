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

def oneMap (n p w : ℕ) : ℕ :=
  if w < p then n + w else if w < n then w else p + w

def oneGate (n p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (oneMap n p)⟩

def oneBuffer (n p : ℕ) (C : Circuit) : Circuit :=
  ⟨(List.range p).map copyGate ++ C.gates.map (oneGate n p), oneMap n p C.output⟩

lemma take_lookup (xs : List Bool) (p : ℕ) (hp : p ≤ xs.length) :
    (List.range p).map (fun i => xs.getD i false) = xs.take p := by
  apply List.ext_getElem
  · simp [List.length_take, hp]
  · intro i hi hj
    have hip : i < p := by simpa using hi
    have hil : i < xs.length := by omega
    simp [List.getD_eq_getElem?_getD, hil]

lemma one_copies_wires (n p : ℕ) (hp : p ≤ n) (xs : List Bool) (hx : xs.length = n) :
    (((List.range p).map copyGate).foldl step xs) = xs ++ xs.take p := by
  have h := copy_fold xs (List.range p) (by
    intro i hi
    have := List.mem_range.mp hi
    omega) []
  simpa only [List.append_nil, List.nil_append, take_lookup xs p (by omega)] using h

lemma one_lookup (n p : ℕ) (hp : p ≤ n) (xs acc : List Bool) (hx : xs.length = n) (w : ℕ) :
    (xs ++ xs.take p ++ acc).getD (oneMap n p w) false = (xs ++ acc).getD w false := by
  have ht : (xs.take p).length = p := by simp [List.length_take, hx, hp]
  by_cases hwp : w < p
  · have hwn : w < n := by omega
    simp only [oneMap, ite_eq_left hwp]
    rw [List.append_assoc]
    have he : n + w = xs.length + w := by omega
    rw [he, getD_append_right, getD_append_left (xs.take p) acc w (by omega),
      getD_append_left xs acc w (by omega)]
    simp [List.getD_eq_getElem?_getD, hwp]
  · simp only [oneMap, ite_eq_right hwp]
    by_cases hwn : w < n
    · rw [ite_eq_left hwn, getD_append_left (xs ++ xs.take p) acc w (by simp [hx]; omega)]
      rw [getD_append_left xs (xs.take p) w (by omega), getD_append_left xs acc w (by omega)]
    · rw [ite_eq_right hwn]
      have he1 : p + w = (xs ++ xs.take p).length + (w - n) := by
        simp only [List.length_append, hx, ht]
        omega
      have he2 : w = xs.length + (w - n) := by omega
      rw [he1, getD_append_right, he2, getD_append_right]
      simp [hx]

lemma one_step (n p : ℕ) (hp : p ≤ n) (xs acc : List Bool) (hx : xs.length = n) (g : Gate) :
    step (xs ++ xs.take p ++ acc) (oneGate n p g) =
      xs ++ xs.take p ++ (acc ++ [g.op.eval (g.inputs.map fun w => (xs ++ acc).getD w false)]) := by
  simp only [step, oneGate, List.map_map, Function.comp_def]
  simp_rw [one_lookup n p hp xs acc hx]
  simp only [List.append_assoc]

lemma one_fold (n p : ℕ) (hp : p ≤ n) (xs : List Bool) (hx : xs.length = n)
    (gs : List Gate) (acc : List Bool) :
    ∃ tail : List Bool, gs.foldl step (xs ++ acc) = xs ++ tail ∧
      ((gs.map (oneGate n p)).foldl step (xs ++ xs.take p ++ acc)) = xs ++ xs.take p ++ tail := by
  induction gs generalizing acc with
  | nil => exact ⟨acc, rfl, rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun w => (xs ++ acc).getD w false)
    obtain ⟨tail, h1, h2⟩ := ih (acc ++ [v])
    refine ⟨tail, ?_, ?_⟩
    · simpa only [List.foldl_cons, step, ← List.append_assoc] using h1
    · simpa only [List.map_cons, List.foldl_cons, one_step n p hp xs acc hx g] using h2

lemma oneBuffer_eval (n p : ℕ) (hp : p ≤ n) (C : Circuit) (xs : List Bool) (hx : xs.length = n) :
    (oneBuffer n p C).eval xs = C.eval xs := by
  obtain ⟨tail, h1, h2⟩ := one_fold n p hp xs hx C.gates []
  simp only [List.append_nil] at h1 h2
  have hw : (oneBuffer n p C).wires xs = xs ++ xs.take p ++ tail := by
    change ((List.range p).map copyGate ++ C.gates.map (oneGate n p)).foldl step xs = _
    rw [List.foldl_append, one_copies_wires n p hp xs hx]
    exact h2
  change ((oneBuffer n p C).wires xs).getD (oneMap n p C.output) false =
    (C.wires xs).getD C.output false
  rw [hw, one_lookup n p hp xs tail hx]
  exact congrArg (fun ws : List Bool => ws.getD C.output false) h1.symm

lemma oneBuffer_size (n p : ℕ) (C : Circuit) : (oneBuffer n p C).size = C.size + p := by
  simp [oneBuffer, Circuit.size, Nat.add_comm]

lemma oneBuffer_gate_early (n p : ℕ) (C : Circuit) (j : ℕ) (hj : j < p) :
    gateAt (oneBuffer n p C) j = copyGate j := by
  simp [gateAt, oneBuffer, List.getD_eq_getElem?_getD, List.getElem?_append_left, hj]

lemma oneBuffer_gate_late (n p : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (oneBuffer n p C) (p + j) = oneGate n p (gateAt C j) := by
  simp [gateAt, oneBuffer, List.getD_eq_getElem?_getD, hj]

lemma oneMap_lt (n p B w : ℕ) (_hp : p ≤ n) (hw : w < n + B) : oneMap n p w < n + p + B := by
  unfold oneMap
  split_ifs <;> omega

lemma oneBuffer_ao (n p : ℕ) (hp : p ≤ n) (C : Circuit) (hAO : IsAO2 n C) :
    IsAO2 n (oneBuffer n p C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [oneBuffer, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
    · exact Or.inl rfl
    · exact hAO.1 g hg
  · intro j hj w hw
    have hj' : j < p + C.gates.length := by simpa [oneBuffer] using hj
    by_cases hjp : j < p
    · rw [oneBuffer_gate_early n p C j hjp] at hw
      simp only [copyGate, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, j = p + k := ⟨j - p, by omega⟩
      have hk : k < C.gates.length := by omega
      rw [oneBuffer_gate_late n p C k hk] at hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      have hul := oneMap_lt n p k u hp (hAO.2.1 k hk u hu)
      omega
  · intro g hg
    simp only [oneBuffer, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
    · rfl
    · simpa [oneGate] using hAO.2.2 g hg

lemma oneMap_ge (n p w : ℕ) (hp : p ≤ n) : p ≤ oneMap n p w := by
  unfold oneMap
  split_ifs <;> omega

lemma oneBuffer_or_inputs (n p : ℕ) (hp : p ≤ n) (C : Circuit) (g : Gate)
    (hg : g ∈ (oneBuffer n p C).gates) (hop : g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) : p ≤ w := by
  simp only [oneBuffer, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
  · cases hop
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    exact oneMap_ge n p u hp

lemma oneBuffer_orIn_line (n p : ℕ) (hp : p ≤ n) (C : Circuit) (g : ℕ) (i : Fin n)
    (hi : i ∈ orIn n (oneBuffer n p C) (n + g)) : p ≤ (i : ℕ) := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with hi | ⟨k, hk, hr, hop, hin⟩
  · have hil := i.isLt
    omega
  · exact oneBuffer_or_inputs n p hp C (gateAt (oneBuffer n p C) k)
      (gateAt_mem (oneBuffer n p C) k hk) hop i hin

lemma oneBuffer_count_zero (n p : ℕ) (hp : p ≤ n) (C : Circuit) :
    tCount n (oneBuffer n p C) (fun i => decide (p ≤ i)) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have h : IsTwoColour n (oneBuffer n p C) (fun i => decide (p ≤ i)) g :=
    (Finset.mem_filter.mp hg).2
  obtain ⟨i, hi, hs⟩ := h.2.2.1
  have hlo := oneBuffer_orIn_line n p hp C g i hi
  simp [hlo] at hs

lemma one_sided_buffering (p l : ℕ) (C : Circuit) (hAO : IsAO2 (p + l) C) :
    ∃ D : Circuit, IsAO2 (p + l) D ∧ D.size = C.size + p ∧
      circuitFun (p + l) D = circuitFun (p + l) C ∧
      tCount (p + l) D (fun i => decide (p ≤ i)) = 0 := by
  refine ⟨oneBuffer (p + l) p C, oneBuffer_ao (p + l) p (by omega) C hAO,
    oneBuffer_size (p + l) p C, ?_, oneBuffer_count_zero (p + l) p (by omega) C⟩
  funext x
  exact oneBuffer_eval (p + l) p (by omega) C (List.ofFn x) (by simp)

end PEqualNP.Outside.L_meta_4675.Buffering


namespace PEqualNP.Outside.L_meta_4675.MatchingConsequence

lemma cover_card_of_matching {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : Fin p → Fin l) (hf : Function.Injective f) (hE : ∀ a, (a, f a) ∈ E)
    (S : Finset (Fin (p + l)))
    (hS : ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) :
    p ≤ S.card := by
  classical
  let pick : Fin p → Fin (p + l) :=
    fun a => if Fin.castAdd l a ∈ S then Fin.castAdd l a else Fin.natAdd p (f a)
  have hpick : Function.Injective pick := by
    intro a b he
    dsimp [pick] at he
    split_ifs at he with ha hb
    · apply Fin.ext
      have hval := congrArg Fin.val he
      simpa using hval
    · have hval := congrArg Fin.val he
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      have := a.isLt
      omega
    · have hval := congrArg Fin.val he
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      have := b.isLt
      omega
    · apply hf
      apply Fin.ext
      have hval := congrArg Fin.val he
      simpa using hval
  have hpS : ∀ a, pick a ∈ S := by
    intro a
    dsimp [pick]
    split_ifs with ha
    · exact ha
    · exact (hS a (f a) (hE a)).resolve_left ha
  calc
    p = (Finset.univ.image pick).card := by
      rw [Finset.card_image_of_injective _ hpick]
      simp
    _ ≤ S.card := Finset.card_le_card (by
      intro v hv
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
      exact hpS a)

lemma size_overhead_cancels {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : Fin p → Fin l) (hf : Function.Injective f) (hE : ∀ a, (a, f a) ∈ E)
    (s d : ℕ) (hd : d = s + p)
    (hbound : ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ d + 1) :
    E.card ≤ s + 1 := by
  obtain ⟨S, hS, hcard⟩ := hbound
  have hmatch := cover_card_of_matching E f hf hE S hS
  omega

end PEqualNP.Outside.L_meta_4675.MatchingConsequence

namespace PEqualNP.Outside.L_meta_4675.MatchingConsequence

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity

def Posted : Prop :=
∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
  PEqualNP.TopForm.IsAO2 (p + l) C →
  (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) →
  PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 →
  ∃ S : Finset (Fin (p + l)),
    (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
    E.card + S.card ≤ C.size + 1

lemma posted_implies_edge_count (hpost : Posted)
    (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hC : IsAO2 (p + l) C)
    (hfun : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (f : Fin p → Fin l) (hf : Function.Injective f) (hE : ∀ a, (a, f a) ∈ E) :
    E.card ≤ C.size + 1 := by
  obtain ⟨D, hD, hsize, hsame, hzero⟩ :=
    PEqualNP.Outside.L_meta_4675.Buffering.one_sided_buffering p l C hC
  apply size_overhead_cancels E f hf hE C.size D.size hsize
  apply hpost p l E D hC4 hD _ hzero
  intro x
  rw [hsame]
  exact hfun x

end PEqualNP.Outside.L_meta_4675.MatchingConsequence
