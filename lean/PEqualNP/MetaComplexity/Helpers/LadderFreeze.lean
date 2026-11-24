import PEqualNP.MetaComplexity.Helpers.FewNotPlan

/-!
# The ladder, steps 1 and 2: freeze the NOT gates; the pieces are convex

Pieces of the build plan of row L-meta-1048 (the ladder), unverified until a checker accepts.

A list `gates` of AND, OR, NOT gates, with an index map `ι : Fin t → Fin gates.length` that
covers every NOT gate, and a pattern `e : Fin t → Bool`. The piece `P_e` is the set of inputs
`x` on which the wire of gate `ι j` carries `e j` for every `j`.

Step 1 (`lf_freeze`): replace in place each gate at an index `ι j` by `AND []` if `e j`, else
by `OR []` (the first `j` with that index decides). Same length, AND/OR of fan-in at most two,
and on `P_e` all wires agree with those of `gates`.

Step 2 (`lf_convex`): if `a ≤ x ≤ b` pointwise and `a, b ∈ P_e`, then `x ∈ P_e`.

`lf_freeze_interval` puts both together, the form the interval step uses.
-/

namespace PEqualNP.MetaComplexity.Ladder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers
  PEqualNP.MetaComplexity.OneNot PEqualNP.MetaComplexity.FewNot

/-! ## Vocabulary -/

/-- The value of one gate on a wire list. -/
def lf_gv (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

/-- The frozen value at gate index `k`: `e j` for the first `j` with `ι j = k`, if any. -/
def lf_slot {L t : ℕ} (ι : Fin t → Fin L) (e : Fin t → Bool) (k : Fin L) : Option Bool :=
  ((List.finRange t).find? (fun j => decide (ι j = k))).map e

/-- The gate kept (`none`) or frozen to a constant. -/
def lf_gate (g : Gate) : Option Bool → Gate
  | none => g
  | some true => ⟨GateOp.and, []⟩
  | some false => ⟨GateOp.or, []⟩

/-- The frozen list. -/
def lf_freezeList (gates : List Gate) {t : ℕ} (ι : Fin t → Fin gates.length)
    (e : Fin t → Bool) : List Gate :=
  List.ofFn fun k : Fin gates.length => lf_gate (gates.get k) (lf_slot ι e k)

/-! ## Wire bookkeeping -/

theorem lf_wiresFrom_single (g : Gate) (v : List Bool) :
    wiresFrom [g] v = v ++ [lf_gv g v] := rfl

/-- Two lists of the same length have the same wires on every prefix, if at each position the
two gates agree on the common prefix wires. -/
theorem lf_agree (fs gs : List Gate) (w : List Bool) (hlen : fs.length = gs.length)
    (H : ∀ k (hk : k < fs.length), wiresFrom (fs.take k) w = wiresFrom (gs.take k) w →
      lf_gv (fs[k]) (wiresFrom (fs.take k) w)
        = lf_gv (gs[k]'(hlen ▸ hk)) (wiresFrom (fs.take k) w)) :
    ∀ k, k ≤ fs.length → wiresFrom (fs.take k) w = wiresFrom (gs.take k) w := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k < fs.length := by omega
    have IH := ih (by omega)
    rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hk',
      List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some]
    rw [wiresFrom_append, wiresFrom_append, lf_wiresFrom_single, lf_wiresFrom_single, ← IH,
      H k hk' IH]

/-- The wire of gate `k`: the gate's value on the wires of the gates before it. -/
theorem lf_wire_eq (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false = lf_gv gs[k] (wiresFrom (gs.take k) w) := by
  have hsplit : gs = gs.take k ++ (gs[k] :: gs.drop (k + 1)) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hl : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take]; omega
  conv_lhs => rw [hsplit]
  rw [wiresFrom_append, on1_wiresFrom_cons]
  rw [getD_wiresFrom _ _ _ (by simp [hl]), ← hl, getD_snoc_eq]
  rfl

theorem lf_wire_eq_ofFn {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ)
    (hk : k < gs.length) :
    (wiresFrom gs (List.ofFn x)).getD (n + k) false
      = lf_gv gs[k] (wiresFrom (gs.take k) (List.ofFn x)) := by
  have := lf_wire_eq gs (List.ofFn x) k hk
  rwa [List.length_ofFn] at this

/-! ## The frozen list -/

theorem lf_freezeList_length (gates : List Gate) {t : ℕ} (ι : Fin t → Fin gates.length)
    (e : Fin t → Bool) : (lf_freezeList gates ι e).length = gates.length := by
  simp [lf_freezeList]

theorem lf_freezeList_getElem (gates : List Gate) {t : ℕ} (ι : Fin t → Fin gates.length)
    (e : Fin t → Bool) (k : ℕ) (hk : k < (lf_freezeList gates ι e).length) :
    (lf_freezeList gates ι e)[k]
      = lf_gate (gates[k]'(by simpa [lf_freezeList] using hk))
          (lf_slot ι e ⟨k, by simpa [lf_freezeList] using hk⟩) := by
  simp [lf_freezeList]

theorem lf_slot_some {L t : ℕ} (ι : Fin t → Fin L) (e : Fin t → Bool) (k : Fin L) (b : Bool)
    (h : lf_slot ι e k = some b) : ∃ j, ι j = k ∧ e j = b := by
  unfold lf_slot at h
  cases hf : (List.finRange t).find? (fun j => decide (ι j = k)) with
  | none => rw [hf] at h; simp at h
  | some j =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have := List.find?_some hf
    exact ⟨j, by simpa using this, h⟩

theorem lf_slot_none {L t : ℕ} (ι : Fin t → Fin L) (e : Fin t → Bool) (k : Fin L)
    (h : lf_slot ι e k = none) : ∀ j, ι j ≠ k := by
  unfold lf_slot at h
  cases hf : (List.finRange t).find? (fun j => decide (ι j = k)) with
  | none =>
    intro j hj
    have := List.find?_eq_none.mp hf j (List.mem_finRange j)
    simp [hj] at this
  | some j => rw [hf] at h; simp at h

theorem lf_gv_const (g : Gate) (b : Bool) (w : List Bool) :
    lf_gv (lf_gate g (some b)) w = b := by
  cases b <;> rfl

theorem lf_freezeList_andOr2 (gates : List Gate) {t : ℕ} (ι : Fin t → Fin gates.length)
    (e : Fin t → Bool) (hops : OpsOK gates)
    (hcov : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → ∃ j, ι j = i) :
    AndOr2 (lf_freezeList gates ι e) := by
  intro g hg
  unfold lf_freezeList at hg
  rw [List.mem_ofFn] at hg
  obtain ⟨k, rfl⟩ := hg
  cases hs : lf_slot ι e k with
  | none =>
    simp only [lf_gate]
    obtain ⟨hop, hfan⟩ := hops (gates.get k) (List.get_mem _ _)
    refine ⟨?_, hfan⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · obtain ⟨j, hj⟩ := hcov k h
      exact absurd hj (lf_slot_none ι e k hs j)
  | some b => cases b <;> simp [lf_gate]

/-! ## The two conditions on an input -/

/-- On `P_e`, the frozen list and `gates` agree on every prefix. -/
theorem lf_prefix_of_P {n t : ℕ} (gates : List Gate) (ι : Fin t → Fin gates.length)
    (e : Fin t → Bool) (x : Fin n → Bool)
    (hP : ∀ j, (wiresFrom gates (List.ofFn x)).getD (n + (ι j : ℕ)) false = e j) :
    ∀ k, k ≤ gates.length → wiresFrom ((lf_freezeList gates ι e).take k) (List.ofFn x)
      = wiresFrom (gates.take k) (List.ofFn x) := by
  intro k hk
  apply lf_agree _ _ _ (lf_freezeList_length gates ι e) _ k
    (by rw [lf_freezeList_length]; exact hk)
  intro k hk IH
  rw [lf_freezeList_getElem]
  have hk2 : k < gates.length := by rwa [lf_freezeList_length] at hk
  cases hs : lf_slot ι e ⟨k, hk2⟩ with
  | none => rfl
  | some b =>
    obtain ⟨j, hj, hb⟩ := lf_slot_some ι e _ b hs
    rw [lf_gv_const, IH, ← lf_wire_eq_ofFn gates x k hk2]
    have hjk : (ι j : ℕ) = k := by rw [hj]
    rw [← hjk, hP j, hb]

/-- The frozen condition `Q_e`: the original gate at `ι j`, evaluated on the frozen wires before
it, gives `e j`. -/
def lf_Q {n t : ℕ} (gates : List Gate) (ι : Fin t → Fin gates.length) (e : Fin t → Bool)
    (x : Fin n → Bool) : Prop :=
  ∀ j, lf_gv (gates[(ι j : ℕ)]) (wiresFrom ((lf_freezeList gates ι e).take (ι j))
    (List.ofFn x)) = e j

theorem lf_prefix_of_Q {n t : ℕ} (gates : List Gate) (ι : Fin t → Fin gates.length)
    (e : Fin t → Bool) (x : Fin n → Bool) (hQ : lf_Q gates ι e x) :
    ∀ k, k ≤ gates.length → wiresFrom ((lf_freezeList gates ι e).take k) (List.ofFn x)
      = wiresFrom (gates.take k) (List.ofFn x) := by
  intro k hk
  apply lf_agree _ _ _ (lf_freezeList_length gates ι e) _ k
    (by rw [lf_freezeList_length]; exact hk)
  intro k hk _
  rw [lf_freezeList_getElem]
  have hk2 : k < gates.length := by rwa [lf_freezeList_length] at hk
  cases hs : lf_slot ι e ⟨k, hk2⟩ with
  | none => rfl
  | some b =>
    obtain ⟨j, hj, hb⟩ := lf_slot_some ι e _ b hs
    rw [lf_gv_const]
    have hjk : (ι j : ℕ) = k := by rw [hj]
    subst hjk
    rw [hQ j, hb]

theorem lf_Q_of_P {n t : ℕ} (gates : List Gate) (ι : Fin t → Fin gates.length)
    (e : Fin t → Bool) (x : Fin n → Bool)
    (hP : ∀ j, (wiresFrom gates (List.ofFn x)).getD (n + (ι j : ℕ)) false = e j) :
    lf_Q gates ι e x := by
  intro j
  rw [lf_prefix_of_P gates ι e x hP _ (le_of_lt (ι j).isLt),
    ← lf_wire_eq_ofFn gates x _ (ι j).isLt, hP j]

theorem lf_P_of_Q {n t : ℕ} (gates : List Gate) (ι : Fin t → Fin gates.length)
    (e : Fin t → Bool) (x : Fin n → Bool) (hQ : lf_Q gates ι e x) :
    ∀ j, (wiresFrom gates (List.ofFn x)).getD (n + (ι j : ℕ)) false = e j := by
  intro j
  rw [lf_wire_eq_ofFn gates x _ (ι j).isLt,
    ← lf_prefix_of_Q gates ι e x hQ _ (le_of_lt (ι j).isLt), hQ j]

/-! ## Monotonicity -/

theorem lf_above_ofFn {n : ℕ} (a x : Fin n → Bool) (hax : ∀ i, a i = true → x i = true) :
    on1_Above (List.ofFn a) (List.ofFn x) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · rw [on1_getD_ofFn _ _ hin] at hi ⊢; exact hax _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact absurd hi (by simp)

theorem lf_gv_mono (g : Gate) (v v' : List Bool) (h : on1_Above v v')
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    lf_gv g v = true → lf_gv g v' = true := by
  intro hv
  have hab := on1_above_wiresFrom [g] (by simpa using hop) v v' h
  rw [lf_wiresFrom_single, lf_wiresFrom_single] at hab
  have := hab.2 v.length (by rw [getD_snoc_eq]; exact hv)
  rwa [h.1, getD_snoc_eq] at this

theorem lf_gv_anti (g : Gate) (v v' : List Bool) (h : on1_Above v v')
    (hop : g.op = GateOp.not) :
    lf_gv g v' = true → lf_gv g v = true := by
  unfold lf_gv
  rw [hop]
  cases hin : g.inputs with
  | nil => simp [GateOp.eval]
  | cons i _ =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true']
    intro hv'
    cases hvi : v.getD i false with
    | false => rfl
    | true => have := h.2 i hvi; rw [this] at hv'; exact absurd hv' (by simp)

theorem lf_frozen_above {n t : ℕ} (gates : List Gate) (ι : Fin t → Fin gates.length)
    (e : Fin t → Bool) (hops : OpsOK gates)
    (hcov : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → ∃ j, ι j = i)
    (a x : Fin n → Bool) (hax : ∀ i, a i = true → x i = true) (k : ℕ) :
    on1_Above (wiresFrom ((lf_freezeList gates ι e).take k) (List.ofFn a))
      (wiresFrom ((lf_freezeList gates ι e).take k) (List.ofFn x)) := by
  apply on1_above_wiresFrom _ _ _ _ (lf_above_ofFn a x hax)
  intro g hg
  exact (lf_freezeList_andOr2 gates ι e hops hcov g (List.mem_of_mem_take hg)).1

/-! ## Step 1 and step 2 -/

/-- STEP 1, FREEZE THE NOTS. With every NOT gate covered by `ι`, there is a list of the same
length, of AND/OR gates of fan-in at most two, whose wires equal those of `gates` on every
input of the piece `P_e`. (The list is `lf_freezeList gates ι e`.) -/
theorem lf_freeze : ∀ (n t : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate)
    (ι : Fin t → Fin gates.length) (e : Fin t → Bool),
    PEqualNP.MetaComplexity.FewNot.OpsOK gates →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
      ∃ j : Fin t, ι j = i) →
    ∃ F : List PEqualNP.CircuitLowerBounds.Gate, F.length = gates.length ∧
      PEqualNP.MetaComplexity.FewNot.AndOr2 F ∧
      ∀ x : Fin n → Bool,
        (∀ j : Fin t, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩
          (List.ofFn x)).getD (n + (ι j : ℕ)) false = e j) →
        ∀ o o' : ℕ, PEqualNP.CircuitLowerBounds.Circuit.wires ⟨F, o⟩ (List.ofFn x)
          = PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, o'⟩ (List.ofFn x) := by
  intro n t gates ι e hops hcov
  refine ⟨lf_freezeList gates ι e, lf_freezeList_length gates ι e,
    lf_freezeList_andOr2 gates ι e hops hcov, ?_⟩
  intro x hP o o'
  have := lf_prefix_of_P gates ι e x hP gates.length le_rfl
  rw [List.take_length, ← lf_freezeList_length gates ι e, List.take_length] at this
  exact this

/-- STEP 2, PIECES ARE CONVEX. With every NOT gate covered by `ι`: if `a ≤ x ≤ b` pointwise and
`a`, `b` lie in the piece `P_e`, then so does `x`. -/
theorem lf_convex : ∀ (n t : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate)
    (ι : Fin t → Fin gates.length) (e : Fin t → Bool),
    PEqualNP.MetaComplexity.FewNot.OpsOK gates →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
      ∃ j : Fin t, ι j = i) →
    ∀ a x b : Fin n → Bool, (∀ i, a i = true → x i = true) → (∀ i, x i = true → b i = true) →
      (∀ j : Fin t, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩
        (List.ofFn a)).getD (n + (ι j : ℕ)) false = e j) →
      (∀ j : Fin t, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩
        (List.ofFn b)).getD (n + (ι j : ℕ)) false = e j) →
      ∀ j : Fin t, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩
        (List.ofFn x)).getD (n + (ι j : ℕ)) false = e j := by
  intro n t gates ι e hops hcov a x b hax hxb hPa hPb
  apply lf_P_of_Q gates ι e x
  have hQa := lf_Q_of_P gates ι e a hPa
  have hQb := lf_Q_of_P gates ι e b hPb
  intro j
  have hA := lf_frozen_above gates ι e hops hcov a x hax (ι j)
  have hB := lf_frozen_above gates ι e hops hcov x b hxb (ι j)
  have ha := hQa j
  have hb := hQb j
  obtain ⟨hop, _⟩ := hops (gates[(ι j : ℕ)]) (List.getElem_mem _)
  rcases hop with hop | hop | hop
  · have m1 := lf_gv_mono _ _ _ hA (Or.inl hop)
    have m2 := lf_gv_mono _ _ _ hB (Or.inl hop)
    revert m1 m2 ha hb
    cases lf_gv (gates[(ι j : ℕ)]) (wiresFrom ((lf_freezeList gates ι e).take (ι j)) (List.ofFn x))
      <;> cases e j <;> simp_all
  · have m1 := lf_gv_mono _ _ _ hA (Or.inr hop)
    have m2 := lf_gv_mono _ _ _ hB (Or.inr hop)
    revert m1 m2 ha hb
    cases lf_gv (gates[(ι j : ℕ)]) (wiresFrom ((lf_freezeList gates ι e).take (ι j)) (List.ofFn x))
      <;> cases e j <;> simp_all
  · have m1 := lf_gv_anti _ _ _ hA hop
    have m2 := lf_gv_anti _ _ _ hB hop
    revert m1 m2 ha hb
    cases lf_gv (gates[(ι j : ℕ)]) (wiresFrom ((lf_freezeList gates ι e).take (ι j)) (List.ofFn x))
      <;> cases e j <;> simp_all

/-- Steps 1 and 2 together: one frozen list of the same length, AND/OR of fan-in at most two,
right (equal output to `gates`, at every output index) on every `x` between two inputs of the
piece `P_e`. -/
theorem lf_freeze_interval : ∀ (n t : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate)
    (ι : Fin t → Fin gates.length) (e : Fin t → Bool),
    PEqualNP.MetaComplexity.FewNot.OpsOK gates →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
      ∃ j : Fin t, ι j = i) →
    ∃ F : List PEqualNP.CircuitLowerBounds.Gate, F.length = gates.length ∧
      PEqualNP.MetaComplexity.FewNot.AndOr2 F ∧
      ∀ a b : Fin n → Bool,
        (∀ j : Fin t, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩
          (List.ofFn a)).getD (n + (ι j : ℕ)) false = e j) →
        (∀ j : Fin t, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩
          (List.ofFn b)).getD (n + (ι j : ℕ)) false = e j) →
        ∀ x : Fin n → Bool, (∀ i, a i = true → x i = true) → (∀ i, x i = true → b i = true) →
          ∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨F, o⟩ (List.ofFn x)
            = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) := by
  intro n t gates ι e hops hcov
  obtain ⟨F, hl, hF, hw⟩ := lf_freeze n t gates ι e hops hcov
  refine ⟨F, hl, hF, ?_⟩
  intro a b hPa hPb x hax hxb o
  unfold Circuit.eval
  rw [hw x (lf_convex n t gates ι e hops hcov a x b hax hxb hPa hPb) o o]

end PEqualNP.MetaComplexity.Ladder
