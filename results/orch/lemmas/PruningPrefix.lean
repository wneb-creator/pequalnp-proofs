namespace PEqualNP.Outside.L_meta_4675.PruningPrefix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Outside.L_meta_4675.Pruning

lemma range_some_getD (N w : ℕ) (hw : w < N) :
    ((List.range N).map some).getD w none = some w := by
  simp [List.getD_eq_getElem?_getD, hw]

lemma pairGate_form (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : ℕ) (hab : g.inputs = [a, b]) : pairGate (isAnd g.op) a b = g := by
  rcases hop with hop | hop <;> cases g <;> simp_all [pairGate, isAnd]

lemma compileStep_identity (n q : ℕ) (gs : List Gate) (g : Gate) (hq : gs.length < q)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2)
    (hback : ∀ w ∈ g.inputs, w < n + gs.length) :
    compileStep n q (gs, (List.range (n + gs.length)).map some) g =
      (gs ++ [g], (List.range (n + (gs ++ [g]).length)).map some) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have ha := hback a (by simp [hab])
  have hb := hback b (by simp [hab])
  have hkill : n + gs.length ≠ n + q := by omega
  simp only [compileStep, List.length_map, List.length_range, hkill, ↓reduceIte]
  simp only [hab, List.getD_cons_zero, List.getD_cons_succ]
  rw [range_some_getD _ _ ha, range_some_getD _ _ hb]
  simp only [emitPair, pairGate_form g hop a b hab, List.length_append, List.length_singleton]
  rw [show n + (gs.length + 1) = (n + gs.length) + 1 by omega, List.range_succ, List.map_append]
  rfl

lemma compiled_before (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (k : ℕ) (hkq : k ≤ q) (hkC : k ≤ C.gates.length) :
    compiled n q (C.gates.take k) = (C.gates.take k, (List.range (n + k)).map some) := by
  induction k with
  | zero => simp [compiled, initial]
  | succ k ih =>
    have hk : k < C.gates.length := by omega
    have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk
    have htake : (C.gates.take k).length = k := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    rw [compiled_take_succ n q C.gates k hk, ih (by omega) (by omega)]
    have hg : gateAt C k = C.gates[k] := by
      simp [gateAt, List.getD_eq_getElem?_getD, hk]
    have hback : ∀ w ∈ C.gates[k].inputs, w < n + (C.gates.take k).length := by
      intro w hw
      rw [htake]
      exact hAO.2.1 k hk w (by simpa [hg] using hw)
    have he := compileStep_identity n q (C.gates.take k) C.gates[k]
      (by omega) (hAO.1 _ hmem) (hAO.2.2 _ hmem) hback
    rw [htake, ← List.take_succ_eq_append_getElem hk] at he
    simpa [List.length_take, Nat.min_eq_left hkC] using he

lemma alias_before (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hq : q ≤ C.gates.length) (w : ℕ) (hw : w < n + q) :
    (compiled n q C.gates).2.getD w none = some w := by
  rw [compiled_split n q C.gates q]
  have hlen : w < (compiled n q (C.gates.take q)).2.length := by
    rw [compiled_map_length, List.length_take, Nat.min_eq_left hq]
    exact hw
  rw [fold_map_prior n q (C.gates.drop q) _ w hlen, compiled_before n q C hAO q le_rfl hq]
  exact range_some_getD (n + q) w hw

lemma force_fold_before (n q : ℕ) (gs : List Gate) (xs : List Bool) (hx : xs.length = n)
    (hlen : gs.length ≤ q) : gs.foldl (forceStep n q) xs = vals gs xs := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    have hlen' : gs.length ≤ q := by simp only [List.length_append, List.length_singleton] at hlen; omega
    have hlt : gs.length < q := by simp only [List.length_append, List.length_singleton] at hlen; omega
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih hlen', vals_snoc]
    unfold forceStep step
    have hne : n + gs.length ≠ n + q := by omega
    simp only [vals_length, hx, hne, ↓reduceIte]

lemma force_fold_prefix (n q : ℕ) (gs : List Gate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    (gs.foldl (forceStep n q) xs).getD w false = xs.getD w false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (forceStep n q xs g) (by simp [forceStep]; omega)]
    exact getD_append_lt xs _ w false hw

lemma vals_prefix (gs : List Gate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    (vals gs xs).getD w false = xs.getD w false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (vals gs (step xs g)).getD w false = xs.getD w false
    rw [ih (step xs g) (by simp [step]; omega)]
    exact getD_append_lt xs _ w false hw

lemma forced_wire_before (n q : ℕ) (C : Circuit) (hq : q ≤ C.gates.length)
    (xs : List Bool) (hx : xs.length = n) (w : ℕ) (hw : w < n + q) :
    (forcedValues n q C xs).getD w false = (C.wires xs).getD w false := by
  have hlen : (C.gates.take q).length = q := by
    rw [List.length_take, Nat.min_eq_left hq]
  have hval : w < (vals (C.gates.take q) xs).length := by
    rw [vals_length, hx, hlen]
    exact hw
  have hplain : (C.wires xs).getD w false = (vals (C.gates.take q) xs).getD w false := by
    change (vals C.gates xs).getD w false = _
    calc
      _ = (vals (C.gates.drop q) (vals (C.gates.take q) xs)).getD w false := by
        rw [← vals_append, List.take_append_drop]
      _ = _ := vals_prefix _ _ w hval
  rw [hplain]
  calc
    _ = ((C.gates.drop q).foldl (forceStep n q)
        ((C.gates.take q).foldl (forceStep n q) xs)).getD w false := by
      unfold forcedValues
      rw [← List.foldl_append, List.take_append_drop]
    _ = _ := by
      rw [force_fold_before n q (C.gates.take q) xs hx (by omega)]
      exact force_fold_prefix n q (C.gates.drop q) _ w hval

lemma pruned_wire_before (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hq : q ≤ C.gates.length) (xs : List Bool) (hx : xs.length = n)
    (w : ℕ) (hw : w < n + q) :
    ((pruned n q C).wires xs).getD w false = (C.wires xs).getD w false := by
  have h := (compiled_valid_related n q C hAO xs hx).2.2 w
  rw [alias_before n q C hAO hq w hw] at h
  exact h.trans (forced_wire_before n q C hq xs hx w hw)

end PEqualNP.Outside.L_meta_4675.PruningPrefix
