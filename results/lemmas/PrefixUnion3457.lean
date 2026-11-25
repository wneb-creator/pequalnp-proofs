import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3457_aux

open PEqualNP.CircuitLowerBounds

lemma any_or_distribute (xs : List ℕ) (a b : ℕ → Bool) :
    xs.any (fun i => a i || b i) = (xs.any a || xs.any b) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons, ih]
    ac_rfl

lemma all_or_false (xs : List ℕ) (a b : ℕ → Bool)
    (h : xs.all (fun i => a i || b i) = false) :
    xs.all a = false ∧ xs.all b = false := by
  constructor
  · apply Bool.eq_false_iff.mpr
    intro ha
    have hu : xs.all (fun i => a i || b i) = true := by
      apply List.all_eq_true.mpr
      intro i hi
      simp [List.all_eq_true.mp ha i hi]
    rw [h] at hu
    cases hu
  · apply Bool.eq_false_iff.mpr
    intro hb
    have hu : xs.all (fun i => a i || b i) = true := by
      apply List.all_eq_true.mpr
      intro i hi
      simp [List.all_eq_true.mp hb i hi]
    rw [h] at hu
    cases hu

lemma gate_union (g : Gate) (a b c : List Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hval : ∀ i, c.getD i false = (a.getD i false || b.getD i false))
    (hoff : g.op = GateOp.and → g.op.eval (g.inputs.map fun i => c.getD i false) = false) :
    g.op.eval (g.inputs.map fun i => c.getD i false) =
      (g.op.eval (g.inputs.map fun i => a.getD i false) ||
       g.op.eval (g.inputs.map fun i => b.getD i false)) := by
  rcases hop with hop | hop
  · have h := hoff hop
    simp only [hop, GateOp.eval, List.all_map, Function.comp_def, id_eq] at h ⊢
    simp_rw [hval] at h ⊢
    obtain ⟨ha, hb⟩ := all_or_false g.inputs (fun i => a.getD i false) (fun i => b.getD i false) h
    rw [h, ha, hb]
    rfl
  · simp only [hop, GateOp.eval, List.any_map, Function.comp_def, id_eq]
    simp_rw [hval]
    exact any_or_distribute _ _ _

lemma append_union (a b c : List Bool) (u v w : Bool)
    (ha : a.length = c.length) (hb : b.length = c.length)
    (hval : ∀ i, c.getD i false = (a.getD i false || b.getD i false))
    (hw : w = (u || v)) :
    ∀ i, (c ++ [w]).getD i false =
      ((a ++ [u]).getD i false || (b ++ [v]).getD i false) := by
  intro i
  by_cases hi : i < c.length
  · rw [List.getD_append c [w] false i hi,
        List.getD_append a [u] false i (by omega),
        List.getD_append b [v] false i (by omega)]
    exact hval i
  · rw [List.getD_append_right c [w] false i (by omega),
        List.getD_append_right a [u] false i (by omega),
        List.getD_append_right b [v] false i (by omega), ha, hb]
    cases h : i - c.length <;> simp [hw]

def runStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_union (gs : List Gate) (a b c : List Bool)
    (ha : a.length = c.length) (hb : b.length = c.length)
    (hval : ∀ i, c.getD i false = (a.getD i false || b.getD i false))
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hoff : ∀ before g after, gs = before ++ g :: after →
      g.op = GateOp.and →
      g.op.eval (g.inputs.map fun i => (before.foldl runStep c).getD i false) = false) :
    ∀ i, (gs.foldl runStep c).getD i false =
      ((gs.foldl runStep a).getD i false || (gs.foldl runStep b).getD i false) := by
  induction gs generalizing a b c with
  | nil => exact hval
  | cons g gs ih =>
    have hgv := gate_union g a b c (hmono g (by simp)) hval (hoff [] g gs rfl)
    have hstep : ∀ i, (runStep c g).getD i false =
        ((runStep a g).getD i false || (runStep b g).getD i false) :=
      append_union a b c _ _ _ ha hb hval hgv
    simp only [List.foldl_cons]
    apply ih (runStep a g) (runStep b g) (runStep c g)
      (by simp [runStep, ha]) (by simp [runStep, hb]) hstep
      (fun q hq => hmono q (by simp [hq]))
    intro before q after heq hq
    have h := hoff (g :: before) q after (by simp only [List.cons_append]; rw [heq]) hq
    simpa only [List.foldl_cons] using h

lemma crossed_singletons (u v p q : Bool)
    (hpair : ((u || p) && (v || q)) = true)
    (hfirst : (u && v) = false) (hsecond : (p && q) = false) :
    (u = true ∧ v = false ∧ p = false ∧ q = true) ∨
    (u = false ∧ v = true ∧ p = true ∧ q = false) := by
  cases u <;> cases v <;> cases p <;> cases q <;> simp_all

lemma first_dirty_operands (gs : List Gate) (a b c : List Bool) (u v : ℕ)
    (ha : a.length = c.length) (hb : b.length = c.length)
    (hval : ∀ i, c.getD i false = (a.getD i false || b.getD i false))
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hoff : ∀ before g after, gs = before ++ g :: after →
      g.op = GateOp.and →
      g.op.eval (g.inputs.map fun i => (before.foldl runStep c).getD i false) = false)
    (hpair : ((gs.foldl runStep c).getD u false &&
      (gs.foldl runStep c).getD v false) = true)
    (hfirst : ((gs.foldl runStep a).getD u false &&
      (gs.foldl runStep a).getD v false) = false)
    (hsecond : ((gs.foldl runStep b).getD u false &&
      (gs.foldl runStep b).getD v false) = false) :
    ((gs.foldl runStep a).getD u false = true ∧
      (gs.foldl runStep a).getD v false = false ∧
      (gs.foldl runStep b).getD u false = false ∧
      (gs.foldl runStep b).getD v false = true) ∨
    ((gs.foldl runStep a).getD u false = false ∧
      (gs.foldl runStep a).getD v false = true ∧
      (gs.foldl runStep b).getD u false = true ∧
      (gs.foldl runStep b).getD v false = false) := by
  have h := fold_union gs a b c ha hb hval hmono hoff
  rw [h u, h v] at hpair
  exact crossed_singletons _ _ _ _ hpair hfirst hsecond

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl runStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, runStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma fold_preserves (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl runStep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (runStep x g) (by simp [runStep]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma circuit_prefix_read (C : Circuit) (x : List Bool) (j i : ℕ)
    (hi : i < x.length + (C.gates.take j).length) :
    (C.wires x).getD i false = ((C.gates.take j).foldl runStep x).getD i false := by
  calc
    (C.wires x).getD i false =
        (((C.gates.take j ++ C.gates.drop j).foldl runStep x)).getD i false := by
      rw [List.take_append_drop]
      rfl
    _ = ((C.gates.take j).foldl runStep x).getD i false := by
      rw [List.foldl_append]
      exact fold_preserves _ _ _ (by simpa only [fold_length] using hi)

lemma circuit_split_gate (C : Circuit) (before after : List Gate) (g : Gate)
    (h : C.gates = before ++ g :: after) : gateAt C before.length = g := by
  simp only [gateAt, h]
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

lemma circuit_split_value (C : Circuit) (before after : List Gate) (g : Gate)
    (x : List Bool) (h : C.gates = before ++ g :: after) :
    (C.wires x).getD (x.length + before.length) false =
      g.op.eval (g.inputs.map fun i => (before.foldl runStep x).getD i false) := by
  change (C.gates.foldl runStep x).getD _ false = _
  rw [h, List.foldl_append, List.foldl_cons, ← fold_length before x]
  rw [fold_preserves after (runStep (before.foldl runStep x) g)
    (before.foldl runStep x).length (by simp [runStep])]
  unfold runStep
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

lemma gates_take_split (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
  have hg : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [hg, List.cons_getElem_drop_succ]
  exact (List.take_append_drop j C.gates).symm

lemma circuit_gate_value (C : Circuit) (x : List Bool) (n j : ℕ)
    (hx : x.length = n) (hj : j < C.gates.length) (hback : ReadsBack n C) :
    (C.wires x).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have ht : (C.gates.take j).length = j := by simp [List.length_take, Nat.min_eq_left hj.le]
  have h := circuit_split_value C (C.gates.take j) (C.gates.drop (j + 1))
    (gateAt C j) x (gates_take_split C j hj)
  rw [hx, ht] at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (circuit_prefix_read C x j i (by rw [hx, ht]; exact hback j hj i hi)).symm

lemma circuit_prefix_union (C : Circuit) (a b c : List Bool) (j : ℕ)
    (hj : j ≤ C.gates.length) (ha : a.length = c.length) (hb : b.length = c.length)
    (hval : ∀ i, c.getD i false = (a.getD i false || b.getD i false))
    (hmono : Monotone2 C)
    (hoff : ∀ k < j, (gateAt C k).op = GateOp.and →
      (C.wires c).getD (c.length + k) false = false) :
    ∀ i < c.length + j, (C.wires c).getD i false =
      ((C.wires a).getD i false || (C.wires b).getD i false) := by
  have ht : (C.gates.take j).length = j := by simp [List.length_take, Nat.min_eq_left hj]
  have hf := fold_union (C.gates.take j) a b c ha hb hval
    (fun g hg => by simpa using (hmono g (List.mem_of_mem_take hg)).1)
  have hp : ∀ before g after, C.gates.take j = before ++ g :: after →
      g.op = GateOp.and →
      g.op.eval (g.inputs.map fun i => (before.foldl runStep c).getD i false) = false := by
    intro before g after hs hand
    have hbefore : before.length < j := by
      have hlen := congrArg List.length hs
      simp only [ht, List.length_append, List.length_cons] at hlen
      omega
    have hfull : C.gates = before ++ g :: (after ++ C.gates.drop j) := by
      calc
        C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
        _ = before ++ g :: (after ++ C.gates.drop j) := by rw [hs]; simp [List.append_assoc]
    have hgate := circuit_split_gate C before (after ++ C.gates.drop j) g hfull
    have hz := hoff before.length hbefore (by rw [hgate]; exact hand)
    rw [circuit_split_value C before (after ++ C.gates.drop j) g c hfull] at hz
    exact hz
  have hunion := hf hp
  intro i hi
  rw [circuit_prefix_read C c j i (by rw [ht]; exact hi),
      circuit_prefix_read C a j i (by rw [ha, ht]; exact hi),
      circuit_prefix_read C b j i (by rw [hb, ht]; exact hi)]
  exact hunion i

lemma first_dirty_circuit (C : Circuit) (a b c : List Bool) (n j u v : ℕ)
    (ha : a.length = n) (hb : b.length = n) (hc : c.length = n)
    (hval : ∀ i, c.getD i false = (a.getD i false || b.getD i false))
    (hmono : Monotone2 C) (hback : ReadsBack n C) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (hin : (gateAt C j).inputs = [u,v])
    (hoff : ∀ k < j, (gateAt C k).op = GateOp.and →
      (C.wires c).getD (n + k) false = false)
    (hpair : (C.wires c).getD (n + j) false = true)
    (hfirst : (C.wires a).getD (n + j) false = false)
    (hsecond : (C.wires b).getD (n + j) false = false) :
    ((C.wires a).getD u false = true ∧ (C.wires a).getD v false = false ∧
      (C.wires b).getD u false = false ∧ (C.wires b).getD v false = true) ∨
    ((C.wires a).getD u false = false ∧ (C.wires a).getD v false = true ∧
      (C.wires b).getD u false = true ∧ (C.wires b).getD v false = false) := by
  have hunion := circuit_prefix_union C a b c j hj.le (ha.trans hc.symm) (hb.trans hc.symm)
    hval hmono (by simpa only [hc] using hoff)
  have hu : u < c.length + j := by rw [hc]; exact hback j hj u (by simp [hin])
  have hv : v < c.length + j := by rw [hc]; exact hback j hj v (by simp [hin])
  rw [circuit_gate_value C c n j hc hj hback] at hpair
  rw [circuit_gate_value C a n j ha hj hback] at hfirst
  rw [circuit_gate_value C b n j hb hj hback] at hsecond
  simp only [hand, hin, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true] at hpair hfirst hsecond
  rw [hunion u hu, hunion v hv] at hpair
  exact crossed_singletons _ _ _ _ hpair hfirst hsecond

lemma and_union_needs_two (xs : List ℕ) (a b c : ℕ → Bool)
    (hlen : xs.length ≤ 2) (hval : ∀ i ∈ xs, c i = (a i || b i))
    (hc : xs.all c = true) (ha : xs.all a = false) (hb : xs.all b = false) :
    ∃ u v, xs = [u,v] := by
  cases xs with
  | nil => simp at ha
  | cons u rest =>
    cases rest with
    | nil =>
      have hu := hval u (by simp)
      simp only [List.all_cons, List.all_nil, Bool.and_true] at hc ha hb
      rw [ha, hb] at hu
      rw [hu] at hc
      cases hc
    | cons v tail =>
      have htail : tail = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at hlen
        omega
      exact ⟨u,v,by rw [htail]⟩

lemma exists_first_dirty (C : Circuit) (x : List Bool)
    (hdirty : ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      (C.wires x).getD (x.length + j) false = true) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      (C.wires x).getD (x.length + j) false = true ∧
      ∀ k < j, (gateAt C k).op = GateOp.and →
        (C.wires x).getD (x.length + k) false = false := by
  classical
  let P (j : ℕ) := j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
    (C.wires x).getD (x.length + j) false = true
  have hex : ∃ j, P j := hdirty
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  refine ⟨j,hj.1,hj.2.1,hj.2.2,?_⟩
  intro k hk hand
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact Nat.find_min hex hk ⟨by omega,hand,htrue⟩

lemma first_dirty_circuit_exists (C : Circuit) (a b c : List Bool) (n : ℕ)
    (ha : a.length = n) (hb : b.length = n) (hc : c.length = n)
    (hval : ∀ i, c.getD i false = (a.getD i false || b.getD i false))
    (hmono : Monotone2 C) (hback : ReadsBack n C)
    (hzero : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (C.wires a).getD (n + j) false = false ∧
      (C.wires b).getD (n + j) false = false)
    (hdirty : ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      (C.wires c).getD (n + j) false = true) :
    ∃ j < C.gates.length, ∃ u v, (gateAt C j).op = GateOp.and ∧
      (gateAt C j).inputs = [u,v] ∧
      ((C.wires a).getD u false = true ∧ (C.wires a).getD v false = false ∧
        (C.wires b).getD u false = false ∧ (C.wires b).getD v false = true ∨
      (C.wires a).getD u false = false ∧ (C.wires a).getD v false = true ∧
        (C.wires b).getD u false = true ∧ (C.wires b).getD v false = false) := by
  obtain ⟨j,hj,hand,hpair,hoff⟩ := exists_first_dirty C c (by simpa only [hc] using hdirty)
  have hpair' : (C.wires c).getD (n + j) false = true := by simpa only [hc] using hpair
  have hoff' : ∀ k < j, (gateAt C k).op = GateOp.and →
      (C.wires c).getD (n + k) false = false := by simpa only [hc] using hoff
  have hz := hzero j hj hand
  have hevalc := (circuit_gate_value C c n j hc hj hback).symm.trans hpair'
  have hevala := (circuit_gate_value C a n j ha hj hback).symm.trans hz.1
  have hevalb := (circuit_gate_value C b n j hb hj hback).symm.trans hz.2
  simp only [hand, GateOp.eval, List.all_map, Function.comp_def, id_eq] at hevalc hevala hevalb
  have hgmem : gateAt C j ∈ C.gates := by
    rw [gates_take_split C j hj]
    simp
  have hlength := (hmono (gateAt C j) hgmem).2
  have hunion := circuit_prefix_union C a b c j hj.le (ha.trans hc.symm) (hb.trans hc.symm)
    hval hmono hoff
  obtain ⟨u,v,hin⟩ := and_union_needs_two (gateAt C j).inputs
    (fun i => (C.wires a).getD i false) (fun i => (C.wires b).getD i false)
    (fun i => (C.wires c).getD i false) hlength
    (fun i hi => hunion i (by rw [hc]; exact hback j hj i hi)) hevalc hevala hevalb
  refine ⟨j,hj,u,v,hand,hin,?_⟩
  exact first_dirty_circuit C a b c n j u v ha hb hc hval hmono hback hj hand hin
    hoff' hpair' hz.1 hz.2

lemma ofFn_union (n : ℕ) (a b : Fin n → Bool) :
    ∀ i, (List.ofFn (fun k => a k || b k)).getD i false =
      ((List.ofFn a).getD i false || (List.ofFn b).getD i false) := by
  intro i
  by_cases hi : i < n
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]

end PEqualNP.Outside.L_meta_3457_aux
