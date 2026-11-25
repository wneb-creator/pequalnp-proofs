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
  | cons g gs ih => simp [List.foldl_cons, ih, runStep, Nat.add_comm, Nat.add_left_comm]

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
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, hi]

lemma or_gate_cover {ι : Type*} (g : Gate) (d : List Bool) (a : ι → List Bool)
    (hor : g.op = GateOp.or)
    (hval : ∀ i, d.getD i false = true → ∃ t, (a t).getD i false = true) :
    g.op.eval (g.inputs.map fun i => d.getD i false) = true →
      ∃ t, g.op.eval (g.inputs.map fun i => (a t).getD i false) = true := by
  simp only [hor, GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
  rintro ⟨i,hi,hvalue⟩
  obtain ⟨t,ht⟩ := hval i hvalue
  exact ⟨t,i,hi,ht⟩

lemma append_cover {ι : Type*} (d : List Bool) (a : ι → List Bool)
    (u : Bool) (v : ι → Bool) (hlen : ∀ t, (a t).length = d.length)
    (hval : ∀ i, d.getD i false = true → ∃ t, (a t).getD i false = true)
    (hnew : u = true → ∃ t, v t = true) :
    ∀ i, (d ++ [u]).getD i false = true →
      ∃ t, (a t ++ [v t]).getD i false = true := by
  intro i hi
  by_cases hlt : i < d.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    obtain ⟨t,ht⟩ := hval i hi
    refine ⟨t,?_⟩
    rw [List.getD_append _ _ _ _ (by rw [hlen t]; exact hlt)]
    exact ht
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    by_cases heq : i = d.length
    · subst i
      simp at hi
      obtain ⟨t,ht⟩ := hnew hi
      refine ⟨t,?_⟩
      rw [List.getD_append_right _ _ _ _ (by simpa only [hlen t] using (Nat.le_refl d.length)), hlen t]
      simpa using ht
    · have hgt : d.length < i := by omega
      rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      cases hi

lemma or_fold_cover {ι : Type*} (gs : List Gate) (d : List Bool) (a : ι → List Bool)
    (hor : ∀ g ∈ gs, g.op = GateOp.or) (hlen : ∀ t, (a t).length = d.length)
    (hval : ∀ i, d.getD i false = true → ∃ t, (a t).getD i false = true) :
    ∀ i, (gs.foldl runStep d).getD i false = true →
      ∃ t, (gs.foldl runStep (a t)).getD i false = true := by
  induction gs generalizing d a with
  | nil => exact hval
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (runStep d g) (fun t => runStep (a t) g)
      (fun q hq => hor q (by simp [hq])) (fun t => by simp [runStep, hlen t])
    exact append_cover d a _ _ hlen hval (or_gate_cover g d a (hor g (by simp)) hval)

lemma or_fold_union (gs : List Gate) (a b c : List Bool)
    (hor : ∀ g ∈ gs, g.op = GateOp.or)
    (ha : a.length = c.length) (hb : b.length = c.length)
    (hval : ∀ i, c.getD i false = (a.getD i false || b.getD i false)) :
    ∀ i, (gs.foldl runStep c).getD i false =
      ((gs.foldl runStep a).getD i false || (gs.foldl runStep b).getD i false) := by
  apply fold_union gs a b c ha hb hval (fun g hg => Or.inr (hor g hg))
  intro before g after hs hand
  have hg : g ∈ gs := by rw [hs]; simp
  rw [hor g hg] at hand
  cases hand

lemma sole_gate_below_output (C : Circuit) (before after : List Gate) (g : Gate)
    (a b c : List Bool) (hsplit : C.gates = before ++ g :: after)
    (hbefore : ∀ q ∈ before, q.op = GateOp.or)
    (hafter : ∀ q ∈ after, q.op = GateOp.or)
    (ha : a.length = c.length) (hb : b.length = c.length)
    (hunion : ∀ i, c.getD i false = (a.getD i false || b.getD i false))
    (hpositive : C.eval c = true) (hfirst : C.eval a = false) (hsecond : C.eval b = false) :
    ∀ d : List Bool, d.length = c.length →
      (C.wires d).getD (d.length + before.length) false = true → C.eval d = true := by
  intro d hd hdirty
  let inputs : Fin 3 → List Bool := ![a,b,d]
  let pre := fun t => before.foldl runStep (inputs t)
  let next := fun t => g.op.eval (g.inputs.map fun i => (pre t).getD i false)
  have hpreunion := or_fold_union before a b c hbefore ha hb hunion
  have hlen : ∀ t, (pre t).length = (before.foldl runStep c).length := by
    intro t
    fin_cases t <;> simp [pre, inputs, fold_length, ha, hb, hd]
  have hcover : ∀ i, (before.foldl runStep c).getD i false = true →
      ∃ t, (pre t).getD i false = true := by
    intro i hi
    rw [hpreunion i] at hi
    simp only [Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact ⟨0,hi⟩
    · exact ⟨1,hi⟩
  have hnext : g.op.eval (g.inputs.map fun i => (before.foldl runStep c).getD i false) = true →
      ∃ t, next t = true := by
    intro _
    refine ⟨2,?_⟩
    exact (circuit_split_value C before after g d hsplit).symm.trans hdirty
  have hpost : ∀ i, (runStep (before.foldl runStep c) g).getD i false = true →
      ∃ t, (runStep (pre t) g).getD i false = true :=
    append_cover _ pre _ next hlen hcover hnext
  have hout := or_fold_cover after _ (fun t => runStep (pre t) g) hafter
    (fun t => by simp [runStep, hlen t]) hpost
  have hc : (after.foldl runStep (runStep (before.foldl runStep c) g)).getD C.output false = true := by
    change (C.gates.foldl runStep c).getD C.output false = true at hpositive
    rw [hsplit, List.foldl_append, List.foldl_cons] at hpositive
    exact hpositive
  obtain ⟨t,ht⟩ := hout C.output hc
  have ht' : C.eval (inputs t) = true := by
    change (C.gates.foldl runStep (inputs t)).getD C.output false = true
    rw [hsplit, List.foldl_append, List.foldl_cons]
    exact ht
  fin_cases t
  · change C.eval a = true at ht'
    rw [hfirst] at ht'
    cases ht'
  · change C.eval b = true at ht'
    rw [hsecond] at ht'
    cases ht'
  · exact ht'

lemma unique_and_context (C : Circuit) (j : ℕ) (hmono : Monotone2 C)
    (hj : j < C.gates.length)
    (hunique : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k = j) :
    (∀ g ∈ C.gates.take j, g.op = GateOp.or) ∧
    (∀ g ∈ C.gates.drop (j + 1), g.op = GateOp.or) := by
  constructor
  · intro g hg
    rcases (show g.op = GateOp.and ∨ g.op = GateOp.or from
      by simpa using (hmono g (List.mem_of_mem_take hg)).1) with hand | hor
    · obtain ⟨k,hk,hget⟩ := List.mem_iff_getElem.mp hg
      have hkj : k < j := by
        have hlen : (C.gates.take j).length = j := by simp [List.length_take, Nat.min_eq_left hj.le]
        omega
      have hkC : k < C.gates.length := by omega
      have hgate : gateAt C k = g := by
        change C.gates.getD k ⟨GateOp.or, []⟩ = g
        rw [List.getD_eq_getElem C.gates _ hkC]
        simpa only [List.getElem_take] using hget
      have := hunique k hkC (by rw [hgate]; exact hand)
      omega
    · exact hor
  · intro g hg
    rcases (show g.op = GateOp.and ∨ g.op = GateOp.or from
      by simpa using (hmono g (List.mem_of_mem_drop hg)).1) with hand | hor
    · obtain ⟨k,hk,hget⟩ := List.mem_iff_getElem.mp hg
      have hkC : j + 1 + k < C.gates.length := by
        simp only [List.length_drop] at hk
        omega
      have hgate : gateAt C (j + 1 + k) = g := by
        change C.gates.getD (j + 1 + k) ⟨GateOp.or, []⟩ = g
        rw [List.getD_eq_getElem C.gates _ hkC]
        simpa only [List.getElem_drop] using hget
      have := hunique (j + 1 + k) hkC (by rw [hgate]; exact hand)
      omega
    · exact hor

lemma unique_and_below_output (C : Circuit) (j : ℕ) (a b c : List Bool)
    (hmono : Monotone2 C) (hj : j < C.gates.length)
    (hunique : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k = j)
    (ha : a.length = c.length) (hb : b.length = c.length)
    (hunion : ∀ i, c.getD i false = (a.getD i false || b.getD i false))
    (hpositive : C.eval c = true) (hfirst : C.eval a = false) (hsecond : C.eval b = false) :
    ∀ d : List Bool, d.length = c.length →
      (C.wires d).getD (d.length + j) false = true → C.eval d = true := by
  obtain ⟨hbefore,hafter⟩ := unique_and_context C j hmono hj hunique
  have ht : (C.gates.take j).length = j := by simp [List.length_take, Nat.min_eq_left hj.le]
  have h := sole_gate_below_output C (C.gates.take j) (C.gates.drop (j + 1)) (gateAt C j)
    a b c (gates_take_split C j hj) hbefore hafter ha hb hunion hpositive hfirst hsecond
  simpa only [ht] using h

lemma point_ne_line (N : ℕ) (p l : Fin N) :
    Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  change p.val = N + l.val at hv
  omega

lemma incidence_singleton_false (N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (C : Circuit)
    (hspec : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (v : Fin (N + N)) :
    C.eval (List.ofFn (fun k => decide (k = v))) = false := by
  cases heval : C.eval (List.ofFn (fun k => decide (k = v))) with
  | false => rfl
  | true =>
    obtain ⟨p,l,_,hp,hl⟩ := (hspec (fun k => decide (k = v))).mp heval
    have hp' : Fin.castAdd N p = v := of_decide_eq_true hp
    have hl' : Fin.natAdd N l = v := of_decide_eq_true hl
    exact False.elim (point_ne_line N p l (hp'.trans hl'.symm))

lemma incidence_nonedge_false (N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (C : Circuit)
    (hspec : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p0 l0 : Fin N) (hnot : ¬ I p0 l0) :
    C.eval (List.ofFn (fun k =>
      decide (k = Fin.castAdd N p0 ∨ k = Fin.natAdd N l0))) = false := by
  cases heval : C.eval (List.ofFn (fun k =>
      decide (k = Fin.castAdd N p0 ∨ k = Fin.natAdd N l0))) with
  | false => rfl
  | true =>
    obtain ⟨p,l,he,hp,hl⟩ :=
      (hspec (fun k => decide (k = Fin.castAdd N p0 ∨ k = Fin.natAdd N l0))).mp heval
    have hp' : Fin.castAdd N p = Fin.castAdd N p0 ∨
        Fin.castAdd N p = Fin.natAdd N l0 := of_decide_eq_true hp
    have hl' : Fin.natAdd N l = Fin.castAdd N p0 ∨
        Fin.natAdd N l = Fin.natAdd N l0 := of_decide_eq_true hl
    have hpp : p = p0 := by
      rcases hp' with h | h
      · apply Fin.ext
        exact congrArg (fun x : Fin (N + N) => x.val) h
      · exact False.elim (point_ne_line N p l0 h)
    have hll : l = l0 := by
      rcases hl' with h | h
      · exact False.elim (point_ne_line N p0 l h.symm)
      · apply Fin.ext
        have hv := congrArg Fin.val h
        change N + l.val = N + l0.val at hv
        omega
    subst p
    subst l
    exact False.elim (hnot he)

lemma unique_and_incidence_clean (N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (C : Circuit) (hmono : Monotone2 C)
    (hspec : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hunique : ∀ j < C.gates.length, ∀ k < C.gates.length,
      (gateAt C j).op = GateOp.and → (gateAt C k).op = GateOp.and → j = k)
    (hedge : ∃ p l : Fin N, I p l) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ p0 l0 : Fin N, ¬ I p0 l0 →
        (C.wires (List.ofFn (fun k =>
          decide (k = Fin.castAdd N p0 ∨ k = Fin.natAdd N l0)))).getD
            (N + N + j) false = false := by
  obtain ⟨p,l,he⟩ := hedge
  let a : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p)
  let b : Fin (N + N) → Bool := fun k => decide (k = Fin.natAdd N l)
  let c : Fin (N + N) → Bool := fun k => a k || b k
  have hpositive : C.eval (List.ofFn c) = true := by
    apply (hspec c).mpr
    exact ⟨p,l,he,by simp [c,a],by simp [c,b]⟩
  have hfirst : C.eval (List.ofFn a) = false :=
    incidence_singleton_false N I C hspec (Fin.castAdd N p)
  have hsecond : C.eval (List.ofFn b) = false :=
    incidence_singleton_false N I C hspec (Fin.natAdd N l)
  intro j hj hand p0 l0 hnot
  let d : Fin (N + N) → Bool := fun k =>
    decide (k = Fin.castAdd N p0 ∨ k = Fin.natAdd N l0)
  have hbelow := unique_and_below_output C j (List.ofFn a) (List.ofFn b) (List.ofFn c)
    hmono hj (fun k hk hkand => hunique k hk j hj hkand hand)
    (by simp) (by simp) (ofFn_union (N + N) a b) hpositive hfirst hsecond
  have hdout : C.eval (List.ofFn d) = false := incidence_nonedge_false N I C hspec p0 l0 hnot
  cases hdgate : (C.wires (List.ofFn d)).getD (N + N + j) false with
  | false => rfl
  | true =>
    have hout := hbelow (List.ofFn d) (by simp) (by simpa using hdgate)
    rw [hdout] at hout
    cases hout

lemma normalize_one_and_incidence (N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (C : Circuit) (hmono : Monotone2 C) (hback : ReadsBack (N + N) C)
    (hspec : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hsingle : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∀ p : Fin N, (C.wires (List.ofFn (fun k => decide (k = Fin.castAdd N p)))).getD
        (N + N + j) false = false) ∧
      ∀ l : Fin N, (C.wires (List.ofFn (fun k => decide (k = Fin.natAdd N l)))).getD
        (N + N + j) false = false)
    (hunique : ∀ j < C.gates.length, ∀ k < C.gates.length,
      (gateAt C j).op = GateOp.and → (gateAt C k).op = GateOp.and → j = k) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∀ p0 l0 : Fin N, ¬ I p0 l0 →
          (D.wires (List.ofFn (fun k =>
            decide (k = Fin.castAdd N p0 ∨ k = Fin.natAdd N l0)))).getD
              (N + N + j) false = false) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun k => decide (k = Fin.castAdd N p)))).getD
          (N + N + j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun k => decide (k = Fin.natAdd N l)))).getD
          (N + N + j) false = false) := by
  classical
  by_cases hedge : ∃ p l : Fin N, I p l
  · exact ⟨C,hmono,hback,le_rfl,hspec,
      unique_and_incidence_clean N I C hmono hspec hunique hedge,hsingle⟩
  · let D : Circuit := ⟨[],N + N⟩
    refine ⟨D,?_,?_,?_,?_,?_,?_⟩
    · simp [D,Monotone2]
    · simp [D,ReadsBack]
    · simp [D,Circuit.size]
    · intro z
      have hfalse : circuitFun (N + N) D z = false := by
        simp [D,circuitFun,Circuit.eval,Circuit.wires]
      rw [hfalse]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨p,l,he,_,_⟩
      exact hedge ⟨p,l,he⟩
    · simp [D]
    · simp [D]

end PEqualNP.Outside.L_meta_3457_aux
