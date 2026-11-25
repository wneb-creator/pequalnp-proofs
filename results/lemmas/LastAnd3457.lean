import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3457_aux.LastAnd

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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

lemma or_fold_mono (gs : List Gate) (a b : List Bool)
    (hor : ∀ g ∈ gs, g.op = GateOp.or) (hlen : a.length = b.length)
    (hle : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (gs.foldl runStep a).getD i false = true →
      (gs.foldl runStep b).getD i false = true := by
  intro i hi
  obtain ⟨t,ht⟩ := or_fold_cover gs a (fun _ : Unit => b) hor
    (fun _ => hlen.symm) (fun i hi => ⟨(),hle i hi⟩) i hi
  exact ht

lemma slot_basis_cover (m : ℕ) (w : List Bool) (b : Bool) (hlen : w.length = m) :
    ∀ i, ((List.replicate m false) ++ [b]).getD i false = true →
      (w ++ [true]).getD i false = true := by
  intro i hi
  obtain ⟨t,ht⟩ := append_cover (List.replicate m false) (fun _ : Unit => w)
    b (fun _ => true) (fun _ => by simpa using hlen)
    (by intro k hk; simp [List.getD_eq_getElem?_getD] at hk) (fun _ => ⟨(),rfl⟩) i hi
  exact ht

lemma or_fold_slot_basis_le (gs : List Gate) (m output : ℕ) (w : List Bool) (b : Bool)
    (hor : ∀ g ∈ gs, g.op = GateOp.or) (hlen : w.length = m) :
    (gs.foldl runStep ((List.replicate m false) ++ [b])).getD output false = true →
      (gs.foldl runStep (w ++ [true])).getD output false = true := by
  exact or_fold_mono gs _ _ hor (by simp [hlen]) (slot_basis_cover m w b hlen) output

lemma or_suffix_slot_dichotomy (gs : List Gate) (m output : ℕ)
    (hor : ∀ g ∈ gs, g.op = GateOp.or) :
    (∀ w : List Bool, w.length = m →
      (gs.foldl runStep (w ++ [true])).getD output false = true) ∨
    (∀ (w : List Bool) (b : Bool), w.length = m →
      (gs.foldl runStep (w ++ [b])).getD output false =
        (gs.foldl runStep (w ++ [false])).getD output false) := by
  cases hflag : (gs.foldl runStep ((List.replicate m false) ++ [true])).getD output false with
  | true =>
    left
    intro w hw
    exact or_fold_slot_basis_le gs m output w true hor hw hflag
  | false =>
    right
    intro w b hw
    have hb : (gs.foldl runStep ((List.replicate m false) ++ [b])).getD output false = false := by
      cases hval : (gs.foldl runStep ((List.replicate m false) ++ [b])).getD output false with
      | false => rfl
      | true =>
        have ht := or_fold_slot_basis_le gs m output (List.replicate m false) b hor
          (by simp) hval
        rw [hflag] at ht
        cases ht
    have hsum := or_fold_union gs (w ++ [false]) ((List.replicate m false) ++ [b])
      (w ++ [b]) hor (by simp) (by simp [hw])
      (append_union w (List.replicate m false) w false b b rfl (by simp [hw])
        (by intro i; simp [List.getD_eq_getElem?_getD]) (by simp))
    rw [hsum output, hb]
    simp

lemma or_suffix_gate_dichotomy (C : Circuit) (before after : List Gate) (g : Gate)
    (n : ℕ) (hsplit : C.gates = before ++ g :: after)
    (hafter : ∀ q ∈ after, q.op = GateOp.or) :
    (∀ d : List Bool, d.length = n →
      (C.wires d).getD (n + before.length) false = true → C.eval d = true) ∨
    (∀ d : List Bool, d.length = n →
      C.eval d = ({gates := before ++ ⟨GateOp.or, []⟩ :: after, output := C.output} : Circuit).eval d) := by
  rcases or_suffix_slot_dichotomy after (n + before.length) C.output hafter with hused | hdead
  · left
    intro d hd hg
    have hvalue := circuit_split_value C before after g d hsplit
    rw [hd] at hvalue
    have hv : g.op.eval (g.inputs.map fun i => (before.foldl runStep d).getD i false) = true :=
      hvalue.symm.trans hg
    have hout := hused (before.foldl runStep d) (by rw [fold_length, hd])
    change (C.gates.foldl runStep d).getD C.output false = true
    rw [hsplit, List.foldl_append, List.foldl_cons]
    change (after.foldl runStep ((before.foldl runStep d) ++
      [g.op.eval (g.inputs.map fun i => (before.foldl runStep d).getD i false)])).getD C.output false = true
    rw [hv]
    exact hout
  · right
    intro d hd
    have hout := hdead (before.foldl runStep d)
      (g.op.eval (g.inputs.map fun i => (before.foldl runStep d).getD i false))
      (by rw [fold_length, hd])
    change (C.gates.foldl runStep d).getD C.output false =
      ((before ++ ⟨GateOp.or, []⟩ :: after).foldl runStep d).getD C.output false
    simp only [hsplit, List.foldl_append, List.foldl_cons]
    exact hout

end PEqualNP.Outside.L_meta_3457_aux.LastAnd
