import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def dAndWeight : GateOp → Bool → Nat
  | .and, b => if b then 1 else 0
  | _, _ => 0

def dCount : List Gate → List Bool → Nat
  | [], _ => 0
  | g :: gs, w =>
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    dAndWeight g.op b + dCount gs (w ++ [b])

def dRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem dRun_length (gs : List Gate) (w : List Bool) :
    (dRun gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [dRun]
  | cons g gs ih =>
    simpa [dRun, List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])

theorem dGet_snoc {α : Type} (w : List α) (a d : α) (i : Nat) :
    (w ++ [a]).getD i d =
      if i < w.length then w.getD i d else if i=w.length then a else d := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [ite_eq_left h, List.getElem?_append_left h]
    rw [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right h, List.getElem?_append_right (by omega)]
    by_cases e : i=w.length
    · subst i; simp
    · rw [ite_eq_right e]
      have : i-w.length ≠ 0 := by omega
      simp [this]

def dAgree (k : Nat) (u v : List Bool) : Prop :=
  ∀ i, i≠k → u.getD i false = v.getD i false

theorem dRun_agree (k : Nat) (gs : List Gate)
    (noRead : ∀ g ∈ gs, k ∉ g.inputs) (u v : List Bool)
    (len : u.length=v.length) (agree : dAgree k u v) :
    dAgree k (dRun gs u) (dRun gs v) := by
  induction gs generalizing u v with
  | nil => exact agree
  | cons g gs ih =>
    have gate_eq : g.op.eval (g.inputs.map fun i => u.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      apply agree i
      intro eq
      exact noRead g List.mem_cons_self (eq ▸ hi)
    apply ih (fun q hq => noRead q (List.mem_cons_of_mem _ hq))
      (u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)])
      (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])
      (by simp [len])
    intro i hi
    simp only [dGet_snoc, ←len]
    split_ifs with h e
    · exact agree i hi
    · exact gate_eq
    · rfl

def dOld (m a b c : Nat) : List Gate :=
  [⟨.or,[a,b]⟩, ⟨.or,[a,c]⟩, ⟨.and,[m,m+1]⟩]

def dNew (m a b c : Nat) : List Gate :=
  [⟨.or,[a,b]⟩, ⟨.and,[b,c]⟩, ⟨.or,[a,m+1]⟩]

theorem dDistrib (a b c : Bool) :
    ((a || b) && (a || c)) = (a || (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem dOld_run (w : List Bool) (a b c : Nat)
    (ha : a<w.length) (hb : b<w.length) (hc : c<w.length) :
    dRun (dOld w.length a b c) w =
      ((w ++ [w.getD a false || w.getD b false]) ++
        [w.getD a false || w.getD c false]) ++
        [(w.getD a false || w.getD b false) &&
         (w.getD a false || w.getD c false)] := by
  have ha1 : a < w.length+1 := by omega
  have hc1 : c < w.length+1 := by omega
  simp [dRun, dOld, GateOp.eval, ha, hb, hc, ha1, hc1]

theorem dNew_run (w : List Bool) (a b c : Nat)
    (ha : a<w.length) (hb : b<w.length) (hc : c<w.length) :
    dRun (dNew w.length a b c) w =
      ((w ++ [w.getD a false || w.getD b false]) ++
        [w.getD b false && w.getD c false]) ++
        [w.getD a false || (w.getD b false && w.getD c false)] := by
  have hb1 : b < w.length+1 := by omega
  have hc1 : c < w.length+1 := by omega
  have ha2 : a < w.length+1+1 := by omega
  simp [dRun, dNew, GateOp.eval, ha, hb, hc, hb1, hc1, ha2]

theorem dLocal_agree (w : List Bool) (a b c : Nat)
    (ha : a<w.length) (hb : b<w.length) (hc : c<w.length) :
    dAgree (w.length+1) (dRun (dOld w.length a b c) w)
      (dRun (dNew w.length a b c) w) := by
  rw [dOld_run w a b c ha hb hc, dNew_run w a b c ha hb hc]
  intro i hi
  simp only [dGet_snoc, List.length_append, List.length_singleton]
  rw [dDistrib]
  simp only [ite_eq_right hi]

def dOldCircuit (n : Nat) (pre post : List Gate) (a b c o : Nat) : Circuit :=
  ⟨pre ++ dOld (n+pre.length) a b c ++ post, o⟩

def dNewCircuit (n : Nat) (pre post : List Gate) (a b c o : Nat) : Circuit :=
  ⟨pre ++ dNew (n+pre.length) a b c ++ post, o⟩

-- The replaced middle wire may be used by the final local gate only.
-- The first OR is retained and can have arbitrary later readers.
theorem diamond_rewrite (n : Nat) (pre post : List Gate) (a b c o : Nat)
    (ha : a<n+pre.length) (hb : b<n+pre.length) (hc : c<n+pre.length)
    (noRead : ∀ g ∈ post, n+pre.length+1 ∉ g.inputs)
    (out : o≠n+pre.length+1) :
    (dOldCircuit n pre post a b c o).size = (dNewCircuit n pre post a b c o).size ∧
    ∀ x : List Bool, x.length=n →
      (dOldCircuit n pre post a b c o).eval x =
        (dNewCircuit n pre post a b c o).eval x := by
  refine ⟨by simp [dOldCircuit,dNewCircuit,Circuit.size,dOld,dNew], ?_⟩
  intro x hx
  let w := dRun pre x
  have hw : w.length=n+pre.length := by simp [w,dRun_length,hx]
  have local_eq := dLocal_agree w a b c (by omega) (by omega) (by omega)
  rw [hw] at local_eq
  have agree := dRun_agree (n+pre.length+1) post noRead
    (dRun (dOld (n+pre.length) a b c) w)
    (dRun (dNew (n+pre.length) a b c) w)
    (by simp [dRun_length,dOld,dNew]) local_eq o out
  simpa [dOldCircuit,dNewCircuit,Circuit.eval,Circuit.wires,dRun,
    List.foldl_append,w] using agree

theorem diamond_new_and_le (a b c : Bool) :
    (b && c) = true → ((a || b) && (a || c)) = true := by
  cases a <;> cases b <;> cases c <;> decide

theorem diamond_singleton_gain :
    ((true || false) && (true || false)) = true ∧ (false && false) = false := by
  decide

end PEqualNP.Outside.L_meta_1904_aux

namespace PEqualNP.Outside.L_meta_1904_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem dCount_append (gs hs : List Gate) (w : List Bool) :
    dCount (gs ++ hs) w = dCount gs w + dCount hs (dRun gs w) := by
  induction gs generalizing w with
  | nil => simp [dCount, dRun]
  | cons g gs ih =>
    simp [dCount, dRun, List.foldl_cons, ih, Nat.add_assoc]

theorem dCount_agree (k : Nat) (gs : List Gate)
    (noRead : ∀ g ∈ gs, k ∉ g.inputs) (u v : List Bool)
    (len : u.length = v.length) (agree : dAgree k u v) :
    dCount gs u = dCount gs v := by
  induction gs generalizing u v with
  | nil => rfl
  | cons g gs ih =>
    have gate_eq : g.op.eval (g.inputs.map fun i => u.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      apply agree i
      intro eq
      exact noRead g List.mem_cons_self (eq ▸ hi)
    have next : dAgree k
        (u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)])
        (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) := by
      intro i hi
      simp only [dGet_snoc, ← len]
      split_ifs with h e
      · exact agree i hi
      · exact gate_eq
      · rfl
    have tail_eq := ih (fun q hq => noRead q (List.mem_cons_of_mem _ hq))
      (u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)])
      (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])
      (by simp [len]) next
    simp only [dCount, gate_eq] at tail_eq ⊢
    rw [tail_eq]

theorem dRun_getD (gs : List Gate) (w : List Bool) (i : Nat)
    (hi : i < w.length) : (dRun gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (dRun gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = _
    rw [ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

theorem dCount_old (w : List Bool) (a b c : Nat)
    (ha : a < w.length) (hb : b < w.length) (hc : c < w.length) :
    dCount (dOld w.length a b c) w =
      if ((w.getD a false || w.getD b false) &&
        (w.getD a false || w.getD c false)) then 1 else 0 := by
  have ha1 : a < w.length + 1 := by omega
  have hc1 : c < w.length + 1 := by omega
  simp [dCount, dOld, dAndWeight, GateOp.eval, ha, hb, hc, ha1, hc1]

theorem dCount_new (w : List Bool) (a b c : Nat)
    (ha : a < w.length) (hb : b < w.length) (hc : c < w.length) :
    dCount (dNew w.length a b c) w =
      if (w.getD b false && w.getD c false) then 1 else 0 := by
  simp [dCount, dNew, dAndWeight, GateOp.eval, ha, hb, hc]
  simp [List.getElem?_append_left hb, List.getElem?_append_left hc,
    List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hc]

def singletonAndRank (n : Nat) (C : Circuit) : Nat :=
  ∑ v : Fin n, dCount C.gates (List.ofFn fun i : Fin n => decide (i = v))

theorem diamond_singleton_count (n : Nat) (pre post : List Gate)
    (a b c v : Fin n) (o : Nat) (bc : b ≠ c)
    (noRead : ∀ g ∈ post, n + pre.length + 1 ∉ g.inputs) :
    dCount (dOldCircuit n pre post a b c o).gates
        (List.ofFn fun i : Fin n => decide (i = v)) =
      dCount (dNewCircuit n pre post a b c o).gates
        (List.ofFn fun i : Fin n => decide (i = v)) + if v = a then 1 else 0 := by
  let x := List.ofFn fun i : Fin n => decide (i = v)
  let w := dRun pre x
  have hw : w.length = n + pre.length := by simp [w, x, dRun_length]
  have hv (i : Fin n) : w.getD i false = decide (i = v) := by
    rw [show w = dRun pre x from rfl, dRun_getD pre x i (by simp [x])]
    simp [x]
  have ha : (a : Nat) < w.length := by rw [hw]; omega
  have hb : (b : Nat) < w.length := by rw [hw]; omega
  have hc : (c : Nat) < w.length := by rw [hw]; omega
  have hbc : (decide (b = v) && decide (c = v)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have both : b = v ∧ c = v := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
    exact bc (both.1.trans both.2.symm)
  have old : dCount (dOld (n + pre.length) a b c) w =
      if v = a then 1 else 0 := by
    rw [← hw, dCount_old w a b c ha hb hc, hv a, hv b, hv c]
    rw [dDistrib, hbc, Bool.or_false]
    simp only [decide_eq_true_eq]
    by_cases av : a = v
    · rw [if_pos av, if_pos av.symm]
    · rw [if_neg av, if_neg (Ne.symm av)]
  have new : dCount (dNew (n + pre.length) a b c) w = 0 := by
    rw [← hw, dCount_new w a b c ha hb hc, hv b, hv c, hbc]
    rfl
  have local_eq := dLocal_agree w a b c ha hb hc
  rw [hw] at local_eq
  have tail_eq := dCount_agree (n + pre.length + 1) post noRead
    (dRun (dOld (n + pre.length) a b c) w)
    (dRun (dNew (n + pre.length) a b c) w)
    (by simp [dRun_length, dOld, dNew]) local_eq
  change dCount ((pre ++ dOld (n + pre.length) a b c) ++ post) x =
    dCount ((pre ++ dNew (n + pre.length) a b c) ++ post) x + _
  simp only [dCount_append, dRun, List.foldl_append]
  change dCount pre x + dCount (dOld (n + pre.length) a b c) w +
    dCount post (dRun (dOld (n + pre.length) a b c) w) =
    dCount pre x + dCount (dNew (n + pre.length) a b c) w +
    dCount post (dRun (dNew (n + pre.length) a b c) w) + _
  rw [old, new, tail_eq]
  omega

theorem diamond_singleton_rank (n : Nat) (pre post : List Gate)
    (a b c : Fin n) (o : Nat) (bc : b ≠ c)
    (noRead : ∀ g ∈ post, n + pre.length + 1 ∉ g.inputs) :
    singletonAndRank n (dOldCircuit n pre post a b c o) =
      singletonAndRank n (dNewCircuit n pre post a b c o) + 1 := by
  unfold singletonAndRank
  simp_rw [diamond_singleton_count n pre post a b c _ o bc noRead]
  rw [Finset.sum_add_distrib]
  simp

theorem diamond_monotone (n : Nat) (pre post : List Gate) (a b c o : Nat) :
    Monotone2 (dOldCircuit n pre post a b c o) ↔
      Monotone2 (dNewCircuit n pre post a b c o) := by
  simp [Monotone2, dOldCircuit, dNewCircuit, dOld, dNew, or_imp, forall_and]

end PEqualNP.Outside.L_meta_1904_aux
