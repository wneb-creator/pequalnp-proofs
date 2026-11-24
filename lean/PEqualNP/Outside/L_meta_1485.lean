import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1485

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), if_neg hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, if_pos (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [if_pos (by omega), bypass_val_lt hx hr i hi]
            · rw [if_neg (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, if_pos (by omega), if_pos (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), if_pos h3, if_pos (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), if_neg h3, if_neg (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k < C.gates.length, n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hk, hm⟩ => absurd hm (hno k hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)

def addTop (n : ℕ) (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g], n + C.gates.length⟩

lemma addTop_length (n : ℕ) (C : Circuit) (g : Gate) :
    (addTop n C g).gates.length = C.gates.length + 1 := by simp [addTop]

lemma addTop_eval {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) (g : Gate) :
    (addTop n C g).eval x = g.op.eval (g.inputs.map fun i => val C x i) := by
  have hl : (C.gates.foldl stepWire x).length = n + C.gates.length := by
    rw [foldl_length, hx]
  simp only [Circuit.eval, addTop, wires_eq_foldl, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rw [← hl]
  simp [stepWire, List.getD_eq_getElem?_getD, val, wires_eq_foldl]

lemma gateAt_addTop_lt {n : ℕ} {C : Circuit} {g : Gate} {k : ℕ} (hk : k < C.gates.length) :
    gateAt (addTop n C g) k = gateAt C k := by
  simp [gateAt, addTop, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma gateAt_addTop_len {n : ℕ} {C : Circuit} {g : Gate} :
    gateAt (addTop n C g) C.gates.length = g := by
  simp [gateAt, addTop, List.getD_eq_getElem?_getD]

lemma addTop_readsBack {n : ℕ} {C : Circuit} {g : Gate}
    (hg : ∀ u ∈ g.inputs, u < n + C.gates.length)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (addTop n C g).gates.length, ∀ u ∈ (gateAt (addTop n C g) k).inputs, u < n + k := by
  intro k hk u hu
  rw [addTop_length] at hk
  by_cases h : k < C.gates.length
  · rw [gateAt_addTop_lt h] at hu; exact hRB k h u hu
  · have hkk : k = C.gates.length := by omega
    subst hkk
    rw [gateAt_addTop_len] at hu
    exact hg u hu

lemma addTop_mem {n : ℕ} {C : Circuit} {g : Gate} :
    ∀ g' ∈ (addTop n C g).gates, g' ∈ C.gates ∨ g' = g := by
  intro g' hg'
  simpa [addTop] using hg'

def trunc (C : Circuit) (m o : ℕ) : Circuit := ⟨C.gates.take m, o⟩

lemma trunc_length {C : Circuit} {m o : ℕ} (hm : m ≤ C.gates.length) :
    (trunc C m o).gates.length = m := by simp [trunc, hm]

lemma gateAt_trunc {C : Circuit} {m o k : ℕ} (hk : k < m) :
    gateAt (trunc C m o) k = gateAt C k := by
  simp [gateAt, trunc, List.getD_eq_getElem?_getD, hk]

lemma trunc_eval {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {m o : ℕ}
    (hm : m ≤ C.gates.length) (ho : o < n + m) : (trunc C m o).eval x = val C x o := by
  rw [eval_eq_val]
  exact val_prefix hx hm (by rw [trunc_length hm]) (fun k hk => gateAt_trunc hk) o ho

lemma trunc_mem {C : Circuit} {m o : ℕ} : ∀ g ∈ (trunc C m o).gates, g ∈ C.gates :=
  fun _ hg => List.mem_of_mem_take hg

lemma caseB {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {j r : ℕ} (hr : r < C.gates.length) (hjr : j < r)
    (hmem : n + j ∈ (gateAt C r).inputs) (hand : (gateAt C r).op = GateOp.and)
    (hbelow : val C x (n + j) = true → C.eval x = true) :
    (bypass n C r (n + j)).eval x = C.eval x := by
  by_cases h : val C x (n + j) = true
  · have h1 := hbelow h
    have h2 := bypass_eval_rel (R := fun a b => a = true → b = true) (fun _ hb => hb)
      opMono_imp hx hAO hr (Or.inl (by omega)) (fun _ => h)
    rw [h1, h2 h1]
  · have hr0 : val C x (n + r) = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      exact h (((val_and hx hr hand).mp hc) _ hmem).2
    have hf : val C x (n + j) = false := by simpa using h
    exact bypass_eval_eq hx hAO hr (Or.inl (by omega)) (by rw [hr0, hf])

lemma bypass_or_eval {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {j r a : ℕ} (hr : r < C.gates.length) (ha : a < n + r)
    (hor : (gateAt C r).op = GateOp.or) (ha_mem : a ∈ (gateAt C r).inputs)
    (h1 : ∀ u ∈ (gateAt C r).inputs, u = n + j ∨ u = a)
    (hf : val C x (n + j) = false) :
    (bypass n C r a).eval x = C.eval x := by
  apply bypass_eval_eq hx hAO hr (Or.inl ha)
  rw [Bool.eq_iff_iff, val_or hx hr hor]
  constructor
  · rintro ⟨u, hu, _, hv⟩
    rcases h1 u hu with rfl | rfl
    · rw [hf] at hv; cases hv
    · exact hv
  · intro hv; exact ⟨a, ha_mem, ha, hv⟩

lemma caseC {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {j r1 r2 a b : ℕ} (hr2 : r2 < C.gates.length) (h12 : r1 < r2) (hj1 : j < r1)
    (ha : a < n + r1) (hb : b < n + r2)
    (hor1 : (gateAt C r1).op = GateOp.or) (hor2 : (gateAt C r2).op = GateOp.or)
    (ha_mem : a ∈ (gateAt C r1).inputs) (hb_mem : b ∈ (gateAt C r2).inputs)
    (h1 : ∀ u ∈ (gateAt C r1).inputs, u = n + j ∨ u = a)
    (h2 : ∀ u ∈ (gateAt C r2).inputs, u = n + j ∨ u = b)
    (hbelow : val C x (n + j) = true → C.eval x = true) :
    (addTop n (bypass n (bypass n C r2 b) r1 a)
      ⟨GateOp.or, [(bypass n (bypass n C r2 b) r1 a).output, n + j]⟩).eval x = C.eval x := by
  have hlen1 : r1 < (bypass n C r2 b).gates.length := by rw [bypass_length]; omega
  have hAO1 := bypass_AO (n := n) (i := b) hr2 hAO
  have hg1 : gateAt (bypass n C r2 b) r1 = gateAt C r1 := by
    rw [gateAt_bypass (by omega), if_pos h12]
  have hvj1 : val (bypass n C r2 b) x (n + j) = val C x (n + j) :=
    bypass_val_lt hx hr2 _ (by omega)
  have e1 : val C x (n + j) = false → (bypass n C r2 b).eval x = C.eval x :=
    fun hf => bypass_or_eval hx hAO hr2 hb hor2 hb_mem h2 hf
  rw [← hg1] at hor1 ha_mem h1
  generalize bypass n C r2 b = D1 at *
  have hvj2 : val (bypass n D1 r1 a) x (n + j) = val D1 x (n + j) :=
    bypass_val_lt hx hlen1 _ (by omega)
  have e2 : val D1 x (n + j) = false → (bypass n D1 r1 a).eval x = D1.eval x :=
    fun hf => bypass_or_eval hx hAO1 hlen1 ha hor1 ha_mem h1 hf
  rw [addTop_eval hx]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false]
  rw [hvj2, hvj1, ← eval_eq_val]
  by_cases h : val C x (n + j) = true
  · rw [h, hbelow h, Bool.or_true]
  · have hf : val C x (n + j) = false := by simpa using h
    rw [hf, Bool.or_false, e2 (by rw [hvj1]; exact hf), e1 hf]

lemma two_elems {l : List ℕ} (hl : l.length ≤ 2) {p a : ℕ} (hp : p ∈ l) (ha : a ∈ l)
    (hne : a ≠ p) : ∀ u ∈ l, u = p ∨ u = a := by
  match l, hl with
  | [], _ => simp at hp
  | [u], _ =>
    simp only [List.mem_singleton] at hp ha
    omega
  | [u, v], _ =>
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ha hw
    omega
  | _ :: _ :: _ :: _, h => simp at h

lemma main_abs (n : ℕ) (C : Circuit) (hn : 0 < n) (Good : Circuit → Prop)
    (hG_AO : ∀ D, Good D → ∀ k < D.gates.length,
      (gateAt D k).op = GateOp.and ∨ (gateAt D k).op = GateOp.or)
    (hG_byp : ∀ D r i, Good D → r < D.gates.length → i < n + r → Good (bypass n D r i))
    (hG_top : ∀ D a b, Good D → a < n + D.gates.length → b < n + D.gates.length →
      Good (addTop n D ⟨GateOp.or, [a, b]⟩))
    (hGC : Good C)
    (hlen2 : ∀ k < C.gates.length, (gateAt C k).inputs.length ≤ 2)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k)
    (hout : C.output < n + C.gates.length)
    (hmin : ∀ D, Good D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
      C.gates.length ≤ D.gates.length)
    (j : ℕ) (hj : j < C.gates.length) (hjo : n + j ≠ C.output)
    (hbelow : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + j) = true →
      C.eval (List.ofFn x) = true) :
    ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧ (gateAt C r).op = GateOp.or ∧
      ∀ r' < C.gates.length, n + j ∈ (gateAt C r').inputs → r' = r := by
  have hAO := hG_AO C hGC
  have hxl : ∀ x : Fin n → Bool, (List.ofFn x).length = n := fun x => List.length_ofFn
  have hreader : ∀ r < C.gates.length, n + j ∈ (gateAt C r).inputs →
      (gateAt C r).op = GateOp.or ∧ ∃ a ∈ (gateAt C r).inputs, a ≠ n + j := by
    intro r hr hmem
    have hjr : j < r := by have := hRB r hr _ hmem; omega
    have hor : (gateAt C r).op = GateOp.or := by
      rcases hAO r hr with hand | hor
      · exfalso
        have hD := hG_byp C r (n + j) hGC hr (by omega)
        have := hmin _ hD (fun x => caseB (hxl x) hAO hr hjr hmem hand (hbelow x))
        rw [bypass_length] at this; omega
      · exact hor
    refine ⟨hor, ?_⟩
    by_contra hall
    push Not at hall
    have hD := hG_byp C r (n + j) hGC hr (by omega)
    have := hmin _ hD (fun x => bypass_eval_eq (hxl x) hAO hr (Or.inl (by omega)) (by
      rw [Bool.eq_iff_iff, val_or (hxl x) hr hor]
      constructor
      · rintro ⟨u, hu, _, hv⟩; rw [hall u hu] at hv; exact hv
      · intro hv; exact ⟨n + j, hmem, by omega, hv⟩))
    rw [bypass_length] at this; omega
  have hex : ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs := by
    by_contra hno
    push Not at hno
    have hD := hG_byp C j 0 hGC hj (by omega)
    have := hmin _ hD (fun x => bypass_eval_unread (hxl x) hAO hj (Or.inl (by omega))
      (fun h => hjo h.symm) hno)
    rw [bypass_length] at this; omega
  obtain ⟨r, hr, hmem⟩ := hex
  refine ⟨r, hr, hmem, (hreader r hr hmem).1, ?_⟩
  have huniq : ∀ r1 r2, r1 < r2 → r2 < C.gates.length → n + j ∈ (gateAt C r1).inputs →
      n + j ∈ (gateAt C r2).inputs → False := by
    intro r1 r2 h12 hr2 hm1 hm2
    have hr1 : r1 < C.gates.length := by omega
    obtain ⟨hor1, a, ha_mem, ha_ne⟩ := hreader r1 hr1 hm1
    obtain ⟨hor2, b, hb_mem, hb_ne⟩ := hreader r2 hr2 hm2
    have hj1 : j < r1 := by have := hRB r1 hr1 _ hm1; omega
    have ha := hRB r1 hr1 _ ha_mem
    have hb := hRB r2 hr2 _ hb_mem
    have h1 := two_elems (hlen2 r1 hr1) hm1 ha_mem ha_ne
    have h2 := two_elems (hlen2 r2 hr2) hm2 hb_mem hb_ne
    have hD1 := hG_byp C r2 b hGC hr2 hb
    have hD2 := hG_byp _ r1 a hD1 (by rw [bypass_length]; omega) ha
    have hl2 : (bypass n (bypass n C r2 b) r1 a).gates.length = C.gates.length - 2 := by
      rw [bypass_length, bypass_length]; omega
    have ho2 : (bypass n (bypass n C r2 b) r1 a).output < n + (C.gates.length - 2) := by
      rw [bypass_output, bypass_output]
      have h3 := aliasWire_lt (u := C.output) (m := n + (C.gates.length - 1)) hb
        (by omega) (by omega)
      exact aliasWire_lt ha (by omega) (by omega)
    have hD3 := hG_top _ (bypass n (bypass n C r2 b) r1 a).output (n + j) hD2
      (by rw [hl2]; exact ho2) (by rw [hl2]; omega)
    have := hmin _ hD3 (fun x => caseC (hxl x) hAO hr2 h12 hj1 ha hb hor1 hor2 ha_mem hb_mem
      h1 h2 (hbelow x))
    rw [addTop_length, hl2] at this; omega
  intro r' hr' hmem'
  rcases Nat.lt_trichotomy r' r with h | h | h
  · exact (huniq r' r h hr hmem' hmem).elim
  · exact h
  · exact (huniq r r' h hr' hmem hmem').elim

lemma isAO2_bypass {n : ℕ} {D : Circuit} {r i : ℕ} (hD : PEqualNP.TopForm.IsAO2 n D)
    (hi : i < n + r) : PEqualNP.TopForm.IsAO2 n (bypass n D r i) := by
  refine ⟨?_, bypass_readsBack hi hD.2.1, ?_⟩
  · intro g hg
    obtain ⟨g', hg', hop, _⟩ := bypass_mem g hg
    rw [hop]; exact hD.1 g' hg'
  · intro g hg
    obtain ⟨g', hg', _, hl⟩ := bypass_mem g hg
    rw [hl]; exact hD.2.2 g' hg'

lemma isAO2_addTop {n : ℕ} {D : Circuit} {a b : ℕ} (hD : PEqualNP.TopForm.IsAO2 n D)
    (ha : a < n + D.gates.length) (hb : b < n + D.gates.length) :
    PEqualNP.TopForm.IsAO2 n (addTop n D ⟨GateOp.or, [a, b]⟩) := by
  refine ⟨?_, addTop_readsBack ?_ hD.2.1, ?_⟩
  · intro g hg
    rcases addTop_mem g hg with h | rfl
    · exact hD.1 g h
    · exact Or.inr rfl
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    rcases addTop_mem g hg with h | rfl
    · exact hD.2.2 g h
    · rfl

lemma final (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hne : G.edgeFinset.Nonempty) (hleast : PEqualNP.TopForm.IsLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (hbelow : PEqualNP.TopForm.BelowF G C j)
    (hjo : n + j ≠ C.output) :
    ∃ r, PEqualNP.TopForm.readers n C j = {r} ∧ (gateAt C r).op = GateOp.or := by
  have hadj : ∃ u v : Fin n, G.Adj u v := by
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ u v => exact ⟨u, v, by simpa using he⟩
  obtain ⟨u, v, he⟩ := hadj
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have htrue : graphFun G ∅ (fun _ => true) = true := by
    unfold graphFun
    rw [Bool.or_eq_true]
    right
    exact decide_eq_true ⟨u, v, he, rfl, rfl⟩
  obtain ⟨hAO2, hfun, hmin⟩ := hleast
  have hout : C.output < n + C.gates.length := by
    by_contra hc
    have h0 : C.eval (List.ofFn (fun _ : Fin n => true)) = false := by
      rw [eval_eq_val]; exact val_ge List.length_ofFn (by omega)
    have h1 : C.eval (List.ofFn (fun _ : Fin n => true)) = true := by
      have h2 := congrFun hfun (fun _ => true)
      rw [htrue] at h2; exact h2
    rw [h0] at h1; cases h1
  obtain ⟨r, hr, hmem, hor, huniq⟩ := main_abs n C hn (PEqualNP.TopForm.IsAO2 n)
    (fun D hD k hk => hD.1 _ (gateAt_mem hk))
    (fun D r i hD _ hi => isAO2_bypass hD hi)
    (fun D a b hD ha hb => isAO2_addTop hD ha hb) hAO2
    (fun k hk => le_of_eq (hAO2.2.2 _ (gateAt_mem hk))) hAO2.2.1 hout
    (fun D hD hfD => hmin D hD (by
      rw [← hfun]
      funext x
      exact hfD x))
    j hj hjo (fun x hx => by
      have h3 := hbelow x hx
      rw [← hfun] at h3
      exact h3)
  refine ⟨r, ?_, hor⟩
  ext k
  simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hk, hkm⟩; exact huniq k hk hkm
  · rintro rfl; exact ⟨hr, hmem⟩

end PEqualNP.Outside.L_meta_1485

theorem PEqualNP.Outside.L_meta_1485 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  ∀ j < C.gates.length, PEqualNP.TopForm.BelowF G C j → n + j ≠ C.output →
    ∃ r, PEqualNP.TopForm.readers n C j = {r} ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C r).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
  intro n G _ C hne hleast j hj hbelow hjo
  exact PEqualNP.Outside.L_meta_1485.final n G C hne hleast j hj hbelow hjo
