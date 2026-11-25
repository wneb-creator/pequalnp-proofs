import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3754.Bypass

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

lemma isAO2_bypass {n : ℕ} {D : Circuit} {r i : ℕ} (hD : PEqualNP.TopForm.IsAO2 n D)
    (hi : i < n + r) : PEqualNP.TopForm.IsAO2 n (bypass n D r i) := by
  refine ⟨?_, bypass_readsBack hi hD.2.1, ?_⟩
  · intro g hg
    obtain ⟨g', hg', hop, _⟩ := bypass_mem g hg
    rw [hop]; exact hD.1 g' hg'
  · intro g hg
    obtain ⟨g', hg', _, hl⟩ := bypass_mem g hg
    rw [hl]; exact hD.2.2 g' hg'


lemma bypass_and_below {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r)
    (hmem : i ∈ (gateAt C r).inputs) (hand : (gateAt C r).op = GateOp.and)
    (hbelow : val C x i = true → C.eval x = true) :
    (bypass n C r i).eval x = C.eval x := by
  by_cases h : val C x i = true
  · have h1 := hbelow h
    have h2 := bypass_eval_rel (R := fun a b => a = true → b = true) (fun _ hb => hb)
      opMono_imp hx hAO hr (Or.inl hi) (fun _ => h)
    rw [h1, h2 h1]
  · have hr0 : val C x (n + r) = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      exact h (((val_and hx hr hand).mp hc) _ hmem).2
    have hf : val C x i = false := by simpa using h
    exact bypass_eval_eq hx hAO hr (Or.inl hi) (by rw [hr0, hf])

open PEqualNP.TopForm PEqualNP.MetaComplexity

lemma least_no_and_below_operand {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hleast : IsLeastAO G C)
    {r i : ℕ} (hr : r < C.gates.length) (hand : (gateAt C r).op = GateOp.and)
    (hmem : i ∈ (gateAt C r).inputs) :
    ¬ (∀ x : Fin n → Bool, val C (List.ofFn x) i = true → graphFun G ∅ x = true) := by
  intro hbelow
  have hi : i < n + r := hleast.1.2.1 r hr i hmem
  have hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
    intro k hk
    exact hleast.1.1 _ (gateAt_mem hk)
  have heq : circuitFun n (bypass n C r i) = graphFun G ∅ := by
    rw [← hleast.2.1]
    funext x
    change (bypass n C r i).eval (List.ofFn x) = C.eval (List.ofFn x)
    apply bypass_and_below (by simp) hAO hr hi hmem hand
    intro hv
    have hf := hbelow x hv
    have hfun := congrFun hleast.2.1 x
    change C.eval (List.ofFn x) = graphFun G ∅ x at hfun
    exact hfun.trans hf
  have hsize := hleast.2.2 _ (isAO2_bypass hleast.1 hi) heq
  change C.gates.length ≤ (bypass n C r i).gates.length at hsize
  rw [bypass_length] at hsize
  omega

lemma least_no_equal_earlier {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hleast : IsLeastAO G C)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r) :
    ¬ (∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = val C (List.ofFn x) i) := by
  intro hequal
  have hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
    intro k hk
    exact hleast.1.1 _ (gateAt_mem hk)
  have heq : circuitFun n (bypass n C r i) = graphFun G ∅ := by
    rw [← hleast.2.1]
    funext x
    change (bypass n C r i).eval (List.ofFn x) = C.eval (List.ofFn x)
    exact bypass_eval_eq (by simp) hAO hr (Or.inl hi) (hequal x)
  have hsize := hleast.2.2 _ (isAO2_bypass hleast.1 hi) heq
  change C.gates.length ≤ (bypass n C r i).gates.length at hsize
  rw [bypass_length] at hsize
  omega

end PEqualNP.Outside.L_meta_3754.Bypass

-- Wire evaluation helpers are adapted from L_meta_5779 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_3754.Ledger
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl wireStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl wireStep acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (wireStep acc g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (wireStep acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_left hw]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  exact foldl_wireStep_length C.gates x

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    wireVal n C (n + k) x =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => wireVal n C u x) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, wireVal n C u x = acc.getD u false := by
    intro u hu
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : wireVal n C (n + k) x =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD (n + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + k < (wireStep acc C.gates[k]).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_wireStep_prefix (C.gates.drop (k + 1)) (wireStep acc C.gates[k]) (n + k) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C k hk] at hu
  exact (hpref u (hRB k hk u hu)).symm


lemma gate_two (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) : ∃ a b,(gateAt C j).inputs=[a,b] := by
  have hm : gateAt C j∈C.gates := by rw [gateAt_eq_getElem C j hj];exact List.getElem_mem hj
  exact List.length_eq_two.mp (hAO.2.2 _ hm)

lemma wire_all_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w,w<n+C.gates.length → wireVal n C w (fun _ => true)=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hinput : w<n
    · rw [wireVal_input n C _ w hinput]
    · obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
      have hk : k<C.gates.length := by omega
      obtain ⟨a,b,hab⟩ := gate_two n C hAO k hk
      have ha : a<n+k := hAO.2.1 k hk a (by simp [hab])
      have hb : b<n+k := hAO.2.1 k hk b (by simp [hab])
      have hva := ih a ha (by omega)
      have hvb := ih b hb (by omega)
      have hm : gateAt C k∈C.gates := by rw [gateAt_eq_getElem C k hk];exact List.getElem_mem hk
      rw [wireVal_gate n C _ k hk hAO.2.1,hab]
      rcases hAO.1 _ hm with hop | hop <;> simp [hop,GateOp.eval,hva,hvb]

lemma operand_bound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) (b : Fin 2) : opnd C j b<n+j := by
  obtain ⟨a,c,hac⟩ := gate_two n C hAO j hj
  have hb : opnd C j b∈(gateAt C j).inputs := by
    fin_cases b <;> simp [opnd,hac]
  exact hAO.2.1 j hj _ hb

lemma below_wire_implicant {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) (hw : w<n+C.gates.length)
    (hbelow : ∀ x : Fin n → Bool,PEqualNP.ReadTwo.wval C x w=true → graphFun G ∅ x=true) :
    PEqualNP.Core.IsImpWire G C w := by
  refine ⟨hbelow,fun _ => true,?_⟩
  exact wire_all_true n C hAO w hw

lemma fixed_or_reader_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j)
    (hop : (gateAt C j).op=GateOp.or) (b : Fin 2)
    (hbelow : ∀ x : Fin n → Bool,
      PEqualNP.ReadTwo.wval C x (opnd C j b)=true → graphFun G ∅ x=true) :
    BelowF G C j := by
  by_contra hn
  apply hfixed
  refine ⟨j,hcone.1,b,hcone,hop,hn,?_⟩
  exact below_wire_implicant G C hAO _ ((operand_bound n C hAO j hcone.1 b).trans (Nat.add_lt_add_left hcone.1 n)) hbelow

lemma and_reader_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j<C.gates.length)
    (hop : (gateAt C j).op=GateOp.and) (b : Fin 2)
    (hbelow : ∀ x : Fin n → Bool,
      PEqualNP.ReadTwo.wval C x (opnd C j b)=true → graphFun G ∅ x=true) :
    BelowF G C j := by
  intro x hx
  apply hbelow x
  change wireVal n C (n+j) x=true at hx
  rw [wireVal_gate n C x j hj hAO.2.1,hop] at hx
  simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at hx
  apply hx
  obtain ⟨a,c,hac⟩ := gate_two n C hAO j hj
  fin_cases b <;> simp [opnd,hac]

lemma fixed_reader_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (b : Fin 2)
    (hbelow : ∀ x : Fin n → Bool,
      PEqualNP.ReadTwo.wval C x (opnd C j b)=true → graphFun G ∅ x=true) :
    BelowF G C j := by
  have hm : gateAt C j∈C.gates := by
    rw [gateAt_eq_getElem C j hcone.1];exact List.getElem_mem hcone.1
  rcases hAO.1 _ hm with hop | hop
  · exact and_reader_closed G C hAO j hcone.1 hop b hbelow
  · exact fixed_or_reader_closed G C hAO hfixed j hcone hop b hbelow

lemma dirty_operand_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j) (b : Fin 2) :
    ∃ x : Fin n → Bool,PEqualNP.ReadTwo.wval C x (opnd C j b)=true ∧ graphFun G ∅ x=false := by
  classical
  by_contra hn
  apply hdirty
  apply fixed_reader_closed G C hAO hfixed j hcone b
  intro x hx
  cases hf : graphFun G ∅ x with
  | false => exact False.elim (hn ⟨x,hx,hf⟩)
  | true => rfl
lemma foldl_coneStep_length (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_coneStep_prefix (n : ℕ) (gs : List Gate) (acc : List (List ℕ))
    (j : ℕ) (hj : j < acc.length) :
    (gs.foldl (coneStep n) acc).getD j [] = acc.getD j [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hj' : j < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (coneStep n acc g) hj']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_left hj]

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (coneStep n) [] with hacc
  have hacc_len : acc.length = j := by
    rw [hacc, foldl_coneStep_length, List.length_nil, List.length_take]
    omega
  have hpref : ∀ k < j, (cones n C).getD k [] = acc.getD k [] := by
    intro k hk
    unfold cones
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_coneStep_prefix n (C.gates.drop j) acc k (by omega)
  have hstep : (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: acc.getD (w - n) []) := by
    unfold cones
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : j < (coneStep n acc C.gates[j]).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_coneStep_prefix n (C.gates.drop (j + 1)) (coneStep n acc C.gates[j]) j hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_right (by omega : acc.length ≤ j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      gateAt_eq_getElem C j hj]
  unfold InCone
  rw [hstep, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    rw [List.mem_filter] at hw
    have hbounds : n ≤ w ∧ w < n + j := by simpa using hw.2
    rw [List.mem_cons] at hi
    refine ⟨w, hw.1, hbounds.1, hbounds.2, ?_⟩
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · right
      rw [hpref (w - n) (by omega)]
      exact hi
  · rintro ⟨w, hw, hnw, hlt, hi⟩
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hw, by simpa using And.intro hnw hlt⟩
    · rw [List.mem_cons]
      rcases hi with rfl | hi
      · exact Or.inl rfl
      · right
        rw [← hpref (w - n) (by omega)]
        exact hi


lemma inCone_lt (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j<C.gates.length)
    (h : InCone n C i j) : i<j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨w,hw,hnw,hwj,hi⟩ := (inCone_iff n C i j hj).mp h
    rcases hi with hi | hi
    · omega
    · have hh := ih (w-n) (by omega) (by omega) hi
      omega

lemma inCone_trans (n : ℕ) (C : Circuit) (i j k : ℕ) (hk : k<C.gates.length)
    (hij : InCone n C i j) (hjk : InCone n C j k) : InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨w,hw,hnw,hwk,hj⟩ := (inCone_iff n C j k hk).mp hjk
    apply (inCone_iff n C i k hk).mpr
    refine ⟨w,hw,hnw,hwk,Or.inr ?_⟩
    rcases hj with rfl | hj
    · exact hij
    · exact ih (w-n) (by omega) (by omega) hj

lemma output_cone_ancestor (n : ℕ) (C : Circuit) (i j : ℕ)
    (hcone : PEqualNP.Core.InOutputCone n C j) (hij : InCone n C i j) :
    PEqualNP.Core.InOutputCone n C i := by
  have hi := (inCone_lt n C i j hcone.1 hij).trans hcone.1
  refine ⟨hi,Or.inr ?_⟩
  rcases hcone.2 with heq | ⟨hle,hjc⟩
  · refine ⟨by omega,?_⟩
    simpa only [heq,Nat.add_sub_cancel_left] using hij
  · refine ⟨hle,?_⟩
    have hout : C.output-n<C.gates.length := by
      by_contra hbad
      have hz : (cones n C).getD (C.output-n) []=[] := by
        apply List.getD_eq_default
        have hlen : (cones n C).length=C.gates.length := by
          simpa [cones] using foldl_coneStep_length n C.gates []
        omega
      change j∈(cones n C).getD (C.output-n) [] at hjc
      rw [hz] at hjc
      simp at hjc
    exact inCone_trans n C i j (C.output-n) hout hij hjc

lemma mem_inputs_opnd (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) (w : ℕ) (hw : w∈(gateAt C j).inputs) :
    ∃ b : Fin 2,opnd C j b=w := by
  obtain ⟨a,c,hac⟩ := gate_two n C hAO j hj
  simp [hac] at hw
  rcases hw with rfl | rfl
  · exact ⟨0,by simp [opnd,hac]⟩
  · exact ⟨1,by simp [opnd,hac]⟩

lemma fixed_reader_closed_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j)
    (w : ℕ) (hw : w∈(gateAt C j).inputs)
    (hbelow : ∀ x : Fin n → Bool,PEqualNP.ReadTwo.wval C x w=true → graphFun G ∅ x=true) :
    BelowF G C j := by
  obtain ⟨b,hb⟩ := mem_inputs_opnd n C hAO j hcone.1 w hw
  apply fixed_reader_closed G C hAO hfixed j hcone b
  simpa only [hb] using hbelow

lemma fixed_cone_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C) :
    ∀ j,PEqualNP.Core.InOutputCone n C j → ∀i,InCone n C i j → BelowF G C i → BelowF G C j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hcone i hanc hib
    obtain ⟨w,hw,hnw,hwj,hi⟩ := (inCone_iff n C i j hcone.1).mp hanc
    have hwcone : InCone n C (w-n) j :=
      (inCone_iff n C (w-n) j hcone.1).mpr ⟨w,hw,hnw,hwj,Or.inl rfl⟩
    have hclean : BelowF G C (w-n) := by
      rcases hi with rfl | hi
      · exact hib
      · exact ih (w-n) (by omega) (output_cone_ancestor n C (w-n) j hcone hwcone) i hi hib
    apply fixed_reader_closed_mem G C hAO hfixed j hcone w hw
    intro x hx
    apply hclean x
    have he : n+(w-n)=w := by omega
    simpa only [gateVal,PEqualNP.ReadTwo.wval,he] using hx

lemma earliest_dirty_no_and_ancestor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j)
    (hearlier : ∀i<j,(gateAt C i).op=GateOp.and → BelowF G C i)
    (i : ℕ) (hi : InCone n C i j) : (gateAt C i).op≠GateOp.and := by
  intro hand
  exact hdirty (fixed_cone_closed G C hAO hfixed j hcone i hi
    (hearlier i (inCone_lt n C i j hcone.1 hi) hand))

lemma earliest_dirty_ancestor_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j)
    (hearlier : ∀i<j,(gateAt C i).op=GateOp.and → BelowF G C i)
    (i : ℕ) (hi : InCone n C i j) : (gateAt C i).op=GateOp.or := by
  have hil := (inCone_lt n C i j hcone.1 hi).trans hcone.1
  have him : gateAt C i∈C.gates := by rw [gateAt_eq_getElem C i hil];exact List.getElem_mem hil
  rcases hAO.1 _ him with hand | hor
  · exact (earliest_dirty_no_and_ancestor G C hAO hfixed j hcone hdirty hearlier i hi hand).elim
  · exact hor


lemma gate_eval_monotone (g : Gate) (hg : g.op=GateOp.and ∨ g.op=GateOp.or)
    (x y : ℕ → Bool) (hxy : ∀i∈g.inputs,x i=true → y i=true) :
    g.op.eval (g.inputs.map x)=true → g.op.eval (g.inputs.map y)=true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval,List.all_map,Function.comp_def,id_eq,List.all_eq_true]
    intro h i hi
    exact hxy i hi (h i hi)
  · rw [hg]
    simp only [GateOp.eval,List.any_map,Function.comp_def,id_eq,List.any_eq_true]
    rintro ⟨i,hi,h⟩
    exact ⟨i,hi,hxy i hi h⟩

lemma wire_monotone (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀i,x i=true → y i=true) :
    ∀w,w<n+C.gates.length → wireVal n C w x=true → wireVal n C w y=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx
    by_cases hinput : w<n
    · rw [wireVal_input n C x w hinput] at hx
      rw [wireVal_input n C y w hinput]
      exact hxy _ hx
    · obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
      have hk : k<C.gates.length := by omega
      have hm : gateAt C k∈C.gates := by rw [gateAt_eq_getElem C k hk];exact List.getElem_mem hk
      rw [wireVal_gate n C x k hk hAO.2.1] at hx
      rw [wireVal_gate n C y k hk hAO.2.1]
      apply gate_eval_monotone (gateAt C k) (hAO.1 _ hm)
        (fun u => wireVal n C u x) (fun u => wireVal n C u y) _ hx
      intro u hu huv
      have hub := hAO.2.1 k hk u hu
      exact ih u hub (by omega) huv

lemma wire_or_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) (hop : (gateAt C j).op=GateOp.or)
    (w : ℕ) (hw : w∈(gateAt C j).inputs) (x : Fin n → Bool)
    (hx : wireVal n C w x=true) : wireVal n C (n+j) x=true := by
  rw [wireVal_gate n C x j hj hAO.2.1,hop]
  simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
  exact ⟨w,hw,hx⟩

def singletonInput {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i=v)

def singletonSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => wireVal n C w (singletonInput v)=true

lemma or_cone_singleton_witness (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∀j,j<C.gates.length → (gateAt C j).op=GateOp.or →
      (∀i,InCone n C i j → (gateAt C i).op=GateOp.or) →
      ∀x : Fin n → Bool,wireVal n C (n+j) x=true →
        ∃v : Fin n,x v=true ∧ wireVal n C (n+j) (singletonInput v)=true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hop hanc x hx
    rw [wireVal_gate n C x j hj hAO.2.1,hop] at hx
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at hx
    obtain ⟨w,hw,hwx⟩ := hx
    have hwj := hAO.2.1 j hj w hw
    by_cases hinput : w<n
    · refine ⟨⟨w,hinput⟩,?_,?_⟩
      · simpa only [wireVal_input n C x w hinput] using hwx
      · apply wire_or_true n C hAO j hj hop w hw
        rw [wireVal_input n C _ w hinput]
        simp [singletonInput]
    · obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
      have hkj : k<j := by omega
      have hk : k<C.gates.length := by omega
      have hcone : InCone n C k j :=
        (inCone_iff n C k j hj).mpr ⟨n+k,hw,by omega,hwj,Or.inl (by omega)⟩
      obtain ⟨v,hv,hvg⟩ := ih k hkj hk (hanc k hcone)
        (fun i hi => hanc i (inCone_trans n C i k j hj hi hcone)) x hwx
      exact ⟨v,hv,wire_or_true n C hAO j hj hop (n+k) hw _ hvg⟩

lemma earliest_dirty_operand_singleton_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j)
    (hearlier : ∀i<j,(gateAt C i).op=GateOp.and → BelowF G C i)
    (b : Fin 2) (x : Fin n → Bool)
    (hx : wireVal n C (opnd C j b) x=true) :
    ∃v : Fin n,x v=true ∧ wireVal n C (opnd C j b) (singletonInput v)=true := by
  let w := opnd C j b
  have hwj : w<n+j := operand_bound n C hAO j hcone.1 b
  change wireVal n C w x=true at hx
  by_cases hinput : w<n
  · refine ⟨⟨w,hinput⟩,?_,?_⟩
    · simpa only [wireVal_input n C x w hinput] using hx
    · change wireVal n C w (singletonInput ⟨w,hinput⟩)=true
      rw [wireVal_input n C _ w hinput]
      simp [singletonInput]
  · obtain ⟨k,hweq⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by have hj:=hcone.1;omega
    have hwmem : w∈(gateAt C j).inputs := by
      obtain ⟨a,c,hac⟩ := gate_two n C hAO j hcone.1
      fin_cases b <;> simp [w,opnd,hac]
    have hkj : InCone n C k j :=
      (inCone_iff n C k j hcone.1).mpr ⟨w,hwmem,by omega,hwj,Or.inl (by omega)⟩
    have hkOR := earliest_dirty_ancestor_or G C hAO hfixed j hcone hdirty hearlier k hkj
    have hall : ∀i,InCone n C i k → (gateAt C i).op=GateOp.or := by
      intro i hi
      exact earliest_dirty_ancestor_or G C hAO hfixed j hcone hdirty hearlier i
        (inCone_trans n C i k j hcone.1 hi hkj)
    change wireVal n C w x=true at hx
    rw [hweq] at hx
    have hh := or_cone_singleton_witness n C hAO k hk hkOR hall x hx
    simpa only [←hweq] using hh

lemma earliest_dirty_operand_exact_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j)
    (hearlier : ∀i<j,(gateAt C i).op=GateOp.and → BelowF G C i)
    (b : Fin 2) (x : Fin n → Bool) :
    wireVal n C (opnd C j b) x=
      decide (∃v∈singletonSupport n C (opnd C j b),x v=true) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · intro hx
    obtain ⟨v,hv,hvs⟩ := earliest_dirty_operand_singleton_witness G C hAO hfixed j hcone hdirty hearlier b x hx
    exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvs⟩,hv⟩
  · rintro ⟨v,hv,hvx⟩
    have hb := (Finset.mem_filter.mp hv).2
    apply wire_monotone n C hAO (singletonInput v) x _ (opnd C j b)
      ((operand_bound n C hAO j hcone.1 b).trans (Nat.add_lt_add_left hcone.1 n)) hb
    intro i hi
    have he : i=v := by simpa [singletonInput] using hi
    simpa only [he] using hvx


lemma earliest_dirty_support_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j)
    (hearlier : ∀i<j,(gateAt C i).op=GateOp.and → BelowF G C i) (b : Fin 2) :
    (singletonSupport n C (opnd C j b)).Nonempty := by
  have ht := wire_all_true n C hAO (opnd C j b)
    ((operand_bound n C hAO j hcone.1 b).trans (Nat.add_lt_add_left hcone.1 n))
  obtain ⟨v,_,hv⟩ := earliest_dirty_operand_singleton_witness G C hAO hfixed j hcone hdirty hearlier b _ ht
  exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩

lemma earliest_dirty_product {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j)
    (hand : (gateAt C j).op=GateOp.and)
    (hearlier : ∀i<j,(gateAt C i).op=GateOp.and → BelowF G C i) (x : Fin n → Bool) :
    gateVal n C j x=
      (decide (∃u∈singletonSupport n C (opnd C j 0),x u=true) &&
       decide (∃v∈singletonSupport n C (opnd C j 1),x v=true)) := by
  rw [←earliest_dirty_operand_exact_or G C hAO hfixed j hcone hdirty hearlier 0 x,
      ←earliest_dirty_operand_exact_or G C hAO hfixed j hcone hdirty hearlier 1 x]
  obtain ⟨a,b,hab⟩ := gate_two n C hAO j hcone.1
  change wireVal n C (n+j) x=(_ && _)
  rw [wireVal_gate n C x j hcone.1 hAO.2.1,hand,hab]
  simp [GateOp.eval,opnd,hab]

lemma earliest_dirty_nonedge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j)
    (hand : (gateAt C j).op=GateOp.and)
    (hearlier : ∀i<j,(gateAt C i).op=GateOp.and → BelowF G C i) :
    ∃u∈singletonSupport n C (opnd C j 0),
      ∃v∈singletonSupport n C (opnd C j 1),¬G.Adj u v := by
  classical
  by_contra hn
  push_neg at hn
  apply hdirty
  intro x hx
  rw [earliest_dirty_product G C hAO hfixed j hcone hdirty hand hearlier x] at hx
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hx
  obtain ⟨⟨u,hu,hxu⟩,⟨v,hv,hxv⟩⟩ := hx
  simpa [graphFun] using (show ∃u v,G.Adj u v ∧ x u=true ∧ x v=true from
    ⟨u,v,hn u hu v hv,hxu,hxv⟩)

end PEqualNP.Outside.L_meta_3754.Ledger


-- Basic monotone semantics and zero-cut compression adapted from the earlier checked
-- normalization component; its compressor follows the accepted L_meta_5138 construction.
namespace PEqualNP.Outside.L_meta_3754.Semantic

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma gate_eval_monotone (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : ℕ → Bool) (hxy : ∀ i, x i = true → y i = true) :
    g.op.eval (g.inputs.map x) = true → g.op.eval (g.inputs.map y) = true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro h i hi
    exact hxy i (h i hi)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨i,hi,h⟩
    exact ⟨i,hi,hxy i h⟩

lemma val_monotone {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ i, val gs x i = true → val gs y i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    rw [val_nil] at hi ⊢
    split_ifs at hi ⊢ with h
    · exact hxy ⟨i,h⟩ hi
  | append_singleton gs g ih =>
    have hold := ih (fun v hv => hg v (by simp [hv]))
    intro i hi
    rw [val_snoc] at hi ⊢
    split_ifs at hi ⊢ with h
    · exact gate_eval_monotone g (hg g (by simp)) _ _ hold hi
    · exact hold i hi


def zeroGate : Gate := ⟨GateOp.or, []⟩

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false =
      if i = w.length then g.op.eval (g.inputs.map fun j => w.getD j false)
      else w.getD i false := by
  unfold step
  rcases lt_trichotomy i w.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left h]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma step_monotone (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (hle : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (step w g).getD i false = true → (step v g).getD i false = true := by
  intro i hi
  rw [step_getD] at hi ⊢
  rw [← hlen]
  split_ifs at hi ⊢ with h
  · exact gate_eval_monotone g hg _ _ hle hi
  · exact hle i hi

lemma fold_state_monotone (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (hle : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (gs.foldl step w).getD i false = true → (gs.foldl step v).getD i false = true := by
  induction gs generalizing w v with
  | nil => exact hle
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
    · simp [step,hlen]
    · exact step_monotone g (hg g List.mem_cons_self) w v hlen hle

lemma val_append_old {n : ℕ} (pre post : List Gate) (x : Fin n → Bool)
    (i : ℕ) (hi : i < n + pre.length) : val (pre ++ post) x i = val pre x i := by
  induction post using List.reverseRecOn with
  | nil => simp
  | append_singleton post g ih =>
    have hne : i ≠ n + (pre ++ post).length := by
      simp only [List.length_append]
      omega
    rw [← List.append_assoc, val_snoc, ite_eq_right hne]
    exact ih

lemma cut_zero_agrees {n : ℕ} (pre post : List Gate) (g : Gate) (x : Fin n → Bool)
    (hz : val (pre ++ [g] ++ post) x (n + pre.length) = false) :
    ∀ i, val (pre ++ [zeroGate] ++ post) x i = val (pre ++ [g] ++ post) x i := by
  have hp : val (pre ++ [g]) x (n + pre.length) = false := by
    have heq := val_append_old (pre ++ [g]) post x (n + pre.length) (by simp)
    exact heq.symm.trans hz
  rw [val_snoc, ite_eq_left rfl] at hp
  have hs : step (pre.foldl step (List.ofFn x)) zeroGate =
      step (pre.foldl step (List.ofFn x)) g := by
    change g.op.eval (g.inputs.map fun j =>
      (pre.foldl step (List.ofFn x)).getD j false) = false at hp
    exact congrArg (fun b => pre.foldl step (List.ofFn x) ++ [b]) hp.symm
  intro i
  simp only [val, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hs]

lemma cut_zero_below {n : ℕ} (pre post : List Gate) (g : Gate)
    (hpost : ∀ k ∈ post, k.op = GateOp.and ∨ k.op = GateOp.or)
    (x : Fin n → Bool) :
    ∀ i, val (pre ++ [zeroGate] ++ post) x i = true →
      val (pre ++ [g] ++ post) x i = true := by
  simp only [val, List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply fold_state_monotone post hpost
  · simp [step]
  · intro i hi
    rw [step_getD] at hi ⊢
    split_ifs at hi ⊢ with h
    · simp [zeroGate,GateOp.eval] at hi
    · exact hi

end PEqualNP.Outside.L_meta_3754.Semantic

namespace PEqualNP.Outside.L_meta_3754.Compression

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def u (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ) (L : ℕ → List ℕ) (x : List Bool)
    (w : ℕ) : Bool :=
  if w < n then x.getD w false
  else if w - n ∈ Del then false
  else if A (w - n) = true then
    ((if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
      (L (w - n)).any (fun t => x.getD t false)) &&
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
  else
    (if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
termination_by w

section Parameters
variable {n : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ} {x : List Bool}

theorem u_in {w : ℕ} (h : w < n) : u n A a b Del L x w = x.getD w false := by
  rw [u, ite_eq_left h]

theorem u_del {j : ℕ} (h : j ∈ Del) : u n A a b Del L x (n + j) = false := by
  rw [u, ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_left h]

theorem u_and {j : ℕ} (h : j ∉ Del) (hA : A j = true) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = ((u n A a b Del L x (a j) ||
      (L j).any (fun t => x.getD t false)) && u n A a b Del L x (b j)) := by
  rw [u, ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_right h, ite_eq_left hA, dite_eq_left ha, dite_eq_left hb]

theorem u_or {j : ℕ} (h : j ∉ Del) (hA : A j = false) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = (u n A a b Del L x (a j) || u n A a b Del L x (b j)) := by
  rw [u, ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_right h, ite_eq_right (by simp [hA]), dite_eq_left ha,
    dite_eq_left hb]
end Parameters

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

theorem ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
theorem dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

theorem ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

theorem ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (hs : s < n + gs.length) (ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

theorem chain (n : ℕ) (F : (Fin n → Bool) → Bool) : ∀ (l : List ℕ), (∀ t ∈ l, t < n) →
    ∀ (gs : List Gate), Ok n gs → ∀ o : Option ℕ, (∀ w, o = some w → w < n + gs.length) →
    ∃ (hs : List Gate) (o' : Option ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ l.length ∧
      dc n F (gs ++ hs) ≤ dc n F gs ∧ (∀ w, o' = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o' =
        (ov gs (List.ofFn x) o || l.any (fun t => (List.ofFn x).getD t false)) := by
  intro l
  induction l with
  | nil =>
    intro _ gs hgs o ho
    exact ⟨[], o, by simpa using hgs, by simp, by simp, by simpa using ho, by simp⟩
  | cons t l ih =>
    intro hl gs hgs o ho
    have ht : t < n := hl t (by simp)
    have hl' : ∀ t ∈ l, t < n := fun s hs => hl s (by simp [hs])
    cases o with
    | none =>
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' gs hgs (some t) (by
        intro w hw; cases hw; omega)
      refine ⟨hs, o', h1, by simp; omega, h3, h4, fun x => ?_⟩
      rw [h5 x]
      have : ov gs (List.ofFn x) (some t) = (List.ofFn x).getD t false :=
        run_input _ _ _ (by simpa using ht)
      rw [this]; simp [ov]
    | some w =>
      have hw := ho w rfl
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' (gs ++ [⟨GateOp.or, [w, t]⟩])
        (ok_snoc hgs (Or.inr rfl) hw (by omega)) (some (n + gs.length)) (by
          intro w hw; cases hw; simp)
      refine ⟨⟨GateOp.or, [w, t]⟩ :: hs, o', by simpa using h1, by simp; omega, ?_,
        by simpa using h4, fun x => ?_⟩
      · have := dc_snoc n F gs ⟨GateOp.or, [w, t]⟩
        rw [ite_eq_right (by simp)] at this
        have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e]; omega
      · have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e, h5 x, ov_new gs n _ (by simp) _ _ _ hw (by omega)]
        rw [run_input gs (List.ofFn x) t (by simpa using ht)]
        simp [ov, GateOp.eval, Bool.or_assoc]

open Classical in
theorem build (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del R : Finset ℕ) (L : ℕ → List ℕ)
    (F : (Fin n → Bool) → Bool) (hL : ∀ j, ∀ t ∈ L j, t < n)
    (hR : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧ (a j = n + d ∨ b j = n + d)) :
    ∀ p, (∀ j < p, a j < n + j ∧ b j < n + j) →
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n + p, (∀ w', m w = some w' → w' < n + gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) = u n A a b Del L (List.ofFn x) w) ∧
      (∀ d ∈ Del, d < p → m (n + d) = none) ∧
      gs.length + ((Finset.range p).filter (· ∈ Del)).card +
        ((Finset.range p).filter (· ∈ R)).card ≤ p + ∑ j ∈ Finset.range p, (L j).length ∧
      dc n F gs ≤ ((Finset.range p).filter fun j => A j = true ∧ j ∉ Del ∧
        ∃ x : Fin n → Bool, u n A a b Del L (List.ofFn x) (n + j) = true ∧ F x = false).card := by
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨[], fun w => some w, by intro j hj; simp at hj, ?_, by simp, by simp, by simp [dc]⟩
    intro w hw
    refine ⟨by intro w' h; cases h; simpa using hw, fun x => ?_⟩
    rw [u_in (by omega)]; rfl
  | succ p ih =>
    intro hab
    obtain ⟨gs, m, hok, hm, hd, hc, hj⟩ := ih fun j hj => hab j (by omega)
    obtain ⟨hap, hbp⟩ := hab p (by omega)
    suffices hh : ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
        (∀ w, o = some w → w < n + (gs ++ hs).length) ∧ (p ∈ Del → o = none) ∧
        (∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o =
          u n A a b Del L (List.ofFn x) (n + p)) ∧
        hs.length + (if p ∈ Del then 1 else 0) + (if p ∈ R then 1 else 0) ≤ 1 + (L p).length ∧
        dc n F (gs ++ hs) ≤ dc n F gs + if A p = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
          u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5, h6⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hwp : w = n + p
        · subst hwp; rw [Function.update_self]; exact ⟨h2, h4⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨q1, q2⟩ := hm w (by omega)
          refine ⟨fun w' hw' => by have := q1 w' hw'; simp; omega, fun x => ?_⟩
          rw [ov_ext gs hs _ _ (by simpa using q1), q2]
      · intro d hdd hdp
        by_cases hdp' : d = p
        · subst hdp'; rw [Function.update_self]; exact h3 hdd
        · rw [Function.update_of_ne (by omega)]; exact hd d hdd (by omega)
      · rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
          Finset.sum_insert (by simp), List.length_append]
        split_ifs at h5 ⊢ with q1 q2 q2 <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;> omega
      · rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs at h6 ⊢ with q1
        · rw [Finset.card_insert_of_notMem (by simp)]; omega
        · omega
    by_cases hpd : p ∈ Del
    · have hpR : p ∉ R := fun h => (hR p h).2.1 hpd
      refine ⟨[], none, by simpa using hok, by simp, fun _ => rfl, fun x => ?_, ?_, by simp⟩
      · rw [u_del hpd]; rfl
      · rw [ite_eq_left hpd, ite_eq_right hpR]; simp
    obtain ⟨a1, a2⟩ := hm (a p) hap
    obtain ⟨b1, b2⟩ := hm (b p) hbp
    cases hA : A p with
    | false =>
      have hu := fun x : Fin n → Bool => u_or (L := L) (x := List.ofFn x) hpd hA hap hbp
      rcases ha0 : m (a p) with _ | s
      · refine ⟨[], m (b p), by simpa using hok, by simpa using b1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, ha0]; simp [ov]
        · rw [ite_eq_right hpd]; split_ifs <;> simp
      rcases hb0 : m (b p) with _ | t
      · refine ⟨[], m (a p), by simpa using hok, by simpa using a1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, hb0]; simp [ov]
        · rw [ite_eq_right hpd]; split_ifs <;> simp
      have hpR : p ∉ R := by
        intro h
        obtain ⟨_, _, d, hd1, hd2, hd3⟩ := hR p h
        have := hd d hd1 hd2
        rcases hd3 with h | h
        · rw [h, this] at ha0; cases ha0
        · rw [h, this] at hb0; cases hb0
      have hs := a1 s ha0
      have ht := b1 t hb0
      refine ⟨[⟨GateOp.or, [s, t]⟩], some (n + gs.length), ok_snoc hok (Or.inr rfl) hs ht,
        by intro w hw; cases hw; simp, fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [ov_new gs n _ (by simp) _ _ _ hs ht, hu x, ← a2 x, ← b2 x, ha0, hb0]
        simp [ov, GateOp.eval]
      · rw [ite_eq_right hpd, ite_eq_right hpR]; simp
      · have := dc_snoc n F gs ⟨GateOp.or, [s, t]⟩
        rw [ite_eq_right (by simp)] at this
        omega
    | true =>
      have hu := fun x : Fin n → Bool => u_and (L := L) (x := List.ofFn x) hpd hA hap hbp
      have hpR : p ∉ R := fun h => by rw [(hR p h).1] at hA; cases hA
      obtain ⟨hs, o', c1, c2, c3, c4, c5⟩ := chain n F (L p) (hL p) gs hok (m (a p)) a1
      rcases ho : o' with _ | s
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := c5 x
          rw [ho, a2 x] at this
          rw [hu x, ← this]; simp [ov]
        · rw [ite_eq_right hpd, ite_eq_right hpR]; omega
      rcases hb0 : m (b p) with _ | t
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := b2 x
          rw [hb0] at this
          rw [hu x, ← this]; simp [ov]
        · rw [ite_eq_right hpd, ite_eq_right hpR]; omega
      have hs' := c4 s ho
      have ht : t < n + (gs ++ hs).length := by have := b1 t hb0; simp; omega
      have hval : ∀ x : Fin n → Bool, ov (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)
          (some (n + (gs ++ hs).length)) = u n A a b Del L (List.ofFn x) (n + p) := by
        intro x
        rw [ov_new (gs ++ hs) n _ (by simp) _ _ _ hs' ht, hu x, ← a2 x, ← b2 x, ← c5 x, ho, hb0,
          ← ov_ext gs hs (List.ofFn x) (some t) (by intro w hw; cases hw; simpa using b1 t hb0)]
        simp [ov, GateOp.eval]
      refine ⟨hs ++ [⟨GateOp.and, [s, t]⟩], some (n + (gs ++ hs).length), ?_, ?_,
        fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [← List.append_assoc]; exact ok_snoc c1 (Or.inl rfl) hs' ht
      · intro w hw; cases hw; simp
      · rw [← List.append_assoc]; exact hval x
      · rw [ite_eq_right hpd, ite_eq_right hpR]; simp; omega
      · rw [← List.append_assoc]
        have := dc_snoc n F (gs ++ hs) ⟨GateOp.and, [s, t]⟩
        have e : ((⟨GateOp.and, [s, t]⟩ : Gate).op = GateOp.and ∧ ∃ x : Fin n → Bool,
            (run (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)).getD
              (n + (gs ++ hs).length) false = true ∧ F x = false) ↔
            (true = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
              u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false) := by
          refine ⟨fun h => ⟨rfl, hpd, ?_⟩, fun h => ⟨rfl, ?_⟩⟩
          · obtain ⟨x, h1, h2⟩ := h.2
            exact ⟨x, by rw [← hval x]; exact h1, h2⟩
          · obtain ⟨x, h1, h2⟩ := h.2.2
            exact ⟨x, by rw [← hval x] at h1; exact h1, h2⟩
        rw [if_congr e rfl rfl] at this
        omega

lemma compress_zero_program (n N : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ)
    (hab : ∀ j < N, a j < n+j ∧ b j < n+j) :
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n+N, (∀ w', m w = some w' → w' < n+gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
          u n A a b Del (fun _ => []) (List.ofFn x) w) ∧
      gs.length + ((Finset.range N).filter (· ∈ Del)).card ≤ N := by
  obtain ⟨gs,m,hok,hsem,hdel,hsize,hdirty⟩ :=
    build n A a b Del ∅ (fun _ => []) (fun _ => false) (by simp) (by simp) N hab
  refine ⟨gs,m,hok,hsem,?_⟩
  simpa using hsize


lemma u_matches_run (n : ℕ) (gs : List Gate) (A : ℕ → Bool)
    (a b : ℕ → ℕ) (Del : Finset ℕ)
    (hab : ∀ j < gs.length, a j < n+j ∧ b j < n+j)
    (hgate : ∀ j (hj : j < gs.length), gs[j] =
      if j ∈ Del then ⟨GateOp.or, []⟩
      else ⟨if A j then GateOp.and else GateOp.or, [a j,b j]⟩)
    (x : Fin n → Bool) :
    ∀ w < n+gs.length, u n A a b Del (fun _ => []) (List.ofFn x) w =
      (run gs (List.ofFn x)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · rw [u_in hin, run_input gs (List.ofFn x) w (by simpa using hin)]
    have hn : n ≤ w := by omega
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    have hj : j < gs.length := by omega
    obtain ⟨ha,hb⟩ := hab j hj
    have hra : u n A a b Del (fun _ => []) (List.ofFn x) (a j) =
        (run gs (List.ofFn x)).getD (a j) false := ih (a j) ha (by omega)
    have hrb : u n A a b Del (fun _ => []) (List.ofFn x) (b j) =
        (run gs (List.ofFn x)).getD (b j) false := ih (b j) hb (by omega)
    have hr := run_gate gs (List.ofFn x) j hj
    simp only [List.length_ofFn] at hr
    rw [hr,hgate j hj]
    by_cases hd : j ∈ Del
    · rw [u_del hd,ite_eq_left hd]
      rfl
    · rw [ite_eq_right hd]
      cases hA : A j with
      | false =>
        rw [u_or hd hA ha hb,hra,hrb]
        simp [hA,GateOp.eval,ha,hb]
      | true =>
        rw [u_and hd hA ha hb,hra,hrb]
        simp [hA,GateOp.eval,ha,hb]

lemma compress_zero_circuit (n : ℕ) (C : Circuit) (A : ℕ → Bool)
    (a b : ℕ → ℕ) (Del : Finset ℕ)
    (hab : ∀ j < C.gates.length, a j < n+j ∧ b j < n+j)
    (hgate : ∀ j (hj : j < C.gates.length), C.gates[j] =
      if j ∈ Del then ⟨GateOp.or, []⟩
      else ⟨if A j then GateOp.and else GateOp.or, [a j,b j]⟩) :
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n+C.gates.length, (∀ w', m w = some w' → w' < n+gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
          (C.wires (List.ofFn x)).getD w false) ∧
      gs.length + ((Finset.range C.gates.length).filter (· ∈ Del)).card ≤ C.gates.length := by
  obtain ⟨gs,m,hok,hsem,hsize⟩ := compress_zero_program n C.gates.length A a b Del hab
  refine ⟨gs,m,hok,?_,hsize⟩
  intro w hw
  obtain ⟨hbound,hval⟩ := hsem w hw
  refine ⟨hbound,?_⟩
  intro x
  rw [hval,u_matches_run n C.gates A a b Del hab hgate x w hw]
  rfl

theorem ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; exact h2
  · intro j hj i hi
    obtain ⟨o', s', t', h1, h2, h3, h4⟩ := hok j hj
    have e1 : gateAt ⟨gs, w⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e1, h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; rfl

theorem gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩

def zeroCut (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩

lemma compress_one_cut {n : ℕ} (C : Circuit) (hC : TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n+C.gates.length, (∀ w', m w = some w' → w' < n+gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
          ((zeroCut C j).wires (List.ofFn x)).getD w false) ∧
      gs.length+1 ≤ C.gates.length := by
  classical
  let A : ℕ → Bool := fun i => decide ((gateAt C i).op = GateOp.and)
  let a : ℕ → ℕ := fun i => TopForm.opnd C i 0
  let b : ℕ → ℕ := fun i => TopForm.opnd C i 1
  have hab : ∀ i < (zeroCut C j).gates.length, a i < n+i ∧ b i < n+i := by
    intro i hi
    have hi' : i < C.gates.length := by simpa [zeroCut] using hi
    obtain ⟨_,_,ha,hb,_⟩ := gate2 hC hi'
    exact ⟨ha,hb⟩
  have hgate : ∀ i (hi : i < (zeroCut C j).gates.length), (zeroCut C j).gates[i] =
      if i ∈ ({j} : Finset ℕ) then ⟨GateOp.or, []⟩
      else ⟨if A i then GateOp.and else GateOp.or, [a i,b i]⟩ := by
    intro i hi
    have hi' : i < C.gates.length := by simpa [zeroCut] using hi
    obtain ⟨he,hin,ha,hb,hop⟩ := gate2 hC hi'
    by_cases hij : i=j
    · subst i
      simp [zeroCut]
    · simp only [Finset.mem_singleton,ite_eq_right hij]
      have hs : (zeroCut C j).gates[i] = C.gates[i] := by
        simp [zeroCut,List.getElem_set,hij,Ne.symm hij]
      rw [hs,he]
      have hop' : (gateAt C i).op = if A i then GateOp.and else GateOp.or := by
        rcases hop with hop | hop <;> simp [A,hop]
      cases hgc : gateAt C i with
      | mk o ins =>
        simp only [hgc] at hin hop'
        rw [hop',hin]
  obtain ⟨gs,m,hok,hsem,hsize⟩ := compress_zero_circuit n (zeroCut C j) A a b {j} hab hgate
  refine ⟨gs,m,hok,?_,?_⟩
  · simpa [zeroCut] using hsem
  · have hfilter : ((Finset.range (zeroCut C j).gates.length).filter (· ∈ ({j} : Finset ℕ))) = {j} := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · intro hij
        subst i
        exact ⟨by simpa [zeroCut] using hj,rfl⟩
    rw [hfilter,Finset.card_singleton] at hsize
    simpa [zeroCut] using hsize

end PEqualNP.Outside.L_meta_3754.Compression

namespace PEqualNP.Outside.L_meta_3754.Compression

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma zeroCut_decomposition {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j+1) ∧
    (zeroCut C j).gates = C.gates.take j ++ [Semantic.zeroGate] ++ C.gates.drop (j+1) := by
  have hs : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j+1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  refine ⟨hs, ?_⟩
  have ht : (C.gates.take j).length = j := by simp; omega
  unfold zeroCut
  dsimp
  conv_lhs => rw [hs]
  have hz (pre post : List Gate) (g : Gate) :
      (pre ++ [g] ++ post).set pre.length Semantic.zeroGate =
        pre ++ [Semantic.zeroGate] ++ post := by simp [List.set_append]
  simpa only [ht, Semantic.zeroGate] using hz (C.gates.take j) (C.gates.drop (j+1)) C.gates[j]

lemma zeroCut_or_and {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) :
    ∀ g ∈ (zeroCut C j).gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  obtain ⟨hs, hz⟩ := zeroCut_decomposition hj
  rw [hz]
  intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with (hg | rfl) | hg
  · exact hC.1 g (by rw [hs]; exact List.mem_append_left _ (List.mem_append_left _ hg))
  · exact Or.inr rfl
  · exact hC.1 g (by rw [hs]; exact List.mem_append_right _ hg)

lemma zeroCut_le {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    ∀ w, ((zeroCut C j).wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn x)).getD w false = true := by
  obtain ⟨hs, hz⟩ := zeroCut_decomposition hj
  change ∀ w, Semantic.val (zeroCut C j).gates x w = true → Semantic.val C.gates x w = true
  rw [hs,hz]
  apply Semantic.cut_zero_below
  intro g hg
  exact hC.1 g (by rw [hs]; exact List.mem_append_right _ hg)

lemma graph_eq_of_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hle : ∀ x, f x = true → graphFun G ∅ x = true)
    (hedge : ∀ u v, G.Adj u v → f (pairInput u v) = true) :
    f = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hle x
  · intro hx
    simp [graphFun] at hx
    obtain ⟨u,v,huv,hxu,hxv⟩ := hx
    apply hmono (pairInput u v) x ?_ (hedge u v huv)
    intro i hi
    simp only [pairInput, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl <;> assumption

lemma zeroCut_smaller {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hout : C.output < n+C.gates.length) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      circuitFun n D = circuitFun n (zeroCut C j) := by
  obtain ⟨gs,m,hok,hsem,hsize⟩ := compress_one_cut C hC j hj
  cases he : m C.output with
  | none =>
    refine ⟨⟨gs,n+gs.length⟩,ok_ao hok,by simpa [Circuit.size] using hsize,?_⟩
    funext x
    have hv := (hsem C.output hout).2 x
    rw [he] at hv
    change false = circuitFun n (zeroCut C j) x at hv
    change (run gs (List.ofFn x)).getD (n+gs.length) false = _
    rw [List.getD_eq_default _ _ (by simp [run_length])]
    exact hv
  | some w =>
    refine ⟨⟨gs,w⟩,ok_ao hok,by simpa [Circuit.size] using hsize,?_⟩
    funext x
    have hv := (hsem C.output hout).2 x
    rw [he] at hv
    exact hv

lemma least_gate_critical_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output < n+C.gates.length) :
    ∃ u v : Fin n, G.Adj u v ∧ circuitFun n (zeroCut C j) (pairInput u v) = false := by
  classical
  by_contra h
  have he : ∀ u v, G.Adj u v → circuitFun n (zeroCut C j) (pairInput u v) = true := by
    intro u v huv
    cases hv : circuitFun n (zeroCut C j) (pairInput u v)
    · exact False.elim (h ⟨u,v,huv,hv⟩)
    · rfl
  have hc : circuitFun n (zeroCut C j) = graphFun G ∅ := by
    apply graph_eq_of_edges G _ ?_ ?_ he
    · intro x y hxy
      exact Semantic.val_monotone (zeroCut C j).gates (zeroCut_or_and hC.1 hj) x y hxy C.output
    · intro x hx
      rw [← hC.2.1]
      exact zeroCut_le hC.1 hj x C.output hx
  obtain ⟨D,hD,hs,hf⟩ := zeroCut_smaller C hC.1 j hj hout
  have hm := hC.2.2 D hD (hf.trans hc)
  omega

lemma least_nonempty_output_valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hj : 0 < C.gates.length) :
    C.output < n + C.gates.length := by
  by_contra hout
  have hzero : IsAO2 n (⟨[],n⟩ : Circuit) := by
    refine ⟨?_,?_,?_⟩
    · intro g hg; cases hg
    · intro j hj; simp at hj
    · intro g hg; cases hg
  have heq : circuitFun n (⟨[],n⟩ : Circuit) = graphFun G ∅ := by
    rw [← hC.2.1]
    funext x
    change (List.ofFn x).getD n false = (run C.gates (List.ofFn x)).getD C.output false
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp [run_length]; omega)]
  have hb := hC.2.2 ⟨[],n⟩ hzero heq
  change C.gates.length ≤ 0 at hb
  omega

lemma zeroCut_agrees_if_false {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin n → Bool) (hg : gateVal n C j x = false) :
    ∀ w, ((zeroCut C j).wires (List.ofFn x)).getD w false =
      (C.wires (List.ofFn x)).getD w false := by
  obtain ⟨hs,hz⟩ := zeroCut_decomposition hj
  change Semantic.val C.gates x (n+j) = false at hg
  have ht : (C.gates.take j).length = j := by simp; omega
  have ha : Semantic.val (C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j+1)) x
      (n+(C.gates.take j).length) = false := by
    simpa only [ht,←hs] using hg
  have hc := Semantic.cut_zero_agrees (C.gates.take j) (C.gates.drop (j+1)) C.gates[j] x ha
  intro w
  change Semantic.val (zeroCut C j).gates x w = Semantic.val C.gates x w
  rw [hs,hz]
  exact hc w

lemma least_gate_edge_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ u v : Fin n, G.Adj u v ∧ gateVal n C j (pairInput u v) = true ∧
      circuitFun n (zeroCut C j) (pairInput u v) = false := by
  obtain ⟨u,v,huv,hcut⟩ := least_gate_critical_edge G C hC j hj
    (least_nonempty_output_valid G C hC (by omega))
  refine ⟨u,v,huv,?_,hcut⟩
  cases hv : gateVal n C j (pairInput u v)
  · have ha := zeroCut_agrees_if_false C j hj (pairInput u v) hv C.output
    change circuitFun n (zeroCut C j) (pairInput u v) = circuitFun n C (pairInput u v) at ha
    rw [hcut,hC.2.1] at ha
    have ht : graphFun G ∅ (pairInput u v) = true := by
      have hh : ∃ a b, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true :=
        ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩
      simpa [graphFun] using hh
    rw [ht] at ha
    cases ha
  · rfl

end PEqualNP.Outside.L_meta_3754.Compression

namespace PEqualNP.Outside.L_meta_3754.RawAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma raw_and_value {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (a b : Fin n) (hin : (gateAt C j).inputs = [a.val,b.val]) (x : Fin n → Bool) :
    gateVal n C j x = (x a && x b) := by
  change wireVal n C (n+j) x = _
  rw [Ledger.wireVal_gate n C x j hj hAO.2.1,hop,hin]
  simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,Bool.and_true]
  rw [Ledger.wireVal_input n C x a.val a.isLt,Ledger.wireVal_input n C x b.val b.isLt]
  rfl

lemma least_raw_and_distinct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (a b : Fin n)
    (hin : (gateAt C j).inputs = [a.val,b.val]) : a ≠ b := by
  intro hab
  subst b
  apply Bypass.least_no_equal_earlier hC hj (i := a.val) (by have := a.isLt;omega)
  intro x
  change gateVal n C j x = wireVal n C a.val x
  rw [raw_and_value C hC.1 j hj hop a a hin x,Ledger.wireVal_input n C x a.val a.isLt]
  simp

lemma least_raw_and_below_of_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (a b : Fin n)
    (hin : (gateAt C j).inputs = [a.val,b.val])
    (hcritical : ∃u v : Fin n,G.Adj u v ∧ gateVal n C j (pairInput u v)=true) :
    BelowF G C j := by
  have hab := least_raw_and_distinct G C hC j hj hop a b hin
  obtain ⟨u,v,huv,hjv⟩ := hcritical
  rw [raw_and_value C hC.1 j hj hop a b hin] at hjv
  have hv : pairInput u v a=true ∧ pairInput u v b=true := by simpa only [Bool.and_eq_true] using hjv
  have ha : a=u ∨ a=v := by simpa [pairInput] using hv.1
  have hb : b=u ∨ b=v := by simpa [pairInput] using hv.2
  have hadj : G.Adj a b := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact huv
    · exact huv.symm
    · exact (hab rfl).elim
  intro x hx
  rw [raw_and_value C hC.1 j hj hop a b hin] at hx
  have hx' : x a=true ∧ x b=true := by simpa only [Bool.and_eq_true] using hx
  simpa [graphFun] using (show ∃u v,G.Adj u v ∧ x u=true ∧ x v=true from
    ⟨a,b,hadj,hx'.1,hx'.2⟩)

lemma least_raw_and_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (a b : Fin n)
    (hin : (gateAt C j).inputs = [a.val,b.val]) : BelowF G C j := by
  obtain ⟨u,v,huv,hjv,_⟩ := Compression.least_gate_edge_witness G C hC j hj
  exact least_raw_and_below_of_edge G C hC j hj hop a b hin ⟨u,v,huv,hjv⟩

end PEqualNP.Outside.L_meta_3754.RawAnd
