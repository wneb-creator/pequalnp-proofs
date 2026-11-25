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


lemma or_subset_absorption {n : ℕ} (A B : Finset (Fin n)) (hAB : A⊆B) (x : Fin n → Bool) :
    (decide (∃u∈A,x u=true) && decide (∃v∈B,x v=true))=decide (∃u∈A,x u=true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · exact And.left
  · rintro ⟨u,hu,hxu⟩
    exact ⟨⟨u,hu,hxu⟩,⟨u,hAB hu,hxu⟩⟩

lemma earliest_dirty_incomparable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j : ℕ) (hcone : PEqualNP.Core.InOutputCone n C j) (hdirty : ¬BelowF G C j)
    (hand : (gateAt C j).op=GateOp.and)
    (hearlier : ∀i<j,(gateAt C i).op=GateOp.and → BelowF G C i)
    (hnoequal : ∀w<n+j,¬∀x : Fin n → Bool,gateVal n C j x=wireVal n C w x) :
    ¬singletonSupport n C (opnd C j 0)⊆singletonSupport n C (opnd C j 1) ∧
    ¬singletonSupport n C (opnd C j 1)⊆singletonSupport n C (opnd C j 0) := by
  constructor
  · intro hs
    apply hnoequal _ (operand_bound n C hAO j hcone.1 0)
    intro x
    rw [earliest_dirty_product G C hAO hfixed j hcone hdirty hand hearlier x,
      earliest_dirty_operand_exact_or G C hAO hfixed j hcone hdirty hearlier 0 x]
    exact or_subset_absorption _ _ hs x
  · intro hs
    apply hnoequal _ (operand_bound n C hAO j hcone.1 1)
    intro x
    rw [earliest_dirty_product G C hAO hfixed j hcone hdirty hand hearlier x,
      earliest_dirty_operand_exact_or G C hAO hfixed j hcone hdirty hearlier 1 x,Bool.and_comm]
    exact or_subset_absorption _ _ hs x

end PEqualNP.Outside.L_meta_3754.Ledger

namespace PEqualNP.Outside.L_meta_3754.Select
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma or_cone_forward (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∀k,k<C.gates.length → (gateAt C k).op=GateOp.or →
      (∀i,InCone n C i k → (gateAt C i).op=GateOp.or) →
      ∀j,(j=k ∨ InCone n C j k) → ∀x : Fin n → Bool,
      wireVal n C (n+j) x=true → wireVal n C (n+k) x=true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hop hall j hreach x hx
    rcases hreach with rfl | hreach
    · exact hx
    obtain ⟨w,hw,hnw,hwk,hj⟩ := (Ledger.inCone_iff n C j k hk).mp hreach
    have ht : w-n<k := by omega
    have htk : InCone n C (w-n) k :=
      (Ledger.inCone_iff n C (w-n) k hk).mpr ⟨w,hw,hnw,hwk,Or.inl rfl⟩
    have hv := ih (w-n) ht (by omega) (hall _ htk)
      (fun i hi => hall i (Ledger.inCone_trans n C i (w-n) k hk hi htk)) j hj x hx
    apply Ledger.wire_or_true n C hAO k hk hop w hw x
    simpa only [show n+(w-n)=w by omega] using hv

lemma singleton_raw_reader (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (v : Fin n) :
    ∀k,k<C.gates.length → (gateAt C k).op=GateOp.or →
      (∀i,InCone n C i k → (gateAt C i).op=GateOp.or) →
      wireVal n C (n+k) (Ledger.singletonInput v)=true →
      ∃j,j≤k ∧ (j=k ∨ InCone n C j k) ∧ (gateAt C j).op=GateOp.or ∧
        v.val∈(gateAt C j).inputs := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hop hall hx
    rw [Ledger.wireVal_gate n C _ k hk hAO.2.1,hop] at hx
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at hx
    obtain ⟨w,hw,hwv⟩ := hx
    have hwk := hAO.2.1 k hk w hw
    by_cases hwn : w<n
    · have he : (⟨w,hwn⟩ : Fin n)=v := by
        simpa [Ledger.wireVal_input n C _ w hwn,Ledger.singletonInput] using hwv
      have heval : w=v.val := congrArg Fin.val he
      exact ⟨k,le_refl _,Or.inl rfl,hop,heval ▸ hw⟩
    · have hnk : n≤w := by omega
      have ht : w-n<k := by omega
      have htk : InCone n C (w-n) k :=
        (Ledger.inCone_iff n C (w-n) k hk).mpr ⟨w,hw,hnk,hwk,Or.inl rfl⟩
      have hwv' : wireVal n C (n+(w-n)) (Ledger.singletonInput v)=true := by
        simpa only [show n+(w-n)=w by omega] using hwv
      obtain ⟨j,hj,hreach,hjor,hjv⟩ := ih (w-n) ht (by omega) (hall _ htk)
        (fun i hi => hall i (Ledger.inCone_trans n C i (w-n) k hk hi htk)) hwv'
      refine ⟨j,by omega,Or.inr ?_,hjor,hjv⟩
      rcases hreach with rfl | hreach
      · exact htk
      · exact Ledger.inCone_trans n C j (w-n) k hk hreach htk

lemma direct_other (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) (v : Fin n) (hv : v.val∈(gateAt C j).inputs) :
    ∃p,p<n+j ∧ ((gateAt C j).inputs=[v.val,p] ∨ (gateAt C j).inputs=[p,v.val]) := by
  obtain ⟨a,b,hab⟩ := Ledger.gate_two n C hAO j hj
  have hva : v.val=a ∨ v.val=b := by simpa [hab] using hv
  rcases hva with h | h
  · refine ⟨b,hAO.2.1 j hj b (by simp [hab]),Or.inl ?_⟩
    simpa only [h] using hab
  · refine ⟨a,hAO.2.1 j hj a (by simp [hab]),Or.inr ?_⟩
    simpa only [h] using hab

lemma direct_or_value (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) (hop : (gateAt C j).op=GateOp.or) (v : Fin n) (p : ℕ)
    (hin : (gateAt C j).inputs=[v.val,p] ∨ (gateAt C j).inputs=[p,v.val]) (x : Fin n → Bool) :
    wireVal n C (n+j) x=(x v || wireVal n C p x) := by
  rw [Ledger.wireVal_gate n C x j hj hAO.2.1,hop]
  rcases hin with hin | hin
  · simp [hin,GateOp.eval,Ledger.wireVal_input n C x v.val v.isLt]
  · simp [hin,GateOp.eval,Ledger.wireVal_input n C x v.val v.isLt,Bool.or_comm]

lemma direct_other_excludes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (j : ℕ) (hj : j<C.gates.length)
    (hop : (gateAt C j).op=GateOp.or) (v : Fin n) (p : ℕ) (hp : p<n+j)
    (hin : (gateAt C j).inputs=[v.val,p] ∨ (gateAt C j).inputs=[p,v.val]) :
    wireVal n C p (Ledger.singletonInput v)=false := by
  cases hv : wireVal n C p (Ledger.singletonInput v)
  · rfl
  · exfalso
    apply Bypass.least_no_equal_earlier hC hj hp
    intro x
    change wireVal n C (n+j) x=wireVal n C p x
    rw [direct_or_value n C hC.1 j hj hop v p hin x]
    have hsub : x v=true → wireVal n C p x=true := by
      intro hx
      apply Ledger.wire_monotone n C hC.1 (Ledger.singletonInput v) x _ p (by omega) hv
      intro i hi
      have he : i=v := by simpa [Ledger.singletonInput] using hi
      simpa only [he] using hx
    cases hx : x v <;> cases hpx : wireVal n C p x <;> simp_all

lemma or_operand_witness (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) (hall : ∀i,InCone n C i j → (gateAt C i).op=GateOp.or)
    (p : ℕ) (hpm : p∈(gateAt C j).inputs) (x : Fin n → Bool) (hpx : wireVal n C p x=true) :
    ∃u : Fin n,x u=true ∧ wireVal n C p (Ledger.singletonInput u)=true := by
  have hpj := hAO.2.1 j hj p hpm
  by_cases hpn : p<n
  · refine ⟨⟨p,hpn⟩,?_,?_⟩
    · simpa only [Ledger.wireVal_input n C x p hpn] using hpx
    · rw [Ledger.wireVal_input n C _ p hpn]
      simp [Ledger.singletonInput]
  · have hnp : n≤p := by omega
    have hpk : p-n<j := by omega
    have hpc : InCone n C (p-n) j :=
      (Ledger.inCone_iff n C (p-n) j hj).mpr ⟨p,hpm,hnp,hpj,Or.inl rfl⟩
    have hpx' : wireVal n C (n+(p-n)) x=true := by simpa only [show n+(p-n)=p by omega] using hpx
    obtain ⟨u,hu,hup⟩ := Ledger.or_cone_singleton_witness n C hAO (p-n) (by omega) (hall _ hpc)
      (fun i hi => hall i (Ledger.inCone_trans n C i (p-n) j hj hi hpc)) x hpx'
    exact ⟨u,hu,by simpa only [show n+(p-n)=p by omega] using hup⟩

lemma select_in_or_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (k : ℕ) (hk : k<C.gates.length)
    (hop : (gateAt C k).op=GateOp.or)
    (hall : ∀i,InCone n C i k → (gateAt C i).op=GateOp.or)
    (v : Fin n) (hv : v∈Ledger.singletonSupport n C (n+k)) :
    ∃ (j p : ℕ) (u : Fin n),j≤k ∧ (j=k ∨ InCone n C j k) ∧
      (gateAt C j).op=GateOp.or ∧ p<n+j ∧
      ((gateAt C j).inputs=[v.val,p] ∨ (gateAt C j).inputs=[p,v.val]) ∧
      wireVal n C p (Ledger.singletonInput v)=false ∧ u≠v ∧
      wireVal n C p (Ledger.singletonInput u)=true ∧
      u∈Ledger.singletonSupport n C (n+k) ∧
      wireVal n C (n+j) (Ledger.singletonInput v)=true ∧
      wireVal n C (n+j) (Ledger.singletonInput u)=true := by
  obtain ⟨j,hjk,hreach,hjor,hjv⟩ := singleton_raw_reader n C hC.1 v k hk hop hall
    (Finset.mem_filter.mp hv).2
  have hj : j<C.gates.length := by omega
  obtain ⟨p,hp,hin⟩ := direct_other n C hC.1 j hj v hjv
  have hpfalse := direct_other_excludes G C hC j hj hjor v p hp hin
  have hpm : p∈(gateAt C j).inputs := by rcases hin with hin | hin <;> simp [hin]
  have hjall : ∀i,InCone n C i j → (gateAt C i).op=GateOp.or := by
    intro i hi
    rcases hreach with rfl | hreach
    · exact hall i hi
    · exact hall i (Ledger.inCone_trans n C i j k hk hi hreach)
  obtain ⟨u,_,hpu⟩ := or_operand_witness n C hC.1 j hj hjall p hpm (fun _ => true)
    (Ledger.wire_all_true n C hC.1 p (by omega))
  have huv : u≠v := by intro he;subst u;rw [hpfalse] at hpu;cases hpu
  have hjut : wireVal n C (n+j) (Ledger.singletonInput u)=true := by
    rw [direct_or_value n C hC.1 j hj hjor v p hin]
    simp [hpu]
  have hju : u∈Ledger.singletonSupport n C (n+k) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,or_cone_forward n C hC.1 k hk hop hall j hreach _ hjut⟩
  refine ⟨j,p,u,hjk,hreach,hjor,hp,hin,hpfalse,huv,hpu,hju,?_,hjut⟩
  rw [direct_or_value n C hC.1 j hj hjor v p hin]
  simp [Ledger.singletonInput]

lemma selected_outside_second {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (a b j p : ℕ) (hb : b<C.gates.length) (hbor : (gateAt C b).op=GateOp.or)
    (hbanc : ∀i,InCone n C i b → (gateAt C i).op=GateOp.or)
    (v u : Fin n) (huv : u≠v)
    (hinter : Ledger.singletonSupport n C a ∩ Ledger.singletonSupport n C (n+b)={v})
    (huA : u∈Ledger.singletonSupport n C a)
    (hpv : wireVal n C p (Ledger.singletonInput v)=false)
    (hju : wireVal n C (n+j) (Ledger.singletonInput u)=true) :
    j≠b ∧ ¬InCone n C j b ∧ p≠n+b := by
  have huB : u∉Ledger.singletonSupport n C (n+b) := by
    intro huB
    have hu : u∈({v} : Finset (Fin n)) := hinter ▸ Finset.mem_inter.mpr ⟨huA,huB⟩
    exact huv (Finset.mem_singleton.mp hu)
  have hnreach : ¬(j=b ∨ InCone n C j b) := by
    intro hreach
    apply huB
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      or_cone_forward n C hAO b hb hbor hbanc j hreach _ hju⟩
  have hvB : v∈Ledger.singletonSupport n C (n+b) := by
    have hv : v∈Ledger.singletonSupport n C a ∩ Ledger.singletonSupport n C (n+b) := by
      rw [hinter];simp
    exact (Finset.mem_inter.mp hv).2
  refine ⟨fun h => hnreach (Or.inl h),fun h => hnreach (Or.inr h),?_⟩
  intro hp
  subst p
  have hv := (Finset.mem_filter.mp hvB).2
  rw [hpv] at hv
  cases hv

lemma raw_support (n : ℕ) (C : Circuit) (w : ℕ) (hw : w<n) :
    Ledger.singletonSupport n C w={⟨w,hw⟩} := by
  ext u
  simp [Ledger.singletonSupport,Ledger.wireVal_input n C _ w hw,Ledger.singletonInput,eq_comm]

lemma select_pure_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (g : ℕ) (hg : g<C.gates.length)
    (hall : ∀i,InCone n C i g → (gateAt C i).op=GateOp.or)
    (a : ℕ) (ham : a∈(gateAt C g).inputs)
    (hcard : 2≤(Ledger.singletonSupport n C a).card)
    (v : Fin n) (hv : v∈Ledger.singletonSupport n C a) :
    ∃ (j p : ℕ) (u : Fin n),j<g ∧ InCone n C j g ∧
      (gateAt C j).op=GateOp.or ∧ p<n+j ∧
      ((gateAt C j).inputs=[v.val,p] ∨ (gateAt C j).inputs=[p,v.val]) ∧
      wireVal n C p (Ledger.singletonInput v)=false ∧ u≠v ∧
      wireVal n C p (Ledger.singletonInput u)=true ∧
      u∈Ledger.singletonSupport n C a ∧
      wireVal n C (n+j) (Ledger.singletonInput v)=true ∧
      wireVal n C (n+j) (Ledger.singletonInput u)=true := by
  have hag := hC.1.2.1 g hg a ham
  have hna : n≤a := by
    by_contra hn
    have han : a<n := by omega
    rw [raw_support n C a han,Finset.card_singleton] at hcard
    omega
  let k := a-n
  have hka : n+k=a := by dsimp [k];omega
  have hkg : k<g := by dsimp [k];omega
  have hk : k<C.gates.length := by omega
  have hkcone : InCone n C k g :=
    (Ledger.inCone_iff n C k g hg).mpr ⟨a,ham,hna,hag,Or.inl rfl⟩
  have hkor := hall k hkcone
  have hkall : ∀i,InCone n C i k → (gateAt C i).op=GateOp.or := by
    intro i hi
    exact hall i (Ledger.inCone_trans n C i k g hg hi hkcone)
  obtain ⟨j,p,u,hjk,hreach,hjor,hp,hin,hpv,huv,hpu,huA,hjv,hju⟩ :=
    select_in_or_gate G C hC k hk hkor hkall v (by simpa only [hka] using hv)
  have hjg : InCone n C j g := by
    rcases hreach with rfl | hreach
    · exact hkcone
    · exact Ledger.inCone_trans n C j k g hg hreach hkcone
  exact ⟨j,p,u,by omega,hjg,hjor,hp,hin,hpv,huv,hpu,by simpa only [hka] using huA,hjv,hju⟩

end PEqualNP.Outside.L_meta_3754.Select
