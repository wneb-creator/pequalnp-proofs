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


lemma graph_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v)=true ↔ G.Adj u v := by
  have hf : graphFun G ∅ (pairInput u v)=true ↔
      ∃a b,G.Adj a b ∧ pairInput u v a=true ∧ pairInput u v b=true := by simp [graphFun]
  rw [hf]
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    simp only [pairInput,decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim
  · intro huv
    exact ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩

lemma gate_and_value (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) (hand : (gateAt C j).op=GateOp.and) (x : Fin n → Bool) :
    gateVal n C j x=(wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  obtain ⟨a,b,hab⟩ := gate_two n C hAO j hj
  change wireVal n C (n+j) x=(_ && _)
  rw [wireVal_gate n C x j hj hAO.2.1,hand,hab]
  simp [GateOp.eval,opnd,hab]

lemma and_support_cross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j<C.gates.length)
    (hand : (gateAt C j).op=GateOp.and) (hbelow : BelowF G C j)
    (u v : Fin n) (hu : u∈singletonSupport n C (opnd C j 0))
    (hv : v∈singletonSupport n C (opnd C j 1)) : G.Adj u v := by
  apply (graph_pair_iff G u v).mp
  apply hbelow
  rw [gate_and_value n C hAO j hj hand]
  simp only [Bool.and_eq_true]
  constructor
  · apply wire_monotone n C hAO (singletonInput u) (pairInput u v) _ (opnd C j 0)
      ((operand_bound n C hAO j hj 0).trans (Nat.add_lt_add_left hj n)) (Finset.mem_filter.mp hu).2
    intro i hi
    have he : i=u := by simpa [singletonInput] using hi
    simp [pairInput,he]
  · apply wire_monotone n C hAO (singletonInput v) (pairInput u v) _ (opnd C j 1)
      ((operand_bound n C hAO j hj 1).trans (Nat.add_lt_add_left hj n)) (Finset.mem_filter.mp hv).2
    intro i hi
    have he : i=v := by simpa [singletonInput] using hi
    simp [pairInput,he]

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcycle : NoFourCycle G) (u v m z : Fin n) (huv : u≠v)
    (hum : G.Adj u m) (hvm : G.Adj v m) (huz : G.Adj u z) (hvz : G.Adj v z) : z=m := by
  apply (Finset.card_le_one.mp (hcycle u v huv))
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,huz,hvz⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hum,hvm⟩

lemma support_center_rigid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcycle : NoFourCycle G) (L R : Finset (Fin n))
    (hcross : ∀u∈L,∀v∈R,G.Adj u v) (u v m : Fin n)
    (hu : u∈L) (hv : v∈L) (huv : u≠v) (hum : G.Adj u m) (hvm : G.Adj v m)
    (hR : R.Nonempty) : R={m} := by
  have hz : ∀z∈R,z=m := by
    intro z hz
    exact common_neighbor_unique G hcycle u v m z huv hum hvm (hcross u hu z hz) (hcross v hv z hz)
  obtain ⟨z,hzmem⟩ := hR
  have hm : m∈R := (hz z hzmem) ▸ hzmem
  ext w
  simp only [Finset.mem_singleton]
  exact ⟨hz w,fun hw => hw ▸ hm⟩

lemma and_center_rigid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcycle : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j<C.gates.length) (hand : (gateAt C j).op=GateOp.and) (hbelow : BelowF G C j)
    (u v m : Fin n) (hu : u∈singletonSupport n C (opnd C j 0))
    (hv : v∈singletonSupport n C (opnd C j 0)) (huv : u≠v)
    (hum : G.Adj u m) (hvm : G.Adj v m)
    (hR : (singletonSupport n C (opnd C j 1)).Nonempty) :
    singletonSupport n C (opnd C j 1)={m} := by
  exact support_center_rigid G hcycle _ _
    (fun a ha b hb => and_support_cross G C hAO j hj hand hbelow a b ha hb)
    u v m hu hv huv hum hvm hR

lemma adjacent_neighborhoods_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcolor : ∀u v,G.Adj u v → s u≠s v)
    (u v : Fin n) (huv : G.Adj u v) :
    Disjoint (Finset.univ.filter fun w => G.Adj u w) (Finset.univ.filter fun w => G.Adj v w) := by
  apply Finset.disjoint_left.mpr
  intro w hwu hwv
  have hu := hcolor u w (Finset.mem_filter.mp hwu).2
  have hv := hcolor v w (Finset.mem_filter.mp hwv).2
  have huv' := hcolor u v huv
  cases hsu : s u <;> cases hsv : s v <;> cases hsw : s w <;> simp_all

lemma cross_support_disjoint_neighborhood {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcolor : ∀u v,G.Adj u v → s u≠s v)
    (L R A : Finset (Fin n)) (hcross : ∀u∈L,∀v∈R,G.Adj u v)
    (v m : Fin n) (hv : v∈L) (hvm : G.Adj v m) (hA : ∀a∈A,G.Adj m a) :
    Disjoint R A := by
  apply Finset.disjoint_left.mpr
  intro z hz hza
  exact (Finset.disjoint_left.mp (adjacent_neighborhoods_disjoint G s hcolor v m hvm))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcross v hv z hz⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hA z hza⟩)


lemma and_center_exact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcycle : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j<C.gates.length) (hand : (gateAt C j).op=GateOp.and) (hbelow : BelowF G C j)
    (u v m : Fin n) (hu : u∈singletonSupport n C (opnd C j 0))
    (hv : v∈singletonSupport n C (opnd C j 0)) (huv : u≠v)
    (hum : G.Adj u m) (hvm : G.Adj v m)
    (hpure : ∀x : Fin n → Bool,wireVal n C (opnd C j 1) x=
      decide (∃z∈singletonSupport n C (opnd C j 1),x z=true)) :
    ∀x : Fin n → Bool,wireVal n C (opnd C j 1) x=x m := by
  have hR : (singletonSupport n C (opnd C j 1)).Nonempty := by
    have ht := wire_all_true n C hAO (opnd C j 1)
      ((operand_bound n C hAO j hj 1).trans (Nat.add_lt_add_left hj n))
    rw [hpure] at ht
    simp only [decide_eq_true_eq] at ht
    obtain ⟨z,hz,_⟩ := ht
    exact ⟨z,hz⟩
  have he := and_center_rigid G hcycle C hAO j hj hand hbelow u v m hu hv huv hum hvm hR
  intro x
  rw [hpure,he]
  simp


lemma singleton_witness_exact_or (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (w : ℕ)
    (hw : w<n+C.gates.length)
    (hwit : ∀x : Fin n → Bool,wireVal n C w x=true →
      ∃v : Fin n,x v=true ∧ wireVal n C w (singletonInput v)=true) :
    ∀x : Fin n → Bool,wireVal n C w x=decide (∃v∈singletonSupport n C w,x v=true) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · intro hx
    obtain ⟨v,hv,hvs⟩ := hwit x hx
    exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvs⟩,hv⟩
  · rintro ⟨v,hv,hvx⟩
    apply wire_monotone n C hAO (singletonInput v) x _ w hw (Finset.mem_filter.mp hv).2
    intro i hi
    have he : i=v := by simpa [singletonInput] using hi
    simpa only [he] using hvx

lemma ancestor_truth_if_and_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (top : ℕ) (htop : top<C.gates.length) (p : Fin n → Bool)
    (hall : ∀i,InCone n C i top → (gateAt C i).op=GateOp.and → gateVal n C i p=true) :
    ∀j,InCone n C j top → ∀i,gateVal n C i p=true →
      (i=j ∨ InCone n C i j) → gateVal n C j p=true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hjtop i hiv hij
    rcases hij with rfl | hij
    · exact hiv
    have hj := (inCone_lt n C j top htop hjtop).trans htop
    have hm : gateAt C j∈C.gates := by rw [gateAt_eq_getElem C j hj];exact List.getElem_mem hj
    rcases hAO.1 _ hm with hand | hor
    · exact hall j hjtop hand
    · obtain ⟨w,hw,hnw,hwj,hic⟩ := (inCone_iff n C i j hj).mp hij
      have hk : InCone n C (w-n) j :=
        (inCone_iff n C (w-n) j hj).mpr ⟨w,hw,hnw,hwj,Or.inl rfl⟩
      have hkTop := inCone_trans n C (w-n) j top htop hk hjtop
      have hval := ih (w-n) (by omega) hkTop i hiv hic
      apply wire_or_true n C hAO j hj hor w hw
      have he : n+(w-n)=w := by omega
      simpa only [gateVal,wireVal,he] using hval

lemma false_operand_exact_or (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (top : ℕ) (htop : top<C.gates.length) (p : Fin n → Bool)
    (hall : ∀i,InCone n C i top → (gateAt C i).op=GateOp.and → gateVal n C i p=true)
    (b : Fin 2) (hfalse : wireVal n C (opnd C top b) p=false) :
    ∀x : Fin n → Bool,wireVal n C (opnd C top b) x=
      decide (∃v∈singletonSupport n C (opnd C top b),x v=true) := by
  let w := opnd C top b
  have hw : w<n+top := operand_bound n C hAO top htop b
  apply singleton_witness_exact_or n C hAO w (hw.trans (Nat.add_lt_add_left htop n))
  intro x hx
  by_cases hinput : w<n
  · refine ⟨⟨w,hinput⟩,?_,?_⟩
    · simpa only [wireVal_input n C x w hinput] using hx
    · rw [wireVal_input n C _ w hinput]
      simp [singletonInput]
  · obtain ⟨k,hweq⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by omega
    have hwmem : w∈(gateAt C top).inputs := by
      obtain ⟨a,c,hac⟩ := gate_two n C hAO top htop
      fin_cases b <;> simp [w,opnd,hac]
    have hkTop : InCone n C k top :=
      (inCone_iff n C k top htop).mpr ⟨w,hwmem,by omega,hw,Or.inl (by omega)⟩
    have hkFalse : gateVal n C k p=false := by
      change wireVal n C w p=false at hfalse
      simpa only [hweq,gateVal,wireVal] using hfalse
    have hkOR : (gateAt C k).op=GateOp.or := by
      have hkm : gateAt C k∈C.gates := by rw [gateAt_eq_getElem C k hk];exact List.getElem_mem hk
      rcases hAO.1 _ hkm with hand | hor
      · have ht := hall k hkTop hand
        rw [hkFalse] at ht
        cases ht
      · exact hor
    have hanc : ∀i,InCone n C i k → (gateAt C i).op=GateOp.or := by
      intro i hi
      have hil := (inCone_lt n C i k hk hi).trans hk
      have him : gateAt C i∈C.gates := by rw [gateAt_eq_getElem C i hil];exact List.getElem_mem hil
      rcases hAO.1 _ him with hand | hor
      · have hiTop := inCone_trans n C i k top htop hi hkTop
        have ht := ancestor_truth_if_and_true n C hAO top htop p hall k hkTop i
          (hall i hiTop hand) (Or.inr hi)
        rw [hkFalse] at ht
        cases ht
      · exact hor
    rw [hweq] at hx ⊢
    exact or_cone_singleton_witness n C hAO k hk hkOR hanc x hx

lemma no_clean_and_ancestor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (top : ℕ) (hcone : PEqualNP.Core.InOutputCone n C top)
    (hnoimp : ∀b : Fin 2,¬∀x : Fin n → Bool,
      wireVal n C (opnd C top b) x=true → graphFun G ∅ x=true)
    (i : ℕ) (hi : InCone n C i top) : ¬BelowF G C i := by
  intro hib
  obtain ⟨w,hw,hnw,hwt,hiw⟩ := (inCone_iff n C i top hcone.1).mp hi
  have hwcone : InCone n C (w-n) top :=
    (inCone_iff n C (w-n) top hcone.1).mpr ⟨w,hw,hnw,hwt,Or.inl rfl⟩
  have hwb : BelowF G C (w-n) := by
    rcases hiw with rfl | hiw
    · exact hib
    · exact fixed_cone_closed G C hAO hfixed (w-n)
        (output_cone_ancestor n C (w-n) top hcone hwcone) i hiw hib
  obtain ⟨b,hb⟩ := mem_inputs_opnd n C hAO top hcone.1 w hw
  apply hnoimp b
  intro x hx
  rw [hb] at hx
  apply hwb x
  have he : n+(w-n)=w := by omega
  simpa only [gateVal,wireVal,he] using hx

lemma unique_dirty_opposite_exact_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (g top : ℕ) (hcone : PEqualNP.Core.InOutputCone n C top)
    (hand : (gateAt C top).op=GateOp.and) (hbelow : BelowF G C top)
    (hunique : ∀i<C.gates.length,(gateAt C i).op=GateOp.and → ¬BelowF G C i → i=g)
    (hnoimp : ∀b : Fin 2,¬∀x : Fin n → Bool,
      wireVal n C (opnd C top b) x=true → graphFun G ∅ x=true)
    (v : Fin n) (hgv : gateVal n C g (singletonInput v)=true)
    (hv : v∈singletonSupport n C (opnd C top 0)) :
    ∀x : Fin n → Bool,wireVal n C (opnd C top 1) x=
      decide (∃z∈singletonSupport n C (opnd C top 1),x z=true) := by
  have hall : ∀i,InCone n C i top → (gateAt C i).op=GateOp.and →
      gateVal n C i (singletonInput v)=true := by
    intro i hi hiAND
    have hil := (inCone_lt n C i top hcone.1 hi).trans hcone.1
    have he := hunique i hil hiAND (no_clean_and_ancestor G C hAO hfixed top hcone hnoimp i hi)
    simpa only [he] using hgv
  apply false_operand_exact_or n C hAO top hcone.1 (singletonInput v) hall 1
  cases hr : wireVal n C (opnd C top 1) (singletonInput v) with
  | false => rfl
  | true =>
    have hl := (Finset.mem_filter.mp hv).2
    have ht : gateVal n C top (singletonInput v)=true := by
      rw [gate_and_value n C hAO top hcone.1 hand]
      simp only [hl,hr,Bool.true_and]
    have hf := hbelow _ ht
    have hz : graphFun G ∅ (singletonInput v)=false := by simp [graphFun,singletonInput]
    rw [hz] at hf
    cases hf


lemma and_center_exact_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcycle : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j<C.gates.length) (hand : (gateAt C j).op=GateOp.and) (hbelow : BelowF G C j)
    (u v m : Fin n) (hu : u∈singletonSupport n C (opnd C j 1))
    (hv : v∈singletonSupport n C (opnd C j 1)) (huv : u≠v)
    (hum : G.Adj u m) (hvm : G.Adj v m)
    (hpure : ∀x : Fin n → Bool,wireVal n C (opnd C j 0) x=
      decide (∃z∈singletonSupport n C (opnd C j 0),x z=true)) :
    ∀x : Fin n → Bool,wireVal n C (opnd C j 0) x=x m := by
  have hR : (singletonSupport n C (opnd C j 0)).Nonempty := by
    have ht := wire_all_true n C hAO (opnd C j 0)
      ((operand_bound n C hAO j hj 0).trans (Nat.add_lt_add_left hj n))
    rw [hpure] at ht
    simp only [decide_eq_true_eq] at ht
    obtain ⟨z,hz,_⟩ := ht
    exact ⟨z,hz⟩
  have he := support_center_rigid G hcycle _ _
    (fun a ha b hb => (and_support_cross G C hAO j hj hand hbelow b a hb ha).symm)
    u v m hu hv huv hum hvm hR
  intro x
  rw [hpure,he]
  simp

lemma unique_dirty_opposite_exact_or_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (g top : ℕ) (hcone : PEqualNP.Core.InOutputCone n C top)
    (hand : (gateAt C top).op=GateOp.and) (hbelow : BelowF G C top)
    (hunique : ∀i<C.gates.length,(gateAt C i).op=GateOp.and → ¬BelowF G C i → i=g)
    (hnoimp : ∀b : Fin 2,¬∀x : Fin n → Bool,
      wireVal n C (opnd C top b) x=true → graphFun G ∅ x=true)
    (v : Fin n) (hgv : gateVal n C g (singletonInput v)=true)
    (hv : v∈singletonSupport n C (opnd C top 1)) :
    ∀x : Fin n → Bool,wireVal n C (opnd C top 0) x=
      decide (∃z∈singletonSupport n C (opnd C top 0),x z=true) := by
  have hall : ∀i,InCone n C i top → (gateAt C i).op=GateOp.and →
      gateVal n C i (singletonInput v)=true := by
    intro i hi hiAND
    have hil := (inCone_lt n C i top hcone.1 hi).trans hcone.1
    have he := hunique i hil hiAND (no_clean_and_ancestor G C hAO hfixed top hcone hnoimp i hi)
    simpa only [he] using hgv
  apply false_operand_exact_or n C hAO top hcone.1 (singletonInput v) hall 0
  cases hr : wireVal n C (opnd C top 0) (singletonInput v) with
  | false => rfl
  | true =>
    have hl := (Finset.mem_filter.mp hv).2
    have ht : gateVal n C top (singletonInput v)=true := by
      rw [gate_and_value n C hAO top hcone.1 hand]
      simp only [hl,hr,Bool.true_and]
    have hf := hbelow _ ht
    have hz : graphFun G ∅ (singletonInput v)=false := by simp [graphFun,singletonInput]
    rw [hz] at hf
    cases hf


lemma false_operand_ancestors_false (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (top : ℕ) (htop : top<C.gates.length) (p : Fin n → Bool)
    (hall : ∀i,InCone n C i top → (gateAt C i).op=GateOp.and → gateVal n C i p=true)
    (b : Fin 2) (hfalse : wireVal n C (opnd C top b) p=false)
    (i : ℕ) (hi : opnd C top b=n+i ∨ ∃k,opnd C top b=n+k ∧ InCone n C i k) :
    gateVal n C i p=false := by
  rcases hi with he | ⟨k,he,hi⟩
  · simpa only [he,gateVal,wireVal] using hfalse
  · have hw := operand_bound n C hAO top htop b
    have hwmem : opnd C top b∈(gateAt C top).inputs := by
      obtain ⟨a,c,hac⟩ := gate_two n C hAO top htop
      fin_cases b <;> simp [opnd,hac]
    have hkTop : InCone n C k top :=
      (inCone_iff n C k top htop).mpr
        ⟨opnd C top b,hwmem,by omega,hw,Or.inl (by omega)⟩
    have hkFalse : gateVal n C k p=false := by simpa only [he,gateVal,wireVal] using hfalse
    cases hv : gateVal n C i p with
    | false => rfl
    | true =>
      have ht := ancestor_truth_if_and_true n C hAO top htop p hall k hkTop i hv (Or.inr hi)
      rw [hkFalse] at ht
      cases ht

lemma neighbor_or_false_on_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcycle : NoFourCycle G) (s : Fin n → Bool) (hcolor : ∀u v,G.Adj u v → s u≠s v)
    (v m a b : Fin n) (hvm : G.Adj v m) (ham : G.Adj a m) (hab : G.Adj a b)
    (hav : a≠v) (hbm : b≠m) (Z : Finset (Fin n)) (hZ : ∀z∈Z,G.Adj v z) :
    decide (∃z∈Z,pairInput a b z=true)=false := by
  cases hh : decide (∃z∈Z,pairInput a b z=true) with
  | false => rfl
  | true =>
    have hh' := of_decide_eq_true hh
    obtain ⟨z,hz,hzx⟩ := hh'
    simp only [pairInput,decide_eq_true_eq] at hzx
    rcases hzx with hza | hzb
    · subst z
      have hd := adjacent_neighborhoods_disjoint G s hcolor v a (hZ a hz)
      exact False.elim ((Finset.disjoint_left.mp hd)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvm⟩)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ham⟩))
    · subst z
      exact False.elim (hbm (common_neighbor_unique G hcycle a v m b hav ham hvm hab (hZ b hz)))

lemma labeled_and_false_on_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcycle : NoFourCycle G) (s : Fin n → Bool) (hcolor : ∀u v,G.Adj u v → s u≠s v)
    (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j<C.gates.length)
    (hand : (gateAt C j).op=GateOp.and) (hbelow : BelowF G C j)
    (v m a b : Fin n) (hv : v∈singletonSupport n C (opnd C j 0))
    (hvm : G.Adj v m) (ham : G.Adj a m) (hab : G.Adj a b) (hav : a≠v) (hbm : b≠m)
    (hpure : ∀x : Fin n → Bool,wireVal n C (opnd C j 1) x=
      decide (∃z∈singletonSupport n C (opnd C j 1),x z=true)) :
    gateVal n C j (pairInput a b)=false := by
  have hz := neighbor_or_false_on_edge G hcycle s hcolor v m a b hvm ham hab hav hbm
    (singletonSupport n C (opnd C j 1))
    (fun z hz => and_support_cross G C hAO j hj hand hbelow v z hv hz)
  rw [gate_and_value n C hAO j hj hand,hpure,hz,Bool.and_false]

lemma labeled_and_false_on_edge_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcycle : NoFourCycle G) (s : Fin n → Bool) (hcolor : ∀u v,G.Adj u v → s u≠s v)
    (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j<C.gates.length)
    (hand : (gateAt C j).op=GateOp.and) (hbelow : BelowF G C j)
    (v m a b : Fin n) (hv : v∈singletonSupport n C (opnd C j 1))
    (hvm : G.Adj v m) (ham : G.Adj a m) (hab : G.Adj a b) (hav : a≠v) (hbm : b≠m)
    (hpure : ∀x : Fin n → Bool,wireVal n C (opnd C j 0) x=
      decide (∃z∈singletonSupport n C (opnd C j 0),x z=true)) :
    gateVal n C j (pairInput a b)=false := by
  have hz := neighbor_or_false_on_edge G hcycle s hcolor v m a b hvm ham hab hav hbm
    (singletonSupport n C (opnd C j 0))
    (fun z hz => (and_support_cross G C hAO j hj hand hbelow z v hz hv).symm)
  rw [gate_and_value n C hAO j hj hand,hpure,hz,Bool.false_and]


lemma labeled_opposite_false_on_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcycle : NoFourCycle G) (s : Fin n → Bool) (hcolor : ∀u v,G.Adj u v → s u≠s v)
    (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j<C.gates.length)
    (hand : (gateAt C j).op=GateOp.and) (hbelow : BelowF G C j)
    (v m a b : Fin n) (hv : v∈singletonSupport n C (opnd C j 0))
    (hvm : G.Adj v m) (ham : G.Adj a m) (hab : G.Adj a b) (hav : a≠v) (hbm : b≠m)
    (hpure : ∀x : Fin n → Bool,wireVal n C (opnd C j 1) x=
      decide (∃z∈singletonSupport n C (opnd C j 1),x z=true)) :
    wireVal n C (opnd C j 1) (pairInput a b)=false := by
  rw [hpure]
  exact neighbor_or_false_on_edge G hcycle s hcolor v m a b hvm ham hab hav hbm
    (singletonSupport n C (opnd C j 1))
    (fun z hz => and_support_cross G C hAO j hj hand hbelow v z hv hz)

lemma labeled_opposite_false_on_edge_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcycle : NoFourCycle G) (s : Fin n → Bool) (hcolor : ∀u v,G.Adj u v → s u≠s v)
    (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j<C.gates.length)
    (hand : (gateAt C j).op=GateOp.and) (hbelow : BelowF G C j)
    (v m a b : Fin n) (hv : v∈singletonSupport n C (opnd C j 1))
    (hvm : G.Adj v m) (ham : G.Adj a m) (hab : G.Adj a b) (hav : a≠v) (hbm : b≠m)
    (hpure : ∀x : Fin n → Bool,wireVal n C (opnd C j 0) x=
      decide (∃z∈singletonSupport n C (opnd C j 0),x z=true)) :
    wireVal n C (opnd C j 0) (pairInput a b)=false := by
  rw [hpure]
  exact neighbor_or_false_on_edge G hcycle s hcolor v m a b hvm ham hab hav hbm
    (singletonSupport n C (opnd C j 0))
    (fun z hz => (and_support_cross G C hAO j hj hand hbelow z v hz hv).symm)


def wireCone (n : ℕ) (C : Circuit) (w i : ℕ) : Prop :=
  w=n+i ∨ (n≤w ∧ InCone n C i (w-n))

lemma wireCone_of_input (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (k : ℕ)
    (hk : k<C.gates.length) (u : ℕ) (hu : u∈(gateAt C k).inputs) (i : ℕ)
    (hi : wireCone n C u i) : InCone n C i k := by
  have huk := hAO.2.1 k hk u hu
  rcases hi with he | ⟨hnu,hi⟩
  · apply (inCone_iff n C i k hk).mpr
    exact ⟨u,hu,by omega,huk,Or.inl (by omega)⟩
  · have hul : InCone n C (u-n) k :=
      (inCone_iff n C (u-n) k hk).mpr ⟨u,hu,hnu,huk,Or.inl rfl⟩
    exact inCone_trans n C i (u-n) k hk hi hul

lemma alias_agree_source_free (n : ℕ) (C P : Circuit) (hAO : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n)
    (hsem : ∀(x : Fin n → Bool) k,k<C.gates.length →
      wireVal n P (n+k) x=
        if k=g ∨ k=B then x v else if k=j then wireVal n P p x else
          (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => wireVal n P u x)) :
    ∀w,w<n+C.gates.length →
      (∀i,wireCone n C w i → i≠g ∧ i≠B ∧ i≠j) →
      ∀x : Fin n → Bool,wireVal n P w x=wireVal n C w x := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw havoid x
    by_cases hraw : w<n
    · rw [wireVal_input n P x w hraw,wireVal_input n C x w hraw]
    · obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
      have hk : k<C.gates.length := by omega
      obtain ⟨hkg,hkB,hkj⟩ := havoid k (Or.inl rfl)
      rw [hsem x k hk,if_neg (by simp [hkg,hkB]),if_neg hkj,wireVal_gate n C x k hk hAO.2.1]
      congr 1
      apply List.map_congr_left
      intro u hu
      have huk := hAO.2.1 k hk u hu
      apply ih u huk (by omega) _ x
      intro i hi
      apply havoid i
      refine Or.inr ⟨by omega,?_⟩
      simpa only [Nat.add_sub_cancel_left] using wireCone_of_input n C hAO k hk u hu i hi

lemma alias_agree_on_false_operand (n : ℕ) (C P : Circuit) (hAO : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n)
    (hsem : ∀(x : Fin n → Bool) k,k<C.gates.length →
      wireVal n P (n+k) x=
        if k=g ∨ k=B then x v else if k=j then wireVal n P p x else
          (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => wireVal n P u x))
    (top : ℕ) (htop : top<C.gates.length) (probe : Fin n → Bool)
    (hall : ∀i,InCone n C i top → (gateAt C i).op=GateOp.and → gateVal n C i probe=true)
    (b : Fin 2) (hfalse : wireVal n C (opnd C top b) probe=false)
    (hjtrue : gateVal n C j probe=true) (hBtrue : gateVal n C B probe=true)
    (hgtrue : gateVal n C g probe=true) :
    ∀x : Fin n → Bool,wireVal n P (opnd C top b) x=wireVal n C (opnd C top b) x := by
  apply alias_agree_source_free n C P hAO j p B g v hsem (opnd C top b)
    ((operand_bound n C hAO top htop b).trans (Nat.add_lt_add_left htop n))
  intro i hi
  have hif : gateVal n C i probe=false := by
    apply false_operand_ancestors_false n C hAO top htop probe hall b hfalse i
    rcases hi with he | ⟨hni,hi⟩
    · exact Or.inl he
    · exact Or.inr ⟨opnd C top b-n,by omega,hi⟩
  refine ⟨?_,?_,?_⟩
  · intro he;subst i;rw [hgtrue] at hif;cases hif
  · intro he;subst i;rw [hBtrue] at hif;cases hif
  · intro he;subst i;rw [hjtrue] at hif;cases hif

end PEqualNP.Outside.L_meta_3754.Ledger

namespace PEqualNP.Outside.L_meta_3754.PairPreserve
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core

def AliasSem (n : ℕ) (C P : Circuit) (j p B g : ℕ) (v : Fin n) : Prop :=
  ∀(x : Fin n → Bool) k,k<C.gates.length →
    wireVal n P (n+k) x=if k=g ∨ k=B then x v else if k=j then wireVal n P p x else
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => wireVal n P u x)

lemma opnd_mem (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (k : ℕ)
    (hk : k<C.gates.length) (b : Fin 2) : opnd C k b∈(gateAt C k).inputs := by
  obtain ⟨a,c,hac⟩ := Ledger.gate_two n C hAO k hk
  fin_cases b <;> simp [opnd,hac]

lemma noimp {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (k : ℕ) (hk : k<C.gates.length)
    (hand : (gateAt C k).op=GateOp.and) (b : Fin 2) :
    ¬∀x : Fin n → Bool,wireVal n C (opnd C k b) x=true → graphFun G ∅ x=true := by
  exact Bypass.least_no_and_below_operand hC hk hand (opnd_mem n C hC.1 k hk b)

lemma least_or_after_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hfixed : IsLiftFixedPoint G C)
    (top : ℕ) (hbelow : BelowF G C top) (k : ℕ) (hcone : InOutputCone n C k)
    (hanc : InCone n C top k) : (gateAt C k).op=GateOp.or := by
  have hm : gateAt C k∈C.gates := by rw [Ledger.gateAt_eq_getElem C k hcone.1];exact List.getElem_mem hcone.1
  rcases hC.1.1 _ hm with hand | hor
  · exact (Ledger.no_clean_and_ancestor G C hC.1 hfixed k hcone
      (noimp G C hC k hcone.1 hand) top hanc hbelow).elim
  · exact hor

lemma alias_unique_forward (n : ℕ) (C P : Circuit) (hAO : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n) (hsem : AliasSem n C P j p B g v)
    (hjg : j<g) (hBg : B<g) (top : ℕ) (htop : top<C.gates.length)
    (hall : ∀i,InCone n C i top → (gateAt C i).op=GateOp.and → i=g)
    (x : Fin n → Bool) (hv : x v=true) :
    ∀k,InCone n C k top → (g=k ∨ InCone n C g k) → wireVal n P (n+k) x=true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hkTop hreach
    have hk : k<C.gates.length := (Ledger.inCone_lt n C k top htop hkTop).trans htop
    by_cases hkg : k=g
    · rw [hsem x k hk,if_pos (Or.inl hkg),hv]
    have hgk : g<k := by
      rcases hreach with he | he
      · exact (hkg he.symm).elim
      · exact Ledger.inCone_lt n C g k hk he
    have hor : (gateAt C k).op=GateOp.or := by
      have hm : gateAt C k∈C.gates := by rw [Ledger.gateAt_eq_getElem C k hk];exact List.getElem_mem hk
      rcases hAO.1 _ hm with hand | hor
      · exact (hkg (hall k hkTop hand)).elim
      · exact hor
    have hanc : InCone n C g k := hreach.resolve_left (Ne.symm hkg)
    obtain ⟨w,hw,hnw,hwk,hgw⟩ := (Ledger.inCone_iff n C g k hk).mp hanc
    have hwcone : InCone n C (w-n) k :=
      (Ledger.inCone_iff n C (w-n) k hk).mpr ⟨w,hw,hnw,hwk,Or.inl rfl⟩
    have hvw := ih (w-n) (by omega) (Ledger.inCone_trans n C (w-n) k top htop hwcone hkTop) hgw
    rw [hsem x k hk,if_neg (by omega),if_neg (by omega),hor]
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    exact ⟨w,hw,by simpa only [show n+(w-n)=w by omega] using hvw⟩

lemma alias_clean_to_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C P : Circuit) (hC : IsLeastAO G C) (hfixed : IsLiftFixedPoint G C)
    (j p B g : ℕ) (v : Fin n) (hsem : AliasSem n C P j p B g v)
    (top : ℕ) (hcone : InOutputCone n C top) (hbelow : BelowF G C top)
    (hjtop : j<top) (hBtop : B<top) (hgtop : g<top)
    (hout : C.output<n+C.gates.length) (x : Fin n → Bool)
    (ht : wireVal n P (n+top) x=true) : wireVal n P C.output x=true := by
  have hup : ∀k,InOutputCone n C k → (k=top ∨ InCone n C top k) → wireVal n P (n+k) x=true := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hkcone hreach
      rcases hreach with rfl | hreach
      · exact ht
      have htk := Ledger.inCone_lt n C top k hkcone.1 hreach
      have hor := least_or_after_clean G C hC hfixed top hbelow k hkcone hreach
      obtain ⟨w,hw,hnw,hwk,htw⟩ := (Ledger.inCone_iff n C top k hkcone.1).mp hreach
      have hwcone : InCone n C (w-n) k :=
        (Ledger.inCone_iff n C (w-n) k hkcone.1).mpr ⟨w,hw,hnw,hwk,Or.inl rfl⟩
      have hvw := ih (w-n) (by omega) (Ledger.output_cone_ancestor n C (w-n) k hkcone hwcone)
        (htw.imp_left Eq.symm)
      rw [hsem x k hkcone.1,if_neg (by omega),if_neg (by omega),hor]
      simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
      exact ⟨w,hw,by simpa only [show n+(w-n)=w by omega] using hvw⟩
  rcases hcone.2 with ho | ⟨hno,ho⟩
  · simpa only [ho] using ht
  · have hk : C.output-n<C.gates.length := by omega
    have hc : InOutputCone n C (C.output-n) := ⟨hk,Or.inl (by omega)⟩
    have hh := hup (C.output-n) hc (Or.inr ho)
    simpa only [show n+(C.output-n)=C.output by omega] using hh

lemma alias_pair_from_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C P : Circuit) (hC : IsLeastAO G C) (hfixed : IsLiftFixedPoint G C)
    (j p B g : ℕ) (v m : Fin n) (hsem : AliasSem n C P j p B g v)
    (hjg : j<g) (hBg : B<g) (hout : C.output<n+C.gates.length)
    (hunique : ∀i<C.gates.length,(gateAt C i).op=GateOp.and → ¬BelowF G C i → i=g)
    (top : ℕ) (hcone : InOutputCone n C top) (hand : (gateAt C top).op=GateOp.and)
    (htg : top≠g) (used other : Fin 2) (hne : used≠other)
    (hreach : ∃k,opnd C top used=n+k ∧ k<C.gates.length ∧ (g=k ∨ InCone n C g k))
    (hother : wireVal n C (opnd C top other) (pairInput v m)=true)
    (hjv : gateVal n C j (Ledger.singletonInput v)=true)
    (hBv : gateVal n C B (Ledger.singletonInput v)=true)
    (hgv : gateVal n C g (Ledger.singletonInput v)=true) :
    wireVal n P C.output (pairInput v m)=true := by
  have hbelow : BelowF G C top := by
    by_contra hn
    exact htg (hunique top hcone.1 hand hn)
  have hall : ∀i,InCone n C i top → (gateAt C i).op=GateOp.and → i=g := by
    intro i hi hiAND
    have hil := (Ledger.inCone_lt n C i top hcone.1 hi).trans hcone.1
    exact hunique i hil hiAND (Ledger.no_clean_and_ancestor G C hC.1 hfixed top hcone
      (noimp G C hC top hcone.1 hand) i hi)
  have hallTrue : ∀i,InCone n C i top → (gateAt C i).op=GateOp.and →
      gateVal n C i (Ledger.singletonInput v)=true := by
    intro i hi hiAND
    simpa only [hall i hi hiAND] using hgv
  obtain ⟨k,hwk,hk,hgk⟩ := hreach
  have hkw := Ledger.operand_bound n C hC.1 top hcone.1 used
  have hkTop : InCone n C k top :=
    (Ledger.inCone_iff n C k top hcone.1).mpr
      ⟨opnd C top used,opnd_mem n C hC.1 top hcone.1 used,by omega,hkw,Or.inl (by omega)⟩
  have hgtop : g<top := by
    have hkt := Ledger.inCone_lt n C k top hcone.1 hkTop
    rcases hgk with he | he
    · omega
    · have := Ledger.inCone_lt n C g k hk he
      omega
  have hused : wireVal n C (opnd C top used) (Ledger.singletonInput v)=true := by
    have hh := Ledger.ancestor_truth_if_and_true n C hC.1 top hcone.1
      (Ledger.singletonInput v) hallTrue k hkTop g hgv hgk
    simpa only [hwk,gateVal,wireVal] using hh
  have hcases : ∀b : Fin 2,b=used ∨ b=other := by
    intro b
    fin_cases b <;> fin_cases used <;> fin_cases other <;> simp_all
  have hfalse : wireVal n C (opnd C top other) (Ledger.singletonInput v)=false := by
    cases hh : wireVal n C (opnd C top other) (Ledger.singletonInput v)
    · rfl
    · have hb : ∀b : Fin 2,wireVal n C (opnd C top b) (Ledger.singletonInput v)=true := by
        intro b
        rcases hcases b with rfl | rfl <;> assumption
      have ht : gateVal n C top (Ledger.singletonInput v)=true := by
        rw [Ledger.gate_and_value n C hC.1 top hcone.1 hand,hb 0,hb 1]
        rfl
      have hf := hbelow _ ht
      have hz : graphFun G ∅ (Ledger.singletonInput v)=false := by simp [graphFun,Ledger.singletonInput]
      rw [hz] at hf
      cases hf
  have hagree := Ledger.alias_agree_on_false_operand n C P hC.1 j p B g v hsem
    top hcone.1 (Ledger.singletonInput v) hallTrue other hfalse hjv hBv hgv
  have hotherP : wireVal n P (opnd C top other) (pairInput v m)=true := by
    rw [hagree];exact hother
  have husedP : wireVal n P (opnd C top used) (pairInput v m)=true := by
    rw [hwk]
    exact alias_unique_forward n C P hC.1 j p B g v hsem hjg hBg top hcone.1 hall
      (pairInput v m) (by simp [pairInput]) k hkTop hgk
  have hbP : ∀b : Fin 2,wireVal n P (opnd C top b) (pairInput v m)=true := by
    intro b
    rcases hcases b with rfl | rfl <;> assumption
  have htP : wireVal n P (n+top) (pairInput v m)=true := by
    rw [hsem _ top hcone.1,if_neg (by omega),if_neg (by omega),hand]
    obtain ⟨a,b,hab⟩ := Ledger.gate_two n C hC.1 top hcone.1
    have ha : wireVal n P a (pairInput v m)=true := by simpa [opnd,hab] using hbP 0
    have hb : wireVal n P b (pairInput v m)=true := by simpa [opnd,hab] using hbP 1
    simp [hab,GateOp.eval,ha,hb]
  exact alias_clean_to_output G C P hC hfixed j p B g v hsem top hcone hbelow
    (by omega) (by omega) hgtop hout (pairInput v m) htP

end PEqualNP.Outside.L_meta_3754.PairPreserve
