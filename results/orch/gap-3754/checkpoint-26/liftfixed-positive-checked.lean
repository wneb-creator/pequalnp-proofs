import PEqualNP.Defs

-- Bypass and strict classification adapt accepted L_meta_1485 and L_meta_3653 (Apache-2.0).

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


def patchThree (C : Circuit) (j p b g v : ℕ) : Circuit :=
  ⟨((C.gates.set j ⟨GateOp.or, [p,p]⟩).set b ⟨GateOp.or, [v,v]⟩).set g
      ⟨GateOp.or, [v,v]⟩, C.output⟩

lemma patchThree_length (C : Circuit) (j p b g v : ℕ) :
    (patchThree C j p b g v).gates.length = C.gates.length := by
  simp [patchThree]

lemma bypass_val_eq_all {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : IsAO2 n C) {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r)
    (he : val C x (n+r) = val C x i) (w : ℕ) :
    val (bypass n C r i) x (aliasWire (n+r) i w) = val C x w := by
  by_cases hw : w = n+r
  · subst w
    rw [aliasWire_self, bypass_val_lt hx hr i hi, he]
  · exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx
      (fun k hk => hAO.1 _ (gateAt_mem hk)) hr (Or.inl hi) (fun _ => he) w hw).symm

lemma aliasWire_bound {n : ℕ} {C : Circuit} {r i : ℕ}
    (hr : r < C.gates.length) (hi : i < n+r) {w : ℕ} (hw : w<n+C.gates.length) :
    aliasWire (n+r) i w < n+(bypass n C r i).gates.length := by
  rw [bypass_length]
  have hh : n+r ≤ n+(C.gates.length-1) := by omega
  apply aliasWire_lt hi hh
  omega

lemma contract_three {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a b c p q r : ℕ} (hab : a<b) (hbc : b<c) (hc : c<C.gates.length)
    (hp : p<n+a) (hq : q<n+b) (hr : r<n+c)
    (haeq : ∀ x : Fin n → Bool, val C (List.ofFn x) (n+a)=val C (List.ofFn x) p)
    (hbeq : ∀ x : Fin n → Bool, val C (List.ofFn x) (n+b)=val C (List.ofFn x) q)
    (hceq : ∀ x : Fin n → Bool, val C (List.ofFn x) (n+c)=val C (List.ofFn x) r) :
    ∃ (D : Circuit) (f : ℕ → ℕ), IsAO2 n D ∧ D.gates.length+3=C.gates.length ∧
      D.output=f C.output ∧
      (∀ w,w<n+C.gates.length → f w<n+D.gates.length) ∧
      (∀ (x : Fin n → Bool) w, val D (List.ofFn x) (f w)=val C (List.ofFn x) w) := by
  let C2 := bypass n C c r
  have hAO2 : IsAO2 n C2 := isAO2_bypass hAO hr
  have hb2 : b<C2.gates.length := by dsimp [C2]; rw [bypass_length]; omega
  have ha2 : a<C2.gates.length := by omega
  have he2 (x : Fin n → Bool) (w : ℕ) :
      val C2 (List.ofFn x) (aliasWire (n+c) r w)=val C (List.ofFn x) w :=
    bypass_val_eq_all (by simp) hAO hc hr (hceq x) w
  have hbeq2 (x : Fin n → Bool) :
      val C2 (List.ofFn x) (n+b)=val C2 (List.ofFn x) q := by
    rw [bypass_val_lt (by simp) hc (n+b) (by omega),
      bypass_val_lt (by simp) hc q (by omega)]
    exact hbeq x
  let C1 := bypass n C2 b q
  have hAO1 : IsAO2 n C1 := isAO2_bypass hAO2 hq
  have ha1 : a<C1.gates.length := by dsimp [C1]; rw [bypass_length]; omega
  have he1 (x : Fin n → Bool) (w : ℕ) :
      val C1 (List.ofFn x) (aliasWire (n+b) q w)=val C2 (List.ofFn x) w :=
    bypass_val_eq_all (by simp) hAO2 hb2 hq (hbeq2 x) w
  have haeq1 (x : Fin n → Bool) :
      val C1 (List.ofFn x) (n+a)=val C1 (List.ofFn x) p := by
    rw [bypass_val_lt (by simp) hb2 (n+a) (by omega),
      bypass_val_lt (by simp) hb2 p (by omega),
      bypass_val_lt (by simp) hc (n+a) (by omega),
      bypass_val_lt (by simp) hc p (by omega)]
    exact haeq x
  let D := bypass n C1 a p
  let f := fun w => aliasWire (n+a) p (aliasWire (n+b) q (aliasWire (n+c) r w))
  have hD : IsAO2 n D := isAO2_bypass hAO1 hp
  refine ⟨D,f,hD,?_,rfl,?_,?_⟩
  · dsimp [D,C1,C2]
    simp only [bypass_length]
    omega
  · intro w hw
    apply aliasWire_bound ha1 hp
    apply aliasWire_bound hb2 hq
    exact aliasWire_bound hc hr hw
  · intro x w
    change val D (List.ofFn x) (aliasWire (n+a) p (aliasWire (n+b) q (aliasWire (n+c) r w))) = _
    rw [bypass_val_eq_all (by simp) hAO1 ha1 hp (haeq1 x), he1, he2]

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


lemma isAO2_addTop_pair {n : ℕ} {D : Circuit} {a b : ℕ} {op : GateOp}
    (hD : IsAO2 n D) (hop : op=GateOp.and ∨ op=GateOp.or)
    (ha : a<n+D.gates.length) (hb : b<n+D.gates.length) :
    IsAO2 n (addTop n D ⟨op,[a,b]⟩) := by
  refine ⟨?_,addTop_readsBack ?_ hD.2.1,?_⟩
  · intro g hg
    rcases addTop_mem g hg with h | rfl
    · exact hD.1 g h
    · exact hop
  · intro u hu
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    rcases addTop_mem g hg with h | rfl
    · exact hD.2.2 g h
    · rfl

lemma addTop_val_old {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length=n)
    (g : Gate) {w : ℕ} (hw : w<n+C.gates.length) :
    val (addTop n C g) x w=val C x w := by
  exact val_prefix hx (Nat.le_refl _) (by rw [addTop_length];omega)
    (fun _ hk => gateAt_addTop_lt hk) w hw

def appendProduct (n : ℕ) (C : Circuit) (a m : ℕ) : Circuit :=
  addTop n (addTop n C ⟨GateOp.and,[m,a]⟩)
    ⟨GateOp.or,[C.output,n+C.gates.length]⟩

lemma appendProduct_length (n : ℕ) (C : Circuit) (a m : ℕ) :
    (appendProduct n C a m).gates.length=C.gates.length+2 := by
  simp [appendProduct,addTop_length]

lemma appendProduct_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a m : ℕ} (ha : a<n+C.gates.length) (hm : m<n+C.gates.length)
    (ho : C.output<n+C.gates.length) : IsAO2 n (appendProduct n C a m) := by
  apply isAO2_addTop_pair (isAO2_addTop_pair hAO (Or.inl rfl) hm ha) (Or.inr rfl)
  · rw [addTop_length];omega
  · rw [addTop_length];omega

lemma appendProduct_eval {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length=n)
    {a m : ℕ} (ho : C.output<n+C.gates.length) :
    (appendProduct n C a m).eval x=(C.eval x || (val C x m && val C x a)) := by
  rw [appendProduct,addTop_eval hx]
  simp only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,Bool.or_false,id_eq]
  rw [addTop_val_old hx _ ho]
  have hnew : val (addTop n C ⟨GateOp.and,[m,a]⟩) x (n+C.gates.length) =
      (val C x m && val C x a) := by
    change (addTop n C ⟨GateOp.and,[m,a]⟩).eval x = _
    rw [addTop_eval hx]
    simp [GateOp.eval]
  rw [hnew]
  rfl

lemma contract_three_and_lift {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a b c p q r w m : ℕ} (hab : a<b) (hbc : b<c) (hc : c<C.gates.length)
    (hp : p<n+a) (hq : q<n+b) (hr : r<n+c)
    (haeq : ∀ x : Fin n → Bool, val C (List.ofFn x) (n+a)=val C (List.ofFn x) p)
    (hbeq : ∀ x : Fin n → Bool, val C (List.ofFn x) (n+b)=val C (List.ofFn x) q)
    (hceq : ∀ x : Fin n → Bool, val C (List.ofFn x) (n+c)=val C (List.ofFn x) r)
    (hw : w<n+C.gates.length) (hm : m<n+C.gates.length)
    (ho : C.output<n+C.gates.length) :
    ∃ D : Circuit, IsAO2 n D ∧ D.gates.length+1=C.gates.length ∧
      ∀ x : Fin n → Bool, circuitFun n D x =
        (circuitFun n C x || (val C (List.ofFn x) m && val C (List.ofFn x) w)) := by
  obtain ⟨K,f,hK,hsize,hout,hbound,hval⟩ :=
    contract_three hAO hab hbc hc hp hq hr haeq hbeq hceq
  have hoK : K.output<n+K.gates.length := by rw [hout]; exact hbound _ ho
  refine ⟨appendProduct n K (f w) (f m),
    appendProduct_isAO2 hK (hbound _ hw) (hbound _ hm) hoK,?_,?_⟩
  · rw [appendProduct_length];omega
  · intro x
    change (appendProduct n K (f w) (f m)).eval (List.ofFn x) = _
    rw [appendProduct_eval (by simp) hoK, hval, hval]
    congr 1
    change val K (List.ofFn x) K.output=val C (List.ofFn x) C.output
    rw [hout,hval]


lemma patchThree_gateAt {C : Circuit} (j p b g v : ℕ) {k : ℕ} (hk : k<C.gates.length) :
    gateAt (patchThree C j p b g v) k =
      if k=g then ⟨GateOp.or,[v,v]⟩ else if k=b then ⟨GateOp.or,[v,v]⟩
      else if k=j then ⟨GateOp.or,[p,p]⟩ else gateAt C k := by
  simp [gateAt,patchThree,List.getD_eq_getElem?_getD,List.getElem_set,hk,eq_comm]

lemma patchThree_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (j p b g v : ℕ) (hp : p<n+j) (hv : v<n) :
    IsAO2 n (patchThree C j p b g v) := by
  have hop (k : ℕ) (hk : k<(patchThree C j p b g v).gates.length) :
      (gateAt (patchThree C j p b g v) k).op=GateOp.and ∨
      (gateAt (patchThree C j p b g v) k).op=GateOp.or := by
    rw [patchThree_length] at hk
    rw [patchThree_gateAt j p b g v hk]
    split_ifs <;> try exact Or.inr rfl
    exact hAO.1 _ (gateAt_mem hk)
  have hlen (k : ℕ) (hk : k<(patchThree C j p b g v).gates.length) :
      (gateAt (patchThree C j p b g v) k).inputs.length=2 := by
    rw [patchThree_length] at hk
    rw [patchThree_gateAt j p b g v hk]
    split_ifs <;> try rfl
    exact hAO.2.2 _ (gateAt_mem hk)
  refine ⟨?_,?_,?_⟩
  · intro z hz
    obtain ⟨k,hk,hz⟩ := List.mem_iff_getElem.mp hz
    rw [← hz, ← gateAt_eq hk]
    exact hop k hk
  · intro k hk w hw
    rw [patchThree_length] at hk
    rw [patchThree_gateAt j p b g v hk] at hw
    split_ifs at hw with hkg hkb hkj
    · simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hw
      subst w;omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hw
      subst w;omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hw
      subst w;omega
    · exact hAO.2.1 k hk w hw
  · intro z hz
    obtain ⟨k,hk,hz⟩ := List.mem_iff_getElem.mp hz
    rw [← hz, ← gateAt_eq hk]
    exact hlen k hk

lemma patchThree_aliases {n : ℕ} {C : Circuit} (j p b g v : ℕ)
    (hj : j<C.gates.length) (hb : b<C.gates.length) (hg : g<C.gates.length)
    (hjg : j≠g) (hbg : b≠g) (hjb : j≠b) (hp : p<n+j) (hv : v<n) :
    ∀ x : Fin n → Bool,
      val (patchThree C j p b g v) (List.ofFn x) (n+j) =
        val (patchThree C j p b g v) (List.ofFn x) p ∧
      val (patchThree C j p b g v) (List.ofFn x) (n+b) =
        val (patchThree C j p b g v) (List.ofFn x) v ∧
      val (patchThree C j p b g v) (List.ofFn x) (n+g) =
        val (patchThree C j p b g v) (List.ofFn x) v := by
  intro x
  have hlen := patchThree_length C j p b g v
  constructor
  · rw [val_gate (by simp) (by omega : j<(patchThree C j p b g v).gates.length),
      patchThree_gateAt j p b g v hj]
    simp [hjg,hjb,hp,GateOp.eval]
  constructor
  · rw [val_gate (by simp) (by omega : b<(patchThree C j p b g v).gates.length),
      patchThree_gateAt j p b g v hb]
    simp [hbg,GateOp.eval,show v<n+b by omega]
  · rw [val_gate (by simp) (by omega : g<(patchThree C j p b g v).gates.length),
      patchThree_gateAt j p b g v hg]
    simp [GateOp.eval,show v<n+g by omega]


lemma patch_three_strict_saving {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hleast : IsLeastAO G C) (j p b g aW : ℕ) (v m : Fin n)
    (hjg : j<g) (hbg : b<g) (hg : g<C.gates.length) (hjb : j≠b)
    (hp : p<n+j) (haW : aW<n+C.gates.length) (ho : C.output<n+C.gates.length)
    (hrestore : ∀ x : Fin n → Bool,
      (circuitFun n (patchThree C j p b g v.val) x ||
        (x m && val (patchThree C j p b g v.val) (List.ofFn x) aW)) = graphFun G ∅ x) : False := by
  let P := patchThree C j p b g v.val
  have hP : IsAO2 n P := patchThree_isAO2 hleast.1 j p b g v.val hp v.isLt
  have hlen : P.gates.length=C.gates.length := patchThree_length C j p b g v.val
  have hEq := patchThree_aliases j p b g v.val (by omega) (by omega) hg
    (by omega) (by omega) hjb hp v.isLt
  have hD : ∃ D : Circuit, IsAO2 n D ∧ D.gates.length+1=P.gates.length ∧
      ∀ x : Fin n → Bool, circuitFun n D x =
        (circuitFun n P x || (val P (List.ofFn x) m.val && val P (List.ofFn x) aW)) := by
    rcases Nat.lt_or_gt_of_ne hjb with hjb' | hbj'
    · exact contract_three_and_lift hP hjb' hbg (by omega) hp (by omega) (by omega)
        (fun x => (hEq x).1) (fun x => (hEq x).2.1) (fun x => (hEq x).2.2)
        (by omega) (by omega) (by simpa [P,patchThree] using ho)
    · exact contract_three_and_lift hP hbj' hjg (by omega) (by omega) hp (by omega)
        (fun x => (hEq x).2.1) (fun x => (hEq x).1) (fun x => (hEq x).2.2)
        (by omega) (by omega) (by simpa [P,patchThree] using ho)
  obtain ⟨D,hDA,hsize,hfun⟩ := hD
  have hDF : circuitFun n D=graphFun G ∅ := by
    funext x
    rw [hfun x]
    have hinput : val P (List.ofFn x) m.val=x m := by
      rw [val_input (by simp) m.isLt]
      simp [List.getD_eq_getElem?_getD]
    rw [hinput]
    exact hrestore x
  have hmin := hleast.2.2 D hDA hDF
  change C.gates.length≤D.gates.length at hmin
  omega


lemma val_gate_readsBack {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length=n)
    (hAO : IsAO2 n C) {k : ℕ} (hk : k<C.gates.length) :
    val C x (n+k)=(gateAt C k).op.eval ((gateAt C k).inputs.map fun w => val C x w) := by
  rw [val_gate hx hk]
  congr 1
  apply List.map_congr_left
  intro w hw
  simp [hAO.2.1 k hk w hw]

lemma patchThree_semantics {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (j p b g : ℕ) (v : Fin n) (hp : p<n+j) :
    ∀ (x : Fin n → Bool) k,k<C.gates.length →
      val (patchThree C j p b g v.val) (List.ofFn x) (n+k) =
        if k=g ∨ k=b then x v else if k=j then
          val (patchThree C j p b g v.val) (List.ofFn x) p else
          (gateAt C k).op.eval ((gateAt C k).inputs.map fun w =>
            val (patchThree C j p b g v.val) (List.ofFn x) w) := by
  intro x k hk
  have hP := patchThree_isAO2 hAO j p b g v.val hp v.isLt
  have hkP : k<(patchThree C j p b g v.val).gates.length := by
    simpa only [patchThree_length] using hk
  rw [val_gate_readsBack (by simp) hP hkP,patchThree_gateAt j p b g v.val hk]
  have hinput : val (patchThree C j p b g v.val) (List.ofFn x) v.val=x v := by
    rw [val_input (by simp) v.isLt]
    simp [List.getD_eq_getElem?_getD]
  by_cases hkg : k=g
  · simp [hkg,GateOp.eval,hinput]
  by_cases hkb : k=b
  · simp [hkg,hkb,GateOp.eval,hinput]
  by_cases hkj : k=j
  · subst k
    simp [hkg,hkb,GateOp.eval]
  · simp [hkg,hkb,hkj]

end PEqualNP.Outside.L_meta_3754.Bypass

-- Strict deletion and minimality API adapted from accepted L_meta_9425.

namespace PEqualNP.Outside.L_meta_3754.Deletion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_allTrue {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wval_input C _ w hwn]
    · have hj : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      rw [hw_eq]
      have hop := hAO.1 _ (gateAt_mem hj)
      have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hj 0; omega
      have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hj 1; omega
      have hv0 := ih _ h0 (by omega)
      have hv1 := ih _ h1 (by omega)
      rcases hop with hand | hor
      · rw [wval_gate_and hAO _ hj hand, hv0, hv1]; rfl
      · rw [wval_gate_or hAO _ hj hor, hv0, hv1]; rfl

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_cones_len]; simp

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  by_contra hge
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro h
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hnw, hwnj, rfl | hsub⟩
    · omega
    · have := ih (w - n) (by omega) hsub; omega

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hk := inCone_lt_len h2
    rw [inCone_iff hk] at h2 ⊢
    rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩

def delWire (n j r w : ℕ) : ℕ :=
  if w = n + j then r else if n + j < w then w - 1 else w

def delCircuit (n : ℕ) (C : Circuit) (j r : ℕ) : Circuit :=
  { gates := (C.gates.eraseIdx j).map (fun g => { g with inputs := g.inputs.map (delWire n j r) })
    output := delWire n j r C.output }

lemma delCircuit_len (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) (r : ℕ) :
    (delCircuit n C j r).gates.length = C.gates.length - 1 := by
  simp [delCircuit, List.length_eraseIdx, hj]

lemma delCircuit_gateAt_lt {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C i) with inputs := (gateAt C i).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx, ite_eq_left hj]; omega) hi]

lemma delCircuit_gateAt_ge {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C (i + 1)) with inputs := (gateAt C (i + 1)).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx, ite_eq_left hj]; omega) hji]

lemma delCircuit_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r : ℕ}
    (hj : j < C.gates.length) (hr : r < n + j) : IsAO2 n (delCircuit n C j r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    exact hAO.1 g0 (List.mem_of_mem_eraseIdx hg0)
  · intro i hi w hw
    rw [delCircuit_len n C hj r] at hi
    by_cases hij : i < j
    · rw [delCircuit_gateAt_lt hj hij] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + i := hAO.2.1 i (by omega) u hu
      unfold delWire
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hult
    · rw [delCircuit_gateAt_ge hj (by omega) hi] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + (i + 1) := hAO.2.1 (i + 1) (by omega) u hu
      unfold delWire
      split_ifs <;> omega
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    simp only [List.length_map]
    exact hAO.2.2 g0 (List.mem_of_mem_eraseIdx hg0)

lemma delCircuit_opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C i b) := by
  unfold opnd
  rw [delCircuit_gateAt_lt hj hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl

lemma delCircuit_opnd_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C (i + 1) b) := by
  unfold opnd
  rw [delCircuit_gateAt_ge hj hji hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl

lemma delCircuit_wval_not_inCone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j) :
    ∀ w < n + C.gates.length, w ≠ n + j → (n ≤ w → ¬ InCone n C j (w - n)) →
      wval (delCircuit n C j r) x (delWire n j r w) = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwj hnc
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by unfold delWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [hdw, wval_input _ x w hwn, wval_input _ x w hwn]
    · have hnc' : ¬ InCone n C j (w - n) := hnc (by omega)
      have hop_ok : ∀ b : Fin 2, opnd C (w - n) b ≠ n + j ∧
          (n ≤ opnd C (w - n) b → ¬ InCone n C j (opnd C (w - n) b - n)) := by
        intro b
        have hk : w - n < C.gates.length := by omega
        have hmem := opnd_mem hAO hk b
        have hlt := opnd_lt hAO hk b
        constructor
        · intro heq; apply hnc'; rw [inCone_iff hk]
          exact ⟨opnd C (w - n) b, hmem, by omega, hlt, Or.inl (by omega)⟩
        · intro hnu hin; apply hnc'; rw [inCone_iff hk]
          exact ⟨opnd C (w - n) b, hmem, hnu, hlt, Or.inr hin⟩
      by_cases hlt : w < n + j
      · have hk : w - n < j := by omega
        have hdw : delWire n j r w = n + (w - n) := by
          unfold delWire; rw [ite_eq_right hwj, ite_eq_right (by omega)]; omega
        have hw_eq : w = n + (w - n) := by omega
        rw [hdw]
        conv_rhs => rw [hw_eq]
        have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
        rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
        have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
        rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
        have h0 := ih (opnd C (w - n) 0) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega) (hop_ok 0).1 (hop_ok 0).2
        have h1 := ih (opnd C (w - n) 1) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega) (hop_ok 1).1 (hop_ok 1).2
        rw [h0, h1, hg]
      · have hgt : n + j < w := by omega
        have hk : w - n - 1 < C.gates.length - 1 := by omega
        have hjk : j ≤ w - n - 1 := by omega
        have hdw : delWire n j r w = n + (w - n - 1) := by
          unfold delWire; rw [ite_eq_right hwj, ite_eq_left hgt]; omega
        have hw_eq : w = n + (w - n - 1 + 1) := by omega
        have hidx : w - n = w - n - 1 + 1 := by omega
        rw [hdw]
        conv_rhs => rw [hw_eq]
        have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
        rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
        have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
        rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
        have h0 := ih (opnd C (w - n - 1 + 1) 0)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          (by rw [← hidx]; exact (hop_ok 0).1) (by rw [← hidx]; exact (hop_ok 0).2)
        have h1 := ih (opnd C (w - n - 1 + 1) 1)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          (by rw [← hidx]; exact (hop_ok 1).1) (by rw [← hidx]; exact (hop_ok 1).2)
        rw [h0, h1, hg]


lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold graphFun; simp

lemma graphFun_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (fun w => decide (w = v)) = false := by
  rw [Bool.eq_false_iff, ne_eq, graphFun_iff]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.loopless.irrefl _ hab

lemma graphFun_pair_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    unfold pairInput at ha hb
    simp only [decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (G.loopless.irrefl _)
    · exact hab
    · exact hab.symm
    · exact absurd hab (G.loopless.irrefl _)
  · intro huv
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩


lemma output_bounds {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    n ≤ C.output ∧ C.output < n + C.gates.length := by
  obtain ⟨u, v, huv⟩ := hne
  have hfun : ∀ x, wval C x C.output = graphFun G ∅ x := fun x => congrFun hL.2.1 x
  constructor
  · by_contra hlt
    push Not at hlt
    have h1 := hfun (fun w => decide (w = ⟨C.output, hlt⟩))
    rw [wval_input C _ C.output hlt, graphFun_unit_false] at h1
    simp at h1
  · by_contra hge
    push Not at hge
    have h1 := hfun (pairInput u v)
    rw [wval_ge_len C _ hge, (graphFun_pair_iff u v).mpr huv] at h1
    cases h1

lemma least_inOutputCone {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    ∀ j < C.gates.length, InOutputCone n C j := by
  have ⟨u, _, _⟩ := hne
  have hn0 : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hout := output_bounds hL hne
  intro j hj
  refine ⟨hj, ?_⟩
  by_contra hnot
  push Not at hnot
  have hr : 0 < n + j := by omega
  let C' := delCircuit n C j 0
  have hAO' := delCircuit_isAO2 hL.1 hj hr
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval C' x C'.output = graphFun G ∅ x
    rw [← congrFun hL.2.1 x]
    exact delCircuit_wval_not_inCone hL.1 x hj hr C.output hout.2 hnot.1 (fun _ => hnot.2 hout.1)
  have hsz := hL.2.2 C' hAO' hfun'
  simp only [Circuit.size, C', delCircuit_len n C hj 0] at hsz
  omega

lemma least_has_edge_of_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (k : ℕ) (hk : k<C.gates.length) :
    ∃ u v : Fin n,G.Adj u v := by
  classical
  by_contra hnone
  push Not at hnone
  let Z : Circuit := ⟨[],n⟩
  have hAO : IsAO2 n Z := by simp [IsAO2,AndOrOnly,ReadsBack,Z]
  have hf : circuitFun n Z=graphFun G ∅ := by
    funext x
    simp [circuitFun,Circuit.eval,Circuit.wires,Z,graphFun,hnone,
      List.getD_eq_getElem?_getD]
  have hmin := hL.2.2 Z hAO hf
  have hlen : C.gates.length≤0 := by
    simpa only [Circuit.size,Z,List.length_nil] using hmin
  omega


lemma below_of_or_descendants {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C=graphFun G ∅)
    (h : ℕ) (hcone : InOutputCone n C h)
    (hall : ∀ k<C.gates.length,InCone n C h k → (gateAt C k).op=GateOp.or) :
    BelowF G C h := by
  intro x hx
  have up : ∀ k,(k=h ∨ InCone n C h k) → gateVal n C k x=true := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rintro (rfl | hk)
      · exact hx
      · have hkl := inCone_lt_len hk
        obtain ⟨w,hw,hnw,hwk,hj⟩ := (inCone_iff hkl).mp hk
        have hv := ih (w-n) (by omega) (hj.imp_left Eq.symm)
        have hwv : wval C x w=true := by
          rw [show w=n+(w-n) by omega]
          exact hv
        rw [gate_inputs_eq hAO hkl] at hw
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hw
        rw [gateVal_eq_wval,wval_gate_or hAO x hkl (hall k hkl hk)]
        simp only [Bool.or_eq_true]
        rcases hw with rfl | rfl
        · exact Or.inl hwv
        · exact Or.inr hwv
  have hF := congrFun hfun x
  rw [←hF]
  change wval C x C.output=true
  rcases hcone.2 with ho | ⟨hno,ho⟩
  · rw [ho]
    exact hx
  · have hv := up (C.output-n) (Or.inr ho)
    rw [show C.output=n+(C.output-n) by omega]
    exact hv

lemma least_only_and_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (h : ℕ) (hh : h<C.gates.length)
    (honly : ∀ k<C.gates.length,(gateAt C k).op=GateOp.and → k=h) :
    BelowF G C h := by
  have hne := least_has_edge_of_gate G C hL h hh
  apply below_of_or_descendants G C hL.1 hL.2.1 h (least_inOutputCone hL hne h hh)
  intro k hk hin
  rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
  · have heq := honly k hk hand
    have hlt := inCone_lt hin
    omega
  · exact hor

lemma least_one_and_goal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C)
    (huniq : ∀ i<C.gates.length,∀ j<C.gates.length,
      (gateAt C i).op=GateOp.and → (gateAt C j).op=GateOp.and → i=j) :
    ∀ k<C.gates.length,(gateAt C k).op=GateOp.and → BelowF G C k := by
  intro k hk hand
  apply least_only_and_below G C hL k hk
  intro j hj hjand
  exact huniq j hj k hk hjand hand

end PEqualNP.Outside.L_meta_3754.Deletion

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


namespace PEqualNP.Outside.L_meta_3754.Strict3653

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.SplitCount PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons gt rest ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun idx => w.getD idx false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons gt rest ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [gt.op.eval (gt.inputs.map fun idx => acc.getD idx false)]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih _ hlt]
    simp [List.getD, List.getElem?_append_left hi]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlen : i < (List.ofFn x).length := by simpa using hi
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlen]
  simp [List.getD, hi]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) (gateAt_mem hj)
  unfold opnd
  cases hl : (gateAt C j).inputs with
  | nil => simp [hl] at hlen
  | cons a l =>
    cases l with
    | nil => simp [hl] at hlen
    | cons b l' =>
      cases l' with
      | nil => simp [hl]
      | cons c l'' => simp [hl] at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj (opnd C j b) (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have hg : gateAt C j = C.gates[j] := by
      unfold gateAt
      exact List.getD_eq_getElem _ _ hj
    rw [hg]
    simpa using (List.take_append_drop j C.gates).symm.trans (by
      congr 1
      exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set step : List Bool → Gate → List Bool :=
    fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]
  set pre := (C.gates.take j).foldl step (List.ofFn x)
  have hpre_len : pre.length = n + j := by
    have h1 := foldl_wires_len (C.gates.take j) (List.ofFn x)
    simp only [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at h1
    exact h1
  have h_eq : C.gates.foldl step (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have h_pre_get : ∀ i < n + j, (C.gates.foldl step (List.ofFn x)).getD i false = pre.getD i false := by
    intro i hi
    rw [h_eq]
    have hi1 : i < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ i hi1]
    simp only [step]
    have hi2 : i < pre.length := by omega
    simp [List.getD, List.getElem?_append_left hi2]
  have h_nj : (C.gates.foldl step (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => pre.getD i false) := by
    rw [h_eq]
    have hlt : n + j < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ (n + j) hlt]
    simp only [step]
    have hle : pre.length ≤ n + j := by omega
    simp [List.getD, List.getElem?_append_right hle, hpre_len]
  rw [h_nj, gate_inputs_eq hAO hj]
  have h0 := h_pre_get (opnd C j 0) (opnd_lt hAO hj 0)
  have h1 := h_pre_get (opnd C j 1) (opnd_lt hAO hj 1)
  simp only [List.map_cons, List.map_nil, ← h0, ← h1]

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  have hlen : (C.wires (List.ofFn x)).length ≤ w := by
    rw [wires_length, List.length_ofFn]
    exact hw
  exact List.getD_eq_default _ _ hlen

lemma wval_allTrue {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wval_input C _ w hlt]
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn]
      have h0 : opnd C (w - n) 0 < w := by
        have := opnd_lt hAO hj 0
        omega
      have h1 : opnd C (w - n) 1 < w := by
        have := opnd_lt hAO hj 1
        omega
      have hv0 := ih (opnd C (w - n) 0) h0 (by omega)
      have hv1 := ih (opnd C (w - n) 1) h1 (by omega)
      rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hj) with hop | hop
      · rw [wval_gate_and hAO _ hj hop, hv0, hv1]; rfl
      · rw [wval_gate_or hAO _ hj hop, hv0, hv1]; rfl

lemma wval_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hx
    by_cases hlt : w < n
    · rw [wval_input C x w hlt] at hx
      rw [wval_input C y w hlt]
      exact hxy ⟨w, hlt⟩ hx
    · by_cases hw : w < n + C.gates.length
      · have hj : w - n < C.gates.length := by omega
        have hwn : w = n + (w - n) := by omega
        rw [hwn] at hx ⊢
        have h0 : opnd C (w - n) 0 < w := by
          have := opnd_lt hAO hj 0
          omega
        have h1 : opnd C (w - n) 1 < w := by
          have := opnd_lt hAO hj 1
          omega
        rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hj) with hop | hop
        · rw [wval_gate_and hAO x hj hop, Bool.and_eq_true] at hx
          rw [wval_gate_and hAO y hj hop, Bool.and_eq_true]
          exact ⟨ih _ h0 hx.1, ih _ h1 hx.2⟩
        · rw [wval_gate_or hAO x hj hop, Bool.or_eq_true] at hx
          rw [wval_gate_or hAO y hj hop, Bool.or_eq_true]
          exact hx.elim (fun h => Or.inl (ih _ h0 h)) (fun h => Or.inr (ih _ h1 h))
      · rw [wval_ge_len C x (by omega)] at hx
        cases hx

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons gt rest ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons gt rest ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc gt).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [ih _ hlt]
    simp [coneStep, List.getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones
  simpa using foldl_cones_len n C.gates []

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  unfold InCone at h
  by_contra hge
  have hle : (cones n C).length ≤ j := by rw [cones_length]; omega
  rw [List.getD_eq_default _ _ hle] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have hg : gateAt C j = C.gates[j] := by
      unfold gateAt
      exact List.getD_eq_getElem _ _ hj
    rw [hg]
    simpa using (List.take_append_drop j C.gates).symm.trans (by
      congr 1
      exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set pre := (C.gates.take j).foldl (coneStep n) []
  have hpre_len : pre.length = j := by
    have h1 := foldl_cones_len n (C.gates.take j) []
    simp only [List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at h1
    exact h1
  have h_eq : C.gates.foldl (coneStep n) [] =
      (C.gates.drop (j + 1)).foldl (coneStep n) (coneStep n pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have h_pre_get : ∀ k < j, (C.gates.foldl (coneStep n) []).getD k [] = pre.getD k [] := by
    intro k hk
    rw [h_eq]
    have hk1 : k < (coneStep n pre (gateAt C j)).length := by
      simp only [coneStep, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_cones_getD_lt _ _ _ k hk1]
    have hk2 : k < pre.length := by omega
    simp [coneStep, List.getD, List.getElem?_append_left hk2]
  have h_j : (C.gates.foldl (coneStep n) []).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: pre.getD (w - n) []) := by
    rw [h_eq]
    have hlt : j < (coneStep n pre (gateAt C j)).length := by
      simp only [coneStep, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_cones_getD_lt _ _ _ j hlt]
    have hle : pre.length ≤ j := by omega
    simp [coneStep, List.getD, List.getElem?_append_right hle, hpre_len]
  rw [h_j]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hwm, hwn, hwlt⟩, hmem⟩
    refine ⟨w, hwm, hwn, hwlt, ?_⟩
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · right
      rw [← h_pre_get (w - n) (by omega)] at hmem
      exact hmem
  · rintro ⟨w, hwm, hwn, hwlt, hmem⟩
    refine ⟨w, ⟨hwm, hwn, hwlt⟩, ?_⟩
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · right
      rw [h_pre_get (w - n) (by omega)] at hmem
      exact hmem

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro h
    have hj : j < C.gates.length := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hwn, hwlt, rfl | hsub⟩
    · omega
    · have h1 := ih (w - n) (by omega) hsub
      omega

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_unitInput_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (unitInput v) = false := by
  cases hf : graphFun G ∅ (unitInput v) with
  | false => rfl
  | true =>
    rw [graphFun_iff] at hf
    rcases hf with ⟨u, w, hadj, hu, hw⟩
    simp only [unitInput, decide_eq_true_eq] at hu hw
    subst hu; subst hw
    exact (G.ne_of_adj hadj rfl).elim

lemma graphFun_pairInput_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hadj, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.ne_of_adj hadj rfl).elim
    · exact hadj
    · exact hadj.symm
    · exact (G.ne_of_adj hadj rfl).elim
  · intro hadj
    exact ⟨u, v, hadj, by simp [pairInput], by simp [pairInput]⟩

def tripleInput {n : ℕ} (u w z : Fin n) : Fin n → Bool :=
  fun t => decide (t = u ∨ t = w ∨ t = z)

lemma graphFun_tripleInput_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u w z : Fin n) :
    graphFun G ∅ (tripleInput u w z) = true ↔ G.Adj u w ∨ G.Adj u z ∨ G.Adj w z := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hadj, ha, hb⟩
    simp only [tripleInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact (G.ne_of_adj hadj rfl).elim
    · exact Or.inl hadj
    · exact Or.inr (Or.inl hadj)
    · exact Or.inl hadj.symm
    · exact (G.ne_of_adj hadj rfl).elim
    · exact Or.inr (Or.inr hadj)
    · exact Or.inr (Or.inl hadj.symm)
    · exact Or.inr (Or.inr hadj.symm)
    · exact (G.ne_of_adj hadj rfl).elim
  · rintro (h | h | h)
    · exact ⟨u, w, h, by simp [tripleInput], by simp [tripleInput]⟩
    · exact ⟨u, z, h, by simp [tripleInput], by simp [tripleInput]⟩
    · exact ⟨w, z, h, by simp [tripleInput], by simp [tripleInput]⟩

lemma noFourCycle_unique {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hC4 : NoFourCycle G) {a b z1 z2 : Fin n} (hab : a ≠ b)
    (ha1 : G.Adj a z1) (hb1 : G.Adj b z1) (ha2 : G.Adj a z2) (hb2 : G.Adj b z2) :
    z1 = z2 := by
  have hcard := hC4 a b hab
  have h1 : z1 ∈ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    simp [ha1, hb1]
  have h2 : z2 ∈ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    simp [ha2, hb2]
  exact Finset.card_le_one.mp hcard z1 h1 z2 h2

lemma circuitFun_eq_graphFun_of {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {D : Circuit} (hAO : IsAO2 n D)
    (hle : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true)
    (hge : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  cases hD : circuitFun n D x with
  | true =>
    exact (hle x hD).symm
  | false =>
    cases hF : graphFun G ∅ x with
    | false => rfl
    | true =>
      rw [graphFun_iff] at hF
      rcases hF with ⟨u, v, hadj, hu, hv⟩
      have hp : circuitFun n D (pairInput u v) = true := hge u v hadj
      have hmono : circuitFun n D x = true := wval_mono hAO (fun i hi => by
        simp only [pairInput, decide_eq_true_eq] at hi
        rcases hi with rfl | rfl <;> assumption) D.output hp
      rw [hD] at hmono
      cases hmono

def WireBelowF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true

lemma not_wireBelowF_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    {w : ℕ} (hw : w < n) : ¬ WireBelowF G C w := by
  intro h
  have h1 : wval C (unitInput ⟨w, hw⟩) w = true := by
    rw [wval_input C _ w hw]
    simp [unitInput]
  have h2 := h (unitInput ⟨w, hw⟩) h1
  rw [graphFun_unitInput_false] at h2
  cases h2

lemma wireBelowF_gate_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    WireBelowF G C (n + k) ↔ BelowF G C k := Iff.rfl

def usesG (n : ℕ) (C : Circuit) (g : ℕ) (w : ℕ) : Bool :=
  if w < n then false
  else if w = n + g then true
  else
    let k := w - n
    if k < C.gates.length then
      if h : opnd C k 0 < w ∧ opnd C k 1 < w then
        usesG n C g (opnd C k 0) || usesG n C g (opnd C k 1)
      else false
    else false
termination_by w
decreasing_by
  · exact h.1
  · exact h.2

def varSet (n : ℕ) (C : Circuit) (g : ℕ) (w : ℕ) : Finset (Fin n) :=
  if h : w < n then {⟨w, h⟩}
  else if w = n + g then ∅
  else
    let k := w - n
    if k < C.gates.length then
      if h2 : opnd C k 0 < w ∧ opnd C k 1 < w then
        varSet n C g (opnd C k 0) ∪ varSet n C g (opnd C k 1)
      else ∅
    else ∅
termination_by w
decreasing_by
  · exact h2.1
  · exact h2.2

lemma usesG_input (n : ℕ) (C : Circuit) (g w : ℕ) (hw : w < n) :
    usesG n C g w = false := by
  rw [usesG]; simp [hw]

lemma usesG_g (n : ℕ) (C : Circuit) (g : ℕ) :
    usesG n C g (n + g) = true := by
  rw [usesG]
  have h1 : ¬ n + g < n := by omega
  simp [h1]

lemma usesG_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g k : ℕ)
    (hk : k < C.gates.length) (hkg : k ≠ g) :
    usesG n C g (n + k) = (usesG n C g (opnd C k 0) || usesG n C g (opnd C k 1)) := by
  rw [usesG]
  have h1 : ¬ n + k < n := by omega
  have h3 : n + k - n = k := by omega
  have hlt0 : opnd C k 0 < n + k := opnd_lt hAO hk 0
  have hlt1 : opnd C k 1 < n + k := opnd_lt hAO hk 1
  simp [h1, hkg, h3, hk, hlt0, hlt1]

lemma usesG_lt_g {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g : ℕ) :
    ∀ w < n + g, usesG n C g w = false := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · exact usesG_input n C g w hlt
    · by_cases hk : w - n < C.gates.length
      · have hwn : w = n + (w - n) := by omega
        have hkg : w - n ≠ g := by omega
        rw [hwn, usesG_gate hAO g (w - n) hk hkg]
        have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        rw [ih _ h0 (by omega), ih _ h1 (by omega)]
        rfl
      · rw [usesG]
        have hne : w ≠ n + g := by omega
        simp [hlt, hne, hk]

lemma varSet_input (n : ℕ) (C : Circuit) (g w : ℕ) (hw : w < n) :
    varSet n C g w = {⟨w, hw⟩} := by
  rw [varSet]; simp [hw]

lemma varSet_g (n : ℕ) (C : Circuit) (g : ℕ) :
    varSet n C g (n + g) = ∅ := by
  rw [varSet]
  have h1 : ¬ n + g < n := by omega
  simp [h1]

lemma varSet_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g k : ℕ)
    (hk : k < C.gates.length) (hkg : k ≠ g) :
    varSet n C g (n + k) = varSet n C g (opnd C k 0) ∪ varSet n C g (opnd C k 1) := by
  rw [varSet]
  have h1 : ¬ n + k < n := by omega
  have h3 : n + k - n = k := by omega
  have hlt0 : opnd C k 0 < n + k := opnd_lt hAO hk 0
  have hlt1 : opnd C k 1 < n + k := opnd_lt hAO hk 1
  simp [h1, hkg, h3, hk, hlt0, hlt1]

def zSet (n : ℕ) (C : Circuit) (g : ℕ) : Finset (Fin n) :=
  (Finset.range C.gates.length).biUnion fun a =>
    match (gateAt C a).op with
    | GateOp.and =>
      if a ≠ g then
        (if usesG n C g (opnd C a 0) = true then varSet n C g (opnd C a 1) else ∅) ∪
        (if usesG n C g (opnd C a 1) = true then varSet n C g (opnd C a 0) else ∅)
      else ∅
    | _ => ∅

def delMap (n g r w : ℕ) : ℕ :=
  if w < n + g then w
  else if w = n + g then r
  else w - 1

def delGateMap (g k : ℕ) : ℕ :=
  if k < g then k else k - 1

lemma delMap_gate (n g r k : ℕ) (hkg : k ≠ g) :
    delMap n g r (n + k) = n + delGateMap g k := by
  unfold delMap delGateMap
  split_ifs <;> omega

def delCircuit (n : ℕ) (C : Circuit) (g r : ℕ) : Circuit :=
  { gates := List.ofFn fun i : Fin (C.gates.length - 1) =>
      let src := if i.val < g then i.val else i.val + 1
      let gt := gateAt C src
      ⟨gt.op, gt.inputs.map (delMap n g r)⟩
    output := delMap n g r C.output }

lemma delCircuit_len (n : ℕ) (C : Circuit) (g r : ℕ) :
    (delCircuit n C g r).gates.length = C.gates.length - 1 := by
  simp [delCircuit]

lemma delCircuit_size (n : ℕ) (C : Circuit) (g r : ℕ) :
    (delCircuit n C g r).size ≤ C.size := by
  simp [Circuit.size, delCircuit]

lemma delCircuit_gateAt {n : ℕ} {C : Circuit} {g r i : ℕ} (hi : i < C.gates.length - 1) :
    gateAt (delCircuit n C g r) i =
      let src := if i < g then i else i + 1
      let gt := gateAt C src
      ⟨gt.op, gt.inputs.map (delMap n g r)⟩ := by
  have hlt : i < (delCircuit n C g r).gates.length := by rw [delCircuit_len]; exact hi
  conv_lhs => unfold gateAt
  rw [List.getD_eq_getElem _ _ hlt]
  simp [delCircuit]

lemma delCircuit_gateAt_src {n : ℕ} {C : Circuit} {g r k : ℕ}
    (hg : g < C.gates.length) (hk : k < C.gates.length) (hkg : k ≠ g) :
    gateAt (delCircuit n C g r) (delGateMap g k) =
      ⟨(gateAt C k).op, (gateAt C k).inputs.map (delMap n g r)⟩ := by
  have hi : delGateMap g k < C.gates.length - 1 := by
    unfold delGateMap; split_ifs <;> omega
  rw [delCircuit_gateAt hi]
  have hsrc : (if delGateMap g k < g then delGateMap g k else delGateMap g k + 1) = k := by
    unfold delGateMap; split_ifs <;> omega
  simp [hsrc]

lemma delCircuit_isAO2 {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) :
    IsAO2 n (delCircuit n C g r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [delCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    have hsrc : (if i.val < g then i.val else i.val + 1) < C.gates.length := by
      split_ifs <;> omega
    exact hAO.1 (gateAt C (if i.val < g then i.val else i.val + 1)) (gateAt_mem hsrc)
  · intro i hi w hw
    rw [delCircuit_len] at hi
    rw [delCircuit_gateAt hi] at hw
    simp only [List.mem_map] at hw
    rcases hw with ⟨u, hu, rfl⟩
    by_cases hig : i < g
    · simp only [hig, ↓reduceIte] at hu
      have hult : u < n + i := hAO.2.1 i (by omega) u hu
      unfold delMap
      split_ifs <;> omega
    · simp only [hig, ↓reduceIte] at hu
      have hult : u < n + (i + 1) := hAO.2.1 (i + 1) (by omega) u hu
      unfold delMap
      split_ifs <;> omega
  · intro gt hgt
    simp only [delCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    have hsrc : (if i.val < g then i.val else i.val + 1) < C.gates.length := by
      split_ifs <;> omega
    simp [hAO.2.2 _ (gateAt_mem hsrc)]

lemma delCircuit_opnd {n : ℕ} {C : Circuit} {g r k : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hk : k < C.gates.length) (hkg : k ≠ g) (b : Fin 2) :
    opnd (delCircuit n C g r) (delGateMap g k) b = delMap n g r (opnd C k b) := by
  unfold opnd
  rw [delCircuit_gateAt_src hg hk hkg, gate_inputs_eq hAO hk]
  fin_cases b <;> simp [opnd]

lemma delCircuit_wval_lt {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) (x : Fin n → Bool) :
    ∀ w < n + g, wval (delCircuit n C g r) x w = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hg hr
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wval_input _ x w hlt, wval_input _ x w hlt]
    · have hk : w - n < g := by omega
      have hklt : w - n < C.gates.length := by omega
      have hkg : w - n ≠ g := by omega
      have hwn : w = n + (w - n) := by omega
      have hdgm : delGateMap g (w - n) = w - n := by simp [delGateMap, hk]
      have hk' : w - n < (delCircuit n C g r).gates.length := by rw [delCircuit_len]; omega
      have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hklt 0; omega
      have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hklt 1; omega
      have hop0 : opnd (delCircuit n C g r) (w - n) 0 = opnd C (w - n) 0 := by
        conv_lhs => rw [← hdgm]
        rw [delCircuit_opnd hAO hg hklt hkg 0]
        unfold delMap; split_ifs <;> omega
      have hop1 : opnd (delCircuit n C g r) (w - n) 1 = opnd C (w - n) 1 := by
        conv_lhs => rw [← hdgm]
        rw [delCircuit_opnd hAO hg hklt hkg 1]
        unfold delMap; split_ifs <;> omega
      have hgate : (gateAt (delCircuit n C g r) (w - n)).op = (gateAt C (w - n)).op := by
        conv_lhs => rw [← hdgm]
        rw [delCircuit_gateAt_src hg hklt hkg]
      rw [hwn]
      rcases hAO.1 _ (gateAt_mem hklt) with hop | hop
      · rw [wval_gate_and hAO' x hk' (hgate.trans hop), wval_gate_and hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega), ih _ h1lt (by omega)]
      · rw [wval_gate_or hAO' x hk' (hgate.trans hop), wval_gate_or hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega), ih _ h1lt (by omega)]

lemma delCircuit_wval_le {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) (x : Fin n → Bool)
    (hle : wval C x r = true → gateVal n C g x = true) :
    ∀ w < n + C.gates.length, wval (delCircuit n C g r) x (delMap n g r w) = true → wval C x w = true := by
  have hAO' := delCircuit_isAO2 hAO hg hr
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hD
    by_cases hlt : w < n + g
    · have hm : delMap n g r w = w := by simp [delMap, hlt]
      rw [hm, delCircuit_wval_lt hAO hg hr x w hlt] at hD
      exact hD
    · by_cases hwg : w = n + g
      · subst hwg
        have hm : delMap n g r (n + g) = r := by simp [delMap]
        rw [hm, delCircuit_wval_lt hAO hg hr x r hr] at hD
        exact hle hD
      · have hk : w - n < C.gates.length := by omega
        have hkg : w - n ≠ g := by omega
        have hwn : w = n + (w - n) := by omega
        have hdm : delMap n g r w = n + delGateMap g (w - n) := by
          conv_lhs => rw [hwn]
          exact delMap_gate n g r (w - n) hkg
        have hk' : delGateMap g (w - n) < (delCircuit n C g r).gates.length := by
          rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
        have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        have hgate : (gateAt (delCircuit n C g r) (delGateMap g (w - n))).op = (gateAt C (w - n)).op := by
          rw [delCircuit_gateAt_src hg hk hkg]
        rw [hdm] at hD
        rw [hwn]
        rcases hAO.1 _ (gateAt_mem hk) with hop | hop
        · rw [wval_gate_and hAO' x hk' (hgate.trans hop), Bool.and_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1] at hD
          rw [wval_gate_and hAO x hk hop, Bool.and_eq_true]
          exact ⟨ih _ h0lt (by omega) hD.1, ih _ h1lt (by omega) hD.2⟩
        · rw [wval_gate_or hAO' x hk' (hgate.trans hop), Bool.or_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1] at hD
          rw [wval_gate_or hAO x hk hop, Bool.or_eq_true]
          exact hD.elim (fun h => Or.inl (ih _ h0lt (by omega) h))
            (fun h => Or.inr (ih _ h1lt (by omega) h))

lemma delCircuit_wval_ge {n : ℕ} {C : Circuit} {g r : ℕ}
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g) (x : Fin n → Bool)
    (hge : gateVal n C g x = true → wval C x r = true) :
    ∀ w < n + C.gates.length, wval C x w = true → wval (delCircuit n C g r) x (delMap n g r w) = true := by
  have hAO' := delCircuit_isAO2 hAO hg hr
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hC
    by_cases hlt : w < n + g
    · have hm : delMap n g r w = w := by simp [delMap, hlt]
      rw [hm, delCircuit_wval_lt hAO hg hr x w hlt]
      exact hC
    · by_cases hwg : w = n + g
      · subst hwg
        have hm : delMap n g r (n + g) = r := by simp [delMap]
        rw [hm, delCircuit_wval_lt hAO hg hr x r hr]
        exact hge hC
      · have hk : w - n < C.gates.length := by omega
        have hkg : w - n ≠ g := by omega
        have hwn : w = n + (w - n) := by omega
        have hdm : delMap n g r w = n + delGateMap g (w - n) := by
          conv_lhs => rw [hwn]
          exact delMap_gate n g r (w - n) hkg
        have hk' : delGateMap g (w - n) < (delCircuit n C g r).gates.length := by
          rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
        have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        have hgate : (gateAt (delCircuit n C g r) (delGateMap g (w - n))).op = (gateAt C (w - n)).op := by
          rw [delCircuit_gateAt_src hg hk hkg]
        rw [hdm]
        rw [hwn] at hC
        rcases hAO.1 _ (gateAt_mem hk) with hop | hop
        · rw [wval_gate_and hAO x hk hop, Bool.and_eq_true] at hC
          rw [wval_gate_and hAO' x hk' (hgate.trans hop), Bool.and_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1]
          exact ⟨ih _ h0lt (by omega) hC.1, ih _ h1lt (by omega) hC.2⟩
        · rw [wval_gate_or hAO x hk hop, Bool.or_eq_true] at hC
          rw [wval_gate_or hAO' x hk' (hgate.trans hop), Bool.or_eq_true,
            delCircuit_opnd hAO hg hk hkg 0, delCircuit_opnd hAO hg hk hkg 1]
          exact hC.elim (fun h => Or.inl (ih _ h0lt (by omega) h))
            (fun h => Or.inr (ih _ h1lt (by omega) h))

def isTwoSided {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g w : ℕ) : Prop :=
  w < n + C.gates.length ∧ ¬ WireBelowF G C w ∧
    (∃ u ∈ varSet n C g w, s u = s v) ∧ (∃ u ∈ varSet n C g w, s u ≠ s v)

def isRSided {n : ℕ} (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g w : ℕ) : Prop :=
  ∀ u ∈ varSet n C g w, s u ≠ s v

def restrictMap {n : ℕ} (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g w : ℕ) : ℕ :=
  if ∀ u ∈ varSet n C g w, s u ≠ s v then v.val else w

def restrictTwoSided {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g : ℕ) : Circuit :=
  { gates := List.ofFn fun i : Fin C.gates.length =>
      let gt := gateAt C i.val
      if ¬ BelowF G C i.val ∧ (∃ u ∈ varSet n C g (n + i.val), s u = s v) ∧
          (∃ u ∈ varSet n C g (n + i.val), s u ≠ s v) then
        ⟨gt.op, gt.inputs.map (restrictMap C s v g)⟩
      else gt
    output := C.output }

lemma restrictTwoSided_len {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g : ℕ) :
    (restrictTwoSided G C s v g).gates.length = C.gates.length := by
  simp [restrictTwoSided]

lemma restrictTwoSided_gateAt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (v : Fin n) (g k : ℕ) (hk : k < C.gates.length) :
    gateAt (restrictTwoSided G C s v g) k =
      if ¬ BelowF G C k ∧ (∃ u ∈ varSet n C g (n + k), s u = s v) ∧
          (∃ u ∈ varSet n C g (n + k), s u ≠ s v) then
        ⟨(gateAt C k).op, (gateAt C k).inputs.map (restrictMap C s v g)⟩
      else gateAt C k := by
  have hlt : k < (restrictTwoSided G C s v g).gates.length := by rw [restrictTwoSided_len]; exact hk
  conv_lhs => unfold gateAt
  rw [List.getD_eq_getElem _ _ hlt]
  simp [restrictTwoSided]

lemma restrictTwoSided_isAO2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (s : Fin n → Bool) (v : Fin n) (g : ℕ) :
    IsAO2 n (restrictTwoSided G C s v g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [restrictTwoSided, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    split_ifs
    · exact hAO.1 (gateAt C i.val) (gateAt_mem i.isLt)
    · exact hAO.1 (gateAt C i.val) (gateAt_mem i.isLt)
  · intro k hk w hw
    rw [restrictTwoSided_len] at hk
    rw [restrictTwoSided_gateAt G C s v g k hk] at hw
    split_ifs at hw with hts
    · simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      unfold restrictMap
      split_ifs
      · omega
      · exact hAO.2.1 k hk u hu
    · exact hAO.2.1 k hk w hw
  · intro gt hgt
    simp only [restrictTwoSided, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    split_ifs
    · simp [hAO.2.2 _ (gateAt_mem i.isLt)]
    · exact hAO.2.2 _ (gateAt_mem i.isLt)

def remapC (n jb g w : ℕ) : ℕ :=
  if w < n + jb then w
  else if w < n + g then w - 1
  else w

def remapCGate (jb g k : ℕ) : ℕ :=
  if k < jb then k
  else if k < g then k - 1
  else k

lemma remapC_gate (n jb g k : ℕ) (hkjb : k ≠ jb) :
    remapC n jb g (n + k) = n + remapCGate jb g k := by
  unfold remapC remapCGate
  split_ifs <;> omega

def rewriteCircuit (n : ℕ) (C : Circuit) (jb g aW : ℕ) (v m : Fin n) : Circuit :=
  { gates := List.ofFn fun i : Fin C.gates.length =>
      if i.val < jb then
        gateAt C i.val
      else if i.val + 1 < g then
        let gt := gateAt C (i.val + 1)
        ⟨gt.op, gt.inputs.map (remapC n jb g)⟩
      else if i.val + 1 = g then
        ⟨GateOp.and, [remapC n jb g aW, m.val]⟩
      else if i.val = g then
        ⟨GateOp.or, [v.val, n + (g - 1)]⟩
      else
        let gt := gateAt C i.val
        ⟨gt.op, gt.inputs.map (remapC n jb g)⟩
    output := C.output }

lemma rewriteCircuit_len (n : ℕ) (C : Circuit) (jb g aW : ℕ) (v m : Fin n) :
    (rewriteCircuit n C jb g aW v m).gates.length = C.gates.length := by
  simp [rewriteCircuit]

lemma rewriteCircuit_size (n : ℕ) (C : Circuit) (jb g aW : ℕ) (v m : Fin n) :
    (rewriteCircuit n C jb g aW v m).size ≤ C.size := by
  simp [Circuit.size, rewriteCircuit]

lemma rewriteCircuit_gateAt {n : ℕ} {C : Circuit} {jb g aW i : ℕ} {v m : Fin n}
    (hi : i < C.gates.length) :
    gateAt (rewriteCircuit n C jb g aW v m) i =
      if i < jb then
        gateAt C i
      else if i + 1 < g then
        let gt := gateAt C (i + 1)
        ⟨gt.op, gt.inputs.map (remapC n jb g)⟩
      else if i + 1 = g then
        ⟨GateOp.and, [remapC n jb g aW, m.val]⟩
      else if i = g then
        ⟨GateOp.or, [v.val, n + (g - 1)]⟩
      else
        let gt := gateAt C i
        ⟨gt.op, gt.inputs.map (remapC n jb g)⟩ := by
  have hlt : i < (rewriteCircuit n C jb g aW v m).gates.length := by rw [rewriteCircuit_len]; exact hi
  conv_lhs => unfold gateAt
  rw [List.getD_eq_getElem _ _ hlt]
  simp [rewriteCircuit]

lemma rewriteCircuit_isAO2 {n : ℕ} {C : Circuit} {jb g aW : ℕ} (v m : Fin n)
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs) :
    IsAO2 n (rewriteCircuit n C jb g aW v m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [rewriteCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    split_ifs with h1 h2 h3 h4
    · exact hAO.1 (gateAt C i.val) (gateAt_mem i.isLt)
    · exact hAO.1 (gateAt C (i.val + 1)) (gateAt_mem (by omega))
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact hAO.1 (gateAt C i.val) (gateAt_mem i.isLt)
  · intro i hi w hw
    rw [rewriteCircuit_len] at hi
    rw [rewriteCircuit_gateAt hi] at hw
    split_ifs at hw with h1 h2 h3 h4
    · exact hAO.2.1 i hi w hw
    · simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult := hAO.2.1 (i + 1) (by omega) u hu
      have hune : u ≠ n + jb := fun heq => hno (i + 1) (by omega) (by omega) (heq ▸ hu)
      unfold remapC
      split_ifs <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · unfold remapC; split_ifs <;> omega
      · omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    · simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult := hAO.2.1 i hi u hu
      unfold remapC
      split_ifs <;> omega
  · intro gt hgt
    simp only [rewriteCircuit, List.mem_ofFn] at hgt
    rcases hgt with ⟨i, rfl⟩
    split_ifs with h1 h2 h3 h4
    · exact hAO.2.2 (gateAt C i.val) (gateAt_mem i.isLt)
    · have hlt2 : i.val + 1 < C.gates.length := by omega
      simp [hAO.2.2 (gateAt C (i.val + 1)) (gateAt_mem hlt2)]
    · rfl
    · rfl
    · simp [hAO.2.2 (gateAt C i.val) (gateAt_mem i.isLt)]

lemma rewriteCircuit_wval_lt_g {n : ℕ} {C : Circuit} {jb g aW : ℕ} {v m : Fin n}
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs)
    (x : Fin n → Bool) :
    ∀ w < n + g, w ≠ n + jb → wval (rewriteCircuit n C jb g aW v m) x (remapC n jb g w) = wval C x w := by
  have hAO' := rewriteCircuit_isAO2 v m hAO hjbg hg haWlt haWne hno
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hwne
    by_cases hlt : w < n
    · have hm : remapC n jb g w = w := by unfold remapC; split_ifs <;> omega
      rw [hm, wval_input _ x w hlt, wval_input _ x w hlt]
    · have hk : w - n < g := by omega
      have hklt : w - n < C.gates.length := by omega
      have hkjb : w - n ≠ jb := by omega
      have hkg : w - n ≠ g := by omega
      have hwn : w = n + (w - n) := by omega
      have hrm : remapC n jb g w = n + remapCGate jb g (w - n) := by
        conv_lhs => rw [hwn]
        exact remapC_gate n jb g (w - n) hkjb
      have hi : remapCGate jb g (w - n) < (rewriteCircuit n C jb g aW v m).gates.length := by
        rw [rewriteCircuit_len]; unfold remapCGate; split_ifs <;> omega
      have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hklt 0; omega
      have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hklt 1; omega
      have h0ne : opnd C (w - n) 0 ≠ n + jb :=
        fun heq => hno (w - n) hklt hkg (heq ▸ opnd_mem hAO hklt 0)
      have h1ne : opnd C (w - n) 1 ≠ n + jb :=
        fun heq => hno (w - n) hklt hkg (heq ▸ opnd_mem hAO hklt 1)
      have hgt : gateAt (rewriteCircuit n C jb g aW v m) (remapCGate jb g (w - n)) =
          ⟨(gateAt C (w - n)).op, (gateAt C (w - n)).inputs.map (remapC n jb g)⟩ := by
        rw [rewriteCircuit_gateAt (by simpa [rewriteCircuit_len] using hi)]
        unfold remapCGate
        by_cases hltjb : w - n < jb
        · simp only [hltjb, ↓reduceIte]
          have h0m : remapC n jb g (opnd C (w - n) 0) = opnd C (w - n) 0 := by
            have := opnd_lt hAO hklt 0; unfold remapC; split_ifs <;> omega
          have h1m : remapC n jb g (opnd C (w - n) 1) = opnd C (w - n) 1 := by
            have := opnd_lt hAO hklt 1; unfold remapC; split_ifs <;> omega
          have hinp := gate_inputs_eq hAO hklt
          cases hc : gateAt C (w - n) with
          | mk op ins =>
            rw [hc] at hinp
            dsimp at hinp
            rw [hinp]
            simp [h0m, h1m]
        · have hif1 : ¬ w - n - 1 < jb := by omega
          have hif2 : w - n - 1 + 1 < g := by omega
          have heq : w - n - 1 + 1 = w - n := by omega
          simp only [hltjb, hk, ↓reduceIte, hif1, hif2, heq]
      have hop0 : opnd (rewriteCircuit n C jb g aW v m) (remapCGate jb g (w - n)) 0 =
          remapC n jb g (opnd C (w - n) 0) := by
        unfold opnd; rw [hgt, gate_inputs_eq hAO hklt]; rfl
      have hop1 : opnd (rewriteCircuit n C jb g aW v m) (remapCGate jb g (w - n)) 1 =
          remapC n jb g (opnd C (w - n) 1) := by
        unfold opnd; rw [hgt, gate_inputs_eq hAO hklt]; rfl
      have hop_eq : (gateAt (rewriteCircuit n C jb g aW v m) (remapCGate jb g (w - n))).op =
          (gateAt C (w - n)).op := by rw [hgt]
      rw [hrm]
      conv_rhs => rw [hwn]
      rcases hAO.1 _ (gateAt_mem hklt) with hop | hop
      · rw [wval_gate_and hAO' x hi (hop_eq.trans hop), wval_gate_and hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega) h0ne, ih _ h1lt (by omega) h1ne]
      · rw [wval_gate_or hAO' x hi (hop_eq.trans hop), wval_gate_or hAO x hklt hop,
          hop0, hop1, ih _ h0lt (by omega) h0ne, ih _ h1lt (by omega) h1ne]

lemma rewriteCircuit_wval_and {n : ℕ} {C : Circuit} {jb g aW : ℕ} {v m : Fin n}
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs)
    (x : Fin n → Bool) :
    gateVal n (rewriteCircuit n C jb g aW v m) (g - 1) x = (wval C x aW && x m) := by
  have hAO' := rewriteCircuit_isAO2 v m hAO hjbg hg haWlt haWne hno
  have hi : g - 1 < (rewriteCircuit n C jb g aW v m).gates.length := by
    rw [rewriteCircuit_len]; omega
  have hgt : gateAt (rewriteCircuit n C jb g aW v m) (g - 1) =
      ⟨GateOp.and, [remapC n jb g aW, m.val]⟩ := by
    rw [rewriteCircuit_gateAt (by omega)]
    have h1 : ¬ g - 1 < jb := by omega
    have h3 : g - 1 + 1 = g := by omega
    simp [h1, h3]
  have hop : (gateAt (rewriteCircuit n C jb g aW v m) (g - 1)).op = GateOp.and := by rw [hgt]
  have hop0 : opnd (rewriteCircuit n C jb g aW v m) (g - 1) 0 = remapC n jb g aW := by
    unfold opnd; rw [hgt]; rfl
  have hop1 : opnd (rewriteCircuit n C jb g aW v m) (g - 1) 1 = m.val := by
    unfold opnd; rw [hgt]; rfl
  change wval (rewriteCircuit n C jb g aW v m) x (n + (g - 1)) = _
  rw [wval_gate_and hAO' x hi hop, hop0, hop1,
    rewriteCircuit_wval_lt_g hAO hjbg hg haWlt haWne hno x aW haWlt haWne,
    wval_input _ x m.val m.isLt]

lemma rewriteCircuit_wval_g {n : ℕ} {C : Circuit} {jb g aW : ℕ} {v m : Fin n}
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs)
    (x : Fin n → Bool) :
    gateVal n (rewriteCircuit n C jb g aW v m) g x = (x v || (wval C x aW && x m)) := by
  have hAO' := rewriteCircuit_isAO2 v m hAO hjbg hg haWlt haWne hno
  have hi : g < (rewriteCircuit n C jb g aW v m).gates.length := by
    rw [rewriteCircuit_len]; exact hg
  have hgt : gateAt (rewriteCircuit n C jb g aW v m) g =
      ⟨GateOp.or, [v.val, n + (g - 1)]⟩ := by
    rw [rewriteCircuit_gateAt hg]
    have h1 : ¬ g < jb := by omega
    have h2 : ¬ g + 1 < g := by omega
    simp [h1, h2]
  have hop : (gateAt (rewriteCircuit n C jb g aW v m) g).op = GateOp.or := by rw [hgt]
  have hop0 : opnd (rewriteCircuit n C jb g aW v m) g 0 = v.val := by
    unfold opnd; rw [hgt]; rfl
  have hop1 : opnd (rewriteCircuit n C jb g aW v m) g 1 = n + (g - 1) := by
    unfold opnd; rw [hgt]; rfl
  change wval (rewriteCircuit n C jb g aW v m) x (n + g) = _
  rw [wval_gate_or hAO' x hi hop, hop0, hop1, wval_input _ x v.val v.isLt]
  exact congrArg (x v || ·) (rewriteCircuit_wval_and hAO hjbg hg haWlt haWne hno x)

lemma rewriteCircuit_wval_le {n : ℕ} {C : Circuit} {jb g aW : ℕ} {v m : Fin n}
    (hAO : IsAO2 n C) (hjbg : jb < g) (hg : g < C.gates.length)
    (haWlt : aW < n + g) (haWne : aW ≠ n + jb)
    (hno : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs)
    (x : Fin n → Bool)
    (hle_g : (x v || (wval C x aW && x m)) = true → gateVal n C g x = true) :
    ∀ w < n + C.gates.length, w ≠ n + jb →
      wval (rewriteCircuit n C jb g aW v m) x (remapC n jb g w) = true → wval C x w = true := by
  have hAO' := rewriteCircuit_isAO2 v m hAO hjbg hg haWlt haWne hno
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hwne hD
    by_cases hlt : w < n + g
    · rw [rewriteCircuit_wval_lt_g hAO hjbg hg haWlt haWne hno x w hlt hwne] at hD
      exact hD
    · by_cases hwg : w = n + g
      · subst hwg
        have hm : remapC n jb g (n + g) = n + g := by unfold remapC; split_ifs <;> omega
        rw [hm] at hD
        change gateVal n (rewriteCircuit n C jb g aW v m) g x = true at hD
        rw [rewriteCircuit_wval_g hAO hjbg hg haWlt haWne hno x] at hD
        exact hle_g hD
      · have hk : w - n < C.gates.length := by omega
        have hkg : w - n ≠ g := by omega
        have hgt_g : g < w - n := by omega
        have hwn : w = n + (w - n) := by omega
        have hm : remapC n jb g w = n + (w - n) := by unfold remapC; split_ifs <;> omega
        have hi : w - n < (rewriteCircuit n C jb g aW v m).gates.length := by
          rw [rewriteCircuit_len]; exact hk
        have hgt : gateAt (rewriteCircuit n C jb g aW v m) (w - n) =
            ⟨(gateAt C (w - n)).op, (gateAt C (w - n)).inputs.map (remapC n jb g)⟩ := by
          rw [rewriteCircuit_gateAt hk]
          have h1 : ¬ w - n < jb := by omega
          have h2 : ¬ w - n + 1 < g := by omega
          have h3 : w - n + 1 ≠ g := by omega
          simp [h1, h2, h3, hkg]
        have hop0 : opnd (rewriteCircuit n C jb g aW v m) (w - n) 0 =
            remapC n jb g (opnd C (w - n) 0) := by
          unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
        have hop1 : opnd (rewriteCircuit n C jb g aW v m) (w - n) 1 =
            remapC n jb g (opnd C (w - n) 1) := by
          unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
        have hop_eq : (gateAt (rewriteCircuit n C jb g aW v m) (w - n)).op = (gateAt C (w - n)).op := by
          rw [hgt]
        have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
        have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
        have h0ne : opnd C (w - n) 0 ≠ n + jb :=
          fun heq => hno (w - n) hk hkg (heq ▸ opnd_mem hAO hk 0)
        have h1ne : opnd C (w - n) 1 ≠ n + jb :=
          fun heq => hno (w - n) hk hkg (heq ▸ opnd_mem hAO hk 1)
        rw [hm] at hD
        rw [hwn]
        rcases hAO.1 _ (gateAt_mem hk) with hop | hop
        · rw [wval_gate_and hAO' x hi (hop_eq.trans hop), Bool.and_eq_true, hop0, hop1] at hD
          rw [wval_gate_and hAO x hk hop, Bool.and_eq_true]
          exact ⟨ih _ h0lt (by omega) h0ne hD.1, ih _ h1lt (by omega) h1ne hD.2⟩
        · rw [wval_gate_or hAO' x hi (hop_eq.trans hop), Bool.or_eq_true, hop0, hop1] at hD
          rw [wval_gate_or hAO x hk hop, Bool.or_eq_true]
          exact hD.elim (fun h => Or.inl (ih _ h0lt (by omega) h0ne h))
            (fun h => Or.inr (ih _ h1lt (by omega) h1ne h))

lemma or_and_or_iff {a1 a2 r1 r2 : Prop} :
    ((a1 ∨ r1) ∨ (a2 ∨ r2)) ↔ ((a1 ∨ a2) ∨ (r1 ∨ r2)) := by
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

lemma bool_eq_of_ne_ne {a b c : Bool} (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

structure Exceptional {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (g aW bW : ℕ) (v m : Fin n) : Prop where
  aBound : aW<n+g
  bBound : bW<n+g
  bGate : n≤bW
  distinct : aW≠bW
  aMember : aW∈(gateAt C g).inputs
  bMember : bW∈(gateAt C g).inputs
  pureA : ∀x : Fin n → Bool,wval C x aW=true ↔ ∃u∈varSet n C g aW,x u=true
  pureB : ∀x : Fin n → Bool,wval C x bW=true ↔ ∃u∈varSet n C g bW,x u=true
  gateProduct : ∀x : Fin n → Bool,gateVal n C g x=(wval C x aW && wval C x bW)
  sharedOnlyV : ∀u∈varSet n C g aW,u∈varSet n C g bW → u=v
  vInA : v∈varSet n C g aW
  vInB : v∈varSet n C g bW
  mInB : m∈varSet n C g bW
  otherA : ∃u∈varSet n C g aW,u≠v
  adjacentA : ∀u∈varSet n C g aW,G.Adj u m
  colorA : ∀u∈varSet n C g aW,s u=s v
  privateB : ∀k<C.gates.length,k≠g → bW∉(gateAt C k).inputs
  mReader : ∃a<C.gates.length,(gateAt C a).op=GateOp.and ∧ a≠g ∧
    ((usesG n C g (opnd C a 0)=true ∧ m∈varSet n C g (opnd C a 1)) ∨
     (usesG n C g (opnd C a 1)=true ∧ m∈varSet n C g (opnd C a 0)))
  oppositeUnique : ∀z∈varSet n C g bW,z∈zSet n C g → z=m
  dirtyWireFormula : ∀w<n+C.gates.length,¬WireBelowF G C w → ∀x : Fin n → Bool,
    wval C x w=true ↔ (usesG n C g w=true ∧ gateVal n C g x=true) ∨
      ∃u∈varSet n C g w,x u=true

lemma delCircuit_size_strict (n : ℕ) (C : Circuit) (g r : ℕ) (hg : g<C.gates.length) :
    (delCircuit n C g r).size<C.size := by
  change (delCircuit n C g r).gates.length<C.gates.length
  rw [delCircuit_len]
  omega

set_option maxHeartbeats 800000 in
lemma main :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C →
      (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) →
      (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) →
      g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g →
      (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) →
      (∃ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput v) = true) →
      (∀(aW bW : ℕ)(v m : Fin n),Exceptional G C s g aW bW v m → False) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
        PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        ∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.BelowF G D k := by
  intro n G _ C s g h_bip h_c4 hAO h_eq h_lift h_no_imp h_cone hg_lt hg_and hg_dirty h_clean_and h_unit h_exception
  rcases h_unit with ⟨v, hv_g⟩
  have h_out_below : WireBelowF G C C.output := by
    intro x hx
    change circuitFun n C x = true at hx
    rw [h_eq] at hx
    exact hx
  have h_out_gt_g : n + g < C.output ∧ C.output < n + C.gates.length := by
    have hc := h_cone g hg_lt
    rcases hc.2 with hout | ⟨hnle, hinc⟩
    · exfalso
      apply hg_dirty
      intro x hx
      have : wval C x C.output = true := by rw [hout]; exact hx
      exact h_out_below x this
    · have hlt_len : C.output - n < C.gates.length := inCone_lt_len hinc
      have hgt : g < C.output - n := inCone_lt hinc
      omega
  have h_out_below_gate : BelowF G C (C.output - n) := by
    intro x hx
    apply h_out_below x
    have : n + (C.output - n) = C.output := by omega
    rw [← this]
    exact hx
  have h_dirty_or : ∀ k < C.gates.length, ¬ BelowF G C k → k ≠ g → (gateAt C k).op = GateOp.or := by
    intro k hk hdirty hkg
    rcases hAO.1 _ (gateAt_mem hk) with hop | hop
    · exact (hdirty (h_clean_and k hk hop hkg)).elim
    · exact hop
  have h_dirty_inputs : ∀ k < C.gates.length, ¬ BelowF G C k → ∀ b : Fin 2, ¬ WireBelowF G C (opnd C k b) := by
    intro k hk hdirty b hwb
    rcases hAO.1 _ (gateAt_mem hk) with hop | hop
    · exact h_no_imp k hk hop (opnd C k b) (opnd_mem hAO hk b) hwb
    · apply h_lift
      refine ⟨k, hk, b, h_cone k hk, hop, hdirty, hwb, fun _ => true, ?_⟩
      exact wval_allTrue hAO (opnd C k b) (by have := opnd_lt hAO hk b; omega)
  have h_clean_or_inputs : ∀ k < C.gates.length, BelowF G C k → (gateAt C k).op = GateOp.or →
      ∀ b : Fin 2, n ≤ opnd C k b ∧ opnd C k b - n < k ∧ BelowF G C (opnd C k b - n) := by
    intro k hk hbf hop b
    have hwb : WireBelowF G C (opnd C k b) := by
      intro x hx
      apply hbf x
      change wval C x (n + k) = true
      rw [wval_gate_or hAO x hk hop, Bool.or_eq_true]
      fin_cases b
      · exact Or.inl hx
      · exact Or.inr hx
    have hge : n ≤ opnd C k b := by
      by_contra hlt
      exact not_wireBelowF_input G C (by omega) hwb
    have hlt := opnd_lt hAO hk b
    refine ⟨hge, by omega, ?_⟩
    intro x hx
    apply hwb x
    have : n + (opnd C k b - n) = opnd C k b := by omega
    rw [← this]
    exact hx
  have h_wval_dirty : ∀ w < n + C.gates.length, ¬ WireBelowF G C w → ∀ x : Fin n → Bool,
      wval C x w = true ↔ (usesG n C g w = true ∧ gateVal n C g x = true) ∨ (∃ u ∈ varSet n C g w, x u = true) := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw hdw x
      by_cases hlt : w < n
      · rw [wval_input C x w hlt, usesG_input n C g w hlt, varSet_input n C g w hlt]
        simp
      · by_cases hwg : w = n + g
        · subst hwg
          rw [usesG_g, varSet_g]
          simp [gateVal, wval]
        · have hk : w - n < C.gates.length := by omega
          have hkg : w - n ≠ g := by omega
          have hwn : w = n + (w - n) := by omega
          have hdk : ¬ BelowF G C (w - n) := by
            intro hbf; apply hdw; rw [hwn]; exact hbf
          have hop : (gateAt C (w - n)).op = GateOp.or := h_dirty_or (w - n) hk hdk hkg
          have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
          have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
          have h0d := h_dirty_inputs (w - n) hk hdk 0
          have h1d := h_dirty_inputs (w - n) hk hdk 1
          have ih0 := ih _ h0lt (by omega) h0d x
          have ih1 := ih _ h1lt (by omega) h1d x
          rw [hwn, wval_gate_or hAO x hk hop, Bool.or_eq_true,
            usesG_gate hAO g (w - n) hk hkg, varSet_gate hAO g (w - n) hk hkg, ih0, ih1]
          simp only [Bool.or_eq_true, Finset.mem_union, or_and_right, exists_or]
          exact or_and_or_iff
  have h_varSet_nonempty : ∀ w < n + C.gates.length, ¬ WireBelowF G C w → usesG n C g w = false →
      (varSet n C g w).Nonempty := by
    intro w hw hdw hug
    have ht := (h_wval_dirty w hw hdw (fun _ => true)).mp (wval_allTrue hAO w hw)
    rw [hug] at ht
    rcases ht with ⟨hfalse, _⟩ | ⟨u, hu, _⟩
    · cases hfalse
    · exact ⟨u, hu⟩
  have h_g_op0_lt : opnd C g 0 < n + g := opnd_lt hAO hg_lt 0
  have h_g_op1_lt : opnd C g 1 < n + g := opnd_lt hAO hg_lt 1
  have h_g_op0_dirty : ¬ WireBelowF G C (opnd C g 0) := h_dirty_inputs g hg_lt hg_dirty 0
  have h_g_op1_dirty : ¬ WireBelowF G C (opnd C g 1) := h_dirty_inputs g hg_lt hg_dirty 1
  have h_g_op0_val : ∀ x, wval C x (opnd C g 0) = true ↔ ∃ u ∈ varSet n C g (opnd C g 0), x u = true := by
    intro x
    have h := h_wval_dirty (opnd C g 0) (by omega) h_g_op0_dirty x
    rw [usesG_lt_g hAO g _ h_g_op0_lt] at h
    simpa using h
  have h_g_op1_val : ∀ x, wval C x (opnd C g 1) = true ↔ ∃ u ∈ varSet n C g (opnd C g 1), x u = true := by
    intro x
    have h := h_wval_dirty (opnd C g 1) (by omega) h_g_op1_dirty x
    rw [usesG_lt_g hAO g _ h_g_op1_lt] at h
    simpa using h
  have h_g_val : ∀ x, gateVal n C g x = true ↔
      (∃ u ∈ varSet n C g (opnd C g 0), x u = true) ∧ (∃ w ∈ varSet n C g (opnd C g 1), x w = true) := by
    intro x
    change wval C x (n + g) = true ↔ _
    rw [wval_gate_and hAO x hg_lt hg_and, Bool.and_eq_true, h_g_op0_val, h_g_op1_val]
  have hv_in_01 : v ∈ varSet n C g (opnd C g 0) ∧ v ∈ varSet n C g (opnd C g 1) := by
    have hv := (h_g_val (unitInput v)).mp hv_g
    rcases hv with ⟨⟨u0, hu0, heq0⟩, ⟨u1, hu1, heq1⟩⟩
    simp only [unitInput, decide_eq_true_eq] at heq0 heq1
    subst heq0; subst heq1
    exact ⟨hu0, hu1⟩
  have h_and_not_both_g : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → a ≠ g →
      ¬ (usesG n C g (opnd C a 0) = true ∧ usesG n C g (opnd C a 1) = true) := by
    intro a ha hop hag ⟨hu0, hu1⟩
    have hbf := h_clean_and a ha hop hag
    have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
    have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
    have h0 : wval C (unitInput v) (opnd C a 0) = true :=
      (h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 (unitInput v)).mpr (Or.inl ⟨hu0, hv_g⟩)
    have h1 : wval C (unitInput v) (opnd C a 1) = true :=
      (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 (unitInput v)).mpr (Or.inl ⟨hu1, hv_g⟩)
    have ha_t : gateVal n C a (unitInput v) = true := by
      change wval C (unitInput v) (n + a) = true
      rw [wval_gate_and hAO _ ha hop, h0, h1]; rfl
    have hf := hbf (unitInput v) ha_t
    rw [graphFun_unitInput_false] at hf
    cases hf
  have h_dirty_cone_usesG : ∀ k < C.gates.length, ¬ BelowF G C k → (g = k ∨ InCone n C g k) →
      usesG n C g (n + k) = true := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk hdk hreach
      rcases hreach with hgk | hinc
      · rw [← hgk]; exact usesG_g n C g
      · have hkg : k ≠ g := by have := inCone_lt hinc; omega
        rw [inCone_iff hk] at hinc
        rcases hinc with ⟨w, hwm, hwn, hwlt, hsub⟩
        have hwk : w - n < k := by omega
        have hwn' : w = n + (w - n) := by omega
        have hdw : ¬ BelowF G C (w - n) := by
          intro hbf
          rw [gate_inputs_eq hAO hk] at hwm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
          rcases hwm with rfl | rfl
          · exact h_dirty_inputs k hk hdk 0 (by rw [hwn']; exact hbf)
          · exact h_dirty_inputs k hk hdk 1 (by rw [hwn']; exact hbf)
        have hug := ih (w - n) hwk (by omega) hdw hsub
        rw [usesG_gate hAO g k hk hkg, Bool.or_eq_true]
        rw [gate_inputs_eq hAO hk] at hwm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
        rcases hwm with rfl | rfl
        · exact Or.inl (by rw [hwn']; exact hug)
        · exact Or.inr (by rw [hwn']; exact hug)
  have h_exists_reader : ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ a ≠ g ∧
      (usesG n C g (opnd C a 0) = true ∨ usesG n C g (opnd C a 1) = true) := by
    have hP : ∃ a, a < C.gates.length ∧ (g = a ∨ InCone n C g a) ∧ BelowF G C a := by
      refine ⟨C.output - n, by omega, Or.inr ?_, h_out_below_gate⟩
      have hc := h_cone g hg_lt
      rcases hc.2 with hout | ⟨_, hinc⟩
      · omega
      · exact hinc
    let a := Nat.find hP
    have ha_spec := Nat.find_spec hP
    have ha_min : ∀ k < a, ¬ (k < C.gates.length ∧ (g = k ∨ InCone n C g k) ∧ BelowF G C k) :=
      fun k hk => Nat.find_min hP hk
    rcases ha_spec with ⟨ha_lt, ha_reach, ha_bf⟩
    have hag : a ≠ g := fun heq => hg_dirty (heq ▸ ha_bf)
    have hinc : InCone n C g a := ha_reach.resolve_left hag.symm
    rw [inCone_iff ha_lt] at hinc
    rcases hinc with ⟨w, hwm, hwn, hwlt, hsub⟩
    have hwk : w - n < a := by omega
    have hdw : ¬ BelowF G C (w - n) := fun hbf => ha_min (w - n) hwk ⟨by omega, hsub, hbf⟩
    have hop : (gateAt C a).op = GateOp.and := by
      rcases hAO.1 _ (gateAt_mem ha_lt) with hop | hop
      · exact hop
      · exfalso
        rw [gate_inputs_eq hAO ha_lt] at hwm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
        rcases hwm with rfl | rfl
        · exact hdw (h_clean_or_inputs a ha_lt ha_bf hop 0).2.2
        · exact hdw (h_clean_or_inputs a ha_lt ha_bf hop 1).2.2
    have hug : usesG n C g w = true := by
      have : w = n + (w - n) := by omega
      rw [this]
      exact h_dirty_cone_usesG (w - n) (by omega) hdw hsub
    refine ⟨a, ha_lt, hop, hag, ?_⟩
    rw [gate_inputs_eq hAO ha_lt] at hwm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
    rcases hwm with rfl | rfl
    · exact Or.inl hug
    · exact Or.inr hug
  have h_mem_zSet : ∀ z : Fin n, z ∈ zSet n C g ↔
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ a ≠ g ∧
        ((usesG n C g (opnd C a 0) = true ∧ z ∈ varSet n C g (opnd C a 1)) ∨
         (usesG n C g (opnd C a 1) = true ∧ z ∈ varSet n C g (opnd C a 0))) := by
    intro z
    unfold zSet
    simp only [Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨a, ha, hmem⟩
      cases hop : (gateAt C a).op with
      | and =>
        rw [hop] at hmem
        dsimp only at hmem
        by_cases hag : a ≠ g
        · rw [if_pos hag, Finset.mem_union] at hmem
          refine ⟨a, ha, hop, hag, ?_⟩
          rcases hmem with h0 | h1
          · split_ifs at h0 with hu0
            · exact Or.inl ⟨hu0, h0⟩
            · simp at h0
          · split_ifs at h1 with hu1
            · exact Or.inr ⟨hu1, h1⟩
            · simp at h1
        · simp [hag] at hmem
      | or => rw [hop] at hmem; simp at hmem
      | not => rw [hop] at hmem; simp at hmem
      | mod m => rw [hop] at hmem; simp at hmem
      | maj => rw [hop] at hmem; simp at hmem
    · rintro ⟨a, ha, hop, hag, hside⟩
      refine ⟨a, ha, ?_⟩
      rw [hop]
      simp only [hag, ne_eq, not_false_eq_true, ↓reduceIte, Finset.mem_union]
      rcases hside with ⟨hu0, hz1⟩ | ⟨hu1, hz0⟩
      · left; simp [hu0, hz1]
      · right; simp [hu1, hz0]
  have h_zSet_nonempty : (zSet n C g).Nonempty := by
    rcases h_exists_reader with ⟨a, ha, hop, hag, hu0 | hu1⟩
    · have hu1f : usesG n C g (opnd C a 1) = false := by
        cases h : usesG n C g (opnd C a 1)
        · rfl
        · exact (h_and_not_both_g a ha hop hag ⟨hu0, h⟩).elim
      have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
      rcases h_varSet_nonempty (opnd C a 1) (by have := opnd_lt hAO ha 1; omega) hd1 hu1f with ⟨z, hz⟩
      exact ⟨z, (h_mem_zSet z).mpr ⟨a, ha, hop, hag, Or.inl ⟨hu0, hz⟩⟩⟩
    · have hu0f : usesG n C g (opnd C a 0) = false := by
        cases h : usesG n C g (opnd C a 0)
        · rfl
        · exact (h_and_not_both_g a ha hop hag ⟨h, hu1⟩).elim
      have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
      rcases h_varSet_nonempty (opnd C a 0) (by have := opnd_lt hAO ha 0; omega) hd0 hu0f with ⟨z, hz⟩
      exact ⟨z, (h_mem_zSet z).mpr ⟨a, ha, hop, hag, Or.inr ⟨hu1, hz⟩⟩⟩
  have h_zSet_below : ∀ z ∈ zSet n C g, ∀ x : Fin n → Bool,
      gateVal n C g x = true → x z = true → graphFun G ∅ x = true := by
    intro z hz x hgx hxz
    rcases (h_mem_zSet z).mp hz with ⟨a, ha, hop, hag, ⟨hu0, hz1⟩ | ⟨hu1, hz0⟩⟩
    · have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
      have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
      have h0 : wval C x (opnd C a 0) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mpr (Or.inl ⟨hu0, hgx⟩)
      have h1 : wval C x (opnd C a 1) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mpr (Or.inr ⟨z, hz1, hxz⟩)
      apply h_clean_and a ha hop hag x
      change wval C x (n + a) = true
      rw [wval_gate_and hAO x ha hop, h0, h1]; rfl
    · have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
      have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
      have h0 : wval C x (opnd C a 0) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mpr (Or.inr ⟨z, hz0, hxz⟩)
      have h1 : wval C x (opnd C a 1) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mpr (Or.inl ⟨hu1, hgx⟩)
      apply h_clean_and a ha hop hag x
      change wval C x (n + a) = true
      rw [wval_gate_and hAO x ha hop, h0, h1]; rfl
  have h_zSet_adj_v : ∀ z ∈ zSet n C g, G.Adj v z := by
    intro z hz
    rw [← graphFun_pairInput_iff G v z]
    apply h_zSet_below z hz (pairInput v z)
    · rw [h_g_val]
      exact ⟨⟨v, hv_in_01.1, by simp [pairInput]⟩, ⟨v, hv_in_01.2, by simp [pairInput]⟩⟩
    · simp [pairInput]
  have h_zSet_color : ∀ z ∈ zSet n C g, s z ≠ s v := fun z hz => (h_bip v z (h_zSet_adj_v z hz)).symm
  have h_clean_and_no_two_sided : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → a ≠ g →
      ∀ b : Fin 2, ¬ ((∃ uL ∈ varSet n C g (opnd C a b), s uL = s v) ∧
                      (∃ uR ∈ varSet n C g (opnd C a b), s uR ≠ s v)) := by
    intro a ha hop hag b ⟨⟨uL, huL, hsL⟩, ⟨uR, huR, hsR⟩⟩
    let b' : Fin 2 := if b = 0 then 1 else 0
    have hbf := h_clean_and a ha hop hag
    have hdb : ¬ WireBelowF G C (opnd C a b) := h_no_imp a ha hop _ (opnd_mem hAO ha b)
    have hdb' : ¬ WireBelowF G C (opnd C a b') := h_no_imp a ha hop _ (opnd_mem hAO ha b')
    have h_pair_adj : ∀ x : Fin n → Bool, wval C x (opnd C a b) = true → wval C x (opnd C a b') = true →
        graphFun G ∅ x = true := by
      intro x hx1 hx2
      apply hbf x
      change wval C x (n + a) = true
      rw [wval_gate_and hAO x ha hop, Bool.and_eq_true]
      fin_cases b
      · exact ⟨hx1, hx2⟩
      · exact ⟨hx2, hx1⟩
    cases hub' : usesG n C g (opnd C a b') with
    | true =>
      have h1 : wval C (pairInput v uL) (opnd C a b) = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha b; omega) hdb _).mpr
          (Or.inr ⟨uL, huL, by simp [pairInput]⟩)
      have hgv : gateVal n C g (pairInput v uL) = true := by
        rw [h_g_val]
        exact ⟨⟨v, hv_in_01.1, by simp [pairInput]⟩, ⟨v, hv_in_01.2, by simp [pairInput]⟩⟩
      have h2 : wval C (pairInput v uL) (opnd C a b') = true :=
        (h_wval_dirty _ (by have := opnd_lt hAO ha b'; omega) hdb' _).mpr (Or.inl ⟨hub', hgv⟩)
      have hadj : G.Adj v uL := (graphFun_pairInput_iff G v uL).mp (h_pair_adj _ h1 h2)
      exact h_bip v uL hadj hsL.symm
    | false =>
      rcases h_varSet_nonempty (opnd C a b') (by have := opnd_lt hAO ha b'; omega) hdb' hub' with ⟨z, hz⟩
      by_cases hsz : s z = s v
      · have h1 : wval C (pairInput uL z) (opnd C a b) = true :=
          (h_wval_dirty _ (by have := opnd_lt hAO ha b; omega) hdb _).mpr
            (Or.inr ⟨uL, huL, by simp [pairInput]⟩)
        have h2 : wval C (pairInput uL z) (opnd C a b') = true :=
          (h_wval_dirty _ (by have := opnd_lt hAO ha b'; omega) hdb' _).mpr
            (Or.inr ⟨z, hz, by simp [pairInput]⟩)
        have hadj : G.Adj uL z := (graphFun_pairInput_iff G uL z).mp (h_pair_adj _ h1 h2)
        exact h_bip uL z hadj (hsL.trans hsz.symm)
      · have h1 : wval C (pairInput uR z) (opnd C a b) = true :=
          (h_wval_dirty _ (by have := opnd_lt hAO ha b; omega) hdb _).mpr
            (Or.inr ⟨uR, huR, by simp [pairInput]⟩)
        have h2 : wval C (pairInput uR z) (opnd C a b') = true :=
          (h_wval_dirty _ (by have := opnd_lt hAO ha b'; omega) hdb' _).mpr
            (Or.inr ⟨z, hz, by simp [pairInput]⟩)
        have hadj : G.Adj uR z := (graphFun_pairInput_iff G uR z).mp (h_pair_adj _ h1 h2)
        have hsr : s uR = s z := bool_eq_of_ne_ne (Ne.symm hsR) (Ne.symm hsz)
        exact h_bip uR z hadj hsr
  have h_solve_ordered :
      ∀ (aW bW : ℕ),
        aW < n + g → bW < n + g →
        ¬ WireBelowF G C aW → ¬ WireBelowF G C bW →
        (∀ x, gateVal n C g x = (wval C x aW && wval C x bW)) →
        (∀ w ∈ (gateAt C g).inputs, w = aW ∨ w = bW) →
        aW∈(gateAt C g).inputs → bW∈(gateAt C g).inputs →
        (∀ u ∈ varSet n C g aW, s u = s v) →
        ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
          circuitFun n D = graphFun G ∅ ∧
          ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → BelowF G D k := by
    intro aW bW haW_lt hbW_lt haW_d hbW_d hg_ab hg_in haWmem hbWmem hA_L
    set A := varSet n C g aW
    set B := varSet n C g bW
    set Z := zSet n C g
    have haW_val : ∀ x, wval C x aW = true ↔ ∃ u ∈ A, x u = true := by
      intro x
      have h := h_wval_dirty aW (by omega) haW_d x
      rw [usesG_lt_g hAO g aW haW_lt] at h
      simpa using h
    have hbW_val : ∀ x, wval C x bW = true ↔ ∃ w ∈ B, x w = true := by
      intro x
      have h := h_wval_dirty bW (by omega) hbW_d x
      rw [usesG_lt_g hAO g bW hbW_lt] at h
      simpa using h
    have hg_AB : ∀ x, gateVal n C g x = true ↔ (∃ u ∈ A, x u = true) ∧ (∃ w ∈ B, x w = true) := by
      intro x
      rw [hg_ab, Bool.and_eq_true, haW_val, hbW_val]
    have hv_A : v ∈ A := by
      rcases ((hg_AB (unitInput v)).mp hv_g).1 with ⟨u, hu, heq⟩
      simp only [unitInput, decide_eq_true_eq] at heq
      exact heq ▸ hu
    have hv_B : v ∈ B := by
      rcases ((hg_AB (unitInput v)).mp hv_g).2 with ⟨w, hw, heq⟩
      simp only [unitInput, decide_eq_true_eq] at heq
      exact heq ▸ hw
    have h_two_sided_le_b : ∀ k < C.gates.length, ¬ BelowF G C k → k ≠ g →
        (∃ uL ∈ varSet n C g (n + k), s uL = s v) →
        (∃ uR ∈ varSet n C g (n + k), s uR ≠ s v) → n + k ≤ bW := by
      intro k hk hdk hkg hL hR
      have hT : ∃ c, c < C.gates.length ∧ (k = c ∨ InCone n C k c) ∧ (c = g ∨ BelowF G C c) := by
        refine ⟨C.output - n, by omega, Or.inr ?_, Or.inr h_out_below_gate⟩
        have hc := h_cone k hk
        rcases hc.2 with hout | ⟨_, hinc⟩
        · exfalso
          apply hdk
          intro x hx
          exact h_out_below x (by rw [hout]; exact hx)
        · exact hinc
      obtain ⟨c, hc_eq⟩ : ∃ c, c = Nat.find hT := ⟨_, rfl⟩
      have hc_spec : c < C.gates.length ∧ (k = c ∨ InCone n C k c) ∧ (c = g ∨ BelowF G C c) :=
        hc_eq ▸ Nat.find_spec hT
      have hc_min : ∀ j < c, ¬ (j < C.gates.length ∧ (k = j ∨ InCone n C k j) ∧ (j = g ∨ BelowF G C j)) :=
        fun j hj => Nat.find_min hT (hc_eq ▸ hj)
      rcases hc_spec with ⟨hc_lt, hc_reach, hc_end⟩
      have h_sub : ∀ j < c, (k = j ∨ InCone n C k j) → varSet n C g (n + k) ⊆ varSet n C g (n + j) := by
        intro j
        induction j using Nat.strongRecOn with
        | ind j ih =>
          intro hjc hjr
          rcases hjr with hkj | hinc
          · rw [hkj]
          · have hjlt : j < C.gates.length := inCone_lt_len hinc
            have hj_not : ¬ (j = g ∨ BelowF G C j) := fun h => hc_min j hjc ⟨hjlt, Or.inr hinc, h⟩
            have hjg : j ≠ g := fun h => hj_not (Or.inl h)
            rw [inCone_iff hjlt] at hinc
            rcases hinc with ⟨w, hwm, hwn, hwlt, hsub⟩
            have hwn' : w = n + (w - n) := by omega
            have h1 := ih (w - n) (by omega) (by omega) hsub
            rw [varSet_gate hAO g j hjlt hjg]
            rw [gate_inputs_eq hAO hjlt] at hwm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
            rcases hwm with rfl | rfl
            · exact Finset.Subset.trans h1 (by rw [← hwn']; exact Finset.subset_union_left)
            · exact Finset.Subset.trans h1 (by rw [← hwn']; exact Finset.subset_union_right)
      have hck : k ≠ c := by
        intro heq
        rcases hc_end with hcg | hbf
        · exact hkg (heq.trans hcg)
        · exact hdk (heq ▸ hbf)
      have hc_inc : InCone n C k c := hc_reach.resolve_left hck
      rw [inCone_iff hc_lt] at hc_inc
      rcases hc_inc with ⟨w, hwm, hwn, hwlt, hsub⟩
      have hwn' : w = n + (w - n) := by omega
      have h_k_le : k ≤ w - n := by
        rcases hsub with hkw | hinc'
        · omega
        · have := inCone_lt hinc'; omega
      have h_sub_w : varSet n C g (n + k) ⊆ varSet n C g w := by
        rw [hwn']
        exact h_sub (w - n) (by omega) hsub
      have hwL : ∃ uL ∈ varSet n C g w, s uL = s v := by
        rcases hL with ⟨u, hu, hs⟩; exact ⟨u, h_sub_w hu, hs⟩
      have hwR : ∃ uR ∈ varSet n C g w, s uR ≠ s v := by
        rcases hR with ⟨u, hu, hs⟩; exact ⟨u, h_sub_w hu, hs⟩
      have hdw : ¬ BelowF G C (w - n) := fun hbf =>
        hc_min (w - n) (by omega) ⟨by omega, hsub, Or.inr hbf⟩
      rcases hc_end with hcg | hbf
      · rw [hcg] at hwm
        rcases hg_in w hwm with rfl | rfl
        · rcases hwR with ⟨uR, huR, hsR⟩
          exact (hsR (hA_L uR huR)).elim
        · omega
      · exfalso
        rcases hAO.1 _ (gateAt_mem hc_lt) with hop | hop
        · have hcg : c ≠ g := fun heq => hg_dirty (heq ▸ hbf)
          rw [gate_inputs_eq hAO hc_lt] at hwm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
          rcases hwm with rfl | rfl
          · exact h_clean_and_no_two_sided c hc_lt hop hcg 0 ⟨hwL, hwR⟩
          · exact h_clean_and_no_two_sided c hc_lt hop hcg 1 ⟨hwL, hwR⟩
        · rw [gate_inputs_eq hAO hc_lt] at hwm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwm
          rcases hwm with rfl | rfl
          · exact hdw (h_clean_or_inputs c hc_lt hbf hop 0).2.2
          · exact hdw (h_clean_or_inputs c hc_lt hbf hop 1).2.2
    have h_del_wval_dirty : ∀ (r : ℕ), r < n + g →
        ∀ w < n + C.gates.length, ¬ WireBelowF G C w → ∀ x : Fin n → Bool,
          wval (delCircuit n C g r) x (delMap n g r w) = true ↔
            (usesG n C g w = true ∧ wval C x r = true) ∨ (∃ u ∈ varSet n C g w, x u = true) := by
      intro r hr
      have hAO' := delCircuit_isAO2 hAO hg_lt hr
      intro w
      induction w using Nat.strongRecOn with
      | ind w ih =>
        intro hw hdw x
        by_cases hlt : w < n + g
        · have hm : delMap n g r w = w := by simp [delMap, hlt]
          rw [hm, delCircuit_wval_lt hAO hg_lt hr x w hlt, h_wval_dirty w hw hdw x, usesG_lt_g hAO g w hlt]
          simp
        · by_cases hwg : w = n + g
          · subst hwg
            have hm : delMap n g r (n + g) = r := by simp [delMap]
            rw [hm, delCircuit_wval_lt hAO hg_lt hr x r hr, usesG_g, varSet_g]
            simp
          · have hk : w - n < C.gates.length := by omega
            have hkg : w - n ≠ g := by omega
            have hwn : w = n + (w - n) := by omega
            have hdk : ¬ BelowF G C (w - n) := fun hbf => hdw (by rw [hwn]; exact hbf)
            have hop : (gateAt C (w - n)).op = GateOp.or := h_dirty_or (w - n) hk hdk hkg
            have hdm : delMap n g r w = n + delGateMap g (w - n) := by
              conv_lhs => rw [hwn]
              exact delMap_gate n g r (w - n) hkg
            have hk' : delGateMap g (w - n) < (delCircuit n C g r).gates.length := by
              rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
            have hgate : (gateAt (delCircuit n C g r) (delGateMap g (w - n))).op = GateOp.or := by
              rw [delCircuit_gateAt_src hg_lt hk hkg, hop]
            have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
            have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
            have ih0 := ih _ h0lt (by omega) (h_dirty_inputs (w - n) hk hdk 0) x
            have ih1 := ih _ h1lt (by omega) (h_dirty_inputs (w - n) hk hdk 1) x
            rw [hdm, wval_gate_or hAO' x hk' hgate, Bool.or_eq_true,
              delCircuit_opnd hAO hg_lt hk hkg 0, delCircuit_opnd hAO hg_lt hk hkg 1, ih0, ih1]
            conv_rhs => rw [hwn, usesG_gate hAO g (w - n) hk hkg, varSet_gate hAO g (w - n) hk hkg]
            simp only [Bool.or_eq_true, Finset.mem_union, or_and_right, exists_or]
            exact or_and_or_iff
    have h_solve_Z1_wire : ∀ (m : Fin n) (r : ℕ),
        (∀ z ∈ Z, z = m) → r < n + g →
        (∀ x, gateVal n C g x = true → wval C x r = true) →
        (∀ x, wval C x r = true → x m = true → graphFun G ∅ x = true) →
        ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
          circuitFun n D = graphFun G ∅ ∧
          ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → BelowF G D k := by
      intro m r hZm hr hge_r h_rm_below
      let D := delCircuit n C g r
      have hAO' := delCircuit_isAO2 hAO hg_lt hr
      have h_and_bf : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → a ≠ g →
          BelowF G D (delGateMap g a) := by
        intro a ha hop hag x hDx
        have ha' : delGateMap g a < D.gates.length := by
          rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
        have hgate : (gateAt D (delGateMap g a)).op = GateOp.and := by
          rw [delCircuit_gateAt_src hg_lt ha hag, hop]
        change wval D x (n + delGateMap g a) = true at hDx
        rw [wval_gate_and hAO' x ha' hgate, Bool.and_eq_true,
          delCircuit_opnd hAO hg_lt ha hag 0, delCircuit_opnd hAO hg_lt ha hag 1] at hDx
        have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
        have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
        have h0 := (h_del_wval_dirty r hr _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mp hDx.1
        have h1 := (h_del_wval_dirty r hr _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mp hDx.2
        rcases h0 with ⟨hu0, hrx⟩ | ⟨u0, hu0, hxu0⟩
        · have hu1f : usesG n C g (opnd C a 1) = false := by
            cases h : usesG n C g (opnd C a 1)
            · rfl
            · exact (h_and_not_both_g a ha hop hag ⟨hu0, h⟩).elim
          rcases h1 with ⟨hu1t, _⟩ | ⟨z, hz, hxz⟩
          · rw [hu1f] at hu1t; cases hu1t
          · have hzm : z = m := hZm z ((h_mem_zSet z).mpr ⟨a, ha, hop, hag, Or.inl ⟨hu0, hz⟩⟩)
            exact h_rm_below x hrx (hzm ▸ hxz)
        · rcases h1 with ⟨hu1, hrx⟩ | ⟨u1, hu1, hxu1⟩
          · have hzm : u0 = m := hZm u0 ((h_mem_zSet u0).mpr ⟨a, ha, hop, hag, Or.inr ⟨hu1, hu0⟩⟩)
            exact h_rm_below x hrx (hzm ▸ hxu0)
          · apply h_clean_and a ha hop hag x
            change wval C x (n + a) = true
            rw [wval_gate_and hAO x ha hop, Bool.and_eq_true]
            exact ⟨(h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mpr (Or.inr ⟨u0, hu0, hxu0⟩),
                   (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mpr (Or.inr ⟨u1, hu1, hxu1⟩)⟩
      have h_all_bf : ∀ k < C.gates.length, BelowF G C k → BelowF G D (delGateMap g k) := by
        intro k
        induction k using Nat.strongRecOn with
        | ind k ih =>
          intro hk hbf
          have hkg : k ≠ g := fun heq => hg_dirty (heq ▸ hbf)
          rcases hAO.1 _ (gateAt_mem hk) with hop | hop
          · exact h_and_bf k hk hop hkg
          · intro x hDx
            have hk' : delGateMap g k < D.gates.length := by
              rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
            have hgate : (gateAt D (delGateMap g k)).op = GateOp.or := by
              rw [delCircuit_gateAt_src hg_lt hk hkg, hop]
            change wval D x (n + delGateMap g k) = true at hDx
            rw [wval_gate_or hAO' x hk' hgate, Bool.or_eq_true,
              delCircuit_opnd hAO hg_lt hk hkg 0, delCircuit_opnd hAO hg_lt hk hkg 1] at hDx
            have hi0 := h_clean_or_inputs k hk hbf hop 0
            have hi1 := h_clean_or_inputs k hk hbf hop 1
            have hne0 : opnd C k 0 - n ≠ g := fun heq => hg_dirty (heq ▸ hi0.2.2)
            have hne1 : opnd C k 1 - n ≠ g := fun heq => hg_dirty (heq ▸ hi1.2.2)
            have heq0 : opnd C k 0 = n + (opnd C k 0 - n) := by omega
            have heq1 : opnd C k 1 = n + (opnd C k 1 - n) := by omega
            rcases hDx with h0 | h1
            · rw [heq0, delMap_gate n g r _ hne0] at h0
              exact ih _ hi0.2.1 (by omega) hi0.2.2 x h0
            · rw [heq1, delMap_gate n g r _ hne1] at h1
              exact ih _ hi1.2.1 (by omega) hi1.2.2 x h1
      refine ⟨D, hAO', delCircuit_size_strict n C g r hg_lt, ?_, ?_⟩
      · funext x
        have h_out_ne : C.output - n ≠ g := by omega
        have h_out_eq : C.output = n + (C.output - n) := by omega
        have h_Dout : circuitFun n D x = gateVal n D (delGateMap g (C.output - n)) x := by
          change wval D x (delMap n g r C.output) = wval D x (n + delGateMap g (C.output - n))
          conv_lhs => rw [h_out_eq]
          rw [delMap_gate n g r _ h_out_ne]
        cases hDx : circuitFun n D x with
        | true =>
          rw [h_Dout] at hDx
          exact (h_all_bf (C.output - n) (by omega) h_out_below_gate x hDx).symm
        | false =>
          cases hFx : graphFun G ∅ x with
          | false => rfl
          | true =>
            have hCx : wval C x C.output = true := by
              change circuitFun n C x = true
              rw [h_eq]; exact hFx
            have hDt : circuitFun n D x = true :=
              delCircuit_wval_ge hAO hg_lt hr x (hge_r x) C.output (by omega) hCx
            rw [hDx] at hDt; cases hDt
      · intro k' hk' hop'
        rw [delCircuit_len] at hk'
        let src := if k' < g then k' else k' + 1
        have hsrc_lt : src < C.gates.length := by dsimp [src]; split_ifs <;> omega
        have hsrc_ne : src ≠ g := by dsimp [src]; split_ifs <;> omega
        have hdgm : delGateMap g src = k' := by dsimp [src, delGateMap]; split_ifs <;> omega
        have hop : (gateAt C src).op = GateOp.and := by
          rw [← hdgm, delCircuit_gateAt_src hg_lt hsrc_lt hsrc_ne] at hop'
          exact hop'
        rw [← hdgm]
        exact h_and_bf src hsrc_lt hop hsrc_ne
    by_cases hZ1 : Z.card ≤ 1
    · rcases h_zSet_nonempty with ⟨m, hmZ⟩
      have hZm : ∀ z ∈ Z, z = m := fun z hz => Finset.card_le_one.mp hZ1 z hz m hmZ
      by_cases hAm : ∀ u ∈ A, G.Adj u m
      · apply h_solve_Z1_wire m aW hZm haW_lt
        · intro x hgx; rw [hg_ab, Bool.and_eq_true] at hgx; exact hgx.1
        · intro x hrx hxm
          rcases (haW_val x).mp hrx with ⟨u, hu, hxu⟩
          exact (graphFun_iff x).mpr ⟨u, m, hAm u hu, hxu, hxm⟩
      · push_neg at hAm
        rcases hAm with ⟨u0, hu0A, hu0m⟩
        have hBL_m : ∀ w ∈ B, s w = s v → G.Adj w m := by
          intro w hwB hsw
          have htri : graphFun G ∅ (tripleInput u0 w m) = true := by
            apply h_zSet_below m hmZ (tripleInput u0 w m)
            · rw [hg_AB]
              exact ⟨⟨u0, hu0A, by simp [tripleInput]⟩, ⟨w, hwB, by simp [tripleInput]⟩⟩
            · simp [tripleInput]
          rw [graphFun_tripleInput_iff] at htri
          rcases htri with hadj | hadj | hadj
          · exact (h_bip u0 w hadj ((hA_L u0 hu0A).trans hsw.symm)).elim
          · exact (hu0m hadj).elim
          · exact hadj
        have hm_not_B : m ∉ B := by
          intro hmB
          have hp : graphFun G ∅ (pairInput u0 m) = true := by
            apply h_zSet_below m hmZ (pairInput u0 m)
            · rw [hg_AB]
              exact ⟨⟨u0, hu0A, by simp [pairInput]⟩, ⟨m, hmB, by simp [pairInput]⟩⟩
            · simp [pairInput]
          exact hu0m ((graphFun_pairInput_iff G u0 m).mp hp)
        by_cases hB_L : ∀ w ∈ B, s w = s v
        · apply h_solve_Z1_wire m bW hZm hbW_lt
          · intro x hgx; rw [hg_ab, Bool.and_eq_true] at hgx; exact hgx.2
          · intro x hrx hxm
            rcases (hbW_val x).mp hrx with ⟨w, hw, hxw⟩
            exact (graphFun_iff x).mpr ⟨w, m, hBL_m w hw (hB_L w hw), hxw, hxm⟩
        · push_neg at hB_L
          rcases hB_L with ⟨wR, hwRB, hwRs⟩
          let C1 := restrictTwoSided G C s v g
          have hAO1 : IsAO2 n C1 := restrictTwoSided_isAO2 hAO s v g
          have hg_lt1 : g < C1.gates.length := by rw [restrictTwoSided_len]; exact hg_lt
          let D := delCircuit n C1 g bW
          have hAO' := delCircuit_isAO2 hAO1 hg_lt1 hbW_lt
          have h_no_ts_reads_ts : ∀ k < C.gates.length, k ≠ g →
              ¬ isTwoSided G C s v g (n + k) → ∀ b : Fin 2, ¬ isTwoSided G C s v g (opnd C k b) := by
            intro k hk hkg hnts b hts
            rcases hts with ⟨_, hdw, hL, hR⟩
            by_cases hbf : BelowF G C k
            · rcases hAO.1 _ (gateAt_mem hk) with hop | hop
              · exact h_clean_and_no_two_sided k hk hop hkg b ⟨hL, hR⟩
              · have hi := h_clean_or_inputs k hk hbf hop b
                apply hdw
                have : opnd C k b = n + (opnd C k b - n) := by omega
                rw [this]; exact hi.2.2
            · apply hnts
              refine ⟨by omega, hbf, ?_, ?_⟩
              · rw [varSet_gate hAO g k hk hkg]
                rcases hL with ⟨u, hu, hs⟩
                fin_cases b
                · exact ⟨u, Finset.mem_union_left _ hu, hs⟩
                · exact ⟨u, Finset.mem_union_right _ hu, hs⟩
              · rw [varSet_gate hAO g k hk hkg]
                rcases hR with ⟨u, hu, hs⟩
                fin_cases b
                · exact ⟨u, Finset.mem_union_left _ hu, hs⟩
                · exact ⟨u, Finset.mem_union_right _ hu, hs⟩
          have h_C1_eq_C : ∀ w < n + g, ¬ isTwoSided G C s v g w →
              ∀ x : Fin n → Bool, wval C1 x w = wval C x w := by
            intro w
            induction w using Nat.strongRecOn with
            | ind w ih =>
              intro hw hnts x
              by_cases hlt : w < n
              · rw [wval_input C1 x w hlt, wval_input C x w hlt]
              · have hk : w - n < C.gates.length := by omega
                have hkg : w - n ≠ g := by omega
                have hwn : w = n + (w - n) := by omega
                have hnts' : ¬ isTwoSided G C s v g (n + (w - n)) := by rwa [← hwn]
                have hgt : gateAt C1 (w - n) = gateAt C (w - n) := by
                  rw [restrictTwoSided_gateAt G C s v g (w - n) hk]
                  split_ifs with hcond
                  · exfalso; exact hnts' ⟨by omega, hcond.1, hcond.2.1, hcond.2.2⟩
                  · rfl
                have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
                have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
                have h0nts := h_no_ts_reads_ts (w - n) hk hkg hnts' 0
                have h1nts := h_no_ts_reads_ts (w - n) hk hkg hnts' 1
                have hop0 : opnd C1 (w - n) 0 = opnd C (w - n) 0 := by unfold opnd; rw [hgt]
                have hop1 : opnd C1 (w - n) 1 = opnd C (w - n) 1 := by unfold opnd; rw [hgt]
                have hk1 : w - n < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
                rw [hwn]
                rcases hAO.1 _ (gateAt_mem hk) with hop | hop
                · rw [wval_gate_and hAO1 x hk1 (by rw [hgt]; exact hop), wval_gate_and hAO x hk hop,
                    hop0, hop1, ih _ h0lt (by omega) h0nts x, ih _ h1lt (by omega) h1nts x]
                · rw [wval_gate_or hAO1 x hk1 (by rw [hgt]; exact hop), wval_gate_or hAO x hk hop,
                    hop0, hop1, ih _ h0lt (by omega) h0nts x, ih _ h1lt (by omega) h1nts x]
          have h_C1_ts_bounds : ∀ w < n + g, isTwoSided G C s v g w → ∀ x : Fin n → Bool,
              (wval C1 x w = true → x v = true ∨ ∃ u ∈ varSet n C g w, s u = s v ∧ x u = true) ∧
              ((∃ u ∈ varSet n C g w, s u = s v ∧ x u = true) → wval C1 x w = true) := by
            intro w
            induction w using Nat.strongRecOn with
            | ind w ih =>
              intro hw hts x
              have hge_n : n ≤ w := by
                by_contra hlt
                rcases hts with ⟨_, _, ⟨uL, huL, hsL⟩, ⟨uR, huR, hsR⟩⟩
                rw [varSet_input n C g w (by omega)] at huL huR
                simp only [Finset.mem_singleton] at huL huR
                subst huL; subst huR
                exact hsR hsL
              have hk : w - n < C.gates.length := by omega
              have hkg : w - n ≠ g := by omega
              have hwn : w = n + (w - n) := by omega
              have hdk : ¬ BelowF G C (w - n) := fun hbf => hts.2.1 (by rw [hwn]; exact hbf)
              have hop : (gateAt C (w - n)).op = GateOp.or := h_dirty_or (w - n) hk hdk hkg
              have hk1 : w - n < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
              have hgt : gateAt C1 (w - n) = ⟨GateOp.or, (gateAt C (w - n)).inputs.map (restrictMap C s v g)⟩ := by
                rw [restrictTwoSided_gateAt G C s v g (w - n) hk]
                have hcond : ¬ BelowF G C (w - n) ∧ (∃ u ∈ varSet n C g (n + (w - n)), s u = s v) ∧
                    (∃ u ∈ varSet n C g (n + (w - n)), s u ≠ s v) := by
                  rw [← hwn]; exact ⟨hdk, hts.2.2.1, hts.2.2.2⟩
                simp [hcond, hop]
              have hop_eq : (gateAt C1 (w - n)).op = GateOp.or := by rw [hgt]
              have hop0 : opnd C1 (w - n) 0 = restrictMap C s v g (opnd C (w - n) 0) := by
                unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
              have hop1 : opnd C1 (w - n) 1 = restrictMap C s v g (opnd C (w - n) 1) := by
                unfold opnd; rw [hgt, gate_inputs_eq hAO hk]; rfl
              have h_branch : ∀ b : Fin 2,
                  (wval C1 x (restrictMap C s v g (opnd C (w - n) b)) = true →
                    x v = true ∨ ∃ u ∈ varSet n C g (opnd C (w - n) b), s u = s v ∧ x u = true) ∧
                  ((∃ u ∈ varSet n C g (opnd C (w - n) b), s u = s v ∧ x u = true) →
                    wval C1 x (restrictMap C s v g (opnd C (w - n) b)) = true) := by
                intro b
                set uW := opnd C (w - n) b
                have huW_lt : uW < w := by have := opnd_lt hAO hk b; omega
                have huW_d : ¬ WireBelowF G C uW := h_dirty_inputs (w - n) hk hdk b
                have huW_val : wval C x uW = true ↔ ∃ u ∈ varSet n C g uW, x u = true := by
                  have h := h_wval_dirty uW (by omega) huW_d x
                  rw [usesG_lt_g hAO g uW (by omega)] at h
                  simpa using h
                unfold restrictMap
                by_cases hR : ∀ u ∈ varSet n C g uW, s u ≠ s v
                · rw [ite_eq_left_iff.mpr (fun hn => (hn hR).elim)]
                  constructor
                  · intro hv1; rw [wval_input C1 x v.val v.isLt] at hv1; exact Or.inl hv1
                  · rintro ⟨u, hu, hsu, _⟩; exact (hR u hu hsu).elim
                · rw [ite_eq_right_iff.mpr (fun hy => (hR hy).elim)]
                  push_neg at hR
                  rcases hR with ⟨uL, huL, hsL⟩
                  by_cases hR2 : ∃ uR ∈ varSet n C g uW, s uR ≠ s v
                  · exact ih uW huW_lt (by omega) ⟨by omega, huW_d, ⟨uL, huL, hsL⟩, hR2⟩ x
                  · push_neg at hR2
                    have hnts_u : ¬ isTwoSided G C s v g uW := by
                      rintro ⟨_, _, _, ⟨uR, huR, hsR⟩⟩; exact hsR (hR2 uR huR)
                    rw [h_C1_eq_C uW (by omega) hnts_u x, huW_val]
                    constructor
                    · rintro ⟨u, hu, hxu⟩; exact Or.inr ⟨u, hu, hR2 u hu, hxu⟩
                    · rintro ⟨u, hu, _, hxu⟩; exact ⟨u, hu, hxu⟩
              have hb0 := h_branch 0
              have hb1 := h_branch 1
              rw [hwn, wval_gate_or hAO1 x hk1 hop_eq, Bool.or_eq_true, hop0, hop1,
                varSet_gate hAO g (w - n) hk hkg]
              constructor
              · rintro (h0 | h1)
                · rcases hb0.1 h0 with hv1 | ⟨u, hu, hsu, hxu⟩
                  · exact Or.inl hv1
                  · exact Or.inr ⟨u, Finset.mem_union_left _ hu, hsu, hxu⟩
                · rcases hb1.1 h1 with hv1 | ⟨u, hu, hsu, hxu⟩
                  · exact Or.inl hv1
                  · exact Or.inr ⟨u, Finset.mem_union_right _ hu, hsu, hxu⟩
              · rintro ⟨u, hu, hsu, hxu⟩
                rcases Finset.mem_union.mp hu with hu0 | hu1
                · exact Or.inl (hb0.2 ⟨u, hu0, hsu, hxu⟩)
                · exact Or.inr (hb1.2 ⟨u, hu1, hsu, hxu⟩)
          have h_C1_bW : ∀ x : Fin n → Bool, wval C1 x bW = true ↔ ∃ w ∈ B, s w = s v ∧ x w = true := by
            intro x
            have hts_b : isTwoSided G C s v g bW := ⟨by omega, hbW_d, ⟨v, hv_B, rfl⟩, ⟨wR, hwRB, hwRs⟩⟩
            have hb := h_C1_ts_bounds bW hbW_lt hts_b x
            constructor
            · intro h1
              rcases hb.1 h1 with hv1 | h2
              · exact ⟨v, hv_B, rfl, hv1⟩
              · exact h2
            · exact hb.2
          have h_D_dirty : ∀ w < n + C.gates.length, ¬ WireBelowF G C w → ¬ isTwoSided G C s v g w →
              ∀ x : Fin n → Bool,
                wval D x (delMap n g bW w) = true ↔
                  (usesG n C g w = true ∧ wval C1 x bW = true) ∨ (∃ u ∈ varSet n C g w, x u = true) := by
            intro w
            induction w using Nat.strongRecOn with
            | ind w ih =>
              intro hw hdw hnts x
              by_cases hlt : w < n + g
              · have hm : delMap n g bW w = w := by simp [delMap, hlt]
                rw [hm, delCircuit_wval_lt hAO1 hg_lt1 hbW_lt x w hlt, h_C1_eq_C w hlt hnts x,
                  h_wval_dirty w hw hdw x, usesG_lt_g hAO g w hlt]
                simp
              · by_cases hwg : w = n + g
                · subst hwg
                  have hm : delMap n g bW (n + g) = bW := by simp [delMap]
                  rw [hm, delCircuit_wval_lt hAO1 hg_lt1 hbW_lt x bW hbW_lt, usesG_g, varSet_g]
                  simp
                · have hk : w - n < C.gates.length := by omega
                  have hkg : w - n ≠ g := by omega
                  have hwn : w = n + (w - n) := by omega
                  have hdk : ¬ BelowF G C (w - n) := fun hbf => hdw (by rw [hwn]; exact hbf)
                  have hop : (gateAt C (w - n)).op = GateOp.or := h_dirty_or (w - n) hk hdk hkg
                  have hnts' : ¬ isTwoSided G C s v g (n + (w - n)) := by rwa [← hwn]
                  have hgt1 : gateAt C1 (w - n) = gateAt C (w - n) := by
                    rw [restrictTwoSided_gateAt G C s v g (w - n) hk]
                    split_ifs with hcond
                    · exfalso; exact hnts' ⟨by omega, hcond.1, hcond.2.1, hcond.2.2⟩
                    · rfl
                  have hdm : delMap n g bW w = n + delGateMap g (w - n) := by
                    conv_lhs => rw [hwn]
                    exact delMap_gate n g bW (w - n) hkg
                  have hk1 : w - n < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
                  have hk' : delGateMap g (w - n) < D.gates.length := by
                    rw [delCircuit_len, restrictTwoSided_len]; unfold delGateMap; split_ifs <;> omega
                  have hgate : (gateAt D (delGateMap g (w - n))).op = GateOp.or := by
                    rw [delCircuit_gateAt_src hg_lt1 hk1 hkg, hgt1, hop]
                  have hop0 : opnd D (delGateMap g (w - n)) 0 = delMap n g bW (opnd C (w - n) 0) := by
                    rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 0]; unfold opnd; rw [hgt1]
                  have hop1 : opnd D (delGateMap g (w - n)) 1 = delMap n g bW (opnd C (w - n) 1) := by
                    rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 1]; unfold opnd; rw [hgt1]
                  have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO hk 0; omega
                  have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO hk 1; omega
                  have ih0 := ih _ h0lt (by omega) (h_dirty_inputs (w - n) hk hdk 0)
                    (h_no_ts_reads_ts (w - n) hk hkg hnts' 0) x
                  have ih1 := ih _ h1lt (by omega) (h_dirty_inputs (w - n) hk hdk 1)
                    (h_no_ts_reads_ts (w - n) hk hkg hnts' 1) x
                  rw [hdm, wval_gate_or hAO' x hk' hgate, Bool.or_eq_true, hop0, hop1, ih0, ih1]
                  conv_rhs => rw [hwn, usesG_gate hAO g (w - n) hk hkg, varSet_gate hAO g (w - n) hk hkg]
                  simp only [Bool.or_eq_true, Finset.mem_union, or_and_right, exists_or]
                  exact or_and_or_iff
          have h_C1_clean : ∀ k < C.gates.length, BelowF G C k → gateAt C1 k = gateAt C k := by
            intro k hk hbf
            rw [restrictTwoSided_gateAt G C s v g k hk]
            simp [hbf]
          have h_and_bf : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → a ≠ g →
              BelowF G D (delGateMap g a) := by
            intro a ha hop hag x hDx
            have ha1 : a < C1.gates.length := by rw [restrictTwoSided_len]; exact ha
            have ha' : delGateMap g a < D.gates.length := by
              rw [delCircuit_len, restrictTwoSided_len]; unfold delGateMap; split_ifs <;> omega
            have hgt1 := h_C1_clean a ha (h_clean_and a ha hop hag)
            have hgate : (gateAt D (delGateMap g a)).op = GateOp.and := by
              rw [delCircuit_gateAt_src hg_lt1 ha1 hag, hgt1, hop]
            have hop0 : opnd D (delGateMap g a) 0 = delMap n g bW (opnd C a 0) := by
              rw [delCircuit_opnd hAO1 hg_lt1 ha1 hag 0]; unfold opnd; rw [hgt1]
            have hop1 : opnd D (delGateMap g a) 1 = delMap n g bW (opnd C a 1) := by
              rw [delCircuit_opnd hAO1 hg_lt1 ha1 hag 1]; unfold opnd; rw [hgt1]
            change wval D x (n + delGateMap g a) = true at hDx
            rw [wval_gate_and hAO' x ha' hgate, Bool.and_eq_true, hop0, hop1] at hDx
            have hd0 : ¬ WireBelowF G C (opnd C a 0) := h_no_imp a ha hop _ (opnd_mem hAO ha 0)
            have hd1 : ¬ WireBelowF G C (opnd C a 1) := h_no_imp a ha hop _ (opnd_mem hAO ha 1)
            have hnts_a : ¬ isTwoSided G C s v g (n + a) := fun h => h.2.1 (h_clean_and a ha hop hag)
            have h0 := (h_D_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0
              (h_no_ts_reads_ts a ha hag hnts_a 0) x).mp hDx.1
            have h1 := (h_D_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1
              (h_no_ts_reads_ts a ha hag hnts_a 1) x).mp hDx.2
            rcases h0 with ⟨hu0, hbx⟩ | ⟨u0, hu0, hxu0⟩
            · have hu1f : usesG n C g (opnd C a 1) = false := by
                cases h : usesG n C g (opnd C a 1)
                · rfl
                · exact (h_and_not_both_g a ha hop hag ⟨hu0, h⟩).elim
              rcases h1 with ⟨hu1t, _⟩ | ⟨z, hz, hxz⟩
              · rw [hu1f] at hu1t; cases hu1t
              · have hzm : z = m := hZm z ((h_mem_zSet z).mpr ⟨a, ha, hop, hag, Or.inl ⟨hu0, hz⟩⟩)
                rcases (h_C1_bW x).mp hbx with ⟨w, hwB, hsw, hxw⟩
                exact (graphFun_iff x).mpr ⟨w, m, hBL_m w hwB hsw, hxw, hzm ▸ hxz⟩
            · rcases h1 with ⟨hu1, hbx⟩ | ⟨u1, hu1, hxu1⟩
              · have hzm : u0 = m := hZm u0 ((h_mem_zSet u0).mpr ⟨a, ha, hop, hag, Or.inr ⟨hu1, hu0⟩⟩)
                rcases (h_C1_bW x).mp hbx with ⟨w, hwB, hsw, hxw⟩
                exact (graphFun_iff x).mpr ⟨w, m, hBL_m w hwB hsw, hxw, hzm ▸ hxu0⟩
              · apply h_clean_and a ha hop hag x
                change wval C x (n + a) = true
                rw [wval_gate_and hAO x ha hop, Bool.and_eq_true]
                exact ⟨(h_wval_dirty _ (by have := opnd_lt hAO ha 0; omega) hd0 x).mpr (Or.inr ⟨u0, hu0, hxu0⟩),
                       (h_wval_dirty _ (by have := opnd_lt hAO ha 1; omega) hd1 x).mpr (Or.inr ⟨u1, hu1, hxu1⟩)⟩
          have h_all_bf : ∀ k < C.gates.length, BelowF G C k → BelowF G D (delGateMap g k) := by
            intro k
            induction k using Nat.strongRecOn with
            | ind k ih =>
              intro hk hbf
              have hkg : k ≠ g := fun heq => hg_dirty (heq ▸ hbf)
              rcases hAO.1 _ (gateAt_mem hk) with hop | hop
              · exact h_and_bf k hk hop hkg
              · intro x hDx
                have hk1 : k < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
                have hk' : delGateMap g k < D.gates.length := by
                  rw [delCircuit_len, restrictTwoSided_len]; unfold delGateMap; split_ifs <;> omega
                have hgt1 := h_C1_clean k hk hbf
                have hgate : (gateAt D (delGateMap g k)).op = GateOp.or := by
                  rw [delCircuit_gateAt_src hg_lt1 hk1 hkg, hgt1, hop]
                have hop0 : opnd D (delGateMap g k) 0 = delMap n g bW (opnd C k 0) := by
                  rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 0]; unfold opnd; rw [hgt1]
                have hop1 : opnd D (delGateMap g k) 1 = delMap n g bW (opnd C k 1) := by
                  rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 1]; unfold opnd; rw [hgt1]
                change wval D x (n + delGateMap g k) = true at hDx
                rw [wval_gate_or hAO' x hk' hgate, Bool.or_eq_true, hop0, hop1] at hDx
                have hi0 := h_clean_or_inputs k hk hbf hop 0
                have hi1 := h_clean_or_inputs k hk hbf hop 1
                have hne0 : opnd C k 0 - n ≠ g := fun heq => hg_dirty (heq ▸ hi0.2.2)
                have hne1 : opnd C k 1 - n ≠ g := fun heq => hg_dirty (heq ▸ hi1.2.2)
                have heq0 : opnd C k 0 = n + (opnd C k 0 - n) := by omega
                have heq1 : opnd C k 1 = n + (opnd C k 1 - n) := by omega
                rcases hDx with h0 | h1
                · rw [heq0, delMap_gate n g bW _ hne0] at h0
                  exact ih _ hi0.2.1 (by omega) hi0.2.2 x h0
                · rw [heq1, delMap_gate n g bW _ hne1] at h1
                  exact ih _ hi1.2.1 (by omega) hi1.2.2 x h1
          have h_edge_keep : ∀ p q : Fin n, G.Adj p q → s p = s v →
              ∀ k < C.gates.length, BelowF G C k →
                gateVal n C k (pairInput p q) = true → gateVal n D (delGateMap g k) (pairInput p q) = true := by
            intro p q hpq hsp k
            have hsq : s q ≠ s v := fun heq => h_bip p q hpq (hsp.trans heq.symm)
            induction k using Nat.strongRecOn with
            | ind k ih =>
              intro hk hbf hCk
              have hkg : k ≠ g := fun heq => hg_dirty (heq ▸ hbf)
              have hk1 : k < C1.gates.length := by rw [restrictTwoSided_len]; exact hk
              have hk' : delGateMap g k < D.gates.length := by
                rw [delCircuit_len, restrictTwoSided_len]; unfold delGateMap; split_ifs <;> omega
              have hgt1 := h_C1_clean k hk hbf
              have hop0 : opnd D (delGateMap g k) 0 = delMap n g bW (opnd C k 0) := by
                rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 0]; unfold opnd; rw [hgt1]
              have hop1 : opnd D (delGateMap g k) 1 = delMap n g bW (opnd C k 1) := by
                rw [delCircuit_opnd hAO1 hg_lt1 hk1 hkg 1]; unfold opnd; rw [hgt1]
              rcases hAO.1 _ (gateAt_mem hk) with hop | hop
              · have hgate : (gateAt D (delGateMap g k)).op = GateOp.and := by
                  rw [delCircuit_gateAt_src hg_lt1 hk1 hkg, hgt1, hop]
                change wval C (pairInput p q) (n + k) = true at hCk
                rw [wval_gate_and hAO _ hk hop, Bool.and_eq_true] at hCk
                change wval D (pairInput p q) (n + delGateMap g k) = true
                rw [wval_gate_and hAO' _ hk' hgate, Bool.and_eq_true, hop0, hop1]
                have hd0 : ¬ WireBelowF G C (opnd C k 0) := h_no_imp k hk hop _ (opnd_mem hAO hk 0)
                have hd1 : ¬ WireBelowF G C (opnd C k 1) := h_no_imp k hk hop _ (opnd_mem hAO hk 1)
                have hnts_k : ¬ isTwoSided G C s v g (n + k) := fun h => h.2.1 hbf
                have h0 := (h_wval_dirty _ (by have := opnd_lt hAO hk 0; omega) hd0 _).mp hCk.1
                have h1 := (h_wval_dirty _ (by have := opnd_lt hAO hk 1; omega) hd1 _).mp hCk.2
                have h_g_to_b : (∃ z ∈ Z, pairInput p q z = true) →
                    gateVal n C g (pairInput p q) = true → wval C1 (pairInput p q) bW = true := by
                  rintro ⟨z, hzZ, hpqz⟩ hgx
                  have hzm : z = m := hZm z hzZ
                  rw [hzm] at hpqz
                  simp only [pairInput, decide_eq_true_eq] at hpqz
                  have hqm : q = m := by
                    rcases hpqz with hmp | hmq
                    · exact (h_zSet_color m hmZ (hmp ▸ hsp)).elim
                    · exact hmq.symm
                  rw [hqm] at hgx ⊢
                  rcases ((hg_AB (pairInput p m)).mp hgx).2 with ⟨w, hwB, hpqw⟩
                  simp only [pairInput, decide_eq_true_eq] at hpqw
                  rcases hpqw with hwp | hwm
                  · exact (h_C1_bW (pairInput p m)).mpr ⟨w, hwB, hwp ▸ hsp, by simp [pairInput, hwp]⟩
                  · exact (hm_not_B (hwm ▸ hwB)).elim
                rw [h_D_dirty _ (by have := opnd_lt hAO hk 0; omega) hd0 (h_no_ts_reads_ts k hk hkg hnts_k 0),
                  h_D_dirty _ (by have := opnd_lt hAO hk 1; omega) hd1 (h_no_ts_reads_ts k hk hkg hnts_k 1)]
                rcases h0 with ⟨hu0, hgx⟩ | h0s
                · have hu1f : usesG n C g (opnd C k 1) = false := by
                    cases h : usesG n C g (opnd C k 1)
                    · rfl
                    · exact (h_and_not_both_g k hk hop hkg ⟨hu0, h⟩).elim
                  rcases h1 with ⟨hu1t, _⟩ | ⟨z, hz, hpqz⟩
                  · rw [hu1f] at hu1t; cases hu1t
                  · have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inl ⟨hu0, hz⟩⟩
                    exact ⟨Or.inl ⟨hu0, h_g_to_b ⟨z, hzZ, hpqz⟩ hgx⟩, Or.inr ⟨z, hz, hpqz⟩⟩
                · rcases h1 with ⟨hu1, hgx⟩ | h1s
                  · rcases h0s with ⟨z, hz, hpqz⟩
                    have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inr ⟨hu1, hz⟩⟩
                    exact ⟨Or.inr ⟨z, hz, hpqz⟩, Or.inl ⟨hu1, h_g_to_b ⟨z, hzZ, hpqz⟩ hgx⟩⟩
                  · exact ⟨Or.inr h0s, Or.inr h1s⟩
              · have hgate : (gateAt D (delGateMap g k)).op = GateOp.or := by
                  rw [delCircuit_gateAt_src hg_lt1 hk1 hkg, hgt1, hop]
                change wval C (pairInput p q) (n + k) = true at hCk
                rw [wval_gate_or hAO _ hk hop, Bool.or_eq_true] at hCk
                change wval D (pairInput p q) (n + delGateMap g k) = true
                rw [wval_gate_or hAO' _ hk' hgate, Bool.or_eq_true, hop0, hop1]
                have hi0 := h_clean_or_inputs k hk hbf hop 0
                have hi1 := h_clean_or_inputs k hk hbf hop 1
                have hne0 : opnd C k 0 - n ≠ g := fun heq => hg_dirty (heq ▸ hi0.2.2)
                have hne1 : opnd C k 1 - n ≠ g := fun heq => hg_dirty (heq ▸ hi1.2.2)
                have heq0 : opnd C k 0 = n + (opnd C k 0 - n) := by omega
                have heq1 : opnd C k 1 = n + (opnd C k 1 - n) := by omega
                rcases hCk with h0 | h1
                · left
                  rw [heq0, delMap_gate n g bW _ hne0]
                  exact ih _ hi0.2.1 (by omega) hi0.2.2
                    (by change wval C (pairInput p q) (n + (opnd C k 0 - n)) = true; rw [← heq0]; exact h0)
                · right
                  rw [heq1, delMap_gate n g bW _ hne1]
                  exact ih _ hi1.2.1 (by omega) hi1.2.2
                    (by change wval C (pairInput p q) (n + (opnd C k 1 - n)) = true; rw [← heq1]; exact h1)
          have h_Dout : ∀ x, circuitFun n D x = gateVal n D (delGateMap g (C.output - n)) x := by
            intro x
            change wval D x (delMap n g bW C.output) = wval D x (n + delGateMap g (C.output - n))
            have h_out_ne : C.output - n ≠ g := by omega
            have h_out_eq : C.output = n + (C.output - n) := by omega
            conv_lhs => rw [h_out_eq]
            rw [delMap_gate n g bW _ h_out_ne]
          refine ⟨D, hAO', by rw [Circuit.size, delCircuit_len, restrictTwoSided_len]; change C.gates.length-1<C.gates.length; omega, ?_, ?_⟩
          · apply circuitFun_eq_graphFun_of hAO'
            · intro x hx
              rw [h_Dout] at hx
              exact h_all_bf (C.output - n) (by omega) h_out_below_gate x hx
            · intro p q hpq
              have hCpq : gateVal n C (C.output - n) (pairInput p q) = true := by
                have h1 : circuitFun n C (pairInput p q) = true := by
                  rw [h_eq]; exact (graphFun_pairInput_iff G p q).mpr hpq
                change wval C (pairInput p q) C.output = true at h1
                have : C.output = n + (C.output - n) := by omega
                rw [this] at h1; exact h1
              by_cases hsp : s p = s v
              · rw [h_Dout]
                exact h_edge_keep p q hpq hsp (C.output - n) (by omega) h_out_below_gate hCpq
              · have hsq : s q = s v := bool_eq_of_ne_ne (h_bip p q hpq) hsp
                have hsym : pairInput p q = pairInput q p := by
                  funext t; simp [pairInput, or_comm]
                rw [hsym, h_Dout]
                exact h_edge_keep q p hpq.symm hsq (C.output - n) (by omega) h_out_below_gate (hsym ▸ hCpq)
          · intro k' hk' hop'
            rw [delCircuit_len, restrictTwoSided_len] at hk'
            let src := if k' < g then k' else k' + 1
            have hsrc_lt : src < C.gates.length := by dsimp [src]; split_ifs <;> omega
            have hsrc_ne : src ≠ g := by dsimp [src]; split_ifs <;> omega
            have hsrc1 : src < C1.gates.length := by rw [restrictTwoSided_len]; exact hsrc_lt
            have hdgm : delGateMap g src = k' := by dsimp [src, delGateMap]; split_ifs <;> omega
            have hop1 : (gateAt C1 src).op = GateOp.and := by
              rw [← hdgm, delCircuit_gateAt_src hg_lt1 hsrc1 hsrc_ne] at hop'
              exact hop'
            have hop : (gateAt C src).op = GateOp.and := by
              rw [restrictTwoSided_gateAt G C s v g src hsrc_lt] at hop1
              split_ifs at hop1 <;> exact hop1
            rw [← hdgm]
            exact h_and_bf src hsrc_lt hop hsrc_ne
    · have hZ2 : 1 < Z.card := by omega
      have hAB_inter : ∀ u ∈ A, u ∈ B → u = v := by
        intro u huA huB
        by_contra huv
        rcases Finset.one_lt_card.mp hZ2 with ⟨z1, hz1, z2, hz2, hz12⟩
        have hadj_u : ∀ z ∈ Z, G.Adj u z := by
          intro z hz
          rw [← graphFun_pairInput_iff G u z]
          apply h_zSet_below z hz (pairInput u z)
          · rw [hg_AB]
            exact ⟨⟨u, huA, by simp [pairInput]⟩, ⟨u, huB, by simp [pairInput]⟩⟩
          · simp [pairInput]
        exact hz12 (noFourCycle_unique h_c4 huv (hadj_u z1 hz1) (h_zSet_adj_v z1 hz1)
          (hadj_u z2 hz2) (h_zSet_adj_v z2 hz2))
      by_cases hBZ : ∃ m ∈ B, m ∈ Z
      · rcases hBZ with ⟨m, hmB, hmZ⟩
        by_cases hA_only_v : ∀ u ∈ A, u = v
        · let D := delCircuit n C g v.val
          have hvl : v.val < n + g := by omega
          have hAO' := delCircuit_isAO2 hAO hg_lt hvl
          have hg_eq_v : ∀ x, gateVal n C g x = true ↔ wval C x v.val = true := by
            intro x
            rw [hg_AB, wval_input C x v.val v.isLt]
            constructor
            · rintro ⟨⟨u, huA, hxu⟩, _⟩
              rw [hA_only_v u huA] at hxu; exact hxu
            · intro hxv
              exact ⟨⟨v, hv_A, hxv⟩, ⟨v, hv_B, hxv⟩⟩
          refine ⟨D, hAO', delCircuit_size_strict n C g v.val hg_lt, ?_, ?_⟩
          · funext x
            have hle_out := delCircuit_wval_le hAO hg_lt hvl x (hg_eq_v x).mpr C.output (by omega)
            have hge_out := delCircuit_wval_ge hAO hg_lt hvl x (hg_eq_v x).mp C.output (by omega)
            cases hDx : circuitFun n D x with
            | true =>
              have hCx : circuitFun n C x = true := hle_out hDx
              rw [h_eq] at hCx; exact hCx.symm
            | false =>
              cases hFx : graphFun G ∅ x with
              | false => rfl
              | true =>
                have hCx : circuitFun n C x = true := by rw [h_eq]; exact hFx
                have hDt : circuitFun n D x = true := hge_out hCx
                rw [hDx] at hDt; cases hDt
          · intro k' hk' hop' x hDx
            rw [delCircuit_len] at hk'
            let src := if k' < g then k' else k' + 1
            have hsrc_lt : src < C.gates.length := by dsimp [src]; split_ifs <;> omega
            have hsrc_ne : src ≠ g := by dsimp [src]; split_ifs <;> omega
            have hdgm : delGateMap g src = k' := by dsimp [src, delGateMap]; split_ifs <;> omega
            have hop : (gateAt C src).op = GateOp.and := by
              rw [← hdgm, delCircuit_gateAt_src hg_lt hsrc_lt hsrc_ne] at hop'
              exact hop'
            apply h_clean_and src hsrc_lt hop hsrc_ne x
            apply delCircuit_wval_le hAO hg_lt hvl x (hg_eq_v x).mpr (n + src) (by omega)
            rw [delMap_gate n g v.val src hsrc_ne, hdgm]
            exact hDx
        · push_neg at hA_only_v
          rcases hA_only_v with ⟨u0, hu0A, hu0v⟩
          have hAm : ∀ u ∈ A, G.Adj u m := by
            intro u huA
            rw [← graphFun_pairInput_iff G u m]
            apply h_zSet_below m hmZ (pairInput u m)
            · rw [hg_AB]
              exact ⟨⟨u, huA, by simp [pairInput]⟩, ⟨m, hmB, by simp [pairInput]⟩⟩
            · simp [pairInput]
          have hBZ_uniq : ∀ m' ∈ B, m' ∈ Z → m' = m := by
            intro m' hm'B hm'Z
            have hu0m' : G.Adj u0 m' := by
              rw [← graphFun_pairInput_iff G u0 m']
              apply h_zSet_below m' hm'Z (pairInput u0 m')
              · rw [hg_AB]
                exact ⟨⟨u0, hu0A, by simp [pairInput]⟩, ⟨m', hm'B, by simp [pairInput]⟩⟩
              · simp [pairInput]
            exact noFourCycle_unique h_c4 hu0v hu0m' (h_zSet_adj_v m' hm'Z)
              (hAm u0 hu0A) (h_zSet_adj_v m hmZ)
          have hms : s m ≠ s v := h_zSet_color m hmZ
          have hbW_ge : n ≤ bW := by
            by_contra hlt
            have h1 := hv_B
            have h2 := hmB
            dsimp [B] at h1 h2
            rw [varSet_input n C g bW (by omega)] at h1 h2
            simp only [Finset.mem_singleton] at h1 h2
            subst h1; subst h2
            exact hms rfl
          let jb := bW - n
          have hbW_eq : bW = n + jb := by omega
          have hjb_lt : jb < g := by omega
          have haW_ne : aW ≠ n + jb := by
            intro heq
            have : m ∈ A := by
              dsimp [A]; rw [heq, ← hbW_eq]; exact hmB
            exact hms (hA_L m this)
          have hno_jb : ∀ k < C.gates.length, k ≠ g → n + jb ∉ (gateAt C k).inputs := by
            intro k hk hkg hmem
            have hjk : jb < k := by
              have := hAO.2.1 k hk (n + jb) hmem; omega
            by_cases hbf : BelowF G C k
            · rcases hAO.1 _ (gateAt_mem hk) with hop | hop
              · rw [gate_inputs_eq hAO hk] at hmem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with heq | heq
                · exact h_clean_and_no_two_sided k hk hop hkg 0
                    ⟨⟨v, by rw [← heq, ← hbW_eq]; exact hv_B, rfl⟩,
                     ⟨m, by rw [← heq, ← hbW_eq]; exact hmB, hms⟩⟩
                · exact h_clean_and_no_two_sided k hk hop hkg 1
                    ⟨⟨v, by rw [← heq, ← hbW_eq]; exact hv_B, rfl⟩,
                     ⟨m, by rw [← heq, ← hbW_eq]; exact hmB, hms⟩⟩
              · rw [gate_inputs_eq hAO hk] at hmem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with heq | heq
                · have hi := h_clean_or_inputs k hk hbf hop 0
                  rw [← heq] at hi
                  apply hbW_d
                  rw [hbW_eq]
                  have : n + jb - n = jb := by omega
                  rw [this] at hi
                  exact hi.2.2
                · have hi := h_clean_or_inputs k hk hbf hop 1
                  rw [← heq] at hi
                  apply hbW_d
                  rw [hbW_eq]
                  have : n + jb - n = jb := by omega
                  rw [this] at hi
                  exact hi.2.2
            · have hsub : B ⊆ varSet n C g (n + k) := by
                rw [varSet_gate hAO g k hk hkg]
                rw [gate_inputs_eq hAO hk] at hmem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with heq | heq
                · rw [← heq, ← hbW_eq]; exact Finset.subset_union_left
                · rw [← heq, ← hbW_eq]; exact Finset.subset_union_right
              have hle := h_two_sided_le_b k hk hbf hkg ⟨v, hsub hv_B, rfl⟩ ⟨m, hsub hmB, hms⟩
              omega
          exfalso
          apply h_exception aW bW v m
          refine ⟨haW_lt,hbW_lt,hbW_ge,?_,haWmem,hbWmem,haW_val,hbW_val,hg_ab,
            hAB_inter,hv_A,hv_B,hmB,⟨u0,hu0A,hu0v⟩,hAm,hA_L,?_,?_,hBZ_uniq,h_wval_dirty⟩
          · simpa only [hbW_eq] using haW_ne
          · intro k hk hkg
            simpa only [hbW_eq] using hno_jb k hk hkg
          · exact (h_mem_zSet m).mp hmZ
      · push_neg at hBZ
        let D := delCircuit n C g v.val
        have hvl : v.val < n + g := by omega
        have hAO' := delCircuit_isAO2 hAO hg_lt hvl
        have hle_v : ∀ x, wval C x v.val = true → gateVal n C g x = true := by
          intro x hxv
          rw [wval_input C x v.val v.isLt] at hxv
          rw [hg_AB]
          exact ⟨⟨v, hv_A, hxv⟩, ⟨v, hv_B, hxv⟩⟩
        have h_edge_keep : ∀ p q : Fin n, G.Adj p q → s p = s v →
            ∀ k < C.gates.length, BelowF G C k →
              gateVal n C k (pairInput p q) = true →
              gateVal n D (delGateMap g k) (pairInput p q) = true := by
          intro p q hpq hsp k
          have hsq : s q ≠ s v := fun heq => h_bip p q hpq (hsp.trans heq.symm)
          induction k using Nat.strongRecOn with
          | ind k ih =>
            intro hk hbf hCk
            have hkg : k ≠ g := fun heq => hg_dirty (heq ▸ hbf)
            have hk' : delGateMap g k < D.gates.length := by
              rw [delCircuit_len]; unfold delGateMap; split_ifs <;> omega
            rcases hAO.1 _ (gateAt_mem hk) with hop | hop
            · have hgate : (gateAt D (delGateMap g k)).op = GateOp.and := by
                rw [delCircuit_gateAt_src hg_lt hk hkg, hop]
              change wval C (pairInput p q) (n + k) = true at hCk
              rw [wval_gate_and hAO _ hk hop, Bool.and_eq_true] at hCk
              change wval D (pairInput p q) (n + delGateMap g k) = true
              rw [wval_gate_and hAO' _ hk' hgate, Bool.and_eq_true,
                delCircuit_opnd hAO hg_lt hk hkg 0, delCircuit_opnd hAO hg_lt hk hkg 1]
              have hd0 : ¬ WireBelowF G C (opnd C k 0) := h_no_imp k hk hop _ (opnd_mem hAO hk 0)
              have hd1 : ¬ WireBelowF G C (opnd C k 1) := h_no_imp k hk hop _ (opnd_mem hAO hk 1)
              have h0 := (h_wval_dirty _ (by have := opnd_lt hAO hk 0; omega) hd0 _).mp hCk.1
              have h1 := (h_wval_dirty _ (by have := opnd_lt hAO hk 1; omega) hd1 _).mp hCk.2
              have h_g_to_v : (∃ z ∈ Z, pairInput p q z = true) →
                  gateVal n C g (pairInput p q) = true → wval C (pairInput p q) v.val = true := by
                rintro ⟨z, hzZ, hpqz⟩ hgx
                simp only [pairInput, decide_eq_true_eq] at hpqz
                have hzq : z = q := by
                  rcases hpqz with rfl | rfl
                  · exact (h_zSet_color z hzZ hsp).elim
                  · rfl
                have hqZ : q ∈ Z := hzq ▸ hzZ
                rcases (hg_AB (pairInput p q)).mp hgx with ⟨⟨u, huA, hpqu⟩, ⟨w, hwB, hpqw⟩⟩
                simp only [pairInput, decide_eq_true_eq] at hpqu hpqw
                have hpA : p ∈ A := by
                  rcases hpqu with rfl | huq
                  · exact huA
                  · exact (hsq (huq ▸ hA_L u huA)).elim
                have hpB : p ∈ B := by
                  rcases hpqw with rfl | hwq
                  · exact hwB
                  · exact (hBZ q (hwq ▸ hwB) hqZ).elim
                have hpv : p = v := hAB_inter p hpA hpB
                subst hpv
                rw [wval_input C _ p.val p.isLt]
                simp [pairInput]
              rw [h_del_wval_dirty v.val hvl _ (by have := opnd_lt hAO hk 0; omega) hd0,
                h_del_wval_dirty v.val hvl _ (by have := opnd_lt hAO hk 1; omega) hd1]
              rcases h0 with ⟨hu0, hgx⟩ | h0s
              · have hu1f : usesG n C g (opnd C k 1) = false := by
                  cases h : usesG n C g (opnd C k 1)
                  · rfl
                  · exact (h_and_not_both_g k hk hop hkg ⟨hu0, h⟩).elim
                rcases h1 with ⟨hu1t, _⟩ | ⟨z, hz, hpqz⟩
                · rw [hu1f] at hu1t; cases hu1t
                · have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inl ⟨hu0, hz⟩⟩
                  exact ⟨Or.inl ⟨hu0, h_g_to_v ⟨z, hzZ, hpqz⟩ hgx⟩, Or.inr ⟨z, hz, hpqz⟩⟩
              · rcases h1 with ⟨hu1, hgx⟩ | h1s
                · rcases h0s with ⟨z, hz, hpqz⟩
                  have hzZ : z ∈ Z := (h_mem_zSet z).mpr ⟨k, hk, hop, hkg, Or.inr ⟨hu1, hz⟩⟩
                  exact ⟨Or.inr ⟨z, hz, hpqz⟩, Or.inl ⟨hu1, h_g_to_v ⟨z, hzZ, hpqz⟩ hgx⟩⟩
                · exact ⟨Or.inr h0s, Or.inr h1s⟩
            · have hgate : (gateAt D (delGateMap g k)).op = GateOp.or := by
                rw [delCircuit_gateAt_src hg_lt hk hkg, hop]
              change wval C (pairInput p q) (n + k) = true at hCk
              rw [wval_gate_or hAO _ hk hop, Bool.or_eq_true] at hCk
              change wval D (pairInput p q) (n + delGateMap g k) = true
              rw [wval_gate_or hAO' _ hk' hgate, Bool.or_eq_true,
                delCircuit_opnd hAO hg_lt hk hkg 0, delCircuit_opnd hAO hg_lt hk hkg 1]
              have hi0 := h_clean_or_inputs k hk hbf hop 0
              have hi1 := h_clean_or_inputs k hk hbf hop 1
              have hne0 : opnd C k 0 - n ≠ g := fun heq => hg_dirty (heq ▸ hi0.2.2)
              have hne1 : opnd C k 1 - n ≠ g := fun heq => hg_dirty (heq ▸ hi1.2.2)
              have heq0 : opnd C k 0 = n + (opnd C k 0 - n) := by omega
              have heq1 : opnd C k 1 = n + (opnd C k 1 - n) := by omega
              rcases hCk with h0 | h1
              · left
                rw [heq0, delMap_gate n g v.val _ hne0]
                exact ih _ hi0.2.1 (by omega) hi0.2.2
                  (by change wval C (pairInput p q) (n + (opnd C k 0 - n)) = true; rw [← heq0]; exact h0)
              · right
                rw [heq1, delMap_gate n g v.val _ hne1]
                exact ih _ hi1.2.1 (by omega) hi1.2.2
                  (by change wval C (pairInput p q) (n + (opnd C k 1 - n)) = true; rw [← heq1]; exact h1)
        refine ⟨D, hAO', delCircuit_size_strict n C g v.val hg_lt, ?_, ?_⟩
        · apply circuitFun_eq_graphFun_of hAO'
          · intro x hx
            exact h_out_below x (delCircuit_wval_le hAO hg_lt hvl x (hle_v x) C.output (by omega) hx)
          · intro p q hpq
            have hCpq : gateVal n C (C.output - n) (pairInput p q) = true := by
              have h1 : circuitFun n C (pairInput p q) = true := by
                rw [h_eq]; exact (graphFun_pairInput_iff G p q).mpr hpq
              change wval C (pairInput p q) C.output = true at h1
              have : C.output = n + (C.output - n) := by omega
              rw [this] at h1; exact h1
            have hDout : ∀ y, circuitFun n D y = gateVal n D (delGateMap g (C.output - n)) y := by
              intro y
              change wval D y (delMap n g v.val C.output) = wval D y (n + delGateMap g (C.output - n))
              have h_out_ne : C.output - n ≠ g := by omega
              have h_out_eq : C.output = n + (C.output - n) := by omega
              conv_lhs => rw [h_out_eq]
              rw [delMap_gate n g v.val _ h_out_ne]
            by_cases hsp : s p = s v
            · rw [hDout]
              exact h_edge_keep p q hpq hsp (C.output - n) (by omega) h_out_below_gate hCpq
            · have hsq : s q = s v := bool_eq_of_ne_ne (h_bip p q hpq) hsp
              have hsym : pairInput p q = pairInput q p := by
                funext t; simp [pairInput, or_comm]
              rw [hsym, hDout]
              exact h_edge_keep q p hpq.symm hsq (C.output - n) (by omega) h_out_below_gate (hsym ▸ hCpq)
        · intro k' hk' hop' x hDx
          rw [delCircuit_len] at hk'
          let src := if k' < g then k' else k' + 1
          have hsrc_lt : src < C.gates.length := by dsimp [src]; split_ifs <;> omega
          have hsrc_ne : src ≠ g := by dsimp [src]; split_ifs <;> omega
          have hdgm : delGateMap g src = k' := by dsimp [src, delGateMap]; split_ifs <;> omega
          have hop : (gateAt C src).op = GateOp.and := by
            rw [← hdgm, delCircuit_gateAt_src hg_lt hsrc_lt hsrc_ne] at hop'
            exact hop'
          apply h_clean_and src hsrc_lt hop hsrc_ne x
          apply delCircuit_wval_le hAO hg_lt hvl x (hle_v x) (n + src) (by omega)
          rw [delMap_gate n g v.val src hsrc_ne, hdgm]
          exact hDx
  by_cases h0L : ∀ u ∈ varSet n C g (opnd C g 0), s u = s v
  · exact h_solve_ordered (opnd C g 0) (opnd C g 1) h_g_op0_lt h_g_op1_lt h_g_op0_dirty h_g_op1_dirty
      (fun x => wval_gate_and hAO x hg_lt hg_and)
      (fun w hw => by
        rw [gate_inputs_eq hAO hg_lt] at hw
        simpa using hw)
      (opnd_mem hAO hg_lt 0) (opnd_mem hAO hg_lt 1) h0L
  · have h1L : ∀ w ∈ varSet n C g (opnd C g 1), s w = s v := by
      push_neg at h0L
      rcases h0L with ⟨u, hu, hsu⟩
      intro w hw
      by_contra hsw
      rcases h_zSet_nonempty with ⟨z, hzZ⟩
      have hsz := h_zSet_color z hzZ
      have htri : graphFun G ∅ (tripleInput u w z) = true := by
        apply h_zSet_below z hzZ (tripleInput u w z)
        · rw [h_g_val]
          exact ⟨⟨u, hu, by simp [tripleInput]⟩, ⟨w, hw, by simp [tripleInput]⟩⟩
        · simp [tripleInput]
      rw [graphFun_tripleInput_iff] at htri
      rcases htri with hadj | hadj | hadj
      · exact h_bip u w hadj (bool_eq_of_ne_ne (Ne.symm hsu) (Ne.symm hsw))
      · exact h_bip u z hadj (bool_eq_of_ne_ne (Ne.symm hsu) (Ne.symm hsz))
      · exact h_bip w z hadj (bool_eq_of_ne_ne (Ne.symm hsw) (Ne.symm hsz))
    exact h_solve_ordered (opnd C g 1) (opnd C g 0) h_g_op1_lt h_g_op0_lt h_g_op1_dirty h_g_op0_dirty
      (fun x => (wval_gate_and hAO x hg_lt hg_and).trans (Bool.and_comm _ _))
      (fun w hw => by
        rw [gate_inputs_eq hAO hg_lt] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        exact hw.symm)
      (opnd_mem hAO hg_lt 1) (opnd_mem hAO hg_lt 0) h1L


lemma least_exceptional (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (g : ℕ)
    (h_bip : ∀u v : Fin n,G.Adj u v → s u≠s v) (h_c4 : NoFourCycle G)
    (h_least : IsLeastAO G C) (h_lift : IsLiftFixedPoint G C)
    (h_no_imp : ∀k<C.gates.length,(gateAt C k).op=GateOp.and →
      ∀t∈(gateAt C k).inputs,¬∀x : Fin n → Bool,
        Circuit.eval ⟨C.gates,t⟩ (List.ofFn x)=true → graphFun G ∅ x=true)
    (h_cone : ∀k<C.gates.length,InOutputCone n C k)
    (hg : g<C.gates.length) (hand : (gateAt C g).op=GateOp.and)
    (hdirty : ¬BelowF G C g)
    (hunique : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → k≠g → BelowF G C k)
    (hunit : ∃v : Fin n,gateVal n C g (unitInput v)=true) :
    ∃(aW bW : ℕ)(v m : Fin n),Exceptional G C s g aW bW v m := by
  classical
  by_contra hn
  have hexc : ∀(aW bW : ℕ)(v m : Fin n),Exceptional G C s g aW bW v m → False := by
    intro aW bW v m h
    exact hn ⟨aW,bW,v,m,h⟩
  obtain ⟨D,hD,hsmall,hfun,_⟩ := main n G C s g h_bip h_c4 h_least.1 h_least.2.1
    h_lift h_no_imp h_cone hg hand hdirty hunique hunit hexc
  exact (Nat.not_lt_of_ge (h_least.2.2 D hD hfun)) hsmall


lemma usesG_reach {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g : ℕ) :
    ∀w,w<n+C.gates.length → usesG n C g w=true →
      ∃k,w=n+k ∧ k<C.gates.length ∧ (g=k ∨ InCone n C g k) := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw ht
    by_cases hraw : w<n
    · rw [usesG_input n C g w hraw] at ht
      cases ht
    by_cases hself : w=n+g
    · exact ⟨g,hself,by omega,Or.inl rfl⟩
    let k := w-n
    have hwk : w=n+k := by dsimp [k];omega
    have hk : k<C.gates.length := by omega
    have hkg : k≠g := by omega
    rw [hwk,usesG_gate hAO g k hk hkg,Bool.or_eq_true] at ht
    have hchild : ∀b : Fin 2,usesG n C g (opnd C k b)=true → InCone n C g k := by
      intro b hb
      have hlt : opnd C k b<w := by have := opnd_lt hAO hk b;omega
      obtain ⟨l,hl,hll,hreach⟩ := ih (opnd C k b) hlt (by omega) hb
      apply (inCone_iff hk).mpr
      refine ⟨opnd C k b,opnd_mem hAO hk b,by omega,opnd_lt hAO hk b,?_⟩
      have he : opnd C k b-n=l := by omega
      rw [he]
      exact hreach
    refine ⟨k,hwk,hk,Or.inr ?_⟩
    rcases ht with h0 | h1
    · exact hchild 0 h0
    · exact hchild 1 h1

end PEqualNP.Outside.L_meta_3754.Strict3653

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

namespace PEqualNP.Outside.L_meta_3754.Glue
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma support_of_pure {n : ℕ} (C : Circuit) (w : ℕ) (A : Finset (Fin n))
    (hpure : ∀x : Fin n → Bool,PEqualNP.ReadTwo.wval C x w=true ↔ ∃u∈A,x u=true) :
    Ledger.singletonSupport n C w=A := by
  ext u
  constructor
  · intro hu
    obtain ⟨v,hv,hvu⟩ := (hpure (Ledger.singletonInput u)).mp (Finset.mem_filter.mp hu).2
    have he : v=u := by simpa [Ledger.singletonInput] using hvu
    simpa only [he] using hv
  · intro hu
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(hpure (Ledger.singletonInput u)).mpr ?_⟩
    exact ⟨u,hu,by simp [Ledger.singletonInput]⟩

lemma select_exception {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (g aW bW : ℕ) (v m : Fin n)
    (hC : IsLeastAO G C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (hcone : PEqualNP.Core.InOutputCone n C g) (hdirty : ¬BelowF G C g)
    (hclean : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → k≠g → BelowF G C k)
    (e : Strict3653.Exceptional G C s g aW bW v m) :
    ∃(j p : ℕ)(u : Fin n),j<g ∧ (gateAt C j).op=GateOp.or ∧ p<n+j ∧
      ((gateAt C j).inputs=[v.val,p] ∨ (gateAt C j).inputs=[p,v.val]) ∧
      wireVal n C p (Ledger.singletonInput v)=false ∧ u≠v ∧
      wireVal n C p (Ledger.singletonInput u)=true ∧
      u∈Ledger.singletonSupport n C aW ∧ G.Adj u m ∧
      wireVal n C (n+j) (Ledger.singletonInput v)=true ∧
      wireVal n C (n+j) (Ledger.singletonInput u)=true ∧
      j≠bW-n ∧ ¬InCone n C j (bW-n) ∧ p≠bW := by
  have hg : g<C.gates.length := hcone.1
  have hA := support_of_pure C aW (Strict3653.varSet n C g aW) e.pureA
  have hB := support_of_pure C bW (Strict3653.varSet n C g bW) e.pureB
  have hcard : 2≤(Ledger.singletonSupport n C aW).card := by
    rw [hA]
    obtain ⟨u,hu,huv⟩ := e.otherA
    have hsub : ({v,u} : Finset (Fin n))⊆Strict3653.varSet n C g aW := by
      intro w hw
      simp only [Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact e.vInA
      · exact hu
    have hc := Finset.card_le_card hsub
    simpa [huv,Ne.symm huv] using hc
  have hall : ∀i,InCone n C i g → (gateAt C i).op=GateOp.or := by
    intro i hi
    apply Ledger.earliest_dirty_ancestor_or G C hC.1 hfixed g hcone hdirty _ i hi
    intro k hkg hand
    exact hclean k (by omega) hand (by omega)
  obtain ⟨j,p,u,hjg,_,hjor,hp,hin,hpv,huv,hpu,huA,hjv,hju⟩ :=
    Select.select_pure_operand G C hC g hcone.1 hall aW e.aMember hcard v (by rw [hA];exact e.vInA)
  have hb : bW-n<C.gates.length := by have := e.bBound;omega
  have hbeq : n+(bW-n)=bW := by have := e.bGate;omega
  have hbg : InCone n C (bW-n) g :=
    (Ledger.inCone_iff n C (bW-n) g hcone.1).mpr
      ⟨bW,e.bMember,e.bGate,e.bBound,Or.inl rfl⟩
  have hbor : (gateAt C (bW-n)).op=GateOp.or := hall _ hbg
  have hborAnc : ∀i,InCone n C i (bW-n) → (gateAt C i).op=GateOp.or := by
    intro i hi
    exact hall i (Ledger.inCone_trans n C i (bW-n) g hcone.1 hi hbg)
  have hinter : Ledger.singletonSupport n C aW ∩ Ledger.singletonSupport n C (n+(bW-n))={v} := by
    rw [hbeq,hA,hB]
    ext z
    simp only [Finset.mem_inter,Finset.mem_singleton]
    constructor
    · rintro ⟨hzA,hzB⟩
      exact e.sharedOnlyV z hzA hzB
    · intro he
      subst z
      exact ⟨e.vInA,e.vInB⟩
  obtain ⟨hjb,hjnb,hpB⟩ := Select.selected_outside_second C hC.1 aW (bW-n) j p hb hbor
    hborAnc v u huv hinter huA hpv hju
  refine ⟨j,p,u,hjg,hjor,hp,hin,hpv,huv,hpu,huA,?_,hjv,hju,hjb,hjnb,?_⟩
  · exact e.adjacentA u (by rwa [← hA])
  · simpa only [hbeq] using hpB

end PEqualNP.Outside.L_meta_3754.Glue

namespace PEqualNP.Outside.L_meta_3754.PatchSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- This relation describes the three aliases before contraction changes any wire indices.
def AliasSem (n : ℕ) (C P : Circuit) (j p B g : ℕ) (v : Fin n) : Prop :=
  ∀ (x : Fin n → Bool) k, k<C.gates.length →
    wireVal n P (n+k) x =
      if k=g ∨ k=B then x v else if k=j then wireVal n P p x else
        (gateAt C k).op.eval ((gateAt C k).inputs.map fun w => wireVal n P w x)

lemma aliases_le {n : ℕ} (C P : Circuit) (hC : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n) (hp : p<n+j)
    (hsem : AliasSem n C P j p B g v)
    (hjBelow : ∀ x, wireVal n C p x=true → gateVal n C j x=true)
    (hBBelow : ∀ x, x v=true → gateVal n C B x=true)
    (hgBelow : ∀ x, x v=true → gateVal n C g x=true) :
    ∀ (x : Fin n → Bool) w, w<n+C.gates.length → wireVal n P w x=true → wireVal n C w x=true := by
  intro x w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hnow
    by_cases hraw : w<n
    · simpa only [Ledger.wireVal_input n P x w hraw,Ledger.wireVal_input n C x w hraw] using hnow
    obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by omega
    rw [hsem x k hk] at hnow
    by_cases hkg : k=g ∨ k=B
    · rw [if_pos hkg] at hnow
      rcases hkg with rfl | rfl
      · exact hgBelow x hnow
      · exact hBBelow x hnow
    rw [if_neg hkg] at hnow
    by_cases hkj : k=j
    · subst k
      rw [if_pos rfl] at hnow
      exact hjBelow x (ih p hp (by omega) hnow)
    rw [if_neg hkj] at hnow
    rw [Ledger.wireVal_gate n C x k hk hC.2.1]
    have hm : gateAt C k∈C.gates := by
      rw [Ledger.gateAt_eq_getElem C k hk]
      exact List.getElem_mem hk
    apply Ledger.gate_eval_monotone (gateAt C k) (hC.1 _ hm) _ _ ?_ hnow
    intro u hu
    exact ih u (hC.2.1 k hk u hu) (by have := hC.2.1 k hk u hu;omega)

lemma aliases_agree_except_private {n : ℕ} (C P : Circuit) (hC : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n) (hp : p<n+j) (hpB : p≠n+B)
    (hsem : AliasSem n C P j p B g v)
    (hprivate : ∀ k<C.gates.length,n+B∈(gateAt C k).inputs → k=g)
    (x : Fin n → Bool) (hxv : x v=false)
    (hjEq : gateVal n C j x=wireVal n C p x) (hgZero : gateVal n C g x=false) :
    ∀ w,w<n+C.gates.length → w≠n+B → wireVal n P w x=wireVal n C w x := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwB
    by_cases hraw : w<n
    · rw [Ledger.wireVal_input n P x w hraw,Ledger.wireVal_input n C x w hraw]
    obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by omega
    have hkB : k≠B := by omega
    rw [hsem x k hk]
    by_cases hkg : k=g
    · subst k
      rw [if_pos (Or.inl rfl),hxv]
      exact hgZero.symm
    rw [if_neg (by simp [hkg,hkB])]
    by_cases hkj : k=j
    · subst k
      rw [if_pos rfl,ih p hp (by omega) hpB]
      exact hjEq.symm
    rw [if_neg hkj,Ledger.wireVal_gate n C x k hk hC.2.1]
    congr 1
    apply List.map_congr_left
    intro u hu
    exact ih u (hC.2.1 k hk u hu) (by have := hC.2.1 k hk u hu;omega)
      (fun h => hkg (hprivate k hk (h ▸ hu)))

lemma aliases_agree_before_g {n : ℕ} (C P : Circuit) (hC : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n) (hg : g<C.gates.length) (hp : p<n+j) (hpB : p≠n+B)
    (hsem : AliasSem n C P j p B g v)
    (hprivate : ∀ k<C.gates.length,n+B∈(gateAt C k).inputs → k=g)
    (x : Fin n → Bool) (hxv : x v=false)
    (hjEq : gateVal n C j x=wireVal n C p x) :
    ∀ w,w<n+g → w≠n+B → wireVal n P w x=wireVal n C w x := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwB
    by_cases hraw : w<n
    · rw [Ledger.wireVal_input n P x w hraw,Ledger.wireVal_input n C x w hraw]
    obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by omega
    have hkB : k≠B := by omega
    have hkg : k≠g := by omega
    rw [hsem x k hk,if_neg (by simp [hkg,hkB])]
    by_cases hkj : k=j
    · subst k
      rw [if_pos rfl,ih p hp (by omega) hpB]
      exact hjEq.symm
    rw [if_neg hkj,Ledger.wireVal_gate n C x k hk hC.2.1]
    congr 1
    apply List.map_congr_left
    intro u hu
    exact ih u (hC.2.1 k hk u hu) (by have := hC.2.1 k hk u hu;omega)
      (fun h => hkg (hprivate k hk (h ▸ hu)))

end PEqualNP.Outside.L_meta_3754.PatchSemantics


namespace PEqualNP.Outside.L_meta_3754.Loss

lemma and_false {a b : Bool} (h : (a && b) = false) : a = false ∨ b = false := by
  cases a <;> cases b <;> simp_all

lemma or_false {a b : Bool} (h : (a || b) = false) : a = false ∧ b = false := by
  cases a <;> cases b <;> simp_all

lemma loss_propagates_label
    (n N j B g : ℕ) (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (old now : ℕ → Bool) (label : ℕ → Prop)
    (hback : ∀ k < N, a k < n+k ∧ b k < n+k)
    (hraw : ∀ w < n, old w = now w)
    (hstart : label (n+j))
    (hB : now (n+B) = true) (hg : now (n+g) = true)
    (hgate : ∀ k < N, k ≠ j → k ≠ B → k ≠ g →
      old (n+k) = (if isAnd k then old (a k) && old (b k) else old (a k) || old (b k)) ∧
      now (n+k) = (if isAnd k then now (a k) && now (b k) else now (a k) || now (b k)))
    (hor : ∀ k < N, isAnd k = false → label (a k) ∨ label (b k) → label (n+k))
    (hand : ∀ k < N, k ≠ j → k ≠ B → k ≠ g → isAnd k = true →
      (label (a k) → old (b k) = false) ∧ (label (b k) → old (a k) = false)) :
    ∀ w < n+N, old w = true → now w = false → label w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw ho hn
    by_cases hwi : w < n
    · have h := hraw w hwi
      rw [ho,hn] at h
      cases h
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    have hk : k < N := by omega
    by_cases hkj : k = j
    · simpa [hkj] using hstart
    by_cases hkB : k = B
    · subst k; rw [hB] at hn; cases hn
    by_cases hkg : k = g
    · subst k; rw [hg] at hn; cases hn
    obtain ⟨ha,hb⟩ := hback k hk
    obtain ⟨hgo,hgn⟩ := hgate k hk hkj hkB hkg
    cases hop : isAnd k
    · rw [hgo,hop] at ho
      rw [hgn,hop] at hn
      have hv : old (a k) = true ∨ old (b k) = true := by simpa using ho
      have hn' : now (a k) = false ∧ now (b k) = false := or_false (by simpa using hn)
      apply hor k hk hop
      rcases hv with hv | hv
      · exact Or.inl (ih (a k) ha (by omega) hv hn'.1)
      · exact Or.inr (ih (b k) hb (by omega) hv hn'.2)
    · rw [hgo,hop] at ho
      rw [hgn,hop] at hn
      have hv : old (a k) = true ∧ old (b k) = true := by simpa using ho
      have hn' : now (a k) = false ∨ now (b k) = false := and_false (by simpa using hn)
      obtain ⟨hga,hgb⟩ := hand k hk hkj hkB hkg hop
      exfalso
      rcases hn' with hn' | hn'
      · have h := hga (ih (a k) ha (by omega) hv.1 hn')
        rw [hv.2] at h
        cases h
      · have h := hgb (ih (b k) hb (by omega) hv.2 hn')
        rw [hv.1] at h
        cases h

lemma loss_from_three_labels
    (n N j B g : ℕ) (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (old now : ℕ → Bool) (label : ℕ → Prop)
    (hback : ∀ k < N, a k < n+k ∧ b k < n+k)
    (hraw : ∀ w < n, old w = now w)
    (hstart : label (n+j))
    (hB : label (n+B)) (hg : label (n+g))
    (hgate : ∀ k < N, k ≠ j → k ≠ B → k ≠ g →
      old (n+k) = (if isAnd k then old (a k) && old (b k) else old (a k) || old (b k)) ∧
      now (n+k) = (if isAnd k then now (a k) && now (b k) else now (a k) || now (b k)))
    (hor : ∀ k < N, isAnd k = false → label (a k) ∨ label (b k) → label (n+k))
    (hand : ∀ k < N, k ≠ j → k ≠ B → k ≠ g → isAnd k = true →
      (label (a k) → old (b k) = false) ∧ (label (b k) → old (a k) = false)) :
    ∀ w < n+N, old w = true → now w = false → label w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw ho hn
    by_cases hwi : w < n
    · have h := hraw w hwi
      rw [ho,hn] at h
      cases h
    obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
    have hk : k < N := by omega
    by_cases hkj : k = j
    · simpa [hkj] using hstart
    by_cases hkB : k = B
    · simpa [hkB] using hB
    by_cases hkg : k = g
    · simpa [hkg] using hg
    obtain ⟨ha,hb⟩ := hback k hk
    obtain ⟨hgo,hgn⟩ := hgate k hk hkj hkB hkg
    cases hop : isAnd k
    · rw [hgo,hop] at ho
      rw [hgn,hop] at hn
      have hv : old (a k) = true ∨ old (b k) = true := by simpa using ho
      have hn' : now (a k) = false ∧ now (b k) = false := or_false (by simpa using hn)
      apply hor k hk hop
      rcases hv with hv | hv
      · exact Or.inl (ih (a k) ha (by omega) hv hn'.1)
      · exact Or.inr (ih (b k) hb (by omega) hv hn'.2)
    · rw [hgo,hop] at ho
      rw [hgn,hop] at hn
      have hv : old (a k) = true ∧ old (b k) = true := by simpa using ho
      have hn' : now (a k) = false ∨ now (b k) = false := and_false (by simpa using hn)
      obtain ⟨hga,hgb⟩ := hand k hk hkj hkB hkg hop
      exfalso
      rcases hn' with hn' | hn'
      · have h := hga (ih (a k) ha (by omega) hv.1 hn')
        rw [hv.2] at h
        cases h
      · have h := hgb (ih (b k) hb (by omega) hv.2 hn')
        rw [hv.1] at h
        cases h

end PEqualNP.Outside.L_meta_3754.Loss

namespace PEqualNP.Outside.L_meta_3754.PatchSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

open Classical in
lemma gate_bin {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k<C.gates.length)
    (f : ℕ → Bool) :
    (gateAt C k).op.eval ((gateAt C k).inputs.map f) =
      if decide ((gateAt C k).op=GateOp.and) then f (opnd C k 0) && f (opnd C k 1)
      else f (opnd C k 0) || f (opnd C k 1) := by
  obtain ⟨a,b,hab⟩ := Ledger.gate_two n C hC k hk
  have hm : gateAt C k∈C.gates := by
    rw [Ledger.gateAt_eq_getElem C k hk]
    exact List.getElem_mem hk
  rcases hC.1 _ hm with hop | hop <;> simp [hab,hop,opnd,GateOp.eval]

lemma alias_middle_preserved {n : ℕ} (C P : Circuit) (hC : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n) (hB : B<C.gates.length) (hg : g<C.gates.length)
    (hout : C.output<n+C.gates.length)
    (hsem : AliasSem n C P j p B g v)
    (label : ℕ → Prop) (hstart : label (n+j)) (houtLabel : ¬label C.output)
    (hlabelOR : ∀ k<C.gates.length,(gateAt C k).op=GateOp.or →
      label (opnd C k 0) ∨ label (opnd C k 1) → label (n+k))
    (x : Fin n → Bool) (hxv : x v=true)
    (hguard : ∀ k<C.gates.length,k≠j → k≠B → k≠g → (gateAt C k).op=GateOp.and →
      (label (opnd C k 0) → wireVal n C (opnd C k 1) x=false) ∧
      (label (opnd C k 1) → wireVal n C (opnd C k 0) x=false)) :
    wireVal n C C.output x=true → wireVal n P C.output x=true := by
  classical
  intro hold
  cases hnow : wireVal n P C.output x
  · apply False.elim
    apply houtLabel
    apply Loss.loss_propagates_label n C.gates.length j B g (fun k=>opnd C k 0)
      (fun k=>opnd C k 1) (fun k=>decide ((gateAt C k).op=GateOp.and))
      (fun w=>wireVal n C w x) (fun w=>wireVal n P w x) label ?_ ?_ hstart ?_ ?_ ?_ ?_ ?_
      C.output hout hold hnow
    · intro k hk
      exact ⟨Ledger.operand_bound n C hC k hk 0,Ledger.operand_bound n C hC k hk 1⟩
    · intro w hw
      rw [Ledger.wireVal_input n C x w hw,Ledger.wireVal_input n P x w hw]
    · rw [hsem x B hB,if_pos (Or.inr rfl),hxv]
    · rw [hsem x g hg,if_pos (Or.inl rfl),hxv]
    · intro k hk hkj hkB hkg
      constructor
      · rw [Ledger.wireVal_gate n C x k hk hC.2.1]
        exact gate_bin C hC k hk _
      · rw [hsem x k hk,if_neg (by simp [hkg,hkB]),if_neg hkj]
        exact gate_bin C hC k hk _
    · intro k hk hnotand hlab
      have hm : gateAt C k∈C.gates := by
        rw [Ledger.gateAt_eq_getElem C k hk]
        exact List.getElem_mem hk
      rcases hC.1 _ hm with hand | hor
      · simp [hand] at hnotand
      · exact hlabelOR k hk hor hlab
    · intro k hk hkj hkB hkg hand
      exact hguard k hk hkj hkB hkg (of_decide_eq_true hand)
  · rfl

lemma alias_guarded_preserved {n : ℕ} (C P : Circuit) (hC : IsAO2 n C)
    (j p B g : ℕ) (v : Fin n) (hB : B<C.gates.length) (hg : g<C.gates.length)
    (hout : C.output<n+C.gates.length)
    (hsem : AliasSem n C P j p B g v)
    (label : ℕ → Prop) (hstart : label (n+j)) (houtLabel : ¬label C.output)
    (hlabelOR : ∀ k<C.gates.length,(gateAt C k).op=GateOp.or →
      label (opnd C k 0) ∨ label (opnd C k 1) → label (n+k))
    (hBLabel : label (n+B)) (hgLabel : label (n+g)) (x : Fin n → Bool)
    (hguard : ∀ k<C.gates.length,k≠j → k≠B → k≠g → (gateAt C k).op=GateOp.and →
      (label (opnd C k 0) → wireVal n C (opnd C k 1) x=false) ∧
      (label (opnd C k 1) → wireVal n C (opnd C k 0) x=false)) :
    wireVal n C C.output x=true → wireVal n P C.output x=true := by
  classical
  intro hold
  cases hnow : wireVal n P C.output x
  · apply False.elim
    apply houtLabel
    apply Loss.loss_from_three_labels n C.gates.length j B g (fun k=>opnd C k 0)
      (fun k=>opnd C k 1) (fun k=>decide ((gateAt C k).op=GateOp.and))
      (fun w=>wireVal n C w x) (fun w=>wireVal n P w x) label ?_ ?_ hstart hBLabel hgLabel ?_ ?_ ?_
      C.output hout hold hnow
    · intro k hk
      exact ⟨Ledger.operand_bound n C hC k hk 0,Ledger.operand_bound n C hC k hk 1⟩
    · intro w hw
      rw [Ledger.wireVal_input n C x w hw,Ledger.wireVal_input n P x w hw]
    · intro k hk hkj hkB hkg
      constructor
      · rw [Ledger.wireVal_gate n C x k hk hC.2.1]
        exact gate_bin C hC k hk _
      · rw [hsem x k hk,if_neg (by simp [hkg,hkB]),if_neg hkj]
        exact gate_bin C hC k hk _
    · intro k hk hnotand hlab
      have hm : gateAt C k∈C.gates := by
        rw [Ledger.gateAt_eq_getElem C k hk]
        exact List.getElem_mem hk
      rcases hC.1 _ hm with hand | hor
      · simp [hand] at hnotand
      · exact hlabelOR k hk hor hlab
    · intro k hk hkj hkB hkg hand
      exact hguard k hk hkj hkB hkg (of_decide_eq_true hand)
  · rfl

end PEqualNP.Outside.L_meta_3754.PatchSemantics

namespace PEqualNP.Outside.L_meta_3754.PatchSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def Probe (n : ℕ) (C : Circuit) (v : Fin n) (w : ℕ) : Prop :=
  wireVal n C w (Ledger.singletonInput v)=true

lemma probe_member {n : ℕ} {C : Circuit} {v : Fin n} {w : ℕ} (h : Probe n C v w) :
    v∈Ledger.singletonSupport n C w := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩

lemma probe_or_closed {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (v : Fin n)
    (k : ℕ) (hk : k<C.gates.length) (hop : (gateAt C k).op=GateOp.or) :
    Probe n C v (opnd C k 0) ∨ Probe n C v (opnd C k 1) → Probe n C v (n+k) := by
  intro h
  obtain ⟨a,b,hab⟩ := Ledger.gate_two n C hC k hk
  rcases h with h | h
  · exact Ledger.wire_or_true n C hC k hk hop (opnd C k 0) (by simp [opnd,hab]) _ h
  · exact Ledger.wire_or_true n C hC k hk hop (opnd C k 1) (by simp [opnd,hab]) _ h

lemma output_not_probe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hcomp : circuitFun n C=graphFun G ∅) (v : Fin n) :
    ¬Probe n C v C.output := by
  intro h
  change circuitFun n C (Ledger.singletonInput v)=true at h
  rw [hcomp] at h
  simpa [graphFun,Ledger.singletonInput] using h

lemma unique_middle_case {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcycle : NoFourCycle G) (C P : Circuit) (hC : IsAO2 n C)
    (hcomp : circuitFun n C=graphFun G ∅) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j p B g : ℕ) (v u m : Fin n) (hB : B<C.gates.length) (hg : g<C.gates.length)
    (hout : C.output<n+C.gates.length) (hsem : AliasSem n C P j p B g v)
    (hcone : ∀k<C.gates.length,PEqualNP.Core.InOutputCone n C k)
    (hclean : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → k≠g → BelowF G C k)
    (hnoimp : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → ∀b : Fin 2,
      ¬∀x : Fin n → Bool,wireVal n C (opnd C k b) x=true → graphFun G ∅ x=true)
    (hjv : Probe n C v (n+j)) (hju : Probe n C u (n+j))
    (hgv : gateVal n C g (Ledger.singletonInput v)=true)
    (huv : u≠v) (hum : G.Adj u m) (hvm : G.Adj v m)
    (x : Fin n → Bool) (hxv : x v=true) (hxm : x m=false) :
    graphFun G ∅ x=true → wireVal n P C.output x=true := by
  have hunique : ∀i<C.gates.length,(gateAt C i).op=GateOp.and → ¬BelowF G C i → i=g := by
    intro i hi hop hn
    by_contra hne
    exact hn (hclean i hi hop hne)
  intro hF
  apply alias_middle_preserved C P hC j p B g v hB hg hout hsem
    (fun w=>Probe n C u w ∧ Probe n C v w) ⟨hju,hjv⟩
    (fun h=>(output_not_probe G C hcomp v) h.2) ?_ x hxv ?_ ?_
  · intro k hk hop hlab
    rcases hlab with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · exact ⟨probe_or_closed C hC u k hk hop (Or.inl hu),probe_or_closed C hC v k hk hop (Or.inl hv)⟩
    · exact ⟨probe_or_closed C hC u k hk hop (Or.inr hu),probe_or_closed C hC v k hk hop (Or.inr hv)⟩
  · intro k hk _ _ hkg hand
    have hb := hclean k hk hand hkg
    constructor
    · rintro ⟨hu,hv⟩
      have hpure := Ledger.unique_dirty_opposite_exact_or G C hC hfixed g k (hcone k hk)
        hand hb hunique (hnoimp k hk hand) v hgv (probe_member hv)
      rw [Ledger.and_center_exact G hcycle C hC k hk hand hb u v m
        (probe_member hu) (probe_member hv) huv hum hvm hpure x,hxm]
    · rintro ⟨hu,hv⟩
      have hpure := Ledger.unique_dirty_opposite_exact_or_right G C hC hfixed g k (hcone k hk)
        hand hb hunique (hnoimp k hk hand) v hgv (probe_member hv)
      rw [Ledger.and_center_exact_right G hcycle C hC k hk hand hb u v m
        (probe_member hu) (probe_member hv) huv hum hvm hpure x,hxm]
  · change circuitFun n C x=true
    rwa [hcomp]

lemma unique_low_oriented {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcycle : NoFourCycle G) (s : Fin n → Bool) (hcolor : ∀a b,G.Adj a b → s a≠s b)
    (C P : Circuit) (hC : IsAO2 n C) (hcomp : circuitFun n C=graphFun G ∅)
    (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (j p B g : ℕ) (v m a b : Fin n) (hB : B<C.gates.length) (hg : g<C.gates.length)
    (hout : C.output<n+C.gates.length) (hsem : AliasSem n C P j p B g v)
    (hcone : ∀k<C.gates.length,PEqualNP.Core.InOutputCone n C k)
    (hclean : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → k≠g → BelowF G C k)
    (hnoimp : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → ∀i : Fin 2,
      ¬∀x : Fin n → Bool,wireVal n C (opnd C k i) x=true → graphFun G ∅ x=true)
    (hjv : Probe n C v (n+j)) (hBv : Probe n C v (n+B)) (hgv : Probe n C v (n+g))
    (hvm : G.Adj v m) (ham : G.Adj a m) (hab : G.Adj a b) (hav : a≠v) (hbm : b≠m) :
    wireVal n P C.output (pairInput a b)=true := by
  have hunique : ∀i<C.gates.length,(gateAt C i).op=GateOp.and → ¬BelowF G C i → i=g := by
    intro i hi hop hn
    by_contra hne
    exact hn (hclean i hi hop hne)
  apply alias_guarded_preserved C P hC j p B g v hB hg hout hsem (Probe n C v) hjv
    (output_not_probe G C hcomp v) (probe_or_closed C hC v) hBv hgv (pairInput a b) ?_ ?_
  · intro k hk _ _ hkg hand
    have hb := hclean k hk hand hkg
    constructor
    · intro hv
      have hpure := Ledger.unique_dirty_opposite_exact_or G C hC hfixed g k (hcone k hk)
        hand hb hunique (hnoimp k hk hand) v hgv (probe_member hv)
      exact Ledger.labeled_opposite_false_on_edge G hcycle s hcolor C hC k hk hand hb
        v m a b (probe_member hv) hvm ham hab hav hbm hpure
    · intro hv
      have hpure := Ledger.unique_dirty_opposite_exact_or_right G C hC hfixed g k (hcone k hk)
        hand hb hunique (hnoimp k hk hand) v hgv (probe_member hv)
      exact Ledger.labeled_opposite_false_on_edge_right G hcycle s hcolor C hC k hk hand hb
        v m a b (probe_member hv) hvm ham hab hav hbm hpure
  · change circuitFun n C (pairInput a b)=true
    rw [hcomp]
    have hh : ∃u w,G.Adj u w ∧ pairInput a b u=true ∧ pairInput a b w=true :=
      ⟨a,b,hab,by simp [pairInput],by simp [pairInput]⟩
    simpa [graphFun] using hh

end PEqualNP.Outside.L_meta_3754.PatchSemantics

namespace PEqualNP.Outside.L_meta_3754.PatchSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma graph_from_edge_values {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y,(∀ i,x i=true → y i=true) → f x=true → f y=true)
    (hsafe : ∀ x,f x=true → graphFun G ∅ x=true)
    (hedge : ∀ a b,G.Adj a b → f (pairInput a b)=true) : f=graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hsafe x
  · intro hx
    simp [graphFun] at hx
    obtain ⟨a,b,hab,ha,hb⟩ := hx
    apply hmono (pairInput a b) x ?_ (hedge a b hab)
    intro i hi
    simp only [pairInput,decide_eq_true_eq] at hi
    rcases hi with rfl | rfl <;> assumption

lemma three_alias_restoration {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C P : Circuit) (hC : IsAO2 n C) (hP : IsAO2 n P)
    (hcomp : circuitFun n C=graphFun G ∅) (hlen : P.gates.length=C.gates.length)
    (j p B g aW : ℕ) (v m : Fin n) (hg : g<C.gates.length)
    (hp : p<n+j) (hpB : p≠n+B) (haW : aW<n+g) (haWB : aW≠n+B)
    (hout : C.output<n+C.gates.length) (houtB : C.output≠n+B)
    (hsem : AliasSem n C P j p B g v)
    (hprivate : ∀ k<C.gates.length,n+B∈(gateAt C k).inputs → k=g)
    (hjval : ∀ x,gateVal n C j x=(x v || wireVal n C p x))
    (hgv : ∀ x,x v=true → gateVal n C g x=true)
    (hBv : ∀ x,x v=true → gateVal n C B x=true)
    (hgA : ∀ x,gateVal n C g x=true → wireVal n C aW x=true)
    (hsafeA : ∀ x,x m=true → wireVal n C aW x=true → graphFun G ∅ x=true)
    (hlow : ∀ a b,G.Adj a b → pairInput a b v=false → pairInput a b m=false →
      gateVal n C g (pairInput a b)=true → wireVal n P C.output (pairInput a b)=true)
    (hmiddle : ∀ a b,G.Adj a b → pairInput a b v=true → pairInput a b m=false →
      wireVal n P C.output (pairInput a b)=true)
    (hpair : wireVal n P C.output (pairInput v m)=true) :
    ∀ x,(wireVal n P C.output x || (x m && wireVal n P aW x))=graphFun G ∅ x := by
  have haFull : aW<n+C.gates.length := by omega
  have hjBelow : ∀ x,wireVal n C p x=true → gateVal n C j x=true := by
    intro x hx
    rw [hjval x,hx]
    simp
  have hdecrease := aliases_le C P hC j p B g v hp hsem hjBelow hBv hgv
  have hkeepA (x : Fin n → Bool) (hv : x v=false) : wireVal n P aW x=wireVal n C aW x := by
    apply aliases_agree_before_g C P hC j p B g v hg hp hpB hsem hprivate x hv ?_ aW haW haWB
    rw [hjval x,hv]
    simp
  have hmono (w : ℕ) (hw : w<n+C.gates.length) :=
    fun x y hxy => Ledger.wire_monotone n P hP x y hxy w (by simpa [hlen] using hw)
  let Fnew := fun x : Fin n → Bool => wireVal n P C.output x || (x m && wireVal n P aW x)
  have hF : Fnew=graphFun G ∅ := by
    apply graph_from_edge_values G Fnew
    · intro x y hxy hx
      change (wireVal n P C.output x || (x m && wireVal n P aW x))=true at hx
      change (wireVal n P C.output y || (y m && wireVal n P aW y))=true
      simp only [Bool.or_eq_true,Bool.and_eq_true] at hx ⊢
      exact hx.elim (fun h=>Or.inl (hmono C.output hout x y hxy h))
        (fun h=>Or.inr ⟨hxy m h.1,hmono aW haFull x y hxy h.2⟩)
    · intro x hx
      change (wireVal n P C.output x || (x m && wireVal n P aW x))=true at hx
      simp only [Bool.or_eq_true,Bool.and_eq_true] at hx
      rcases hx with hx | ⟨hm,ha⟩
      · have hc := hdecrease x C.output hout hx
        change circuitFun n C x=true at hc
        rwa [hcomp] at hc
      · exact hsafeA x hm (hdecrease x aW haFull ha)
    · intro a b hab
      change (wireVal n P C.output (pairInput a b) ||
        (pairInput a b m && wireVal n P aW (pairInput a b)))=true
      simp only [Bool.or_eq_true,Bool.and_eq_true]
      cases hv : pairInput a b v
      · cases hgd : gateVal n C g (pairInput a b)
        · left
          have he := aliases_agree_except_private C P hC j p B g v hp hpB hsem hprivate
            (pairInput a b) hv (by rw [hjval,hv];simp) hgd C.output hout houtB
          rw [he]
          change circuitFun n C (pairInput a b)=true
          rw [hcomp]
          have he : ∃ u w,G.Adj u w ∧ pairInput a b u=true ∧ pairInput a b w=true :=
            ⟨a,b,hab,by simp [pairInput],by simp [pairInput]⟩
          simpa [graphFun] using he
        · cases hm : pairInput a b m
          · exact Or.inl (hlow a b hab hv hm hgd)
          · exact Or.inr ⟨rfl,by rw [hkeepA _ hv];exact hgA _ hgd⟩
      · cases hm : pairInput a b m
        · exact Or.inl (hmiddle a b hab hv hm)
        · left
          apply hmono C.output hout (pairInput v m) (pairInput a b) ?_ hpair
          intro i hi
          simp only [pairInput,decide_eq_true_eq] at hi
          rcases hi with rfl | rfl <;> assumption
  exact fun x=>congrFun hF x

end PEqualNP.Outside.L_meta_3754.PatchSemantics

namespace PEqualNP.Outside.L_meta_3754.PatchSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma exceptional_restoration {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcycle : NoFourCycle G) (s : Fin n → Bool) (hcolor : ∀a b,G.Adj a b → s a≠s b)
    (C P : Circuit) (hC : IsAO2 n C) (hP : IsAO2 n P)
    (hcomp : circuitFun n C=graphFun G ∅) (hlen : P.gates.length=C.gates.length)
    (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (g aW bW : ℕ) (v m : Fin n) (hg : g<C.gates.length)
    (E : Strict3653.Exceptional G C s g aW bW v m)
    (hcone : ∀k<C.gates.length,PEqualNP.Core.InOutputCone n C k)
    (hclean : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → k≠g → BelowF G C k)
    (hnoimp : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → ∀i : Fin 2,
      ¬∀x : Fin n → Bool,wireVal n C (opnd C k i) x=true → graphFun G ∅ x=true)
    (j p : ℕ) (u : Fin n) (hjg : j<g) (hjOR : (gateAt C j).op=GateOp.or)
    (hp : p<n+j) (hjin : (gateAt C j).inputs=[v.val,p] ∨ (gateAt C j).inputs=[p,v.val])
    (huv : u≠v) (huA : u∈Ledger.singletonSupport n C aW)
    (hjv : Probe n C v (n+j)) (hju : Probe n C u (n+j))
    (hout : C.output<n+C.gates.length)
    (hsem : AliasSem n C P j p (bW-n) g v)
    (hpair : wireVal n P C.output (pairInput v m)=true) :
    ∀x,(wireVal n P C.output x || (x m && wireVal n P aW x))=graphFun G ∅ x := by
  have hBwire : n+(bW-n)=bW := by have := E.bGate;omega
  have hBlt : bW-n<C.gates.length := by have := E.bBound;have := E.bGate;omega
  have hjlt : j<C.gates.length := hjg.trans hg
  have hprivate : ∀k<C.gates.length,n+(bW-n)∈(gateAt C k).inputs → k=g := by
    intro k hk hmem
    by_contra hne
    rw [hBwire] at hmem
    exact E.privateB k hk hne hmem
  have hpB : p≠n+(bW-n) := by
    intro he
    have hm : p∈(gateAt C j).inputs := by rcases hjin with h | h <;> simp [h]
    have hje := hprivate j hjlt (he ▸ hm)
    omega
  have haWB : aW≠n+(bW-n) := by rw [hBwire];exact E.distinct
  have hgv (x : Fin n → Bool) (hv : x v=true) : gateVal n C g x=true := by
    rw [E.gateProduct]
    have ha := (E.pureA x).mpr ⟨v,E.vInA,hv⟩
    have hb := (E.pureB x).mpr ⟨v,E.vInB,hv⟩
    simp [ha,hb]
  have hBv (x : Fin n → Bool) (hv : x v=true) : gateVal n C (bW-n) x=true := by
    change wireVal n C (n+(bW-n)) x=true
    rw [hBwire]
    exact (E.pureB x).mpr ⟨v,E.vInB,hv⟩
  have hgvProbe : Probe n C v (n+g) := hgv _ (by simp [Ledger.singletonInput])
  have hBvProbe : Probe n C v (n+(bW-n)) := hBv _ (by simp [Ledger.singletonInput])
  have houtB : C.output≠n+(bW-n) := by
    intro he
    apply output_not_probe G C hcomp v
    simpa only [he] using hBvProbe
  have hjval (x : Fin n → Bool) : gateVal n C j x=(x v || wireVal n C p x) := by
    change wireVal n C (n+j) x= _
    rw [Ledger.wireVal_gate n C x j hjlt hC.2.1,hjOR]
    rcases hjin with hin | hin <;>
      simp [hin,GateOp.eval,Ledger.wireVal_input n C x v.val v.isLt,Bool.or_comm]
  have hum : G.Adj u m := by
    have hu := (Finset.mem_filter.mp huA).2
    obtain ⟨z,hz,hzu⟩ := (E.pureA (Ledger.singletonInput u)).mp hu
    have hzu' : z=u := by simpa [Ledger.singletonInput] using hzu
    exact hzu' ▸ E.adjacentA z hz
  have hvm : G.Adj v m := E.adjacentA v E.vInA
  apply three_alias_restoration G C P hC hP hcomp hlen j p (bW-n) g aW v m hg hp hpB
    E.aBound haWB hout houtB hsem hprivate hjval hgv hBv ?_ ?_ ?_ ?_ hpair
  · intro x hx
    rw [E.gateProduct] at hx
    exact (Bool.and_eq_true_iff.mp hx).1
  · intro x hm ha
    obtain ⟨z,hz,hzx⟩ := (E.pureA x).mp ha
    have hh : ∃a b,G.Adj a b ∧ x a=true ∧ x b=true := ⟨z,m,E.adjacentA z hz,hzx,hm⟩
    simpa [graphFun] using hh
  · intro a b hab hv hm hgd
    rw [E.gateProduct] at hgd
    have hvAB : PEqualNP.ReadTwo.wval C (pairInput a b) aW=true ∧
        PEqualNP.ReadTwo.wval C (pairInput a b) bW=true := by simpa only [Bool.and_eq_true] using hgd
    obtain ⟨a',ha',hax⟩ := (E.pureA _).mp hvAB.1
    obtain ⟨b',hb',hbx⟩ := (E.pureB _).mp hvAB.2
    have hab' : a'≠b' := by
      intro he
      have hav := E.sharedOnlyV a' ha' (he.symm ▸ hb')
      rw [hav,hv] at hax
      cases hax
    have haEq : a'=a ∨ a'=b := by simpa only [pairInput,decide_eq_true_eq] using hax
    have hbEq : b'=a ∨ b'=b := by simpa only [pairInput,decide_eq_true_eq] using hbx
    have he : pairInput a' b'=pairInput a b ∧ G.Adj a' b' := by
      rcases haEq with rfl | rfl <;> rcases hbEq with rfl | rfl
      · exact (hab' rfl).elim
      · exact ⟨rfl,hab⟩
      · exact ⟨by funext i;simp [pairInput,or_comm],hab.symm⟩
      · exact (hab' rfl).elim
    have hav : a'≠v := by intro he;rw [he,hv] at hax;cases hax
    have hbm : b'≠m := by intro he;rw [he,hm] at hbx;cases hbx
    have hh := unique_low_oriented G hcycle s hcolor C P hC hcomp hfixed j p (bW-n) g
      v m a' b' hBlt hg hout hsem hcone hclean hnoimp hjv hBvProbe hgvProbe
      hvm (E.adjacentA a' ha') he.2 hav hbm
    simpa only [he.1] using hh
  · intro a b hab hv hm
    apply unique_middle_case G hcycle C P hC hcomp hfixed j p (bW-n) g v u m hBlt hg
      hout hsem hcone hclean hnoimp hjv hju hgvProbe huv hum hvm (pairInput a b) hv hm
    have hh : ∃u w,G.Adj u w ∧ pairInput a b u=true ∧ pairInput a b w=true :=
      ⟨a,b,hab,by simp [pairInput],by simp [pairInput]⟩
    simpa [graphFun] using hh

end PEqualNP.Outside.L_meta_3754.PatchSemantics

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

namespace PEqualNP.Outside.L_meta_3754.ExceptionalPair
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core

lemma exceptional_alias_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C P : Circuit) (s : Fin n → Bool) (hC : IsLeastAO G C) (hfixed : IsLiftFixedPoint G C)
    (g aW bW : ℕ) (v m : Fin n) (E : Strict3653.Exceptional G C s g aW bW v m)
    (j p : ℕ) (hjg : j<g)
    (hsem : PairPreserve.AliasSem n C P j p (bW-n) g v)
    (hout : C.output<n+C.gates.length)
    (hcones : ∀k<C.gates.length,InOutputCone n C k)
    (hunique : ∀i<C.gates.length,(gateAt C i).op=GateOp.and → i≠g → BelowF G C i)
    (hjv : gateVal n C j (Ledger.singletonInput v)=true) :
    wireVal n P C.output (pairInput v m)=true := by
  have hBg : bW-n<g := by have hb:=E.bBound;have hn:=E.bGate;omega
  have hbEq : n+(bW-n)=bW := by have hn:=E.bGate;omega
  have hBv : gateVal n C (bW-n) (Ledger.singletonInput v)=true := by
    have hb := (E.pureB (Ledger.singletonInput v)).mpr ⟨v,E.vInB,by simp [Ledger.singletonInput]⟩
    simpa only [gateVal,PEqualNP.ReadTwo.wval,hbEq] using hb
  have hgv : gateVal n C g (Ledger.singletonInput v)=true := by
    rw [E.gateProduct]
    have ha := (E.pureA (Ledger.singletonInput v)).mpr ⟨v,E.vInA,by simp [Ledger.singletonInput]⟩
    have hb := (E.pureB (Ledger.singletonInput v)).mpr ⟨v,E.vInB,by simp [Ledger.singletonInput]⟩
    rw [ha,hb]
    rfl
  have huniq : ∀i<C.gates.length,(gateAt C i).op=GateOp.and → ¬BelowF G C i → i=g := by
    intro i hi hand hd
    by_contra hne
    exact hd (hunique i hi hand hne)
  obtain ⟨top,htop,hand,htg,hreader⟩ := E.mReader
  have hother : ∀b : Fin 2,m∈Strict3653.varSet n C g (opnd C top b) →
      wireVal n C (opnd C top b) (pairInput v m)=true := by
    intro b hm
    have hw := Ledger.operand_bound n C hC.1 top htop b
    have hd : ¬Strict3653.WireBelowF G C (opnd C top b) := by
      exact Bypass.least_no_and_below_operand hC htop hand
        (Strict3653.opnd_mem hC.1 htop b)
    have hh := (E.dirtyWireFormula (opnd C top b) (hw.trans (Nat.add_lt_add_left htop n)) hd
      (pairInput v m)).mpr (Or.inr ⟨m,hm,by simp [pairInput]⟩)
    exact hh
  have hreach : ∀b : Fin 2,Strict3653.usesG n C g (opnd C top b)=true →
      ∃k,opnd C top b=n+k ∧ k<C.gates.length ∧ (g=k ∨ InCone n C g k) := by
    intro b hb
    exact Strict3653.usesG_reach hC.1 g (opnd C top b)
      ((Ledger.operand_bound n C hC.1 top htop b).trans (Nat.add_lt_add_left htop n)) hb
  rcases hreader with ⟨h0,h1⟩ | ⟨h1,h0⟩
  · exact PairPreserve.alias_pair_from_reader G C P hC hfixed j p (bW-n) g v m hsem hjg hBg hout
      huniq top (hcones top htop) hand htg 0 1 (by decide) (hreach 0 h0) (hother 1 h1) hjv hBv hgv
  · exact PairPreserve.alias_pair_from_reader G C P hC hfixed j p (bW-n) g v m hsem hjg hBg hout
      huniq top (hcones top htop) hand htg 1 0 (by decide) (hreach 1 h1) (hother 0 h0) hjv hBv hgv

end PEqualNP.Outside.L_meta_3754.ExceptionalPair

namespace PEqualNP.Outside.L_meta_3754.Positive
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core

lemma unique_dirty_positive_impossible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (g : ℕ)
    (hcolor : ∀a b : Fin n,G.Adj a b → s a≠s b) (hcycle : NoFourCycle G)
    (hC : IsLeastAO G C) (hfixed : IsLiftFixedPoint G C)
    (hg : g<C.gates.length) (hand : (gateAt C g).op=GateOp.and)
    (hdirty : ¬BelowF G C g)
    (hclean : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → k≠g → BelowF G C k)
    (hunit : ∃v : Fin n,gateVal n C g (PEqualNP.SplitCount.unitInput v)=true) : False := by
  have hne := Deletion.least_has_edge_of_gate G C hC g hg
  have hcones := Deletion.least_inOutputCone hC hne
  have hout := (Deletion.output_bounds hC hne).2
  have hnoimp : ∀k<C.gates.length,(gateAt C k).op=GateOp.and →
      ∀t∈(gateAt C k).inputs,¬∀x : Fin n → Bool,
        Circuit.eval ⟨C.gates,t⟩ (List.ofFn x)=true → graphFun G ∅ x=true := by
    intro k hk hkAND t ht
    exact Bypass.least_no_and_below_operand hC hk hkAND ht
  obtain ⟨aW,bW,v,m,E⟩ := Strict3653.least_exceptional n G C s g hcolor hcycle hC hfixed
    hnoimp hcones hg hand hdirty hclean hunit
  obtain ⟨j,p,u,hjg,hjor,hp,hjin,hpv,huv,hpu,huA,hum,hjv,hju,hjB,hjnb,hpB⟩ :=
    Glue.select_exception G C s g aW bW v m hC hfixed (hcones g hg) hdirty hclean E
  let P := Bypass.patchThree C j p (bW-n) g v.val
  have hP : IsAO2 n P := Bypass.patchThree_isAO2 hC.1 j p (bW-n) g v.val hp v.isLt
  have hlen : P.gates.length=C.gates.length := Bypass.patchThree_length C j p (bW-n) g v.val
  have hsem : PatchSemantics.AliasSem n C P j p (bW-n) g v :=
    Bypass.patchThree_semantics hC.1 j p (bW-n) g v hp
  have hpair : wireVal n P C.output (pairInput v m)=true :=
    ExceptionalPair.exceptional_alias_pair G C P s hC hfixed g aW bW v m E j p hjg
      hsem hout hcones hclean hjv
  have hnoimpOpnd : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → ∀b : Fin 2,
      ¬∀x : Fin n → Bool,wireVal n C (opnd C k b) x=true → graphFun G ∅ x=true := by
    intro k hk hkAND b
    exact PairPreserve.noimp G C hC k hk hkAND b
  have hrestore := PatchSemantics.exceptional_restoration G hcycle s hcolor C P hC.1 hP
    hC.2.1 hlen hfixed g aW bW v m hg E hcones hclean hnoimpOpnd j p u hjg hjor hp
    hjin huv huA hjv hju hout hsem hpair
  have hBg : bW-n<g := by have := E.bBound;have := E.bGate;omega
  apply Bypass.patch_three_strict_saving hC j p (bW-n) g aW v m hjg hBg hg hjB hp
    (E.aBound.trans (Nat.add_lt_add_left hg n)) hout
  intro x
  change (wireVal n P C.output x || (x m && wireVal n P aW x))=graphFun G ∅ x
  exact hrestore x

end PEqualNP.Outside.L_meta_3754.Positive
