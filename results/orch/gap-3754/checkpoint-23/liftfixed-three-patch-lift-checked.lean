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
