import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_4101_aux

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
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
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
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

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
      · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
      · rw [ite_eq_right hi, ite_eq_right hi]

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
  rw [gateAt_bypass (by omega), ite_eq_left hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

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
          gateAt_bypass (by omega), ite_eq_right hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, ite_eq_left (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [ite_eq_left (by omega), bypass_val_lt hx hr i hi]
            · rw [ite_eq_right (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, ite_eq_left (by omega), ite_eq_left (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), ite_eq_left h3, ite_eq_left (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), ite_eq_right h3, ite_eq_right (by omega)]
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
    rw [gateAt_bypass (by omega), ite_eq_left h12]
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


/-- Every AND is an implicant of the chosen output function. -/
def Productive (n : Nat) (C : Circuit) (F : (Fin n → Bool) → Bool) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
    ∀ x : Fin n → Bool, val C (List.ofFn x) (n+j) = true → F x = true

lemma bypass_productive {n : Nat} {C : Circuit} {F : (Fin n → Bool) → Bool}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hp : Productive n C F)
    {r i : Nat} (hr : r < C.gates.length) (hi : i < n+r)
    (hsafe : ∀ x : Fin n → Bool, F x = false →
      val C (List.ofFn x) (n+r) = val C (List.ofFn x) i) :
    Productive n (bypass n C r i) F := by
  intro k hk hop x hv
  by_contra hFx
  have hF : F x = false := by simpa using hFx
  have hA : ∀ t < C.gates.length,
      (gateAt C t).op = GateOp.and ∨ (gateAt C t).op = GateOp.or :=
    fun t ht => hAO.1 _ (gateAt_mem ht)
  have hrel := bypass_rel (R := Eq) (fun _ => rfl) opMono_eq
    (List.length_ofFn (f := x)) hA hr (Or.inl hi) (fun _ => hsafe x hF)
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hop
  by_cases hkr : k < r
  · rw [ite_eq_left hkr] at hop
    have heq := hrel (n+k) (by omega)
    rw [aliasWire_lt_self (by omega)] at heq
    have := hp k (by omega) hop x (heq.trans hv)
    rw [hF] at this
    cases this
  · rw [ite_eq_right hkr] at hop
    have heq := hrel (n+(k+1)) (by omega)
    rw [aliasWire_gt_self (by omega)] at heq
    have heqidx : n+(k+1)-1 = n+k := by omega
    rw [heqidx] at heq
    have := hp (k+1) (by omega) hop x (heq.trans hv)
    rw [hF] at this
    cases this

lemma addTop_productive {n : Nat} {C : Circuit} {F : (Fin n → Bool) → Bool}
    (hp : Productive n C F) (a b : Nat) :
    Productive n (addTop n C ⟨GateOp.or, [a,b]⟩) F := by
  intro k hk hop x hv
  rw [addTop_length] at hk
  by_cases hkl : k < C.gates.length
  · rw [gateAt_addTop_lt hkl] at hop
    have heq := val_prefix (C := C) (D := addTop n C ⟨GateOp.or, [a,b]⟩)
      (List.length_ofFn (f := x)) (m := C.gates.length) (by omega)
      (by rw [addTop_length]; omega)
      (fun q hq => gateAt_addTop_lt hq) (n+k) (by omega)
    exact hp k hkl hop x (heq.symm.trans hv)
  · have hkq : k = C.gates.length := by omega
    subst k
    rw [gateAt_addTop_len] at hop
    cases hop


/-- Minimality only among circuits whose AND gates are implicants. -/
def MinimalProductive (n : Nat) (C : Circuit) (F : (Fin n → Bool) → Bool) : Prop :=
  ∀ D : Circuit, PEqualNP.TopForm.IsAO2 n D → Productive n D F →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x) → C.size ≤ D.size

lemma no_and_reader {n : Nat} {C : Circuit} {F : (Fin n → Bool) → Bool}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hp : Productive n C F)
    (hcorrect : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hmin : MinimalProductive n C F)
    {j r : Nat} (hr : r < C.gates.length)
    (hmem : n+j ∈ (gateAt C r).inputs) (hand : (gateAt C r).op = GateOp.and)
    (hbelow : ∀ x : Fin n → Bool, val C (List.ofFn x) (n+j) = true → F x = true) : False := by
  have hjr : j < r := by have := hAO.2.1 r hr _ hmem; omega
  have hA : ∀ t < C.gates.length,
      (gateAt C t).op = GateOp.and ∨ (gateAt C t).op = GateOp.or :=
    fun t ht => hAO.1 _ (gateAt_mem ht)
  have hprod : Productive n (bypass n C r (n+j)) F :=
    bypass_productive hAO hp hr (by omega) (by
      intro x hFx
      have hz : val C (List.ofFn x) (n+j) = false := by
        by_contra h
        have := hbelow x (by simpa using h)
        rw [hFx] at this
        cases this
      have hg : val C (List.ofFn x) (n+r) = false := by
        by_contra h
        have := ((val_and List.length_ofFn hr hand).mp (by simpa using h)) (n+j) hmem
        rw [hz] at this
        cases this.2
      exact hg.trans hz.symm)
  have heval : ∀ x : Fin n → Bool,
      (bypass n C r (n+j)).eval (List.ofFn x) = F x := by
    intro x
    rw [caseB List.length_ofFn hA hr hjr hmem hand
      (fun h => (hcorrect x).trans (hbelow x h)), hcorrect]
  have hs := hmin (bypass n C r (n+j)) (isAO2_bypass hAO (by omega)) hprod heval
  change C.gates.length ≤ (bypass n C r (n+j)).gates.length at hs
  rw [bypass_length] at hs
  omega

lemma other_operand {l : List Nat} (hlen : l.length = 2) {p : Nat} (hp : p ∈ l) :
    ∃ a, a ∈ l ∧ ∀ u ∈ l, u = p ∨ u = a := by
  obtain ⟨a,b,hab⟩ := List.length_eq_two.1 hlen
  rw [hab] at hp ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · refine ⟨b, by simp, ?_⟩
    intro u hu
    simpa using hu
  · refine ⟨a, by simp, ?_⟩
    intro u hu
    simpa [or_comm] using hu

lemma or_drop_value {n : Nat} {C : Circuit} {x : List Bool} (hx : x.length = n)
    {j r a : Nat} (hr : r < C.gates.length) (ha : a < n+r)
    (hor : (gateAt C r).op = GateOp.or) (ha_mem : a ∈ (gateAt C r).inputs)
    (hspan : ∀ u ∈ (gateAt C r).inputs, u = n+j ∨ u = a)
    (hz : val C x (n+j) = false) : val C x (n+r) = val C x a := by
  rw [Bool.eq_iff_iff, val_or hx hr hor]
  constructor
  · rintro ⟨u,hu,_,hv⟩
    rcases hspan u hu with rfl | rfl
    · rw [hz] at hv
      cases hv
    · exact hv
  · intro hv
    exact ⟨a,ha_mem,ha,hv⟩

lemma no_two_or_readers {n : Nat} {C : Circuit} {F : (Fin n → Bool) → Bool}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hp : Productive n C F)
    (hcorrect : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hmin : MinimalProductive n C F) (hout : C.output < n+C.gates.length)
    {j r1 r2 : Nat} (h12 : r1 < r2) (hr2 : r2 < C.gates.length)
    (hm1 : n+j ∈ (gateAt C r1).inputs) (hm2 : n+j ∈ (gateAt C r2).inputs)
    (hor1 : (gateAt C r1).op = GateOp.or) (hor2 : (gateAt C r2).op = GateOp.or)
    (hbelow : ∀ x : Fin n → Bool, val C (List.ofFn x) (n+j) = true → F x = true) : False := by
  have hr1 : r1 < C.gates.length := by omega
  have hj1 : j < r1 := by have := hAO.2.1 r1 hr1 _ hm1; omega
  obtain ⟨a,ha_mem,hspan1⟩ := other_operand (hAO.2.2 _ (gateAt_mem hr1)) hm1
  obtain ⟨b,hb_mem,hspan2⟩ := other_operand (hAO.2.2 _ (gateAt_mem hr2)) hm2
  have ha : a < n+r1 := hAO.2.1 r1 hr1 _ ha_mem
  have hb : b < n+r2 := hAO.2.1 r2 hr2 _ hb_mem
  have hA : ∀ t < C.gates.length,
      (gateAt C t).op = GateOp.and ∨ (gateAt C t).op = GateOp.or :=
    fun t ht => hAO.1 _ (gateAt_mem ht)
  have hz (x : Fin n → Bool) (hx : F x = false) : val C (List.ofFn x) (n+j) = false := by
    by_contra h
    have := hbelow x (by simpa using h)
    rw [hx] at this
    cases this
  let D1 := bypass n C r2 b
  let D2 := bypass n D1 r1 a
  let D3 := addTop n D2 ⟨GateOp.or, [D2.output,n+j]⟩
  have hAO1 : PEqualNP.TopForm.IsAO2 n D1 := isAO2_bypass hAO hb
  have hprod1 : Productive n D1 F :=
    bypass_productive hAO hp hr2 hb (fun x hx =>
      or_drop_value List.length_ofFn hr2 hb hor2 hb_mem hspan2 (hz x hx))
  have hr1' : r1 < D1.gates.length := by dsimp [D1]; rw [bypass_length]; omega
  have hgate1 : gateAt D1 r1 = gateAt C r1 := by
    dsimp [D1]
    rw [gateAt_bypass (by omega), ite_eq_left h12]
  have hAO2 : PEqualNP.TopForm.IsAO2 n D2 := isAO2_bypass hAO1 ha
  have hprod2 : Productive n D2 F :=
    bypass_productive hAO1 hprod1 hr1' ha (by
      intro x hx
      apply or_drop_value List.length_ofFn hr1' ha
      · rw [hgate1]; exact hor1
      · rw [hgate1]; exact ha_mem
      · rw [hgate1]; exact hspan1
      · dsimp [D1]
        rw [bypass_val_lt List.length_ofFn hr2 (n+j) (by omega)]
        exact hz x hx)
  have hl2 : D2.gates.length = C.gates.length - 2 := by
    dsimp [D2,D1]
    rw [bypass_length,bypass_length]
    omega
  have ho2 : D2.output < n+(C.gates.length-2) := by
    dsimp [D2,D1]
    rw [bypass_output,bypass_output]
    have h3 := aliasWire_lt (u := C.output) (m := n+(C.gates.length-1)) hb
      (by omega) (by omega)
    exact aliasWire_lt ha (by omega) (by omega)
  have hAO3 : PEqualNP.TopForm.IsAO2 n D3 :=
    isAO2_addTop hAO2 (by rw [hl2]; exact ho2) (by rw [hl2]; omega)
  have hprod3 : Productive n D3 F := addTop_productive hprod2 _ _
  have heval : ∀ x : Fin n → Bool, D3.eval (List.ofFn x) = F x := by
    intro x
    have he := caseC List.length_ofFn hA hr2 h12 hj1 ha hb hor1 hor2 ha_mem hb_mem
      hspan1 hspan2 (fun h => (hcorrect x).trans (hbelow x h))
    exact he.trans (hcorrect x)
  have hs := hmin D3 hAO3 hprod3 heval
  change C.gates.length ≤ D3.gates.length at hs
  dsimp [D3] at hs
  rw [addTop_length,hl2] at hs
  omega


def OrStep (n : Nat) (C : Circuit) (u v : Nat) : Prop :=
  ∃ j, v = n+j ∧ (gateAt C j).op = GateOp.or ∧ u ∈ (gateAt C j).inputs

def OrPath (n : Nat) (C : Circuit) := Relation.ReflTransGen (OrStep n C)

lemma gate_bound_of_mem {C : Circuit} {j u : Nat} (hu : u ∈ (gateAt C j).inputs) :
    j < C.gates.length := by
  by_contra hj
  have heq : gateAt C j = ⟨GateOp.or, []⟩ := by
    unfold gateAt
    apply List.getD_eq_default
    omega
  rw [heq] at hu
  cases hu

lemma gate_bound_of_and {C : Circuit} {j : Nat} (hj : (gateAt C j).op = GateOp.and) :
    j < C.gates.length := by
  by_contra hb
  have heq : gateAt C j = ⟨GateOp.or, []⟩ := by
    unfold gateAt
    apply List.getD_eq_default
    omega
  rw [heq] at hj
  cases hj

lemma orPath_val {n : Nat} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 n C)
    {u v : Nat} (hr : OrPath n C u v) (x : Fin n → Bool) :
    val C (List.ofFn x) u = true → val C (List.ofFn x) v = true := by
  induction hr with
  | refl => exact fun h => h
  | @tail b c hpath hstep ih =>
    intro hu
    obtain ⟨j,rfl,hop,hmem⟩ := hstep
    have hj : j < C.gates.length := gate_bound_of_mem hmem
    exact (val_or List.length_ofFn hj hop).2 ⟨b,hmem,hAO.2.1 j hj b hmem,ih hu⟩

lemma common_below {n : Nat} {C : Circuit} {F : (Fin n → Bool) → Bool}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hp : Productive n C F)
    {j a b w : Nat} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hins : (gateAt C j).inputs = [a,b])
    (ha : OrPath n C w a) (hb : OrPath n C w b) :
    ∀ x : Fin n → Bool, val C (List.ofFn x) w = true → F x = true := by
  intro x hw
  apply hp j hj hand x
  apply (val_and List.length_ofFn hj hand).2
  intro u hu
  rw [hins] at hu
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl
  · exact ⟨hAO.2.1 j hj u (by simp [hins]),orPath_val hAO ha x hw⟩
  · exact ⟨hAO.2.1 j hj u (by simp [hins]),orPath_val hAO hb x hw⟩

lemma no_overlap_minimal {n : Nat} {C : Circuit} {F : (Fin n → Bool) → Bool}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hp : Productive n C F)
    (hcorrect : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hmin : MinimalProductive n C F) (hout : C.output < n+C.gates.length)
    {j a b w : Nat} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hins : (gateAt C j).inputs = [a,b])
    (hw : n ≤ w) (ha : OrPath n C w a) (hb : OrPath n C w b) : False := by
  have hclaim : ∀ {u : Nat}, OrPath n C u a → n ≤ u → OrPath n C u b → False := by
    intro u hu
    induction hu using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro hna hab
      have below := common_below hAO hp hj hand hins (Relation.ReflTransGen.refl) hab
      have heq : n+(a-n) = a := by omega
      apply no_and_reader hAO hp hcorrect hmin hj (j := a-n)
      · rw [heq]; simp [hins]
      · exact hand
      · rw [heq]; exact below
    | @head u v hstep hva ih =>
      intro hnu hub
      have hua : OrPath n C u a := Relation.ReflTransGen.head hstep hva
      have below := common_below hAO hp hj hand hins hua hub
      rcases Relation.ReflTransGen.cases_head hub with hub | ⟨z,huz,hzb⟩
      · subst b
        have heq : n+(u-n) = u := by omega
        apply no_and_reader hAO hp hcorrect hmin hj (j := u-n)
        · rw [heq]; simp [hins]
        · exact hand
        · rw [heq]; exact below
      · obtain ⟨r1,hv,hor1,hm1⟩ := hstep
        obtain ⟨r2,hz,hor2,hm2⟩ := huz
        have hr1 : r1 < C.gates.length := gate_bound_of_mem hm1
        have hr2 : r2 < C.gates.length := gate_bound_of_mem hm2
        by_cases heq : r1 = r2
        · subst r2
          have hvz : v = z := hv.trans hz.symm
          subst z
          apply ih (by omega)
          simpa only [hv, OrPath] using hzb
        · have hequ : n+(u-n) = u := by omega
          have hb' : ∀ x : Fin n → Bool, val C (List.ofFn x) (n+(u-n)) = true → F x = true := by
            rw [hequ]; exact below
          have hm1' : n+(u-n) ∈ (gateAt C r1).inputs := by rw [hequ]; exact hm1
          have hm2' : n+(u-n) ∈ (gateAt C r2).inputs := by rw [hequ]; exact hm2
          rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
          · exact no_two_or_readers hAO hp hcorrect hmin hout hlt hr2 hm1' hm2' hor1 hor2 hb'
          · exact no_two_or_readers hAO hp hcorrect hmin hout hgt hr1 hm2' hm1' hor2 hor1 hb'
  exact hclaim ha hw hb

end PEqualNP.Outside.L_meta_4101_aux


namespace PEqualNP.Outside.L_meta_4101_aux.CleanCount

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


def posRead {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  match w with
  | 0 => false
  | i + 1 => (wiresFrom gs (List.ofFn x)).getD i false

def clampWire (lim i : ℕ) : ℕ := if i < lim then i + 1 else 0

def gateAtPos (n : ℕ) (gs : List Gate) (w : ℕ) : Gate :=
  gs.getD (w - (n + 1)) ⟨GateOp.or, []⟩

def firstWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 0 (w-1))

def secondWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 1 ((gateAtPos n gs w).inputs.getD 0 (w-1)))

def andPos (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
  match (gateAtPos n gs w).op with
  | GateOp.and => true
  | _ => false

lemma clamp_lt (w i : ℕ) (hw : 0 < w) : clampWire (w-1) i < w := by
  unfold clampWire
  split <;> omega

lemma pos_clamp {n : ℕ} (gs : List Gate) (lim i : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire lim i) x =
    (if i < lim then (wiresFrom gs (List.ofFn x)).getD i false else false) := by
  simp only [clampWire]
  split <;> rfl

lemma pos_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    posRead gs (i+1) x = x ⟨i,hi⟩ := by
  change (wiresFrom gs (List.ofFn x)).getD i false = x ⟨i,hi⟩
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hi),List.getElem_ofFn]

lemma pos_mono {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) :
    posRead gs w x = true → posRead gs w y = true := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    apply wiresFrom_mono gs ops _ _ (by simp)
    intro j h
    by_cases hj : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction

def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def singletonBits {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z = u)
def pairBits {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

lemma edge_single {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ¬ edgeTrue G (singletonBits u) := by
  rintro ⟨i,j,h,hi,hj⟩
  simp only [singletonBits, decide_eq_true_eq] at hi hj
  subst i
  subst j
  exact G.loopless.irrefl u h

lemma edge_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    edgeTrue G (pairBits u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    simp only [pairBits, decide_eq_true_eq] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (G.loopless.irrefl _ h).elim
    · exact h
    · exact h.symm
    · exact (G.loopless.irrefl _ h).elim
  · intro h
    exact ⟨u,v,h,by simp [pairBits],by simp [pairBits]⟩

lemma binary_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (nonempty : op = GateOp.and → l ≠ [])
    (v : ℕ → Bool) (lim : ℕ) (vd : v lim = false) :
    op.eval (l.map v) =
      (if (match op with | GateOp.and => true | _ => false) then
        v (l.getD 0 lim) && v (l.getD 1 (l.getD 0 lim))
       else v (l.getD 0 lim) || v (l.getD 1 (l.getD 0 lim))) := by
  cases l with
  | nil =>
    rcases hop with rfl | rfl
    · exact (nonempty rfl rfl).elim
    · simp [GateOp.eval,vd]
  | cons i t =>
    cases t with
    | nil => rcases hop with rfl | rfl <;> simp [GateOp.eval]
    | cons j t =>
      have ht : t = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst t
      rcases hop with rfl | rfl <;> simp [GateOp.eval]

def supports {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => posRead gs w (singletonBits u) = true

lemma mem_support {n : ℕ} (gs : List Gate) (w : ℕ) (u : Fin n) :
    u ∈ supports gs w ↔ posRead gs w (singletonBits u) = true := by simp [supports]


def cleanOn {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
  ∀ (j : Fin gs.length) (x : Fin n → Bool),
    (x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) →
    (gs.get j).op = GateOp.and →
    (wiresFrom gs (List.ofFn x)).getD (n + j.val) false = true → edgeTrue G x

def binaryOps (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma gateAt_index {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtPos n gs (n+j+1) = gs[j] := by
  unfold gateAtPos
  rw [show n+j+1-(n+1) = j by omega,List.getD_eq_getElem _ _ hj]

lemma pos_gate {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs)
    (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  have nonempty : gs[j].op = GateOp.and → gs[j].inputs ≠ [] := by
    intro ha hempty
    let z : Fin n → Bool := fun _ => false
    have eqg := getD_wiresFrom_gate gs (List.ofFn z) j hj
    simp only [List.length_ofFn, hempty, List.map_nil, ha, GateOp.eval, List.all_nil] at eqg
    obtain ⟨u,v,_,h,_⟩ := clean ⟨j,hj⟩ z (Or.inl rfl) ha eqg
    contradiction
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 nonempty
    (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n+j) (by simp)

lemma pos_clean {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) (x : Fin n → Bool)
    (hx : x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) :
    posRead gs w x = true → edgeTrue G x := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  rw [hw] at ha ⊢
  simp only [andPos, gateAt_index gs j hj] at ha
  have hop : gs[j].op = GateOp.and := by
    cases h : gs[j].op <;> simp_all
  exact clean ⟨j,hj⟩ x hx hop

lemma support_base {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n+1) :
    (supports (n:=n) gs w).card ≤ 1 := by
  cases w with
  | zero => simp [supports,posRead]
  | succ i =>
    have hi : i < n := by omega
    have hs : supports gs (i+1) = {⟨i,hi⟩} := by
      ext u
      simp [mem_support,pos_input gs i hi,singletonBits,eq_comm]
    simp [hs]

lemma hit_base {n : ℕ} (gs : List Gate) (w : ℕ) (u v : Fin n) (hw : w < n+1) :
    posRead gs w (pairBits u v) = true → u ∈ supports gs w ∨ v ∈ supports gs w := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    have hi : i<n := by omega
    simp [mem_support,pos_input gs i hi,pairBits,singletonBits]

lemma support_and {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) : supports (n:=n) gs w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact edge_single G u (pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inl ⟨u, rfl⟩)) ((mem_support gs w u).mp hu))

lemma support_or {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = false) :
    supports (n:=n) gs w = supports gs (firstWire n gs w) ∪ supports gs (secondWire n gs w) := by
  ext u
  simp only [Finset.mem_union,mem_support,pos_gate G gs ops clean w lo hi,ha]
  simp

lemma cross_support {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = true)
    (u : Fin n) (hu : u ∈ supports gs (firstWire n gs w))
    (v : Fin n) (hv : v ∈ supports gs (secondWire n gs w)) : G.Adj u v := by
  apply (edge_pair G u v).mp
  apply pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inr ⟨u, v, rfl⟩))
  rw [pos_gate G gs ops clean w lo hi,ha]
  simp only [ite_true, Bool.and_eq_true]
  have hm := pos_mono (n:=n) gs (fun g h => (ops g h).1)
  constructor
  · apply hm (firstWire n gs w) (singletonBits u) (pairBits u v) _ ((mem_support _ _ _).mp hu)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]
  · apply hm (secondWire n gs w) (singletonBits v) (pairBits u v) _ ((mem_support _ _ _).mp hv)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]


lemma root_read {n : ℕ} (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire (n+gs.length) out) x = (Circuit.mk gs out).eval (List.ofFn x) := by
  rw [pos_clamp]
  change (if out < n+gs.length then _ else _) = (wiresFrom gs (List.ofFn x)).getD out false
  split_ifs with h
  · rfl
  · symm
    apply List.getD_eq_default
    simpa only [length_wiresFrom, List.length_ofFn] using Nat.le_of_not_lt h

lemma root_bound (n len out : ℕ) : clampWire (n+len) out < n+1+len := by
  unfold clampWire
  split <;> omega

lemma root_support_empty {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    supports (n:=n) gs (clampWire (n+gs.length) out) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u h
  apply edge_single G u
  apply (heval _).mp
  rw [← root_read]
  exact (mem_support _ _ _).mp h

lemma root_hits {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    ∀ u v, G.Adj u v → posRead gs (clampWire (n+gs.length) out) (pairBits u v) = true := by
  intro u v h
  rw [root_read,heval]
  exact (edge_pair G u v).mpr h

theorem countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

theorem dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

theorem gate_partition_count (n len : ℕ) (A : ℕ → Bool) (S : ℕ → Finset (Fin n)) :
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = true)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      1 < (S w).card)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      (S w).card ≤ 1)).card ≤ len := by
  classical
  let gates := Finset.range (n + 1 + len)
  let ands := gates.filter (fun w => n + 1 ≤ w ∧ A w = true)
  let large := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let small := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
  change ands.card + large.card + small.card ≤ len
  have hdis : Disjoint ands large := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have a := (Finset.mem_filter.mp h₁).2.2
    have b := (Finset.mem_filter.mp h₂).2.2.1
    simp_all
  have hdis' : Disjoint (ands ∪ large) small := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have b := (Finset.mem_filter.mp h₂).2.2
    rcases Finset.mem_union.mp h₁ with ha | hl
    · have a := (Finset.mem_filter.mp ha).2.2
      simp_all
    · have a := (Finset.mem_filter.mp hl).2.2.2
      exact (Nat.not_lt_of_ge b.2) a
  have hsub : (ands ∪ large) ∪ small ⊆ Finset.Ico (n+1) (n+1+len) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · rcases Finset.mem_union.mp h with h | h <;>
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
        Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
  rw [← Finset.card_union_of_disjoint hdis, ← Finset.card_union_of_disjoint hdis']
  simpa using Finset.card_le_card hsub

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A ha hb (a w)
        else coverCert k N S a b A ha hb (b w)
      else
        coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

theorem cover_half (n k N r : ℕ) (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool) (hr : r < N) (hrS : S r = ∅)
    (hrH : ∀ u v, G.Adj u v → H r u v)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdag : ∀ (f : ℕ → Finset (Fin n)) (R B : Finset ℕ),
      (∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
        (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) →
      (R.biUnion f).card ≤ R.card + B.card) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ 1 + ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1).card := by
  let f := coverCert k N S a b A ha hb
  let B := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := by
    exact coverCert.eq_1 ..
  have hit : ∀ w, w < N → (S w).card ≤ 1 →
      ∀ u v, H w u v → u ∈ f w ∨ v ∈ f w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v hwuv
      rw [feq, ite_eq_left ht]
      by_cases hkw : k ≤ w
      · rw [ite_eq_left ⟨hkw, hw⟩]
        cases hg : A w with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have heq := horS w hkw hw hg
          have hta : (S (a w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_left
          have htb : (S (b w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_right
          have hia := ha w hkw hw
          have hib := hb w hkw hw
          rcases horH w u v hkw hw hg hwuv with h | h
          · have hitA := ih _ hia (hia.trans hw) hta u v h
            simp only [Finset.mem_union]
            tauto
          · have hitB := ih _ hib (hib.trans hw) htb u v h
            simp only [Finset.mem_union]
            tauto
        | true =>
          simp only [ite_true]
          have hz := handH w u v hkw hw hg hwuv
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            have hl := ha w hkw hw
            exact ih _ hl (hl.trans hw) htA u v hz.1
          · rw [ite_eq_right htA]
            have hl := hb w hkw hw
            exact ih _ hl (hl.trans hw) ((handS w hkw hw hg).resolve_left htA) u v hz.2
      · rw [ite_eq_right (fun h => hkw h.1)]
        exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv
  refine ⟨f r, fun u v huv => hit r hr (by simp [hrS]) u v (hrH u v huv), ?_⟩
  have hstep (w : ℕ) (hw : 1 < (f w).card) :
      (∃ j < w, f w ⊆ f j) ∨
        (w ∈ B ∧ ∃ i < w, ∃ j < w, f w ⊆ f i ∪ f j) := by
    have ht : (S w).card ≤ 1 := by
      by_contra ht
      rw [feq, ite_eq_right ht] at hw
      simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h
      rw [feq, ite_eq_left ht, ite_eq_right h] at hw
      omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    cases hop : A w with
    | false =>
      right
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩,
        a w, hia, b w, hib, ?_⟩
      rw [feq, ite_eq_left ht, ite_eq_left hg, hop]
      simp
    | true =>
      left
      by_cases htA : (S (a w)).card ≤ 1
      · refine ⟨a w, hia, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left htA]
      · refine ⟨b w, hib, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right htA]
  simpa [B] using hdag f {r} B hstep

theorem edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → Disjoint (S (a w)) (S (b w))) :
    ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w))) := by
  induction r using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hkw : k ≤ w
    · have hia := ha w hkw hr
      have hib := hb w hkw hr
      cases hop : A w with
      | false =>
        have hSw := horS w hkw hr hop
        rw [hSw, Finset.mem_union] at hx hy
        rcases horH w x y hkw hr hop hxy with h | h
        · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        have htrue := handH w x y hkw hr hop hxy
        by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
        · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
          · refine ⟨w, hkw, hr, hop, ?_⟩
            have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop)
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hd hax hbx)
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hd hay hby)
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)

theorem edge_finset_gate_bound (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hside : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, G.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    G.edgeFinset.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    have he : G.edgeFinset = ∅ := Finset.eq_empty_of_forall_notMem (fun e => isEmptyElim e)
    simp [he]
  | inr hn =>
    let z := Classical.choice hn
    let AS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true)
    let OS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w),
          (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA⟩ : w < N ∧ k ≤ w ∧ A w = true := by simpa [AS] using hw
        obtain ⟨ha,hb⟩ := hparents w hk hN
        have hJ := hjoin w hk hN hA
        rcases hside w hk hN hA with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
            exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
            exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c,h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hbig
      exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i = false := by
          cases he : A i with
          | false => rfl
          | true => simp [hzero i hk hgood.1 he] at hi
        have ⟨ha,hb⟩ := hparents i hk hgood.1
        have hu := hunion i hk hgood.1 hA
        have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        right
        refine ⟨?_, a i, ha, b i, hb, ?_⟩
        · simp [B, OS, hgood.1, hk, hA, hi, owner_eq i c hi hgood.2]
        · rw [hf,hfa,hfb,hu]
      · simp [F,hgood] at hi
    let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c,x))
    have subset : G.edgeFinset ⊆ Finset.univ.biUnion E := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        have huv : G.Adj u v := G.mem_edgeFinset.mp he
        obtain ⟨w,hk,hN,hA,how⟩ := hcover u v huv
        have hw : w ∈ AS := by simp [AS,hN,hk,hA]
        have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw,rfl⟩)
        have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
            s(cOf w,t) ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
            Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w,hj,ht⟩)⟩
        rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
        · rcases spec w hw u hu v hv with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he, Sym2.eq_swap] using member u ht
          · simpa only [he] using member v ht
    have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
      _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
      _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]

theorem total_from_model (n k N r L : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hr : r < N) (hrS : S r = ∅) (hrH : ∀ u v, G.Adj u v → H r u v)
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hpartition :
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)).card ≤ L) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ L + 1 := by
  classical
  have hd (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) : Disjoint (S (a w)) (S (b w)) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    exact G.loopless.irrefl t (hjoin w hk hN hA t ht t ht')
  have hside (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) :
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1 := by
    by_contra! hf
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hf.1
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hf.2
    have hJ := hjoin w hk hN hA
    exact hc4 u x v y huv hxy ⟨hJ u hu x hx, (hJ v hv x hx).symm, hJ v hv y hy, (hJ u hu y hy).symm⟩
  have births (u v) (huv : G.Adj u v) := edge_birth n k N r S H a b A u v hr
    (hrH u v huv) (by simp [hrS]) (by simp [hrS]) hinput ha hb horS horH handH hd
  have edgeCount := edge_finset_gate_bound n k N G S a b A hc4 hsmall
    (fun w hk hN => ⟨ha w hk hN, hb w hk hN⟩) hzero horS hjoin hside births
  obtain ⟨T,hT,hcard⟩ := cover_half n k N r G S H a b A hr hrS hrH hinput ha hb
    horS horH hside handH (fun f R B step => dag_union_bound f R B step)
  exact ⟨T,hT,by omega⟩

theorem pairCleanBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (x = (fun _ => false) ∨ (∃ u : Fin n, x = fun z => decide (z = u)) ∨ (∃ u v : Fin n, x = fun z => decide (z = u ∨ z = v))) → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G inst hc4 gs out ops eval clean
  have he : ∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x := by
    intro x
    rw [eval]
    exact decide_eq_true_iff
  apply total_from_model n (n+1) (n+1+gs.length) (clampWire (n+gs.length) out) gs.length G
    (supports gs) (fun w u v => posRead gs w (pairBits u v) = true)
    (firstWire n gs) (secondWire n gs) (andPos n gs) hc4 (root_bound n gs.length out)
    (root_support_empty G gs out he) (root_hits G gs out he) (support_base gs) (hit_base gs)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · exact support_or G gs ops clean
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,Bool.false_eq_true,ite_false,Bool.or_eq_true]
      using h
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,ite_true,Bool.and_eq_true] using h
  · exact support_and G gs clean
  · exact cross_support G gs ops clean
  · exact gate_partition_count n gs.length (andPos n gs) (supports gs)



end PEqualNP.Outside.L_meta_4101_aux.CleanCount


namespace PEqualNP.Outside.L_meta_4101_aux.Plane

def near (p l : Fin 13) : Prop := p - l ∈ ([0, 1, 3, 9] : List (Fin 13))

def pV (p : Fin 13) : Fin 26 := Fin.castAdd 13 p

def lV (l : Fin 13) : Fin 26 := Fin.natAdd 13 l

def directedB (u v : Fin 26) : Bool := by
  letI : DecidableRel near := fun p l =>
    inferInstanceAs (Decidable (p - l ∈ ([0, 1, 3, 9] : List (Fin 13))))
  exact decide (u.val < 13 ∧ 13 ≤ v.val ∧
    near (Fin.ofNat 13 u.val) (Fin.ofNat 13 (v.val - 13)))

def adjB (u v : Fin 26) : Bool := directedB u v || directedB v u

lemma adjB_symm (u v : Fin 26) : adjB u v = adjB v u := by
  simp [adjB, Bool.or_comm]

lemma adjB_irrefl : ∀ u : Fin 26, adjB u u = false := by
  decide +kernel

def G : SimpleGraph (Fin 26) := SimpleGraph.fromRel (fun u v => adjB u v = true)

lemma G_adj (u v : Fin 26) : G.Adj u v ↔ adjB u v = true := by
  unfold G
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rw [adjB_symm]; exact h
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    rw [adjB_irrefl] at h
    exact Bool.false_ne_true h

def common (a c : Fin 26) : Finset (Fin 26) :=
  Finset.univ.filter (fun b => adjB a b = true ∧ adjB c b = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma common_small : ∀ a c : Fin 26, a ≠ c → (common a c).card ≤ 1 := by
  decide +kernel

lemma G_c4 : ∀ a b c d : Fin 26, a ≠ c → b ≠ d →
    ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
  rintro a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
  have hb : b ∈ common a c := by
    simp only [common, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(G_adj _ _).1 hab, (G_adj _ _).1 hbc.symm⟩
  have hd : d ∈ common a c := by
    simp only [common, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(G_adj _ _).1 hda.symm, (G_adj _ _).1 hcd⟩
  have hlarge := Finset.one_lt_card.mpr ⟨b, hb, d, hd, hbd⟩
  have hsmall := common_small a c hac
  omega

def pairSet : Finset (Fin 26 × Fin 26) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ adjB p.1 p.2 = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairSet_card : pairSet.card = 52 := by decide +kernel

lemma G_edges (inst : Fintype G.edgeSet) :
    52 ≤ (@SimpleGraph.edgeFinset _ G inst).card := by
  rw [← pairSet_card]
  refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
  · intro p hp
    have hp' : p.1 < p.2 ∧ adjB p.1 p.2 = true := by simpa [pairSet] using hp
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (G_adj _ _).2 hp'.2
  · intro p hp q hq h
    have hp' : p.1 < p.2 ∧ adjB p.1 p.2 = true := by simpa [pairSet] using hp
    have hq' : q.1 < q.2 ∧ adjB q.1 q.2 = true := by simpa [pairSet] using hq
    have h' : s(p.1, p.2) = s(q.1, q.2) := h
    rw [Sym2.eq_iff] at h'
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have h3 := hp'.1
      rw [h1, h2] at h3
      exact absurd h3 (not_lt.2 hq'.1.le)

def mIdx (v : Fin 26) : Fin 13 := Fin.ofNat 13 v.val

lemma match_facts : ∀ i : Fin 13,
    adjB (pV i) (lV i) = true ∧ mIdx (pV i) = i ∧ mIdx (lV i) = i := by
  decide +kernel

lemma cover13 (T : Finset (Fin 26))
    (h : ∀ u v : Fin 26, G.Adj u v → u ∈ T ∨ v ∈ T) : 13 ≤ T.card := by
  have hs : (Finset.univ : Finset (Fin 13)) ⊆ T.image mIdx := by
    intro i _
    obtain ⟨h1, h2, h3⟩ := match_facts i
    rcases h _ _ ((G_adj _ _).2 h1) with hh | hh
    · exact Finset.mem_image.2 ⟨_, hh, h2⟩
    · exact Finset.mem_image.2 ⟨_, hh, h3⟩
  have h1 := Finset.card_le_card hs
  have h2 := Finset.card_image_le (s := T) (f := mIdx)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

lemma directedB_iff (u v : Fin 26) : directedB u v = true ↔
    ∃ p l : Fin 13, near p l ∧ u = pV p ∧ v = lV l := by
  simp only [directedB, decide_eq_true_eq]
  constructor
  · rintro ⟨hu, hv, hnear⟩
    let p : Fin 13 := ⟨u.val, hu⟩
    let l : Fin 13 := ⟨v.val - 13, by omega⟩
    have hp : Fin.ofNat 13 u.val = p := by
      apply Fin.ext
      change u.val % 13 = u.val
      omega
    have hl : Fin.ofNat 13 (v.val - 13) = l := by
      apply Fin.ext
      change (v.val - 13) % 13 = v.val - 13
      omega
    refine ⟨p, l, ?_, ?_, ?_⟩
    · simpa only [hp, hl] using hnear
    · apply Fin.ext
      rfl
    · apply Fin.ext
      change v.val = 13 + (v.val - 13)
      omega
  · rintro ⟨p, l, hnear, rfl, rfl⟩
    have hp : Fin.ofNat 13 (pV p).val = p := by
      apply Fin.ext
      change p.val % 13 = p.val
      omega
    have hl : Fin.ofNat 13 ((lV l).val - 13) = l := by
      apply Fin.ext
      change (13 + l.val - 13) % 13 = l.val
      omega
    refine ⟨?_, ?_, ?_⟩
    · exact p.isLt
    · change 13 ≤ 13 + l.val
      omega
    · simpa only [hp, hl] using hnear

lemma edge_iff (x : Fin 26 → Bool) :
    (∃ p l : Fin 13, near p l ∧ x (Fin.castAdd 13 p) = true ∧
      x (Fin.natAdd 13 l) = true) ↔
    ∃ u v : Fin 26, G.Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨p, l, hnear, hp, hl⟩
    refine ⟨pV p, lV l, (G_adj _ _).2 ?_, hp, hl⟩
    simp only [adjB, Bool.or_eq_true]
    exact Or.inl ((directedB_iff _ _).2 ⟨p, l, hnear, rfl, rfl⟩)
  · rintro ⟨u, v, huv, hu, hv⟩
    have h := (G_adj _ _).1 huv
    simp only [adjB, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨p, l, hnear, rfl, rfl⟩ := (directedB_iff _ _).1 h
      exact ⟨p, l, hnear, hu, hv⟩
    · obtain ⟨p, l, hnear, rfl, rfl⟩ := (directedB_iff _ _).1 h
      exact ⟨p, l, hnear, hv, hu⟩

end PEqualNP.Outside.L_meta_4101_aux.Plane


namespace PEqualNP.Outside.L_meta_4101_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def planeF (x : Fin 26 → Bool) : Bool :=
  decide (∃ p l : Fin 13, p-l ∈ ([0,1,3,9] : List (Fin 13)) ∧ x (Fin.castAdd 13 p) = true ∧
    x (Fin.natAdd 13 l) = true)

lemma plane_lower_bound (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 26 C)
    (hp : Productive 26 C planeF)
    (hc : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = planeF x) : 64 ≤ C.size := by
  classical
  have hcorrect : ∀ x : Fin 26 → Bool,
      C.eval (List.ofFn x) = decide (∃ u v : Fin 26,
        Plane.G.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    rw [hc x, Bool.eq_iff_iff]
    simp only [planeF, decide_eq_true_eq]
    exact Plane.edge_iff x
  have hclean : ∀ (i : Fin C.gates.length) (x : Fin 26 → Bool),
      (x = (fun _ => false) ∨ (∃ u : Fin 26, x = fun z => decide (z = u)) ∨
        (∃ u v : Fin 26, x = fun z => decide (z = u ∨ z = v))) →
      (C.gates.get i).op = GateOp.and →
      (Circuit.wires ⟨C.gates,0⟩ (List.ofFn x)).getD (26+i.val) false = true →
      ∃ u v : Fin 26, Plane.G.Adj u v ∧ x u = true ∧ x v = true := by
    intro i x _ hop hv
    have hg : (gateAt C i.val).op = GateOp.and := by
      rw [gateAt_eq i.isLt]
      exact hop
    have hF := hp i.val i.isLt hg x hv
    have hinc : ∃ p l : Fin 13, p-l ∈ ([0,1,3,9] : List (Fin 13)) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true :=
      of_decide_eq_true hF
    exact (Plane.edge_iff x).1 hinc
  obtain ⟨T,hcover,hcount⟩ := CleanCount.pairCleanBound 26 Plane.G Plane.G_c4
    C.gates C.output
    (fun g hg => ⟨hAO.1 g hg, by have := hAO.2.2 g hg; omega⟩)
    hcorrect hclean
  have hE := Plane.G_edges (inferInstance)
  have hT := Plane.cover13 T hcover
  change 64 ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_4101_aux

open PEqualNP.Outside.L_meta_4101_aux in

theorem PEqualNP.Outside.L_meta_4101 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1;   have x3 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x3 : Fin (26 : ℕ) → Bool) (x4 : ℕ) => (x1.wires (List.ofFn x3)).getD x4 Bool.false;   have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => x4 - x5 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))];   x1.size ≤ (64 : ℕ) →     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →       (∀ x7 ∈ x1.gates, x7.inputs.Nodup) →         (∀ (x8 : Fin (26 : ℕ) → Bool), x3 x8 x1.output = Bool.true ↔ ∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x4 x9 x10 ∧ x8 (Fin.castAdd (13 : ℕ) x9) = Bool.true ∧ x8 (Fin.natAdd (13 : ℕ) x10) = Bool.true) →           (∀ (x9 : ℕ), (x2 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin (26 : ℕ) → Bool), x3 x11 ((26 : ℕ) + x9) = Bool.true → x3 x11 x1.output = Bool.true) →             ∀ (x10 x11 : Fin (13 : ℕ)) (x12 x13 x14 x15 : ℕ),               have x16 : Fin (26 : ℕ) → Bool := fun (x16 : Fin (26 : ℕ)) => Decidable.decide (x16 = Fin.castAdd (13 : ℕ) x10 ∨ x16 = Fin.natAdd (13 : ℕ) x11);               have x17 : ℕ → ℕ → Prop := fun (x17 x18 : ℕ) => (x2 x17).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3 x16 ((26 : ℕ) + x17) = Bool.true ∧ Relation.ReflTransGen (fun (x19 x20 : ℕ) => ∃ (x21 : ℕ), x20 = (26 : ℕ) + x21 ∧ (x2 x21).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x19 ∈ (x2 x21).inputs) ((26 : ℕ) + x17) x18;               x4 x10 x11 → x2 x12 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x13, x14] : PEqualNP.CircuitLowerBounds.Gate } → x3 x16 ((26 : ℕ) + x12) = Bool.true → (∀ (x21 : Fin (26 : ℕ)), x16 x21 = Bool.true → (x3 (fun (x23 : Fin (26 : ℕ)) => Decidable.decide (x23 = x21)) x13 || x3 (fun (x23 : Fin (26 : ℕ)) => Decidable.decide (x23 = x21)) x14) = Bool.false) → x17 x15 x13 → x17 x15 x14 → False := by

  classical
  intro C
  dsimp only
  intro hsize hAO _ hcorrect hall p l j a b k _ hjgate hjtrue _ hka hkb
  have hcorrectF : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = planeF x := by
    intro x
    rw [Bool.eq_iff_iff]
    simpa only [PEqualNP.CircuitLowerBounds.Circuit.eval, planeF, Plane.near,
      decide_eq_true_eq] using hcorrect x
  have hprod : Productive 26 C planeF := by
    intro t _ hop x hx
    exact (hcorrectF x).symm.trans (hall t hop x hx)
  have hmin : MinimalProductive 26 C planeF := by
    intro D hD hpD hcD
    exact hsize.trans (plane_lower_bound D hD hpD hcD)
  have hand : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
      PEqualNP.CircuitLowerBounds.GateOp.and := congrArg (fun g => g.op) hjgate
  have hins : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a,b] :=
    congrArg (fun g => g.inputs) hjgate
  have hj : j < C.gates.length := gate_bound_of_and hand
  have hout : C.output < 26+C.gates.length := by
    have htrue := hall j hand
      (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) hjtrue
    by_contra ho
    have hz := val_ge (C := C) (n := 26)
      (x := List.ofFn (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)))
      List.length_ofFn (u := C.output) (by omega)
    exact Bool.false_ne_true (hz.symm.trans htrue)
  exact no_overlap_minimal hAO hprod hcorrectF hmin hout hj hand hins
    (w := 26+k) (by omega) hka.2.2 hkb.2.2
