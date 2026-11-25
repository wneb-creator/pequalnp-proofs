import PEqualNP.Defs

-- Bypass helpers adapted from willakone, L-meta-1499, PR 3112.
namespace PEqualNP.Outside.L_meta_1772_aux.Dichotomy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
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
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
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
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

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
    (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
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
          exact hR ⟨k + 1, by omega, hk1, hi'⟩
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
    (hno : ∀ k, r < k → k < C.gates.length → n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hrk, hk, hm⟩ => absurd hm (hno k hrk hk)) _ hout).symm

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


lemma erase_eq_bypass (n : ℕ) (C : Circuit) (r i : ℕ) (hr : r < C.gates.length) :
    PEqualNP.CircuitMoves.eraseGate n C r i = bypass n C r i := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hr]
  change Circuit.mk _ (aliasWire (n + r) i C.output) = Circuit.mk _ (aliasWire (n + r) i C.output)
  congr 1
  apply List.ext_getElem
  · simp [bypass]; omega
  · intro k hk hk'
    have hlen : (C.gates.take r).length = r := by simp; omega
    have hklen : k < C.gates.length - 1 := by simpa [bypass] using hk'
    simp only [bypass, List.getElem_map, List.getElem_range]
    by_cases hkr : k < r
    · rw [if_pos hkr, List.getElem_append_left (by omega), List.getElem_take,
        gateAt_eq (by omega)]
    · rw [if_neg hkr, List.getElem_append_right (by omega), List.getElem_map,
        List.getElem_drop]
      simp only [hlen]
      have he : r + 1 + (k - r) = k + 1 := by omega
      simp only [he]
      rw [gateAt_eq (by omega : k + 1 < C.gates.length)]
      rfl

lemma mono_ops {C : Circuit} (hM : Monotone2 C) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  intro k hk
  exact (hM _ (gateAt_mem hk)).1

lemma wire_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ u, val C (List.ofFn x) u = true → val C (List.ofFn y) u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hun : u < n
    · rw [val_input (n := n) (by simp) hun, val_input (n := n) (by simp) hun]
      simpa [hun] using hxy ⟨u, hun⟩
    · by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge (n := n) (by simp) hge]
        intro h; cases h
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk, val_gate (n := n) (by simp) hk]
        apply opMono_imp _ (mono_ops hM k hk)
        intro i hi
        by_cases hil : i < n + k
        · rw [if_pos hil, if_pos hil]
          exact ih i hil
        · rw [if_neg hil, if_neg hil]
          exact id

lemma circuit_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true :=
  wire_monotone n C hM x y hxy C.output

lemma opMono_reverse : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f h

lemma bypass_mono {n : ℕ} {C : Circuit} {r i : ℕ} (hM : Monotone2 C) :
    Monotone2 (bypass n C r i) := by
  intro g hg
  obtain ⟨g', hg', hop, hlen⟩ := bypass_mem g hg
  rw [hop, hlen]
  exact hM g' hg'

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p l, G.Adj p l ∧ x p = true ∧ x l = true := by
  simp [graphFun]

lemma pair_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p l : Fin n)
    (hp : G.Adj p l) : graphFun G ∅ (PEqualNP.EdgeOwnership.pairInput p l) = true := by
  rw [graph_true]
  exact ⟨p, l, hp, by simp [PEqualNP.EdgeOwnership.pairInput], by simp [PEqualNP.EdgeOwnership.pairInput]⟩

lemma no_owned_edge_forces_ancestor
    (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (i j : ℕ)
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (sole : ∀ k < j, PEqualNP.EdgeOwnership.InCone n C k j →
      (gateAt C k).op = GateOp.and → k = i)
    (none : ∀ u v, G.Adj u v → ¬ PEqualNP.EdgeOwnership.Owns n C j u v)
    (u v : Fin n) (edge : G.Adj u v)
    (active : PEqualNP.EdgeOwnership.gateVal n C j
      (PEqualNP.EdgeOwnership.pairInput u v) = true) :
    PEqualNP.EdgeOwnership.gateVal n C i
      (PEqualNP.EdgeOwnership.pairInput u v) = true := by
  cases hi : PEqualNP.EdgeOwnership.gateVal n C i
      (PEqualNP.EdgeOwnership.pairInput u v)
  · apply False.elim
    apply none u v edge
    refine ⟨hj, hand, active, ?_⟩
    intro k hk cone andk
    rw [sole k hk cone andk]
    exact hi
  · rfl

lemma dominated_single_ancestor_owns
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (minimal : IsMinimalMonoCircuit n C) (computes : circuitFun n C = graphFun G ∅)
    (i j : ℕ) (hij : i < j) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (sole : ∀ k < j, PEqualNP.EdgeOwnership.InCone n C k j →
      (gateAt C k).op = GateOp.and → k = i)
    (dominates : ∀ x : Fin n → Bool,
      PEqualNP.EdgeOwnership.gateVal n C i x = true →
      PEqualNP.EdgeOwnership.gateVal n C j x = true) :
    ∃ u v, G.Adj u v ∧ PEqualNP.EdgeOwnership.Owns n C j u v := by
  classical
  by_contra hn
  have none : ∀ u v, G.Adj u v → ¬ PEqualNP.EdgeOwnership.Owns n C j u v :=
    fun u v edge owned => hn ⟨u, v, edge, owned⟩
  let D := bypass n C j (n + i)
  have monoD : Monotone2 D := bypass_mono minimal.1
  have decreases (x : Fin n → Bool) :
      D.eval (List.ofFn x) = true → C.eval (List.ofFn x) = true := by
    exact bypass_eval_rel (R := fun a b => b = true → a = true)
      (fun _ => id) opMono_reverse (n := n) (C := C) (by simp)
      (mono_ops minimal.1) hj (Or.inl (by omega)) (dominates x)
  have preserves (u v : Fin n) (edge : G.Adj u v) :
      D.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) = true := by
    have values : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) (n + j) =
        val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) (n + i) := by
      apply Bool.eq_iff_iff.mpr
      exact ⟨no_owned_edge_forces_ancestor n G C i j hj hand sole none u v edge,
        dominates (PEqualNP.EdgeOwnership.pairInput u v)⟩
    have same := bypass_eval_eq (n := n) (C := C) (by simp) (mono_ops minimal.1)
      hj (Or.inl (by omega : n + i < n + j)) values
    change (bypass n C j (n + i)).eval _ = true
    rw [same]
    change circuitFun n C _ = true
    rw [computes]
    exact pair_true G u v edge
  have same : circuitFun n D = circuitFun n C := by
    funext x
    apply Bool.eq_iff_iff.mpr
    refine ⟨decreases x, ?_⟩
    intro hx
    have hgraph : graphFun G ∅ x = true := by rw [← computes]; exact hx
    obtain ⟨u, v, edge, hu, hv⟩ := (graph_true G x).mp hgraph
    apply circuit_monotone n D monoD (PEqualNP.EdgeOwnership.pairInput u v) x
      (fun k hk => ?_) (preserves u v edge)
    have hmem : k = u ∨ k = v := by simpa [PEqualNP.EdgeOwnership.pairInput] using hk
    rcases hmem with rfl | rfl
    · exact hu
    · exact hv
  have bound := minimal.2 D monoD same
  have smaller : D.size = C.gates.length - 1 := bypass_length n C j (n + i)
  change C.gates.length ≤ D.size at bound
  omega

def orLink (n : ℕ) (C : Circuit) (w v : ℕ) : Prop :=
  ∃ k < C.gates.length, w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    v ∈ (gateAt C k).inputs ∧ v < n + k

def orPath (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (orLink n C)

lemma orLink_active (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w v : ℕ)
    (link : orLink n C w v) : val C (List.ofFn x) v = true →
      val C (List.ofFn x) w = true := by
  obtain ⟨k, hk, rfl, hop, hv, hlt⟩ := link
  intro active
  exact (val_or (n := n) (by simp) hk hop).mpr ⟨v, hv, hlt, active⟩

lemma orPath_active (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w v : ℕ)
    (path : orPath n C w v) : val C (List.ofFn x) v = true →
      val C (List.ofFn x) w = true := by
  induction path with
  | refl => exact id
  | tail path link ih => exact fun active => ih (orLink_active n C x _ _ link active)

lemma shared_ancestor_in_all_sides_owns
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (minimal : IsMinimalMonoCircuit n C) (computes : circuitFun n C = graphFun G ∅)
    (i j : ℕ) (hij : i < j) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (sole : ∀ k < j, PEqualNP.EdgeOwnership.InCone n C k j →
      (gateAt C k).op = GateOp.and → k = i)
    (paths : ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ orPath n C w (n + i)) :
    ∃ u v, G.Adj u v ∧ PEqualNP.EdgeOwnership.Owns n C j u v := by
  apply dominated_single_ancestor_owns n G C minimal computes i j hij hj hand sole
  intro x active
  apply (val_and (n := n) (by simp) hj hand).mpr
  intro w hw
  obtain ⟨hlt, path⟩ := paths w hw
  exact ⟨hlt, orPath_active n C x w (n + i) path active⟩


lemma lost_edge (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hm : IsMinimalMonoCircuit n C) (hf : circuitFun n C = graphFun G ∅)
    (r : ℕ) (hr : r < C.gates.length) :
    ∃ p l : Fin n, G.Adj p l ∧
      (bypass n C r (n + C.gates.length)).eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput p l)) = false := by
  let D := bypass n C r (n + C.gates.length)
  have hD : Monotone2 D := bypass_mono hm.1
  have hle (x : Fin n → Bool) : D.eval (List.ofFn x) = true → C.eval (List.ofFn x) = true := by
    apply bypass_eval_rel (R := fun a b => b = true → a = true) (fun _ => id) opMono_reverse
      (n := n) (C := C) (by simp) (mono_ops hm.1) hr (Or.inr le_rfl)
    rw [val_ge (n := n) (by simp) le_rfl]
    intro h; cases h
  by_contra hn
  have hpairs (p l : Fin n) (hp : G.Adj p l) :
      D.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput p l)) = true := by
    cases h : D.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput p l))
    · exact (hn ⟨p, l, hp, h⟩).elim
    · rfl
  have heq : circuitFun n D = circuitFun n C := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hle x
    · intro hx
      have hx' : graphFun G ∅ x = true := by rw [← hf]; exact hx
      obtain ⟨p, l, hp, hpx, hlx⟩ := (graph_true G x).mp hx'
      apply circuit_monotone n D hD (PEqualNP.EdgeOwnership.pairInput p l) x
        (fun i hi => ?_) (hpairs p l hp)
      have hi' : i = p ∨ i = l := by simpa [PEqualNP.EdgeOwnership.pairInput] using hi
      rcases hi' with rfl | rfl
      · exact hpx
      · exact hlx
  have hsz := hm.2 D hD heq
  have hlen : D.size = C.gates.length - 1 := bypass_length n C r (n + C.gates.length)
  change C.gates.length ≤ D.size at hsz
  omega

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hm : IsMinimalMonoCircuit n C) (hf : circuitFun n C = graphFun G ∅)
    (r : ℕ) (hr : r < C.gates.length) (_hand : (gateAt C r).op = GateOp.and) :
    ∃ p l : Fin n, G.Adj p l ∧
      PEqualNP.EdgeOwnership.gateVal n C r (PEqualNP.EdgeOwnership.pairInput p l) = true ∧
      circuitFun n (PEqualNP.CircuitMoves.eraseGate n C r (n + C.gates.length))
        (PEqualNP.EdgeOwnership.pairInput p l) = false := by
  obtain ⟨p, l, hp, hlost⟩ := lost_edge n G C hm hf r hr
  have hC : C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput p l)) = true := by
    change circuitFun n C _ = true
    rw [hf]
    exact pair_true G p l hp
  refine ⟨p, l, hp, ?_, ?_⟩
  · cases hgate : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput p l)) (n + r)
    · have heq := bypass_eval_eq (n := n) (by simp) (mono_ops hm.1) hr
        (Or.inr (le_refl (n + C.gates.length)))
        (show val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput p l)) (n + r) =
          val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput p l)) (n + C.gates.length) by
            rw [hgate, val_ge (n := n) (by simp) le_rfl])
      rw [hlost, hC] at heq
      cases heq
    · exact hgate
  · rw [erase_eq_bypass n C r (n + C.gates.length) hr]
    exact hlost


open PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega
lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3
lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (i k : ℕ) (hik : InCone n C i k) :
    ∀ j, InCone n C k j → InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hkj
    obtain ⟨hj, r, hrj, hrin, hkr | hkr⟩ := (inCone_iff n C k j).mp hkj
    · subst r
      exact (inCone_iff n C i j).mpr ⟨hj, k, hrj, hrin, Or.inr hik⟩
    · exact (inCone_iff n C i j).mpr
        ⟨hj, r, hrj, hrin, Or.inr (ih r hrj hkr)⟩

lemma sole_ancestor_orPath (n : ℕ) (C : Circuit) (mono : Monotone2 C)
    (i j : ℕ) (hj : j < C.gates.length)
    (sole : ∀ k < j, InCone n C k j → (gateAt C k).op = GateOp.and → k = i) :
    ∀ k < j, InCone n C k j → (i = k ∨ InCone n C i k) →
      orPath n C (n + k) (n + i) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hkj hcone hreach
    rcases hreach with rfl | hreach
    · exact Relation.ReflTransGen.refl
    have hik := (inCone_lt n C i k hreach).1
    have hor : (gateAt C k).op = GateOp.or := by
      rcases mono_ops mono k (hkj.trans hj) with hand | hor
      · have heq := sole k hkj hcone hand
        omega
      · exact hor
    obtain ⟨_, t, htk, htin, hreach'⟩ := (inCone_iff n C i k).mp hreach
    have htkcone : InCone n C t k :=
      (inCone_iff n C t k).mpr ⟨hkj.trans hj, t, htk, htin, Or.inl rfl⟩
    have htjcone := inCone_trans n C t k htkcone j hcone
    have tail := ih t htk (htk.trans hkj) htjcone hreach'
    have link : orLink n C (n + k) (n + t) :=
      ⟨k, hkj.trans hj, rfl, hor, htin, by omega⟩
    exact (Relation.ReflTransGen.single link).trans tail

lemma unowned_single_ancestor_is_filter
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (minimal : IsMinimalMonoCircuit n C) (computes : circuitFun n C = graphFun G ∅)
    (i j : ℕ) (hij : i < j) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (sole : ∀ k < j, InCone n C k j → (gateAt C k).op = GateOp.and → k = i)
    (unowned : ∀ u v, G.Adj u v → ¬ Owns n C j u v) :
    (∀ w ∈ (gateAt C j).inputs, w < n + j) ∧
    (∃ w ∈ (gateAt C j).inputs, orPath n C w (n + i)) ∧
    (∃ w ∈ (gateAt C j).inputs, ¬ orPath n C w (n + i)) := by
  classical
  obtain ⟨u, v, edge, active, _⟩ := main n G C minimal computes j hj hand
  have back : ∀ w ∈ (gateAt C j).inputs, w < n + j := by
    intro w hw
    exact ((val_and (n := n) (by simp) hj hand).mp active w hw).1
  have ancestor : InCone n C i j := by
    by_contra absent
    apply unowned u v edge
    refine ⟨hj, hand, active, ?_⟩
    intro k hk cone andk
    have same := sole k hk cone andk
    exact (absent (same ▸ cone)).elim
  obtain ⟨_, k, hkj, hkin, hreach⟩ := (inCone_iff n C i j).mp ancestor
  have kcone : InCone n C k j :=
    (inCone_iff n C k j).mpr ⟨hj, k, hkj, hkin, Or.inl rfl⟩
  refine ⟨back, ⟨n + k, hkin, sole_ancestor_orPath n C minimal.1 i j hj sole k hkj kcone hreach⟩, ?_⟩
  by_contra allReach
  have paths : ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ orPath n C w (n + i) := by
    intro w hw
    exact ⟨back w hw, by_contra fun hn => allReach ⟨w, hw, hn⟩⟩
  obtain ⟨a, b, edge', own⟩ :=
    shared_ancestor_in_all_sides_owns n G C minimal computes i j hij hj hand sole paths
  exact unowned a b edge' own

end PEqualNP.Outside.L_meta_1772_aux.Dichotomy
