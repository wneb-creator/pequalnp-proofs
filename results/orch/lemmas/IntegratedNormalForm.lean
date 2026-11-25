import PEqualNP.Defs

-- Bypass helpers adapted from willakone, L-meta-1499, PR 3112.
namespace PEqualNP.Outside.L_meta_1772_aux.IntegratedNormalForm.Pivots

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


def replaceGate (C : Circuit) (j : ℕ) (g : Gate) : Circuit :=
  ⟨C.gates.set j g, C.output⟩

lemma replaceGate_length (C : Circuit) (j : ℕ) (g : Gate) :
    (replaceGate C j g).gates.length = C.gates.length := by
  simp [replaceGate]

lemma replaceGate_gateAt (C : Circuit) (j k : ℕ) (g : Gate)
    (hk : k < C.gates.length) :
    gateAt (replaceGate C j g) k = if k = j then g else gateAt C k := by
  rw [gateAt_eq (by simpa [replaceGate] using hk), gateAt_eq hk]
  change (C.gates.set j g)[k]'(by simpa using hk) = if k = j then g else C.gates[k]
  by_cases h : k = j
  · subst k
    simp
  · rw [List.getElem_set_of_ne (Ne.symm h), if_neg h]

lemma replaceGate_values (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate)
    (hj : j < C.gates.length) (x : Fin n → Bool)
    (agree : g.op.eval (g.inputs.map fun w =>
      if w < n + j then val C (List.ofFn x) w else false) =
        val C (List.ofFn x) (n + j)) :
    ∀ w, val (replaceGate C j g) (List.ofFn x) w = val C (List.ofFn x) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hinput : w < n
    · rw [val_input (n := n) (by simp) hinput, val_input (n := n) (by simp) hinput]
    by_cases hmissing : n + C.gates.length ≤ w
    · rw [val_ge (n := n) (by simp) (by simpa [replaceGate_length] using hmissing),
        val_ge (n := n) (by simp) hmissing]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rw [val_gate (n := n) (by simp) (by simpa [replaceGate_length] using hk),
      replaceGate_gateAt C j k g hk]
    have reads (ws : List ℕ) :
        (ws.map fun t => if t < n + k then val (replaceGate C j g) (List.ofFn x) t else false) =
        (ws.map fun t => if t < n + k then val C (List.ofFn x) t else false) := by
      apply List.map_congr_left
      intro t _
      by_cases ht : t < n + k
      · rw [if_pos ht, if_pos ht, ih t ht]
      · rw [if_neg ht, if_neg ht]
    by_cases hkj : k = j
    · subst k
      rw [if_pos rfl, reads]
      exact agree
    · rw [if_neg hkj, reads]
      exact (val_gate (n := n) (by simp) hk).symm

lemma replaceGate_mono (C : Circuit) (j : ℕ) (g : Gate) (mono : Monotone2 C)
    (newMono : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Monotone2 (replaceGate C j g) := by
  intro g' hg'
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hg'
  have hkC : k < C.gates.length := by simpa [replaceGate_length] using hk
  have heq' : gateAt (replaceGate C j g) k = g' := by rw [gateAt_eq hk, heq]
  rw [replaceGate_gateAt C j k g hkC] at heq'
  by_cases hkj : k = j
  · rw [if_pos hkj] at heq'
    exact heq' ▸ newMono
  · rw [if_neg hkj] at heq'
    exact heq' ▸ mono (gateAt C k) (gateAt_mem hkC)

lemma cone_mono_of_readers (n : ℕ) (C D : Circuit)
    (readers : ∀ j < D.gates.length, ∀ k < j,
      n + k ∈ (gateAt D j).inputs → InCone n C k j) :
    ∀ j i, InCone n D i j → InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro i cone
    obtain ⟨hj, k, hkj, hkin, hik | hik⟩ := (inCone_iff n D i j).mp cone
    · subst i
      exact readers j hj k hkj hkin
    · exact inCone_trans n C i k (ih k hkj i hik) j (readers j hj k hkj hkin)

lemma owns_of_cone_restriction (n : ℕ) (C D : Circuit)
    (lengths : C.gates.length = D.gates.length)
    (ops : ∀ j < C.gates.length, (gateAt D j).op = (gateAt C j).op)
    (values : ∀ (x : Fin n → Bool) w, val D (List.ofFn x) w = val C (List.ofFn x) w)
    (cones : ∀ j i, InCone n D i j → InCone n C i j) :
    ∀ j u v, Owns n C j u v → Owns n D j u v := by
  intro j u v own
  obtain ⟨hj, hand, active, first⟩ := own
  refine ⟨lengths ▸ hj, (ops j hj).trans hand, ?_, ?_⟩
  · change val D (List.ofFn (pairInput u v)) (n + j) = true
    rw [values]
    exact active
  · intro i hij cone andi
    change val D (List.ofFn (pairInput u v)) (n + i) = false
    rw [values]
    exact first i hij (cones j i cone) ((ops i (hij.trans hj)).symm.trans andi)

lemma replaceGate_decreases (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate)
    (mono : Monotone2 C) (newOp : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool)
    (dom : g.op.eval (g.inputs.map fun w =>
      if w < n + j then val C (List.ofFn x) w else false) = true →
        val C (List.ofFn x) (n + j) = true) :
    ∀ w, val (replaceGate C j g) (List.ofFn x) w = true → val C (List.ofFn x) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hinput : w < n
    · rw [val_input (n := n) (by simp) hinput, val_input (n := n) (by simp) hinput]
      exact id
    by_cases hmissing : n + C.gates.length ≤ w
    · rw [val_ge (n := n) (by simp) (by simpa [replaceGate_length] using hmissing)]
      simp
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rw [val_gate (n := n) (by simp) (by simpa [replaceGate_length] using hk),
      replaceGate_gateAt C j k g hk]
    have reads (ws : List ℕ) : ∀ t ∈ ws,
        (if t < n + k then val (replaceGate C j g) (List.ofFn x) t else false) = true →
        (if t < n + k then val C (List.ofFn x) t else false) = true := by
      intro t _
      by_cases ht : t < n + k
      · rw [if_pos ht, if_pos ht]
        exact ih t ht
      · rw [if_neg ht, if_neg ht]
        exact id
    by_cases hkj : k = j
    · subst k
      rw [if_pos rfl]
      exact fun h => dom (opMono_imp g.op newOp g.inputs _ _ (reads g.inputs) h)
    · rw [if_neg hkj, val_gate (n := n) (by simp) hk]
      exact opMono_imp _ (mono_ops mono k hk) _ _ _ (reads _)

lemma replaceGate_preserves_graph
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (mono : Monotone2 C) (computes : circuitFun n C = graphFun G ∅)
    (j : ℕ) (g : Gate) (hj : j < C.gates.length)
    (newMono : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (dom : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map fun w =>
      if w < n + j then val C (List.ofFn x) w else false) = true →
        val C (List.ofFn x) (n + j) = true)
    (agree : ∀ u v, G.Adj u v → g.op.eval (g.inputs.map fun w =>
      if w < n + j then val C (List.ofFn (pairInput u v)) w else false) =
        val C (List.ofFn (pairInput u v)) (n + j)) :
    circuitFun n (replaceGate C j g) = graphFun G ∅ := by
  let D := replaceGate C j g
  have monoD : Monotone2 D := replaceGate_mono C j g mono newMono
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hC := replaceGate_decreases n C j g mono newMono.1 x (dom x) C.output h
    change circuitFun n C x = true at hC
    simpa [computes] using hC
  · intro h
    obtain ⟨u, v, edge, hu, hv⟩ := (graph_true G x).mp h
    have pairC : circuitFun n C (pairInput u v) = true := by
      rw [computes]
      exact pair_true G u v edge
    have pairD : circuitFun n D (pairInput u v) = true := by
      change val D (List.ofFn (pairInput u v)) C.output = true
      rw [replaceGate_values n C j g hj (pairInput u v) (agree u v edge)]
      exact pairC
    apply circuit_monotone n D monoD (pairInput u v) x _ pairD
    intro t ht
    have cases : t = u ∨ t = v := by simpa [pairInput] using ht
    rcases cases with rfl | rfl
    · exact hu
    · exact hv

lemma owns_edges_of_cone_restriction
    (n : ℕ) (G : SimpleGraph (Fin n)) (C D : Circuit)
    (lengths : C.gates.length = D.gates.length)
    (ops : ∀ j < C.gates.length, (gateAt D j).op = (gateAt C j).op)
    (values : ∀ u v, G.Adj u v → ∀ w,
      val D (List.ofFn (pairInput u v)) w = val C (List.ofFn (pairInput u v)) w)
    (cones : ∀ j i, InCone n D i j → InCone n C i j) :
    ∀ j u v, G.Adj u v → Owns n C j u v → Owns n D j u v := by
  intro j u v edge own
  obtain ⟨hj, hand, active, first⟩ := own
  refine ⟨lengths ▸ hj, (ops j hj).trans hand, ?_, ?_⟩
  · change val D (List.ofFn (pairInput u v)) (n + j) = true
    rw [values u v edge]
    exact active
  · intro i hij cone andi
    change val D (List.ofFn (pairInput u v)) (n + i) = false
    rw [values u v edge]
    exact first i hij (cones j i cone) ((ops i (hij.trans hj)).symm.trans andi)
lemma replaceGate_values_outside_cone (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate)
    (x : Fin n → Bool) :
    ∀ w, (∀ k, w = n + k → k ≠ j ∧ ¬ InCone n C j k) →
      val (replaceGate C j g) (List.ofFn x) w = val C (List.ofFn x) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro outside
    by_cases hinput : w < n
    · rw [val_input (n := n) (by simp) hinput, val_input (n := n) (by simp) hinput]
    by_cases hmissing : n + C.gates.length ≤ w
    · rw [val_ge (n := n) (by simp) (by simpa [replaceGate_length] using hmissing),
        val_ge (n := n) (by simp) hmissing]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    obtain ⟨different, noCone⟩ := outside k rfl
    rw [val_gate (n := n) (by simp) (by simpa [replaceGate_length] using hk),
      replaceGate_gateAt C j k g hk, if_neg different, val_gate (n := n) (by simp) hk]
    congr 1
    apply List.map_congr_left
    intro t htin
    by_cases ht : t < n + k
    · rw [if_pos ht, if_pos ht]
      apply ih t ht
      intro r htr
      have hrk : r < k := by omega
      have direct : InCone n C r k :=
        (inCone_iff n C r k).mpr ⟨hk, r, hrk, htr ▸ htin, Or.inl rfl⟩
      constructor
      · intro same
        exact noCone (same ▸ direct)
      · intro cone
        exact noCone (inCone_trans n C j r cone k direct)
    · rw [if_neg ht, if_neg ht]

lemma replaceGate_gateVal_outside_cone
    (n : ℕ) (C : Circuit) (j k : ℕ) (g : Gate) (x : Fin n → Bool)
    (different : k ≠ j) (outside : ¬ InCone n C j k) :
    gateVal n (replaceGate C j g) k x = gateVal n C k x := by
  apply replaceGate_values_outside_cone n C j g x (n + k)
  intro r same
  have hr : r = k := by omega
  subst r
  exact ⟨different, outside⟩

lemma downward_and_preserves_other_owners
    (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate)
    (mono : Monotone2 C) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (newOp : g.op = GateOp.and ∨ g.op = GateOp.or)
    (dom : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map fun w =>
      if w < n + j then val C (List.ofFn x) w else false) = true →
        val C (List.ofFn x) (n + j) = true)
    (andCones : ∀ k i, InCone n (replaceGate C j g) i k →
      (gateAt (replaceGate C j g) i).op = GateOp.and → InCone n C i k) :
    ∀ k u v, k ≠ j → Owns n C k u v → Owns n (replaceGate C j g) k u v := by
  intro k u v different own
  obtain ⟨hk, andk, active, first⟩ := own
  refine ⟨by simpa [replaceGate_length] using hk, ?_, ?_, ?_⟩
  · rw [replaceGate_gateAt C j k g hk, if_neg different]
    exact andk
  · cases oldj : gateVal n C j (pairInput u v)
    · have agree : g.op.eval (g.inputs.map fun w =>
          if w < n + j then val C (List.ofFn (pairInput u v)) w else false) =
          val C (List.ofFn (pairInput u v)) (n + j) := by
        apply Bool.eq_iff_iff.mpr
        constructor
        · exact dom _
        · intro h
          change gateVal n C j (pairInput u v) = true at h
          rw [oldj] at h
          cases h
      change val (replaceGate C j g) (List.ofFn (pairInput u v)) (n + k) = true
      rw [replaceGate_values n C j g hj (pairInput u v) agree]
      exact active
    · have outside : ¬ InCone n C j k := by
        intro cone
        have hf := first j (inCone_lt n C j k cone).1 cone hand
        rw [oldj] at hf
        cases hf
      rw [replaceGate_gateVal_outside_cone n C j k g (pairInput u v) different outside]
      exact active
  · intro i hik cone andi
    have andiC : (gateAt C i).op = GateOp.and := by
      by_cases h : i = j
      · subst i
        exact hand
      · rw [replaceGate_gateAt C j i g (hik.trans hk), if_neg h] at andi
        exact andi
    have oldFalse := first i hik (andCones k i cone andi) andiC
    cases newi : gateVal n (replaceGate C j g) i (pairInput u v)
    · rfl
    · have oldTrue := replaceGate_decreases n C j g mono newOp (pairInput u v)
          (dom (pairInput u v)) (n + i) newi
      change gateVal n C i (pairInput u v) = true at oldTrue
      rw [oldFalse] at oldTrue
      cases oldTrue

lemma primary_replacement_cones
    (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate)
    (inputs : ∀ w ∈ g.inputs, w < n) :
    ∀ k i, InCone n (replaceGate C j g) i k → InCone n C i k := by
  apply cone_mono_of_readers n C (replaceGate C j g)
  intro k hk i hik hin
  have hkC : k < C.gates.length := by simpa [replaceGate_length] using hk
  rw [replaceGate_gateAt C j k g hkC] at hin
  split_ifs at hin with hkj
  · have bad := inputs (n + i) hin
    omega
  · exact (inCone_iff n C i k).mpr ⟨hkC, i, hik, hin, Or.inl rfl⟩

lemma downward_primary_preserves_other_owners
    (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate)
    (mono : Monotone2 C) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (newOp : g.op = GateOp.and ∨ g.op = GateOp.or)
    (inputs : ∀ w ∈ g.inputs, w < n)
    (dom : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map fun w =>
      if w < n + j then val C (List.ofFn x) w else false) = true →
        val C (List.ofFn x) (n + j) = true) :
    ∀ k u v, k ≠ j → Owns n C k u v → Owns n (replaceGate C j g) k u v := by
  apply downward_and_preserves_other_owners n C j g mono hj hand newOp dom
  intro k i cone _
  exact primary_replacement_cones n C j g inputs k i cone

lemma primary_and_eval (n : ℕ) (C : Circuit) (j : ℕ) (u v : Fin n) (x : Fin n → Bool) :
    GateOp.and.eval ([u.val, v.val].map fun w =>
      if w < n + j then val C (List.ofFn x) w else false) = (x u && x v) := by
  have hu : u.val < n + j := by omega
  have hv : v.val < n + j := by omega
  have readu : val C (List.ofFn x) u.val = x u := by
    rw [val_input (n := n) (by simp) u.isLt]
    simp [List.getD_eq_getElem?_getD]
  have readv : val C (List.ofFn x) v.val = x v := by
    rw [val_input (n := n) (by simp) v.isLt]
    simp [List.getD_eq_getElem?_getD]
  simp [GateOp.eval, hu, hv, readu, readv]

lemma singleton_edge_domination
    (n : ℕ) (C : Circuit) (mono : Monotone2 C) (j : ℕ) (u v : Fin n)
    (active : gateVal n C j (pairInput u v) = true) (x : Fin n → Bool) :
    GateOp.and.eval ([u.val, v.val].map fun w =>
      if w < n + j then val C (List.ofFn x) w else false) = true →
      val C (List.ofFn x) (n + j) = true := by
  rw [primary_and_eval]
  intro both
  have both' : x u = true ∧ x v = true := by simpa using both
  have hu := both'.1
  have hv := both'.2
  apply wire_monotone n C mono (pairInput u v) x _ (n + j) active
  intro t ht
  have cases : t = u ∨ t = v := by simpa [pairInput] using ht
  rcases cases with rfl | rfl
  · exact hu
  · exact hv


lemma primary_and_cones
    (n : ℕ) (C : Circuit) (j : ℕ) (u v : Fin n) (hj : j < C.gates.length) :
    (∀ r i, InCone n (replaceGate C j ⟨GateOp.and, [u.val, v.val]⟩) i r →
      InCone n C i r) ∧
    (∀ i, ¬ InCone n (replaceGate C j ⟨GateOp.and, [u.val, v.val]⟩) i j) := by
  let D := replaceGate C j ⟨GateOp.and, [u.val, v.val]⟩
  have absent : ∀ k, n + k ∉ (gateAt D j).inputs := by
    intro k h
    rw [replaceGate_gateAt C j j _ hj, if_pos rfl] at h
    change n + k ∈ [u.val, v.val] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h <;> omega
  constructor
  · apply cone_mono_of_readers n C D
    intro r hr k hkr hmem
    have hrC : r < C.gates.length := by simpa [D, replaceGate_length] using hr
    by_cases hrj : r = j
    · subst r
      exact (absent k hmem).elim
    · rw [replaceGate_gateAt C j r _ hrC, if_neg hrj] at hmem
      exact (inCone_iff n C k r).mpr ⟨hrC, k, hkr, hmem, Or.inl rfl⟩
  · intro i h
    obtain ⟨_, k, _, hmem, _⟩ := (inCone_iff n D i j).mp h
    exact absent k hmem


def badAndGates (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) : Set ℕ :=
  {j | j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
    ∀ u v, G.Adj u v → ¬ Owns n C j u v}

lemma badAndGates_finite (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) :
    (badAndGates n G C).Finite := by
  apply (Finset.range C.gates.length).finite_toSet.subset
  intro j hj
  simpa using hj.1

lemma badAndGates_strict_drop
    (n : ℕ) (G : SimpleGraph (Fin n)) (C D : Circuit)
    (lengths : D.gates.length = C.gates.length)
    (ops : ∀ k < C.gates.length, (gateAt D k).op = (gateAt C k).op)
    (preserve : ∀ k u v, G.Adj u v → Owns n C k u v → Owns n D k u v)
    (j : ℕ) (bad : j ∈ badAndGates n G C)
    (u v : Fin n) (edge : G.Adj u v) (newOwn : Owns n D j u v) :
    (badAndGates n G D).ncard < (badAndGates n G C).ncard := by
  apply Set.ncard_lt_ncard _ (badAndGates_finite n G C)
  refine ⟨?_, ?_⟩
  · intro k hk
    have hkC : k < C.gates.length := by rw [← lengths]; exact hk.1
    exact ⟨hkC, (ops k hkC).symm.trans hk.2.1,
      fun a b h own => hk.2.2 a b h (preserve k a b h own)⟩
  · intro reverse
    exact (reverse bad).2.2 u v edge newOwn

def disabled (C : Circuit) (j : ℕ) : Circuit := replaceGate C j ⟨GateOp.or, []⟩

lemma disabled_after_replacement (C : Circuit) (j : ℕ) (g : Gate) :
    disabled (replaceGate C j g) j = disabled C j := by
  simp [disabled, replaceGate]

lemma disabled_below_replacement (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate)
    (mono : Monotone2 (replaceGate C j g)) (x : Fin n → Bool) :
    circuitFun n (disabled C j) x = true → circuitFun n (replaceGate C j g) x = true := by
  have h := replaceGate_decreases n (replaceGate C j g) j ⟨GateOp.or, []⟩ mono
    (Or.inr rfl) x (by simp [GateOp.eval]) C.output
  change val (disabled (replaceGate C j g) j) (List.ofFn x) C.output = true →
    val (replaceGate C j g) (List.ofFn x) C.output = true at h
  rw [disabled_after_replacement] at h
  exact h

lemma bypass_after_replacement (n : ℕ) (C : Circuit) (j i : ℕ) (g : Gate) :
    bypass n (replaceGate C j g) j i = bypass n C j i := by
  unfold bypass
  have lengths := replaceGate_length C j g
  rw [lengths]
  change Circuit.mk _ (aliasWire (n + j) i C.output) = Circuit.mk _ _
  congr 1
  apply List.map_congr_left
  intro k hk
  have hklen : k < C.gates.length - 1 := by simpa using hk
  by_cases hkj : k < j
  · rw [if_pos hkj, if_pos hkj, replaceGate_gateAt C j k g (by omega), if_neg (by omega)]
  · rw [if_neg hkj, if_neg hkj,
      replaceGate_gateAt C j (k + 1) g (by omega), if_neg (by omega)]

lemma disabled_eq_bypass (n : ℕ) (C : Circuit) (mono : Monotone2 C)
    (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    circuitFun n (disabled C j) x =
      (bypass n C j (n + C.gates.length)).eval (List.ofFn x) := by
  have monoZ : Monotone2 (disabled C j) := replaceGate_mono C j _ mono (by simp)
  have hjZ : j < (disabled C j).gates.length := by simpa [disabled, replaceGate_length] using hj
  have newGate : gateAt (disabled C j) j = ⟨GateOp.or, []⟩ := by
    unfold disabled
    rw [replaceGate_gateAt C j j _ hj, if_pos rfl]
  have gateZero : val (disabled C j) (List.ofFn x) (n + j) = false := by
    rw [val_gate (n := n) (by simp) hjZ, newGate]
    simp [GateOp.eval]
  have missing : val (disabled C j) (List.ofFn x) (n + C.gates.length) = false :=
    val_ge (n := n) (by simp) (by simp [disabled, replaceGate_length])
  have same := bypass_eval_eq (n := n) (C := disabled C j) (by simp) (mono_ops monoZ)
    hjZ (Or.inr (by simp [disabled, replaceGate_length])) (gateZero.trans missing.symm)
  have bypassSame := bypass_after_replacement n C j (n + C.gates.length) ⟨GateOp.or, []⟩
  change bypass n (disabled C j) j (n + C.gates.length) = _ at bypassSame
  rw [bypassSame] at same
  exact same.symm

lemma pivotal_edge_exists
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (minimal : IsMinimalMonoCircuit n C) (computes : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) :
    ∃ u v, G.Adj u v ∧ gateVal n C j (pairInput u v) = true ∧
      circuitFun n (disabled C j) (pairInput u v) = false := by
  obtain ⟨u, v, edge, active, erased⟩ := main n G C minimal computes j hj hand
  rw [erase_eq_bypass n C j (n + C.gates.length) hj] at erased
  exact ⟨u, v, edge, active, (disabled_eq_bypass n C minimal.1 j hj _).trans erased⟩

lemma singleton_pivotal_exchange
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (minimal : IsMinimalMonoCircuit n C) (computes : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (andj : (gateAt C j).op = GateOp.and)
    (u v : Fin n) (edge : G.Adj u v) (active : gateVal n C j (pairInput u v) = true)
    (onlyPivotal : ∀ a b, G.Adj a b → circuitFun n (disabled C j) (pairInput a b) = false →
      (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.gates.length = C.gates.length ∧
      (∀ k < C.gates.length, (gateAt D k).op = (gateAt C k).op) ∧
      (∀ k a b, k ≠ j → Owns n C k a b → Owns n D k a b) ∧
      D = replaceGate C j ⟨GateOp.and, [u.val, v.val]⟩ ∧ Owns n D j u v := by
  let g : Gate := ⟨GateOp.and, [u.val, v.val]⟩
  let D := replaceGate C j g
  have lengthD : D.gates.length = C.gates.length := replaceGate_length C j g
  have monoD : Monotone2 D := replaceGate_mono C j g minimal.1 (by simp [g])
  have dom := singleton_edge_domination n C minimal.1 j u v active
  have pairCorrect (a b : Fin n) (hab : G.Adj a b) :
      circuitFun n D (pairInput a b) = true := by
    cases zeroVal : circuitFun n (disabled C j) (pairInput a b)
    · have pairEqual : pairInput a b = pairInput u v := by
        rcases onlyPivotal a b hab zeroVal with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · funext t
          simp [pairInput, or_comm]
      rw [pairEqual]
      have agree : g.op.eval (g.inputs.map fun w =>
          if w < n + j then val C (List.ofFn (pairInput u v)) w else false) =
          val C (List.ofFn (pairInput u v)) (n + j) := by
        change GateOp.and.eval _ = _
        rw [primary_and_eval]
        change _ = gateVal n C j (pairInput u v)
        rw [active]
        simp [pairInput]
      change val D (List.ofFn (pairInput u v)) C.output = true
      rw [replaceGate_values n C j g hj (pairInput u v) agree]
      change circuitFun n C (pairInput u v) = true
      rw [computes]
      exact pair_true G u v edge
    · exact disabled_below_replacement n C j g monoD _ zeroVal
  have computesD : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have oldTrue := replaceGate_decreases n C j g minimal.1 (Or.inl rfl) x (dom x) C.output hx
      change circuitFun n C x = true at oldTrue
      simpa [computes] using oldTrue
    · intro hx
      obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G x).mp hx
      apply circuit_monotone n D monoD (pairInput a b) x _ (pairCorrect a b hab)
      intro t ht
      have cases : t = a ∨ t = b := by simpa [pairInput] using ht
      rcases cases with rfl | rfl
      · exact ha
      · exact hb
  have sizeD : D.size = C.size := lengthD
  have minimalD : IsMinimalMonoCircuit n D := by
    refine ⟨monoD, fun E hE hfun => ?_⟩
    rw [sizeD]
    exact minimal.2 E hE (hfun.trans (computesD.trans computes.symm))
  have ops : ∀ k < C.gates.length, (gateAt D k).op = (gateAt C k).op := by
    intro k hk
    rw [replaceGate_gateAt C j k g hk]
    by_cases hkj : k = j
    · subst k
      simpa [g] using andj.symm
    · rw [if_neg hkj]
  have preserve := downward_primary_preserves_other_owners n C j g minimal.1 hj andj
    (Or.inl rfl) (by simp [g]) dom
  refine ⟨D, minimalD, computesD, lengthD, ops, preserve, rfl,
    by omega, (ops j hj).trans andj, ?_, ?_⟩
  · change val D (List.ofFn (pairInput u v)) (n + j) = true
    rw [val_gate (n := n) (by simp) (by omega), replaceGate_gateAt C j j g hj, if_pos rfl]
    change GateOp.and.eval _ = true
    rw [primary_and_eval]
    simp [pairInput]
  · intro i _ cone _
    exact ((primary_and_cones n C j u v hj).2 i cone).elim

lemma singleton_pivotal_repair
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (minimal : IsMinimalMonoCircuit n C) (computes : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (andj : (gateAt C j).op = GateOp.and)
    (unowned : ∀ a b, G.Adj a b → ¬ Owns n C j a b)
    (u v : Fin n) (edge : G.Adj u v) (active : gateVal n C j (pairInput u v) = true)
    (onlyPivotal : ∀ a b, G.Adj a b → circuitFun n (disabled C j) (pairInput a b) = false →
      (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size = C.size ∧ (badAndGates n G D).ncard < (badAndGates n G C).ncard := by
  obtain ⟨D, hmin, hfun, hlen, hops, hpres, _, hown⟩ :=
    singleton_pivotal_exchange n G C minimal computes j hj andj u v edge active onlyPivotal
  have preserve : ∀ k a b, G.Adj a b → Owns n C k a b → Owns n D k a b := by
    intro k a b hab own
    have different : k ≠ j := by
      rintro rfl
      exact unowned a b hab own
    exact hpres k a b different own
  exact ⟨D, hmin, hfun, hlen,
    badAndGates_strict_drop n G C D hlen hops preserve j ⟨hj, andj, unowned⟩ u v edge hown⟩

open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma primary_edge_dirty_subset
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (mono : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (u v : Fin n) (edge : G.Adj u v) (active : gateVal n C j (pairInput u v) = true) :
    junk G (replaceGate C j ⟨GateOp.and, [u.val, v.val]⟩) ⊆ (junk G C).erase j := by
  intro k hk
  obtain ⟨hkRange, andk, _, x, hkTrue, graphFalse⟩ := Finset.mem_filter.mp hk
  have hkC : k < C.gates.length := by
    simpa [gatesWhere, replaceGate_length] using hkRange
  have different : k ≠ j := by
    rintro rfl
    change val (replaceGate C k ⟨GateOp.and, [u.val, v.val]⟩) (List.ofFn x) (n + k) = true at hkTrue
    rw [val_gate (n := n) (by simp) (by simpa [replaceGate_length] using hkC),
      replaceGate_gateAt C k k _ hkC, if_pos rfl] at hkTrue
    change GateOp.and.eval _ = true at hkTrue
    rw [primary_and_eval] at hkTrue
    have endpoints : x u = true ∧ x v = true := by simpa using hkTrue
    have graphTrue := (graph_true G x).mpr ⟨u, v, edge, endpoints.1, endpoints.2⟩
    rw [graphFalse] at graphTrue
    cases graphTrue
  have oldAnd : (gateAt C k).op = GateOp.and := by
    rw [replaceGate_gateAt C j k _ hkC, if_neg different] at andk
    exact andk
  have oldTrue := replaceGate_decreases n C j ⟨GateOp.and, [u.val, v.val]⟩ mono
    (Or.inl rfl) x (singleton_edge_domination n C mono j u v active x) (n + k) hkTrue
  exact Finset.mem_erase.mpr ⟨different, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hkC, oldAnd, hkC, x, oldTrue, graphFalse⟩⟩

lemma badAndGates_le_of_preserved_other_owners
    (n : ℕ) (G : SimpleGraph (Fin n)) (C D : Circuit)
    (lengths : D.gates.length = C.gates.length)
    (ops : ∀ k < C.gates.length, (gateAt D k).op = (gateAt C k).op)
    (j : ℕ) (preserve : ∀ k u v, k ≠ j → Owns n C k u v → Owns n D k u v)
    (u v : Fin n) (edge : G.Adj u v) (newOwn : Owns n D j u v) :
    (badAndGates n G D).ncard ≤ (badAndGates n G C).ncard := by
  apply Set.ncard_le_ncard _ (badAndGates_finite n G C)
  intro k hk
  have hkC : k < C.gates.length := by rw [← lengths]; exact hk.1
  have different : k ≠ j := by
    rintro rfl
    exact hk.2.2 u v edge newOwn
  exact ⟨hkC, (ops k hkC).symm.trans hk.2.1,
    fun a b hab own => hk.2.2 a b hab (preserve k a b different own)⟩

lemma singleton_pivotal_controlled
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (minimal : IsMinimalMonoCircuit n C) (computes : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (andj : (gateAt C j).op = GateOp.and)
    (u v : Fin n) (edge : G.Adj u v) (active : gateVal n C j (pairInput u v) = true)
    (onlyPivotal : ∀ a b, G.Adj a b → circuitFun n (disabled C j) (pairInput a b) = false →
      (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size = C.size ∧ (junk G D).card ≤ (junk G C).card ∧
      (j ∈ junk G C → (junk G D).card < (junk G C).card) ∧
      (badAndGates n G D).ncard ≤ (badAndGates n G C).ncard ∧
      ((∀ a b, G.Adj a b → ¬ Owns n C j a b) →
        (badAndGates n G D).ncard < (badAndGates n G C).ncard) := by
  obtain ⟨D, minimumD, computesD, lengths, ops, preserve, exactD, newOwn⟩ :=
    singleton_pivotal_exchange n G C minimal computes j hj andj u v edge active onlyPivotal
  have dirtySub : junk G D ⊆ (junk G C).erase j := by
    rw [exactD]
    exact primary_edge_dirty_subset n G C minimal.1 j hj u v edge active
  have dirtyLe : (junk G D).card ≤ ((junk G C).erase j).card := Finset.card_le_card dirtySub
  have cardErase := Finset.card_le_card (Finset.erase_subset (s := junk G C) j)
  refine ⟨D, minimumD, computesD, lengths, dirtyLe.trans cardErase, ?_,
    badAndGates_le_of_preserved_other_owners n G C D lengths ops j preserve u v edge newOwn, ?_⟩
  · intro dirty
    have card := Finset.card_erase_add_one dirty
    omega
  · intro unowned
    apply badAndGates_strict_drop n G C D lengths ops _ j ⟨hj, andj, unowned⟩ u v edge newOwn
    intro k a b hab own
    apply preserve k a b _ own
    rintro rfl
    exact unowned a b hab own

lemma andPairs_le_of_cone_restriction
    (n : ℕ) (C D : Circuit)
    (lengths : D.gates.length = C.gates.length)
    (ops : ∀ k < C.gates.length, (gateAt D k).op = GateOp.and →
      (gateAt C k).op = GateOp.and)
    (cones : ∀ i j, InCone n D i j → InCone n C i j) :
    andPairs n D ≤ andPairs n C := by
  letI : DecidableEq GateOp := gateOpDecEq
  unfold andPairs
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hprod, hi, hj, hcone⟩ := Finset.mem_filter.mp hp
  have hprodC : p ∈ Finset.range C.gates.length ×ˢ Finset.range C.gates.length := by
    simpa only [lengths] using hprod
  obtain ⟨hpi, hpj⟩ := Finset.mem_product.mp hprodC
  exact Finset.mem_filter.mpr ⟨hprodC,
    ops p.1 (Finset.mem_range.mp hpi) hi,
    ops p.2 (Finset.mem_range.mp hpj) hj, cones p.1 p.2 hcone⟩

lemma primary_edge_andPairs_le
    (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (andj : (gateAt C j).op = GateOp.and) (u v : Fin n) :
    andPairs n (replaceGate C j ⟨GateOp.and, [u.val, v.val]⟩) ≤ andPairs n C := by
  apply andPairs_le_of_cone_restriction n C _ (replaceGate_length C j _)
  · intro k hk hand
    by_cases hkj : k = j
    · subst k
      exact andj
    · rw [replaceGate_gateAt C j k _ hk, if_neg hkj] at hand
      exact hand
  · intro i k hcone
    exact (primary_and_cones n C j u v hj).1 k i hcone

lemma singleton_pivotal_all_measures
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (minimal : IsMinimalMonoCircuit n C) (computes : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (andj : (gateAt C j).op = GateOp.and)
    (u v : Fin n) (edge : G.Adj u v) (active : gateVal n C j (pairInput u v) = true)
    (onlyPivotal : ∀ a b, G.Adj a b → circuitFun n (disabled C j) (pairInput a b) = false →
      (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size = C.size ∧ (junk G D).card ≤ (junk G C).card ∧
      andPairs n D ≤ andPairs n C ∧
      (j ∈ junk G C → (junk G D).card < (junk G C).card) ∧
      (badAndGates n G D).ncard ≤ (badAndGates n G C).ncard ∧
      ((∀ a b, G.Adj a b → ¬ Owns n C j a b) →
        (badAndGates n G D).ncard < (badAndGates n G C).ncard) := by
  obtain ⟨D, minimumD, computesD, lengths, ops, preserve, exactD, newOwn⟩ :=
    singleton_pivotal_exchange n G C minimal computes j hj andj u v edge active onlyPivotal
  have dirtySub : junk G D ⊆ (junk G C).erase j := by
    rw [exactD]
    exact primary_edge_dirty_subset n G C minimal.1 j hj u v edge active
  have dirtyLe : (junk G D).card ≤ ((junk G C).erase j).card := Finset.card_le_card dirtySub
  have cardErase := Finset.card_le_card (Finset.erase_subset (s := junk G C) j)
  have pairsLe : andPairs n D ≤ andPairs n C := by
    rw [exactD]
    exact primary_edge_andPairs_le n C j hj andj u v
  refine ⟨D, minimumD, computesD, lengths, dirtyLe.trans cardErase, pairsLe, ?_,
    badAndGates_le_of_preserved_other_owners n G C D lengths ops j preserve u v edge newOwn, ?_⟩
  · intro dirty
    have card := Finset.card_erase_add_one dirty
    omega
  · intro unowned
    apply badAndGates_strict_drop n G C D lengths ops _ j ⟨hj, andj, unowned⟩ u v edge newOwn
    intro k a b hab own
    apply preserve k a b _ own
    rintro rfl
    exact unowned a b hab own

end PEqualNP.Outside.L_meta_1772_aux.IntegratedNormalForm.Pivots



-- Bypass helpers adapted from willakone, L-meta-1499, PR 3112.
namespace PEqualNP.Outside.L_meta_1772_aux.IntegratedNormalForm.Model

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
    (r : ℕ) (hr : r < C.gates.length) :
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

lemma no_copy_to_earlier (n : ℕ) (C : Circuit) (minimal : IsMinimalMonoCircuit n C)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r)
    (same : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = val C (List.ofFn x) i) : False := by
  let D := bypass n C r i
  have monoD : Monotone2 D := bypass_mono minimal.1
  have equal : circuitFun n D = circuitFun n C := by
    funext x
    exact bypass_eval_eq (n := n) (by simp) (mono_ops minimal.1) hr (Or.inl hi) (same x)
  have bound := minimal.2 D monoD equal
  have lengthD : D.size = C.gates.length - 1 := bypass_length n C r i
  change C.gates.length ≤ D.size at bound
  omega

lemma minimum_gate_shape
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (minimal : IsMinimalMonoCircuit n C) (computes : circuitFun n C = graphFun G ∅)
    (r : ℕ) (hr : r < C.gates.length) :
    (∃ a b, (gateAt C r).inputs = [a, b] ∧ a < n + r ∧ b < n + r) ∨
      ((gateAt C r).op = GateOp.and ∧ (gateAt C r).inputs = []) := by
  have mono := minimal.1 (gateAt C r) (gateAt_mem hr)
  have ops := mono_ops minimal.1 r hr
  obtain ⟨u, v, _, active, _⟩ := main n G C minimal computes r hr
  rcases hins : (gateAt C r).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases ops with hand | hor
    · exact Or.inr ⟨hand, rfl⟩
    · have h := (val_or (n := n) (by simp) hr hor).mp active
      simpa [hins] using h
  · have ha : a < n + r := by
      rcases ops with hand | hor
      · exact ((val_and (n := n) (by simp) hr hand).mp active a (by simp [hins])).1
      · obtain ⟨w, hw, hwlt, _⟩ := (val_or (n := n) (by simp) hr hor).mp active
        have hw' : w = a := by simpa [hins] using hw
        simpa [hw'] using hwlt
    apply False.elim
    apply no_copy_to_earlier n C minimal r a hr ha
    intro x
    rw [val_gate (n := n) (by simp) hr, hins]
    rcases ops with hand | hor
    · simp [hand, GateOp.eval, ha]
    · simp [hor, GateOp.eval, ha]
  · rcases ops with hand | hor
    · have all := (val_and (n := n) (by simp) hr hand).mp active
      exact Or.inl ⟨a, b, rfl, (all a (by simp [hins])).1, (all b (by simp [hins])).1⟩
    · by_cases ha : a < n + r
      · by_cases hb : b < n + r
        · exact Or.inl ⟨a, b, rfl, ha, hb⟩
        · apply False.elim
          apply no_copy_to_earlier n C minimal r a hr ha
          intro x
          rw [val_gate (n := n) (by simp) hr, hins, hor]
          simp [GateOp.eval, ha, hb]
      · have hb : b < n + r := by
          obtain ⟨w, hw, hwlt, _⟩ := (val_or (n := n) (by simp) hr hor).mp active
          have hw' : w = a ∨ w = b := by simpa [hins] using hw
          rcases hw' with rfl | rfl
          · exact (ha hwlt).elim
          · exact hwlt
        apply False.elim
        apply no_copy_to_earlier n C minimal r b hr hb
        intro x
        rw [val_gate (n := n) (by simp) hr, hins, hor]
        simp [GateOp.eval, ha, hb]
  · have len := mono.2
    rw [hins] at len
    simp only [List.length_cons] at len
    omega

lemma minimum_no_constant_true
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (minimal : IsMinimalMonoCircuit n C) (computes : circuitFun n C = graphFun G ∅) :
    ∀ i < C.gates.length, ¬ (∀ x : Fin n → Bool, gateVal n C i x = true) := by
  classical
  intro i hi always
  let T := (Finset.range C.gates.length).filter fun k =>
    ∀ x : Fin n → Bool, gateVal n C k x = true
  have nonempty : T.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, always⟩⟩
  let k := T.max' nonempty
  have kmem : k ∈ T := Finset.max'_mem T nonempty
  have hk : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp kmem).1
  have ktrue : ∀ x : Fin n → Bool, gateVal n C k x = true := (Finset.mem_filter.mp kmem).2
  have outputDifferent : C.output ≠ n + k := by
    intro equal
    have outputTrue : circuitFun n C (fun _ => false) = true := by
      change val C (List.ofFn (fun _ => false)) C.output = true
      rw [equal]
      exact ktrue (fun _ => false)
    rw [computes] at outputTrue
    simpa [graphFun] using outputTrue
  have noReaders : ∀ r, k < r → r < C.gates.length → n + k ∉ (gateAt C r).inputs := by
    intro r hkr hr reader
    rcases minimum_gate_shape n G C minimal computes r hr with ⟨a, b, inputs, ha, hb⟩ | ⟨_, empty⟩
    · rcases mono_ops minimal.1 r hr with hand | hor
      · have atSide : n + k = a ∨ n + k = b := by simpa [inputs] using reader
        rcases atSide with eqA | eqB
        · apply no_copy_to_earlier n C minimal r b hr hb
          intro x
          rw [val_gate (n := n) (by simp) hr, hand, inputs]
          have kt : val C (List.ofFn x) a = true := by rw [← eqA]; exact ktrue x
          simp [GateOp.eval, ha, hb, kt]
        · apply no_copy_to_earlier n C minimal r a hr ha
          intro x
          rw [val_gate (n := n) (by simp) hr, hand, inputs]
          have kt : val C (List.ofFn x) b = true := by rw [← eqB]; exact ktrue x
          simp [GateOp.eval, ha, hb, kt]
      · have rtrue : ∀ x : Fin n → Bool, gateVal n C r x = true := by
          intro x
          exact (val_or (n := n) (by simp) hr hor).mpr ⟨n + k, reader, by omega, ktrue x⟩
        have rmem : r ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, rtrue⟩
        have bound : r ≤ k := Finset.le_max' T r rmem
        omega
    · simpa [empty] using reader
  obtain ⟨u, v, edge, lost⟩ := lost_edge n G C minimal computes k hk
  have same := bypass_eval_unread (n := n) (by simp) (mono_ops minimal.1) hk
    (Or.inr (le_refl (n + C.gates.length))) outputDifferent noReaders
    (x := List.ofFn (pairInput u v))
  have oldTrue : C.eval (List.ofFn (pairInput u v)) = true := by
    change circuitFun n C (pairInput u v) = true
    rw [computes]
    exact pair_true G u v edge
  rw [lost, oldTrue] at same
  cases same

lemma minimal_isAO2
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (minimal : IsMinimalMonoCircuit n C) (computes : circuitFun n C = graphFun G ∅) :
    PEqualNP.TopForm.IsAO2 n C := by
  have shape (r : ℕ) (hr : r < C.gates.length) :
      ∃ a b, (gateAt C r).inputs = [a, b] ∧ a < n + r ∧ b < n + r := by
    rcases minimum_gate_shape n G C minimal computes r hr with pair | ⟨hand, empty⟩
    · exact pair
    · apply False.elim
      apply minimum_no_constant_true n G C minimal computes r hr
      intro x
      change val C (List.ofFn x) (n + r) = true
      rw [val_gate (n := n) (by simp) hr, hand, empty]
      simp [GateOp.eval]
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact (minimal.1 g hg).1
  · intro r hr w hw
    obtain ⟨a, b, inputs, ha, hb⟩ := shape r hr
    have sides : w = a ∨ w = b := by simpa [inputs] using hw
    exact sides.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
  · intro g hg
    obtain ⟨r, hr, equal⟩ := List.mem_iff_getElem.mp hg
    have same : gateAt C r = g := by rw [gateAt_eq hr, equal]
    obtain ⟨a, b, inputs, _, _⟩ := shape r hr
    rw [← same, inputs]
    rfl

lemma minimal_isLeastAO
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (minimal : IsMinimalMonoCircuit n C) (computes : circuitFun n C = graphFun G ∅) :
    PEqualNP.TopForm.IsLeastAO G C := by
  refine ⟨minimal_isAO2 n G C minimal computes, computes, ?_⟩
  intro D hD correctD
  have monoD : Monotone2 D := by
    intro g hg
    refine ⟨hD.1 g hg, ?_⟩
    rw [hD.2.2 g hg]
  exact minimal.2 D monoD (correctD.trans computes.symm)

end PEqualNP.Outside.L_meta_1772_aux.IntegratedNormalForm.Model


-- TopForm extraction adapted from the checked L-meta-1733 A1501 proof.
namespace PEqualNP.Outside.L_meta_1772_aux.IntegratedNormalForm.Extraction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

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

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [if_neg (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO2 n C ∧ ∀ D : Circuit, AO2 n D → (∀ x, wv n D x D.output = wv n C x C.output) →
    C.gates.length ≤ D.gates.length

lemma reader_or (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hle := hL.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hL hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hL hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hle := hL.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [if_pos h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [if_pos h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [if_neg h1] at hwk
        by_cases h2 : w = n + r
        · rw [if_pos h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [if_neg h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [if_neg (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [if_pos h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [if_neg h1] at hwk
    by_cases h2 : w = n + r
    · rw [if_pos h2] at hwk
      exact hci hwk
    · rw [if_neg h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin


lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [if_pos h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [if_neg (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma step3_core (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hL hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hL hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (reader_unique n C hL hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma least_of_same (n : ℕ) (C D : Circuit) (hL : Least n C) (hD : AO2 n D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) : Least n D :=
  ⟨hD, fun E hE hEf => by rw [hlen]; exact hL.2 E hE (fun x => (hEf x).trans (hfun x))⟩

lemma V2_gateval (n : ℕ) (C : Circuit) (r c i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    wv n (V2 n C r c i) x (n + k') = wv n C x (n + rho r k') := by
  have h := V2_same n C r c i x hC hr hb hi hout h0 (n + rho r k')
    (by have := rho_lt r k' _ hr hk'; omega)
  rw [tau_rho] at h
  exact h

lemma V2_below (n : ℕ) (C : Circuit) (r c i : ℕ) (F : (Fin n → Bool) → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbelF : ∀ x, wv n C x (n + i) = true → F x = true)
    (h0 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    (∀ x, wv n (V2 n C r c i) x (n + k') = true → F x = true) ↔
      (∀ x, wv n C x (n + rho r k') = true → F x = true) := by
  constructor
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [← V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv


lemma card_filter_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q]
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    ((Finset.range m).filter Q).card = ((Finset.range m).filter P).card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [Finset.mem_filter, Finset.mem_range] at hk' ⊢
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩


lemma step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : Least n C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i, r, hr, hir, least_of_same n C _ hL hD hfun (V2_len n C r c i),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [if_pos hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma card_mem_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < m ∧ P k) (hS' : ∀ k, k ∈ S' ↔ k < m ∧ Q k)
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    S'.card = S.card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [hS'] at hk'
    rw [hS]
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [hS] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [hS']
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma junk_eq (n : ℕ) (C C' : Circuit) (F : (Fin n → Bool) → Bool) (r : ℕ)
    (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or)
    (hbelow : ∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true)))
    (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)
    (hS' : ∀ k, k ∈ S' ↔ k < C'.gates.length ∧ (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true) :
    S'.card = S.card := by
  rw [hlen] at hS'
  apply card_mem_rho C.gates.length r hr _ _ S S' hS hS'
  · intro k' hk'
    rw [hops k' hk', hbelow k' hk']
  · rintro ⟨h, _⟩
    rw [hopr] at h
    exact absurd h (by simp)
  · rintro ⟨h, _⟩
    rw [htop] at h
    exact absurd h (by simp)


lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma mem_gateAt (C : Circuit) (g : Gate) (hg : g ∈ C.gates) :
    ∃ j, j < C.gates.length ∧ gateAt C j = g := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  exact ⟨j, hj, by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]⟩


lemma ao2_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro j hj
  have hm := gateAt_mem C j hj
  exact ⟨h1 _ hm, List.length_eq_two.mp (h3 _ hm), h2 j hj⟩

lemma ao2_to (n : ℕ) (C : Circuit) (h : AO2 n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    exact (h j hj).1
  · intro j hj
    exact (h j hj).2.2
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    obtain ⟨a, b, hab⟩ := (h j hj).2.1
    rw [hab]
    rfl

lemma least_glue (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : PEqualNP.TopForm.IsLeastAO G C) :
    Least n C ∧ ∀ x, wv n C x C.output = graphFun G ∅ x := by
  obtain ⟨h1, h2, h3⟩ := hL
  have hF : ∀ x, wv n C x C.output = graphFun G ∅ x := fun x => congrFun h2 x
  refine ⟨⟨ao2_of n C h1, ?_⟩, hF⟩
  intro D hD hDf
  exact h3 D (ao2_to n D hD) (funext fun x => (hDf x).trans (hF x))

lemma least_glue' (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : Least n C) (hF : ∀ x, wv n C x C.output = graphFun G ∅ x) :
    PEqualNP.TopForm.IsLeastAO G C := by
  refine ⟨ao2_to n C hL.1, funext hF, ?_⟩
  intro D hD hDf
  exact hL.2 D (ao2_of n D hD) (fun x => (congrFun hDf x).trans (hF x).symm)

lemma exists_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  refine ⟨fun _ => true, ?_⟩
  obtain ⟨e, he⟩ := hG
  rw [SimpleGraph.mem_edgeFinset] at he
  revert he
  refine Sym2.inductionOn e ?_
  intro u v he
  have hadj : G.Adj u v := he
  unfold graphFun
  have hd : decide (∃ u v, G.Adj u v ∧ (fun _ : Fin n => true) u = true ∧
      (fun _ : Fin n => true) v = true) = true := decide_eq_true ⟨u, v, hadj, rfl, rfl⟩
  rw [hd]
  simp

lemma mem_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → graphFun G ∅ x = true := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hne
    apply h3
    intro x hx
    by_contra hF
    exact hne ⟨x, hx, by simpa using hF⟩

open Classical in
lemma main_ind (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) :
    ∀ k : ℕ, ∀ C : Circuit, PEqualNP.TopForm.IsLeastAO G C →
      ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
          (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card = k →
      ∃ C' : Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
        (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
        PEqualNP.TopForm.TopForm G C' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hC hk
    by_cases htop : PEqualNP.TopForm.TopForm G C
    · exact ⟨C, hC, rfl, rfl, htop⟩
    · have hex : ∃ i j, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧ PEqualNP.TopForm.BelowF G C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone n C i j := by
        by_contra hne
        apply htop
        intro i hi j hj h1 h2 h3 h4
        exact hne ⟨i, j, hi, hj, h1, h2, h3, h4⟩
      obtain ⟨i, j, hi, hj, hopi, hbi, hopj, hcone⟩ := hex
      obtain ⟨hL, hF⟩ := least_glue n G C hC
      obtain ⟨x1, hx1⟩ := exists_true n G hG
      have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF]; exact hx1)
      obtain ⟨C', r, hr, hir, hL', hF', hlen, hops, htop', hopr, hbelow, hcn, hno⟩ :=
        step3_struct n C (graphFun G ∅) hL hF hout i j hbi hcone
      have hlt := pairs_lt n C C' r i j hr hir hlen hops htop' hcn hno hopi hopj hcone
      rw [hk] at hlt
      obtain ⟨C'', h1, h2, h3, h4⟩ := ih _ hlt C' (least_glue' n G C' hL' hF') rfl
      refine ⟨C'', h1, h2.trans hlen, h3.trans ?_, h4⟩
      refine junk_eq n C C' (graphFun G ∅) r hr hlen hops htop' hopr hbelow _ _ ?_ ?_
      · intro k
        exact mem_junk n G C k
      · intro k
        exact mem_junk n G C' k

end PEqualNP.Outside.L_meta_1772_aux.IntegratedNormalForm.Extraction


-- Initial circuit construction adapted from the checked L-meta-5355 proof.
namespace PEqualNP.Outside.L_meta_1772_aux.IntegratedNormalForm.StarBuilder

open PEqualNP.CircuitLowerBounds

-- A vertex cover circuit: for each cover vertex c (in increasing order) an OR chain of the
-- neighbours of c not already handled, ANDed with c; the AND gates are ORed together.

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

def V {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ fs.map (fun f => f x)

def Sem {n : ℕ} (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  ∀ x : Fin n → Bool, wf gs (List.ofFn x) = V fs x

def Val {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (i : ℕ) (F : (Fin n → Bool) → Bool) : Prop :=
  i < n + fs.length ∧ ∀ x, (V fs x).getD i false = F x

theorem V_append {n : ℕ} (fs fs' : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    V (fs ++ fs') x = V fs x ++ fs'.map (fun f => f x) := by
  simp [V]

theorem V_length {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    (V fs x).length = n + fs.length := by simp [V]

theorem V_read {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) (j : ℕ)
    (hj : j < fs.length) : (V fs x).getD (n + j) false = fs.getD j (fun _ => false) x := by
  simp only [V]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hj]

theorem val_ext {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ} {F : (Fin n → Bool) → Bool}
    (h : Val fs i F) (fs' : List ((Fin n → Bool) → Bool)) : Val (fs ++ fs') i F := by
  refine ⟨by have := h.1; simp; omega, fun x => ?_⟩
  rw [V_append, List.getD_append _ _ _ _ (by rw [V_length]; exact h.1)]
  exact h.2 x

theorem val_congr {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ}
    {F F' : (Fin n → Bool) → Bool} (h : Val fs i F) (e : ∀ x, F x = F' x) : Val fs i F' :=
  ⟨h.1, fun x => by rw [h.2 x, e x]⟩

theorem val_in {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (a : Fin n) :
    Val fs a.val (fun x => x a) := by
  refine ⟨by omega, fun x => ?_⟩
  simp only [V]
  rw [List.getD_append _ _ _ _ (by simp)]
  simp

theorem val_new {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (f : (Fin n → Bool) → Bool) :
    Val (fs ++ [f]) (n + fs.length) f := by
  refine ⟨by simp, fun x => ?_⟩
  rw [V_read _ _ _ (by simp)]
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem sem_snoc {n : ℕ} {gs : List Gate} {fs : List ((Fin n → Bool) → Bool)} (h : Sem gs fs)
    (op : GateOp) (a b : ℕ) (A B : (Fin n → Bool) → Bool) (ha : Val fs a A) (hb : Val fs b B) :
    Sem (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) := by
  intro x
  rw [wf_snoc, h x, V_append]
  simp only [List.map_cons, List.map_nil, ha.2 x, hb.2 x]

def Mono (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def St {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) (gs : List Gate)
    (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  Sem gs fs ∧ fs.length = gs.length ∧ Mono gs ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ l, P l ∧ ∀ x, fs.getD j (fun _ => false) x = true → x l = true) ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ c v : Fin n, G.Adj c v ∧
      fs.getD j (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = true ∧
      ∀ i < j, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false)

theorem st_nil {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) : St G P [] [] := by
  refine ⟨fun x => by simp [wf, V], rfl, by simp [Mono], ?_, ?_⟩ <;> simp

theorem st_weak {n : ℕ} {G : SimpleGraph (Fin n)} {P Q : Fin n → Prop} {gs fs}
    (h : St G P gs fs) (hPQ : ∀ l, P l → Q l) : St G Q gs fs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, fun j hj hand => ?_, h5⟩
  obtain ⟨l, hl, hl2⟩ := h4 j hj hand
  exact ⟨l, hPQ l hl, hl2⟩

theorem push {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} {gs : List Gate}
    {fs : List ((Fin n → Bool) → Bool)} (h : St G P gs fs) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ) (A B : (Fin n → Bool) → Bool)
    (ha : Val fs a A) (hb : Val fs b B)
    (nA : op = GateOp.and → ∃ l, P l ∧ ∀ x, op.eval [A x, B x] = true → x l = true)
    (nB : op = GateOp.and → ∃ c v : Fin n, G.Adj c v ∧
      op.eval [A (PEqualNP.EdgeOwnership.pairInput c v), B (PEqualNP.EdgeOwnership.pairInput c v)]
        = true ∧
      ∀ i < gs.length, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false) :
    St G P (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) ∧
      Val (fs ++ [fun x => op.eval [A x, B x]]) (n + fs.length) (fun x => op.eval [A x, B x]) := by
  obtain ⟨hs, hl, hm, hA, hB⟩ := h
  refine ⟨⟨sem_snoc hs op a b A B ha hb, by simp [hl], ?_, ?_, ?_⟩, val_new _ _⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hm g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      rcases hop with e | e <;> simp [e]
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      obtain ⟨l, hl1, hl2⟩ := hA j hj hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rwa [List.getD_append _ _ _ _ (by omega)] at hx
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      obtain ⟨l, hl1, hl2⟩ := nA hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rw [← hl, List.getD_append_right _ _ _ _ le_rfl] at hx
      simpa using hx
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      obtain ⟨c, v, hadj, h1, h2⟩ := hB j hj hand
      refine ⟨c, v, hadj, ?_, fun i hi hand' => ?_⟩
      · rw [List.getD_append _ _ _ _ (by omega)]; exact h1
      · rw [List.getD_append _ _ _ _ (by omega)] at hand'
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 i hi hand'
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      obtain ⟨c, v, hadj, h1, h2⟩ := nB hand
      refine ⟨c, v, hadj, ?_, fun i hi hand' => ?_⟩
      · rw [← hl, List.getD_append_right _ _ _ _ le_rfl]
        simpa using h1
      · rw [List.getD_append _ _ _ _ hi] at hand'
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 i hi hand'

theorem chain {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} :
    ∀ (rest : List (Fin n)) (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (a : ℕ)
      (A : (Fin n → Bool) → Bool), St G P gs fs → Val fs a A →
      ∃ gs' fs' o, St G P gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
        gs'.length = gs.length + rest.length ∧
        Val fs' o (fun x => A x || rest.any (fun w => x w))
  | [], gs, fs, a, A, h, ha => ⟨gs, fs, a, h, ⟨[], by simp⟩, by simp, by simpa using ha⟩
  | w :: rest, gs, fs, a, A, h, ha => by
    obtain ⟨h1, h2⟩ := push h GateOp.or (Or.inr rfl) a w.val A (fun x => x w) ha (val_in fs w)
      (fun e => by simp at e) (fun e => by simp at e)
    obtain ⟨gs', fs', o, h3, ⟨fsn, hfs⟩, hlen, hv⟩ := chain rest _ _ _ _ h1 h2
    refine ⟨gs', fs', o, h3, ⟨(fun x => GateOp.or.eval [A x, x w]) :: fsn, by rw [hfs]; simp⟩, ?_, ?_⟩
    · rw [hlen]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    refine ⟨hv.1, fun x => ?_⟩
    rw [hv.2 x]
    simp [GateOp.eval, Bool.or_assoc]

def N {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun w => G.Adj c w ∧ ¬ (w ∈ C ∧ w < c))

def gad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n)
    (x : Fin n → Bool) : Bool :=
  x c && decide (∃ w ∈ N G C c, x w = true)

theorem gad_empty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {c : Fin n} (h : N G C c = ∅) (x : Fin n → Bool) : gad G C c x = false := by
  simp [gad, h]

theorem gadget {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {P : Fin n → Prop} (c : Fin n) (hP : ∀ l, P l → l ∈ C ∧ l < c) (hne : (N G C c).Nonempty)
    (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (h : St G P gs fs) :
    ∃ gs' fs' o, St G (fun l => P l ∨ l = c) gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
      gs'.length = gs.length + (N G C c).card ∧ Val fs' o (gad G C c) := by
  have hL : (N G C c).toList ≠ [] := by
    rw [Ne, Finset.toList_eq_nil]; exact hne.ne_empty
  obtain ⟨w0, rest, hL⟩ := List.exists_cons_of_ne_nil hL
  have hw0 : w0 ∈ N G C c := by
    rw [← Finset.mem_toList, hL]; exact List.mem_cons_self
  have hcard : (N G C c).card = rest.length + 1 := by
    rw [← Finset.length_toList, hL]; simp
  have key : ∀ x : Fin n → Bool,
      (x w0 || rest.any (fun w => x w)) = decide (∃ w ∈ N G C c, x w = true) := by
    intro x
    have : (x w0 || rest.any (fun w => x w)) = (N G C c).toList.any (fun w => x w) := by
      rw [hL]; simp
    rw [this, Bool.eq_iff_iff]
    simp [List.any_eq_true, Finset.mem_toList]
  obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, hv1⟩ :=
    chain rest gs fs w0.val (fun x => x w0) h (val_in fs w0)
  have hlab := h1.2.2.2.1
  have hl1 := h1.2.1
  obtain ⟨h2, hv2⟩ := push (st_weak (Q := fun l => P l ∨ l = c) h1 (fun l hl => Or.inl hl)) GateOp.and (Or.inl rfl) c.val o1
    (fun x => x c) _ (val_in fs1 c) hv1
    (fun _ => ⟨c, Or.inr rfl, fun x hx => by simp [GateOp.eval] at hx; exact hx.1⟩)
    (fun _ => ⟨c, w0, by
        simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw0; exact hw0.1, by
        simp [GateOp.eval, PEqualNP.EdgeOwnership.pairInput], by
        intro i hi hand
        obtain ⟨l, hl, hl2⟩ := hlab i hi hand
        obtain ⟨hlC, hlc⟩ := hP l hl
        cases hval : fs1.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c w0) with
        | false => rfl
        | true =>
          exfalso
          have := hl2 _ hval
          simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at this
          rcases this with rfl | rfl
          · exact lt_irrefl _ hlc
          · simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw0
            exact hw0.2 ⟨hlC, hlc⟩⟩)
  refine ⟨_, _, n + fs1.length, h2, ⟨fsn ++ [fun x => GateOp.and.eval [x c, x w0 || rest.any fun w => x w]], by rw [hfs]; simp⟩, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton, hlen1, hcard]; omega
  refine val_congr hv2 (fun x => ?_)
  simp only [GateOp.eval, gad, ← key x]
  simp

theorem build {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (S : Finset (Fin n)) : S ⊆ C →
    ∃ gs fs, St G (fun l => l ∈ S) gs fs ∧
      ((gs = [] ∧ ∀ c ∈ S, N G C c = ∅) ∨
       ∃ o, Val fs o (fun x => decide (∃ c ∈ S, gad G C c x = true)) ∧
         gs.length + 1 ≤ (∑ c ∈ S, (N G C c).card) + S.card) := by
  induction S using Finset.induction_on_max with
  | empty => intro _; exact ⟨[], [], st_nil G _, Or.inl ⟨rfl, by simp⟩⟩
  | insert c S hlt ih =>
    intro hsub
    have hcS : c ∉ S := fun hc => lt_irrefl _ (hlt c hc)
    obtain ⟨gs, fs, h, hcase⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
    have hP : ∀ l, l ∈ S → l ∈ C ∧ l < c :=
      fun l hl => ⟨hsub (Finset.mem_insert_of_mem hl), hlt l hl⟩
    by_cases hN : N G C c = ∅
    · refine ⟨gs, fs, st_weak h (fun l hl => Finset.mem_insert_of_mem hl), ?_⟩
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · left
        refine ⟨hg, ?_⟩
        intro c' hc'
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · exact hN
        · exact hall c' hc'
      · right
        refine ⟨o, val_congr hv ?_, ?_⟩
        · intro x
          simp [Finset.mem_insert, gad_empty hN]
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]; omega
    · have hne : (N G C c).Nonempty := Finset.nonempty_iff_ne_empty.2 hN
      obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, hv1⟩ := gadget c hP hne gs fs h
      have h1' : St G (fun l => l ∈ insert c S) gs1 fs1 := by
        refine st_weak h1 ?_
        intro l hl
        rcases hl with hl | rfl
        · exact Finset.mem_insert_of_mem hl
        · exact Finset.mem_insert_self _ _
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · refine ⟨gs1, fs1, h1', Or.inr ⟨o1, val_congr hv1 ?_, ?_⟩⟩
        · intro x
          have : ¬ ∃ c' ∈ S, gad G C c' x = true := by
            rintro ⟨c', hc', hg'⟩
            rw [gad_empty (hall c' hc')] at hg'
            exact Bool.false_ne_true hg'
          rw [Bool.eq_iff_iff]
          simp only [decide_eq_true_eq, Finset.mem_insert]
          constructor
          · intro hx; exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact hx
            · exact absurd ⟨c', hc', hx⟩ this
        · subst hg
          rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp at hlen1
          omega
      · obtain ⟨h2, hv2⟩ := push h1' GateOp.or (Or.inr rfl) o o1 _ _
          (by rw [hfs]; exact val_ext hv fsn) hv1 (fun e => by simp at e) (fun e => by simp at e)
        refine ⟨_, _, h2, Or.inr ⟨_, val_congr hv2 ?_, ?_⟩⟩
        · intro x
          rw [Bool.eq_iff_iff]
          simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id,
            Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
          constructor
          · rintro (⟨c', hc', hx⟩ | hx)
            · exact ⟨c', Or.inr hc', hx⟩
            · exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact Or.inr hx
            · exact Or.inl ⟨c', hc', hx⟩
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp only [List.length_append, List.length_singleton]
          omega

theorem edge_N {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) {u v : Fin n} (h : G.Adj u v) :
    ∃ c ∈ C, ∃ w ∈ N G C c, (c = u ∧ w = v) ∨ (c = v ∧ w = u) := by
  simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hC u v h with hu | hv
  · by_cases hv' : v ∈ C ∧ v < u
    · refine ⟨v, hv'.1, u, ⟨h.symm, fun hh => lt_asymm hh.2 hv'.2⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨u, hu, v, ⟨h, hv'⟩, Or.inl ⟨rfl, rfl⟩⟩
  · by_cases hu' : u ∈ C ∧ u < v
    · exact ⟨u, hu'.1, v, ⟨h, fun hh => lt_asymm hh.2 hu'.2⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, hv, u, ⟨h.symm, hu'⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem any_gad {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) (x : Fin n → Bool) :
    decide (∃ c ∈ C, gad G C c x = true) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x := by
  rw [Bool.eq_iff_iff]
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, gad, decide_eq_true_eq,
    Bool.and_eq_true, Bool.or_eq_true, Finset.notMem_empty, false_and, exists_false,
    false_or]
  constructor
  · rintro ⟨c, -, hc, w, hw, hxw⟩
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨c, w, hw.1, hc, hxw⟩
  · rintro ⟨u, v, h, hu, hv⟩
    obtain ⟨c, hc, w, hw, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := edge_N hC h
    · exact ⟨c, hc, hu, w, hw, hv⟩
    · exact ⟨c, hc, hv, w, hw, hu⟩

theorem sumN_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) :
    ∑ c ∈ C, (N G C c).card ≤ G.edgeSet.ncard := by
  rw [← Finset.card_sigma]
  have : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [this]
  apply Finset.card_le_card_of_injOn (fun p => s(p.1, p.2))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hp.2.1
  · rintro ⟨c, w⟩ hp ⟨c', w'⟩ hq hpq
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; rfl
    · exfalso
      subst h1; subst h2
      have e1 : ¬ w < c := fun hl => hp.2.2 ⟨hq.1, hl⟩
      have e2 : ¬ c < w := fun hl => hq.2.2 ⟨hp.1, hl⟩
      have : c = w := le_antisymm (not_lt.1 e1) (not_lt.1 e2)
      subst this
      exact G.irrefl hp.2.1

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hC : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G C) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      D.size ≤ G.edgeSet.ncard + C.card - 1 ∧
      ∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧ PEqualNP.EdgeOwnership.Owns n D j u v := by
  have hC' : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C := hC
  obtain ⟨gs, fs, ⟨hs, hl, hm, -, hB⟩, hcase⟩ := build G C C (subset_refl _)
  rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
  · subst hg
    refine ⟨⟨[], n⟩, by simp [PEqualNP.MetaComplexity.Monotone2], ?_, by simp [Circuit.size], ?_⟩
    · funext x
      rw [← any_gad hC' x]
      have : ¬ ∃ c ∈ C, gad G C c x = true := by
        rintro ⟨c', hc', hg'⟩
        rw [gad_empty (hall c' hc')] at hg'
        exact Bool.false_ne_true hg'
      simp only [this, decide_false]
      show (wf [] (List.ofFn x)).getD n false = false
      simp only [wf, List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp)
    · intro j hj
      simp [Circuit.size] at hj
  · refine ⟨⟨gs, o⟩, hm, ?_, ?_, ?_⟩
    · funext x
      show (wf gs (List.ofFn x)).getD o false = _
      rw [hs x, hv.2 x]
      exact any_gad hC' x
    · have h1 := sumN_le G C
      show gs.length ≤ _
      omega
    · intro j hj hand
      have hj' : j < gs.length := hj
      obtain ⟨c, v, hadj, h1, h2⟩ := hB j hj' hand
      have gv : ∀ i, i < gs.length → ∀ y : Fin n → Bool,
          PEqualNP.EdgeOwnership.gateVal n ⟨gs, o⟩ i y = fs.getD i (fun _ => false) y := by
        intro i hi y
        show (wf gs (List.ofFn y)).getD (n + i) false = _
        rw [hs y, V_read _ _ _ (by omega)]
      refine ⟨c, v, hadj, hj', hand, by rw [gv j hj']; exact h1, ?_⟩
      intro i hi _ hand'
      rw [gv i (by omega)]
      exact h2 i hi hand'

end PEqualNP.Outside.L_meta_1772_aux.IntegratedNormalForm.StarBuilder

namespace PEqualNP.Outside.L_meta_1772_aux.IntegratedNormalForm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

lemma exists_minimal_graph_circuit
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ := by
  classical
  obtain ⟨B, monoB, computesB, _, _⟩ :=
    StarBuilder.main n G Finset.univ (fun _ _ _ => Or.inl (Finset.mem_univ _))
  let feasible (k : ℕ) := ∃ C : Circuit,
    Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧ C.size = k
  have existsFeasible : ∃ k, feasible k := ⟨B.size, B, monoB, computesB, rfl⟩
  obtain ⟨C, monoC, computesC, sizeC⟩ := Nat.find_spec existsFeasible
  refine ⟨C, ⟨monoC, ?_⟩, computesC⟩
  intro E monoE funE
  rw [sizeC]
  exact Nat.find_min' existsFeasible
    (show feasible E.size from ⟨E, monoE, funE.trans computesC, rfl⟩)

open PEqualNP.TopForm PEqualNP.CleanedNonEdge
open Pivots

lemma extract_sound_ancestor
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (nonempty : G.edgeFinset.Nonempty)
    (C : Circuit) (minimum : IsMinimalMonoCircuit n C) (correct : circuitFun n C = graphFun G ∅)
    (i j : ℕ) (hi : i < C.gates.length) (hj : j < C.gates.length)
    (andi : (gateAt C i).op = GateOp.and) (sound : BelowF G C i)
    (andj : (gateAt C j).op = GateOp.and) (cone : InCone n C i j) :
    ∃ E : Circuit, IsMinimalMonoCircuit n E ∧ circuitFun n E = graphFun G ∅ ∧
      (junk G E).card = (junk G C).card ∧ andPairs n E < andPairs n C := by
  classical
  have least := Model.minimal_isLeastAO n G C minimum correct
  obtain ⟨hL, hF⟩ := Extraction.least_glue n G C least
  obtain ⟨x, hx⟩ := Extraction.exists_true n G nonempty
  have outputBound : C.output < n + C.gates.length :=
    Extraction.out_lt n C x (by rw [hF]; exact hx)
  obtain ⟨E, r, hr, hir, hLE, hFE, lengths, ops, lastOR, removedOR, below, cones, noCone⟩ :=
    Extraction.step3_struct n C (graphFun G ∅) hL hF outputBound i j sound cone
  have leastE := Extraction.least_glue' n G E hLE hFE
  have monoE : Monotone2 E := by
    intro g hg
    refine ⟨leastE.1.1 g hg, ?_⟩
    rw [leastE.1.2.2 g hg]
  have minimumE : IsMinimalMonoCircuit n E := by
    refine ⟨monoE, fun B monoB correctB => ?_⟩
    change E.gates.length ≤ B.size
    rw [lengths]
    exact minimum.2 B monoB (correctB.trans (leastE.2.1.trans correct.symm))
  have fewerPairs := Extraction.pairs_lt n C E r i j hr hir lengths ops lastOR cones noCone andi andj cone
  have sameJunk : (junk G E).card = (junk G C).card := by
    apply Extraction.junk_eq n C E (graphFun G ∅) r hr lengths ops lastOR removedOR below
    · intro k
      exact Extraction.mem_junk n G C k
    · intro k
      exact Extraction.mem_junk n G E k
  refine ⟨E, minimumE, leastE.2.1, sameJunk, ?_⟩
  convert fewerPairs using 1 <;> unfold andPairs <;> congr 1 <;> ext p <;> simp

lemma exists_integrated_normal_form
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (nonempty : G.edgeFinset.Nonempty) :
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
      PEqualNP.TopForm.TopForm G D ∧
      (∀ E : Circuit, IsMinimalMonoCircuit n E → circuitFun n E = graphFun G ∅ →
        (junk G D).card ≤ (junk G E).card) ∧
      (∀ E : Circuit, IsMinimalMonoCircuit n E → circuitFun n E = graphFun G ∅ →
        (junk G E).card = (junk G D).card → andPairs n D ≤ andPairs n E) ∧
      (∀ E : Circuit, IsMinimalMonoCircuit n E → circuitFun n E = graphFun G ∅ →
        (junk G E).card = (junk G D).card → andPairs n E = andPairs n D →
        (badAndGates n G D).ncard ≤ (badAndGates n G E).ncard) ∧
      ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        (IsDirtyAnd n G D j ∨ ∀ u v, G.Adj u v → ¬ Owns n D j u v) →
        ∃ u v a b, G.Adj u v ∧ G.Adj a b ∧
          circuitFun n (disabled D j) (pairInput u v) = false ∧
          circuitFun n (disabled D j) (pairInput a b) = false ∧ s(a, b) ≠ s(u, v) := by
  classical
  obtain ⟨C, minimumC, computesC⟩ := exists_minimal_graph_circuit n G
  let dirtyAdmissible (k : ℕ) := ∃ E : Circuit,
    IsMinimalMonoCircuit n E ∧ circuitFun n E = graphFun G ∅ ∧ (junk G E).card = k
  have existsDirty : ∃ k, dirtyAdmissible k :=
    ⟨(junk G C).card, C, minimumC, computesC, rfl⟩
  obtain ⟨B, minimumB, computesB, dirtyB⟩ := Nat.find_spec existsDirty
  let pairAdmissible (k : ℕ) := ∃ E : Circuit,
    IsMinimalMonoCircuit n E ∧ circuitFun n E = graphFun G ∅ ∧
      (junk G E).card = Nat.find existsDirty ∧ andPairs n E = k
  have existsPairs : ∃ k, pairAdmissible k :=
    ⟨andPairs n B, B, minimumB, computesB, dirtyB, rfl⟩
  obtain ⟨A, minimumA, computesA, dirtyA, pairsA⟩ := Nat.find_spec existsPairs
  let badAdmissible (k : ℕ) := ∃ E : Circuit,
    IsMinimalMonoCircuit n E ∧ circuitFun n E = graphFun G ∅ ∧
      (junk G E).card = Nat.find existsDirty ∧ andPairs n E = Nat.find existsPairs ∧
      (badAndGates n G E).ncard = k
  have existsBad : ∃ k, badAdmissible k :=
    ⟨(badAndGates n G A).ncard, A, minimumA, computesA, dirtyA, pairsA, rfl⟩
  obtain ⟨D, minimumD, computesD, dirtyD, pairsD, badD⟩ := Nat.find_spec existsBad
  have leastDirty (E : Circuit) (minimumE : IsMinimalMonoCircuit n E)
      (computesE : circuitFun n E = graphFun G ∅) : (junk G D).card ≤ (junk G E).card := by
    rw [dirtyD]
    exact Nat.find_min' existsDirty
      (show dirtyAdmissible (junk G E).card from ⟨E, minimumE, computesE, rfl⟩)
  have leastPairs (E : Circuit) (minimumE : IsMinimalMonoCircuit n E)
      (computesE : circuitFun n E = graphFun G ∅)
      (equalDirty : (junk G E).card = (junk G D).card) : andPairs n D ≤ andPairs n E := by
    rw [pairsD]
    exact Nat.find_min' existsPairs
      (show pairAdmissible (andPairs n E) from
        ⟨E, minimumE, computesE, equalDirty.trans dirtyD, rfl⟩)
  have leastBad (E : Circuit) (minimumE : IsMinimalMonoCircuit n E)
      (computesE : circuitFun n E = graphFun G ∅)
      (equalDirty : (junk G E).card = (junk G D).card)
      (equalPairs : andPairs n E = andPairs n D) :
      (badAndGates n G D).ncard ≤ (badAndGates n G E).ncard := by
    rw [badD]
    exact Nat.find_min' existsBad
      (show badAdmissible (badAndGates n G E).ncard from
        ⟨E, minimumE, computesE, equalDirty.trans dirtyD, equalPairs.trans pairsD, rfl⟩)
  have top : PEqualNP.TopForm.TopForm G D := by
    intro i hi j hj andi sound andj cone
    obtain ⟨E, minimumE, computesE, sameJunk, fewerPairs⟩ :=
      extract_sound_ancestor n G nonempty D minimumD computesD i j hi hj andi sound andj cone
    have bound := leastPairs E minimumE computesE sameJunk
    omega
  refine ⟨D, minimumD, computesD, top, leastDirty, leastPairs, leastBad, ?_⟩
  intro j hj hand offending
  obtain ⟨u, v, edge, active, pivotal⟩ := pivotal_edge_exists n G D minimumD computesD j hj hand
  have other : ∃ a b, G.Adj a b ∧ circuitFun n (disabled D j) (pairInput a b) = false ∧
      s(a, b) ≠ s(u, v) := by
    by_contra noOther
    have onlyPivotal : ∀ a b, G.Adj a b →
        circuitFun n (disabled D j) (pairInput a b) = false →
        (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
      intro a b hab hpivotal
      apply Sym2.eq_iff.mp
      by_contra different
      exact noOther ⟨a, b, hab, hpivotal, different⟩
    obtain ⟨E, minimumE, computesE, _, dirtyLe, pairsLe, dirtyStrict, _, badStrict⟩ :=
      singleton_pivotal_all_measures n G D minimumD computesD j hj hand u v edge active onlyPivotal
    have dirtyLower := leastDirty E minimumE computesE
    have equalDirty : (junk G E).card = (junk G D).card := Nat.le_antisymm dirtyLe dirtyLower
    have pairsLower := leastPairs E minimumE computesE equalDirty
    have equalPairs : andPairs n E = andPairs n D := Nat.le_antisymm pairsLe pairsLower
    rcases offending with dirty | unowned
    · have memDirty : j ∈ junk G D :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, dirty⟩
      have strict := dirtyStrict memDirty
      omega
    · have badLower := leastBad E minimumE computesE equalDirty equalPairs
      have strict := badStrict unowned
      omega
  obtain ⟨a, b, edge', pivotal', different⟩ := other
  exact ⟨u, v, a, b, edge, edge', pivotal, pivotal', different⟩

end PEqualNP.Outside.L_meta_1772_aux.IntegratedNormalForm
