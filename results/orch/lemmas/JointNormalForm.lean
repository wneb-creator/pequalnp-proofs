import PEqualNP.Defs

-- Bypass helpers adapted from willakone, L-meta-1499, PR 3112.
namespace PEqualNP.Outside.L_meta_1772_aux.JointNormalForm

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

end PEqualNP.Outside.L_meta_1772_aux.JointNormalForm

namespace PEqualNP.Outside.L_meta_1772_aux.JointNormalForm.StarBuilder

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

end PEqualNP.Outside.L_meta_1772_aux.JointNormalForm.StarBuilder

namespace PEqualNP.Outside.L_meta_1772_aux.JointNormalForm
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

lemma exists_joint_pivotal_normal_form
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ E : Circuit, IsMinimalMonoCircuit n E → circuitFun n E = graphFun G ∅ →
        (junk G D).card ≤ (junk G E).card) ∧
      (∀ E : Circuit, IsMinimalMonoCircuit n E → circuitFun n E = graphFun G ∅ →
        (junk G E).card = (junk G D).card →
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
  let badAdmissible (k : ℕ) := ∃ E : Circuit,
    IsMinimalMonoCircuit n E ∧ circuitFun n E = graphFun G ∅ ∧
      (junk G E).card = Nat.find existsDirty ∧ (badAndGates n G E).ncard = k
  have existsBad : ∃ k, badAdmissible k :=
    ⟨(badAndGates n G B).ncard, B, minimumB, computesB, dirtyB, rfl⟩
  obtain ⟨D, minimumD, computesD, dirtyD, badD⟩ := Nat.find_spec existsBad
  have leastDirty (E : Circuit) (minimumE : IsMinimalMonoCircuit n E)
      (computesE : circuitFun n E = graphFun G ∅) : (junk G D).card ≤ (junk G E).card := by
    rw [dirtyD]
    exact Nat.find_min' existsDirty
      (show dirtyAdmissible (junk G E).card from ⟨E, minimumE, computesE, rfl⟩)
  have leastBad (E : Circuit) (minimumE : IsMinimalMonoCircuit n E)
      (computesE : circuitFun n E = graphFun G ∅)
      (equalDirty : (junk G E).card = (junk G D).card) :
      (badAndGates n G D).ncard ≤ (badAndGates n G E).ncard := by
    rw [badD]
    exact Nat.find_min' existsBad
      (show badAdmissible (badAndGates n G E).ncard from
        ⟨E, minimumE, computesE, equalDirty.trans dirtyD, rfl⟩)
  refine ⟨D, minimumD, computesD, leastDirty, leastBad, ?_⟩
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
    obtain ⟨E, minimumE, computesE, _, dirtyLe, dirtyStrict, _, badStrict⟩ :=
      singleton_pivotal_controlled n G D minimumD computesD j hj hand u v edge active onlyPivotal
    have dirtyLower := leastDirty E minimumE computesE
    rcases offending with dirty | unowned
    · have memDirty : j ∈ junk G D :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, dirty⟩
      have strict := dirtyStrict memDirty
      omega
    · have equalDirty : (junk G E).card = (junk G D).card := Nat.le_antisymm dirtyLe dirtyLower
      have badLower := leastBad E minimumE computesE equalDirty
      have strict := badStrict unowned
      omega
  obtain ⟨a, b, edge', pivotal', different⟩ := other
  exact ⟨u, v, a, b, edge, edge', pivotal, pivotal', different⟩

end PEqualNP.Outside.L_meta_1772_aux.JointNormalForm
