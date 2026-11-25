import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.clean

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

lemma minimal_no_alias {n : ℕ} {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i) :
    ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = val C (List.ofFn x) i := by
  intro heq
  have hs := hmin.2 (bypass n C r i) (bypass_mono hmin.1) (by
    funext x
    exact bypass_eval_eq (by simp) (mono_ops hmin.1) hr hi (heq x))
  change C.gates.length ≤ (bypass n C r i).gates.length at hs
  rw [bypass_length] at hs
  omega

lemma minimal_gate_true_somewhere {n : ℕ} {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    {r : ℕ} (hr : r < C.gates.length) :
    ∃ x : Fin n → Bool, val C (List.ofFn x) (n + r) = true := by
  by_contra hn
  apply minimal_no_alias hmin hr (Or.inr (le_refl (n + C.gates.length)))
  intro x
  rw [val_ge (n := n) (by simp) le_rfl]
  cases h : val C (List.ofFn x) (n + r)
  · rfl
  · exact False.elim (hn ⟨x, h⟩)

lemma minimal_gate_not_input {n : ℕ} {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    {r : ℕ} (hr : r < C.gates.length) (i : Fin n) :
    ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = x i := by
  intro heq
  apply minimal_no_alias hmin hr (Or.inl (show i.val < n + r by omega))
  intro x
  rw [val_input (n := n) (by simp) i.isLt]
  simpa using heq x

lemma minimal_gate_has_reader {n : ℕ} {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    {r : ℕ} (hr : r < C.gates.length) (hout : C.output ≠ n + r) :
    ∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs := by
  by_contra hn
  have hs := hmin.2 (bypass n C r (n + C.gates.length)) (bypass_mono hmin.1) (by
    funext x
    exact bypass_eval_unread (by simp) (mono_ops hmin.1) hr (Or.inr le_rfl) hout
      (fun k hrk hk hm => hn ⟨k, hrk, hk, hm⟩))
  change C.gates.length ≤ (bypass n C r (n + C.gates.length)).gates.length at hs
  rw [bypass_length] at hs
  omega

def previousWire (n : ℕ) (C : Circuit) (k p : ℕ) : ℕ :=
  if p < n + k then p else n + C.gates.length

lemma previousWire_valid (n : ℕ) (C : Circuit) (k p : ℕ) :
    previousWire n C k p < n + k ∨ n + C.gates.length ≤ previousWire n C k p := by
  unfold previousWire
  split <;> simp_all

lemma previousWire_val (n : ℕ) (C : Circuit) (k p : ℕ) (x : Fin n → Bool) :
    val C (List.ofFn x) (previousWire n C k p) =
      if p < n + k then val C (List.ofFn x) p else false := by
  unfold previousWire
  split
  · rfl
  · exact val_ge (by simp) le_rfl

lemma minimal_no_read_alias {n : ℕ} {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    {k : ℕ} (hk : k < C.gates.length) (p : ℕ) :
    ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) =
      if p < n + k then val C (List.ofFn x) p else false := by
  intro h
  apply minimal_no_alias hmin hk (previousWire_valid n C k p)
  intro x
  rw [previousWire_val]
  exact h x

lemma inputs_shapes (l : List ℕ) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  have hcases : l.length = 0 ∨ l.length = 1 ∨ l.length = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exact Or.inl (List.length_eq_zero_iff.mp h0)
  · exact Or.inr (Or.inl (List.length_eq_one_iff.mp h1))
  · exact Or.inr (Or.inr (List.length_eq_two.mp h2))

lemma minimal_not_unary {n : ℕ} {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    {k : ℕ} (hk : k < C.gates.length) (p : ℕ) : (gateAt C k).inputs ≠ [p] := by
  intro hins
  apply minimal_no_read_alias hmin hk p
  intro x
  rw [val_gate (by simp) hk, hins]
  rcases mono_ops hmin.1 k hk with hop | hop <;> simp [hop, GateOp.eval]

lemma minimal_not_repeated {n : ℕ} {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    {k : ℕ} (hk : k < C.gates.length) (p : ℕ) : (gateAt C k).inputs ≠ [p, p] := by
  intro hins
  apply minimal_no_read_alias hmin hk p
  intro x
  rw [val_gate (by simp) hk, hins]
  rcases mono_ops hmin.1 k hk with hop | hop <;> simp [hop, GateOp.eval]

lemma minimal_gate_not_true {n : ℕ} {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    (hzero : circuitFun n C (fun _ => false) = false)
    {r : ℕ} (hr : r < C.gates.length) :
    ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = true := by
  intro htrue
  have hout : C.output ≠ n + r := by
    intro h
    have hz := htrue (fun _ => false)
    change val C (List.ofFn (fun _ : Fin n => false)) C.output = false at hzero
    rw [h, hz] at hzero
    cases hzero
  obtain ⟨k, hrk, hk, hmem⟩ := minimal_gate_has_reader hmin hr hout
  have hrkn : n + r < n + k := by omega
  rcases mono_ops hmin.1 k hk with hand | hor
  · have hlen := (hmin.1 _ (gateAt_mem hk)).2
    rcases inputs_shapes (gateAt C k).inputs hlen with hnil | ⟨a, ha⟩ | ⟨a, b, hab⟩
    · simp [hnil] at hmem
    · exact minimal_not_unary hmin hk a ha
    · have hm : a = n + r ∨ b = n + r := by simpa [hab, eq_comm] using hmem
      rcases hm with rfl | rfl
      · apply minimal_no_read_alias hmin hk b
        intro x
        rw [val_gate (by simp) hk, hand, hab]
        simp [GateOp.eval, hrkn, htrue x]
      · apply minimal_no_read_alias hmin hk a
        intro x
        rw [val_gate (by simp) hk, hand, hab]
        simp [GateOp.eval, hrkn, htrue x]
  · apply minimal_no_alias hmin hk (Or.inl hrkn)
    intro x
    rw [htrue x]
    apply (val_or (by simp) hk hor).mpr
    exact ⟨n + r, hmem, hrkn, htrue x⟩

lemma minimal_nonempty_inputs {n : ℕ} {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    (hzero : circuitFun n C (fun _ => false) = false)
    {k : ℕ} (hk : k < C.gates.length) : (gateAt C k).inputs ≠ [] := by
  intro hins
  rcases mono_ops hmin.1 k hk with hand | hor
  · apply minimal_gate_not_true hmin hzero hk
    intro x
    rw [val_gate (by simp) hk, hand, hins]
    rfl
  · obtain ⟨x, hx⟩ := minimal_gate_true_somewhere hmin hk
    rw [val_gate (by simp) hk, hor, hins] at hx
    cases hx

lemma minimal_inputs_two {n : ℕ} {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    (hzero : circuitFun n C (fun _ => false) = false)
    {k : ℕ} (hk : k < C.gates.length) :
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a ≠ b := by
  have hlen := (hmin.1 _ (gateAt_mem hk)).2
  rcases inputs_shapes (gateAt C k).inputs hlen with hnil | ⟨a, ha⟩ | ⟨a, b, hab⟩
  · exact False.elim (minimal_nonempty_inputs hmin hzero hk hnil)
  · exact False.elim (minimal_not_unary hmin hk a ha)
  · exact ⟨a, b, hab, fun h => minimal_not_repeated hmin hk b (h ▸ hab)⟩

lemma minimal_readsBack {n : ℕ} {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    (hzero : circuitFun n C (fun _ => false) = false) : ReadsBack n C := by
  intro k hk p hp
  rcases mono_ops hmin.1 k hk with hand | hor
  · obtain ⟨x, hx⟩ := minimal_gate_true_somewhere hmin hk
    exact ((val_and (by simp) hk hand).mp hx p hp).1
  · obtain ⟨a, b, hab, _⟩ := minimal_inputs_two hmin hzero hk
    have hp' : p = a ∨ p = b := by simpa [hab] using hp
    rcases hp' with rfl | rfl
    · by_contra hn
      apply minimal_no_read_alias hmin hk b
      intro x
      rw [val_gate (by simp) hk, hor, hab]
      simp [GateOp.eval, hn]
    · by_contra hn
      apply minimal_no_read_alias hmin hk a
      intro x
      rw [val_gate (by simp) hk, hor, hab]
      simp [GateOp.eval, hn]

lemma minimal_isAO2 {n : ℕ} {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    (hzero : circuitFun n C (fun _ => false) = false) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨fun g hg => (hmin.1 g hg).1, minimal_readsBack hmin hzero, ?_⟩
  intro g hg
  obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
  obtain ⟨a, b, hab, _⟩ := minimal_inputs_two hmin hzero hk
  rw [gateAt_eq hk, hgk] at hab
  simp [hab]

lemma mono_of_isAO2 {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    Monotone2 C := by
  intro g hg
  exact ⟨h.1 g hg, by rw [h.2.2 g hg]⟩

lemma exists_minimal_of_mono (n : ℕ) (C : Circuit) (hC : Monotone2 C) :
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = circuitFun n C := by
  classical
  let feasible (k : ℕ) := ∃ D : Circuit, Monotone2 D ∧
    circuitFun n D = circuitFun n C ∧ D.size = k
  have hex : ∃ k, feasible k := ⟨C.size, C, hC, rfl, rfl⟩
  obtain ⟨D, hD, heq, hs⟩ := Nat.find_spec hex
  refine ⟨D, ⟨hD, ?_⟩, heq⟩
  intro E hE hED
  rw [hs]
  exact Nat.find_min' hex (show feasible E.size from ⟨E, hE, hED.trans heq, rfl⟩)

lemma minimal_graph_isLeastAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hmin : IsMinimalMonoCircuit n C) (hf : circuitFun n C = graphFun G ∅) :
    PEqualNP.TopForm.IsLeastAO G C := by
  refine ⟨minimal_isAO2 hmin ?_, hf, ?_⟩
  · rw [hf]
    simp [graphFun]
  · intro D hD hF
    exact hmin.2 D (mono_of_isAO2 hD) (hF.trans hf.symm)

lemma leastAO_graph_isMinimal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (h : PEqualNP.TopForm.IsLeastAO G C) : IsMinimalMonoCircuit n C := by
  refine ⟨mono_of_isAO2 h.1, ?_⟩
  intro D hD hDC
  obtain ⟨E, hE, hED⟩ := exists_minimal_of_mono n D hD
  have hEF : circuitFun n E = graphFun G ∅ := hED.trans (hDC.trans h.2.1)
  have hCE : C.size ≤ E.size := h.2.2 E (minimal_graph_isLeastAO G hE hEF).1 hEF
  exact hCE.trans (hE.2 D hD hED.symm)

end PEqualNP.Outside.L_meta_1772_aux.clean

namespace PEqualNP.Outside.L_meta_1772_aux.protectedPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_1772_aux.clean

lemma mem_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {j : ℕ} :
    j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]

def skipIndex (r k : ℕ) : ℕ := if k < r then k else k + 1

lemma skip_injective (r : ℕ) : Function.Injective (skipIndex r) := by
  intro a b h
  unfold skipIndex at h
  split_ifs at h <;> omega

lemma bypass_gate_op {n : ℕ} {C : Circuit} {r i k : ℕ}
    (hk : k < (bypass n C r i).gates.length) :
    (gateAt (bypass n C r i) k).op = (gateAt C (skipIndex r k)).op := by
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  unfold skipIndex
  split_ifs <;> rfl

lemma bypass_gate_eq {n : ℕ} {C : Circuit} (hC : Monotone2 C)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r)
    (x : Fin n → Bool) (heq : val C (List.ofFn x) (n + r) = val C (List.ofFn x) i)
    {k : ℕ} (hk : k < (bypass n C r i).gates.length) :
    gateVal n (bypass n C r i) k x = gateVal n C (skipIndex r k) x := by
  have hskip : skipIndex r k ≠ r := by unfold skipIndex; split_ifs <;> omega
  have hwire : aliasWire (n + r) i (n + skipIndex r k) = n + k := by
    unfold skipIndex
    split_ifs with h
    · exact aliasWire_lt_self (by omega)
    · rw [aliasWire_gt_self (by omega)]; omega
  have h := bypass_rel (R := Eq) (fun _ => rfl) opMono_eq (by simp) (mono_ops hC)
    hr (Or.inl hi) (fun _ => heq) (n + skipIndex r k) (by omega)
  rw [hwire] at h
  exact h.symm

lemma bypass_junk_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C) (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r)
    (heq : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      val C (List.ofFn x) (n + r) = val C (List.ofFn x) i) :
    (junk G (bypass n C r i)).card ≤ ((junk G C).erase r).card := by
  apply Finset.card_le_card_of_injOn (skipIndex r)
  · intro k hk
    obtain ⟨hkl, hop, _, x, hx, hxF⟩ := mem_junk.mp hk
    have hlen : k < C.gates.length - 1 := by simpa [bypass_length] using hkl
    have hkr : skipIndex r k ≠ r := by unfold skipIndex; split_ifs <;> omega
    have hkc : skipIndex r k < C.gates.length := by unfold skipIndex; split_ifs <;> omega
    refine Finset.mem_erase.mpr ⟨hkr, mem_junk.mpr ⟨hkc, ?_, hkc, x, ?_, hxF⟩⟩
    · rwa [bypass_gate_op hkl] at hop
    · rwa [bypass_gate_eq hC hr hi x (heq x hxF) hkl] at hx
  · exact fun _ _ _ _ h => skip_injective r h

lemma bypass_junk_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C) (r i : ℕ) (hr : r ∈ junk G C) (hi : i < n + r)
    (heq : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      val C (List.ofFn x) (n + r) = val C (List.ofFn x) i) :
    (junk G (bypass n C r i)).card < (junk G C).card :=
  lt_of_le_of_lt (bypass_junk_le G C hC r i (mem_junk.mp hr).1 hi heq)
    (Finset.card_erase_lt_of_mem hr)

def appendEdge {n : ℕ} (C : Circuit) (u v : Fin n) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.and, [u.val, v.val]⟩,
    ⟨GateOp.or, [C.output, n + C.gates.length]⟩], n + C.gates.length + 1⟩

lemma appendEdge_length {n : ℕ} (C : Circuit) (u v : Fin n) :
    (appendEdge C u v).gates.length = C.gates.length + 2 := by simp [appendEdge]

lemma appendEdge_at_old {n : ℕ} (C : Circuit) (u v : Fin n) {k : ℕ}
    (hk : k < C.gates.length) : gateAt (appendEdge C u v) k = gateAt C k := by
  rw [gateAt_eq (by rw [appendEdge_length]; omega), gateAt_eq hk]
  simp [appendEdge, List.getElem_append_left hk]

lemma appendEdge_at_and {n : ℕ} (C : Circuit) (u v : Fin n) :
    gateAt (appendEdge C u v) C.gates.length = ⟨GateOp.and, [u.val, v.val]⟩ := by
  simp [gateAt, appendEdge, List.getD_eq_getElem?_getD]

lemma appendEdge_at_or {n : ℕ} (C : Circuit) (u v : Fin n) :
    gateAt (appendEdge C u v) (C.gates.length + 1) =
      ⟨GateOp.or, [C.output, n + C.gates.length]⟩ := by
  simp [gateAt, appendEdge, List.getD_eq_getElem?_getD]

lemma appendEdge_val_old {n : ℕ} (C : Circuit) (u v : Fin n) (x : Fin n → Bool)
    {w : ℕ} (hw : w < n + C.gates.length) :
    val (appendEdge C u v) (List.ofFn x) w = val C (List.ofFn x) w := by
  exact val_prefix (n := n) (C := C) (D := appendEdge C u v)
    (x := List.ofFn x) (m := C.gates.length) (by simp)
    le_rfl (by rw [appendEdge_length]; omega)
    (fun k hk => appendEdge_at_old C u v hk) w hw

lemma appendEdge_and {n : ℕ} (C : Circuit) (u v : Fin n) (x : Fin n → Bool) :
    gateVal n (appendEdge C u v) C.gates.length x = (x u && x v) := by
  change val (appendEdge C u v) (List.ofFn x) (n + C.gates.length) = _
  rw [val_gate (by simp) (by rw [appendEdge_length]; omega), appendEdge_at_and]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true, id_eq]
  rw [if_pos (by omega), if_pos (by omega), val_input (by simp) u.isLt,
    val_input (by simp) v.isLt]
  simp

lemma appendEdge_eval {n : ℕ} (C : Circuit) (u v : Fin n) (x : Fin n → Bool)
    (hout : C.output < n + C.gates.length) :
    circuitFun n (appendEdge C u v) x = (circuitFun n C x || (x u && x v)) := by
  change val (appendEdge C u v) (List.ofFn x) (n + (C.gates.length + 1)) = _
  rw [val_gate (by simp) (by rw [appendEdge_length]; omega), appendEdge_at_or]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    Bool.or_false, id_eq]
  rw [if_pos (by omega), if_pos (by omega), appendEdge_val_old C u v x hout]
  change (circuitFun n C x || gateVal n (appendEdge C u v) C.gates.length x) = _
  rw [appendEdge_and]

lemma appendEdge_mono {n : ℕ} (C : Circuit) (hC : Monotone2 C) (u v : Fin n) :
    Monotone2 (appendEdge C u v) := by
  intro g hg
  simp only [appendEdge, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | rfl | rfl
  · exact hC g hg
  · simp
  · simp

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : graphFun G ∅ x = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma protected_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) (x : Fin n → Bool) (hx : graphFun G ∅ x = false) :
    (x u && x v) = false := by
  cases h : x u && x v with
  | false => rfl
  | true =>
    have hh : x u = true ∧ x v = true := by simpa using h
    obtain ⟨hu, hv⟩ := hh
    have hf := (graph_true G x).mpr ⟨u,v,huv,hu,hv⟩
    rw [hx] at hf
    cases hf

lemma appendEdge_junk_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (huv : G.Adj u v) :
    (junk G (appendEdge C u v)).card ≤ (junk G C).card := by
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hkl, hop, _, x, hx, hxF⟩ := mem_junk.mp hk
  rw [appendEdge_length] at hkl
  have hkold : k < C.gates.length := by
    by_contra h
    have hcases : k = C.gates.length ∨ k = C.gates.length + 1 := by omega
    rcases hcases with rfl | rfl
    · rw [appendEdge_and] at hx
      have hh := protected_false G u v huv x hxF
      rw [hh] at hx
      cases hx
    · rw [appendEdge_at_or] at hop
      cases hop
  refine mem_junk.mpr ⟨hkold, ?_, hkold, x, ?_, hxF⟩
  · rwa [appendEdge_at_old C u v hkold] at hop
  · exact (appendEdge_val_old C u v x (by omega)).symm.trans hx


lemma bypass_output_lt {n : ℕ} {C : Circuit} {r i : ℕ}
    (hr : r < C.gates.length) (hi : i < n + r)
    (hout : C.output < n + C.gates.length) :
    (bypass n C r i).output < n + (bypass n C r i).gates.length := by
  rw [bypass_output, bypass_length]
  exact aliasWire_lt hi (by omega) (by omega)

lemma two_conditional_alias_repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C) (hF : circuitFun n C = graphFun G ∅)
    (j k p q : ℕ) (hjk : j < k) (hj : j ∈ junk G C) (hk : k ∈ junk G C)
    (hp : p < n + j) (hq : q < n + k)
    (u v : Fin n) (huv : G.Adj u v)
    (hjAlias : ∀ x : Fin n → Bool, (x u && x v) = false →
      val C (List.ofFn x) (n + j) = val C (List.ofFn x) p)
    (hkAlias : ∀ x : Fin n → Bool, (x u && x v) = false →
      val C (List.ofFn x) (n + k) = val C (List.ofFn x) q) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ (junk G D).card < (junk G C).card := by
  have hjlt := (mem_junk.mp hj).1
  have hklt := (mem_junk.mp hk).1
  let D1 := bypass n C k q
  let D2 := bypass n D1 j p
  let D := appendEdge D2 u v
  have hm1 : Monotone2 D1 := bypass_mono hC
  have hm2 : Monotone2 D2 := bypass_mono hm1
  have hlen1 : D1.gates.length = C.gates.length - 1 := bypass_length n C k q
  have hlen2 : D2.gates.length = D1.gates.length - 1 := bypass_length n D1 j p
  have hjlt1 : j < D1.gates.length := by omega
  have hjAlias1 (x : Fin n → Bool) (hx : (x u && x v) = false) :
      val D1 (List.ofFn x) (n + j) = val D1 (List.ofFn x) p := by
    rw [bypass_val_lt (by simp) hklt (n + j) (by omega),
      bypass_val_lt (by simp) hklt p (by omega)]
    exact hjAlias x hx
  have hj1 : j ∈ junk G D1 := by
    obtain ⟨_, hop, _, x, hx, hxF⟩ := mem_junk.mp hj
    refine mem_junk.mpr ⟨hjlt1, ?_, hjlt1, x, ?_, hxF⟩
    · change (gateAt (bypass n C k q) j).op = GateOp.and
      rw [gateAt_bypass (by omega), if_pos hjk]
      exact hop
    · change val D1 (List.ofFn x) (n + j) = true
      rw [bypass_val_lt (by simp) hklt (n + j) (by omega)]
      exact hx
  have hjunk1 : (junk G D1).card < (junk G C).card :=
    bypass_junk_lt G C hC k q hk hq
      (fun x hx => hkAlias x (protected_false G u v huv x hx))
  have hjunk2 : (junk G D2).card < (junk G D1).card :=
    bypass_junk_lt G D1 hm1 j p hj1 hp
      (fun x hx => hjAlias1 x (protected_false G u v huv x hx))
  have hcomputeOff (x : Fin n → Bool) (hx : (x u && x v) = false) :
      circuitFun n D2 x = graphFun G ∅ x := by
    change D2.eval (List.ofFn x) = _
    rw [bypass_eval_eq (by simp) (mono_ops hm1) hjlt1 (Or.inl hp) (hjAlias1 x hx)]
    rw [bypass_eval_eq (by simp) (mono_ops hC) hklt (Or.inl hq) (hkAlias x hx)]
    exact congrFun hF x
  have hout : C.output < n + C.gates.length := by
    by_contra hh
    have hv : circuitFun n C (pairInput u v) = false :=
      val_ge (n := n) (C := C) (x := List.ofFn (pairInput u v))
        (by simp) (by omega)
    rw [hF] at hv
    have ht : graphFun G ∅ (pairInput u v) = true :=
      (graph_true G _).mpr ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩
    rw [hv] at ht
    cases ht
  have hout1 : D1.output < n + D1.gates.length := bypass_output_lt hklt hq hout
  have hout2 : D2.output < n + D2.gates.length := bypass_output_lt hjlt1 hp hout1
  refine ⟨D, appendEdge_mono D2 hm2 u v, ?_, ?_, ?_⟩
  · funext x
    rw [appendEdge_eval D2 u v x hout2]
    cases hh : x u && x v with
    | false => rw [hcomputeOff x hh, Bool.or_false]
    | true =>
      rw [Bool.or_true]
      symm
      have he : x u = true ∧ x v = true := by simpa using hh
      exact (graph_true G x).mpr ⟨u,v,huv,he.1,he.2⟩
  · change (appendEdge D2 u v).gates.length ≤ C.gates.length
    rw [appendEdge_length, hlen2, hlen1]
    omega
  · exact lt_of_le_of_lt (appendEdge_junk_le G D2 u v huv) (hjunk2.trans hjunk1)

end PEqualNP.Outside.L_meta_1772_aux.protectedPatch

namespace PEqualNP.Outside.L_meta_1772_aux.prefixPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_1772_aux.clean
open PEqualNP.Outside.L_meta_1772_aux.protectedPatch

lemma delete_aliases {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C) (S : Finset ℕ) (rho : ℕ → ℕ)
    (hidx : ∀ j ∈ S, j < C.gates.length)
    (hearly : ∀ j ∈ S, rho j < n + j)
    (halias : ∀ j ∈ S, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (n + j) = val C (List.ofFn x) (rho j)) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = circuitFun n C ∧
      D.size + S.card ≤ C.size ∧ (junk G D).card ≤ (junk G C).card := by
  induction S using Finset.strongInductionOn generalizing C with
  | _ S ih =>
    by_cases hs : S.Nonempty
    · let r := S.max' hs
      have hr : r ∈ S := Finset.max'_mem S hs
      have hrlt := hidx r hr
      have hlow : ∀ j ∈ S.erase r, j < r := by
        intro j hj
        obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hj
        have hle : j ≤ r := Finset.le_max' S j hmem
        omega
      let C1 := bypass n C r (rho r)
      have hC1 : Monotone2 C1 := bypass_mono hC
      have hlen1 : C1.gates.length = C.gates.length - 1 := bypass_length n C r (rho r)
      have hidx1 : ∀ j ∈ S.erase r, j < C1.gates.length := by
        intro j hj; have := hlow j hj; omega
      have hearly1 : ∀ j ∈ S.erase r, rho j < n + j :=
        fun j hj => hearly j (Finset.mem_of_mem_erase hj)
      have halias1 : ∀ j ∈ S.erase r, ∀ x : Fin n → Bool,
          val C1 (List.ofFn x) (n + j) = val C1 (List.ofFn x) (rho j) := by
        intro j hj x
        have hjr := hlow j hj
        have hp := hearly1 j hj
        rw [bypass_val_lt (by simp) hrlt (n+j) (by omega),
          bypass_val_lt (by simp) hrlt (rho j) (by omega)]
        exact halias j (Finset.mem_of_mem_erase hj) x
      obtain ⟨D,hD,hfun,hsize,hjunk⟩ := ih (S.erase r) (Finset.erase_ssubset hr)
        C1 hC1 hidx1 hearly1 halias1
      refine ⟨D,hD,?_,?_,?_⟩
      · apply hfun.trans
        funext x
        exact bypass_eval_eq (by simp) (mono_ops hC) hrlt (Or.inl (hearly r hr)) (halias r hr x)
      · have hcard := Finset.card_erase_add_one hr
        change D.gates.length + (S.erase r).card ≤ C1.gates.length at hsize
        change D.gates.length + S.card ≤ C.gates.length
        omega
      · exact hjunk.trans ((bypass_junk_le G C hC r (rho r) hrlt (hearly r hr)
          (fun x _ => halias r hr x)).trans Finset.card_erase_le)
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst S
      exact ⟨C,hC,rfl,by simp,le_rfl⟩

def shiftWire (n t w : ℕ) : ℕ := if w < n then w else w + t

def replaceGate (n t : ℕ) (C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ) (j : ℕ) : Gate :=
  if j ∈ S then ⟨GateOp.or, [rho j]⟩
  else ⟨(gateAt C j).op, (gateAt C j).inputs.map (shiftWire n t)⟩

def extend (n : ℕ) (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ) : Circuit :=
  ⟨B.gates ++ (List.range C.gates.length).map (replaceGate n B.gates.length C S rho),
    shiftWire n B.gates.length C.output⟩

lemma extend_length (n : ℕ) (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ) :
    (extend n B C S rho).gates.length = B.gates.length + C.gates.length := by simp [extend]

lemma extend_prefix {n : ℕ} (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ) {j : ℕ}
    (hj : j < B.gates.length) : gateAt (extend n B C S rho) j = gateAt B j := by
  rw [gateAt_eq (by rw [extend_length]; omega), gateAt_eq hj]
  simp [extend, List.getElem_append_left hj]

lemma extend_at {n : ℕ} (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ) {j : ℕ}
    (hj : j < C.gates.length) : gateAt (extend n B C S rho) (B.gates.length+j) =
      replaceGate n B.gates.length C S rho j := by
  rw [gateAt_eq (by rw [extend_length]; omega)]
  change (B.gates ++ (List.range C.gates.length).map
    (replaceGate n B.gates.length C S rho))[B.gates.length+j]'
      (by simp; omega) = _
  rw [List.getElem_append_right (show B.gates.length ≤ B.gates.length+j by omega)]
  simp

lemma extend_val_prefix {n : ℕ} (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ)
    (x : Fin n → Bool) {w : ℕ} (hw : w < n+B.gates.length) :
    val (extend n B C S rho) (List.ofFn x) w = val B (List.ofFn x) w := by
  exact val_prefix (n := n) (C := B) (D := extend n B C S rho) (m := B.gates.length)
    (by simp) le_rfl (by rw [extend_length]; omega) (fun j hj => extend_prefix B C S rho hj) w hw

lemma extend_alias {n : ℕ} (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ)
    (x : Fin n → Bool) {j : ℕ} (hj : j < C.gates.length) (hjs : j ∈ S)
    (hr : rho j < n+B.gates.length) :
    val (extend n B C S rho) (List.ofFn x) (n+(B.gates.length+j)) =
      val B (List.ofFn x) (rho j) := by
  rw [val_gate (by simp) (by rw [extend_length]; omega), extend_at B C S rho hj]
  simp only [replaceGate, if_pos hjs, GateOp.eval, List.map_cons, List.map_nil,
    List.any_cons, List.any_nil, Bool.or_false, id_eq]
  rw [if_pos (by omega), extend_val_prefix B C S rho x hr]

lemma shift_lt {n t w j : ℕ} (hw : w < n+j) : shiftWire n t w < n+(t+j) := by
  unfold shiftWire; split_ifs <;> omega

lemma extend_relation {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ)
    (hC : Monotone2 C) (hRB : ReadsBack n C)
    (hidx : ∀ j ∈ S, j < C.gates.length) (hrho : ∀ j ∈ S, rho j < n+B.gates.length)
    (x : Fin n → Bool)
    (hrel : ∀ j ∈ S, R (val C (List.ofFn x) (n+j)) (val B (List.ofFn x) (rho j))) :
    ∀ w, R (val C (List.ofFn x) w)
      (val (extend n B C S rho) (List.ofFn x) (shiftWire n B.gates.length w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hin : w < n
    · rw [show shiftWire n B.gates.length w = w by simp [shiftWire, hin],
        val_input (by simp) hin, val_input (by simp) hin]
      exact hrefl _
    by_cases hout : n+C.gates.length ≤ w
    · rw [val_ge (n := n) (C := C) (x := List.ofFn x) (by simp) hout,
        val_ge (n := n) (C := extend n B C S rho) (x := List.ofFn x)
          (by simp) (by rw [extend_length]; simp only [shiftWire, if_neg hin]; omega)]
      exact hrefl _
    obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n, by omega⟩
    have hj : j<C.gates.length := by omega
    have hs : shiftWire n B.gates.length (n+j) = n+(B.gates.length+j) := by
      simp [shiftWire]; omega
    rw [hs]
    by_cases hjs : j∈S
    · rw [extend_alias B C S rho x hj hjs (hrho j hjs)]
      exact hrel j hjs
    · rw [val_gate (by simp) hj,
        val_gate (by simp) (by rw [extend_length]; omega), extend_at B C S rho hj]
      simp only [replaceGate, if_neg hjs, List.map_map]
      apply hmono _ (mono_ops hC j hj)
      intro a ha
      have hal := hRB j hj a ha
      simp only [Function.comp_apply, if_pos hal, if_pos (shift_lt (t := B.gates.length) hal)]
      exact ih a hal

lemma extend_mono {n : ℕ} (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ)
    (hB : Monotone2 B) (hC : Monotone2 C) : Monotone2 (extend n B C S rho) := by
  intro g hg
  simp only [extend, List.mem_append, List.mem_map, List.mem_range] at hg
  rcases hg with hg | ⟨j,hj,rfl⟩
  · exact hB g hg
  · unfold replaceGate
    split_ifs with h
    · simp
    · have hm := hC _ (gateAt_mem hj)
      simpa using hm

lemma opMono_reverse : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f h


lemma extend_computes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ)
    (hB : Monotone2 B) (hC : Monotone2 C) (hRB : ReadsBack n C)
    (hF : circuitFun n C = graphFun G ∅)
    (hidx : ∀ j ∈ S, j < C.gates.length) (hrho : ∀ j ∈ S, rho j < n+B.gates.length)
    (hpos : ∀ a b : Fin n, G.Adj a b → ∀ j ∈ S,
      gateVal n C j (pairInput a b) = true → val B (List.ofFn (pairInput a b)) (rho j) = true)
    (hneg : ∀ x : Fin n → Bool, graphFun G ∅ x = false → ∀ j ∈ S,
      val B (List.ofFn x) (rho j) = true → gateVal n C j x = true) :
    circuitFun n (extend n B C S rho) = graphFun G ∅ := by
  let D := extend n B C S rho
  have hD : Monotone2 D := extend_mono B C S rho hB hC
  have hEdge (a b : Fin n) (hab : G.Adj a b) : circuitFun n D (pairInput a b) = true := by
    have ht : circuitFun n C (pairInput a b) = true := by
      rw [hF]
      exact (protectedPatch.graph_true G _).mpr ⟨a,b,hab,by simp [pairInput],by simp [pairInput]⟩
    exact extend_relation (R := fun a b => a=true → b=true) (fun _ h => h) opMono_imp
      B C S rho hC hRB hidx hrho (pairInput a b) (hpos a b hab) C.output ht
  funext x
  cases hf : graphFun G ∅ x with
  | true =>
    obtain ⟨a,b,hab,ha,hb⟩ := (protectedPatch.graph_true G x).mp hf
    apply wire_monotone n D hD (pairInput a b) x ?_ D.output (hEdge a b hab)
    intro i hi
    simp only [pairInput, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl <;> assumption
  | false =>
    cases hd : circuitFun n D x with
    | false => rfl
    | true =>
      have hh : circuitFun n C x = true :=
        extend_relation (R := fun a b => b=true → a=true) (fun _ h => h) opMono_reverse
          B C S rho hC hRB hidx hrho x (hneg x hf) C.output hd
      rw [hF,hf] at hh
      cases hh

lemma extend_junk_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ)
    (hC : Monotone2 C) (hRB : ReadsBack n C)
    (hidx : ∀ j ∈ S, j < C.gates.length) (hrho : ∀ j ∈ S, rho j < n+B.gates.length)
    (hsafe : ∀ j < B.gates.length, (gateAt B j).op=GateOp.and → BelowF G B j)
    (hneg : ∀ x : Fin n → Bool, graphFun G ∅ x = false → ∀ j ∈ S,
      val B (List.ofFn x) (rho j) = true → gateVal n C j x = true) :
    (junk G (extend n B C S rho)).card ≤ (junk G C \ S).card := by
  let D := extend n B C S rho
  have hlarge : ∀ k ∈ junk G D, B.gates.length ≤ k := by
    intro k hk
    obtain ⟨hkl,hop,_,x,hx,hxF⟩ := mem_junk.mp hk
    by_contra h
    have hkp : k<B.gates.length := by omega
    have hopB : (gateAt B k).op=GateOp.and := by rwa [extend_prefix B C S rho hkp] at hop
    have hxB : gateVal n B k x=true := by
      exact (extend_val_prefix B C S rho x (by omega)).symm.trans hx
    have he := hsafe k hkp hopB x hxB
    rw [hxF] at he
    cases he
  apply Finset.card_le_card_of_injOn (fun k => k-B.gates.length)
  · intro k hk
    have hklow := hlarge k hk
    obtain ⟨hkl,hop,_,x,hx,hxF⟩ := mem_junk.mp hk
    have hlen : (extend n B C S rho).gates.length = B.gates.length+C.gates.length := extend_length n B C S rho
    let j := k-B.gates.length
    have hj : j<C.gates.length := by dsimp [j]; omega
    have hkj : k=B.gates.length+j := by dsimp [j]; omega
    have hnot : j∉S := by
      intro hjS
      rw [hkj, extend_at B C S rho hj] at hop
      simp [replaceGate,hjS] at hop
    have hopC : (gateAt C j).op=GateOp.and := by
      rw [hkj,extend_at B C S rho hj] at hop
      simpa [replaceGate,hnot] using hop
    refine Finset.mem_sdiff.mpr ⟨mem_junk.mpr ⟨hj,hopC,hj,x,?_,hxF⟩,hnot⟩
    have hr := extend_relation (R := fun a b => b=true → a=true)
      (fun _ h => h) opMono_reverse B C S rho hC hRB hidx hrho x (hneg x hxF) (n+j)
    have hs : shiftWire n B.gates.length (n+j)=n+k := by simp [shiftWire]; omega
    rw [hs] at hr
    exact hr hx
  · intro a ha b hb he
    have hla := hlarge a ha
    have hlb := hlarge b hb
    change a-B.gates.length=b-B.gates.length at he
    omega

lemma prefix_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ)
    (hB : Monotone2 B) (hC : Monotone2 C) (hRB : ReadsBack n C)
    (hF : circuitFun n C = graphFun G ∅)
    (hidx : ∀ j ∈ S, j < C.gates.length) (hrho : ∀ j ∈ S, rho j < n+B.gates.length)
    (hbudget : B.size ≤ S.card)
    (hsafe : ∀ j < B.gates.length, (gateAt B j).op=GateOp.and → BelowF G B j)
    (hpos : ∀ a b : Fin n, G.Adj a b → ∀ j ∈ S,
      gateVal n C j (pairInput a b) = true → val B (List.ofFn (pairInput a b)) (rho j) = true)
    (hneg : ∀ x : Fin n → Bool, graphFun G ∅ x = false → ∀ j ∈ S,
      val B (List.ofFn x) (rho j) = true → gateVal n C j x = true)
    (hdirty : ∃ j∈S, j∈junk G C) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ (junk G D).card < (junk G C).card := by
  let E := extend n B C S rho
  let T := S.image (fun j => B.gates.length+j)
  let sigma := fun k => rho (k-B.gates.length)
  have hE : Monotone2 E := extend_mono B C S rho hB hC
  have hidxT : ∀ k∈T, k<E.gates.length := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    rw [extend_length]
    have := hidx j hj
    omega
  have hearlyT : ∀ k∈T, sigma k<n+k := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    have := hrho j hj
    simp only [sigma,Nat.add_sub_cancel_left]
    omega
  have haliasT : ∀ k∈T, ∀ x : Fin n → Bool,
      val E (List.ofFn x) (n+k)=val E (List.ofFn x) (sigma k) := by
    intro k hk x
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    simp only [sigma,Nat.add_sub_cancel_left]
    rw [extend_alias B C S rho x (hidx j hj) hj (hrho j hj),
      extend_val_prefix B C S rho x (hrho j hj)]
  obtain ⟨D,hD,hDE,hsize,hjunk⟩ := delete_aliases G E hE T sigma hidxT hearlyT haliasT
  have hcard : T.card=S.card := Finset.card_image_of_injective S (by
    intro a b h
    change B.gates.length+a=B.gates.length+b at h
    omega)
  have hlen : E.gates.length=B.gates.length+C.gates.length := extend_length n B C S rho
  have hdrop : (junk G C \ S).card < (junk G C).card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset,?_⟩
    intro he
    obtain ⟨j,hjS,hjJ⟩ := hdirty
    have hjBoth : j∈junk G C \ S := he.symm ▸ hjJ
    exact (Finset.mem_sdiff.mp hjBoth).2 hjS
  refine ⟨D,hD,hDE.trans (extend_computes G B C S rho hB hC hRB hF hidx hrho hpos hneg),?_,?_⟩
  · change D.gates.length+T.card≤E.gates.length at hsize
    change B.gates.length≤S.card at hbudget
    change D.gates.length≤C.gates.length
    omega
  · exact lt_of_le_of_lt (hjunk.trans (extend_junk_le G B C S rho hC hRB hidx hrho hsafe hneg)) hdrop

end PEqualNP.Outside.L_meta_1772_aux.prefixPatch


namespace PEqualNP.Outside.L_meta_1772_aux.factorSubstitution

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

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

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

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩


open PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.FactorSubst

lemma reach_le {n : ℕ} {C : Circuit} {g : ℕ} :
    ∀ w, OrReaches n C w g → n + g ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    rw [orReaches_iff] at h
    rcases h.2 with h | ⟨_, i, _, hlt, hr⟩
    · omega
    · have := ih i hlt hr
      omega

end PEqualNP.Outside.L_meta_1772_aux.factorSubstitution

namespace PEqualNP.Outside.L_meta_1772_aux.prefixAnchor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_1772_aux.clean
open PEqualNP.Outside.L_meta_1772_aux.protectedPatch
open PEqualNP.Outside.L_meta_1772_aux.prefixPatch

lemma restore_anchor {n : ℕ} (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ)
    (l : ℕ) (hlS : l∈S) (hl : l<C.gates.length)
    (hmax : ∀ j∈S, j≤l) (hrho : rho l<n+B.gates.length)
    (x : Fin n → Bool) (htrue : val B (List.ofFn x) (rho l)=true) :
    ∀ w, OrReaches n C w l →
      val (extend n B C S rho) (List.ofFn x) (shiftWire n B.gates.length w)=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hp
    have hnw : n≤w := hp.1
    have hlw := factorSubstitution.reach_le w hp
    obtain ⟨k,rfl⟩ : ∃k, w=n+k := ⟨w-n,by omega⟩
    have hshift : shiftWire n B.gates.length (n+k)=n+(B.gates.length+k) := by
      simp [shiftWire]; omega
    rw [hshift]
    obtain ⟨hk,hpath⟩ := (factorSubstitution.orReaches_iff n C k l).mp hp
    rcases hpath with rfl | ⟨hop,i,hi,hilt,hip⟩
    · rw [extend_alias B C S rho x hl hlS hrho]
      exact htrue
    · by_cases hkl : k=l
      · subst k
        rw [extend_alias B C S rho x hl hlS hrho]
        exact htrue
      have hkn : k∉S := by intro h; have := hmax k h; omega
      rw [val_gate (by simp) (by rw [extend_length]; omega),extend_at B C S rho hk]
      simp only [replaceGate,if_neg hkn,hop,List.map_map,GateOp.eval,List.any_map,
        List.any_eq_true,Function.comp_apply,id_eq]
      refine ⟨i,hi,?_⟩
      rw [if_pos (shift_lt hilt)]
      exact ih i hilt hip

lemma extend_computes_anchored {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ) (l : ℕ)
    (hB : Monotone2 B) (hC : Monotone2 C) (hRB : ReadsBack n C)
    (hF : circuitFun n C=graphFun G ∅)
    (hidx : ∀j∈S,j<C.gates.length) (hrho : ∀j∈S,rho j<n+B.gates.length)
    (hlS : l∈S) (hmax : ∀j∈S,j≤l) (hpath : OrReaches n C C.output l)
    (hpos : ∀a b : Fin n, G.Adj a b →
      val B (List.ofFn (pairInput a b)) (rho l)=false → ∀j∈S,
      gateVal n C j (pairInput a b)=true → val B (List.ofFn (pairInput a b)) (rho j)=true)
    (hneg : ∀x : Fin n → Bool, graphFun G ∅ x=false → ∀j∈S,
      val B (List.ofFn x) (rho j)=true → gateVal n C j x=true) :
    circuitFun n (extend n B C S rho)=graphFun G ∅ := by
  let D := extend n B C S rho
  have hD : Monotone2 D := extend_mono B C S rho hB hC
  have hEdge (a b : Fin n) (hab : G.Adj a b) : circuitFun n D (pairInput a b)=true := by
    cases hp : val B (List.ofFn (pairInput a b)) (rho l) with
    | true =>
      exact restore_anchor B C S rho l hlS (hidx l hlS) hmax (hrho l hlS)
        (pairInput a b) hp C.output hpath
    | false =>
      have ht : circuitFun n C (pairInput a b)=true := by
        rw [hF]
        exact (protectedPatch.graph_true G _).mpr ⟨a,b,hab,by simp [pairInput],by simp [pairInput]⟩
      exact extend_relation (R := fun a b => a=true → b=true) (fun _ h => h) opMono_imp
        B C S rho hC hRB hidx hrho (pairInput a b) (hpos a b hab hp) C.output ht
  funext x
  cases hf : graphFun G ∅ x with
  | true =>
    obtain ⟨a,b,hab,ha,hb⟩ := (protectedPatch.graph_true G x).mp hf
    apply wire_monotone n D hD (pairInput a b) x ?_ D.output (hEdge a b hab)
    intro i hi
    simp only [pairInput,decide_eq_true_eq] at hi
    rcases hi with rfl | rfl <;> assumption
  | false =>
    cases hd : circuitFun n D x with
    | false => rfl
    | true =>
      have hh : circuitFun n C x=true :=
        extend_relation (R := fun a b => b=true → a=true) (fun _ h => h) prefixPatch.opMono_reverse
          B C S rho hC hRB hidx hrho x (hneg x hf) C.output hd
      rw [hF,hf] at hh
      cases hh

lemma prefix_replacement_anchored {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (S : Finset ℕ) (rho : ℕ → ℕ) (l : ℕ)
    (hB : Monotone2 B) (hC : Monotone2 C) (hRB : ReadsBack n C)
    (hF : circuitFun n C=graphFun G ∅)
    (hidx : ∀j∈S,j<C.gates.length) (hrho : ∀j∈S,rho j<n+B.gates.length)
    (hbudget : B.size≤S.card)
    (hsafe : ∀j<B.gates.length,(gateAt B j).op=GateOp.and → BelowF G B j)
    (hlS : l∈S) (hmax : ∀j∈S,j≤l) (hpath : OrReaches n C C.output l)
    (hpos : ∀a b : Fin n, G.Adj a b →
      val B (List.ofFn (pairInput a b)) (rho l)=false → ∀j∈S,
      gateVal n C j (pairInput a b)=true → val B (List.ofFn (pairInput a b)) (rho j)=true)
    (hneg : ∀x : Fin n → Bool, graphFun G ∅ x=false → ∀j∈S,
      val B (List.ofFn x) (rho j)=true → gateVal n C j x=true)
    (hdirty : ∃j∈S,j∈junk G C) :
    ∃D : Circuit, Monotone2 D ∧ circuitFun n D=graphFun G ∅ ∧
      D.size≤C.size ∧ (junk G D).card<(junk G C).card := by
  let E := extend n B C S rho
  let T := S.image (fun j => B.gates.length+j)
  let sigma := fun k => rho (k-B.gates.length)
  have hE : Monotone2 E := extend_mono B C S rho hB hC
  have hidxT : ∀k∈T,k<E.gates.length := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    rw [extend_length]
    have := hidx j hj
    omega
  have hearlyT : ∀k∈T,sigma k<n+k := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    have := hrho j hj
    simp only [sigma,Nat.add_sub_cancel_left]
    omega
  have haliasT : ∀k∈T,∀x : Fin n → Bool,
      val E (List.ofFn x) (n+k)=val E (List.ofFn x) (sigma k) := by
    intro k hk x
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    simp only [sigma,Nat.add_sub_cancel_left]
    rw [extend_alias B C S rho x (hidx j hj) hj (hrho j hj),
      extend_val_prefix B C S rho x (hrho j hj)]
  obtain ⟨D,hD,hDE,hsize,hjunk⟩ := delete_aliases G E hE T sigma hidxT hearlyT haliasT
  have hcard : T.card=S.card := Finset.card_image_of_injective S (by
    intro a b h
    change B.gates.length+a=B.gates.length+b at h
    omega)
  have hlen : E.gates.length=B.gates.length+C.gates.length := extend_length n B C S rho
  have hdrop : (junk G C \ S).card<(junk G C).card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset,?_⟩
    intro he
    obtain ⟨j,hjS,hjJ⟩ := hdirty
    have hjBoth : j∈junk G C \ S := he.symm ▸ hjJ
    exact (Finset.mem_sdiff.mp hjBoth).2 hjS
  refine ⟨D,hD,hDE.trans (extend_computes_anchored G B C S rho l hB hC hRB hF hidx hrho
    hlS hmax hpath hpos hneg),?_,?_⟩
  · change D.gates.length+T.card≤E.gates.length at hsize
    change B.gates.length≤S.card at hbudget
    change D.gates.length≤C.gates.length
    omega
  · exact lt_of_le_of_lt (hjunk.trans (extend_junk_le G B C S rho hC hRB hidx hrho hsafe hneg)) hdrop

end PEqualNP.Outside.L_meta_1772_aux.prefixAnchor

namespace PEqualNP.Outside.L_meta_1772_aux.anchorPath

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_1772_aux.clean

lemma orReach_cone {n : ℕ} (C : Circuit) (l : ℕ) :
    ∀k, OrReaches n C (n+k) l → l=k ∨ InCone n C l k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hp
    obtain ⟨hk,hp⟩ := (factorSubstitution.orReaches_iff n C k l).mp hp
    rcases hp with he | ⟨_,i,hi,hilt,hip⟩
    · exact Or.inl he
    have hni : n ≤ i := hip.1
    obtain ⟨r,rfl⟩ : ∃r,i=n+r := ⟨i-n,by omega⟩
    exact Or.inr ((factorSubstitution.inCone_iff n C l k).mpr
      ⟨hk,r,by omega,hi,ih r (by omega) hip⟩)

lemma safe_anchor_or_path {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hmin : IsMinimalMonoCircuit n C) (htop : TopForm G C)
    (l : ℕ) (hl : l<C.gates.length) (hop : (gateAt C l).op=GateOp.and)
    (hsafe : BelowF G C l) : OrReaches n C C.output l := by
  classical
  let R := (Finset.range C.gates.length).filter (fun k => OrReaches n C (n+k) l)
  have hlR : l∈R := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hl,?_⟩
    exact (factorSubstitution.orReaches_iff n C l l).mpr ⟨hl,Or.inl rfl⟩
  have hR : R.Nonempty := ⟨l,hlR⟩
  let m := R.max' hR
  have hmR : m∈R := Finset.max'_mem R hR
  obtain ⟨hml,hmp⟩ := Finset.mem_filter.mp hmR
  have hm : m<C.gates.length := Finset.mem_range.mp hml
  by_cases hout : C.output=n+m
  · rw [hout]
    exact hmp
  obtain ⟨k,hmk,hk,hread⟩ := minimal_gate_has_reader hmin hm hout
  have hcone : InCone n C l k :=
    (factorSubstitution.inCone_iff n C l k).mpr ⟨hk,m,hmk,hread,orReach_cone C l m hmp⟩
  have hkor : (gateAt C k).op=GateOp.or := by
    rcases mono_ops hmin.1 k hk with hand | hor
    · exact (htop l hl k hk hop hsafe hand hcone).elim
    · exact hor
  have hkR : k∈R := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hk,?_⟩
    exact (factorSubstitution.orReaches_iff n C k l).mpr
      ⟨hk,Or.inr ⟨hkor,n+m,hread,by omega,hmp⟩⟩
  have hkm : k ≤ m := Finset.le_max' R k hkR
  omega

end PEqualNP.Outside.L_meta_1772_aux.anchorPath
