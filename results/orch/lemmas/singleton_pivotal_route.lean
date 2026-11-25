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

namespace PEqualNP.Outside.L_meta_1772_aux.singletonPivotal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.Outside.L_meta_1772_aux.clean

lemma underapprox_lost_edge (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : IsMinimalMonoCircuit n C) (hf : circuitFun n C = graphFun G ∅)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hweak : ∀ x : Fin n → Bool,
      val C (List.ofFn x) i = true → val C (List.ofFn x) (n+r) = true) :
    ∃ u v : Fin n, G.Adj u v ∧
      gateVal n C r (pairInput u v) = true ∧
      val C (List.ofFn (pairInput u v)) i = false ∧
      circuitFun n (bypass n C r i) (pairInput u v) = false := by
  let D := bypass n C r i
  have hD : Monotone2 D := bypass_mono hm.1
  have hle (x : Fin n → Bool) : D.eval (List.ofFn x) = true → C.eval (List.ofFn x) = true := by
    apply bypass_eval_rel (R := fun a b => b = true → a = true) (fun _ => id) opMono_reverse
      (n := n) (C := C) (by simp) (mono_ops hm.1) hr hi
    exact hweak x
  have existsLost : ∃ u v : Fin n, G.Adj u v ∧ D.eval (List.ofFn (pairInput u v)) = false := by
    by_contra hn
    have hpairs (u v : Fin n) (huv : G.Adj u v) : D.eval (List.ofFn (pairInput u v)) = true := by
      cases h : D.eval (List.ofFn (pairInput u v))
      · exact (hn ⟨u, v, huv, h⟩).elim
      · rfl
    have heq : circuitFun n D = circuitFun n C := by
      funext x
      apply Bool.eq_iff_iff.mpr
      constructor
      · exact hle x
      · intro hx
        have hx' : graphFun G ∅ x = true := by rw [← hf]; exact hx
        obtain ⟨u, v, huv, hux, hvx⟩ := (graph_true G x).mp hx'
        apply circuit_monotone n D hD (pairInput u v) x (fun k hk => ?_) (hpairs u v huv)
        have hk' : k = u ∨ k = v := by simpa [pairInput] using hk
        rcases hk' with rfl | rfl
        · exact hux
        · exact hvx
    have hs := hm.2 D hD heq
    have hl : D.size = C.gates.length - 1 := bypass_length n C r i
    change C.gates.length ≤ D.size at hs
    omega
  obtain ⟨u, v, huv, hfalse⟩ := existsLost
  have htrue : C.eval (List.ofFn (pairInput u v)) = true := by
    change circuitFun n C _ = true
    rw [hf]
    exact pair_true G u v huv
  have hne : val C (List.ofFn (pairInput u v)) (n+r) ≠ val C (List.ofFn (pairInput u v)) i := by
    intro heq
    have hh := bypass_eval_eq (n := n) (by simp) (mono_ops hm.1) hr hi heq
    rw [htrue] at hh
    change D.eval (List.ofFn (pairInput u v)) = true at hh
    rw [hfalse] at hh
    cases hh
  have hg : val C (List.ofFn (pairInput u v)) (n+r) = true := by
    cases he : val C (List.ofFn (pairInput u v)) (n+r)
    · cases he' : val C (List.ofFn (pairInput u v)) i
      · exact False.elim (hne (he.trans he'.symm))
      · have ht := hweak (pairInput u v) he'
        rw [he] at ht
        cases ht
    · rfl
  have hir : val C (List.ofFn (pairInput u v)) i = false := by
    cases he : val C (List.ofFn (pairInput u v)) i
    · rfl
    · exact False.elim (hne (hg.trans he.symm))
  exact ⟨u, v, huv, hg, hir, hfalse⟩

lemma singleton_true_has_disjoint_pivotal (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : IsMinimalMonoCircuit n C) (hf : circuitFun n C = graphFun G ∅)
    (r : ℕ) (hr : r < C.gates.length) (z : Fin n)
    (hz : gateVal n C r (pairInput z z) = true) :
    ∃ u v : Fin n, G.Adj u v ∧ u ≠ z ∧ v ≠ z ∧
      gateVal n C r (pairInput u v) = true ∧
      circuitFun n (PEqualNP.CircuitMoves.eraseGate n C r z.val) (pairInput u v) = false := by
  have hweak (x : Fin n → Bool) :
      val C (List.ofFn x) z.val = true → val C (List.ofFn x) (n+r) = true := by
    intro hzx
    have hxz : x z = true := by
      rw [val_input (n := n) (by simp) z.isLt] at hzx
      simpa using hzx
    apply wire_monotone n C hm.1 (pairInput z z) x ?_ (n+r) hz
    intro w hw
    simp only [pairInput, decide_eq_true_eq, or_self] at hw
    simpa [hw] using hxz
  obtain ⟨u, v, huv, hg, hzfalse, hb⟩ := underapprox_lost_edge n G C hm hf r z.val hr
    (Or.inl (by omega)) hweak
  have hs : pairInput u v z = false := by
    rw [val_input (n := n) (by simp) z.isLt] at hzfalse
    simpa using hzfalse
  have hends : z ≠ u ∧ z ≠ v := by
    simpa [pairInput] using hs
  refine ⟨u, v, huv, hends.1.symm, hends.2.symm, hg, ?_⟩
  rw [erase_eq_bypass n C r z.val hr]
  exact hb

end PEqualNP.Outside.L_meta_1772_aux.singletonPivotal
