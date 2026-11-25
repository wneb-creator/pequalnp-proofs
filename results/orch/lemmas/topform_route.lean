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

namespace PEqualNP.Outside.L_meta_1772_aux.topform

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

lemma isAndOp_eq_true_iff (op : GateOp) : isAndOp op = true ↔ op = GateOp.and := by
  cases op <;> simp [isAndOp]

def andIndexSum (C : Circuit) : ℕ :=
  ∑ k ∈ (Finset.range C.gates.length).filter (fun k => isAndOp (gateAt C k).op = true), k

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

lemma wireVal_append_lt (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + C.gates.length) :
    wireVal n ⟨C.gates ++ [g], out⟩ w x = wireVal n C w x := by
  unfold wireVal Circuit.wires
  change ((C.gates ++ [g]).foldl wireStep (List.ofFn x)).getD w false =
    (C.gates.foldl wireStep (List.ofFn x)).getD w false
  rw [List.foldl_append]
  have hw' : w < (C.gates.foldl wireStep (List.ofFn x)).length := by
    rw [foldl_wireStep_length, List.length_ofFn]
    exact hw
  exact foldl_wireStep_prefix [g] (C.gates.foldl wireStep (List.ofFn x)) w hw'

lemma wireVal_append_last (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ) (x : Fin n → Bool) :
    wireVal n ⟨C.gates ++ [g], out⟩ (n + C.gates.length) x =
      g.op.eval (g.inputs.map fun u => wireVal n C u x) := by
  unfold wireVal Circuit.wires
  change ((C.gates ++ [g]).foldl wireStep (List.ofFn x)).getD (n + C.gates.length) false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  set acc := C.gates.foldl wireStep (List.ofFn x) with hacc
  have hlen : acc.length = n + C.gates.length := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn]
  rw [List.getD_eq_getElem?_getD]
  simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + C.gates.length),
    hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rfl

lemma output_lt_of_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hE : G.edgeFinset.Nonempty) (hF : circuitFun n C = graphFun G ∅) :
    C.output < n + C.gates.length := by
  by_contra hge
  push Not at hge
  obtain ⟨e, he⟩ := hE
  induction e using Sym2.ind with
  | _ u v =>
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
    have htrue : graphFun G ∅ (fun _ => true) = true := by
      unfold graphFun
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_eq]
      exact ⟨u, v, hadj, rfl, rfl⟩
    have hfalse : circuitFun n C (fun _ => true) = false := by
      unfold circuitFun Circuit.eval
      rw [List.getD_eq_getElem?_getD]
      have hlen : (C.wires (List.ofFn (fun _ : Fin n => true))).length = n + C.gates.length := by
        rw [wires_length, List.length_ofFn]
      rw [List.getElem?_eq_none (by omega)]
      rfl
    have hEq := congrFun hF (fun _ => true)
    rw [hfalse, htrue] at hEq
    cases hEq

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

lemma exists_direct_reader (n : ℕ) (C : Circuit) (i j : ℕ)
    (hj : j < C.gates.length) (h : InCone n C i j) :
    ∃ g, i < g ∧ g ≤ j ∧ g < C.gates.length ∧ n + i ∈ (gateAt C g).inputs := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [inCone_iff n C i j hj] at h
    obtain ⟨w, hw, hnw, hlt, hcase⟩ := h
    rcases hcase with rfl | hcone
    · refine ⟨j, by omega, le_refl j, hj, ?_⟩
      have heq : n + (w - n) = w := by omega
      rw [heq]
      exact hw
    · have hklt : w - n < j := by omega
      obtain ⟨g, hig, hgk, hglen, hmem⟩ := ih (w - n) hklt (by omega) hcone
      exact ⟨g, hig, by omega, hglen, hmem⟩

def remap (n g r w : ℕ) : ℕ :=
  if w < n + g then w
  else if w = n + g then r
  else w - 1

def origWire (n g w : ℕ) : ℕ :=
  if w < n + g then w else w + 1

def mapGate (f : ℕ → ℕ) (gt : Gate) : Gate :=
  ⟨gt.op, gt.inputs.map f⟩

def delGate (n g r : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx g).map (mapGate (remap n g r)), remap n g r C.output⟩

lemma delGate_length (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length) :
    (delGate n g r C).gates.length = C.gates.length - 1 := by
  simp [delGate, List.length_eraseIdx_of_lt hg]

lemma delGate_gateAt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (delGate n g r C) k =
      mapGate (remap n g r) (gateAt C (if k < g then k else k + 1)) := by
  have hk' : k < (delGate n g r C).gates.length := by
    rw [delGate_length n g r C hg]; exact hk
  rw [gateAt_eq_getElem (delGate n g r C) k hk']
  have hk_e : k < (C.gates.eraseIdx g).length := by
    rw [List.length_eraseIdx_of_lt hg]; exact hk
  simp only [delGate, List.getElem_map]
  split_ifs with hkg
  · rw [List.getElem_eraseIdx_of_lt hk_e hkg, gateAt_eq_getElem C k (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hk_e (by omega), gateAt_eq_getElem C (k + 1) (by omega)]

lemma delGate_isAO2 (n g r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hg : g < C.gates.length) (hr : r < n + g) :
    IsAO2 n (delGate n g r C) := by
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    exact hAOOnly gt0 (List.mem_of_mem_eraseIdx hgt0)
  · intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap
      split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap
      split_ifs <;> omega
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    simp only [mapGate, List.length_map]
    exact hLen2 gt0 (List.mem_of_mem_eraseIdx hgt0)

lemma delGate_output_lt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (hr : r < n + g) (hout : C.output < n + C.gates.length) :
    (delGate n g r C).output < n + (delGate n g r C).gates.length := by
  rw [delGate_length n g r C hg]
  simp only [delGate, remap]
  split_ifs <;> omega

lemma origWire_remap_ne (n g r u : ℕ) (hne : u ≠ n + g) :
    origWire n g (remap n g r u) = u := by
  unfold origWire remap
  split_ifs <;> omega

lemma origWire_remap_eq (n g r : ℕ) (hr : r < n + g) :
    origWire n g (remap n g r (n + g)) = r := by
  unfold origWire remap
  split_ifs <;> omega

lemma delGate_wireVal_eq (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmatch : wireVal n C (n + g) x = wireVal n C r x) :
    ∀ w < n + (delGate n g r C).gates.length,
      wireVal n (delGate n g r C) w x = wireVal n C (origWire n g w) x := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn]
      have horig : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [horig, wireVal_input n C x w hwn]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hk_lt' : k < C.gates.length - 1 := by
        rw [← delGate_length n g r C hg]; exact hk_lt
      rw [hw_eq, wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k hk_lt']
      set k0 := if k < g then k else k + 1 with hk0_def
      have hk0_lt : k0 < C.gates.length := by
        rw [hk0_def]; split_ifs <;> omega
      have horig : origWire n g (n + k) = n + k0 := by
        unfold origWire; rw [hk0_def]; split_ifs <;> omega
      rw [horig, wireVal_gate n C x k0 hk0_lt hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt']
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu, rfl⟩
        exact hAO_rb k hk_lt (remap n g r u) h1
      have hih := ih (remap n g r u) (by omega) (by omega)
      simp only [Function.comp_apply, hih]
      by_cases hug : u = n + g
      · rw [hug, origWire_remap_eq n g r hr, hmatch]
      · rw [origWire_remap_ne n g r u hug]

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hmono : ∀ p (hp1 : p < l1.length) (hp2 : p < l2.length), l1[p] = true → l2[p] = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · intro h1
    simp only [GateOp.eval, List.all_eq_true, id_eq] at h1 ⊢
    intro b hb
    rw [List.mem_iff_getElem] at hb
    obtain ⟨p, hp2, rfl⟩ := hb
    have hp1 : p < l1.length := by omega
    exact hmono p hp1 hp2 (h1 l1[p] (List.getElem_mem hp1))
  · intro h1
    simp only [GateOp.eval, List.any_eq_true, id_eq] at h1 ⊢
    obtain ⟨b, hb, rfl⟩ := h1
    rw [List.mem_iff_getElem] at hb
    obtain ⟨p, hp1, hbp⟩ := hb
    have hp2 : p < l2.length := by omega
    exact ⟨l2[p], List.getElem_mem hp2, hmono p hp1 hp2 hbp⟩

lemma delGate_wireVal_mono (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAOOnly : AndOrOnly C) (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmono_g : wireVal n C (n + g) x = true → wireVal n C r x = true) :
    ∀ w < n + (delGate n g r C).gates.length,
      wireVal n C (origWire n g w) x = true → wireVal n (delGate n g r C) w x = true := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn]
      have horig : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [horig, wireVal_input n C x w hwn] at htrue
      exact htrue
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hk_lt' : k < C.gates.length - 1 := by
        rw [← delGate_length n g r C hg]; exact hk_lt
      rw [hw_eq] at htrue ⊢
      rw [wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k hk_lt']
      set k0 := if k < g then k else k + 1 with hk0_def
      have hk0_lt : k0 < C.gates.length := by
        rw [hk0_def]; split_ifs <;> omega
      have horig : origWire n g (n + k) = n + k0 := by
        unfold origWire; rw [hk0_def]; split_ifs <;> omega
      rw [horig, wireVal_gate n C x k0 hk0_lt hRB] at htrue
      simp only [mapGate, List.map_map]
      have hop : (gateAt C k0).op = GateOp.and ∨ (gateAt C k0).op = GateOp.or := by
        rw [gateAt_eq_getElem C k0 hk0_lt]
        exact hAOOnly C.gates[k0] (List.getElem_mem hk0_lt)
      apply gateOp_eval_mono (gateAt C k0).op hop _ _ (by simp) _ htrue
      intro p hp1 hp2 hv
      simp only [List.getElem_map, Function.comp_apply] at hv ⊢
      set u := (gateAt C k0).inputs[p]'(by simpa using hp1) with hu_def
      have hu_mem : u ∈ (gateAt C k0).inputs := List.getElem_mem (by simpa using hp1)
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt']
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu_mem, rfl⟩
        exact hAO_rb k hk_lt (remap n g r u) h1
      apply ih (remap n g r u) (by omega) (by omega)
      by_cases hug : u = n + g
      · rw [hug, origWire_remap_eq n g r hr]
        rw [hug] at hv
        exact hmono_g hv
      · rw [origWire_remap_ne n g r u hug]
        exact hv

lemma delGate_wireVal_prefix_eq (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g) :
    ∀ w < n + g, wireVal n (delGate n g r C) w x = wireVal n C w x := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn, wireVal_input n C x w hwn]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hkg : k < g := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by
        rw [delGate_length n g r C hg]; omega
      rw [hw_eq, wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k (by omega)]
      simp only [hkg, ↓reduceIte]
      rw [wireVal_gate n C x k (by omega) hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu_lt : u < n + k := hRB k (by omega) u hu
      have hrm : remap n g r u = u := by unfold remap; split_ifs <;> omega
      simp only [Function.comp_apply, hrm]
      exact ih u (by omega) (by omega)

lemma no_and_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (i g : ℕ)
    (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hig : i < g) (hg : g < C.gates.length)
    (hBelow : BelowF G C i)
    (hgAnd : (gateAt C g).op = GateOp.and)
    (hmem : n + i ∈ (gateAt C g).inputs) : False := by
  rcases hL with ⟨hAO, hF, hMin⟩
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  have hout : C.output < n + C.gates.length := output_lt_of_nonempty G C hE hF
  set C' := delGate n g (n + i) C with hC'
  have hAO' : IsAO2 n C' := delGate_isAO2 n g (n + i) C ⟨hAOOnly, hRB, hLen2⟩ hg (by omega)
  have hout' : C'.output < n + C'.gates.length :=
    delGate_output_lt n g (n + i) C hg (by omega) hout
  have hF' : circuitFun n C' = graphFun G ∅ := by
    funext x
    have hmono_g : wireVal n C (n + g) x = true → wireVal n C (n + i) x = true := by
      intro hg_true
      rw [wireVal_gate n C x g hg hRB, hgAnd] at hg_true
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hg_true
      exact hg_true (wireVal n C (n + i) x) ⟨n + i, hmem, rfl⟩
    cases hgx : graphFun G ∅ x
    · have hi_false : wireVal n C (n + i) x = false := by
        cases hvi : wireVal n C (n + i) x with
        | false => rfl
        | true =>
          have := hBelow x hvi
          rw [hgx] at this
          cases this
      have hg_false : wireVal n C (n + g) x = false := by
        cases hvg : wireVal n C (n + g) x with
        | false => rfl
        | true =>
          have := hmono_g hvg
          rw [hi_false] at this
          cases this
      have hmatch : wireVal n C (n + g) x = wireVal n C (n + i) x := by
        rw [hg_false, hi_false]
      have hval := delGate_wireVal_eq n g (n + i) C x hRB hg (by omega) hmatch C'.output hout'
      have hcf : circuitFun n C' x = wireVal n C' C'.output x := rfl
      rw [hcf, hval]
      have hcfC : circuitFun n C x = false := by rw [hF, hgx]
      by_cases ho : C.output = n + g
      · simp only [hC', delGate]
        rw [ho, origWire_remap_eq n g (n + i) (by omega), ← hmatch]
        change wireVal n C (n + g) x = false
        rw [← ho]
        exact hcfC
      · simp only [hC', delGate]
        rw [origWire_remap_ne n g (n + i) C.output ho]
        exact hcfC
    · have hcfC : wireVal n C C.output x = true := by
        change circuitFun n C x = true
        rw [hF, hgx]
      have hval := delGate_wireVal_mono n g (n + i) C x hAOOnly hRB hg (by omega) hmono_g
        C'.output hout'
      change wireVal n C' C'.output x = true
      apply hval
      by_cases ho : C.output = n + g
      · simp only [hC', delGate]
        rw [ho, origWire_remap_eq n g (n + i) (by omega)]
        rw [ho] at hcfC
        exact hmono_g hcfC
      · simp only [hC', delGate]
        rw [origWire_remap_ne n g (n + i) C.output ho]
        exact hcfC
  have hle := hMin C' hAO' hF'
  have hsz : C'.size = C.size - 1 := delGate_length n g (n + i) C hg
  change C.gates.length ≤ C'.gates.length at hle
  rw [show C'.gates.length = C.gates.length - 1 from hsz] at hle
  omega

def pushOr (n g y i : ℕ) (C : Circuit) : Circuit :=
  let Cmid := delGate n g y C
  ⟨Cmid.gates ++ [⟨GateOp.or, [Cmid.output, n + i]⟩], n + Cmid.gates.length⟩

def shiftDown (g k : ℕ) : ℕ :=
  if k < g then k else k - 1

lemma pushOr_step {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (i g j : ℕ)
    (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hig : i < g) (hgj : g < j) (hj : j < C.gates.length)
    (hBelow : BelowF G C i)
    (hgOr : (gateAt C g).op = GateOp.or)
    (hjAnd : (gateAt C j).op = GateOp.and)
    (hmem : n + i ∈ (gateAt C g).inputs) :
    ∃ C' : Circuit, IsLeastAO G C' ∧ C'.size = C.size ∧
      (junk G C').card = (junk G C).card ∧ andIndexSum C' < andIndexSum C := by
  rcases hL with ⟨hAO, hF, hMin⟩
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  have hg : g < C.gates.length := by omega
  have hout : C.output < n + C.gates.length := output_lt_of_nonempty G C hE hF
  have hgin_len : (gateAt C g).inputs.length = 2 := by
    rw [gateAt_eq_getElem C g hg]
    exact hLen2 C.gates[g] (List.getElem_mem hg)
  rcases hgin : (gateAt C g).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · simp [hgin] at hgin_len
  · simp [hgin] at hgin_len
  · have hmem' : n + i = a ∨ n + i = b := by
      simpa [hgin] using hmem
    set y := if a = n + i then b else a with hy_def
    have hy_mem : y ∈ (gateAt C g).inputs := by
      rw [hgin, hy_def]
      split_ifs <;> simp
    have hy_lt : y < n + g := hRB g hg y hy_mem
    have hg_eval : ∀ x : Fin n → Bool,
        wireVal n C (n + g) x = (wireVal n C (n + i) x || wireVal n C y x) := by
      intro x
      rw [wireVal_gate n C x g hg hRB, hgOr, hgin]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      rw [hy_def]
      split_ifs with ha
      · rw [ha]
      · rcases hmem' with rfl | rfl
        · exact absurd rfl ha
        · exact Bool.or_comm _ _
    set Cmid := delGate n g y C with hCmid
    set C' := pushOr n g y i C with hC'
    have hCmid_len : Cmid.gates.length = C.gates.length - 1 := delGate_length n g y C hg
    have hC'_len : C'.gates.length = C.gates.length := by
      simp only [hC', pushOr, List.length_append, List.length_singleton, ← hCmid, hCmid_len]
      omega
    have hCmid_AO : IsAO2 n Cmid := delGate_isAO2 n g y C ⟨hAOOnly, hRB, hLen2⟩ hg hy_lt
    have hCmid_out : Cmid.output < n + Cmid.gates.length :=
      delGate_output_lt n g y C hg hy_lt hout
    have hC'_AO : IsAO2 n C' := by
      rcases hCmid_AO with ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, ?_⟩
      · intro gt hgt
        simp only [hC', pushOr, ← hCmid, List.mem_append, List.mem_singleton] at hgt
        rcases hgt with hgt | rfl
        · exact h1 gt hgt
        · exact Or.inr rfl
      · intro k hk w hw
        have hk' : k < Cmid.gates.length + 1 := by
          simpa [hC', pushOr, ← hCmid] using hk
        by_cases hkm : k < Cmid.gates.length
        · have hgat : gateAt C' k = gateAt Cmid k := by
            rw [gateAt_eq_getElem C' k hk, gateAt_eq_getElem Cmid k hkm]
            simp [hC', pushOr, ← hCmid, List.getElem_append_left hkm]
          rw [hgat] at hw
          exact h2 k hkm w hw
        · have hkeq : k = Cmid.gates.length := by omega
          have hgat : gateAt C' k = ⟨GateOp.or, [Cmid.output, n + i]⟩ := by
            rw [gateAt_eq_getElem C' k hk]
            simp [hC', pushOr, ← hCmid, hkeq]
          rw [hgat] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · omega
          · rw [hkeq, hCmid_len]; omega
      · intro gt hgt
        simp only [hC', pushOr, ← hCmid, List.mem_append, List.mem_singleton] at hgt
        rcases hgt with hgt | rfl
        · exact h3 gt hgt
        · rfl
    have hC'_F : circuitFun n C' = graphFun G ∅ := by
      funext x
      have hlast : circuitFun n C' x =
          (wireVal n Cmid Cmid.output x || wireVal n Cmid (n + i) x) := by
        change wireVal n C' (n + Cmid.gates.length) x = _
        have h := wireVal_append_last n Cmid ⟨GateOp.or, [Cmid.output, n + i]⟩
          (n + Cmid.gates.length) x
        simpa [hC', pushOr, ← hCmid, GateOp.eval] using h
      rw [hlast]
      have hni : wireVal n Cmid (n + i) x = wireVal n C (n + i) x :=
        delGate_wireVal_prefix_eq n g y C x hRB hg hy_lt (n + i) (by omega)
      rw [hni]
      cases hvi : wireVal n C (n + i) x
      · have hmatch : wireVal n C (n + g) x = wireVal n C y x := by
          rw [hg_eval x, hvi, Bool.false_or]
        have hval := delGate_wireVal_eq n g y C x hRB hg hy_lt hmatch Cmid.output hCmid_out
        rw [hval, Bool.or_false]
        have hcfC : wireVal n C C.output x = graphFun G ∅ x := congrFun hF x
        by_cases ho : C.output = n + g
        · simp only [hCmid, delGate]
          rw [ho, origWire_remap_eq n g y hy_lt, ← hmatch, ← ho]
          exact hcfC
        · simp only [hCmid, delGate]
          rw [origWire_remap_ne n g y C.output ho]
          exact hcfC
      · rw [Bool.or_true]
        exact (hBelow x hvi).symm
    have hC'_Least : IsLeastAO G C' := by
      refine ⟨hC'_AO, hC'_F, ?_⟩
      intro D hDAO hDF
      have hle := hMin D hDAO hDF
      change C'.gates.length ≤ D.gates.length
      rw [hC'_len]
      exact hle
    have hgateAt_lt : ∀ m < Cmid.gates.length,
        gateAt C' m = gateAt Cmid m := by
      intro m hm
      have hm' : m < C'.gates.length := by rw [hC'_len]; omega
      rw [gateAt_eq_getElem C' m hm', gateAt_eq_getElem Cmid m hm]
      simp [hC', pushOr, ← hCmid, List.getElem_append_left hm]
    have hgateAt_last : gateAt C' Cmid.gates.length = ⟨GateOp.or, [Cmid.output, n + i]⟩ := by
      have hm' : Cmid.gates.length < C'.gates.length := by rw [hC'_len]; omega
      rw [gateAt_eq_getElem C' Cmid.gates.length hm']
      simp [hC', pushOr, ← hCmid]
    have hop_shift : ∀ k < C.gates.length, k ≠ g →
        (gateAt C' (shiftDown g k)).op = (gateAt C k).op := by
      intro k hk hne
      have hsd : shiftDown g k < Cmid.gates.length := by
        unfold shiftDown; rw [hCmid_len]; split_ifs <;> omega
      rw [hgateAt_lt (shiftDown g k) hsd]
      rw [hCmid, delGate_gateAt n g y C hg (shiftDown g k) (by omega)]
      simp only [mapGate]
      have hidx : (if shiftDown g k < g then shiftDown g k else shiftDown g k + 1) = k := by
        unfold shiftDown; split_ifs <;> omega
      rw [hidx]
    have hval_false : ∀ k < C.gates.length, k ≠ g → ∀ x : Fin n → Bool,
        graphFun G ∅ x = false →
        gateVal n C' (shiftDown g k) x = gateVal n C k x := by
      intro k hk hne x hgx
      have hsd : shiftDown g k < Cmid.gates.length := by
        unfold shiftDown; rw [hCmid_len]; split_ifs <;> omega
      have hi_false : wireVal n C (n + i) x = false := by
        cases hvi : wireVal n C (n + i) x with
        | false => rfl
        | true =>
          have := hBelow x hvi
          rw [hgx] at this
          cases this
      have hmatch : wireVal n C (n + g) x = wireVal n C y x := by
        rw [hg_eval x, hi_false, Bool.false_or]
      have happ : wireVal n C' (n + shiftDown g k) x = wireVal n Cmid (n + shiftDown g k) x :=
        wireVal_append_lt n Cmid ⟨GateOp.or, [Cmid.output, n + i]⟩ (n + Cmid.gates.length) x
          (n + shiftDown g k) (by omega)
      have heq := delGate_wireVal_eq n g y C x hRB hg hy_lt hmatch
        (n + shiftDown g k) (by rw [← hCmid]; omega)
      have horig : origWire n g (n + shiftDown g k) = n + k := by
        unfold origWire shiftDown
        split_ifs <;> omega
      change wireVal n C' (n + shiftDown g k) x = wireVal n C (n + k) x
      rw [happ, hCmid, heq, horig]
    have hjunk : (junk G C').card = (junk G C).card := by
      symm
      apply Finset.card_bij (fun k _ => shiftDown g k)
      · intro k hk
        unfold junk gatesWhere at hk ⊢
        rw [Finset.mem_filter, Finset.mem_range] at hk ⊢
        rcases hk with ⟨hk_lt, hk_and, _, x, hkx, hgx⟩
        have hkne : k ≠ g := by
          intro hEq; rw [hEq, hgOr] at hk_and; cases hk_and
        have hsd_lt : shiftDown g k < C'.gates.length := by
          unfold shiftDown; rw [hC'_len]; split_ifs <;> omega
        refine ⟨hsd_lt, ?_, hsd_lt, x, ?_, hgx⟩
        · rw [hop_shift k hk_lt hkne]; exact hk_and
        · rw [hval_false k hk_lt hkne x hgx]; exact hkx
      · intro k1 hk1 k2 hk2 heq
        unfold junk gatesWhere at hk1 hk2
        rw [Finset.mem_filter, Finset.mem_range] at hk1 hk2
        have hne1 : k1 ≠ g := by
          intro hEq; have := hk1.2.1; rw [hEq, hgOr] at this; cases this
        have hne2 : k2 ≠ g := by
          intro hEq; have := hk2.2.1; rw [hEq, hgOr] at this; cases this
        unfold shiftDown at heq
        split_ifs at heq <;> omega
      · intro m hm
        unfold junk gatesWhere at hm
        rw [Finset.mem_filter, Finset.mem_range] at hm
        rcases hm with ⟨hm_lt, hm_and, _, x, hmx, hgx⟩
        have hm_ne : m ≠ Cmid.gates.length := by
          intro hEq; rw [hEq, hgateAt_last] at hm_and; cases hm_and
        have hm_mid : m < Cmid.gates.length := by
          rw [hC'_len] at hm_lt; omega
        set k := if m < g then m else m + 1 with hk_def
        have hk_lt : k < C.gates.length := by rw [hk_def]; split_ifs <;> omega
        have hkne : k ≠ g := by rw [hk_def]; split_ifs <;> omega
        have hsd : shiftDown g k = m := by unfold shiftDown; rw [hk_def]; split_ifs <;> omega
        refine ⟨k, ?_, hsd⟩
        unfold junk gatesWhere
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨hk_lt, ?_, hk_lt, x, ?_, hgx⟩
        · rw [← hop_shift k hk_lt hkne, hsd]; exact hm_and
        · rw [← hval_false k hk_lt hkne x hgx, hsd]; exact hmx
    have hsum : andIndexSum C' < andIndexSum C := by
      unfold andIndexSum
      set A := (Finset.range C.gates.length).filter (fun k => isAndOp (gateAt C k).op = true)
      set A' := (Finset.range C'.gates.length).filter (fun k => isAndOp (gateAt C' k).op = true)
      have hsum_eq : ∑ k ∈ A, shiftDown g k = ∑ m ∈ A', m := by
        apply Finset.sum_bij (fun k _ => shiftDown g k)
        · intro k hk
          simp only [A, A', Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hk ⊢
          have hkne : k ≠ g := by
            intro hEq; rw [hEq, hgOr] at hk; cases hk.2
          have hsd_lt : shiftDown g k < C'.gates.length := by
            unfold shiftDown; rw [hC'_len]; split_ifs <;> omega
          exact ⟨hsd_lt, by rw [hop_shift k hk.1 hkne]; exact hk.2⟩
        · intro k1 hk1 k2 hk2 heq
          simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hk1 hk2
          have hne1 : k1 ≠ g := by intro hEq; rw [hEq, hgOr] at hk1; cases hk1.2
          have hne2 : k2 ≠ g := by intro hEq; rw [hEq, hgOr] at hk2; cases hk2.2
          unfold shiftDown at heq
          split_ifs at heq <;> omega
        · intro m hm
          simp only [A', Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hm
          have hm_ne : m ≠ Cmid.gates.length := by
            intro hEq; rw [hEq, hgateAt_last] at hm; cases hm.2
          have hm_mid : m < Cmid.gates.length := by rw [hC'_len] at hm; omega
          set k := if m < g then m else m + 1 with hk_def
          have hk_lt : k < C.gates.length := by rw [hk_def]; split_ifs <;> omega
          have hkne : k ≠ g := by rw [hk_def]; split_ifs <;> omega
          have hsd : shiftDown g k = m := by unfold shiftDown; rw [hk_def]; split_ifs <;> omega
          refine ⟨k, ?_, hsd⟩
          simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff]
          exact ⟨hk_lt, by rw [← hop_shift k hk_lt hkne, hsd]; exact hm.2⟩
        · intro _ _; rfl
      rw [← hsum_eq]
      apply Finset.sum_lt_sum
      · intro k _
        unfold shiftDown; split_ifs <;> omega
      · refine ⟨j, ?_, ?_⟩
        · simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff]
          exact ⟨hj, hjAnd⟩
        · unfold shiftDown; split_ifs <;> omega
    exact ⟨C', hC'_Least, hC'_len, hjunk, hsum⟩
  · simp [hgin] at hgin_len

lemma main_aux {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty) (m : ℕ) :
    ∀ C : Circuit, andIndexSum C = m → IsLeastAO G C →
      ∃ C' : Circuit, IsLeastAO G C' ∧ C'.size = C.size ∧
        (junk G C').card = (junk G C).card ∧ TopForm G C' := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro C hm hL
    by_cases hTF : TopForm G C
    · exact ⟨C, hL, rfl, rfl, hTF⟩
    · unfold TopForm at hTF
      push Not at hTF
      obtain ⟨i, hi, j, hj, hiAnd, hiBelow, hjAnd, hCone⟩ := hTF
      obtain ⟨g, hig, hgj, hglen, hmem⟩ := exists_direct_reader n C i j hj hCone
      have hgAO : (gateAt C g).op = GateOp.and ∨ (gateAt C g).op = GateOp.or := by
        rw [gateAt_eq_getElem C g hglen]
        exact hL.1.1 C.gates[g] (List.getElem_mem hglen)
      rcases hgAO with hgAnd | hgOr
      · exfalso
        exact no_and_reader G C i g hE hL hig hglen hiBelow hgAnd hmem
      · have hgj_lt : g < j := by
          by_contra hge
          have hEq : g = j := by omega
          rw [hEq, hjAnd] at hgOr
          cases hgOr
        obtain ⟨C1, hL1, hsz1, hjunk1, hsum1⟩ :=
          pushOr_step G C i g j hE hL hig hgj_lt hj hiBelow hgOr hjAnd hmem
        obtain ⟨C2, hL2, hsz2, hjunk2, hTF2⟩ :=
          ih (andIndexSum C1) (by omega) C1 rfl hL1
        exact ⟨C2, hL2, hsz2.trans hsz1, hjunk2.trans hjunk1, hTF2⟩

lemma minimal_has_topform {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hmin : PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C)
    (hf : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.IsMinimalMonoCircuit n D ∧
      circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧ TopForm G D := by
  classical
  by_cases hex : ∃ a b, G.Adj a b
  · obtain ⟨a, b, hab⟩ := hex
    have hne : G.edgeFinset.Nonempty := ⟨s(a, b), by simpa using hab⟩
    obtain ⟨D, hD, hs, _, ht⟩ := main_aux G hne (andIndexSum C) C rfl
      (PEqualNP.Outside.L_meta_1772_aux.clean.minimal_graph_isLeastAO G hmin hf)
    exact ⟨D, PEqualNP.Outside.L_meta_1772_aux.clean.leastAO_graph_isMinimal G hD,
      hD.2.1, hs, ht⟩
  · have hNo : ∀ a b, ¬ G.Adj a b := fun a b hab => hex ⟨a, b, hab⟩
    let D : Circuit := ⟨[], n⟩
    have hD : Monotone2 D := by intro g hg; simp [D] at hg
    have hDF : circuitFun n D = circuitFun n C := by
      rw [hf]
      funext x
      change (List.ofFn x).getD n false = graphFun G ∅ x
      simp [graphFun, hNo, List.getD_eq_getElem?_getD]
    have hsz := hmin.2 D hD hDF
    have hlen : C.gates.length = 0 := by simpa [Circuit.size, D] using hsz
    refine ⟨C, hmin, hf, rfl, ?_⟩
    intro i hi
    simp [hlen] at hi

end PEqualNP.Outside.L_meta_1772_aux.topform
