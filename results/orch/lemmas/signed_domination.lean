import PEqualNP.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.SplitIfs

namespace PEqualNP.Outside.L_meta_1031.SignedDomination

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
      · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
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
          exact hR ⟨k + 1, by omega, hk1, hi'⟩
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
  rw [ite_eq_left hr]
  change Circuit.mk _ (aliasWire (n + r) i C.output) = Circuit.mk _ (aliasWire (n + r) i C.output)
  congr 1
  apply List.ext_getElem
  · simp; omega
  · intro k hk hk'
    have hlen : (C.gates.take r).length = r := by simp; omega
    have hklen : k < C.gates.length - 1 := by simpa [bypass] using hk'
    simp only [List.getElem_map, List.getElem_range]
    by_cases hkr : k < r
    · rw [ite_eq_left hkr, List.getElem_append_left (by omega), List.getElem_take,
        gateAt_eq (by omega)]
    · rw [ite_eq_right hkr, List.getElem_append_right (by omega), List.getElem_map,
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
        · rw [ite_eq_left hil, ite_eq_left hil]
          exact ih i hil
        · rw [ite_eq_right hil, ite_eq_right hil]
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

def independent {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

lemma boundary_certificate (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool)
    (mono : ∀ x y : Fin n → Bool,
      (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (edges : ∀ u v : Fin n, G.Adj u v →
      f (fun i => decide (i = u ∨ i = v)) = true)
    (misses : ∀ S : Finset (Fin n), independent G S →
      (∀ T : Finset (Fin n), independent G T → S ⊆ T → T ⊆ S) →
      f (fun i => decide (i ∈ S)) = false) :
    ∀ x : Fin n → Bool, f x = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
  classical
  intro x
  by_cases hx : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
  · obtain ⟨u, v, huv, hu, hv⟩ := hx
    have hf : f x = true := mono _ x (by
      intro i hi
      simp only [decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hu
      · exact hv) (edges u v huv)
    simp [hf, show ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true from ⟨u,v,huv,hu,hv⟩]
  · let S : Finset (Fin n) := Finset.univ.filter (fun i => x i = true)
    have hS : independent G S := by
      intro u hu v hv huv
      exact hx ⟨u, v, huv, (Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2⟩
    let family := Finset.univ.powerset.filter (independent G)
    have member (T : Finset (Fin n)) : T ∈ family ↔ independent G T := by
      simp [family]
    obtain ⟨T, hST, hmax⟩ := Finset.exists_le_maximal family ((member S).mpr hS)
    have hT : independent G T := (member T).mp hmax.1
    have hbound : ∀ U : Finset (Fin n), independent G U → T ⊆ U → U ⊆ T := by
      intro U hU hTU
      exact hmax.2 ((member U).mpr hU) hTU
    have hmiss := misses T hT hbound
    have hf : f x = false := by
      cases hfx : f x with
      | false => rfl
      | true =>
        have htrue : f (fun i => decide (i ∈ T)) = true := mono x _ (by
          intro i hi
          simp only [decide_eq_true_eq]
          exact hST (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)) hfx
        exact Bool.noConfusion (hmiss.symm.trans htrue)
    simp [hx, hf]


end PEqualNP.Outside.L_meta_1031.SignedDomination

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_1031.SignedDomination

theorem PEqualNP.Outside.L_meta_1031.signed_domination_impossible_with_false
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hfun : circuitFun n C = graphFun G ∅)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j ∨ n + C.gates.length ≤ i)
    (hpos : ∀ u v : Fin n, G.Adj u v →
      (C.wires (List.ofFn (pairInput u v))).getD (n + j) false = true →
      (C.wires (List.ofFn (pairInput u v))).getD i false = true)
    (hneg : ∀ S : Finset (Fin n), independent G S →
      (∀ T : Finset (Fin n), independent G T → S ⊆ T → T ⊆ S) →
      (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ S)))).getD i false = true →
      (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ S)))).getD (n + j) false = true) :
    False := by
  classical
  let D := bypass n C j i
  have hDmono : Monotone2 D := bypass_mono hmin.1
  have hDpos (u v : Fin n) (huv : G.Adj u v) :
      D.eval (List.ofFn (pairInput u v)) = true := by
    have transfer := bypass_eval_rel (R := fun a b => a = true → b = true)
      (fun _ => id) opMono_imp (n := n) (C := C) (by simp) (mono_ops hmin.1)
      hj hi (hpos u v huv)
    apply transfer
    change circuitFun n C (pairInput u v) = true
    rw [hfun]
    exact pair_true G u v huv
  have hDneg (S : Finset (Fin n)) (hS : independent G S)
      (hmax : ∀ T : Finset (Fin n), independent G T → S ⊆ T → T ⊆ S) :
      D.eval (List.ofFn (fun k : Fin n => decide (k ∈ S))) = false := by
    have transfer := bypass_eval_rel (R := fun a b => b = true → a = true)
      (fun _ => id) opMono_reverse (n := n) (C := C) (by simp) (mono_ops hmin.1)
      hj hi (hneg S hS hmax)
    cases heval : D.eval (List.ofFn (fun k : Fin n => decide (k ∈ S))) with
    | false => rfl
    | true =>
      have hc := transfer heval
      change circuitFun n C (fun k : Fin n => decide (k ∈ S)) = true at hc
      rw [hfun, graph_true] at hc
      obtain ⟨u, v, huv, hu, hv⟩ := hc
      exact (hS u (of_decide_eq_true hu) v (of_decide_eq_true hv) huv).elim
  have hDfun : circuitFun n D = graphFun G ∅ := by
    have agrees := boundary_certificate n G (fun x => D.eval (List.ofFn x))
      (circuit_monotone n D hDmono) hDpos hDneg
    funext x
    change D.eval (List.ofFn x) = graphFun G ∅ x
    rw [agrees x]
    simp [graphFun]
  have smaller := hmin.2 D hDmono (hDfun.trans hfun.symm)
  have hsize : D.size = C.gates.length - 1 := bypass_length n C j i
  change C.gates.length ≤ D.size at smaller
  omega

theorem PEqualNP.Outside.L_meta_1031.signed_domination_impossible
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hfun : circuitFun n C = graphFun G ∅)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (hpos : ∀ u v : Fin n, G.Adj u v →
      (C.wires (List.ofFn (pairInput u v))).getD (n + j) false = true →
      (C.wires (List.ofFn (pairInput u v))).getD i false = true)
    (hneg : ∀ S : Finset (Fin n), independent G S →
      (∀ T : Finset (Fin n), independent G T → S ⊆ T → T ⊆ S) →
      (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ S)))).getD i false = true →
      (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ S)))).getD (n + j) false = true) :
    False := by
  exact PEqualNP.Outside.L_meta_1031.signed_domination_impossible_with_false
    n G C hmin hfun j i hj (Or.inl hi) hpos hneg

lemma PEqualNP.Outside.L_meta_1031.and_operand_negative_witness
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hfun : circuitFun n C = graphFun G ∅)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (hand : (gateAt C j).op = GateOp.and) (hin : i ∈ (gateAt C j).inputs) :
    ∃ S : Finset (Fin n), independent G S ∧
      (∀ T : Finset (Fin n), independent G T → S ⊆ T → T ⊆ S) ∧
      (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ S)))).getD i false = true ∧
      (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ S)))).getD (n + j) false = false := by
  classical
  by_contra hnone
  apply PEqualNP.Outside.L_meta_1031.signed_domination_impossible n G C hmin hfun j i hj hi
  · intro u v _ hgate
    exact ((val_and (n := n) (by simp) hj hand).mp hgate i hin).2
  · intro S hS hmax hinput
    cases hgate : (C.wires (List.ofFn (fun k : Fin n => decide (k ∈ S)))).getD
        (n + j) false with
    | false => exact (hnone ⟨S, hS, hmax, hinput, hgate⟩).elim
    | true => rfl

lemma PEqualNP.Outside.L_meta_1031.or_operand_positive_witness
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hfun : circuitFun n C = graphFun G ∅)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (hor : (gateAt C j).op = GateOp.or) (hin : i ∈ (gateAt C j).inputs) :
    ∃ u v : Fin n, G.Adj u v ∧
      (C.wires (List.ofFn (pairInput u v))).getD (n + j) false = true ∧
      (C.wires (List.ofFn (pairInput u v))).getD i false = false := by
  classical
  by_contra hnone
  apply PEqualNP.Outside.L_meta_1031.signed_domination_impossible n G C hmin hfun j i hj hi
  · intro u v huv hgate
    cases hinput : (C.wires (List.ofFn (pairInput u v))).getD i false with
    | false => exact (hnone ⟨u, v, huv, hgate, hinput⟩).elim
    | true => rfl
  · intro S _ _ hinput
    exact (val_or (n := n) (by simp) hj hor).mpr ⟨i, hin, hi, hinput⟩

lemma PEqualNP.Outside.L_meta_1031.sound_wire_not_and_input
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hfun : circuitFun n C = graphFun G ∅)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (hand : (gateAt C j).op = GateOp.and)
    (hsound : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD i false = true → graphFun G ∅ x = true) :
    i ∉ (gateAt C j).inputs := by
  intro hin
  obtain ⟨S, hS, _, hinput, _⟩ :=
    PEqualNP.Outside.L_meta_1031.and_operand_negative_witness n G C hmin hfun j i hj hi hand hin
  have hhit := hsound (fun k : Fin n => decide (k ∈ S)) hinput
  obtain ⟨u, v, huv, hu, hv⟩ := (graph_true G _).mp hhit
  exact hS u (of_decide_eq_true hu) v (of_decide_eq_true hv) huv

lemma PEqualNP.Outside.L_meta_1031.gate_positive_edge_witness
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hfun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ u v : Fin n, G.Adj u v ∧
      (C.wires (List.ofFn (pairInput u v))).getD (n + j) false = true := by
  classical
  by_contra hnone
  apply PEqualNP.Outside.L_meta_1031.signed_domination_impossible_with_false
    n G C hmin hfun j (n + C.gates.length) hj (Or.inr le_rfl)
  · intro u v huv hgate
    exact (hnone ⟨u, v, huv, hgate⟩).elim
  · intro S _ _ hfalse
    change val C (List.ofFn (fun k : Fin n => decide (k ∈ S))) (n + C.gates.length) = true at hfalse
    rw [val_ge (n := n) (by simp) le_rfl] at hfalse
    cases hfalse

lemma PEqualNP.Outside.L_meta_1031.and_inputs_earlier
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hfun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) :
    ∀ i ∈ (gateAt C j).inputs, i < n + j := by
  obtain ⟨u, v, _, hgate⟩ :=
    PEqualNP.Outside.L_meta_1031.gate_positive_edge_witness n G C hmin hfun j hj
  exact fun i hi => ((val_and (n := n) (by simp) hj hand).mp hgate i hi).1

lemma PEqualNP.Outside.L_meta_1031.and_has_another_operand
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hfun : circuitFun n C = graphFun G ∅)
    (j i : ℕ) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (hin : i ∈ (gateAt C j).inputs) :
    ∃ k ∈ (gateAt C j).inputs, k ≠ i := by
  classical
  have hearly := PEqualNP.Outside.L_meta_1031.and_inputs_earlier n G C hmin hfun j hj hand
  obtain ⟨S, _, _, hinput, hgate⟩ :=
    PEqualNP.Outside.L_meta_1031.and_operand_negative_witness n G C hmin hfun j i hj
      (hearly i hin) hand hin
  by_contra hnone
  have htrue : val C (List.ofFn (fun k : Fin n => decide (k ∈ S))) (n + j) = true := by
    apply (val_and (n := n) (by simp) hj hand).mpr
    intro k hk
    have hki : k = i := by
      by_contra hne
      exact hnone ⟨k, hk, hne⟩
    exact ⟨hearly k hk, hki ▸ hinput⟩
  exact Bool.noConfusion (hgate.symm.trans htrue)

lemma PEqualNP.Outside.L_meta_1031.or_has_another_earlier_operand
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hfun : circuitFun n C = graphFun G ∅)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (hor : (gateAt C j).op = GateOp.or) (hin : i ∈ (gateAt C j).inputs) :
    ∃ k ∈ (gateAt C j).inputs, k < n + j ∧ k ≠ i := by
  obtain ⟨u, v, _, hgate, hinput⟩ :=
    PEqualNP.Outside.L_meta_1031.or_operand_positive_witness n G C hmin hfun j i hj hi hor hin
  obtain ⟨k, hk, hkearly, hktrue⟩ := (val_or (n := n) (by simp) hj hor).mp hgate
  refine ⟨k, hk, hkearly, ?_⟩
  intro hki
  subst k
  exact Bool.noConfusion (hinput.symm.trans hktrue)

lemma PEqualNP.Outside.L_meta_1031.SignedDomination.list_eq_pair_of_distinct_mem
    {l : List ℕ} {i k : ℕ} (hlen : l.length ≤ 2) (hi : i ∈ l) (hk : k ∈ l)
    (hne : k ≠ i) : l = [i, k] ∨ l = [k, i] := by
  cases l with
  | nil => simp at hi
  | cons a l =>
    cases l with
    | nil =>
      simp only [List.mem_singleton] at hi hk
      exact (hne (hk.trans hi.symm)).elim
    | cons b l =>
      have hempty : l = [] := by
        cases l with
        | nil => rfl
        | cons c cs => simp only [List.length_cons] at hlen; omega
      subst l
      simp at hi hk
      rcases hi with rfl | rfl
      · rcases hk with hka | rfl
        · exact (hne hka).elim
        · exact Or.inl rfl
      · rcases hk with rfl | hkb
        · exact Or.inr rfl
        · exact (hne hkb).elim

lemma PEqualNP.Outside.L_meta_1031.or_inputs_pair
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hfun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) :
    ∃ a b : ℕ, (gateAt C j).inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j := by
  obtain ⟨u, v, _, hgate⟩ :=
    PEqualNP.Outside.L_meta_1031.gate_positive_edge_witness n G C hmin hfun j hj
  obtain ⟨i, hi, hiearly, _⟩ := (val_or (n := n) (by simp) hj hor).mp hgate
  obtain ⟨k, hk, hkearly, hne⟩ :=
    PEqualNP.Outside.L_meta_1031.or_has_another_earlier_operand n G C hmin hfun j i hj hiearly hor hi
  have hlen := (hmin.1 _ (gateAt_mem hj)).2
  rcases list_eq_pair_of_distinct_mem hlen hi hk hne with hp | hp
  · exact ⟨i, k, hp, Ne.symm hne, hiearly, hkearly⟩
  · exact ⟨k, i, hp, hne, hkearly, hiearly⟩

lemma PEqualNP.Outside.L_meta_1031.and_inputs_nil_or_pair
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hfun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) :
    (gateAt C j).inputs = [] ∨
      ∃ a b : ℕ, (gateAt C j).inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j := by
  cases hinputs : (gateAt C j).inputs with
  | nil => exact Or.inl rfl
  | cons i l =>
    have hi : i ∈ (gateAt C j).inputs := by simp [hinputs]
    obtain ⟨k, hk, hne⟩ :=
      PEqualNP.Outside.L_meta_1031.and_has_another_operand n G C hmin hfun j i hj hand hi
    have hearly := PEqualNP.Outside.L_meta_1031.and_inputs_earlier n G C hmin hfun j hj hand
    have hlen := (hmin.1 _ (gateAt_mem hj)).2
    apply Or.inr
    rcases list_eq_pair_of_distinct_mem hlen hi hk hne with hp | hp
    · exact ⟨i, k, hinputs ▸ hp, Ne.symm hne, hearly i hi, hearly k hk⟩
    · exact ⟨k, i, hinputs ▸ hp, hne, hearly k hk, hearly i hi⟩
