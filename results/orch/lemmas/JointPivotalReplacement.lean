import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.JointPivotalReplacement

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

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

lemma edge_dominating_bypass {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (hf : circuitFun n C = graphFun G ∅)
    (r i : ℕ) (hr : r < C.gates.length) (hi : i < n+r)
    (hnegative : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      val C (List.ofFn x) i = true → val C (List.ofFn x) (n+r) = true)
    (hedge : ∀ u v : Fin n, G.Adj u v →
      val C (List.ofFn (pairInput u v)) (n+r) = true →
      val C (List.ofFn (pairInput u v)) i = true) :
    circuitFun n (bypass n C r i) = graphFun G ∅ := by
  let D := bypass n C r i
  have hD : Monotone2 D := bypass_mono hm
  have lower (x : Fin n → Bool) (hx : graphFun G ∅ x = false) :
      circuitFun n D x = true → circuitFun n C x = true :=
    bypass_eval_rel (R := fun a b => b = true → a = true) (fun _ => id)
      opMono_reverse (by simp) (mono_ops hm) hr (Or.inl hi) (hnegative x hx)
  have edge (u v : Fin n) (huv : G.Adj u v) : circuitFun n D (pairInput u v) = true := by
    apply bypass_eval_rel (R := fun a b => a = true → b = true) (fun _ => id)
      opMono_imp (by simp) (mono_ops hm) hr (Or.inl hi) (hedge u v huv)
    change circuitFun n C (pairInput u v) = true
    rw [hf]
    exact pair_true G u v huv
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hd
    by_cases hx : graphFun G ∅ x = true
    · exact hx
    · have hn : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hx
      have hc := lower x hn hd
      rw [hf, hn] at hc
      cases hc
  · intro hx
    obtain ⟨u,v,huv,hu,hv⟩ := (graph_true G x).mp hx
    apply circuit_monotone n D hD (pairInput u v) x _ (edge u v huv)
    intro z hz
    simp only [pairInput, decide_eq_true_eq] at hz
    rcases hz with rfl | rfl
    · exact hu
    · exact hv

def oldIndex (r k : ℕ) : ℕ := if k < r then k else k+1

lemma oldIndex_injective (r : ℕ) : Function.Injective (oldIndex r) := by
  intro a b h
  unfold oldIndex at h
  split_ifs at h <;> omega

lemma oldIndex_ne (r k : ℕ) : oldIndex r k ≠ r := by
  unfold oldIndex
  split_ifs <;> omega

lemma oldIndex_lt {r k l : ℕ} (hr : r < l) (hk : k < l-1) : oldIndex r k < l := by
  unfold oldIndex
  split_ifs <;> omega

lemma oldIndex_alias (n r i k : ℕ) :
    aliasWire (n+r) i (n+oldIndex r k) = n+k := by
  unfold oldIndex
  split_ifs with h
  · exact aliasWire_lt_self (by omega)
  · rw [aliasWire_gt_self (by omega)]
    omega

lemma bypass_op {n : ℕ} {C : Circuit} {r i k : ℕ}
    (hk : k < (bypass n C r i).gates.length) :
    (gateAt (bypass n C r i) k).op = (gateAt C (oldIndex r k)).op := by
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  unfold oldIndex
  split_ifs <;> rfl

lemma bypass_dirty_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (r i : ℕ) (hr : r < C.gates.length) (hi : i < n+r)
    (hweak : ∀ x : Fin n → Bool, graphFun G ∅ x = false → val C (List.ofFn x) i = true →
      val C (List.ofFn x) (n+r) = true) :
    (junk G (bypass n C r i)).card ≤ ((junk G C).erase r).card := by
  classical
  have sub : (junk G (bypass n C r i)).image (oldIndex r) ⊆ (junk G C).erase r := by
    intro t ht
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp ht
    have hk' := Finset.mem_filter.mp hk
    have kbound : k < (bypass n C r i).gates.length := Finset.mem_range.mp hk'.1
    obtain ⟨hand,_,x,hx,hfalse⟩ := hk'.2
    have oldbound : oldIndex r k < C.gates.length :=
      oldIndex_lt hr (by simpa [bypass_length] using kbound)
    have oldval : val C (List.ofFn x) (n+oldIndex r k) = true := by
      have lower := bypass_rel (R := fun a b => b = true → a = true) (fun _ => id)
        opMono_reverse (by simp) (mono_ops hm) hr (Or.inl hi) (fun _ => hweak x hfalse)
        (n+oldIndex r k) (by have := oldIndex_ne r k; omega)
      rw [oldIndex_alias] at lower
      exact lower hx
    apply Finset.mem_erase.mpr
    refine ⟨oldIndex_ne r k, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr oldbound, ?_⟩
    exact ⟨(bypass_op kbound).symm.trans hand,oldbound,x,oldval,hfalse⟩
  have hcard := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ (oldIndex_injective r)] at hcard
  exact hcard

lemma bypass_dirty_card_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (r i : ℕ) (hr : r < C.gates.length) (hi : i < n+r)
    (hweak : ∀ x : Fin n → Bool, graphFun G ∅ x = false → val C (List.ofFn x) i = true →
      val C (List.ofFn x) (n+r) = true) (hdirty : r ∈ junk G C) :
    (junk G (bypass n C r i)).card < (junk G C).card := by
  have hle := bypass_dirty_card G C hm r i hr hi hweak
  have he := Finset.card_erase_add_one hdirty
  omega

lemma bypass_dirty_before {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hj : j < r) :
    j ∈ junk G (bypass n C r i) ↔ j ∈ junk G C := by
  have hb : j < (bypass n C r i).gates.length := by rw [bypass_length]; omega
  have hop : gateAt (bypass n C r i) j = gateAt C j := by
    rw [gateAt_bypass (by omega), ite_eq_left hj]
  have hv (x : Fin n → Bool) : gateVal n (bypass n C r i) j x = gateVal n C j x :=
    bypass_val_lt (by simp) hr (n+j) (by omega)
  change (j ∈ (Finset.range _).filter _) ↔ (j ∈ (Finset.range _).filter _)
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_range, IsDirtyAnd, IsDirty, hop, hv]
  simp only [hb, show j < C.gates.length by omega, true_and]

lemma erase_covered_class {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset ℕ) (C : Circuit) (hm : Monotone2 C)
    (hf : circuitFun n C = graphFun G ∅) (i : ℕ)
    (hb : ∀ r ∈ S, r < C.gates.length ∧ i < n+r)
    (hweak : ∀ r ∈ S, ∀ x : Fin n → Bool, graphFun G ∅ x = false → val C (List.ofFn x) i = true →
      val C (List.ofFn x) (n+r) = true)
    (hedge : ∀ r ∈ S, ∀ u v : Fin n, G.Adj u v →
      val C (List.ofFn (pairInput u v)) (n+r) = true → val C (List.ofFn (pairInput u v)) i = true) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size + S.card = C.size ∧ (junk G D).card ≤ (junk G C).card ∧
      ((∃ r ∈ S, r ∈ junk G C) → (junk G D).card < (junk G C).card) := by
  classical
  induction S using Finset.strongInductionOn generalizing C with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · let r := S.max' hS
      have hrS : r ∈ S := Finset.max'_mem _ _
      obtain ⟨hr,hi⟩ := hb r hrS
      let B := bypass n C r i
      have hB : Monotone2 B := bypass_mono hm
      have hBF : circuitFun n B = graphFun G ∅ :=
        edge_dominating_bypass G C hm hf r i hr hi (hweak r hrS) (hedge r hrS)
      have earlier (j : ℕ) (hj : j ∈ S.erase r) : j < r := by
        have hs := Finset.mem_erase.mp hj
        have hm' : j ≤ r := Finset.le_max' S j hs.2
        omega
      have before (j : ℕ) (hj : j ∈ S.erase r) (x : Fin n → Bool) :
          val B (List.ofFn x) (n+j) = val C (List.ofFn x) (n+j) :=
        bypass_val_lt (by simp) hr (n+j) (by have := earlier j hj; omega)
      have redirect (x : Fin n → Bool) : val B (List.ofFn x) i = val C (List.ofFn x) i :=
        bypass_val_lt (by simp) hr i hi
      have hbb : ∀ j ∈ S.erase r, j < B.gates.length ∧ i < n+j := by
        intro j hj
        have old := hb j (Finset.mem_erase.mp hj).2
        have hjr := earlier j hj
        refine ⟨?_,old.2⟩
        change j < (bypass n C r i).gates.length
        rw [bypass_length]
        omega
      have hbw : ∀ j ∈ S.erase r, ∀ x : Fin n → Bool, graphFun G ∅ x = false → val B (List.ofFn x) i = true →
          val B (List.ofFn x) (n+j) = true := by
        intro j hj x hn hv
        rw [before j hj x]
        apply hweak j (Finset.mem_erase.mp hj).2 x hn
        rwa [redirect] at hv
      have hbe : ∀ j ∈ S.erase r, ∀ u v : Fin n, G.Adj u v →
          val B (List.ofFn (pairInput u v)) (n+j) = true → val B (List.ofFn (pairInput u v)) i = true := by
        intro j hj u v huv
        rw [before j hj,redirect]
        exact hedge j (Finset.mem_erase.mp hj).2 u v huv
      obtain ⟨D,hD,hDF,hsize,hle,hstrict⟩ :=
        ih (S.erase r) (Finset.erase_ssubset hrS) B hB hBF hbb hbw hbe
      have erle := bypass_dirty_card G C hm r i hr hi (hweak r hrS)
      have noninc : (junk G B).card ≤ (junk G C).card :=
        erle.trans (Finset.card_le_card (Finset.erase_subset _ _))
      refine ⟨D,hD,hDF,?_,hle.trans noninc,?_⟩
      · have hc := Finset.card_erase_add_one hrS
        have hl : B.size = C.size-1 := bypass_length n C r i
        have hp : 0 < C.size := by change 0 < C.gates.length; omega
        omega
      · intro hbad
        by_cases hd : r ∈ junk G C
        · exact hle.trans_lt (bypass_dirty_card_lt G C hm r i hr hi (hweak r hrS) hd)
        · obtain ⟨j,hj,hjd⟩ := hbad
          have jne : j ≠ r := fun h => hd (h ▸ hjd)
          have hjE : j ∈ S.erase r := Finset.mem_erase.mpr ⟨jne,hj⟩
          have hjB : j ∈ junk G B :=
            (bypass_dirty_before G C r i j hr (earlier j hjE)).mpr hjd
          exact (hstrict ⟨j,hjE,hjB⟩).trans_le noninc
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      refine ⟨C,hm,hf,by simp,le_rfl,?_⟩
      simp




def shiftWire (n k u : ℕ) : ℕ := if u < n then u else u+k

def shiftGate (n k : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (shiftWire n k)⟩

def prepend (n : ℕ) (D C : Circuit) : Circuit :=
  ⟨D.gates ++ C.gates.map (shiftGate n D.gates.length), shiftWire n D.gates.length C.output⟩

lemma prepend_length (n : ℕ) (D C : Circuit) :
    (prepend n D C).gates.length = D.gates.length + C.gates.length := by simp [prepend]

lemma prepend_gate_left {n : ℕ} {D C : Circuit} {j : ℕ} (hj : j < D.gates.length) :
    gateAt (prepend n D C) j = gateAt D j := by
  simp [gateAt,prepend,List.getD_eq_getElem?_getD,List.getElem?_append_left hj]

lemma prepend_gate_right {n : ℕ} {D C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt (prepend n D C) (D.gates.length+j) = shiftGate n D.gates.length (gateAt C j) := by
  rw [gateAt_eq (by rw [prepend_length]; omega),gateAt_eq hj]
  simp [prepend]

lemma shiftWire_lt (n k u j : ℕ) : shiftWire n k u < n+k+j ↔ u < n+j := by
  unfold shiftWire
  split_ifs <;> omega

lemma prepend_val_left {n : ℕ} (D C : Circuit) {x : List Bool} (hx : x.length = n)
    (u : ℕ) (hu : u < n+D.gates.length) : val (prepend n D C) x u = val D x u := by
  apply val_prefix hx (le_refl _) (by rw [prepend_length]; omega) _ u hu
  intro j hj
  exact prepend_gate_left hj

lemma prepend_val_right {n : ℕ} (D C : Circuit) {x : List Bool} (hx : x.length = n)
    (u : ℕ) : val (prepend n D C) x (shiftWire n D.gates.length u) = val C x u := by
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hun : u < n
    · rw [show shiftWire n D.gates.length u = u by simp [shiftWire,hun],val_input hx hun,val_input hx hun]
    · by_cases hge : n+C.gates.length ≤ u
      · rw [val_ge hx hge]
        apply val_ge hx
        rw [prepend_length]
        simp only [shiftWire,ite_eq_right hun]
        omega
      · obtain ⟨j,rfl⟩ : ∃ j, u=n+j := ⟨u-n,by omega⟩
        have hj : j < C.gates.length := by omega
        have hs : shiftWire n D.gates.length (n+j) = n+(D.gates.length+j) := by
          simp [shiftWire]; omega
        rw [hs,val_gate hx (by rw [prepend_length]; omega),val_gate hx hj,prepend_gate_right hj]
        simp only [shiftGate,List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        simp only [Function.comp_apply]
        by_cases ha : a < n+j
        · have hsa : shiftWire n D.gates.length a < n+(D.gates.length+j) := by
            have := (shiftWire_lt n D.gates.length a j).mpr ha
            omega
          rw [ite_eq_left hsa,ite_eq_left ha]
          exact ih a ha
        · have hsa : ¬ shiftWire n D.gates.length a < n+(D.gates.length+j) := by
            have := (shiftWire_lt n D.gates.length a j).not.mpr ha
            omega
          rw [ite_eq_right hsa,ite_eq_right ha]

lemma prepend_fun (n : ℕ) (D C : Circuit) : circuitFun n (prepend n D C) = circuitFun n C := by
  funext x
  exact prepend_val_right D C (by simp) C.output

lemma prepend_mono {n : ℕ} {D C : Circuit} (hD : Monotone2 D) (hC : Monotone2 C) :
    Monotone2 (prepend n D C) := by
  intro g hg
  change g ∈ D.gates ++ C.gates.map (shiftGate n D.gates.length) at hg
  rcases List.mem_append.mp hg with hd | hc
  · exact hD g hd
  · obtain ⟨g',hg',heq⟩ := List.mem_map.mp hc
    subst g
    simpa [shiftGate] using hC g' hg'



lemma prepend_dirty_left {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D C : Circuit) (j : ℕ) (hj : j < D.gates.length) :
    j ∈ junk G (prepend n D C) ↔ j ∈ junk G D := by
  have hp : j < (prepend n D C).gates.length := by rw [prepend_length]; omega
  have hv (x : Fin n → Bool) : gateVal n (prepend n D C) j x = gateVal n D j x :=
    prepend_val_left D C (by simp) (n+j) (by omega)
  change (j ∈ (Finset.range _).filter _) ↔ (j ∈ (Finset.range _).filter _)
  rw [Finset.mem_filter,Finset.mem_filter]
  simp only [Finset.mem_range,IsDirtyAnd,IsDirty,prepend_gate_left hj,hv,hp,hj,true_and]

lemma prepend_dirty_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    D.gates.length+j ∈ junk G (prepend n D C) ↔ j ∈ junk G C := by
  have hp : D.gates.length+j < (prepend n D C).gates.length := by rw [prepend_length]; omega
  have hv (x : Fin n → Bool) : gateVal n (prepend n D C) (D.gates.length+j) x = gateVal n C j x := by
    change val (prepend n D C) (List.ofFn x) (n+(D.gates.length+j)) = val C (List.ofFn x) (n+j)
    have h := prepend_val_right D C (by simp : (List.ofFn x).length=n) (n+j)
    simpa [shiftWire,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  change (_ ∈ (Finset.range _).filter _) ↔ (j ∈ (Finset.range _).filter _)
  rw [Finset.mem_filter,Finset.mem_filter]
  simp only [Finset.mem_range,IsDirtyAnd,IsDirty,prepend_gate_right hj,shiftGate,hv,hp,hj,true_and]

lemma prepend_dirty_set {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D C : Circuit) (hclean : junk G D = ∅) :
    junk G (prepend n D C) = (junk G C).image (fun j => D.gates.length+j) := by
  classical
  ext j
  constructor
  · intro hj
    have hb := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    rw [prepend_length] at hb
    have hlow : D.gates.length ≤ j := by
      by_contra h
      have hc := (prepend_dirty_left G D C j (by omega)).mp hj
      rw [hclean] at hc
      simpa using hc
    have he : D.gates.length+(j-D.gates.length)=j := by omega
    apply Finset.mem_image.mpr
    refine ⟨j-D.gates.length,?_,he⟩
    apply (prepend_dirty_right G D C _ (by omega)).mp
    rwa [he]
  · intro hj
    obtain ⟨r,hr,heq⟩ := Finset.mem_image.mp hj
    subst j
    have hb := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    exact (prepend_dirty_right G D C r hb).mpr hr

lemma prepend_dirty_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D C : Circuit) (hclean : junk G D = ∅) :
    (junk G (prepend n D C)).card = (junk G C).card := by
  have hi : Function.Injective (fun j => D.gates.length+j) := by
    intro a b h
    exact Nat.add_left_cancel h
  rw [prepend_dirty_set G D C hclean,Finset.card_image_of_injective _ hi]



theorem clean_class_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hC : Monotone2 C) (hD : Monotone2 D)
    (hf : circuitFun n C = graphFun G ∅) (hclean : junk G D = ∅)
    (hout : D.output < n+D.gates.length)
    (hnegative : ∀ x : Fin n → Bool, graphFun G ∅ x = false → circuitFun n D x = false)
    (S : Finset ℕ) (hbound : ∀ r ∈ S, r < C.gates.length)
    (hcover : ∀ r ∈ S, ∀ u v : Fin n, G.Adj u v →
      gateVal n C r (pairInput u v) = true → circuitFun n D (pairInput u v) = true)
    (hbudget : D.size ≤ S.card) :
    ∃ E : Circuit, Monotone2 E ∧ circuitFun n E = graphFun G ∅ ∧
      E.size ≤ C.size ∧ (junk G E).card ≤ (junk G C).card ∧
      ((∃ r ∈ S, r ∈ junk G C) → (junk G E).card < (junk G C).card) := by
  classical
  let P := prepend n D C
  let T := S.image (fun r => D.gates.length+r)
  have hP : Monotone2 P := prepend_mono hD hC
  have hPF : circuitFun n P = graphFun G ∅ := (prepend_fun n D C).trans hf
  have hsize : P.size = D.size+C.size := prepend_length n D C
  have inj : Function.Injective (fun r => D.gates.length+r) := by
    intro a b h
    exact Nat.add_left_cancel h
  have hcard : T.card=S.card := Finset.card_image_of_injective S inj
  have redirect (x : Fin n → Bool) : val P (List.ofFn x) D.output = circuitFun n D x :=
    prepend_val_left D C (by simp) D.output hout
  have shifted (r : ℕ) (x : Fin n → Bool) :
      val P (List.ofFn x) (n+(D.gates.length+r)) = gateVal n C r x := by
    change val (prepend n D C) (List.ofFn x) (n+(D.gates.length+r)) = val C (List.ofFn x) (n+r)
    have h := prepend_val_right D C (by simp : (List.ofFn x).length=n) (n+r)
    simpa [shiftWire,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  have hb : ∀ r ∈ T, r < P.gates.length ∧ D.output < n+r := by
    intro r hr
    obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp hr
    subst r
    have := hbound a ha
    change D.gates.length+a < (prepend n D C).gates.length ∧ _
    rw [prepend_length]
    constructor <;> omega
  have hn : ∀ r ∈ T, ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      val P (List.ofFn x) D.output = true → val P (List.ofFn x) (n+r) = true := by
    intro r hr x hx hv
    rw [redirect,hnegative x hx] at hv
    cases hv
  have he : ∀ r ∈ T, ∀ u v : Fin n, G.Adj u v →
      val P (List.ofFn (pairInput u v)) (n+r) = true →
      val P (List.ofFn (pairInput u v)) D.output = true := by
    intro r hr u v huv hv
    obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp hr
    subst r
    rw [shifted] at hv
    rw [redirect]
    exact hcover a ha u v huv hv
  obtain ⟨E,hE,hEF,hES,hle,hstrict⟩ := erase_covered_class G T P hP hPF D.output hb hn he
  have hdirty : (junk G P).card = (junk G C).card := prepend_dirty_card G D C hclean
  refine ⟨E,hE,hEF,?_,by simpa [hdirty] using hle,?_⟩
  · rw [hcard,hsize] at hES
    omega
  · intro hbad
    obtain ⟨r,hr,hd⟩ := hbad
    have hT : D.gates.length+r ∈ T := Finset.mem_image.mpr ⟨r,hr,rfl⟩
    have hdP : D.gates.length+r ∈ junk G P :=
      (prepend_dirty_right G D C r (hbound r hr)).mpr hd
    simpa [hdirty] using hstrict ⟨D.gates.length+r,hT,hdP⟩



def overwrite (C : Circuit) (S : Finset ℕ) (g : Gate) : Circuit :=
  ⟨(List.range C.gates.length).map (fun j => if j ∈ S then g else gateAt C j),C.output⟩

lemma overwrite_length (C : Circuit) (S : Finset ℕ) (g : Gate) :
    (overwrite C S g).gates.length = C.gates.length := by simp [overwrite]

lemma overwrite_gate {C : Circuit} {S : Finset ℕ} {g : Gate} {j : ℕ} (hj : j < C.gates.length) :
    gateAt (overwrite C S g) j = if j ∈ S then g else gateAt C j := by
  simp [gateAt,overwrite,List.getD_eq_getElem?_getD,hj]

lemma overwrite_mono {C : Circuit} (S : Finset ℕ) (g : Gate) (hC : Monotone2 C)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Monotone2 (overwrite C S g) := by
  intro a ha
  simp only [overwrite,List.mem_map,List.mem_range] at ha
  obtain ⟨j,hj,rfl⟩ := ha
  split_ifs
  · exact hg
  · exact hC _ (gateAt_mem hj)

lemma overwrite_rel {R : Bool → Bool → Prop} (href : ∀ b, R b b) (hop : OpMono R)
    {n : ℕ} {C : Circuit} {S : Finset ℕ} {g : Gate} {x : List Bool}
    (hx : x.length=n) (hC : Monotone2 C)
    (hselected : ∀ j < C.gates.length, j ∈ S →
      R (val C x (n+j)) (val (overwrite C S g) x (n+j))) :
    ∀ u, R (val C x u) (val (overwrite C S g) x u) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hun : u < n
    · rw [val_input hx hun,val_input hx hun]
      exact href _
    · by_cases hge : n+C.gates.length ≤ u
      · rw [val_ge hx hge,val_ge hx (by rw [overwrite_length]; exact hge)]
        exact href _
      · obtain ⟨j,rfl⟩ : ∃ j, u=n+j := ⟨u-n,by omega⟩
        have hj : j < C.gates.length := by omega
        by_cases hs : j ∈ S
        · exact hselected j hj hs
        · rw [val_gate hx hj,val_gate hx (by rw [overwrite_length]; exact hj),
            overwrite_gate hj,ite_eq_right hs]
          apply hop _ (mono_ops hC j hj)
          intro a ha
          by_cases hal : a < n+j
          · rw [ite_eq_left hal,ite_eq_left hal]
            exact ih a hal
          · rw [ite_eq_right hal,ite_eq_right hal]
            exact href _

def constGate (b : Bool) : Gate := ⟨if b then GateOp.and else GateOp.or,[]⟩
def clamp (C : Circuit) (S : Finset ℕ) (b : Bool) : Circuit := overwrite C S (constGate b)

lemma clamp_gate {C : Circuit} {S : Finset ℕ} {b : Bool} {j : ℕ} (hj : j < C.gates.length) :
    gateAt (clamp C S b) j = if j ∈ S then constGate b else gateAt C j := overwrite_gate hj

lemma clamp_val {n : ℕ} {C : Circuit} {S : Finset ℕ} {b : Bool} {x : List Bool}
    (hx : x.length=n) {j : ℕ} (hj : j < C.gates.length) (hs : j ∈ S) :
    val (clamp C S b) x (n+j) = b := by
  rw [val_gate hx (by simp [clamp,overwrite_length]; exact hj),clamp_gate hj,ite_eq_left hs]
  cases b <;> rfl

lemma clamp_false_le {n : ℕ} (C : Circuit) (S : Finset ℕ) (hC : Monotone2 C)
    (x : List Bool) (hx : x.length=n) :
    ∀ u, val (clamp C S false) x u = true → val C x u = true := by
  apply overwrite_rel (R := fun a b => b=true → a=true) (fun _ => id) opMono_reverse hx hC
  intro j hj hs
  rw [show val (overwrite C S (constGate false)) x (n+j) = false from clamp_val hx hj hs]
  intro h
  cases h

lemma le_clamp_true {n : ℕ} (C : Circuit) (S : Finset ℕ) (hC : Monotone2 C)
    (x : List Bool) (hx : x.length=n) :
    ∀ u, val C x u = true → val (clamp C S true) x u = true := by
  apply overwrite_rel (R := fun a b => a=true → b=true) (fun _ => id) opMono_imp hx hC
  intro j hj hs
  rw [show val (overwrite C S (constGate true)) x (n+j) = true from clamp_val hx hj hs]
  exact fun _ => rfl

def redirect (C : Circuit) (S : Finset ℕ) (i : ℕ) : Circuit := overwrite C S ⟨GateOp.or,[i]⟩

lemma redirect_gate {C : Circuit} {S : Finset ℕ} {i j : ℕ} (hj : j < C.gates.length) :
    gateAt (redirect C S i) j = if j ∈ S then ⟨GateOp.or,[i]⟩ else gateAt C j := overwrite_gate hj

lemma redirect_val {n : ℕ} {C : Circuit} {S : Finset ℕ} {i : ℕ} {x : List Bool}
    (hx : x.length=n) {j : ℕ} (hj : j < C.gates.length) (hs : j ∈ S) (hi : i < n+j) :
    val (redirect C S i) x (n+j) = val (redirect C S i) x i := by
  rw [val_gate hx (by simp [redirect,overwrite_length]; exact hj),redirect_gate hj,ite_eq_left hs]
  simp [GateOp.eval,hi]

lemma redirect_clamp_eq {n : ℕ} (C : Circuit) (S : Finset ℕ) (i : ℕ)
    (x : List Bool) (hx : x.length=n) (hi : ∀ j ∈ S, i < n+j) :
    ∀ u, val (redirect C S i) x u = val (clamp C S (val (redirect C S i) x i)) x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hun : u < n
    · rw [val_input hx hun,val_input hx hun]
    · by_cases hge : n+C.gates.length ≤ u
      · rw [val_ge hx (by simpa [redirect,overwrite_length] using hge),
          val_ge hx (by simpa [clamp,overwrite_length] using hge)]
      · obtain ⟨j,rfl⟩ : ∃ j,u=n+j := ⟨u-n,by omega⟩
        have hj : j<C.gates.length := by omega
        by_cases hs : j∈S
        · rw [redirect_val hx hj hs (hi j hs),clamp_val hx hj hs]
        · rw [val_gate hx (by simpa [redirect,overwrite_length] using hj),
            val_gate hx (by simpa [clamp,overwrite_length] using hj),
            redirect_gate hj,clamp_gate hj]
          simp only [ite_eq_right hs]
          congr 1
          apply List.map_congr_left
          intro a _
          by_cases ha : a<n+j
          · rw [ite_eq_left ha,ite_eq_left ha]
            exact ih a ha
          · rw [ite_eq_right ha,ite_eq_right ha]



lemma redirect_mono {C : Circuit} (S : Finset ℕ) (i : ℕ) (hC : Monotone2 C) :
    Monotone2 (redirect C S i) := overwrite_mono S _ hC (by simp)

lemma redirect_prefix {n m : ℕ} (C : Circuit) (S : Finset ℕ) (i : ℕ)
    (hm : m ≤ C.gates.length) (hS : ∀ j ∈ S, m ≤ j) (x : List Bool) (hx : x.length=n)
    (u : ℕ) (hu : u<n+m) : val (redirect C S i) x u = val C x u := by
  apply val_prefix hx hm (by simpa [redirect,overwrite_length] using hm) _ u hu
  intro j hj
  rw [redirect_gate (by omega),ite_eq_right]
  intro hs
  have := hS j hs
  omega

lemma joint_pivotal_redirect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C) (hf : circuitFun n C = graphFun G ∅)
    (S : Finset ℕ) (i : ℕ) (hi : ∀ j ∈ S, i<n+j)
    (hn : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      val (redirect C S i) (List.ofFn x) i = false)
    (hp : ∀ u v : Fin n, G.Adj u v → circuitFun n (clamp C S false) (pairInput u v) = false →
      val (redirect C S i) (List.ofFn (pairInput u v)) i = true) :
    circuitFun n (redirect C S i) = graphFun G ∅ := by
  let R := redirect C S i
  have hR : Monotone2 R := redirect_mono S i hC
  have hfalse (x : Fin n → Bool) (hx : graphFun G ∅ x = false) : circuitFun n R x = false := by
    have he := redirect_clamp_eq C S i (List.ofFn x) (by simp) hi C.output
    rw [hn x hx] at he
    change circuitFun n R x = circuitFun n (clamp C S false) x at he
    rw [he]
    by_contra h
    have ht : circuitFun n (clamp C S false) x = true := by simpa using h
    have hc := clamp_false_le (n := n) C S hC (List.ofFn x) (by simp) C.output ht
    change circuitFun n C x = true at hc
    rw [hf,hx] at hc
    cases hc
  have hedge (u v : Fin n) (huv : G.Adj u v) : circuitFun n R (pairInput u v) = true := by
    have he := redirect_clamp_eq C S i (List.ofFn (pairInput u v)) (by simp) hi C.output
    by_cases hb : val R (List.ofFn (pairInput u v)) i = true
    · change val R _ _ = val (clamp C S (val R _ i)) _ _ at he
      rw [hb] at he
      change circuitFun n R (pairInput u v) = circuitFun n (clamp C S true) (pairInput u v) at he
      rw [he]
      apply le_clamp_true (n := n) C S hC (List.ofFn (pairInput u v)) (by simp) C.output
      change circuitFun n C (pairInput u v)=true
      rw [hf]
      exact pair_true G u v huv
    · have hb' : val R (List.ofFn (pairInput u v)) i = false := Bool.eq_false_iff.mpr hb
      change val R _ _ = val (clamp C S (val R _ i)) _ _ at he
      rw [hb'] at he
      change circuitFun n R (pairInput u v) = circuitFun n (clamp C S false) (pairInput u v) at he
      rw [he]
      by_contra hh
      have hh' : circuitFun n (clamp C S false) (pairInput u v)=false := Bool.eq_false_iff.mpr hh
      exact hb (hp u v huv hh')
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    by_contra h
    have hf' := hfalse x (Bool.eq_false_iff.mpr h)
    rw [hf'] at hx
    cases hx
  · intro hx
    obtain ⟨u,v,huv,hu,hv⟩ := (graph_true G x).mp hx
    apply circuit_monotone n R hR (pairInput u v) x _ (hedge u v huv)
    intro z hz
    simp only [pairInput,decide_eq_true_eq] at hz
    rcases hz with rfl | rfl
    · exact hu
    · exact hv

lemma redirect_dirty_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : Monotone2 C) (S : Finset ℕ) (i : ℕ) (hi : ∀ j ∈ S, i<n+j)
    (hn : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      val (redirect C S i) (List.ofFn x) i = false) :
    junk G (redirect C S i) ⊆ (junk G C) \ S := by
  intro j hj
  have hmem := Finset.mem_filter.mp hj
  have hjb : j<C.gates.length := by
    simpa [redirect,overwrite_length] using Finset.mem_range.mp hmem.1
  obtain ⟨hand,_,x,hx,hfalse⟩ := hmem.2
  have hjs : j∉S := by
    intro hs
    rw [redirect_gate hjb,ite_eq_left hs] at hand
    cases hand
  have hop : (gateAt C j).op=GateOp.and := by
    simpa [redirect_gate hjb,hjs] using hand
  have hv : gateVal n C j x=true := by
    apply overwrite_rel (n := n) (R := fun a b => b=true → a=true) (fun _ => id) opMono_reverse
      (by simp) hC _ (n+j) hx
    intro r hr hs
    change val (redirect C S i) (List.ofFn x) (n+r)=true → _
    rw [redirect_val (by simp) hr hs (hi r hs),hn x hfalse]
    intro h
    cases h
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hjb,hop,hjb,x,hv,hfalse⟩,hjs⟩



lemma circuit_ext (C D : Circuit) (hl : C.gates.length=D.gates.length)
    (hg : ∀ j<C.gates.length, gateAt C j=gateAt D j) (ho : C.output=D.output) : C=D := by
  have hgs : C.gates=D.gates := by
    apply List.ext_getElem hl
    intro j hj hj'
    rw [← gateAt_eq hj,← gateAt_eq hj']
    exact hg j hj
  cases C
  cases D
  cases hgs
  cases ho
  rfl

lemma clamp_prepend (n : ℕ) (D C : Circuit) (S : Finset ℕ) (b : Bool) :
    clamp (prepend n D C) (S.image (fun r => D.gates.length+r)) b =
      prepend n D (clamp C S b) := by
  apply circuit_ext
  · simp [clamp,overwrite_length,prepend_length]
  · intro j hj
    have hj' : j<D.gates.length+C.gates.length := by
      simpa [clamp,overwrite_length,prepend_length] using hj
    rw [clamp_gate (by simpa [prepend_length] using hj')]
    by_cases hd : j<D.gates.length
    · have hs : j∉S.image (fun r => D.gates.length+r) := by
        rintro hm
        obtain ⟨r,hr,heq⟩ := Finset.mem_image.mp hm
        omega
      rw [ite_eq_right hs,prepend_gate_left hd,prepend_gate_left hd]
    · obtain ⟨r,rfl⟩ : ∃ r,j=D.gates.length+r := ⟨j-D.gates.length,by omega⟩
      have hr : r<C.gates.length := by omega
      have hs : D.gates.length+r ∈ S.image (fun r => D.gates.length+r) ↔ r∈S := by simp
      rw [prepend_gate_right hr,prepend_gate_right (by simpa [clamp,overwrite_length] using hr),clamp_gate hr]
      simp only [hs]
      split_ifs
      · simp [shiftGate,constGate]
      · rfl
  · rfl

theorem joint_pivotal_class_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hC : Monotone2 C) (hD : Monotone2 D)
    (hf : circuitFun n C = graphFun G ∅) (hclean : junk G D = ∅)
    (hout : D.output < n+D.gates.length)
    (hnegative : ∀ x : Fin n → Bool, graphFun G ∅ x = false → circuitFun n D x = false)
    (S : Finset ℕ) (hbound : ∀ r ∈ S, r<C.gates.length)
    (hcover : ∀ u v : Fin n, G.Adj u v → circuitFun n (clamp C S false) (pairInput u v)=false →
      circuitFun n D (pairInput u v)=true)
    (hbudget : D.size≤S.card) :
    ∃ E : Circuit, Monotone2 E ∧ circuitFun n E=graphFun G ∅ ∧
      E.size≤C.size ∧ (junk G E).card≤(junk G C).card ∧
      ((∃ r∈S, r∈junk G C) → (junk G E).card<(junk G C).card) := by
  classical
  let P := prepend n D C
  let T := S.image (fun r => D.gates.length+r)
  let R := redirect P T D.output
  have hP : Monotone2 P := prepend_mono hD hC
  have hR : Monotone2 R := redirect_mono T D.output hP
  have hPF : circuitFun n P=graphFun G ∅ := (prepend_fun n D C).trans hf
  have hsize : P.size=D.size+C.size := prepend_length n D C
  have hRS : R.size=P.size := overwrite_length P T _
  have inj : Function.Injective (fun r => D.gates.length+r) := by
    intro a b h
    exact Nat.add_left_cancel h
  have hcard : T.card=S.card := Finset.card_image_of_injective S inj
  have hb : ∀ r∈T, r<P.gates.length ∧ D.output<n+r := by
    intro r hr
    obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp hr
    subst r
    have := hbound a ha
    change D.gates.length+a<(prepend n D C).gates.length ∧ _
    rw [prepend_length]
    constructor <;> omega
  have hi : ∀ r∈T, D.output<n+r := fun r hr => (hb r hr).2
  have hv (x : Fin n → Bool) : val R (List.ofFn x) D.output=circuitFun n D x := by
    rw [redirect_prefix P T D.output (m := D.gates.length)
      (by change D.gates.length≤(prepend n D C).gates.length; rw [prepend_length]; omega)
      (by intro r hr; obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp hr; omega)
      (List.ofFn x) (by simp) D.output hout]
    exact prepend_val_left D C (by simp) D.output hout
  have hn : ∀ x : Fin n → Bool, graphFun G ∅ x=false → val R (List.ofFn x) D.output=false := by
    intro x hx
    rw [hv,hnegative x hx]
  have hp : ∀ u v : Fin n, G.Adj u v → circuitFun n (clamp P T false) (pairInput u v)=false →
      val R (List.ofFn (pairInput u v)) D.output=true := by
    intro u v huv hcl
    change circuitFun n (clamp (prepend n D C) (S.image (fun r => D.gates.length+r)) false)
      (pairInput u v)=false at hcl
    rw [clamp_prepend,prepend_fun] at hcl
    rw [hv]
    exact hcover u v huv hcl
  have hRF : circuitFun n R=graphFun G ∅ := joint_pivotal_redirect G P hP hPF T D.output hi hn hp
  have hRb : ∀ r∈T, r<R.gates.length ∧ D.output<n+r := by
    intro r hr
    simpa [R,redirect,overwrite_length] using hb r hr
  have hRw : ∀ r∈T, ∀ x : Fin n → Bool, graphFun G ∅ x=false →
      val R (List.ofFn x) D.output=true → val R (List.ofFn x) (n+r)=true := by
    intro r hr x _ hx
    rw [redirect_val (by simp) (hb r hr).1 hr (hi r hr)]
    exact hx
  have hRe : ∀ r∈T, ∀ u v : Fin n, G.Adj u v →
      val R (List.ofFn (pairInput u v)) (n+r)=true → val R (List.ofFn (pairInput u v)) D.output=true := by
    intro r hr u v _ hx
    rw [redirect_val (by simp) (hb r hr).1 hr (hi r hr)] at hx
    exact hx
  obtain ⟨E,hE,hEF,hES,hle,hstrict⟩ := erase_covered_class G T R hR hRF D.output hRb hRw hRe
  have hsub : junk G R ⊆ (junk G P) \ T := redirect_dirty_subset G P hP T D.output hi hn
  have hnoninc : (junk G R).card≤(junk G P).card :=
    Finset.card_le_card (hsub.trans Finset.sdiff_subset)
  have hdirty : (junk G P).card=(junk G C).card := prepend_dirty_card G D C hclean
  refine ⟨E,hE,hEF,?_,?_,?_⟩
  · rw [hcard,hRS,hsize] at hES
    omega
  · rw [← hdirty]
    exact hle.trans hnoninc
  · rintro ⟨r,hr,hd⟩
    have hT : D.gates.length+r∈T := Finset.mem_image.mpr ⟨r,hr,rfl⟩
    have hdP : D.gates.length+r∈junk G P := (prepend_dirty_right G D C r (hbound r hr)).mpr hd
    have hsub' : junk G R ⊆ (junk G P).erase (D.gates.length+r) := by
      intro a ha
      have ham := Finset.mem_sdiff.mp (hsub ha)
      exact Finset.mem_erase.mpr ⟨by intro heq; subst a; exact ham.2 hT,ham.1⟩
    have hle' := Finset.card_le_card hsub'
    have hcard' := Finset.card_erase_add_one hdP
    rw [← hdirty]
    omega

end PEqualNP.Outside.L_meta_1772_aux.JointPivotalReplacement
