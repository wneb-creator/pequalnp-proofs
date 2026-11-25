import PEqualNP.Defs

-- Bypass helpers adapted from willakone, L-meta-1499, PR 3112.
namespace PEqualNP.Outside.L_meta_1772_aux.MixedFilter

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

lemma val_equal_except {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n)
    (hlen : D.gates.length = C.gates.length) (k j : ℕ) (hkj : k < j)
    (same : ∀ m < C.gates.length, m ≠ k → gateAt D m = gateAt C m)
    (reader : ∀ m < C.gates.length, n + k ∈ (gateAt C m).inputs → m = j)
    (repair : (∀ u, u < n + j → u ≠ n + k → val D x u = val C x u) →
      val D x (n + j) = val C x (n + j)) :
    ∀ u, u ≠ n + k → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hne
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · by_cases huge : n + C.gates.length ≤ u
      · rw [val_ge hx huge, val_ge hx (by omega)]
      · obtain ⟨m, rfl⟩ : ∃ m, u = n + m := ⟨u - n, by omega⟩
        have hm : m < C.gates.length := by omega
        by_cases hmj : m = j
        · subst m
          exact repair (fun v hv hnv => ih v hv hnv)
        · rw [val_gate hx (by omega : m < D.gates.length), val_gate hx hm,
            same m hm (by omega)]
          congr 1
          apply List.map_congr_left
          intro v hv
          by_cases hvm : v < n + m
          · rw [ite_eq_left hvm, ite_eq_left hvm]
            apply ih v hvm
            intro heq
            subst v
            exact hmj (reader m hm hv)
          · rw [ite_eq_right hvm, ite_eq_right hvm]

def replace (C : Circuit) (k : ℕ) (g : Gate) : Circuit :=
  ⟨C.gates.set k g, C.output⟩

lemma replace_length (C : Circuit) (k : ℕ) (g : Gate) :
    (replace C k g).gates.length = C.gates.length := by
  simp [replace]

lemma replace_gate_eq (C : Circuit) (k : ℕ) (g : Gate) (hk : k < C.gates.length) :
    gateAt (replace C k g) k = g := by
  rw [gateAt_eq (by simpa [replace] using hk)]
  simp [replace]

lemma replace_gate_ne (C : Circuit) (k m : ℕ) (g : Gate)
    (hm : m < C.gates.length) (hne : m ≠ k) :
    gateAt (replace C k g) m = gateAt C m := by
  rw [gateAt_eq (by simpa [replace] using hm), gateAt_eq hm]
  simp [replace, hne, hne.symm]

lemma filter_absorb (a b s t : Bool) (h : t = true → a = true) :
    (((a && b) || s) && t) = ((b || s) && t) := by
  cases a <;> cases b <;> cases s <;> cases t <;> simp_all

lemma mixed_filter_preserves
    (n : ℕ) (C : Circuit) (i k j a b s t : ℕ)
    (hmono : Monotone2 C) (hik : i < k) (hkj : k < j) (hj : j < C.gates.length)
    (ha : a < n + i) (hb : b < n + i) (hs : s < n + k) (ht : t < n + j)
    (htk : t ≠ n + k)
    (gi : gateAt C i = ⟨GateOp.and, [a, b]⟩)
    (gk : gateAt C k = ⟨GateOp.or, [n + i, s]⟩)
    (gj : gateAt C j = ⟨GateOp.and, [n + k, t]⟩)
    (reader : ∀ m < C.gates.length, n + k ∈ (gateAt C m).inputs → m = j)
    (hout : C.output ≠ n + k)
    (dom : ∀ x : Fin n → Bool,
      val C (List.ofFn x) t = true → val C (List.ofFn x) a = true) :
    let D := replace C k ⟨GateOp.or, [b, s]⟩
    Monotone2 D ∧ D.size = C.size ∧ circuitFun n D = circuitFun n C ∧
      ∀ (x : Fin n → Bool) u, u ≠ n + k → val D (List.ofFn x) u = val C (List.ofFn x) u := by
  let D := replace C k ⟨GateOp.or, [b, s]⟩
  have hk : k < C.gates.length := hkj.trans hj
  have hi : i < C.gates.length := hik.trans hk
  have hlen : D.gates.length = C.gates.length := replace_length C k _
  have same : ∀ m < C.gates.length, m ≠ k → gateAt D m = gateAt C m :=
    fun m hm hne => replace_gate_ne C k m _ hm hne
  have values : ∀ (x : Fin n → Bool) u, u ≠ n + k →
      val D (List.ofFn x) u = val C (List.ofFn x) u := by
    intro x
    apply val_equal_except (n := n) (by simp) hlen k j hkj same reader
    intro pre
    have vi : val C (List.ofFn x) (n + i) =
        (val C (List.ofFn x) a && val C (List.ofFn x) b) := by
      rw [val_gate (n := n) (by simp) hi, gi]
      simp [GateOp.eval, ha, hb]
    have vk : val C (List.ofFn x) (n + k) =
        (val C (List.ofFn x) (n + i) || val C (List.ofFn x) s) := by
      rw [val_gate (n := n) (by simp) hk, gk]
      simp [GateOp.eval, hs, show n + i < n + k by omega]
    have vkD : val D (List.ofFn x) (n + k) =
        (val C (List.ofFn x) b || val C (List.ofFn x) s) := by
      rw [val_gate (n := n) (by simp) (by omega : k < D.gates.length),
        show gateAt D k = ⟨GateOp.or, [b, s]⟩ from replace_gate_eq C k _ hk]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, ite_eq_left (show b < n + k by omega), ite_eq_left hs]
      rw [pre b (by omega) (by omega), pre s (by omega) (by omega)]
      rfl
    have vj : val C (List.ofFn x) (n + j) =
        (val C (List.ofFn x) (n + k) && val C (List.ofFn x) t) := by
      rw [val_gate (n := n) (by simp) hj, gj]
      simp [GateOp.eval, ht, show n + k < n + j by omega]
    have vjD : val D (List.ofFn x) (n + j) =
        (val D (List.ofFn x) (n + k) && val C (List.ofFn x) t) := by
      rw [val_gate (n := n) (by simp) (by omega : j < D.gates.length),
        same j hj (by omega), gj]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, ite_eq_left (show n + k < n + j by omega), ite_eq_left ht]
      rw [pre t ht htk]
      rfl
    rw [vjD, vj, vkD, vk, vi]
    exact (filter_absorb _ _ _ _ (dom x)).symm
  refine ⟨?_, ?_, ?_, values⟩
  · intro g hg
    rcases List.mem_or_eq_of_mem_set hg with old | new
    · exact hmono g old
    · subst g
      exact ⟨Or.inr rfl, by simp⟩
  · exact hlen
  · funext x
    exact values x C.output hout

end PEqualNP.Outside.L_meta_1772_aux.MixedFilter

