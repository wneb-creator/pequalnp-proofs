import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9811.BlockingAll
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

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def transparent (p q : ℕ) (b : Bool) (g : Gate) : Prop :=
  p ∉ g.inputs ∨
  (g.op = GateOp.and ∧ q ∈ g.inputs ∧ b = false) ∨
  (g.op = GateOp.or ∧ q ∈ g.inputs ∧ b = true)

lemma and_block {n : ℕ} (C : Circuit) (x : Fin n → Bool) (q : Fin n) (r : ℕ)
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and)
    (hq : q.val ∈ (gateAt C r).inputs) (hx : x q = false) :
    val C (List.ofFn x) (n + r) = false := by
  cases hv : val C (List.ofFn x) (n + r) with
  | false => rfl
  | true =>
    have h := ((val_and (n := n) (by simp) hr hop).mp hv q.val hq).2
    rw [val_ofFn, hx] at h
    cases h

lemma or_block {n : ℕ} (C : Circuit) (x : Fin n → Bool) (q : Fin n) (r : ℕ)
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or)
    (hq : q.val ∈ (gateAt C r).inputs) (hx : x q = true) :
    val C (List.ofFn x) (n + r) = true := by
  apply (val_or (n := n) (by simp) hr hop).mpr
  exact ⟨q.val,hq,by have := q.isLt; omega,by rw [val_ofFn,hx]⟩

lemma transparent_agreement {n : ℕ} (C : Circuit) (p q : Fin n) (b : Bool)
    (x y : Fin n → Bool) (hxy : ∀ i, i ≠ p → x i = y i)
    (hx : x q = b) (hy : y q = b)
    (hc : ∀ r < C.gates.length, transparent p.val q.val b (gateAt C r)) :
    ∀ w, w ≠ p.val → val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwp
    by_cases hwn : w < n
    · have he := hxy ⟨w,hwn⟩ (by intro he; apply hwp; exact congrArg Fin.val he)
      rw [val_ofFn C x ⟨w,hwn⟩,val_ofFn C y ⟨w,hwn⟩]
      exact he
    by_cases hwl : n + C.gates.length ≤ w
    · rw [val_ge (n := n) (by simp) hwl, val_ge (n := n) (by simp) hwl]
    obtain ⟨r,rfl⟩ : ∃ r, w = n + r := ⟨w - n,by omega⟩
    have hr : r < C.gates.length := by omega
    rcases hc r hr with hn | ⟨hop,hq,hb⟩ | ⟨hop,hq,hb⟩
    · rw [val_gate (n := n) (by simp) hr, val_gate (n := n) (by simp) hr]
      congr 1
      apply List.map_congr_left
      intro k hk
      by_cases hkr : k < n + r
      · rw [if_pos hkr,if_pos hkr]
        exact ih k hkr (by intro he; subst k; exact hn hk)
      · rw [if_neg hkr,if_neg hkr]
    · rw [and_block C x q r hr hop hq (hx.trans hb),
        and_block C y q r hr hop hq (hy.trans hb)]
    · rw [or_block C x q r hr hop hq (hx.trans hb),
        or_block C y q r hr hop hq (hy.trans hb)]

def target (x : Fin 14 → Bool) : Bool :=
  ([(0,8),(0,10),(1,7),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),
    (4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] :
    List (Fin 14 × Fin 14)).any fun e => x e.1 && x e.2

def witness (q k : Fin 14) (b : Bool) : Fin 14 → Bool :=
  fun i => (decide (i = q) && b) || decide (i = k)

set_option maxHeartbeats 0 in
lemma robust_witness : ∀ p q : Fin 14, p ≠ q → ∀ b : Bool, ∃ k : Fin 14,
    witness q k b q = b ∧
    target (Function.update (witness q k b) p false) ≠
    target (Function.update (witness q k b) p true) := by
  decide +kernel

lemma no_transparent_target (C : Circuit) (p q : Fin 14) (hpq : p ≠ q)
    (b : Bool) (ho : C.output ≠ p.val)
    (hf : ∀ x, C.eval (List.ofFn x) = target x) :
    ¬ ∀ r < C.gates.length, transparent p.val q.val b (gateAt C r) := by
  intro hc
  obtain ⟨k,hk,ht⟩ := robust_witness p q hpq b
  let x := Function.update (witness q k b) p false
  let y := Function.update (witness q k b) p true
  have hxy : ∀ i, i ≠ p → x i = y i := by
    intro i hip
    simp [x,y,Function.update_of_ne hip]
  have hx : x q = b := by simp [x,Function.update_of_ne hpq.symm,hk]
  have hy : y q = b := by simp [y,Function.update_of_ne hpq.symm,hk]
  have he := transparent_agreement C p q b x y hxy hx hy hc C.output ho
  change C.eval (List.ofFn x) = C.eval (List.ofFn y) at he
  rw [hf x,hf y] at he
  exact ht he

lemma sole_reader_not_primary_binary (C : Circuit) (p q : Fin 14) (hpq : p ≠ q)
    (r : ℕ) (ho : C.output ≠ p.val)
    (hf : ∀ x, C.eval (List.ofFn x) = target x)
    (hsole : ∀ s < C.gates.length, p.val ∈ (gateAt C s).inputs → s = r)
    (hq : q.val ∈ (gateAt C r).inputs) :
    (gateAt C r).op ≠ GateOp.and ∧ (gateAt C r).op ≠ GateOp.or := by
  constructor <;> intro hop
  · apply no_transparent_target C p q hpq false ho hf
    intro s hs
    by_cases hp : p.val ∈ (gateAt C s).inputs
    · rw [hsole s hs hp]
      exact Or.inr (Or.inl ⟨hop,hq,rfl⟩)
    · exact Or.inl hp

  · apply no_transparent_target C p q hpq true ho hf
    intro s hs
    by_cases hp : p.val ∈ (gateAt C s).inputs
    · rw [hsole s hs hp]
      exact Or.inr (Or.inr ⟨hop,hq,rfl⟩)
    · exact Or.inl hp

lemma semantic_agreement {n : ℕ} (C : Circuit) (p : Fin n)
    (x y : Fin n → Bool) (hxy : ∀ i, i ≠ p → x i = y i)
    (hc : ∀ r < C.gates.length, p.val ∉ (gateAt C r).inputs ∨
      val C (List.ofFn x) (n+r) = val C (List.ofFn y) (n+r)) :
    ∀ w, w ≠ p.val → val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwp
    by_cases hwn : w < n
    · rw [val_ofFn C x ⟨w,hwn⟩,val_ofFn C y ⟨w,hwn⟩]
      exact hxy ⟨w,hwn⟩ (by intro he; apply hwp; exact congrArg Fin.val he)
    by_cases hwl : n + C.gates.length ≤ w
    · rw [val_ge (n := n) (by simp) hwl, val_ge (n := n) (by simp) hwl]
    obtain ⟨r,rfl⟩ : ∃ r, w = n + r := ⟨w-n,by omega⟩
    have hr : r < C.gates.length := by omega
    rcases hc r hr with hn | he
    · rw [val_gate (n := n) (by simp) hr, val_gate (n := n) (by simp) hr]
      congr 1
      apply List.map_congr_left
      intro k hk
      by_cases hkr : k < n + r
      · rw [if_pos hkr,if_pos hkr]
        exact ih k hkr (by intro he; subst k; exact hn hk)
      · rw [if_neg hkr,if_neg hkr]
    · exact he

lemma sole_reader_contradiction (C : Circuit) (p : Fin 14) (r : ℕ)
    (x y : Fin 14 → Bool) (hxy : ∀ i, i ≠ p → x i = y i)
    (ho : C.output ≠ p.val) (hf : ∀ x, C.eval (List.ofFn x) = target x)
    (hsole : ∀ s < C.gates.length, p.val ∈ (gateAt C s).inputs → s = r)
    (hval : val C (List.ofFn x) (14+r) = val C (List.ofFn y) (14+r))
    (ht : target x ≠ target y) : False := by
  have hc : ∀ s < C.gates.length, p.val ∉ (gateAt C s).inputs ∨
      val C (List.ofFn x) (14+s) = val C (List.ofFn y) (14+s) := by
    intro s hs
    by_cases hp : p.val ∈ (gateAt C s).inputs
    · exact Or.inr (by rw [hsole s hs hp]; exact hval)
    · exact Or.inl hp
  have he := semantic_agreement C p x y hxy hc C.output ho
  change C.eval (List.ofFn x) = C.eval (List.ofFn y) at he
  rw [hf x,hf y] at he
  exact ht he

lemma and_block_wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (q r : ℕ)
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and)
    (hq : q ∈ (gateAt C r).inputs) (hx : val C (List.ofFn x) q = false) :
    val C (List.ofFn x) (n+r) = false := by
  cases hv : val C (List.ofFn x) (n+r) with
  | false => rfl
  | true =>
    have h := ((val_and (n := n) (by simp) hr hop).mp hv q hq).2
    rw [hx] at h
    cases h

lemma or_block_wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (q r : ℕ)
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or)
    (hq : q ∈ (gateAt C r).inputs) (hqr : q < n+r)
    (hx : val C (List.ofFn x) q = true) :
    val C (List.ofFn x) (n+r) = true := by
  exact (val_or (n := n) (by simp) hr hop).mpr ⟨q,hq,hqr,hx⟩

lemma sole_reader_not_and_and (C : Circuit) (p q : Fin 14) (hpq : p ≠ q)
    (r t : ℕ) (hr : r < C.gates.length) (ht : t < C.gates.length)
    (ho : C.output ≠ p.val) (hf : ∀ x, C.eval (List.ofFn x) = target x)
    (hsole : ∀ s < C.gates.length, p.val ∈ (gateAt C s).inputs → s = r)
    (hqr : 14+t ∈ (gateAt C r).inputs) (hqt : q.val ∈ (gateAt C t).inputs)
    (hopt : (gateAt C t).op = GateOp.and) : (gateAt C r).op ≠ GateOp.and := by
  intro hopr
  obtain ⟨k,hk,hfneq⟩ := robust_witness p q hpq false
  let x := Function.update (witness q k false) p false
  let y := Function.update (witness q k false) p true
  have hx : x q = false := by simp [x,Function.update_of_ne hpq.symm,hk]
  have hy : y q = false := by simp [y,Function.update_of_ne hpq.symm,hk]
  have hvx := and_block_wire C x (14+t) r hr hopr hqr (and_block C x q t ht hopt hqt hx)
  have hvy := and_block_wire C y (14+t) r hr hopr hqr (and_block C y q t ht hopt hqt hy)
  exact sole_reader_contradiction C p r x y (by
    intro i hip; simp [x,y,Function.update_of_ne hip]) ho hf hsole (hvx.trans hvy.symm) hfneq

lemma sole_reader_not_or_or (C : Circuit) (p q : Fin 14) (hpq : p ≠ q)
    (r t : ℕ) (hr : r < C.gates.length) (htr : t < r)
    (ho : C.output ≠ p.val) (hf : ∀ x, C.eval (List.ofFn x) = target x)
    (hsole : ∀ s < C.gates.length, p.val ∈ (gateAt C s).inputs → s = r)
    (hqr : 14+t ∈ (gateAt C r).inputs) (hqt : q.val ∈ (gateAt C t).inputs)
    (hopt : (gateAt C t).op = GateOp.or) : (gateAt C r).op ≠ GateOp.or := by
  intro hopr
  have ht : t < C.gates.length := by omega
  obtain ⟨k,hk,hfneq⟩ := robust_witness p q hpq true
  let x := Function.update (witness q k true) p false
  let y := Function.update (witness q k true) p true
  have hx : x q = true := by simp [x,Function.update_of_ne hpq.symm,hk]
  have hy : y q = true := by simp [y,Function.update_of_ne hpq.symm,hk]
  have hvx := or_block_wire C x (14+t) r hr hopr hqr (by omega) (or_block C x q t ht hopt hqt hx)
  have hvy := or_block_wire C y (14+t) r hr hopr hqr (by omega) (or_block C y q t ht hopt hqt hy)
  exact sole_reader_contradiction C p r x y (by
    intro i hip; simp [x,y,Function.update_of_ne hip]) ho hf hsole (hvx.trans hvy.symm) hfneq

def single (k : Fin 14) : Fin 14 → Bool := fun i => decide (i = k)

set_option maxHeartbeats 0 in
lemma degree_three_witness : ∀ p a b : Fin 14,
    p ∉ ({0,1,7,9} : Finset (Fin 14)) → ∃ k : Fin 14,
    k ≠ a ∧ k ≠ b ∧
    target (Function.update (single k) p false) ≠
    target (Function.update (single k) p true) := by
  decide +kernel

lemma or_two_false {n : ℕ} (C : Circuit) (x : Fin n → Bool) (a b : Fin n) (t : ℕ)
    (ht : t < C.gates.length) (hop : (gateAt C t).op = GateOp.or)
    (hin : (gateAt C t).inputs = [a.val,b.val]) (ha : x a = false) (hb : x b = false) :
    val C (List.ofFn x) (n+t) = false := by
  cases hv : val C (List.ofFn x) (n+t) with
  | false => rfl
  | true =>
    obtain ⟨q,hq,_,he⟩ := (val_or (n := n) (by simp) ht hop).mp hv
    rw [hin] at hq
    simp at hq
    rcases hq with rfl | rfl
    · rw [val_ofFn,ha] at he; cases he
    · rw [val_ofFn,hb] at he; cases he

lemma degree_three_sole_reader_not_and_or (C : Circuit) (p a b : Fin 14)
    (hp : p ∉ ({0,1,7,9} : Finset (Fin 14)))
    (r t : ℕ) (hr : r < C.gates.length) (htr : t < r)
    (ho : C.output ≠ p.val) (hf : ∀ x, C.eval (List.ofFn x) = target x)
    (hsole : ∀ s < C.gates.length, p.val ∈ (gateAt C s).inputs → s = r)
    (hqr : 14+t ∈ (gateAt C r).inputs)
    (hqt : (gateAt C t).inputs = [a.val,b.val])
    (hopt : (gateAt C t).op = GateOp.or) : (gateAt C r).op ≠ GateOp.and := by
  intro hopr
  have ht : t < C.gates.length := by omega
  have hap : a ≠ p := by
    intro he; subst a
    have he := hsole t ht (by simp [hqt])
    omega
  have hbp : b ≠ p := by
    intro he; subst b
    have he := hsole t ht (by simp [hqt])
    omega
  obtain ⟨k,hka,hkb,hfneq⟩ := degree_three_witness p a b hp
  let x := Function.update (single k) p false
  let y := Function.update (single k) p true
  have hxa : x a = false := by simp [x,single,Function.update_of_ne hap,hka.symm]
  have hxb : x b = false := by simp [x,single,Function.update_of_ne hbp,hkb.symm]
  have hya : y a = false := by simp [y,single,Function.update_of_ne hap,hka.symm]
  have hyb : y b = false := by simp [y,single,Function.update_of_ne hbp,hkb.symm]
  have hvx := and_block_wire C x (14+t) r hr hopr hqr (or_two_false C x a b t ht hopt hqt hxa hxb)
  have hvy := and_block_wire C y (14+t) r hr hopr hqr (or_two_false C y a b t ht hopt hqt hya hyb)
  exact sole_reader_contradiction C p r x y (by
    intro i hip; simp [x,y,Function.update_of_ne hip]) ho hf hsole (hvx.trans hvy.symm) hfneq

def pair (a b : Fin 14) : Fin 14 → Bool := fun i => decide (i = a) || decide (i = b)
def triple (a b k : Fin 14) : Fin 14 → Bool := fun i => pair a b i || decide (i = k)

set_option maxHeartbeats 0 in
lemma degree_three_pair_witness : ∀ p a b : Fin 14,
    p ∉ ({0,1,7,9} : Finset (Fin 14)) → a ≠ p → b ≠ p →
    target (pair a b) = false → ∃ k : Fin 14,
    target (Function.update (triple a b k) p false) ≠
    target (Function.update (triple a b k) p true) := by
  decide +kernel

lemma and_two_true {n : ℕ} (C : Circuit) (x : Fin n → Bool) (a b : Fin n) (t : ℕ)
    (ht : t < C.gates.length) (hop : (gateAt C t).op = GateOp.and)
    (hin : (gateAt C t).inputs = [a.val,b.val]) (ha : x a = true) (hb : x b = true) :
    val C (List.ofFn x) (n+t) = true := by
  apply (val_and (n := n) (by simp) ht hop).mpr
  intro q hq
  rw [hin] at hq
  simp at hq
  rcases hq with rfl | rfl
  · exact ⟨by have := a.isLt; omega,by rw [val_ofFn,ha]⟩
  · exact ⟨by have := b.isLt; omega,by rw [val_ofFn,hb]⟩

lemma degree_three_sole_reader_or_and_is_edge (C : Circuit) (p a b : Fin 14)
    (hp : p ∉ ({0,1,7,9} : Finset (Fin 14)))
    (r t : ℕ) (hr : r < C.gates.length) (htr : t < r)
    (ho : C.output ≠ p.val) (hf : ∀ x, C.eval (List.ofFn x) = target x)
    (hsole : ∀ s < C.gates.length, p.val ∈ (gateAt C s).inputs → s = r)
    (hqr : 14+t ∈ (gateAt C r).inputs)
    (hqt : (gateAt C t).inputs = [a.val,b.val])
    (hopt : (gateAt C t).op = GateOp.and) (hopr : (gateAt C r).op = GateOp.or) :
    target (pair a b) = true := by
  cases hab : target (pair a b) with
  | true => rfl
  | false =>
    exfalso
    have ht : t < C.gates.length := by omega
    have hap : a ≠ p := by
      intro he; subst a
      have he := hsole t ht (by simp [hqt])
      omega
    have hbp : b ≠ p := by
      intro he; subst b
      have he := hsole t ht (by simp [hqt])
      omega
    obtain ⟨k,hfneq⟩ := degree_three_pair_witness p a b hp hap hbp hab
    let x := Function.update (triple a b k) p false
    let y := Function.update (triple a b k) p true
    have hxa : x a = true := by simp [x,triple,pair,Function.update_of_ne hap]
    have hxb : x b = true := by simp [x,triple,pair,Function.update_of_ne hbp]
    have hya : y a = true := by simp [y,triple,pair,Function.update_of_ne hap]
    have hyb : y b = true := by simp [y,triple,pair,Function.update_of_ne hbp]
    have hvx := or_block_wire C x (14+t) r hr hopr hqr (by omega)
      (and_two_true C x a b t ht hopt hqt hxa hxb)
    have hvy := or_block_wire C y (14+t) r hr hopr hqr (by omega)
      (and_two_true C y a b t ht hopt hqt hya hyb)
    exact sole_reader_contradiction C p r x y (by
      intro i hip; simp [x,y,Function.update_of_ne hip]) ho hf hsole (hvx.trans hvy.symm) hfneq

lemma not_primary {n : ℕ} (C : Circuit) (x : Fin n → Bool) (q : Fin n) (t : ℕ)
    (ht : t < C.gates.length) (hop : (gateAt C t).op = GateOp.not)
    (hin : (gateAt C t).inputs = [q.val]) :
    val C (List.ofFn x) (n+t) = !x q := by
  rw [val_gate (n := n) (by simp) ht,hop,hin]
  have hq : q.val < n+t := by have := q.isLt; omega
  simp [GateOp.eval,hq,val_ofFn C x q]

lemma sole_reader_not_negated_primary (C : Circuit) (p q : Fin 14) (hpq : p ≠ q)
    (r t : ℕ) (hr : r < C.gates.length) (htr : t < r)
    (ho : C.output ≠ p.val) (hf : ∀ x, C.eval (List.ofFn x) = target x)
    (hsole : ∀ s < C.gates.length, p.val ∈ (gateAt C s).inputs → s = r)
    (hqr : 14+t ∈ (gateAt C r).inputs)
    (hqt : (gateAt C t).inputs = [q.val])
    (hopt : (gateAt C t).op = GateOp.not) :
    (gateAt C r).op ≠ GateOp.and ∧ (gateAt C r).op ≠ GateOp.or := by
  have ht : t < C.gates.length := by omega
  constructor <;> intro hopr
  · obtain ⟨k,hk,hfneq⟩ := robust_witness p q hpq true
    let x := Function.update (witness q k true) p false
    let y := Function.update (witness q k true) p true
    have hx : x q = true := by simp [x,Function.update_of_ne hpq.symm,hk]
    have hy : y q = true := by simp [y,Function.update_of_ne hpq.symm,hk]
    have htx : val C (List.ofFn x) (14+t) = false := by rw [not_primary C x q t ht hopt hqt,hx]; rfl
    have hty : val C (List.ofFn y) (14+t) = false := by rw [not_primary C y q t ht hopt hqt,hy]; rfl
    have hvx := and_block_wire C x (14+t) r hr hopr hqr htx
    have hvy := and_block_wire C y (14+t) r hr hopr hqr hty
    exact sole_reader_contradiction C p r x y (by
      intro i hip; simp [x,y,Function.update_of_ne hip]) ho hf hsole (hvx.trans hvy.symm) hfneq
  · obtain ⟨k,hk,hfneq⟩ := robust_witness p q hpq false
    let x := Function.update (witness q k false) p false
    let y := Function.update (witness q k false) p true
    have hx : x q = false := by simp [x,Function.update_of_ne hpq.symm,hk]
    have hy : y q = false := by simp [y,Function.update_of_ne hpq.symm,hk]
    have htx : val C (List.ofFn x) (14+t) = true := by rw [not_primary C x q t ht hopt hqt,hx]; rfl
    have hty : val C (List.ofFn y) (14+t) = true := by rw [not_primary C y q t ht hopt hqt,hy]; rfl
    have hvx := or_block_wire C x (14+t) r hr hopr hqr (by omega) htx
    have hvy := or_block_wire C y (14+t) r hr hopr hqr (by omega) hty
    exact sole_reader_contradiction C p r x y (by
      intro i hip; simp [x,y,Function.update_of_ne hip]) ho hf hsole (hvx.trans hvy.symm) hfneq

end PEqualNP.Outside.L_meta_9811.BlockingAll

