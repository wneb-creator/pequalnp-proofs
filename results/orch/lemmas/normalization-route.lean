import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2685

lemma and_below_linear {α : Type*} (A : Finset α)
    (f g : (α → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (f x && g x) = true → ∃ a ∈ A, x a = true) :
    (∀ x, f x = true → ∃ a ∈ A, x a = true) ∨
      (∀ x, g x = true → ∃ a ∈ A, x a = true) := by
  classical
  by_cases hfA : ∀ x, f x = true → ∃ a ∈ A, x a = true
  · exact Or.inl hfA
  right
  intro y hgy
  by_contra hy
  obtain ⟨x, hx⟩ := not_forall.mp hfA
  obtain ⟨hfx, hx⟩ := not_imp.mp hx
  let z : α → Bool := fun a => x a || y a
  have hxz : x ≤ z := by
    intro a
    change x a ≤ (x a || y a)
    cases x a <;> cases y a <;> decide
  have hyz : y ≤ z := by
    intro a
    change y a ≤ (x a || y a)
    cases x a <;> cases y a <;> decide
  have hfz : f z = true := le_antisymm le_top (hfx ▸ hf hxz)
  have hgz : g z = true := le_antisymm le_top (hgy ▸ hg hyz)
  obtain ⟨a, ha, hza⟩ := h z (by simp only [hfz, hgz, Bool.and_self])
  have hxa : x a = false := by
    cases hxa : x a
    · rfl
    · exact False.elim (hx ⟨a, ha, hxa⟩)
  have hya : y a = false := by
    cases hya : y a
    · rfl
    · exact False.elim (hy ⟨a, ha, hya⟩)
  simp only [z, hxa, hya, Bool.or_self, Bool.false_eq_true] at hza

def oneInput {α : Type*} [DecidableEq α] (a : α) : α → Bool :=
  fun b => decide (b = a)

lemma oneInput_le {α : Type*} [DecidableEq α] {a : α} {x : α → Bool}
    (h : x a = true) : oneInput a ≤ x := by
  intro b
  by_cases hb : b = a
  · subst b
    simp only [oneInput, decide_true, h, le_refl]
  · simp only [oneInput, hb, decide_false, Bool.false_le]

lemma below_linear_singleton {α : Type*} [DecidableEq α] (A : Finset α)
    (f : (α → Bool) → Bool)
    (h : ∀ x, f x = true → ∃ a ∈ A, x a = true)
    {a : α} (ha : f (oneInput a) = true) : a ∈ A := by
  obtain ⟨b, hb, hba⟩ := h (oneInput a) ha
  have : b = a := by simpa only [oneInput, decide_eq_true_eq] using hba
  simpa only [this] using hb

lemma linear_or_singletons {α : Type*} [DecidableEq α] (A : Finset α)
    (f g : (α → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (f x || g x) = true ↔ ∃ a ∈ A, x a = true) :
    ∀ x, (f x || g x) = true ↔
      (∃ a, f (oneInput a) = true ∧ x a = true) ∨ g x = true := by
  intro x
  constructor
  · intro hfg
    obtain ⟨a, ha, hxa⟩ := (h x).mp hfg
    have hp : (f (oneInput a) || g (oneInput a)) = true :=
      (h _).mpr ⟨a, ha, by simp only [oneInput, decide_true]⟩
    rw [Bool.or_eq_true_eq_eq_true_or_eq_true] at hp
    rcases hp with hfa | hga
    · exact Or.inl ⟨a, hfa, hxa⟩
    · exact Or.inr (le_antisymm le_top (hga ▸ hg (oneInput_le hxa)))
  · rintro (⟨a, hfa, hxa⟩ | hgx)
    · rw [Bool.or_eq_true_eq_eq_true_or_eq_true]
      exact Or.inl (le_antisymm le_top (hfa ▸ hf (oneInput_le hxa)))
    · rw [Bool.or_eq_true_eq_eq_true_or_eq_true]
      exact Or.inr hgx

lemma shared_singleton_support {α : Type*} [DecidableEq α] (A B : Finset α)
    (f : (α → Bool) → Bool)
    (hA : ∀ x, f x = true → ∃ a ∈ A, x a = true)
    (hB : ∀ x, f x = true → ∃ a ∈ B, x a = true)
    (hAB : ∀ a ∈ A, ∀ b ∈ A, a ∈ B → b ∈ B → a = b)
    {a b : α} (ha : f (oneInput a) = true) (hb : f (oneInput b) = true) :
    a = b := by
  exact hAB a (below_linear_singleton A f hA ha)
    b (below_linear_singleton A f hA hb)
    (below_linear_singleton B f hB ha) (below_linear_singleton B f hB hb)

lemma eq_of_true_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

lemma shared_linear_replace {α β : Type*} [DecidableEq α]
    (A : β → Finset α) (v : (α → Bool) → Bool)
    (h : β → (α → Bool) → Bool) (hv : Monotone v)
    (hh : ∀ k, Monotone (h k))
    (hout : ∀ k x, (v x || h k x) = true ↔ ∃ a ∈ A k, x a = true)
    (i j : β)
    (hij : ∀ a ∈ A i, ∀ b ∈ A i, a ∈ A j → b ∈ A j → a = b) :
    (∀ k x, (v x || h k x) = h k x) ∨
      ∃ a, v (oneInput a) = true ∧
        ∀ k x, (v x || h k x) = (x a || h k x) := by
  classical
  have hbelow (k : β) : ∀ x, v x = true → ∃ a ∈ A k, x a = true := by
    intro x hx
    apply (hout k x).mp
    simp only [hx, Bool.true_or]
  have unique {a b : α} (ha : v (oneInput a) = true)
      (hb : v (oneInput b) = true) : a = b :=
    shared_singleton_support (A i) (A j) v (hbelow i) (hbelow j) hij ha hb
  by_cases hs : ∃ a, v (oneInput a) = true
  · obtain ⟨a, ha⟩ := hs
    right
    refine ⟨a, ha, ?_⟩
    intro k x
    apply eq_of_true_iff
    rw [linear_or_singletons (A k) v (h k) hv (hh k) (hout k) x,
      Bool.or_eq_true_eq_eq_true_or_eq_true]
    apply or_congr _ Iff.rfl
    constructor
    · rintro ⟨b, hb, hxb⟩
      simpa only [unique hb ha] using hxb
    · intro hxa
      exact ⟨a, ha, hxa⟩
  · left
    intro k x
    apply eq_of_true_iff
    rw [linear_or_singletons (A k) v (h k) hv (hh k) (hout k) x]
    constructor
    · rintro (⟨a, ha, _⟩ | hkx)
      · exact False.elim (hs ⟨a, ha⟩)
      · exact hkx
    · exact Or.inr

end PEqualNP.Outside.L_meta_2685

namespace PEqualNP.Outside.L_meta_2685.CircuitNorm

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]; simp [step]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]; simp [hl]

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma fold_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (h : w.length + gs.length ≤ i) : (gs.foldl step w).getD i false = false := by
  rw [List.getD_eq_default]; rw [fold_length]; exact h
def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

lemma fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi; simp at hi

lemma or_factor (a b c d t : Bool) :
    ((a || (b && t)) || (c || (d && t))) =
      ((a || c) || ((b || d) && t)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases t <;> rfl

lemma eval_or_factor (l : List ℕ) (f f₀ f₁ : ℕ → Bool) (t : Bool)
    (h : ∀ i, f i = (f₀ i || (f₁ i && t))) :
    GateOp.or.eval (l.map f) =
      (GateOp.or.eval (l.map f₀) || (GateOp.or.eval (l.map f₁) && t)) := by
  change (l.map f).any id = ((l.map f₀).any id || ((l.map f₁).any id && t))
  induction l with
  | nil => simp
  | cons a l ih =>
    change (f a || (l.map f).any id) =
      ((f₀ a || (l.map f₀).any id) || ((f₁ a || (l.map f₁).any id) && t))
    rw [h a, ih]
    exact or_factor _ _ _ _ _

lemma fold_or_factor (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.or)
    (a b r : List Bool) (t : Bool) (hlb : a.length = b.length)
    (hlr : a.length = r.length)
    (h : ∀ i, a.getD i false = (b.getD i false || (r.getD i false && t))) :
    ∀ i, (gs.foldl step a).getD i false =
      ((gs.foldl step b).getD i false || ((gs.foldl step r).getD i false && t)) := by
  induction gs generalizing a b r with
  | nil => exact h
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hlb]
    · simp [step, hlr]
    · intro i
      unfold step
      by_cases hi : i < a.length
      · rw [List.getD_append _ _ _ _ hi,
          List.getD_append _ _ _ _ (by omega),
          List.getD_append _ _ _ _ (by omega)]
        exact h i
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), ← hlb, ← hlr]
        by_cases he : i - a.length = 0
        · rw [he]
          simp only [List.getD_cons_zero, hgs g List.mem_cons_self]
          exact eval_or_factor _ _ _ _ t h
        · obtain ⟨k, hk⟩ : ∃ k, i - a.length = k + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hk]
          simp

lemma suffix_or_factor (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.or)
    (w : List Bool) (t : Bool) (i : ℕ) :
    (gs.foldl step (w ++ [t])).getD i false =
      ((gs.foldl step (w ++ [false])).getD i false ||
        ((gs.foldl step (List.replicate w.length false ++ [true])).getD i false && t)) := by
  apply fold_or_factor gs hgs (w ++ [t]) (w ++ [false])
    (List.replicate w.length false ++ [true]) t (by simp) (by simp) _ i
  intro k
  by_cases hk : k < w.length
  · rw [List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ hk,
      List.getD_append _ _ _ _ (by simpa using hk), List.getD_replicate false hk]
    simp
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hk)]
    simp only [List.length_replicate]
    by_cases he : k - w.length = 0
    · simp [he]
    · obtain ⟨j, hj⟩ : ∃ j, k - w.length = j + 1 := ⟨k - w.length - 1, by omega⟩
      simp [hj]

lemma ofFn_LeL {n : ℕ} (x y : Fin n → Bool) (hxy : x ≤ y) :
    LeL (List.ofFn x) (List.ofFn y) := by
  intro i hx
  by_cases hi : i < n
  · have hle := hxy ⟨i, hi⟩
    have hx' : x ⟨i, hi⟩ = true := by
      simpa [List.getD_eq_getElem?_getD, hi] using hx
    have hy' : y ⟨i, hi⟩ = true := le_antisymm le_top (hx' ▸ hle)
    simpa [List.getD_eq_getElem?_getD, hi] using hy'
  · simp [List.getD_eq_getElem?_getD, hi] at hx

lemma fold_get_mono (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (i : ℕ) :
    Monotone (fun x : Fin n → Bool => (gs.foldl step (List.ofFn x)).getD i false) := by
  intro x y hxy
  change (gs.foldl step (List.ofFn x)).getD i false ≤ (gs.foldl step (List.ofFn y)).getD i false
  cases hx : (gs.foldl step (List.ofFn x)).getD i false with
  | false => exact Bool.false_le _
  | true =>
    have hy := fold_mono gs hgs (List.ofFn x) (List.ofFn y)
      (by simp) (ofFn_LeL x y hxy) i hx
    simp only [hy, le_refl]

lemma bool_and_mono {α : Type*} [Preorder α] (f g : α → Bool)
    (hf : Monotone f) (hg : Monotone g) : Monotone (fun x => f x && g x) := by
  intro x y hxy
  have h₁ := hf hxy
  have h₂ := hg hxy
  change (f x && g x) ≤ (f y && g y)
  cases hfx : f x <;> cases hfy : f y <;> cases hgx : g x <;> cases hgy : g y <;> simp_all

lemma or_replace_majorant_linear {α : Type*} (A : Finset α)
    (v q h : (α → Bool) → Bool)
    (hout : ∀ x, (v x || h x) = true ↔ ∃ a ∈ A, x a = true)
    (hvq : ∀ x, v x = true → q x = true)
    (hq : ∀ x, q x = true → ∃ a ∈ A, x a = true) :
    ∀ x, (v x || h x) = (q x || h x) := by
  intro x
  apply eq_of_true_iff
  constructor
  · intro hvh
    rw [Bool.or_eq_true_eq_eq_true_or_eq_true] at hvh ⊢
    exact hvh.elim (fun hv => Or.inl (hvq x hv)) Or.inr
  · intro hqh
    rw [Bool.or_eq_true_eq_eq_true_or_eq_true] at hqh
    rcases hqh with hqx | hhx
    · exact (hout x).mpr (hq x hqx)
    · simp only [hhx, Bool.or_true]

lemma last_and_overwrite_linear {β : Type*} (n : ℕ)
    (pre tail : List Gate) (a b : ℕ) (out : β → ℕ)
    (A : β → Finset (Fin n))
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (htail : ∀ g ∈ tail, g.op = GateOp.or)
    (ha : a < n + pre.length) (hb : b < n + pre.length)
    (hA : ∀ i j, i ≠ j → ∀ u ∈ A i, ∀ v ∈ A i, u ∈ A j → v ∈ A j → u = v)
    (hfun : ∀ k x, Circuit.eval ⟨pre ++ ⟨GateOp.and, [a, b]⟩ :: tail, out k⟩
      (List.ofFn x) = decide (∃ u ∈ A k, x u = true)) :
    ∃ g : Gate, g.op = GateOp.or ∧ g.inputs.length ≤ 1 ∧
      (∀ u ∈ g.inputs, u < n + pre.length) ∧
      ∀ k x, Circuit.eval ⟨pre ++ g :: tail, out k⟩ (List.ofFn x) =
        decide (∃ u ∈ A k, x u = true) := by
  classical
  let W (x : Fin n → Bool) := pre.foldl step (List.ofFn x)
  let v (x : Fin n → Bool) := (W x).getD a false && (W x).getD b false
  let H (k : β) (x : Fin n → Bool) := (tail.foldl step (W x ++ [false])).getD (out k) false
  let R (k : β) := (tail.foldl step (List.replicate (n + pre.length) false ++ [true])).getD
    (out k) false
  have Wlen (x : Fin n → Bool) : (W x).length = n + pre.length := by
    simp only [W, fold_length, List.length_ofFn]
  have Wa (u : Fin n) (x : Fin n → Bool) : (W x).getD u.val false = x u := by
    dsimp only [W]
    rw [fold_getD_lt _ _ _ (by simpa only [List.length_ofFn] using u.isLt)]
    simp [List.getD_eq_getElem?_getD]
  have hm (u : ℕ) : Monotone (fun x : Fin n → Bool => (W x).getD u false) :=
    fold_get_mono n pre hpre u
  have hv : Monotone v := bool_and_mono _ _ (hm a) (hm b)
  have hH (k : β) : Monotone (H k) := by
    have hm' := fold_get_mono n (pre ++ ⟨GateOp.or, []⟩ :: tail)
      (by
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hpre g hg
        · rcases List.mem_cons.mp hg with rfl | hg
          · exact Or.inr rfl
          · exact Or.inr (htail g hg)) (out k)
    simpa only [H, W, List.foldl_append, List.foldl_cons, step, GateOp.eval,
      List.map_nil, List.any_nil] using hm'
  have factor (k : β) (x : Fin n → Bool) (t : Bool) :
      (tail.foldl step (W x ++ [t])).getD (out k) false = (H k x || (R k && t)) := by
    simpa only [H, R, Wlen x] using suffix_or_factor tail htail (W x) t (out k)
  have original (k : β) (x : Fin n → Bool) :
      (tail.foldl step (W x ++ [v x])).getD (out k) false =
        decide (∃ u ∈ A k, x u = true) := by
    have h := hfun k x
    change ((pre ++ ⟨GateOp.and, [a, b]⟩ :: tail).foldl step (List.ofFn x)).getD (out k) false = _ at h
    rw [List.foldl_append, List.foldl_cons] at h
    change (tail.foldl step (W x ++
      [(W x).getD a false && ((W x).getD b false && true)])).getD (out k) false = _ at h
    simpa only [Bool.and_true] using h
  have linear (k : β) (hk : R k = true) (x : Fin n → Bool) :
      (v x || H k x) = true ↔ ∃ u ∈ A k, x u = true := by
    have h := (factor k x (v x)).symm.trans (original k x)
    have h' : (v x || H k x) = decide (∃ u ∈ A k, x u = true) := by
      simpa only [hk, Bool.true_and, Bool.or_comm] using h
    rw [h', decide_eq_true_eq]
  have finish (g : Gate) (hop : g.op = GateOp.or) (hlen : g.inputs.length ≤ 1)
      (hbound : ∀ u ∈ g.inputs, u < n + pre.length) (q : (Fin n → Bool) → Bool)
      (hval : ∀ x, g.op.eval (g.inputs.map fun u => (W x).getD u false) = q x)
      (heq : ∀ k x, (H k x || (R k && q x)) = (H k x || (R k && v x))) :
      ∃ g : Gate, g.op = GateOp.or ∧ g.inputs.length ≤ 1 ∧
        (∀ u ∈ g.inputs, u < n + pre.length) ∧
        ∀ k x, Circuit.eval ⟨pre ++ g :: tail, out k⟩ (List.ofFn x) =
          decide (∃ u ∈ A k, x u = true) := by
    refine ⟨g, hop, hlen, hbound, ?_⟩
    intro k x
    change ((pre ++ g :: tail).foldl step (List.ofFn x)).getD (out k) false = _
    rw [List.foldl_append, List.foldl_cons]
    change (tail.foldl step (W x ++
      [g.op.eval (g.inputs.map fun u => (W x).getD u false)])).getD (out k) false = _
    rw [hval, factor, heq, ← factor]
    exact original k x
  by_cases htwo : ∃ i j, R i = true ∧ R j = true ∧ i ≠ j
  · obtain ⟨i, j, hi, hj, hij⟩ := htwo
    obtain hzero | ⟨u, _, hone⟩ := shared_linear_replace
      (fun k : {k : β // R k = true} => A k.val) v
      (fun k : {k : β // R k = true} => H k.val) hv (fun k => hH k.val)
      (fun k => linear k.val k.property) ⟨i, hi⟩ ⟨j, hj⟩ (hA i j hij)
    · apply finish ⟨GateOp.or, []⟩ rfl (by decide) (by simp) (fun _ => false) (by simp [GateOp.eval])
      intro k x
      by_cases hk : R k = true
      · simpa only [hk, Bool.true_and, Bool.or_false, Bool.false_or, Bool.or_comm] using (hzero ⟨k, hk⟩ x).symm
      · have hk' : R k = false := Bool.eq_false_of_not_eq_true hk
        simp only [hk', Bool.false_and]
    · apply finish ⟨GateOp.or, [u.val]⟩ rfl (by simp)
        (by simpa only [List.mem_singleton, forall_eq] using Nat.lt_add_right pre.length u.isLt)
        (fun x => x u) (by intro x; change ((W x).getD u.val false || false) = x u; rw [Wa, Bool.or_false])
      intro k x
      by_cases hk : R k = true
      · simpa only [hk, Bool.true_and, Bool.or_comm] using (hone ⟨k, hk⟩ x).symm
      · have hk' : R k = false := Bool.eq_false_of_not_eq_true hk
        simp only [hk', Bool.false_and]
  · by_cases hsome : ∃ i, R i = true
    · obtain ⟨i, hi⟩ := hsome
      have only (k : β) (hk : R k = true) : k = i := by
        by_contra hki
        exact htwo ⟨k, i, hk, hi, hki⟩
      have hbelow : ∀ x, ((W x).getD a false && (W x).getD b false) = true →
          ∃ u ∈ A i, x u = true := by
        intro x hx
        apply (linear i hi x).mp
        simp only [v, hx, Bool.true_or]
      obtain hleft | hright := and_below_linear (A i)
        (fun x => (W x).getD a false) (fun x => (W x).getD b false) (hm a) (hm b) hbelow
      · have heq := or_replace_majorant_linear (A i) v
          (fun x => (W x).getD a false) (H i) (linear i hi)
          (by intro x hx; exact (show (W x).getD a false = true ∧ (W x).getD b false = true by
            simpa only [v, Bool.and_eq_true_eq_eq_true_and_eq_true] using hx).1) hleft
        apply finish ⟨GateOp.or, [a]⟩ rfl (by simp) (by simpa using ha)
          (fun x => (W x).getD a false) (by simp [GateOp.eval])
        intro k x
        by_cases hk : R k = true
        · have hki := only k hk
          subst k
          simpa only [hi, Bool.true_and, Bool.or_comm] using (heq x).symm
        · have hk' : R k = false := Bool.eq_false_of_not_eq_true hk
          simp only [hk', Bool.false_and]
      · have heq := or_replace_majorant_linear (A i) v
          (fun x => (W x).getD b false) (H i) (linear i hi)
          (by intro x hx; exact (show (W x).getD a false = true ∧ (W x).getD b false = true by
            simpa only [v, Bool.and_eq_true_eq_eq_true_and_eq_true] using hx).2) hright
        apply finish ⟨GateOp.or, [b]⟩ rfl (by simp) (by simpa using hb)
          (fun x => (W x).getD b false) (by simp [GateOp.eval])
        intro k x
        by_cases hk : R k = true
        · have hki := only k hk
          subst k
          simpa only [hi, Bool.true_and, Bool.or_comm] using (heq x).symm
        · have hk' : R k = false := Bool.eq_false_of_not_eq_true hk
          simp only [hk', Bool.false_and]
    · apply finish ⟨GateOp.or, []⟩ rfl (by decide) (by simp) (fun _ => false) (by simp [GateOp.eval])
      intro k x
      have hk : R k = false := Bool.eq_false_of_not_eq_true (fun hk => hsome ⟨k, hk⟩)
      simp only [hk, Bool.false_and]

end PEqualNP.Outside.L_meta_2685.CircuitNorm
