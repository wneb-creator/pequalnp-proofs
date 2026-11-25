import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux

lemma safeRows_unique {α β : Type} (R : α → β → Prop)
    (A : α → Prop) (B : β → Prop) (S : α → Prop) (T : β → Prop)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ a b, A a → B b → (S a ∨ T b) → R a b)
    (b b' : β) (hb : B b) (hb' : B b') (hne : b ≠ b')
    (a a' : α) (ha : A a) (ha' : A a') (hs : S a) (hs' : S a') :
    a = a' := by
  apply Classical.byContradiction
  intro haa
  exact free a a' b b' haa hne
    ⟨safe a b ha hb (Or.inl hs), safe a b' ha hb' (Or.inl hs),
      safe a' b ha' hb (Or.inl hs'), safe a' b' ha' hb' (Or.inl hs')⟩

lemma safeColumns_unique {α β : Type} (R : α → β → Prop)
    (A : α → Prop) (B : β → Prop) (S : α → Prop) (T : β → Prop)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ a b, A a → B b → (S a ∨ T b) → R a b)
    (a a' : α) (ha : A a) (ha' : A a') (hne : a ≠ a')
    (b b' : β) (hb : B b) (hb' : B b') (ht : T b) (ht' : T b') :
    b = b' := by
  apply Classical.byContradiction
  intro hbb
  exact free a a' b b' hne hbb
    ⟨safe a b ha hb (Or.inr ht), safe a b' ha hb' (Or.inr ht'),
      safe a' b ha' hb (Or.inr ht), safe a' b' ha' hb' (Or.inr ht')⟩

lemma safeFilter_doubleStar {α β : Type} (R : α → β → Prop)
    (A : α → Prop) (B : β → Prop) (S : α → Prop) (T : β → Prop)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ a b, A a → B b → (S a ∨ T b) → R a b)
    (a₀ a₁ : α) (ha₀ : A a₀) (ha₁ : A a₁) (ha : a₀ ≠ a₁)
    (b₀ b₁ : β) (hb₀ : B b₀) (hb₁ : B b₁) (hb : b₀ ≠ b₁) :
    ∃ p q, A p ∧ B q ∧
      ∀ a b, A a → B b → (S a ∨ T b) → a = p ∨ b = q := by
  have row : ∃ p, A p ∧ ∀ a, A a → S a → a = p := by
    by_cases h : ∃ p, A p ∧ S p
    · obtain ⟨p, hp, hs⟩ := h
      exact ⟨p, hp, fun a ha hs' =>
        safeRows_unique R A B S T free safe b₀ b₁ hb₀ hb₁ hb a p ha hp hs' hs⟩
    · exact ⟨a₀, ha₀, fun a ha hs => False.elim (h ⟨a, ha, hs⟩)⟩
  have col : ∃ q, B q ∧ ∀ b, B b → T b → b = q := by
    by_cases h : ∃ q, B q ∧ T q
    · obtain ⟨q, hq, ht⟩ := h
      exact ⟨q, hq, fun b hb ht' =>
        safeColumns_unique R A B S T free safe a₀ a₁ ha₀ ha₁ ha b q hb hq ht' ht⟩
    · exact ⟨b₀, hb₀, fun b hb ht => False.elim (h ⟨b, hb, ht⟩)⟩
  obtain ⟨p, hp, hrow⟩ := row
  obtain ⟨q, hq, hcol⟩ := col
  exact ⟨p, q, hp, hq, fun a b ha hb h =>
    h.elim (fun hs => Or.inl (hrow a ha hs)) (fun ht => Or.inr (hcol b hb ht))⟩

namespace Rename

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wire {n : ℕ} (f : Fin n → Fin n) (i : ℕ) : ℕ :=
  if hi : i < n then (f ⟨i, hi⟩).val else i

def gate {n : ℕ} (f : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire f)⟩

def circuit {n : ℕ} (f : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gate f), wire f C.output⟩

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wire_eq_above {n : ℕ} (f : Fin n → Fin n) (i m : ℕ) (hm : n ≤ m) :
    wire f i = m ↔ i = m := by
  by_cases hi : i < n
  · have hf := (f ⟨i, hi⟩).isLt
    simp only [wire, dif_pos hi]
    omega
  · simp only [wire, dif_neg hi]

lemma wire_input {n : ℕ} (f : Fin n → Fin n) (i : Fin n) :
    wire f i.val = (f i).val := by
  simp [wire, i.isLt]

lemma wire_past {n : ℕ} (f : Fin n → Fin n) (i : ℕ) (hi : n ≤ i) :
    wire f i = i := by
  simp [wire, Nat.not_lt_of_ge hi]

lemma wire_lt {n m : ℕ} (f : Fin n → Fin n) (i : ℕ) (hn : n ≤ m) (hi : i < m) :
    wire f i < m := by
  by_cases h : i < n
  · rw [wire, dif_pos h]
    exact lt_of_lt_of_le (f ⟨i, h⟩).isLt hn
  · simpa [wire, h] using hi

lemma wire_injective {n : ℕ} (f : Fin n → Fin n) (hf : Function.Injective f) :
    Function.Injective (wire f) := by
  intro i j hij
  by_cases hi : i < n <;> by_cases hj : j < n
  · have h : f ⟨i, hi⟩ = f ⟨j, hj⟩ := by
      apply Fin.ext
      simpa [wire, hi, hj] using hij
    exact congrArg Fin.val (hf h)
  · have h := (f ⟨i, hi⟩).isLt
    simp only [wire, dif_pos hi, dif_neg hj] at hij
    omega
  · have h := (f ⟨j, hj⟩).isLt
    simp only [wire, dif_neg hi, dif_pos hj] at hij
    omega
  · simpa [wire, hi, hj] using hij

lemma append_get (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  rcases Nat.lt_trichotomy i w.length with h | h | h
  · rw [List.getD_append _ _ _ _ h, if_neg (by omega)]
  · subst i
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega), if_neg (by omega),
      List.getD_eq_default _ _ (by omega)]

lemma initial {n : ℕ} (f : Fin n → Fin n) (x : Fin n → Bool) (s : List Bool) (i : ℕ) :
    (List.ofFn x ++ s).getD (wire f i) false =
      (List.ofFn (x ∘ f) ++ s).getD i false := by
  by_cases hi : i < n
  · simp only [wire, dif_pos hi]
    rw [List.getD_append _ _ _ _ (by simpa using (f ⟨i, hi⟩).isLt),
      List.getD_append _ _ _ _ (by simpa using hi)]
    rw [List.getD_eq_getElem _ _ (by simpa using (f ⟨i, hi⟩).isLt),
      List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn, Function.comp_apply]
  · simp only [wire, dif_neg hi]
    rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi)]
    simp only [List.length_ofFn]

lemma fold {n : ℕ} (f : Fin n → Fin n) (gs : List Gate) :
    ∀ old new : List Bool, n ≤ old.length → new.length = old.length →
      (∀ i, new.getD (wire f i) false = old.getD i false) →
      ∀ i, (run (gs.map (gate f)) new).getD (wire f i) false =
        (run gs old).getD i false := by
  induction gs with
  | nil => intro old new hn hl hr; exact hr
  | cons g gs ih =>
    intro old new hn hl hr
    let b := g.op.eval (g.inputs.map fun i => old.getD i false)
    have hb : (gate f g).op.eval ((gate f g).inputs.map fun i => new.getD i false) = b := by
      simp only [gate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hr i
    have step : ∀ i, (new ++ [b]).getD (wire f i) false = (old ++ [b]).getD i false := by
      intro i
      rw [append_get, append_get, hl]
      simp only [wire_eq_above f i old.length hn, hr i]
    have hh := ih (old ++ [b]) (new ++ [b]) (by simp; omega) (by simp [hl]) step
    simpa only [run, List.map_cons, List.foldl_cons, hb] using hh

lemma eval {n : ℕ} (f : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) (s : List Bool) :
    (circuit f C).eval (List.ofFn x ++ s) = C.eval (List.ofFn (x ∘ f) ++ s) := by
  exact fold f C.gates (List.ofFn (x ∘ f) ++ s) (List.ofFn x ++ s)
    (by simp) (by simp) (initial f x s) C.output

lemma size {n : ℕ} (f : Fin n → Fin n) (C : Circuit) : (circuit f C).size = C.size := by
  simp [circuit, Circuit.size]

lemma monotone {n : ℕ} (f : Fin n → Fin n) {C : Circuit} (h : Monotone2 C) :
    Monotone2 (circuit f C) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  obtain ⟨ho, hi⟩ := h a ha
  exact ⟨ho, by simpa [gate] using hi⟩

end Rename

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def prefixScore (a b c d : ℕ) : ℕ :=
  (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

def prefixRename (σ : Equiv.Perm (Fin 14)) (i : Fin 15) : ℕ :=
  if i.val < 14 then (σ (Fin.ofNat 14 i.val)).val else 14

def prefixWitness (F : (Fin 14 → Bool) → Bool)
    (a b : Fin 14) (c d : Fin 15) (op₁ op₂ : GateOp) (D : Circuit) : Prop :=
  a < b ∧ c < d ∧
  (op₁ = GateOp.and ∨ op₁ = GateOp.or) ∧
  (op₂ = GateOp.and ∨ op₂ = GateOp.or) ∧
  Monotone2 D ∧ D.size ≤ 24 ∧
  ∀ x : Fin 14 → Bool,
    let w := List.ofFn x ++ [op₁.eval [x a, x b]]
    D.eval (w ++ [op₂.eval [w.getD c.val false, w.getD d.val false]]) = F x

lemma minimum_prefix (F : (Fin 14 → Bool) → Bool)
    (h : ∃ a b c d op₁ op₂ D, prefixWitness F a b c d op₁ op₂ D) :
    ∃ a b c d op₁ op₂ D, prefixWitness F a b c d op₁ op₂ D ∧
      ∀ a' b' c' d' op₁' op₂' D', prefixWitness F a' b' c' d' op₁' op₂' D' →
        prefixScore a.val b.val c.val d.val ≤ prefixScore a'.val b'.val c'.val d'.val := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ a b c d op₁ op₂ D, prefixWitness F a b c d op₁ op₂ D ∧
      prefixScore a.val b.val c.val d.val = n
  have hex : ∃ n, P n := by
    obtain ⟨a, b, c, d, op₁, op₂, D, hD⟩ := h
    exact ⟨_, a, b, c, d, op₁, op₂, D, hD, rfl⟩
  obtain ⟨a, b, c, d, op₁, op₂, D, hD, hs⟩ := Nat.find_spec hex
  refine ⟨a, b, c, d, op₁, op₂, D, hD, ?_⟩
  intro a' b' c' d' op₁' op₂' D' hD'
  rw [hs]
  exact Nat.find_min' hex ⟨a', b', c', d', op₁', op₂', D', hD', rfl⟩

lemma canonical_prefix (F : (Fin 14 → Bool) → Bool)
    (h : ∃ a b c d op₁ op₂ D, prefixWitness F a b c d op₁ op₂ D)
    (transport : ∀ a b c d op₁ op₂ D,
      prefixWitness F a b c d op₁ op₂ D →
      ∀ σ : Equiv.Perm (Fin 14), (∀ x, F (x ∘ σ) = F x) →
        ∃ a' b' c' d' op₁' op₂' D', prefixWitness F a' b' c' d' op₁' op₂' D' ∧
          prefixScore a'.val b'.val c'.val d'.val =
            prefixScore (σ a).val (σ b).val (prefixRename σ c) (prefixRename σ d)) :
    ∃ a b c d op₁ op₂ D,
      a < b ∧ c < d ∧
      (op₁ = GateOp.and ∨ op₁ = GateOp.or) ∧
      (op₂ = GateOp.and ∨ op₂ = GateOp.or) ∧
      (∀ σ : Equiv.Perm (Fin 14), (∀ x, F (x ∘ σ) = F x) →
        prefixScore a.val b.val c.val d.val ≤
          prefixScore (σ a).val (σ b).val (prefixRename σ c) (prefixRename σ d)) ∧
      Monotone2 D ∧ D.size ≤ 24 ∧
      ∀ x : Fin 14 → Bool,
        let w := List.ofFn x ++ [op₁.eval [x a, x b]]
        D.eval (w ++ [op₂.eval [w.getD c.val false, w.getD d.val false]]) = F x := by
  obtain ⟨a, b, c, d, op₁, op₂, D, hD, hmin⟩ := minimum_prefix F h
  obtain ⟨hab, hcd, ho₁, ho₂, hm, hs, he⟩ := hD
  refine ⟨a, b, c, d, op₁, op₂, D, hab, hcd, ho₁, ho₂, ?_, hm, hs, he⟩
  intro σ hσ
  obtain ⟨a', b', c', d', op₁', op₂', D', hD', hs'⟩ :=
    transport a b c d op₁ op₂ D ⟨hab, hcd, ho₁, ho₂, hm, hs, he⟩ σ hσ
  rw [← hs']
  exact hmin a' b' c' d' op₁' op₂' D' hD'

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def prefixIndex (σ : Equiv.Perm (Fin 14)) (i : Fin 15) : Fin 15 :=
  ⟨Rename.wire σ i.val, Rename.wire_lt σ i.val (by decide) i.isLt⟩

lemma prefixIndex_injective (σ : Equiv.Perm (Fin 14)) :
    Function.Injective (prefixIndex σ) := by
  intro i j h
  apply Fin.ext
  exact Rename.wire_injective σ σ.injective (congrArg Fin.val h)

lemma prefixIndex_val (σ : Equiv.Perm (Fin 14)) (i : Fin 15) :
    (prefixIndex σ i).val = prefixRename σ i := by
  unfold prefixIndex prefixRename Rename.wire
  by_cases h : i.val < 14
  · simp only [dif_pos h, if_pos h]
    congr 1
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt h]
  · have hi : i.val = 14 := by omega
    simp [h, hi]

lemma op_comm (op : GateOp) (h : op = GateOp.and ∨ op = GateOp.or) (a b : Bool) :
    op.eval [a, b] = op.eval [b, a] := by
  rcases h with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

lemma op_min_max {n : ℕ} (op : GateOp) (h : op = GateOp.and ∨ op = GateOp.or)
    (x : Fin n → Bool) (a b : Fin n) :
    op.eval [x (min a b), x (max a b)] = op.eval [x a, x b] := by
  by_cases hab : a ≤ b
  · simp [min_eq_left hab, max_eq_right hab]
  · simp only [min_eq_right (le_of_not_ge hab), max_eq_left (le_of_not_ge hab)]
    exact op_comm op h _ _

lemma score_sorted (a b : Fin 14) (c d : Fin 15) :
    prefixScore (min a b).val (max a b).val (min c d).val (max c d).val =
      prefixScore a.val b.val c.val d.val := by
  simp [prefixScore, Fin.val_min, Fin.val_max]

lemma transport_prefix (F : (Fin 14 → Bool) → Bool)
    (a b : Fin 14) (c d : Fin 15) (op₁ op₂ : GateOp) (D : Circuit)
    (hD : prefixWitness F a b c d op₁ op₂ D)
    (σ : Equiv.Perm (Fin 14)) (hσ : ∀ x, F (x ∘ σ) = F x) :
    ∃ a' b' c' d' op₁' op₂' D', prefixWitness F a' b' c' d' op₁' op₂' D' ∧
      prefixScore a'.val b'.val c'.val d'.val =
        prefixScore (σ a).val (σ b).val (prefixRename σ c) (prefixRename σ d) := by
  obtain ⟨hab, hcd, ho₁, ho₂, hm, hs, he⟩ := hD
  let ca := σ a
  let cb := σ b
  let cc := prefixIndex σ c
  let cd := prefixIndex σ d
  have hab' : ca ≠ cb := fun h => ne_of_lt hab (σ.injective h)
  have hcd' : cc ≠ cd := fun h => ne_of_lt hcd (prefixIndex_injective σ h)
  refine ⟨min ca cb, max ca cb, min cc cd, max cc cd, op₁, op₂, Rename.circuit σ D, ?_, ?_⟩
  · refine ⟨min_lt_max.mpr hab', min_lt_max.mpr hcd', ho₁, ho₂,
      Rename.monotone σ hm, ?_, ?_⟩
    · simpa only [Rename.size] using hs
    · intro x
      simp only [op_min_max op₁ ho₁]
      let u := op₁.eval [x ca, x cb]
      let w := List.ofFn x ++ [u]
      let v := List.ofFn (x ∘ σ) ++ [u]
      have hget (i : Fin 15) : w.getD (prefixIndex σ i).val false = v.getD i.val false :=
        Rename.initial σ x [u] i.val
      have hsecond : op₂.eval [w.getD (min cc cd).val false, w.getD (max cc cd).val false] =
          op₂.eval [v.getD c.val false, v.getD d.val false] := by
        rw [op_min_max op₂ ho₂ (fun i : Fin 15 => w.getD i.val false)]
        rw [hget c, hget d]
      change (Rename.circuit σ D).eval
        (w ++ [op₂.eval [w.getD (min cc cd).val false, w.getD (max cc cd).val false]]) = F x
      rw [hsecond]
      have hEval := Rename.eval σ D x [u, op₂.eval [v.getD c.val false, v.getD d.val false]]
      have hOriginal := he (x ∘ σ)
      change D.eval (v ++ [op₂.eval [v.getD c.val false, v.getD d.val false]]) = F (x ∘ σ) at hOriginal
      simpa only [w, v, List.append_assoc, List.cons_append, List.nil_append] using
        hEval.trans (hOriginal.trans (hσ x))
  · rw [score_sorted]
    simp only [cc, cd, ca, cb, prefixIndex_val]

end PEqualNP.Outside.L_meta_2732_aux
