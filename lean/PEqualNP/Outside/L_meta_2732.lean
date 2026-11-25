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

lemma commonFilter_center {α : Type} (R : α → α → Prop)
    (A B S : α → Prop)
    (symm : ∀ u v, R u v → R v u)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) → R u v)
    (i : α) (hiA : A i) (hiB : B i) (p : α) (hp : S p)
    (cross : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → S u → v ≠ i → R p v) :
    ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) →
      u = i ∨ v = i ∨ u = p ∨ v = p := by
  have common : ∀ s, S s → R s i := fun s hs =>
    symm i s (safe i s (Or.inl hiA) (Or.inl hiB) (Or.inr hs))
  have same : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → S u → v ≠ i → u = p := by
    intro u v ha hb hu hv
    apply Classical.byContradiction
    intro hup
    exact free u p i v hup (fun h => hv h.symm)
      ⟨common u hu, safe u v ha hb (Or.inl hu), common p hp,
        cross u v ha hb hu hv⟩
  intro u v ha hb hs
  cases hs with
  | inl hu =>
      by_cases hv : v = i
      · exact Or.inr (Or.inl hv)
      · exact Or.inr (Or.inr (Or.inl (same u v ha hb hu hv)))
  | inr hv =>
      by_cases hu : u = i
      · exact Or.inl hu
      · exact Or.inr (Or.inr (Or.inr
          (same v u (ha.elim Or.inr Or.inl) (hb.elim Or.inr Or.inl) hv hu)))

lemma commonFilter_twoStars {α : Type} (R : α → α → Prop)
    (A B S : α → Prop)
    (symm : ∀ u v, R u v → R v u)
    (triangle : ∀ u v w, R u v → R v w → ¬ R u w)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) → R u v)
    (i : α) (hiA : A i) (hiB : B i) :
    ∃ p, ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) →
      u = i ∨ v = i ∨ u = p ∨ v = p := by
  have common : ∀ s, S s → R i s := fun s hs =>
    safe i s (Or.inl hiA) (Or.inl hiB) (Or.inr hs)
  by_cases hA : ∃ p, A p ∧ S p
  · obtain ⟨p, hpA, hpS⟩ := hA
    refine ⟨p, commonFilter_center R A B S symm free safe i hiA hiB p hpS ?_⟩
    intro u v _ hb hu _
    have hnu : ¬ B u := by
      intro hbu
      exact triangle i p u (common p hpS)
        (safe p u (Or.inl hpA) (Or.inr hbu) (Or.inl hpS)) (common u hu)
    exact safe p v (Or.inl hpA) (Or.inr (hb.resolve_left hnu)) (Or.inl hpS)
  · by_cases hB : ∃ p, B p ∧ S p
    · obtain ⟨p, hpB, hpS⟩ := hB
      refine ⟨p, commonFilter_center R A B S symm free safe i hiA hiB p hpS ?_⟩
      intro u v ha _ hu _
      have hnu : ¬ A u := fun hau => hA ⟨u, hau, hu⟩
      exact safe p v (Or.inr (ha.resolve_left hnu)) (Or.inl hpB) (Or.inl hpS)
    · by_cases hS : ∃ p, S p
      · obtain ⟨p, hpS⟩ := hS
        refine ⟨p, commonFilter_center R A B S symm free safe i hiA hiB p hpS ?_⟩
        intro u v ha hb hu _
        have hna : ¬ A u := fun hau => hA ⟨u, hau, hu⟩
        have hnb : ¬ B u := fun hbu => hB ⟨u, hbu, hu⟩
        exact safe p v (Or.inr (ha.resolve_left hna))
          (Or.inr (hb.resolve_left hnb)) (Or.inl hpS)
      · refine ⟨i, ?_⟩
        intro u v _ _ hs
        exact hs.elim (fun hu => False.elim (hS ⟨u, hu⟩))
          (fun hv => False.elim (hS ⟨v, hv⟩))

lemma safeFilter_coverTwo {α : Type} (R : α → α → Prop)
    (A B S : α → Prop) (z : α)
    (symm : ∀ u v, R u v → R v u)
    (triangle : ∀ u v w, R u v → R v w → ¬ R u w)
    (free : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (safe : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) → R u v) :
    ∃ p q, ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) →
      u = p ∨ v = p ∨ u = q ∨ v = q := by
  by_cases hA : ∃ a, A a
  · obtain ⟨a₀, ha₀⟩ := hA
    by_cases hB : ∃ b, B b
    · obtain ⟨b₀, hb₀⟩ := hB
      by_cases hI : ∃ i, A i ∧ B i
      · obtain ⟨i, hiA, hiB⟩ := hI
        obtain ⟨p, hp⟩ := commonFilter_twoStars R A B S symm triangle free safe i hiA hiB
        exact ⟨i, p, hp⟩
      · by_cases hA₂ : ∃ a₁, A a₁ ∧ a₁ ≠ a₀
        · obtain ⟨a₁, ha₁, hna⟩ := hA₂
          by_cases hB₂ : ∃ b₁, B b₁ ∧ b₁ ≠ b₀
          · obtain ⟨b₁, hb₁, hnb⟩ := hB₂
            have cross : ∀ a b, A a → B b → (S a ∨ S b) → R a b := by
              intro a b ha hb hs
              exact safe a b (Or.inl ha) (Or.inr hb) hs
            obtain ⟨p, q, _, _, hpq⟩ := safeFilter_doubleStar R A B S S free cross
              a₀ a₁ ha₀ ha₁ (fun h => hna h.symm)
              b₀ b₁ hb₀ hb₁ (fun h => hnb h.symm)
            refine ⟨p, q, ?_⟩
            intro u v ha hb hs
            cases ha with
            | inl hau =>
                cases hb with
                | inl hbu => exact False.elim (hI ⟨u, hau, hbu⟩)
                | inr hbv =>
                    exact (hpq u v hau hbv hs).elim Or.inl
                      (fun h => Or.inr (Or.inr (Or.inr h)))
            | inr hav =>
                cases hb with
                | inl hbu =>
                    exact (hpq v u hav hbu (hs.elim Or.inr Or.inl)).elim
                      (fun h => Or.inr (Or.inl h))
                      (fun h => Or.inr (Or.inr (Or.inl h)))
                | inr hbv => exact False.elim (hI ⟨v, hav, hbv⟩)
          · have unique : ∀ b, B b → b = b₀ := by
              intro b hb
              apply Classical.byContradiction
              intro h
              exact hB₂ ⟨b, hb, h⟩
            exact ⟨b₀, z, fun u v _ hb _ => hb.elim
              (fun h => Or.inl (unique u h))
              (fun h => Or.inr (Or.inl (unique v h)))⟩
        · have unique : ∀ a, A a → a = a₀ := by
            intro a ha
            apply Classical.byContradiction
            intro h
            exact hA₂ ⟨a, ha, h⟩
          exact ⟨a₀, z, fun u v ha _ _ => ha.elim
            (fun h => Or.inl (unique u h))
            (fun h => Or.inr (Or.inl (unique v h)))⟩
    · exact ⟨z, z, fun u v _ hb _ => hb.elim
        (fun h => False.elim (hB ⟨u, h⟩)) (fun h => False.elim (hB ⟨v, h⟩))⟩
  · exact ⟨z, z, fun u v ha _ _ => ha.elim
      (fun h => False.elim (hA ⟨u, h⟩)) (fun h => False.elim (hA ⟨v, h⟩))⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def heawoodEdges : List (ℕ × ℕ) :=
  [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
   (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
   (6, 8), (6, 9), (6, 11)]

def star27 : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [3, 14]⟩, ⟨GateOp.or, [4, 17]⟩,
    ⟨GateOp.or, [5, 16]⟩, ⟨GateOp.or, [5, 19]⟩, ⟨GateOp.or, [6, 15]⟩,
    ⟨GateOp.or, [6, 18]⟩, ⟨GateOp.or, [6, 20]⟩, ⟨GateOp.and, [7, 21]⟩,
    ⟨GateOp.and, [8, 25]⟩, ⟨GateOp.and, [9, 26]⟩, ⟨GateOp.and, [10, 23]⟩,
    ⟨GateOp.and, [11, 27]⟩, ⟨GateOp.and, [12, 24]⟩, ⟨GateOp.and, [13, 22]⟩,
    ⟨GateOp.or, [28, 29]⟩, ⟨GateOp.or, [30, 35]⟩, ⟨GateOp.or, [31, 36]⟩,
    ⟨GateOp.or, [32, 37]⟩, ⟨GateOp.or, [33, 38]⟩, ⟨GateOp.or, [34, 39]⟩], 40⟩

lemma star27_monotone : Monotone2 star27 := by
  simp [Monotone2, star27]

lemma star27_size : star27.size = 27 := rfl

def starFormula (x : Fin 14 → Bool) : Bool :=
  (x 13 && (x 4 || (x 1 || x 2))) ||
  ((x 12 && (x 5 || (x 2 || x 3))) ||
  ((x 11 && (x 6 || (x 3 || x 4))) ||
  ((x 10 && (x 5 || (x 0 || x 4))) ||
  ((x 9 && (x 6 || (x 1 || x 5))) ||
  ((x 7 && (x 3 || (x 0 || x 1))) || (x 8 && (x 6 || (x 0 || x 2))))))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
lemma star27_eval (x : Fin 14 → Bool) : star27.eval (List.ofFn x) = starFormula x := by
  simp [star27, starFormula, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
lemma star27_correct (x : Fin 14 → Bool) :
    star27.eval (List.ofFn x) = decide
      (∃ u v : Fin 14, (u.val, v.val) ∈ heawoodEdges ∧ x u = true ∧ x v = true) := by
  rw [star27_eval]
  apply Bool.eq_iff_iff.mpr
  simp only [starFormula, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  simp [heawoodEdges, Fin.exists_fin_succ]
  simp only [and_or_left]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  generalize x 8 = b8
  generalize x 9 = b9
  generalize x 10 = b10
  generalize x 11 = b11
  generalize x 12 = b12
  generalize x 13 = b13
  simp only [and_comm, or_assoc, or_comm, or_left_comm]

end PEqualNP.Outside.L_meta_2732_aux
