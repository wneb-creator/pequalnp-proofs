import PEqualNP.Defs

-- The counting argument below reuses willakone’s checked proof of L-meta-2059 (PR 4283).
-- The final theorem translates the Singer plane predicates and the zero nested-AND count.

namespace PEqualNP.Outside.L_meta_5158

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

def Cl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (i : Fin gates.length) (X : Finset (Fin n)) : Prop :=
  (gates.get i).op = GateOp.or → val gates (n + (i : ℕ)) c = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ M, ∀ y' ∈ M,
      (val gates a (τ y) = true ∨ val gates b (τ y) = true) →
      (val gates a (τ y') = true ∨ val gates b (τ y') = true) → (y ∈ X ↔ y' ∈ X)

def Con {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (k : ℕ) (X : Finset (Fin n)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < k → Cl gates M c τ i X

def Mrg {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
      val gates w1 (τ r) = true ∧ val gates w2 (τ r') = true ∧
      ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X

theorem single {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    ∀ w, w < n + k → val gates w c = false → ∀ y ∈ M, ∀ y' ∈ M,
      val gates w (τ y) = true → val gates w (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwc y hy y' hy' h1 h2
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h1 h2
      have e1 := hτ y hy _ h1
      have e2 := hτ y' hy' _ h2
      rw [← e1, ← e2]
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      rw [← he] at hwc h1 h2
      have hinp : ∀ a ∈ gates[w - n].inputs, a < n + (w - n) :=
        hin ⟨w - n, hi⟩
      have hlen := (legal gates[w - n] (List.getElem_mem hi)).2
      rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
      · have hex : ∃ j ∈ gates[w - n].inputs, val gates j c = false := by
          by_contra hne
          have hall : val gates (n + (w - n)) c = true := by
            apply (val_and gates c (w - n) hi ha).2
            intro j hj
            refine ⟨hinp j hj, ?_⟩
            cases hv : val gates j c with
            | true => rfl
            | false => exact absurd ⟨j, hj, hv⟩ hne
          rw [hall] at hwc
          exact Bool.noConfusion hwc
        obtain ⟨j, hj, hjc⟩ := hex
        have hjlt := hinp j hj
        exact ih j (by omega) (by omega) hjc y hy y' hy'
          ((val_and gates (τ y) (w - n) hi ha).1 h1 j hj).2
          ((val_and gates (τ y') (w - n) hi ha).1 h2 j hj).2
      · have hall : ∀ j ∈ gates[w - n].inputs, val gates j c = false := by
          intro j hj
          cases hv : val gates j c with
          | false => rfl
          | true =>
            have ht : val gates (n + (w - n)) c = true :=
              (val_or gates c (w - n) hi ho).2 ⟨j, hj, hinp j hj, hv⟩
            rw [ht] at hwc
            exact Bool.noConfusion hwc
        obtain ⟨j1, hj1, _, hv1⟩ := (val_or gates (τ y) (w - n) hi ho).1 h1
        obtain ⟨j2, hj2, _, hv2⟩ := (val_or gates (τ y') (w - n) hi ho).1 h2
        rcases hinpe : gates[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · rw [hinpe] at hj1
          simp at hj1
        · rw [hinpe] at hj1 hj2
          have e1 : j1 = a := by simpa using hj1
          have e2 : j2 = a := by simpa using hj2
          rw [e1] at hv1
          rw [e2] at hv2
          have hjlt := hinp a (by rw [hinpe]; simp)
          exact ih a (by omega) (by omega) (hall a (by rw [hinpe]; simp)) y hy y' hy' hv1 hv2
        · rw [hinpe] at hj1 hj2
          have d1 : val gates a (τ y) = true ∨ val gates b (τ y) = true := by
            rcases List.mem_pair.1 hj1 with e | e
            · subst e; exact Or.inl hv1
            · subst e; exact Or.inr hv1
          have d2 : val gates a (τ y') = true ∨ val gates b (τ y') = true := by
            rcases List.mem_pair.1 hj2 with e | e
            · subst e; exact Or.inl hv2
            · subst e; exact Or.inr hv2
          exact hX ⟨w - n, hi⟩ (by simp; omega) ho hwc a b hinpe y hy y' hy' d1 d2
        · rw [hinpe] at hlen
          simp at hlen

theorem con_succ {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (hk : k < gates.length) (X : Finset (Fin n)) :
    Con gates M c τ (k + 1) X ↔ Con gates M c τ k X ∧ Cl gates M c τ ⟨k, hk⟩ X := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases e : (i : ℕ) = k
    · have e' : i = ⟨k, hk⟩ := Fin.ext e
      rw [e']
      exact h2
    · exact h1 i (by omega)

theorem con_compl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (h : Con gates M c τ k X) :
    Con gates M c τ k Xᶜ := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_compl, Finset.mem_compl, not_iff_not]
  exact h i hi ho hc' a b hab y hy y' hy' h1 h2

theorem con_symm {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : Con gates M c τ k X)
    (hY : Con gates M c τ k Y) : Con gates M c τ k (symmDiff X Y) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  have e2 := hY i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_symmDiff, Finset.mem_symmDiff, e1, e2]

theorem con_inter {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    Con gates M c τ k (X ∩ M) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_inter, Finset.mem_inter, e1]
  exact ⟨fun h => ⟨h.1, hy'⟩, fun h => ⟨h.1, hy⟩⟩

theorem cl_of {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (g : Fin gates.length) (X : Finset (Fin n)) (a b : ℕ)
    (hab : (gates.get g).inputs = [a, b])
    (sA : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates a (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (sB : ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (Q : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X)) : Cl gates M c τ g X := by
  intro _ _ a' b' hab' y hy y' hy' h1 h2
  rw [hab] at hab'
  obtain ⟨e1, e2⟩ : a = a' ∧ b = b' := by simpa using hab'
  subst e1
  subst e2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact sA y hy y' hy' h1 h2
  · exact Q y hy y' hy' h1 h2
  · exact (Q y' hy' y hy h2 h1).symm
  · exact sB y hy y' hy' h1 h2

theorem symm_flip {n : ℕ} (X Y : Finset (Fin n)) (r r' : Fin n) (hr : r ∈ Y) (hr' : r' ∉ Y) :
    (r ∈ symmDiff X Y ↔ r' ∈ symmDiff X Y) ↔ ¬ (r ∈ X ↔ r' ∈ X) := by
  by_cases h1 : r ∈ X <;> by_cases h2 : r' ∈ X <;> simp [Finset.mem_symmDiff, h1, h2, hr, hr']

open Classical in
noncomputable def P {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) : Finset (Finset (Fin n)) :=
  M.powerset.filter (fun X => Con gates M c τ k X)

open Classical in
theorem symm_mem {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : X ∈ P gates M c τ k)
    (hY : Y ⊆ M) (hYc : Con gates M c τ k Y) : symmDiff X Y ∈ P gates M c τ k := by
  rw [P, Finset.mem_filter, Finset.mem_powerset] at hX ⊢
  refine ⟨?_, con_symm gates M c τ k X Y hX.2 hYc⟩
  intro v hv
  rw [Finset.mem_symmDiff] at hv
  rcases hv with hv | hv
  · exact hX.1 hv.1
  · exact hY hv.1

open Classical in
theorem step {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (g : Fin gates.length) :
    (P gates M c τ ((g : ℕ) + 1)).card * (if Mrg gates M c τ g then 2 else 1)
      = (P gates M c τ (g : ℕ)).card := by
  by_cases hal : (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
      ∃ a b : ℕ, (gates.get g).inputs = [a, b]
  swap
  · have hnm : ¬ Mrg gates M c τ g := by
      rintro ⟨h1, h2, w1, w2, h3, _⟩
      exact hal ⟨h1, h2, w1, w2, h3⟩
    have hP : P gates M c τ ((g : ℕ) + 1) = P gates M c τ (g : ℕ) := by
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro ho hc' a b hab
        exact absurd ⟨ho, hc', a, b, hab⟩ hal
    rw [hP, if_neg hnm, Nat.mul_one]
  · obtain ⟨ho, hgc, a, b, hab⟩ := hal
    have hma : a ∈ (gates.get g).inputs := by rw [hab]; simp
    have hmb : b ∈ (gates.get g).inputs := by rw [hab]; simp
    have ha : a < n + (g : ℕ) := hin g a hma
    have hb : b < n + (g : ℕ) := hin g b hmb
    have hac : val gates a c = false := by
      cases hv : val gates a c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨a, hma, ha, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have hbc : val gates b c = false := by
      cases hv : val gates b c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨b, hmb, hb, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have sA : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true →
        val gates a (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX a ha hac
    have sB : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true →
        val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX b hb hbc
    by_cases hm : ∃ r ∈ M, ∃ r' ∈ M, val gates a (τ r) = true ∧ val gates b (τ r') = true ∧
        ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X
    · have hmrg : Mrg gates M c τ g := ⟨ho, hgc, a, b, hab, hm⟩
      obtain ⟨r, hr, r', hr', hra, hrb, X0, hrX, hr'X, hX0⟩ := hm
      rw [if_pos hmrg]
      have hP : P gates M c τ ((g : ℕ) + 1)
          = (P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X) := by
        unfold P
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro X _
        rw [con_succ gates M c τ g g.2 X]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2 ho hgc a b hab r hr r' hr' (Or.inl hra) (Or.inr hrb)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, cl_of gates M c τ g X a b hab (sA X h1) (sB X h1) ?_⟩
          intro y hy y' hy' hya hyb
          exact ((sA X h1 y hy r hr hya hra).trans h2).trans (sB X h1 r' hr' y' hy' hrb hyb)
      rw [hP]
      have hsplit := Finset.card_filter_add_card_filter_not (s := P gates M c τ (g : ℕ))
        (fun X => r ∈ X ↔ r' ∈ X)
      have hY0 : X0 ∩ M ⊆ M := Finset.inter_subset_right
      have hY0c := con_inter gates M c τ g X0 hX0
      have hrY : r ∈ X0 ∩ M := Finset.mem_inter.2 ⟨hrX, hr⟩
      have hr'Y : r' ∉ X0 ∩ M := fun h => hr'X (Finset.mem_inter.1 h).1
      have hbij : ((P gates M c τ (g : ℕ)).filter (fun X => ¬ (r ∈ X ↔ r' ∈ X))).card
          = ((P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X)).card := by
        refine Finset.card_bij' (fun X _ => symmDiff X (X0 ∩ M)) (fun X _ => symmDiff X (X0 ∩ M))
          ?_ ?_ ?_ ?_
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).2 hX.2
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          intro hcon
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).1 hcon hX.2
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
      omega
    · have hnm : ¬ Mrg gates M c τ g := by
        rintro ⟨_, _, w1, w2, h3, r, hr, r', hr', h4, h5, h6⟩
        rw [hab] at h3
        obtain ⟨e1, e2⟩ : a = w1 ∧ b = w2 := by simpa using h3
        subst e1
        subst e2
        exact hm ⟨r, hr, r', hr', h4, h5, h6⟩
      rw [if_neg hnm, Nat.mul_one]
      congr 1
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, cl_of gates M c τ g X a b hab (sA X h) (sB X h) ?_⟩
        intro y hy y' hy' hya hyb
        constructor
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, X, hyX, hn, h⟩
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, Xᶜ, Finset.mem_compl.2 hn,
            fun h' => Finset.mem_compl.1 h' hyX, con_compl gates M c τ g X h⟩

open Classical in
theorem count {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) :
    (P gates M c τ k).card *
      2 ^ (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
      = 2 ^ M.card := by
  induction k with
  | zero =>
    have h0 : P gates M c τ 0 = M.powerset := by
      unfold P
      apply Finset.filter_true_of_mem
      intro X _ i hi
      exact absurd hi (Nat.not_lt_zero _)
    rw [h0, Finset.card_powerset]
    simp
  | succ k ih =>
    have hk' : k < gates.length := hk
    have hs : (P gates M c τ (k + 1)).card * (if Mrg gates M c τ ⟨k, hk'⟩ then 2 else 1)
        = (P gates M c τ k).card := step gates M c τ hτ legal hin ⟨k, hk'⟩
    have hsum : (∑ g : Fin gates.length, if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
        = (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
          + (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) := by
      have hpt : ∀ g : Fin gates.length,
          (if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
          = (if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
            + (if g = ⟨k, hk'⟩ then (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) else 0) := by
        intro g
        by_cases e : g = ⟨k, hk'⟩
        · subst e
          simp
        · have hne : (g : ℕ) ≠ k := fun h => e (Fin.ext h)
          have h2 : ((g : ℕ) < k + 1) ↔ ((g : ℕ) < k) := by omega
          simp [e, h2]
      rw [Finset.sum_congr rfl (fun g _ => hpt g), Finset.sum_add_distrib]
      simp
    rw [hsum, pow_add, ← ih (le_of_lt hk'), ← hs]
    split_ifs <;> ring


open Classical in
theorem mcount {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : 1 ≤ M.card) (o : ℕ) (hoc : val gates o c = false)
    (hot : ∀ p ∈ M, val gates o (τ p) = true) :
    (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = M.card - 1 := by
  have hne : M.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p0, hp0⟩ := hne
  have holt : o < n + gates.length := by
    by_contra h
    have hb := val_big gates (τ p0) o (by omega)
    rw [hot p0 hp0] at hb
    exact Bool.noConfusion hb
  have hfin : P gates M c τ gates.length = {∅, M} := by
    ext X
    rw [P, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hX⟩
      have hs := single gates M c τ hτ legal hin gates.length le_rfl X hX o holt hoc
      by_cases hex : ∃ y ∈ M, y ∈ X
      · obtain ⟨y, hy, hyX⟩ := hex
        right
        apply Finset.Subset.antisymm hsub
        intro z hz
        exact (hs y hy z hz (hot y hy) (hot z hz)).1 hyX
      · left
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        exact hex ⟨z, hsub hz, hz⟩
    · rintro (e | e)
      · subst e
        refine ⟨Finset.empty_subset _, ?_⟩
        intro i _ _ _ a b _ y _ y' _ _ _
        simp
      · subst e
        refine ⟨Finset.Subset.refl _, ?_⟩
        intro i _ _ _ a b _ y hy y' hy' _ _
        exact ⟨fun _ => hy', fun _ => hy⟩
  have hcnt := count gates M c τ hτ legal hin gates.length le_rfl
  have hpair : ({∅, M} : Finset (Finset (Fin n))).card = 2 := by
    apply Finset.card_pair
    intro h
    rw [← h] at hp0
    simp at hp0
  rw [hfin, hpair] at hcnt
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ Mrg gates M c τ g then 1 else 0)
      = ∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have hm1 : 2 ^ M.card = 2 * 2 ^ (M.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h8 : 2 ^ (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = 2 ^ (M.card - 1) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcnt.trans hm1)
  exact Nat.pow_right_injective (le_refl 2) h8

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

theorem disj {n : ℕ} (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (L1 L2 A1 A2 : Finset (Fin n)) (hA : A1 ⊆ L1) (hcard : (L1 ∩ L2).card ≤ 1)
    (g : Fin gates.length)
    (h1 : Mrg gates A1 (fun v => decide (v ∉ L1)) (fun y v => decide (v = y)) g)
    (h2 : Mrg gates A2 (fun v => decide (v ∉ L2)) (fun y v => decide (v = y)) g) : False := by
  obtain ⟨ho, _, w1, w2, hab, r, hr, r', hr', hv1, hv2, X, hrX, hr'X, _⟩ := h1
  obtain ⟨_, hc2, _⟩ := h2
  have hne : r ≠ r' := fun e => hr'X (e ▸ hrX)
  have hm1 : w1 ∈ (gates.get g).inputs := by rw [hab]; simp
  have hm2 : w2 ∈ (gates.get g).inputs := by rw [hab]; simp
  have ht1 : val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = r)) = true :=
    (val_or gates _ g g.2 ho).2 ⟨w1, hm1, hin g w1 hm1, hv1⟩
  have ht2 : val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = r')) = true :=
    (val_or gates _ g g.2 ho).2 ⟨w2, hm2, hin g w2 hm2, hv2⟩
  have key : ∀ s : Fin n, val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = s)) = true →
      s ∈ L2 := by
    intro s hs
    by_contra hns
    have hmo := val_mono gates legal (fun v : Fin n => decide (v = s))
      (fun v : Fin n => decide (v ∉ L2)) (by
        intro v hv
        have e : v = s := of_decide_eq_true hv
        rw [e]
        exact decide_eq_true hns) _ hs
    rw [hc2] at hmo
    exact Bool.noConfusion hmo
  have hr2 := key r ht1
  have hr2' := key r' ht2
  have hsub : ({r, r'} : Finset (Fin n)) ⊆ L1 ∩ L2 := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with e | e
    · rw [e]; exact Finset.mem_inter.2 ⟨hA hr, hr2⟩
    · rw [e]; exact Finset.mem_inter.2 ⟨hA hr', hr2'⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hc
  omega

def MJ {n m : ℕ} (gates : List Gate) (L A : Fin m → Finset (Fin n)) (j : Fin m)
    (g : Fin gates.length) : Prop :=
  Mrg gates (A j) (fun v => decide (v ∉ L j)) (fun y v => decide (v = y)) g

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h


def adjb (s t : Fin 26) : Bool :=
  decide (s.val < 13 ∧ 13 ≤ t.val ∧ (s.val + 26 - t.val) % 13 ∈ [0, 1, 3, 9]) ||
  decide (t.val < 13 ∧ 13 ≤ s.val ∧ (t.val + 26 - s.val) % 13 ∈ [0, 1, 3, 9])

def mk (f g : Fin 13 → Bool) (u : Fin 26) : Bool :=
  if h : u.val < 13 then f ⟨u.val, h⟩ else g ⟨u.val - 13, by omega⟩

theorem mk_eq (f g : Fin 13 → Bool) : List.ofFn f ++ List.ofFn g = List.ofFn (mk f g) := by
  have hl : (List.ofFn f).length = 13 := List.length_ofFn
  apply List.ext_getElem
  · rw [List.length_append, List.length_ofFn, List.length_ofFn, List.length_ofFn]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    by_cases h : i < 13
    · rw [List.getElem_append_left (by rw [hl]; exact h), List.getElem_ofFn]
      unfold mk
      rw [dif_pos h]
    · rw [List.getElem_append_right (by rw [hl]; omega), List.getElem_ofFn]
      unfold mk
      rw [dif_neg h]
      congr 2

def pr (s t : Fin 26) : Fin 26 → Bool := fun u => decide (u = s ∨ u = t)

def N (v : Fin 26) : Finset (Fin 26) := Finset.univ.filter (fun y => adjb v y = true)

theorem mem_N (v y : Fin 26) : y ∈ N v ↔ adjb v y = true := by
  simp [N]

def qin (Q : Finset (Fin 13)) : Fin 26 → Bool :=
  mk (fun u => decide (u ∈ Q)) (fun v => decide (∀ r ∈ Q, r - v ∉ ({0, 1, 3, 9} : Finset (Fin 13))))

def ein (p l : Fin 13) : Fin 26 → Bool :=
  mk (fun x => decide (x = p)) (fun x => decide (x = l))

def Pp (s t : Fin 26) : Fin 13 := ⟨(min s.val t.val) % 13, Nat.mod_lt _ (by norm_num)⟩

def Ll (s t : Fin 26) : Fin 13 := ⟨(max s.val t.val - 13) % 13, Nat.mod_lt _ (by norm_num)⟩

def tab : List (List ℕ) := [[0, 1, 2, 5], [0, 1, 2, 5], [0, 1, 2, 5], [0, 2, 3, 4], [0, 1, 4, 6], [0, 1, 2, 5], [0, 1, 2, 6], [0, 1, 2, 7], [0, 1, 4, 8], [0, 2, 4, 9], [0, 1, 5, 10], [0, 1, 2, 11], [0, 1, 4, 12], [], [0, 3, 5, 6], [0, 1, 4, 6], [0, 1, 2, 5], [], [0, 2, 3, 4], [0, 1, 4, 8], [0, 1, 2, 5], [0, 1, 2, 5], [0, 1, 2, 6], [], [0, 2, 3, 4], [], [], [], [2, 4, 5, 6], [], [2, 4, 5, 6], [2, 4, 5, 6], [2, 4, 5, 6], [2, 4, 7, 8], [2, 4, 5, 8], [], [2, 5, 6, 10], [2, 4, 6, 11], [2, 4, 5, 12], [2, 4, 5, 6], [5, 6, 7, 11], [4, 6, 7, 8], [2, 5, 7, 8], [2, 6, 8, 10], [2, 4, 7, 11], [4, 5, 8, 10], [2, 4, 5, 6], [2, 5, 6, 10], [2, 4, 6, 8], [2, 4, 5, 8], [2, 4, 5, 6], [4, 5, 6, 10]]

def sh (s : Fin 26) : ℕ := if s.val < 13 then s.val else s.val - 13

def tidx (s t : Fin 26) : ℕ :=
  (if s.val < 13 then 0 else 26) +
    (if t.val < 13 then (t.val + 13 - sh s) % 13 else 13 + (t.val - 13 + 13 - sh s) % 13)

def Wt (s t : Fin 26) : Finset (Fin 13) :=
  ((tab.getD (tidx s t) []).map
    (fun a => (⟨(a + sh s) % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13))).toFinset

theorem adj_irr : ∀ s : Fin 26, adjb s s = false := by decide +kernel

theorem adj_symm : ∀ s t : Fin 26, adjb s t = adjb t s := by decide +kernel

theorem hLN : ∀ i j : Fin 26, i ≠ j → (N i ∩ N j).card ≤ 1 := by decide +kernel

theorem degN : ∀ v : Fin 26, (N v).card = 4 := by decide +kernel

theorem adj_total :
    ∑ v : Fin 26, ∑ y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) = 104 := by
  decide +kernel

theorem accwit : ∀ s t : Fin 26, adjb s t = true →
    (Pp s t - Ll s t ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ∧
      ∀ u : Fin 26, ein (Pp s t) (Ll s t) u = true → (u = s ∨ u = t) := by
  decide +kernel

theorem wit : ∀ s t : Fin 26, adjb s t = false →
    (Wt s t).card = 4 ∧
    (∀ l : Fin 13, ({x ∈ Wt s t | x - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))}).card ≤ 2) ∧
    qin (Wt s t) s = true ∧ qin (Wt s t) t = true := by
  decide +kernel

theorem k22 (s1 s2 t1 t2 : Fin 26) (h11 : adjb s1 t1 = true) (h12 : adjb s1 t2 = true)
    (h21 : adjb s2 t1 = true) (h22 : adjb s2 t2 = true) (hne : s1 ≠ s2) : t1 = t2 := by
  have hc := hLN s1 s2 hne
  rw [Finset.card_le_one] at hc
  exact hc t1 (Finset.mem_inter.2 ⟨(mem_N _ _).2 h11, (mem_N _ _).2 h21⟩) t2
    (Finset.mem_inter.2 ⟨(mem_N _ _).2 h12, (mem_N _ _).2 h22⟩)

theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem hin_of (C : Circuit) (n : ℕ) (hrb : ReadsBack n C) :
    ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < n + (i : ℕ) := by
  intro i a ha
  apply hrb i i.2 a
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ i.2]
  exact ha

def Lin (gs : List Gate) (w : ℕ) : Prop :=
  ∀ x : Fin 26 → Bool, val gs w x = true →
    ∃ u : Fin 26, x u = true ∧ val gs w (fun v => decide (v = u)) = true

open PEqualNP.EdgeOwnership in
theorem lin_ind (C : Circuit)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < 26 + (i : ℕ)) :
    ∀ w, (26 ≤ w → w - 26 < C.gates.length → (gateAt C (w - 26)).op = GateOp.or ∧
      ∀ i, InCone 26 C i (w - 26) → (gateAt C i).op ≠ GateOp.and) → Lin C.gates w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw x hx
    by_cases hwn : w < 26
    · refine ⟨⟨w, hwn⟩, ?_, ?_⟩
      · rw [val_input C.gates _ w hwn] at hx
        exact hx
      · rw [val_input C.gates _ w hwn]
        simp
    · by_cases hbig : 26 + C.gates.length ≤ w
      · rw [val_big C.gates x w hbig] at hx
        exact Bool.noConfusion hx
      · have hi : w - 26 < C.gates.length := by omega
        have he : 26 + (w - 26) = w := by omega
        obtain ⟨hor, hcone⟩ := hw (by omega) hi
        rw [gateAt_eq C _ hi] at hor
        have hx' : val C.gates (26 + (w - 26)) x = true := by rw [he]; exact hx
        obtain ⟨a, ha, halt, hav⟩ := (val_or C.gates x (w - 26) hi hor).1 hx'
        have hga : a ∈ (gateAt C (w - 26)).inputs := by rw [gateAt_eq C _ hi]; exact ha
        have hla : Lin C.gates a := by
          apply ih a (by omega)
          intro ha26 hai
          have hic : InCone 26 C (a - 26) (w - 26) :=
            (inCone_iff 26 C (a - 26) (w - 26) hi).2 ⟨a, hga, ha26, halt, Or.inl rfl⟩
          have hna := hcone _ hic
          refine ⟨?_, ?_⟩
          · rw [gateAt_eq C _ hai] at hna ⊢
            rcases (legal _ (List.getElem_mem hai)).1 with h | h
            · exact absurd h hna
            · exact h
          · intro i hi2
            exact hcone i ((inCone_iff 26 C i (w - 26) hi).2 ⟨a, hga, ha26, halt, Or.inr hi2⟩)
        obtain ⟨u, hu, huv⟩ := hla x hav
        refine ⟨u, hu, ?_⟩
        rw [← he]
        exact (val_or C.gates _ (w - 26) hi hor).2 ⟨a, ha, halt, huv⟩

open PEqualNP.EdgeOwnership in
theorem lin_and (C : Circuit)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < 26 + (i : ℕ))
    (hflat : ¬ ∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 26 C i j)
    (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and) (a : ℕ)
    (ha : a ∈ C.gates[j].inputs) : Lin C.gates a := by
  have halt : a < 26 + j := hin ⟨j, hj⟩ a ha
  have hgj : (gateAt C j).op = GateOp.and := by rw [gateAt_eq C j hj]; exact hop
  have hga : a ∈ (gateAt C j).inputs := by rw [gateAt_eq C j hj]; exact ha
  apply lin_ind C legal hin a
  intro ha26 hai
  have hic : InCone 26 C (a - 26) j :=
    (inCone_iff 26 C (a - 26) j hj).2 ⟨a, hga, ha26, halt, Or.inl rfl⟩
  refine ⟨?_, ?_⟩
  · rcases (legal _ (List.getElem_mem hai)).1 with h | h
    · exact absurd ⟨a - 26, j, by rw [gateAt_eq C _ hai]; exact h, hgj, hic⟩ hflat
    · rw [gateAt_eq C _ hai]; exact h
  · intro i hi2 hand
    exact hflat ⟨i, j, hand, hgj,
      (inCone_iff 26 C i j hj).2 ⟨a, hga, ha26, halt, Or.inr hi2⟩⟩

def Reach (gs : List Gate) (o : ℕ) (w : ℕ) : Prop :=
  ∀ S : ℕ → Prop, S o →
    (∀ (k : ℕ) (hk : k < gs.length), gs[k].op = GateOp.or → S (26 + k) →
      ∀ a ∈ gs[k].inputs, S a) → S w

theorem reach_out (gs : List Gate) (o : ℕ) : Reach gs o o := fun _ h _ => h

theorem reach_step (gs : List Gate) (o : ℕ) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) (hr : Reach gs o (26 + k)) (a : ℕ) (ha : a ∈ gs[k].inputs) :
    Reach gs o a :=
  fun S h0 hs => hs k hk hop (hr S h0 hs) a ha

theorem reach_imp (gs : List Gate) (o : ℕ)
    (hin : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < 26 + (i : ℕ))
    (w : ℕ) (hr : Reach gs o w) :
    ∀ x : Fin 26 → Bool, val gs w x = true → val gs o x = true := by
  apply hr (fun w => ∀ x : Fin 26 → Bool, val gs w x = true → val gs o x = true)
  · intro x h
    exact h
  · intro k hk hop hS a ha x hx
    exact hS x ((val_or gs x k hk hop).2 ⟨a, ha, hin ⟨k, hk⟩ a ha, hx⟩)

theorem reach_down (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin 26 → Bool) :
    ∀ w, Reach gs o w → val gs w x = true →
      ∃ w', Reach gs o w' ∧ val gs w' x = true ∧
        (w' < 26 ∨ ∃ (j : ℕ) (hj : j < gs.length), w' = 26 + j ∧ gs[j].op = GateOp.and) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hr hx
    by_cases hwn : w < 26
    · exact ⟨w, hr, hx, Or.inl hwn⟩
    · by_cases hbig : 26 + gs.length ≤ w
      · rw [val_big gs x w hbig] at hx
        exact Bool.noConfusion hx
      · have hi : w - 26 < gs.length := by omega
        have he : 26 + (w - 26) = w := by omega
        rcases (legal gs[w - 26] (List.getElem_mem hi)).1 with ha | ho
        · exact ⟨w, hr, hx, Or.inr ⟨w - 26, hi, he.symm, ha⟩⟩
        · have hx' : val gs (26 + (w - 26)) x = true := by rw [he]; exact hx
          have hr' : Reach gs o (26 + (w - 26)) := by rw [he]; exact hr
          obtain ⟨a, ha, halt, hav⟩ := (val_or gs x (w - 26) hi ho).1 hx'
          exact ih a (by omega) (reach_step gs o (w - 26) hi ho hr' a ha) hav

theorem reach_parent (gs : List Gate) (o : ℕ) (w : ℕ) (hr : Reach gs o w) :
    w = o ∨ ∃ (k : ℕ) (hk : k < gs.length), gs[k].op = GateOp.or ∧ Reach gs o (26 + k) ∧
      w ∈ gs[k].inputs := by
  apply hr (fun w => w = o ∨ ∃ (k : ℕ) (hk : k < gs.length), gs[k].op = GateOp.or ∧
    Reach gs o (26 + k) ∧ w ∈ gs[k].inputs)
  · exact Or.inl rfl
  · intro k hk hop hS a ha
    right
    refine ⟨k, hk, hop, ?_, ha⟩
    rcases hS with h | ⟨k', hk', hop', hr', hmem⟩
    · rw [h]
      exact reach_out gs o
    · exact reach_step gs o k' hk' hop' hr' _ hmem

open Classical in
theorem top_count (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (U RO : Finset (Fin gs.length))
    (hU : ∀ j ∈ U, (gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)))
    (hRO : ∀ j, j ∈ RO ↔ ((gs.get j).op = GateOp.or ∧ Reach gs o (26 + (j : ℕ)))) :
    U.card ≤ RO.card + 1 := by
  have hdisj : Disjoint U RO := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    have a1 := (hU j h1).1
    have a2 := ((hRO j).1 h2).1
    rw [a1] at a2
    exact GateOp.noConfusion a2
  have hsub : (U ∪ RO).image (fun j : Fin gs.length => 26 + (j : ℕ)) ⊆
      insert o (RO.biUnion (fun k => (gs.get k).inputs.toFinset)) := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
    have hr : Reach gs o (26 + (j : ℕ)) := by
      rcases Finset.mem_union.1 hj with h | h
      · exact (hU j h).2
      · exact ((hRO j).1 h).2
    rcases reach_parent gs o _ hr with h | ⟨k, hk, hop, hrk, hmem⟩
    · rw [h]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_biUnion]
      exact ⟨⟨k, hk⟩, (hRO ⟨k, hk⟩).2 ⟨hop, hrk⟩, List.mem_toFinset.2 hmem⟩
  have hinj : Function.Injective (fun j : Fin gs.length => 26 + (j : ℕ)) := by
    intro a b h
    apply Fin.ext
    simpa using h
  have hc1 : ((U ∪ RO).image (fun j : Fin gs.length => 26 + (j : ℕ))).card
      = U.card + RO.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_union_of_disjoint hdisj]
  have hc2 : (RO.biUnion (fun k => (gs.get k).inputs.toFinset)).card ≤ RO.card * 2 := by
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 2 ?_).trans (by simp)
    intro k _
    exact (List.toFinset_card_le _).trans (legal _ (List.getElem_mem k.2)).2
  have hc3 := Finset.card_le_card hsub
  have hc4 := Finset.card_insert_le o (RO.biUnion (fun k => (gs.get k).inputs.toFinset))
  omega

open Classical in
theorem mrg_count {n m : ℕ} (L A : Fin m → Finset (Fin n)) (gates : List Gate) (o : Fin m → ℕ)
    (hL : ∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hA : ∀ j : Fin m, A j ⊆ L j)
    (hot : ∀ (j : Fin m) (p : Fin n), p ∈ A j →
      val gates (o j) (fun i : Fin n => decide (i = p)) = true)
    (hoc : ∀ j : Fin m, 1 ≤ (A j).card →
      val gates (o j) (fun i : Fin n => decide (i ∉ L j)) = false) :
    ∑ j : Fin m, ((A j).card - 1) ≤
      (Finset.univ.filter (fun g : Fin gates.length => ∃ j, MJ gates L A j g)).card := by
  have h1 : ∀ j : Fin m, (A j).card - 1 ≤
      ∑ g : Fin gates.length, (if MJ gates L A j g then (1 : ℕ) else 0) := by
    intro j
    by_cases hc : 1 ≤ (A j).card
    · exact le_of_eq (mcount gates (A j) (fun v => decide (v ∉ L j)) (fun y v => decide (v = y))
        (fun p _ v hv => of_decide_eq_true hv) legal hin hc (o j) (hoc j hc)
        (fun p hp => hot j p hp)).symm
    · have hz : (A j).card - 1 = 0 := by omega
      rw [hz]
      exact Nat.zero_le _
  have h2 : ∀ g : Fin gates.length,
      (∑ j : Fin m, (if MJ gates L A j g then (1 : ℕ) else 0)) ≤
        (if ∃ j, MJ gates L A j g then (1 : ℕ) else 0) := by
    intro g
    by_cases hex : ∃ j0 : Fin m, MJ gates L A j0 g
    · rw [if_pos hex]
      obtain ⟨j0, hj0⟩ := hex
      have hle : ∀ j ∈ (Finset.univ : Finset (Fin m)),
          (if MJ gates L A j g then (1 : ℕ) else 0) ≤ (if j = j0 then (1 : ℕ) else 0) := by
        intro j _
        by_cases hj : MJ gates L A j g
        · have e : j = j0 := by
            by_contra hne
            exact disj gates legal hin (L j) (L j0) (A j) (A j0) (hA j) (hL j j0 hne) g hj hj0
          rw [if_pos hj, if_pos e]
        · rw [if_neg hj]
          exact Nat.zero_le _
      refine (Finset.sum_le_sum hle).trans ?_
      simp
    · have hz : ∀ j ∈ (Finset.univ : Finset (Fin m)),
          (if MJ gates L A j g then (1 : ℕ) else 0) = 0 :=
        fun j _ => if_neg (fun h => hex ⟨j, h⟩)
      rw [Finset.sum_eq_zero hz]
      exact Nat.zero_le _
  calc ∑ j : Fin m, ((A j).card - 1)
      ≤ ∑ j : Fin m, ∑ g : Fin gates.length, (if MJ gates L A j g then (1 : ℕ) else 0) :=
        Finset.sum_le_sum (fun j _ => h1 j)
    _ = ∑ g : Fin gates.length, ∑ j : Fin m, (if MJ gates L A j g then (1 : ℕ) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ g : Fin gates.length, (if ∃ j, MJ gates L A j g then (1 : ℕ) else 0) :=
        Finset.sum_le_sum (fun g _ => h2 g)
    _ = (Finset.univ.filter (fun g : Fin gates.length => ∃ j, MJ gates L A j g)).card := by
        rw [Finset.card_filter]

def Hy (gs : List Gate) (o : ℕ) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  (∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < 26 + (i : ℕ)) ∧
  (∀ (j : ℕ) (hj : j < gs.length), gs[j].op = GateOp.and → ∀ a ∈ gs[j].inputs, Lin gs a) ∧
  (∀ s t : Fin 26, adjb s t = true → val gs o (pr s t) = true) ∧
  (∀ s t : Fin 26, adjb s t = false → val gs o (pr s t) = false)

theorem reach_adj (gs : List Gate) (o : ℕ) (H : Hy gs o) (w : ℕ) (hr : Reach gs o w)
    (s t : Fin 26) (h : val gs w (pr s t) = true) : adjb s t = true := by
  have h2 := reach_imp gs o H.2.1 w hr _ h
  cases hb : adjb s t with
  | true => rfl
  | false =>
    rw [H.2.2.2.2 s t hb] at h2
    exact Bool.noConfusion h2

theorem val_e_pr (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (s t u : Fin 26) (hu : u = s ∨ u = t)
    (h : val gs w (fun v : Fin 26 => decide (v = u)) = true) : val gs w (pr s t) = true :=
  val_mono gs legal _ _ (by
    intro v hv
    have e : v = u := of_decide_eq_true hv
    rw [e]
    exact decide_eq_true hu) w h

theorem reach_single (gs : List Gate) (o : ℕ) (H : Hy gs o) (w : ℕ) (hr : Reach gs o w)
    (s : Fin 26) (h : val gs w (fun v : Fin 26 => decide (v = s)) = true) : False := by
  have h2 := reach_adj gs o H w hr s s (val_e_pr gs H.1 w s s s (Or.inl rfl) h)
  rw [adj_irr s] at h2
  exact Bool.noConfusion h2

theorem and_struct (gs : List Gate) (o : ℕ) (H : Hy gs o) (j : ℕ) (hj : j < gs.length)
    (hop : gs[j].op = GateOp.and) (hr : Reach gs o (26 + j)) (s0 t0 : Fin 26)
    (h0 : val gs (26 + j) (pr s0 t0) = true) : ∃ a b : ℕ, gs[j].inputs = [a, b] := by
  have hlen := (H.1 gs[j] (List.getElem_mem hj)).2
  have hall := (val_and gs (pr s0 t0) j hj hop).1 h0
  have hlinj := H.2.2.1 j hj hop
  rcases hinp : gs[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · exfalso
    apply reach_single gs o H _ hr s0
    apply (val_and gs _ j hj hop).2
    intro i hi
    rw [hinp] at hi
    simp at hi
  · exfalso
    have ha : a ∈ gs[j].inputs := by rw [hinp]; simp
    obtain ⟨halt, hav⟩ := hall a ha
    obtain ⟨u, hu, huv⟩ := hlinj a ha _ hav
    apply reach_single gs o H _ hr u
    apply (val_and gs _ j hj hop).2
    intro i hi
    rw [hinp] at hi
    have e : i = a := by simpa using hi
    rw [e]
    exact ⟨halt, huv⟩
  · exact ⟨a, b, rfl⟩
  · rw [hinp] at hlen
    simp at hlen

theorem star (gs : List Gate) (o : ℕ) (H : Hy gs o) (j : ℕ) (hj : j < gs.length)
    (hop : gs[j].op = GateOp.and) (hr : Reach gs o (26 + j)) (s0 t0 : Fin 26)
    (h0 : val gs (26 + j) (pr s0 t0) = true) :
    ∃ (z : Fin 26) (A : Finset (Fin 26)) (lw : ℕ), A ⊆ N z ∧
      (∀ p ∈ A, val gs lw (fun v : Fin 26 => decide (v = p)) = true) ∧
      val gs lw (fun v : Fin 26 => decide (v ∉ N z)) = false ∧
      ∀ s t : Fin 26, val gs (26 + j) (pr s t) = true → (s = z ∧ t ∈ A) ∨ (t = z ∧ s ∈ A) := by
  obtain ⟨a, b, hab⟩ := and_struct gs o H j hj hop hr s0 t0 h0
  have ha : a ∈ gs[j].inputs := by rw [hab]; simp
  have hb : b ∈ gs[j].inputs := by rw [hab]; simp
  have halt : a < 26 + j := H.2.1 ⟨j, hj⟩ a ha
  have hblt : b < 26 + j := H.2.1 ⟨j, hj⟩ b hb
  have la : Lin gs a := H.2.2.1 j hj hop a ha
  have lb : Lin gs b := H.2.2.1 j hj hop b hb
  have hST : ∀ s t : Fin 26, val gs a (fun v : Fin 26 => decide (v = s)) = true →
      val gs b (fun v : Fin 26 => decide (v = t)) = true → adjb s t = true := by
    intro s t hs ht
    apply reach_adj gs o H _ hr s t
    apply (val_and gs _ j hj hop).2
    intro i hi
    rw [hab] at hi
    rcases List.mem_pair.1 hi with e | e
    · rw [e]
      exact ⟨halt, val_e_pr gs H.1 a s t s (Or.inl rfl) hs⟩
    · rw [e]
      exact ⟨hblt, val_e_pr gs H.1 b s t t (Or.inr rfl) ht⟩
  have hcov : ∀ s t : Fin 26, val gs (26 + j) (pr s t) = true →
      (val gs a (fun v : Fin 26 => decide (v = s)) = true ∧
        val gs b (fun v : Fin 26 => decide (v = t)) = true) ∨
      (val gs a (fun v : Fin 26 => decide (v = t)) = true ∧
        val gs b (fun v : Fin 26 => decide (v = s)) = true) := by
    intro s t h
    have hall := (val_and gs (pr s t) j hj hop).1 h
    obtain ⟨u1, hu1, hv1⟩ := la _ (hall a ha).2
    obtain ⟨u2, hu2, hv2⟩ := lb _ (hall b hb).2
    have hadj := hST u1 u2 hv1 hv2
    have e1 : u1 = s ∨ u1 = t := of_decide_eq_true hu1
    have e2 : u2 = s ∨ u2 = t := of_decide_eq_true hu2
    have hne : u1 ≠ u2 := by
      intro e
      rw [e, adj_irr] at hadj
      exact Bool.noConfusion hadj
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
    · exact absurd (e1.trans e2.symm) hne
    · left
      rw [← e1, ← e2]
      exact ⟨hv1, hv2⟩
    · right
      rw [← e1, ← e2]
      exact ⟨hv1, hv2⟩
    · exact absurd (e1.trans e2.symm) hne
  have hne : ∃ sa tb : Fin 26, val gs a (fun v : Fin 26 => decide (v = sa)) = true ∧
      val gs b (fun v : Fin 26 => decide (v = tb)) = true := by
    rcases hcov s0 t0 h0 with h | h
    · exact ⟨s0, t0, h⟩
    · exact ⟨t0, s0, h⟩
  obtain ⟨sa, tb, hsa, htb⟩ := hne
  by_cases hT : ∀ t : Fin 26, val gs b (fun v : Fin 26 => decide (v = t)) = true → t = tb
  · refine ⟨tb, Finset.univ.filter
      (fun s : Fin 26 => val gs a (fun v : Fin 26 => decide (v = s)) = true), a, ?_, ?_, ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_filter] at hs
      rw [mem_N, adj_symm]
      exact hST s tb hs.2 htb
    · intro p hp
      exact (Finset.mem_filter.1 hp).2
    · cases hv : val gs a (fun v : Fin 26 => decide (v ∉ N tb)) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨u, hu, huv⟩ := la _ hv
        have hu' : u ∉ N tb := of_decide_eq_true hu
        apply hu'
        rw [mem_N, adj_symm]
        exact hST u tb huv htb
    · intro s t h
      rcases hcov s t h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right
        exact ⟨hT t h2, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩⟩
      · left
        exact ⟨hT s h2, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩⟩
  · push_neg at hT
    obtain ⟨t1, ht1, hne1⟩ := hT
    have hS : ∀ s : Fin 26, val gs a (fun v : Fin 26 => decide (v = s)) = true → s = sa := by
      intro s hs
      by_contra hne2
      exact hne1 (k22 s sa t1 tb (hST s t1 hs ht1) (hST s tb hs htb) (hST sa t1 hsa ht1)
        (hST sa tb hsa htb) hne2)
    refine ⟨sa, Finset.univ.filter
      (fun t : Fin 26 => val gs b (fun v : Fin 26 => decide (v = t)) = true), b, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [Finset.mem_filter] at ht
      rw [mem_N]
      exact hST sa t hsa ht.2
    · intro p hp
      exact (Finset.mem_filter.1 hp).2
    · cases hv : val gs b (fun v : Fin 26 => decide (v ∉ N sa)) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨u, hu, huv⟩ := lb _ hv
        have hu' : u ∉ N sa := of_decide_eq_true hu
        apply hu'
        rw [mem_N]
        exact hST sa u hsa huv
    · intro s t h
      rcases hcov s t h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        exact ⟨hS s h1, Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩⟩
      · right
        exact ⟨hS t h1, Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩⟩

open Classical in
noncomputable def US (gs : List Gate) (o : ℕ) : Finset (Fin gs.length) :=
  Finset.univ.filter (fun j => (gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)) ∧
    ∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true)

open Classical in
noncomputable def ROS (gs : List Gate) (o : ℕ) : Finset (Fin gs.length) :=
  Finset.univ.filter (fun j => (gs.get j).op = GateOp.or ∧ Reach gs o (26 + (j : ℕ)))

open Classical in
noncomputable def MGS (gs : List Gate) (A' : Fin 26 → Finset (Fin 26)) :
    Finset (Fin gs.length) :=
  Finset.univ.filter (fun g : Fin gs.length => ∃ j, MJ gs N A' j g)

open Classical in
theorem mem_US (gs : List Gate) (o : ℕ) (j : Fin gs.length) :
    j ∈ US gs o ↔ ((gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)) ∧
      ∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true) := by
  unfold US
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open Classical in
theorem mem_ROS (gs : List Gate) (o : ℕ) (j : Fin gs.length) :
    j ∈ ROS gs o ↔ ((gs.get j).op = GateOp.or ∧ Reach gs o (26 + (j : ℕ))) := by
  unfold ROS
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem cover (gs : List Gate) (o : ℕ) (H : Hy gs o) (v y : Fin 26) (hadj : adjb v y = true) :
    ∃ j : Fin gs.length, j ∈ US gs o ∧ val gs (26 + (j : ℕ)) (pr v y) = true := by
  have hout := H.2.2.2.1 v y hadj
  obtain ⟨w, hr, hx, hw⟩ := reach_down gs o H.1 (pr v y) o (reach_out gs o) hout
  rcases hw with hw | ⟨j, hj, e, hop⟩
  · exfalso
    apply reach_single gs o H w hr ⟨w, hw⟩
    rw [val_input gs _ w hw]
    simp
  · rw [e] at hr hx
    exact ⟨⟨j, hj⟩, (mem_US gs o _).2 ⟨hop, hr, v, y, hx⟩, hx⟩

theorem arith (b c m : ℕ) (h4 : b ≤ 4) (hm : b ≤ c * m) :
    5 * b ≤ 4 * (2 * c + (m - 1)) := by
  rcases c with _ | _ | _ | c
  · simp at hm
    omega
  · simp at hm
    omega
  · omega
  · clear hm
    omega

theorem tally {ι : Type} (U : Finset ι) (z : ι → Fin 26) (A : ι → Finset (Fin 26))
    (A' : Fin 26 → Finset (Fin 26))
    (h1 : ∀ j ∈ U, A j ⊆ N (z j)) (h2 : ∀ j ∈ U, (A j).card ≤ (A' (z j)).card)
    (h3 : ∀ v y : Fin 26, adjb v y = true →
      ∃ j ∈ U, (v = z j ∧ y ∈ A j) ∨ (y = z j ∧ v ∈ A j)) :
    260 ≤ 8 * U.card + 4 * ∑ v : Fin 26, ((A' v).card - 1) := by
  obtain ⟨B, hB⟩ : ∃ B : Fin 26 → Finset (Fin 26),
      ∀ v, B v = (U.filter (fun j => z j = v)).biUnion A := ⟨_, fun _ => rfl⟩
  have hB4 : ∀ v, (B v).card ≤ 4 := by
    intro v
    rw [← degN v, hB v]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.1 hy
    rw [Finset.mem_filter] at hj
    rw [← hj.2]
    exact h1 j hj.1 hyj
  have hBm : ∀ v, (B v).card ≤ (U.filter (fun j => z j = v)).card * (A' v).card := by
    intro v
    rw [hB v]
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_card_nsmul _ _ ((A' v).card) ?_).trans (by simp)
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [← hj.2]
    exact h2 j hj.1
  have hv : ∀ v, 5 * (B v).card ≤
      4 * (2 * (U.filter (fun j => z j = v)).card + ((A' v).card - 1)) :=
    fun v => arith _ _ _ (hB4 v) (hBm v)
  have hpt : ∀ v y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) ≤
      (if y ∈ B v then (1 : ℕ) else 0) + (if v ∈ B y then (1 : ℕ) else 0) := by
    intro v y
    by_cases hadj : adjb v y = true
    · obtain ⟨j, hj, h | h⟩ := h3 v y hadj
      · have hm : y ∈ B v := by
          rw [hB v]
          exact Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨hj, h.1.symm⟩, h.2⟩
        rw [if_pos hadj, if_pos hm]
        omega
      · have hm : v ∈ B y := by
          rw [hB y]
          exact Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨hj, h.1.symm⟩, h.2⟩
        rw [if_pos hadj, if_pos hm]
        omega
    · rw [if_neg hadj]
      exact Nat.zero_le _
  have hsumB : ∀ v : Fin 26, ∑ y : Fin 26, (if y ∈ B v then (1 : ℕ) else 0) = (B v).card := by
    intro v
    simp
  have hsumB' : ∑ v : Fin 26, ∑ y : Fin 26, (if v ∈ B y then (1 : ℕ) else 0)
      = ∑ y : Fin 26, (B y).card := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun y _ => hsumB y)
  have h104 : 104 ≤ 2 * ∑ v : Fin 26, (B v).card := by
    calc 104 = ∑ v : Fin 26, ∑ y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) :=
          adj_total.symm
      _ ≤ ∑ v : Fin 26, ∑ y : Fin 26,
            ((if y ∈ B v then (1 : ℕ) else 0) + (if v ∈ B y then (1 : ℕ) else 0)) :=
          Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun y _ => hpt v y))
      _ = (∑ v : Fin 26, (B v).card) + ∑ y : Fin 26, (B y).card := by
          simp only [Finset.sum_add_distrib]
          rw [hsumB', Finset.sum_congr rfl (fun v _ => hsumB v)]
      _ = 2 * ∑ v : Fin 26, (B v).card := by ring
  have hU : U.card = ∑ v : Fin 26, (U.filter (fun j => z j = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (z j))
  have hfin : ∑ v : Fin 26, 5 * (B v).card ≤ ∑ v : Fin 26,
      4 * (2 * (U.filter (fun j => z j = v)).card + ((A' v).card - 1)) :=
    Finset.sum_le_sum (fun v _ => hv v)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← hU]
    at hfin
  omega

open Classical in
theorem core2 (gs : List Gate) (o : ℕ) (H : Hy gs o) : 64 ≤ gs.length := by
  have hstar : ∀ j : Fin gs.length, ∃ (z : Fin 26) (A : Finset (Fin 26)) (lw : ℕ),
      ((gs.get j).op = GateOp.and → Reach gs o (26 + (j : ℕ)) →
        (∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true) →
        A ⊆ N z ∧ (∀ p ∈ A, val gs lw (fun v : Fin 26 => decide (v = p)) = true) ∧
        val gs lw (fun v : Fin 26 => decide (v ∉ N z)) = false ∧
        ∀ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true →
          (s = z ∧ t ∈ A) ∨ (t = z ∧ s ∈ A)) := by
    intro j
    by_cases h : (gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)) ∧
        ∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true
    · obtain ⟨h1, h2, s, t, h3⟩ := h
      obtain ⟨z, A, lw, hh⟩ := star gs o H j j.2 h1 h2 s t h3
      exact ⟨z, A, lw, fun _ _ _ => hh⟩
    · exact ⟨0, ∅, 0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose z A lw hst using hstar
  have hst' : ∀ j ∈ US gs o, A j ⊆ N (z j) ∧
      (∀ p ∈ A j, val gs (lw j) (fun v : Fin 26 => decide (v = p)) = true) ∧
      val gs (lw j) (fun v : Fin 26 => decide (v ∉ N (z j))) = false ∧
      ∀ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true →
        (s = z j ∧ t ∈ A j) ∨ (t = z j ∧ s ∈ A j) := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := (mem_US gs o j).1 hj
    exact hst j h1 h2 h3
  have hmax : ∀ v : Fin 26, ∃ (A' : Finset (Fin 26)) (o' : ℕ), A' ⊆ N v ∧
      (∀ p : Fin 26, p ∈ A' → val gs o' (fun i : Fin 26 => decide (i = p)) = true) ∧
      (1 ≤ A'.card → val gs o' (fun i : Fin 26 => decide (i ∉ N v)) = false) ∧
      (∀ j ∈ US gs o, z j = v → (A j).card ≤ A'.card) := by
    intro v
    by_cases hne : ((US gs o).filter (fun j => z j = v)).Nonempty
    · obtain ⟨j0, hj0, hmx⟩ := Finset.exists_max_image _ (fun j => (A j).card) hne
      rw [Finset.mem_filter] at hj0
      obtain ⟨hA1, hA2, hA3, _⟩ := hst' j0 hj0.1
      rw [hj0.2] at hA1 hA3
      exact ⟨A j0, lw j0, hA1, hA2, fun _ => hA3,
        fun j hj hz => hmx j (Finset.mem_filter.2 ⟨hj, hz⟩)⟩
    · refine ⟨∅, 0, Finset.empty_subset _, ?_, ?_, ?_⟩
      · intro p hp
        simp at hp
      · intro h
        simp at h
      · intro j hj hz
        exact absurd ⟨j, Finset.mem_filter.2 ⟨hj, hz⟩⟩ hne
  choose A' o' hA1 hA2 hA3 hA4 using hmax
  have hmc : ∑ v : Fin 26, ((A' v).card - 1) ≤ (MGS gs A').card :=
    mrg_count N A' gs o' hLN H.1 H.2.1 hA1 hA2 hA3
  have htl := tally (US gs o) z A A' (fun j hj => (hst' j hj).1)
    (fun j hj => hA4 (z j) j hj rfl) (by
      intro v y hadj
      obtain ⟨j, hj, hval⟩ := cover gs o H v y hadj
      exact ⟨j, hj, (hst' j hj).2.2.2 v y hval⟩)
  have htop := top_count gs o H.1 (US gs o) (ROS gs o)
    (fun j hj => ⟨((mem_US gs o j).1 hj).1, ((mem_US gs o j).1 hj).2.1⟩) (mem_ROS gs o)
  have hd1 : Disjoint (US gs o) (ROS gs o) := by
    rw [Finset.disjoint_left]
    intro g h1 h2
    have a1 := ((mem_US gs o g).1 h1).1
    have a2 := ((mem_ROS gs o g).1 h2).1
    rw [a1] at a2
    exact GateOp.noConfusion a2
  have hd2 : Disjoint (US gs o ∪ ROS gs o) (MGS gs A') := by
    rw [Finset.disjoint_left]
    intro g hg hm
    obtain ⟨_, v, hmj⟩ := Finset.mem_filter.1 hm
    obtain ⟨ho, _, w1, w2, hab, r, _, r', _, hv1, _⟩ := hmj
    rcases Finset.mem_union.1 hg with h | h
    · have a1 := ((mem_US gs o g).1 h).1
      rw [a1] at ho
      exact GateOp.noConfusion ho
    · have hr := ((mem_ROS gs o g).1 h).2
      have hm1 : w1 ∈ (gs.get g).inputs := by rw [hab]; simp
      exact reach_single gs o H _ hr r
        ((val_or gs _ g g.2 ho).2 ⟨w1, hm1, H.2.1 g w1 hm1, hv1⟩)
  have hcard : (US gs o ∪ ROS gs o ∪ MGS gs A').card ≤ gs.length := by
    simpa using Finset.card_le_univ (US gs o ∪ ROS gs o ∪ MGS gs A')
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1] at hcard
  omega

open PEqualNP.EdgeOwnership in
theorem core (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hacc : ∀ (x3 x4 : Fin 13), x3 - x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      C.eval ((List.ofFn fun (x6 : Fin 13) => decide (x6 = x3)) ++
        List.ofFn fun (x6 : Fin 13) => decide (x6 = x4)) = true)
    (hrej : ∀ (x3 : Finset (Fin 13)), x3.card = 4 →
      (∀ (x5 : Fin 13), ({x6 ∈ x3 | x6 - x5 ∈ ({0, 1, 3, 9} : Finset (Fin 13))}).card ≤ 2) →
      C.eval ((List.ofFn fun (x6 : Fin 13) => decide (x6 ∈ x3)) ++
        List.ofFn fun (x6 : Fin 13) => decide (∀ x7 ∈ x3, x7 - x6 ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) = false)
    (hflat : ¬ ∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 26 C i j) : 64 ≤ C.size := by
  have legal := legal_of C hmono
  have hin := hin_of C 26 hrb
  have H : Hy C.gates C.output := by
    refine ⟨legal, hin, ?_, ?_, ?_⟩
    · intro j hj hop a ha
      exact lin_and C legal hin hflat j hj hop a ha
    · intro s t hadj
      obtain ⟨hD, hsub⟩ := accwit s t hadj
      have h : val C.gates C.output (ein (Pp s t) (Ll s t)) = true := by
        have h := hacc _ _ hD
        rw [mk_eq] at h
        exact h
      exact val_mono C.gates legal _ _ (fun u hu => decide_eq_true (hsub u hu)) C.output h
    · intro s t hadj
      obtain ⟨hc, hq, hs, ht⟩ := wit s t hadj
      have h : val C.gates C.output (qin (Wt s t)) = false := by
        have h := hrej _ hc hq
        rw [mk_eq] at h
        exact h
      cases hv : val C.gates C.output (pr s t) with
      | false => rfl
      | true =>
        have h2 := val_mono C.gates legal (pr s t) (qin (Wt s t)) (by
          intro u hu
          have e : u = s ∨ u = t := of_decide_eq_true hu
          rcases e with e | e
          · rw [e]
            exact hs
          · rw [e]
            exact ht) C.output hv
        rw [h] at h2
        exact Bool.noConfusion h2
  exact core2 C.gates C.output H

end PEqualNP.Outside.L_meta_5158

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.HeptadCover PEqualNP.TopForm

theorem PEqualNP.Outside.L_meta_5158 : have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → PEqualNP.TopForm.andPairs (26 : ℕ) x3 = (0 : ℕ) → (64 : ℕ) ≤ x3.size := by
  intro negative valid C good flat
  obtain ⟨monotone, readsBack, accepts, rejects⟩ := good
  have onLine : ∀ p l : Fin 13, p ∈ singerLines3 l ↔
      p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by decide +kernel
  refine PEqualNP.Outside.L_meta_5158.core C monotone readsBack
    (fun p l h => accepts p l ((onLine p l).mpr h)) ?_ ?_
  · intro Q card intersections
    have sameIntersection (l : Fin 13) :
        Q ∩ singerLines3 l = Q.filter (fun p => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_filter, onLine]
    have quad : IsQuadrangle singerLines3 Q := ⟨card, fun l => by
      rw [sameIntersection l]
      exact intersections l⟩
    have sameLines :
        (List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)) =
        List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) := by
      apply congrArg List.ofFn
      funext l
      apply decide_eq_decide.mpr
      simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left, onLine]
      constructor
      · exact fun h p hQ hL => h hL hQ
      · exact fun h p hL hQ => h p hQ hL
    have rejected := rejects Q quad
    change C.eval ((List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))) = false at rejected
    rw [sameLines] at rejected
    exact rejected
  · rintro ⟨i, j, andI, andJ, inside⟩
    letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    have bound (k : ℕ) (hop : (gateAt C k).op = GateOp.and) : k < C.gates.length := by
      by_contra! outside
      simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none outside] at hop
    unfold andPairs at flat
    have member : (i, j) ∈
        ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter fun p : ℕ × ℕ =>
          (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 26 C p.1 p.2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (bound i andI), Finset.mem_range.mpr (bound j andJ)⟩, andI, andJ, inside⟩
    rw [Finset.card_eq_zero.mp flat] at member
    exact Finset.notMem_empty _ member
