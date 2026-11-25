import PEqualNP.Defs

-- The counting argument below reuses willakone’s checked proof of L-meta-2059 (PR 4283).

namespace PEqualNP.Outside.L_meta_1896.Routes

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
    (hτ : ∀ p ∈ M, ∀ v, c v = false → τ p v = true → v = p)
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
    · rw [val_input gates _ w hwn] at hwc h1 h2
      have e1 := hτ y hy _ hwc h1
      have e2 := hτ y' hy' _ hwc h2
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
    (hτ : ∀ p ∈ M, ∀ v, c v = false → τ p v = true → v = p)
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
    (hτ : ∀ p ∈ M, ∀ v, c v = false → τ p v = true → v = p)
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
    (hτ : ∀ p ∈ M, ∀ v, c v = false → τ p v = true → v = p)
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


lemma or_sensitivity_bound {n : ℕ} (C : Circuit) (M : Finset (Fin n))
    (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, c v = false → τ p v = true → v = p)
    (legal : Monotone2 C)
    (hin : ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < n + i.val)
    (hM : 1 ≤ M.card) (hc : circuitFun n C c = false)
    (ht : ∀ p ∈ M, circuitFun n C (τ p) = true) :
    M.card - 1 ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard := by
  classical
  have h := mcount C.gates M c τ hτ legal hin hM C.output hc ht
  rw [← h]
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Finset.card_filter]
  apply Finset.sum_le_sum
  intro g hg
  by_cases hm : Mrg C.gates M c τ g
  · have hop : C.gates[g.val].op = GateOp.or := hm.1
    simp [hm, hop]
  · simp [hm]

end PEqualNP.Outside.L_meta_1896.Routes


namespace PEqualNP.Outside.L_meta_1896.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cleanGate (k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun i => if i < k then i + 1 else 0⟩

def cleanGates : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => cleanGate k g :: cleanGates (k + 1) gs

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma cleanGate_values (w : List Bool) (g : Gate) :
    (cleanGate w.length g).op.eval ((cleanGate w.length g).inputs.map
      fun i => (false :: w).getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  congr 1
  simp only [cleanGate, List.map_map]
  apply List.map_congr_left
  intro i hi
  by_cases h : i < w.length
  · simp [h]
  · simp [h, List.getD_eq_default w false (Nat.le_of_not_gt h)]

lemma clean_run (gs : List Gate) (w : List Bool) :
    run (cleanGates w.length gs) (false :: w) = false :: run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [cleanGates, run, List.foldl_cons]
    rw [cleanGate_values]
    simpa only [run, List.cons_append, List.length_append, List.length_singleton] using
      ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])

lemma cleanGates_length (k : ℕ) (gs : List Gate) : (cleanGates k gs).length = gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => simp [cleanGates, ih]

lemma cleanGate_inputs_lt (k : ℕ) (g : Gate) :
    ∀ a ∈ (cleanGate k g).inputs, a < k + 1 := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  split_ifs <;> omega

lemma cleanGates_back (k : ℕ) (gs : List Gate) :
    ∀ j : Fin (cleanGates k gs).length,
      ∀ a ∈ ((cleanGates k gs).get j).inputs, a < k + 1 + j.val := by
  induction gs generalizing k with
  | nil => intro j; exact Fin.elim0 j
  | cons g gs ih =>
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [cleanGates] using cleanGate_inputs_lt k g
    · simpa [cleanGates, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1) j

lemma cleanGates_op (k : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ((cleanGates k gs)[j]'(by simpa [cleanGates_length] using hj)).op = (gs[j]'hj).op := by
  induction gs generalizing k j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => rfl
    | succ j => simpa [cleanGates] using ih (k + 1) j (by simpa using hj)

lemma cleanGates_legal (k : ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ cleanGates k gs,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing k with
  | nil => simp [cleanGates]
  | cons g gs ih =>
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · simpa [cleanGate] using h g (by simp)
    · exact ih (k + 1) (fun g hg => h g (by simp [hg])) g' hg'

def cleanCircuit (n : ℕ) (C : Circuit) : Circuit :=
  ⟨cleanGates n C.gates, C.output + 1⟩

lemma cleanCircuit_eval (C : Circuit) (x : List Bool) :
    (cleanCircuit x.length C).eval (false :: x) = C.eval x := by
  change (run (cleanGates x.length C.gates) (false :: x)).getD (C.output + 1) false = _
  rw [clean_run]
  rfl

lemma cleanCircuit_fun {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    circuitFun (n + 1) (cleanCircuit n C) (Fin.cases false x) = circuitFun n C x := by
  have h := cleanCircuit_eval C (List.ofFn x)
  simpa [circuitFun, List.ofFn_succ] using h

lemma cleanCircuit_or_count (n : ℕ) (C : Circuit) :
    {j : Fin (cleanCircuit n C).gates.length |
      ((cleanCircuit n C).gates.get j).op = GateOp.or}.ncard =
      {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard := by
  classical
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Finset.card_filter]
  apply Fintype.sum_equiv (finCongr (cleanGates_length n C.gates))
  intro j
  have hj : j.val < C.gates.length := by simpa [cleanGates_length] using j.isLt
  simp only [cleanCircuit, List.get_eq_getElem, finCongr_apply, Fin.val_cast]
  simp only [cleanGates_op n C.gates j.val hj]

end PEqualNP.Outside.L_meta_1896.Normalize

namespace PEqualNP.Outside.L_meta_1896.Sensitivity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Normalize

lemma or_sensitivity_bound {n : ℕ} (C : Circuit) (M : Finset (Fin n))
    (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, c v = false → τ p v = true → v = p)
    (legal : Monotone2 C) (hM : 1 ≤ M.card) (hc : circuitFun n C c = false)
    (ht : ∀ p ∈ M, circuitFun n C (τ p) = true) :
    M.card - 1 ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard := by
  classical
  let M' : Finset (Fin (n + 1)) := M.image Fin.succ
  let c' : Fin (n + 1) → Bool := Fin.cases false c
  let τ' : Fin (n + 1) → Fin (n + 1) → Bool :=
    Fin.cases (fun _ => false) (fun p => Fin.cases false (τ p))
  have card : M'.card = M.card := Finset.card_image_of_injective _ (Fin.succ_injective n)
  have one : ∀ p ∈ M', ∀ v, c' v = false → τ' p v = true → v = p := by
    intro p hp v
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    refine Fin.cases ?_ (fun v => ?_) v
    · simp [τ']
    · intro hc ht
      exact congrArg Fin.succ (hτ q hq v hc ht)
  have hm : 1 ≤ M'.card := by omega
  have hlegal : Monotone2 (cleanCircuit n C) := cleanGates_legal n C.gates legal
  have hback : ∀ i : Fin (cleanCircuit n C).gates.length,
      ∀ a ∈ ((cleanCircuit n C).gates.get i).inputs, a < (n + 1) + i.val :=
    cleanGates_back n C.gates
  have hfalse : circuitFun (n + 1) (cleanCircuit n C) c' = false :=
    (cleanCircuit_fun C c).trans hc
  have htrue : ∀ p ∈ M', circuitFun (n + 1) (cleanCircuit n C) (τ' p) = true := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (cleanCircuit_fun C (τ q)).trans (ht q hq)
  have h := Routes.or_sensitivity_bound (cleanCircuit n C) M' c' τ' one hlegal hback hm hfalse htrue
  rw [cleanCircuit_or_count] at h
  simpa only [card] using h

def gateValue {n : ℕ} (C : Circuit) (c : Fin n → Bool) (j : Fin C.gates.length) : Bool :=
  circuitFun n {C with output := n + j.val} c

noncomputable def falseOrCount {n : ℕ} (C : Circuit) (c : Fin n → Bool) : ℕ :=
  {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or ∧ gateValue C c j = false}.ncard

lemma clean_gateValue {n : ℕ} (C : Circuit) (c : Fin n → Bool)
    (j : Fin (cleanCircuit n C).gates.length) :
    gateValue (cleanCircuit n C) (Fin.cases false c) j =
      gateValue C c (Fin.cast (cleanGates_length n C.gates) j) := by
  have h := cleanCircuit_fun {C with output := n + j.val} c
  change circuitFun (n + 1) ⟨cleanGates n C.gates, (n + 1) + j.val⟩ (Fin.cases false c) =
    circuitFun n ⟨C.gates, n + j.val⟩ c
  simpa [cleanCircuit, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

lemma clean_falseOrCount {n : ℕ} (C : Circuit) (c : Fin n → Bool) :
    falseOrCount (cleanCircuit n C) (Fin.cases false c) = falseOrCount C c := by
  classical
  simp only [falseOrCount, Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Finset.card_filter]
  apply Fintype.sum_equiv (finCongr (cleanGates_length n C.gates))
  intro j
  have hj : j.val < C.gates.length := by simpa [cleanGates_length] using j.isLt
  have ho : ((cleanCircuit n C).gates.get j).op =
      (C.gates.get (Fin.cast (cleanGates_length n C.gates) j)).op :=
    cleanGates_op n C.gates j.val hj
  have hv := clean_gateValue C c j
  simp only [finCongr_apply, ho, hv]

lemma or_false_sensitivity_bound_back {n : ℕ} (C : Circuit) (M : Finset (Fin n))
    (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, c v = false → τ p v = true → v = p)
    (legal : Monotone2 C)
    (hin : ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < n + i.val)
    (hM : 1 ≤ M.card) (hc : circuitFun n C c = false)
    (ht : ∀ p ∈ M, circuitFun n C (τ p) = true) :
    M.card - 1 ≤ falseOrCount C c := by
  classical
  have h := Routes.mcount C.gates M c τ hτ legal hin hM C.output hc ht
  rw [← h]
  simp only [falseOrCount, Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Finset.card_filter]
  apply Finset.sum_le_sum
  intro g hg
  by_cases hm : Routes.Mrg C.gates M c τ g
  · have hop : C.gates[g.val].op = GateOp.or := hm.1
    have hv : gateValue C c g = false := hm.2.1
    simp [hm, hop, hv]
  · simp [hm]

lemma or_false_sensitivity_bound {n : ℕ} (C : Circuit) (M : Finset (Fin n))
    (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, c v = false → τ p v = true → v = p)
    (legal : Monotone2 C) (hM : 1 ≤ M.card) (hc : circuitFun n C c = false)
    (ht : ∀ p ∈ M, circuitFun n C (τ p) = true) :
    M.card - 1 ≤ falseOrCount C c := by
  classical
  let M' : Finset (Fin (n + 1)) := M.image Fin.succ
  let c' : Fin (n + 1) → Bool := Fin.cases false c
  let τ' : Fin (n + 1) → Fin (n + 1) → Bool :=
    Fin.cases (fun _ => false) (fun p => Fin.cases false (τ p))
  have card : M'.card = M.card := Finset.card_image_of_injective _ (Fin.succ_injective n)
  have one : ∀ p ∈ M', ∀ v, c' v = false → τ' p v = true → v = p := by
    intro p hp v
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    refine Fin.cases ?_ (fun v => ?_) v
    · simp [τ']
    · intro hc ht
      exact congrArg Fin.succ (hτ q hq v hc ht)
  have hm : 1 ≤ M'.card := by omega
  have hlegal : Monotone2 (cleanCircuit n C) := cleanGates_legal n C.gates legal
  have hback : ∀ i : Fin (cleanCircuit n C).gates.length,
      ∀ a ∈ ((cleanCircuit n C).gates.get i).inputs, a < (n + 1) + i.val :=
    cleanGates_back n C.gates
  have hfalse : circuitFun (n + 1) (cleanCircuit n C) c' = false :=
    (cleanCircuit_fun C c).trans hc
  have htrue : ∀ p ∈ M', circuitFun (n + 1) (cleanCircuit n C) (τ' p) = true := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (cleanCircuit_fun C (τ q)).trans (ht q hq)
  have h := or_false_sensitivity_bound_back (cleanCircuit n C) M' c' τ' one hlegal hback hm hfalse htrue
  rw [clean_falseOrCount] at h
  simpa only [card] using h

lemma all_or_false_of_count {n : ℕ} (C : Circuit) (c : Fin n → Bool) (k : ℕ)
    (hfalse : k ≤ falseOrCount C c)
    (htotal : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ≤ k) :
    ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.or → gateValue C c j = false := by
  let A : Set (Fin C.gates.length) :=
    {j | (C.gates.get j).op = GateOp.or ∧ gateValue C c j = false}
  let B : Set (Fin C.gates.length) := {j | (C.gates.get j).op = GateOp.or}
  have hsub : A ⊆ B := fun _ h => h.1
  have hcard : B.ncard ≤ A.ncard := le_trans htotal hfalse
  have he : A = B := Set.eq_of_subset_of_ncard_le hsub hcard
  intro j hj
  have hjA : j ∈ A := he.symm ▸ hj
  exact hjA.2

end PEqualNP.Outside.L_meta_1896.Sensitivity


namespace PEqualNP.Outside.L_meta_1896_aux.FourRows

abbrev incidence (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def points (a : Fin 4) : Finset (Fin 13) :=
  ([{0, 1, 2}, {3, 4, 5}, {6, 8, 12}, {7, 9, 10, 11}] : List (Finset (Fin 13))).getD a.val ∅

def row (a : Fin 4) (v : Fin 26) : Bool :=
  decide (v.val ∈ ([[0, 1, 2, 16, 20, 21, 22], [3, 4, 5, 19, 23, 24, 25], [6, 8, 12, 13, 14, 15, 17], [7, 9, 10, 11, 16, 18, 25]] : List (List ℕ)).getD a.val [])

def rowInput (X : Finset (Fin 13)) (v : Fin 26) : Bool :=
  decide ((∃ p ∈ X, v = Fin.castAdd 13 p) ∨
    ∃ l : Fin 13, v = Fin.natAdd 13 l ∧ ∀ p ∈ X, ¬incidence p l)

def admissible (X : Finset (Fin 13)) : Prop :=
  (∀ p ∉ X, ∃ l : Fin 13, (∀ q ∈ X, ¬incidence q l) ∧ incidence p l) ∧
  (¬∃ l : Fin 13, ∀ p ∈ X, incidence p l) ∧
  ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ X, ¬incidence q l) → incidence p l

def missing (a : Fin 4) : Finset (Fin 26) := Finset.univ.filter fun v => row a v = false

def pairInput (p l : Fin 13) (v : Fin 26) : Bool :=
  decide (v = Fin.castAdd 13 p ∨ v = Fin.natAdd 13 l)

def edgeFor (a : Fin 4) (v : Fin 26) : Fin 13 × Fin 13 :=
  ([
    (0, 0), (0, 0), (0, 0), (3, 3), (4, 3), (5, 9), (6, 3), (7, 7), (8, 7), (9, 8), (10, 7), (11, 8), (12, 3),
    (0, 0), (1, 1), (2, 2), (0, 0), (0, 4), (1, 5), (2, 6), (0, 0), (0, 0), (0, 0), (0, 10), (1, 11), (0, 12),
    (0, 10), (1, 11), (2, 6), (0, 0), (0, 0), (0, 0), (6, 6), (7, 6), (8, 12), (9, 6), (10, 10), (11, 10), (12, 11),
    (3, 0), (4, 1), (3, 2), (3, 3), (4, 4), (5, 5), (0, 0), (3, 7), (4, 8), (5, 9), (0, 0), (0, 0), (0, 0),
    (0, 0), (1, 0), (2, 1), (3, 0), (4, 1), (5, 2), (0, 0), (7, 4), (0, 0), (9, 0), (10, 1), (11, 2), (0, 0),
    (0, 0), (0, 0), (0, 0), (6, 3), (0, 0), (6, 5), (6, 6), (8, 7), (8, 8), (12, 9), (6, 10), (12, 11), (8, 12),
    (0, 12), (1, 5), (2, 12), (3, 3), (4, 3), (5, 5), (6, 3), (0, 0), (8, 5), (0, 0), (0, 0), (0, 0), (12, 3),
    (9, 0), (10, 1), (11, 2), (0, 0), (7, 4), (0, 0), (7, 6), (7, 7), (9, 8), (9, 9), (10, 10), (7, 11), (0, 0)] : List (Fin 13 × Fin 13)).getD (26 * a.val + v.val) (0, 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 100000 in
lemma rows_admissible : ∀ a : Fin 4, admissible (points a) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_eq : ∀ a : Fin 4, row a = rowInput (points a) := by decide +kernel

set_option maxRecDepth 10000 in
lemma missing_card : ∀ a : Fin 4, (missing a).card = 19 := by decide +kernel

set_option maxRecDepth 10000 in
lemma rows_cover : ∀ v : Fin 26, ∃ a : Fin 4, row a v = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 100000 in
lemma edgeFor_ok : ∀ (a : Fin 4) (v : Fin 26), row a v = false →
    incidence (edgeFor a v).1 (edgeFor a v).2 ∧
      ∀ w : Fin 26, row a w = false →
        pairInput (edgeFor a v).1 (edgeFor a v).2 w = true → w = v := by
  decide +kernel

end PEqualNP.Outside.L_meta_1896_aux.FourRows

namespace PEqualNP.Outside.L_meta_1896.FourRowsSensitivity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Routes
open PEqualNP.Outside.L_meta_1896.Sensitivity
open PEqualNP.Outside.L_meta_1896_aux.FourRows

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

lemma eighteen_false_at_row (C : Circuit) (legal : Monotone2 C)
    (pos : ∀ p l : Fin 13, incidence p l → circuitFun 26 C (pairInput p l) = true)
    (neg : ∀ a : Fin 4, circuitFun 26 C (row a) = false) (a : Fin 4) :
    18 ≤ falseOrCount C (row a) := by
  let τ : Fin 26 → Fin 26 → Bool := fun v => pairInput (edgeFor a v).1 (edgeFor a v).2
  have one : ∀ p ∈ missing a, ∀ v, row a v = false → τ p v = true → v = p := by
    intro p hp
    exact (edgeFor_ok a p (Finset.mem_filter.mp hp).2).2
  have positive : ∀ p ∈ missing a, circuitFun 26 C (τ p) = true := by
    intro p hp
    exact pos _ _ (edgeFor_ok a p (Finset.mem_filter.mp hp).2).1
  have h := or_false_sensitivity_bound C (missing a) (row a) τ one legal
    (by rw [missing_card]; omega) (neg a) positive
  simpa only [missing_card, Nat.reduceSub] using h

lemma all_or_false_at_rows (C : Circuit) (legal : Monotone2 C)
    (pos : ∀ p l : Fin 13, incidence p l → circuitFun 26 C (pairInput p l) = true)
    (neg : ∀ a : Fin 4, circuitFun 26 C (row a) = false)
    (small : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ≤ 18) :
    ∀ a : Fin 4, ∀ j : Fin C.gates.length,
      (C.gates.get j).op = GateOp.or → gateValue C (row a) j = false := by
  intro a
  exact all_or_false_of_count C (row a) 18 (eighteen_false_at_row C legal pos neg a) small

lemma all_or_false_at_small (C : Circuit) (legal : Monotone2 C)
    (pos : ∀ p l : Fin 13, incidence p l → circuitFun 26 C (pairInput p l) = true)
    (neg : ∀ a : Fin 4, circuitFun 26 C (row a) = false)
    (small : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ≤ 18)
    (x : Fin 26 → Bool) (single : ∃ v : Fin 26, ∀ w, x w = true → w = v) :
    ∀ j : Fin C.gates.length,
      (C.gates.get j).op = GateOp.or → gateValue C x j = false := by
  obtain ⟨v, hv⟩ := single
  obtain ⟨a, ha⟩ := rows_cover v
  have sub : ∀ w, x w = true → row a w = true := by
    intro w hw
    exact hv w hw ▸ ha
  intro j hj
  have hf := all_or_false_at_rows C legal pos neg small a j hj
  cases he : gateValue C x j with
  | false => rfl
  | true =>
    have htrue : gateValue C (row a) j = true :=
      val_mono C.gates legal x (row a) sub (26 + j.val) he
    rw [htrue] at hf
    exact Bool.noConfusion hf

lemma output_false_at_small (C : Circuit) (legal : Monotone2 C)
    (neg : ∀ a : Fin 4, circuitFun 26 C (row a) = false)
    (x : Fin 26 → Bool) (single : ∃ v : Fin 26, ∀ w, x w = true → w = v) :
    circuitFun 26 C x = false := by
  obtain ⟨v, hv⟩ := single
  obtain ⟨a, ha⟩ := rows_cover v
  have sub : ∀ w, x w = true → row a w = true := by
    intro w hw
    exact hv w hw ▸ ha
  cases he : circuitFun 26 C x with
  | false => rfl
  | true =>
    have htrue : circuitFun 26 C (row a) = true :=
      val_mono C.gates legal x (row a) sub C.output he
    have hf := neg a
    rw [htrue] at hf
    exact Bool.noConfusion hf

end PEqualNP.Outside.L_meta_1896.FourRowsSensitivity

namespace PEqualNP.Outside.L_meta_1896.DirtyOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Sensitivity
open PEqualNP.Outside.L_meta_1896.FourRowsSensitivity

lemma at_most_one_true {n : ℕ} (C : Circuit) (c : Fin n → Bool) (k : ℕ)
    (hfalse : k ≤ falseOrCount C c)
    (htotal : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ≤ k + 1)
    (i j : Fin C.gates.length) (hi : (C.gates.get i).op = GateOp.or)
    (hj : (C.gates.get j).op = GateOp.or)
    (hvi : gateValue C c i = true) (hvj : gateValue C c j = true) : i = j := by
  classical
  by_contra hne
  let A : Set (Fin C.gates.length) :=
    {j | (C.gates.get j).op = GateOp.or ∧ gateValue C c j = false}
  let B : Set (Fin C.gates.length) := {j | (C.gates.get j).op = GateOp.or}
  have hia : i ∉ A := by simp [A, hvi]
  have hja : j ∉ A := by simp [A, hvj]
  have hij : i ∉ insert j A := by simp [hne, hia]
  have hsub : insert i (insert j A) ⊆ B := by
    intro g hg
    rcases hg with rfl | hg
    · exact hi
    rcases hg with rfl | hg
    · exact hj
    · exact hg.1
  have hc := Set.ncard_le_ncard hsub
  rw [Set.ncard_insert_of_notMem hij, Set.ncard_insert_of_notMem hja] at hc
  have ha : A.ncard = falseOrCount C c := rfl
  have hb : B.ncard ≤ k + 1 := htotal
  omega

def singletonInput {n : ℕ} (v : Fin n) : Fin n → Bool :=
  fun w => decide (w = v)

noncomputable def dirtyOrCount {n : ℕ} (C : Circuit) : ℕ :=
  {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or ∧
    ∃ v : Fin n, gateValue C (singletonInput v) j = true}.ncard

lemma dirty_or_bound_of_triple_cover {n : ℕ} {R : Type*} (C : Circuit)
    (rows : R → Fin n → Bool) (legal : Monotone2 C)
    (hlower : ∀ r, 18 ≤ falseOrCount C (rows r))
    (small : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ≤ 19)
    (cover : ∀ u v w : Fin n, ∃ r,
      (rows r u = true ∧ rows r v = true) ∨
      (rows r u = true ∧ rows r w = true) ∨
      (rows r v = true ∧ rows r w = true)) :
    dirtyOrCount (n := n) C ≤ 2 := by
  classical
  let D : Finset (Fin C.gates.length) := Finset.univ.filter
    (fun j => (C.gates.get j).op = GateOp.or ∧
      ∃ v : Fin n, gateValue C (singletonInput v) j = true)
  have hd : dirtyOrCount (n := n) C = D.card := by
    simp [dirtyOrCount, D, Set.ncard_eq_toFinset_card']
  rw [hd]
  by_contra hcard
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < D.card)
  obtain ⟨hi, u, hu⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨hj, v, hv⟩ := (Finset.mem_filter.mp hj).2
  obtain ⟨hk, w, hw⟩ := (Finset.mem_filter.mp hk).2
  obtain ⟨r, hc⟩ := cover u v w
  have up (a : Fin C.gates.length) (x : Fin n)
      (ha : gateValue C (singletonInput x) a = true) (hx : rows r x = true) :
      gateValue C (rows r) a = true := by
    apply val_mono C.gates legal (singletonInput x) (rows r) _ (n + a.val) ha
    intro y hy
    have he : y = x := by simpa [singletonInput] using hy
    exact he ▸ hx
  rcases hc with ⟨hru, hrv⟩ | ⟨hru, hrw⟩ | ⟨hrv, hrw⟩
  · exact hij (at_most_one_true C (rows r) 18 (hlower r) small i j hi hj
      (up i u hu hru) (up j v hv hrv))
  · exact hik (at_most_one_true C (rows r) 18 (hlower r) small i k hi hk
      (up i u hu hru) (up k w hw hrw))
  · exact hjk (at_most_one_true C (rows r) 18 (hlower r) small j k hj hk
      (up j v hv hrv) (up k w hw hrw))

end PEqualNP.Outside.L_meta_1896.DirtyOr


namespace PEqualNP.Outside.L_meta_1896_aux.PairRows

abbrev incidence (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def points (a : Fin 25) : Finset (Fin 13) :=
  ([
    {0, 1, 2},
    {3, 4, 5},
    {6, 8, 12},
    {7, 9, 10, 11},
    {2, 4, 7},
    {0, 4, 6, 9},
    {0, 3, 8, 11},
    {3, 10, 12},
    {2, 5, 8, 10},
    {1, 6, 7},
    {1, 2, 9, 12},
    {5, 6, 11},
    {7, 8, 9},
    {0, 4, 10, 12},
    {2, 3, 6},
    {1, 10, 11},
    {5, 7, 12},
    {4, 11, 12},
    {1, 3, 4, 8},
    {0, 3, 7},
    {0, 5, 9},
    {2, 3, 9},
    {0, 1, 5},
    {1, 6, 10},
    {0, 2, 11}] : List (Finset (Fin 13))).getD a.val ∅

def row (a : Fin 25) (v : Fin 26) : Bool :=
  decide (v.val ∈ ([
    [0, 1, 2, 16, 20, 21, 22],
    [3, 4, 5, 19, 23, 24, 25],
    [6, 8, 12, 13, 14, 15, 17],
    [7, 9, 10, 11, 16, 18, 25],
    [2, 4, 7, 13, 18, 22, 23],
    [0, 4, 6, 9, 15, 20, 24],
    [0, 3, 8, 11, 14, 19, 22],
    [3, 10, 12, 17, 18, 19, 21],
    [2, 5, 8, 10, 13, 16, 24],
    [1, 6, 7, 15, 21, 22, 25],
    [1, 2, 9, 12, 17, 20, 23],
    [5, 6, 11, 13, 14, 20, 25],
    [7, 8, 9, 14, 15, 16, 23],
    [0, 4, 10, 12, 15, 18, 19],
    [2, 3, 6, 17, 21, 22, 24],
    [1, 10, 11, 16, 17, 19, 25],
    [5, 7, 12, 13, 14, 21, 23],
    [4, 11, 12, 13, 18, 19, 20],
    [1, 3, 4, 8, 19, 22, 23],
    [0, 3, 7, 14, 18, 21, 22],
    [0, 5, 9, 14, 16, 20, 24],
    [2, 3, 9, 17, 18, 23, 24],
    [0, 1, 5, 16, 19, 20, 21],
    [1, 6, 10, 15, 17, 21, 25],
    [0, 2, 11, 16, 18, 20, 22]] : List (List ℕ)).getD a.val [])

def rowInput (X : Finset (Fin 13)) (v : Fin 26) : Bool :=
  decide ((∃ p ∈ X, v = Fin.castAdd 13 p) ∨
    ∃ l : Fin 13, v = Fin.natAdd 13 l ∧ ∀ p ∈ X, ¬incidence p l)

def admissible (X : Finset (Fin 13)) : Prop :=
  (∀ p ∉ X, ∃ l : Fin 13, (∀ q ∈ X, ¬incidence q l) ∧ incidence p l) ∧
  (¬∃ l : Fin 13, ∀ p ∈ X, incidence p l) ∧
  ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ X, ¬incidence q l) → incidence p l

def missing (a : Fin 25) : Finset (Fin 26) := Finset.univ.filter fun v => row a v = false

def pairInput (p l : Fin 13) (v : Fin 26) : Bool :=
  decide (v = Fin.castAdd 13 p ∨ v = Fin.natAdd 13 l)

def edgeFor (a : Fin 25) (v : Fin 26) : Fin 13 × Fin 13 :=
  ((([
    [(0, 0), (0, 0), (0, 0), (3, 3), (4, 3), (5, 9), (6, 3), (7, 7), (8, 7), (9, 8), (10, 7), (11, 8), (12, 3), (0, 0), (1, 1), (2, 2), (0, 0), (0, 4), (1, 5), (2, 6), (0, 0), (0, 0), (0, 0), (0, 10), (1, 11), (0, 12)],
    [(0, 10), (1, 11), (2, 6), (0, 0), (0, 0), (0, 0), (6, 6), (7, 6), (8, 12), (9, 6), (10, 10), (11, 10), (12, 11), (3, 0), (4, 1), (3, 2), (3, 3), (4, 4), (5, 5), (0, 0), (3, 7), (4, 8), (5, 9), (0, 0), (0, 0), (0, 0)],
    [(0, 0), (1, 0), (2, 1), (3, 0), (4, 1), (5, 2), (0, 0), (7, 4), (0, 0), (9, 0), (10, 1), (11, 2), (0, 0), (0, 0), (0, 0), (0, 0), (6, 3), (0, 0), (6, 5), (6, 6), (8, 7), (8, 8), (12, 9), (6, 10), (12, 11), (8, 12)],
    [(0, 12), (1, 5), (2, 12), (3, 3), (4, 3), (5, 5), (6, 3), (0, 0), (8, 5), (0, 0), (0, 0), (0, 0), (12, 3), (9, 0), (10, 1), (11, 2), (0, 0), (7, 4), (0, 0), (7, 6), (7, 7), (9, 8), (9, 9), (10, 10), (7, 11), (0, 0)],
    [(0, 0), (1, 0), (0, 0), (3, 0), (0, 0), (5, 5), (6, 5), (0, 0), (8, 5), (9, 0), (10, 9), (11, 10), (12, 9), (0, 0), (2, 1), (2, 2), (4, 3), (4, 4), (0, 0), (2, 6), (7, 7), (4, 8), (0, 0), (0, 0), (7, 11), (2, 12)],
    [(0, 0), (1, 11), (2, 2), (3, 2), (0, 0), (5, 2), (0, 0), (7, 7), (8, 7), (0, 0), (10, 7), (11, 2), (12, 11), (0, 0), (4, 1), (0, 0), (4, 3), (0, 4), (6, 5), (6, 6), (0, 0), (4, 8), (9, 9), (0, 10), (0, 0), (0, 12)],
    [(0, 0), (1, 1), (2, 1), (0, 0), (4, 1), (5, 9), (6, 6), (7, 6), (0, 0), (9, 6), (10, 1), (0, 0), (12, 9), (0, 0), (0, 0), (3, 2), (3, 3), (0, 4), (8, 5), (0, 0), (3, 7), (8, 8), (0, 0), (0, 10), (11, 11), (0, 12)],
    [(0, 4), (1, 5), (2, 6), (0, 0), (4, 4), (5, 4), (6, 5), (7, 4), (8, 5), (9, 6), (0, 0), (11, 8), (0, 0), (3, 0), (10, 1), (3, 2), (3, 3), (0, 0), (0, 0), (0, 0), (3, 7), (0, 0), (10, 9), (10, 10), (12, 11), (12, 12)],
    [(0, 0), (1, 0), (0, 0), (3, 0), (4, 3), (0, 0), (6, 3), (7, 11), (0, 0), (9, 0), (0, 0), (11, 11), (12, 3), (0, 0), (2, 1), (2, 2), (0, 0), (5, 4), (5, 5), (2, 6), (8, 7), (8, 8), (5, 9), (10, 10), (0, 0), (2, 12)],
    [(0, 12), (0, 0), (2, 2), (3, 2), (4, 8), (5, 2), (0, 0), (0, 0), (8, 8), (9, 8), (10, 9), (11, 2), (12, 9), (1, 0), (1, 1), (0, 0), (6, 3), (7, 4), (1, 5), (6, 6), (7, 7), (0, 0), (0, 0), (6, 10), (1, 11), (0, 0)],
    [(0, 4), (0, 0), (0, 0), (3, 7), (4, 4), (5, 4), (6, 10), (7, 4), (8, 7), (0, 0), (10, 7), (11, 10), (0, 0), (1, 0), (1, 1), (2, 2), (12, 3), (0, 0), (1, 5), (2, 6), (0, 0), (9, 8), (9, 9), (0, 0), (1, 11), (2, 12)],
    [(0, 0), (1, 0), (2, 1), (3, 0), (4, 1), (0, 0), (0, 0), (7, 7), (8, 7), (9, 0), (10, 1), (0, 0), (12, 12), (0, 0), (0, 0), (5, 2), (6, 3), (5, 4), (5, 5), (6, 6), (0, 0), (11, 8), (5, 9), (6, 10), (11, 11), (0, 0)],
    [(0, 10), (1, 1), (2, 1), (3, 2), (4, 1), (5, 2), (6, 3), (0, 0), (0, 0), (0, 0), (10, 1), (11, 2), (12, 3), (9, 0), (0, 0), (0, 0), (0, 0), (7, 4), (8, 5), (7, 6), (7, 7), (8, 8), (9, 9), (0, 0), (7, 11), (8, 12)],
    [(0, 0), (1, 5), (2, 2), (3, 2), (0, 0), (5, 2), (6, 5), (7, 6), (8, 5), (9, 6), (0, 0), (11, 2), (0, 0), (0, 0), (4, 1), (0, 0), (4, 3), (0, 4), (0, 0), (0, 0), (10, 7), (4, 8), (10, 9), (0, 10), (12, 11), (0, 12)],
    [(0, 4), (1, 11), (0, 0), (0, 0), (4, 4), (5, 4), (0, 0), (7, 4), (8, 8), (9, 8), (10, 9), (11, 8), (12, 9), (3, 0), (2, 1), (2, 2), (3, 3), (0, 0), (6, 5), (2, 6), (3, 7), (0, 0), (0, 0), (6, 10), (0, 0), (2, 12)],
    [(0, 4), (0, 0), (2, 6), (3, 3), (4, 3), (5, 4), (6, 3), (7, 4), (8, 12), (9, 6), (0, 0), (0, 0), (12, 3), (1, 0), (1, 1), (11, 2), (0, 0), (0, 0), (1, 5), (0, 0), (10, 7), (11, 8), (10, 9), (10, 10), (1, 11), (0, 0)],
    [(0, 0), (1, 0), (2, 1), (3, 0), (4, 1), (0, 0), (6, 10), (0, 0), (8, 8), (9, 0), (10, 1), (11, 8), (0, 0), (0, 0), (0, 0), (5, 2), (12, 3), (5, 4), (5, 5), (7, 6), (7, 7), (0, 0), (5, 9), (0, 0), (7, 11), (12, 12)],
    [(0, 0), (1, 0), (2, 6), (3, 0), (0, 0), (5, 5), (6, 5), (7, 6), (8, 5), (9, 0), (10, 7), (0, 0), (0, 0), (0, 0), (4, 1), (11, 2), (4, 3), (4, 4), (0, 0), (0, 0), (0, 0), (4, 8), (12, 9), (11, 10), (11, 11), (12, 12)],
    [(0, 10), (0, 0), (2, 6), (0, 0), (0, 0), (5, 9), (6, 6), (7, 6), (0, 0), (9, 6), (10, 9), (11, 10), (12, 9), (1, 0), (1, 1), (3, 2), (3, 3), (4, 4), (1, 5), (0, 0), (3, 7), (4, 8), (0, 0), (0, 0), (1, 11), (8, 12)],
    [(0, 0), (1, 1), (2, 1), (0, 0), (4, 1), (5, 5), (6, 5), (0, 0), (8, 5), (9, 8), (10, 1), (11, 8), (12, 9), (0, 0), (0, 0), (3, 2), (3, 3), (0, 4), (0, 0), (7, 6), (3, 7), (0, 0), (0, 0), (0, 10), (7, 11), (0, 12)],
    [(0, 0), (1, 1), (2, 1), (3, 3), (4, 1), (0, 0), (6, 3), (7, 7), (8, 7), (0, 0), (10, 1), (11, 11), (12, 3), (0, 0), (0, 0), (5, 2), (0, 0), (0, 4), (5, 5), (9, 6), (0, 0), (9, 8), (5, 9), (0, 10), (0, 0), (0, 12)],
    [(0, 4), (1, 5), (0, 0), (0, 0), (4, 4), (5, 4), (6, 5), (7, 4), (8, 5), (0, 0), (10, 10), (11, 10), (12, 11), (3, 0), (2, 1), (2, 2), (3, 3), (0, 0), (0, 0), (2, 6), (3, 7), (9, 8), (9, 9), (0, 0), (0, 0), (2, 12)],
    [(0, 0), (0, 0), (2, 6), (3, 3), (4, 3), (0, 0), (6, 3), (7, 6), (8, 7), (9, 6), (10, 7), (11, 8), (12, 3), (0, 0), (1, 1), (5, 2), (0, 0), (0, 4), (1, 5), (0, 0), (0, 0), (0, 0), (5, 9), (0, 10), (1, 11), (0, 12)],
    [(0, 4), (0, 0), (2, 2), (3, 2), (4, 4), (5, 2), (0, 0), (7, 4), (8, 8), (9, 8), (0, 0), (11, 2), (12, 12), (1, 0), (1, 1), (0, 0), (6, 3), (0, 0), (1, 5), (6, 6), (10, 7), (0, 0), (10, 9), (6, 10), (1, 11), (0, 0)],
    [(0, 0), (1, 5), (0, 0), (3, 3), (4, 3), (5, 5), (6, 3), (7, 7), (8, 5), (9, 9), (10, 7), (0, 0), (12, 3), (0, 0), (2, 1), (2, 2), (0, 0), (0, 4), (0, 0), (2, 6), (0, 0), (11, 8), (0, 0), (0, 10), (11, 11), (0, 12)]] : List (List (Fin 13 × Fin 13))).getD a.val []).getD v.val (0, 0))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 100000 in
lemma rows_admissible : ∀ a : Fin 25, admissible (points a) := by
  unfold admissible
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_eq : ∀ a : Fin 25, row a = rowInput (points a) := by decide +kernel

set_option maxRecDepth 10000 in
lemma missing_card : ∀ a : Fin 25, (missing a).card = 19 := by decide +kernel

set_option maxRecDepth 10000 in
lemma rows_cover : ∀ v : Fin 26, ∃ a : Fin 25, row a v = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 100000 in
lemma edgeFor_ok : ∀ (a : Fin 25) (v : Fin 26), row a v = false →
    incidence (edgeFor a v).1 (edgeFor a v).2 ∧
      ∀ w : Fin 26, row a w = false →
        pairInput (edgeFor a v).1 (edgeFor a v).2 w = true → w = v := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma point_pairs_cover : ∀ p q : Fin 13, ∃ a : Fin 25,
    row a (Fin.castAdd 13 p) = true ∧ row a (Fin.castAdd 13 q) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma line_pairs_cover : ∀ l m : Fin 13, ∃ a : Fin 25,
    row a (Fin.natAdd 13 l) = true ∧ row a (Fin.natAdd 13 m) = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_1896_aux.PairRows

namespace PEqualNP.Outside.L_meta_1896.DirtyOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Sensitivity
open PEqualNP.Outside.L_meta_1896_aux.PairRows

lemma triple_cover : ∀ u v w : Fin 26, ∃ a : Fin 25,
    (row a u = true ∧ row a v = true) ∨
    (row a u = true ∧ row a w = true) ∨
    (row a v = true ∧ row a w = true) := by
  intro u v w
  refine Fin.addCases (m := 13) (n := 13) ?_ ?_ u <;> intro u
  all_goals refine Fin.addCases (m := 13) (n := 13) ?_ ?_ v <;> intro v
  all_goals refine Fin.addCases (m := 13) (n := 13) ?_ ?_ w <;> intro w
  all_goals first
    | exact (point_pairs_cover u v).imp (fun a h => Or.inl h)
    | exact (line_pairs_cover u v).imp (fun a h => Or.inl h)
    | exact (point_pairs_cover u w).imp (fun a h => Or.inr (Or.inl h))
    | exact (line_pairs_cover u w).imp (fun a h => Or.inr (Or.inl h))
    | exact (point_pairs_cover v w).imp (fun a h => Or.inr (Or.inr h))
    | exact (line_pairs_cover v w).imp (fun a h => Or.inr (Or.inr h))

lemma eighteen_false_at_pair_row (C : Circuit) (legal : Monotone2 C)
    (pos : ∀ p l : Fin 13, incidence p l → circuitFun 26 C (pairInput p l) = true)
    (neg : ∀ a : Fin 25, circuitFun 26 C (row a) = false) (a : Fin 25) :
    18 ≤ falseOrCount C (row a) := by
  let τ : Fin 26 → Fin 26 → Bool := fun v => pairInput (edgeFor a v).1 (edgeFor a v).2
  have one : ∀ p ∈ missing a, ∀ v, row a v = false → τ p v = true → v = p := by
    intro p hp
    exact (edgeFor_ok a p (Finset.mem_filter.mp hp).2).2
  have positive : ∀ p ∈ missing a, circuitFun 26 C (τ p) = true := by
    intro p hp
    exact pos _ _ (edgeFor_ok a p (Finset.mem_filter.mp hp).2).1
  have h := or_false_sensitivity_bound C (missing a) (row a) τ one legal
    (by rw [missing_card]; omega) (neg a) positive
  simpa only [missing_card, Nat.reduceSub] using h

lemma dirty_or_bound (C : Circuit) (legal : Monotone2 C)
    (pos : ∀ p l : Fin 13, incidence p l → circuitFun 26 C (pairInput p l) = true)
    (neg : ∀ a : Fin 25, circuitFun 26 C (row a) = false)
    (small : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ≤ 19) :
    dirtyOrCount (n := 26) C ≤ 2 :=
  dirty_or_bound_of_triple_cover C row legal
    (eighteen_false_at_pair_row C legal pos neg) small triple_cover

end PEqualNP.Outside.L_meta_1896.DirtyOr

namespace PEqualNP.Outside.L_meta_1896.DirtyOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Routes
open PEqualNP.Outside.L_meta_1896.Sensitivity

lemma two_singletons_or_below {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (u v : Fin n) (hne : u ≠ v) :
    ∀ w : ℕ, val C.gates w (fun _ : Fin n => false) = false →
      val C.gates w (singletonInput u) = true →
      val C.gates w (singletonInput v) = true →
      ∃ j : Fin C.gates.length, n + j.val ≤ w ∧ (C.gates.get j).op = GateOp.or ∧
        gateValue C (singletonInput u) j = true ∧ gateValue C (singletonInput v) j = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hc hu hv
    by_cases hwn : w < n
    · rw [val_input C.gates _ w hwn] at hu hv
      have hwu : (⟨w, hwn⟩ : Fin n) = u := by simpa [singletonInput] using hu
      have hwv : (⟨w, hwn⟩ : Fin n) = v := by simpa [singletonInput] using hv
      exact False.elim (hne (hwu.symm.trans hwv))
    · by_cases hbig : n + C.gates.length ≤ w
      · rw [val_big C.gates _ w hbig] at hu
        exact Bool.noConfusion hu
      · have hi : w - n < C.gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at hc hu hv
        rcases (legal C.gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · have hex : ∃ a ∈ C.gates[w - n].inputs,
              val C.gates a (fun _ : Fin n => false) = false := by
            by_contra! hn
            have htrue : val C.gates (n + (w - n)) (fun _ : Fin n => false) = true := by
              apply (val_and C.gates _ (w - n) hi ha).2
              intro a hmem
              refine ⟨((val_and C.gates _ (w - n) hi ha).1 hu a hmem).1, ?_⟩
              exact Bool.eq_true_of_not_eq_false (hn a hmem)
            rw [htrue] at hc
            exact Bool.noConfusion hc
          obtain ⟨a, hmem, hafalse⟩ := hex
          obtain ⟨habound, hau⟩ := (val_and C.gates _ (w - n) hi ha).1 hu a hmem
          have hav := ((val_and C.gates _ (w - n) hi ha).1 hv a hmem).2
          obtain ⟨j, hj, hop, hju, hjv⟩ := ih a (by omega) hafalse hau hav
          exact ⟨j, by omega, hop, hju, hjv⟩
        · exact ⟨⟨w - n, hi⟩, (show n + (w - n) ≤ w by omega), ho, hu, hv⟩

lemma or_operand_singletons_unique {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (unique : ∀ (v : Fin n) (i j : Fin C.gates.length),
      (C.gates.get i).op = GateOp.or → (C.gates.get j).op = GateOp.or →
      gateValue C (singletonInput v) i = true → gateValue C (singletonInput v) j = true → i = j)
    (j : Fin C.gates.length) (hop : (C.gates.get j).op = GateOp.or)
    (hempty : gateValue C (fun _ : Fin n => false) j = false)
    (a : ℕ) (hamem : a ∈ (C.gates.get j).inputs) (habound : a < n + j.val)
    (u v : Fin n) (hu : val C.gates a (singletonInput u) = true)
    (hv : val C.gates a (singletonInput v) = true) : u = v := by
  by_contra hne
  have hafalse : val C.gates a (fun _ : Fin n => false) = false := by
    cases h : val C.gates a (fun _ : Fin n => false) with
    | false => rfl
    | true =>
      have he : gateValue C (fun _ : Fin n => false) j = true :=
        (val_or C.gates _ j.val j.isLt hop).2 ⟨a, hamem, habound, h⟩
      rw [he] at hempty
      exact Bool.noConfusion hempty
  obtain ⟨i, hi, hio, hiu, hiv⟩ := two_singletons_or_below C legal u v hne a hafalse hu hv
  have hju : gateValue C (singletonInput u) j = true :=
    (val_or C.gates _ j.val j.isLt hop).2 ⟨a, hamem, habound, hu⟩
  have he := unique u i j hio hop hiu hju
  have hie : i.val = j.val := congrArg Fin.val he
  omega

lemma or_singleton_support_card {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (unique : ∀ (v : Fin n) (i j : Fin C.gates.length),
      (C.gates.get i).op = GateOp.or → (C.gates.get j).op = GateOp.or →
      gateValue C (singletonInput v) i = true → gateValue C (singletonInput v) j = true → i = j)
    (j : Fin C.gates.length) (hop : (C.gates.get j).op = GateOp.or)
    (hempty : gateValue C (fun _ : Fin n => false) j = false) :
    (Finset.univ.filter fun v : Fin n => gateValue C (singletonInput v) j = true).card ≤ 2 := by
  classical
  let S := Finset.univ.filter fun v : Fin n => gateValue C (singletonInput v) j = true
  have hw : ∀ v ∈ S, ∃ a ∈ (C.gates.get j).inputs,
      a < n + j.val ∧ val C.gates a (singletonInput v) = true := by
    intro v hv
    exact (val_or C.gates _ j.val j.isLt hop).1 (Finset.mem_filter.mp hv).2
  choose f hf using hw
  let f' : Fin n → ℕ := fun v => if hv : v ∈ S then f v hv else 0
  have hmap : Set.MapsTo f' (S : Set (Fin n)) (C.gates.get j).inputs.toFinset := by
    intro v hv
    change v ∈ S at hv
    simp only [Finset.mem_coe, List.mem_toFinset]
    simpa [f', hv] using (hf v hv).1
  have hinj : (S : Set (Fin n)).InjOn f' := by
    intro u hu v hv he
    change u ∈ S at hu
    change v ∈ S at hv
    have hue := hf u hu
    have hve := hf v hv
    simp only [f', dif_pos hu, dif_pos hv] at he
    apply or_operand_singletons_unique C legal unique j hop hempty (f u hu)
      hue.1 hue.2.1 u v hue.2.2
    rw [he]
    exact hve.2.2
  have hc := Finset.card_le_card_of_injOn f' hmap hinj
  have hlen := (legal (C.gates.get j) (List.get_mem C.gates j)).2
  exact hc.trans ((List.toFinset_card_le _).trans hlen)

end PEqualNP.Outside.L_meta_1896.DirtyOr

namespace PEqualNP.Outside.L_meta_1896.DirtyOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Routes
open PEqualNP.Outside.L_meta_1896.Sensitivity
open PEqualNP.Outside.L_meta_1896.FourRowsSensitivity
open PEqualNP.Outside.L_meta_1896_aux.PairRows

lemma unique_at_singleton (C : Circuit) (legal : Monotone2 C)
    (pos : ∀ p l : Fin 13, incidence p l → circuitFun 26 C (pairInput p l) = true)
    (neg : ∀ a : Fin 25, circuitFun 26 C (row a) = false)
    (small : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ≤ 19)
    (v : Fin 26) (i j : Fin C.gates.length)
    (hi : (C.gates.get i).op = GateOp.or) (hj : (C.gates.get j).op = GateOp.or)
    (hvi : gateValue C (singletonInput v) i = true)
    (hvj : gateValue C (singletonInput v) j = true) : i = j := by
  obtain ⟨a, ha⟩ := rows_cover v
  have sub : ∀ w, singletonInput v w = true → row a w = true := by
    intro w hw
    have he : w = v := by simpa [singletonInput] using hw
    exact he ▸ ha
  have hri : gateValue C (row a) i = true :=
    val_mono C.gates legal (singletonInput v) (row a) sub (26 + i.val) hvi
  have hrj : gateValue C (row a) j = true :=
    val_mono C.gates legal (singletonInput v) (row a) sub (26 + j.val) hvj
  exact at_most_one_true C (row a) 18 (eighteen_false_at_pair_row C legal pos neg a)
    small i j hi hj hri hrj

noncomputable def badCoords {n : ℕ} (C : Circuit) : Finset (Fin n) := by
  classical
  exact (Finset.univ.filter fun j : Fin C.gates.length =>
    (C.gates.get j).op = GateOp.or ∧ gateValue C (fun _ : Fin n => false) j = false ∧
      ∃ v : Fin n, gateValue C (singletonInput v) j = true).biUnion
    (fun j => Finset.univ.filter fun v : Fin n => gateValue C (singletonInput v) j = true)

lemma singleton_mem_badCoords {n : ℕ} (C : Circuit) (j : Fin C.gates.length)
    (hop : (C.gates.get j).op = GateOp.or)
    (hempty : gateValue C (fun _ : Fin n => false) j = false)
    (v : Fin n) (hv : gateValue C (singletonInput v) j = true) :
    v ∈ badCoords (n := n) C := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨j, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hop, hempty, v, hv⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩

lemma badCoords_card (C : Circuit) (legal : Monotone2 C)
    (pos : ∀ p l : Fin 13, incidence p l → circuitFun 26 C (pairInput p l) = true)
    (neg : ∀ a : Fin 25, circuitFun 26 C (row a) = false)
    (small : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ≤ 19) :
    (badCoords (n := 26) C).card ≤ 4 := by
  classical
  let D : Finset (Fin C.gates.length) := Finset.univ.filter fun j =>
    (C.gates.get j).op = GateOp.or ∧ gateValue C (fun _ : Fin 26 => false) j = false ∧
      ∃ v : Fin 26, gateValue C (singletonInput v) j = true
  have hd : D.card ≤ dirtyOrCount (n := 26) C := by
    simp only [dirtyOrCount, Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    apply Finset.card_le_card
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1, h.2.2⟩
  have hd2 : D.card ≤ 2 := hd.trans (dirty_or_bound C legal pos neg small)
  have hs : ∀ j ∈ D,
      (Finset.univ.filter fun v : Fin 26 => gateValue C (singletonInput v) j = true).card ≤ 2 := by
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    exact or_singleton_support_card C legal (unique_at_singleton C legal pos neg small)
      j h.1 h.2.1
  change (D.biUnion (fun j => Finset.univ.filter fun v : Fin 26 =>
    gateValue C (singletonInput v) j = true)).card ≤ 4
  calc
    _ ≤ ∑ j ∈ D, (Finset.univ.filter fun v : Fin 26 =>
        gateValue C (singletonInput v) j = true).card := Finset.card_biUnion_le
    _ ≤ ∑ j ∈ D, 2 := Finset.sum_le_sum hs
    _ = D.card * 2 := by simp
    _ ≤ 4 := by omega

end PEqualNP.Outside.L_meta_1896.DirtyOr

namespace PEqualNP.Outside.L_meta_1896.DirtyOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Routes
open PEqualNP.Outside.L_meta_1896.Sensitivity
open PEqualNP.Outside.L_meta_1896.FourRowsSensitivity

noncomputable def freshCoords {n : ℕ} (C : Circuit) (j : Fin C.gates.length) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => (C.gates.get j).op = GateOp.or ∧
    gateValue C (fun _ : Fin n => false) j = false ∧
    gateValue C (singletonInput v) j = true ∧
    ∀ i : Fin C.gates.length, i.val < j.val → (C.gates.get i).op = GateOp.or →
      gateValue C (fun _ : Fin n => false) i = false → gateValue C (singletonInput v) i = false

lemma two_singletons_nonconstant_or_below {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (u v : Fin n) (hne : u ≠ v) :
    ∀ w : ℕ, val C.gates w (fun _ : Fin n => false) = false →
      val C.gates w (singletonInput u) = true →
      val C.gates w (singletonInput v) = true →
      ∃ j : Fin C.gates.length, n + j.val ≤ w ∧ (C.gates.get j).op = GateOp.or ∧
        gateValue C (fun _ : Fin n => false) j = false ∧
        gateValue C (singletonInput u) j = true ∧ gateValue C (singletonInput v) j = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hc hu hv
    by_cases hwn : w < n
    · rw [val_input C.gates _ w hwn] at hu hv
      have hwu : (⟨w, hwn⟩ : Fin n) = u := by simpa [singletonInput] using hu
      have hwv : (⟨w, hwn⟩ : Fin n) = v := by simpa [singletonInput] using hv
      exact False.elim (hne (hwu.symm.trans hwv))
    · by_cases hbig : n + C.gates.length ≤ w
      · rw [val_big C.gates _ w hbig] at hu
        exact Bool.noConfusion hu
      · have hi : w - n < C.gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at hc hu hv
        rcases (legal C.gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · have hex : ∃ a ∈ C.gates[w - n].inputs,
              val C.gates a (fun _ : Fin n => false) = false := by
            by_contra! hn
            have htrue : val C.gates (n + (w - n)) (fun _ : Fin n => false) = true := by
              apply (val_and C.gates _ (w - n) hi ha).2
              intro a hmem
              refine ⟨((val_and C.gates _ (w - n) hi ha).1 hu a hmem).1, ?_⟩
              exact Bool.eq_true_of_not_eq_false (hn a hmem)
            rw [htrue] at hc
            exact Bool.noConfusion hc
          obtain ⟨a, hmem, hafalse⟩ := hex
          obtain ⟨habound, hau⟩ := (val_and C.gates _ (w - n) hi ha).1 hu a hmem
          have hav := ((val_and C.gates _ (w - n) hi ha).1 hv a hmem).2
          obtain ⟨j, hj, hop, hjz, hju, hjv⟩ := ih a (by omega) hafalse hau hav
          exact ⟨j, by omega, hop, hjz, hju, hjv⟩
        · exact ⟨⟨w - n, hi⟩, (show n + (w - n) ≤ w by omega), ho, hc, hu, hv⟩

lemma fresh_operand_unique {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (j : Fin C.gates.length) (a : ℕ) (hamem : a ∈ (C.gates.get j).inputs)
    (habound : a < n + j.val) (u v : Fin n)
    (huf : u ∈ freshCoords C j) (hvf : v ∈ freshCoords C j)
    (hu : val C.gates a (singletonInput u) = true)
    (hv : val C.gates a (singletonInput v) = true) : u = v := by
  classical
  have huf := (Finset.mem_filter.mp huf).2
  have hvf := (Finset.mem_filter.mp hvf).2
  by_contra hne
  have hafalse : val C.gates a (fun _ : Fin n => false) = false := by
    cases h : val C.gates a (fun _ : Fin n => false) with
    | false => rfl
    | true =>
      have he : gateValue C (fun _ : Fin n => false) j = true :=
        (val_or C.gates _ j.val j.isLt huf.1).2 ⟨a, hamem, habound, h⟩
      have hf := huf.2.1
      rw [he] at hf
      exact Bool.noConfusion hf
  obtain ⟨i, hi, hio, hiz, hiu, hiv⟩ :=
    two_singletons_nonconstant_or_below C legal u v hne a hafalse hu hv
  have hif := huf.2.2.2 i (by omega) hio hiz
  rw [hiu] at hif
  exact Bool.noConfusion hif

lemma freshCoords_card {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (j : Fin C.gates.length) : (freshCoords (n := n) C j).card ≤ 2 := by
  classical
  let S := freshCoords (n := n) C j
  by_cases hs : S.Nonempty
  · obtain ⟨v, hv⟩ := hs
    have hop := (Finset.mem_filter.mp hv).2.1
    have hw : ∀ v ∈ S, ∃ a ∈ (C.gates.get j).inputs,
        a < n + j.val ∧ val C.gates a (singletonInput v) = true := by
      intro v hv
      exact (val_or C.gates _ j.val j.isLt hop).1 (Finset.mem_filter.mp hv).2.2.2.1
    choose f hf using hw
    let f' : Fin n → ℕ := fun v => if hv : v ∈ S then f v hv else 0
    have hmap : Set.MapsTo f' (S : Set (Fin n)) (C.gates.get j).inputs.toFinset := by
      intro v hv
      change v ∈ S at hv
      simp only [Finset.mem_coe, List.mem_toFinset]
      simpa [f', hv] using (hf v hv).1
    have hinj : (S : Set (Fin n)).InjOn f' := by
      intro u hu v hv he
      change u ∈ S at hu
      change v ∈ S at hv
      have hue := hf u hu
      have hve := hf v hv
      simp only [f', dite_eq_left hu, dite_eq_left hv] at he
      apply fresh_operand_unique C legal j (f u hu) hue.1 hue.2.1 u v hu hv hue.2.2
      rw [he]
      exact hve.2.2
    have hc := Finset.card_le_card_of_injOn f' hmap hinj
    have hlen := (legal (C.gates.get j) (List.get_mem C.gates j)).2
    exact hc.trans ((List.toFinset_card_le _).trans hlen)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change S.card ≤ 2
    rw [he]
    simp

lemma freshCoords_disjoint {n : ℕ} (C : Circuit) (i j : Fin C.gates.length) (hne : i ≠ j) :
    Disjoint (freshCoords (n := n) C i) (freshCoords C j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hi hj
  have hi := (Finset.mem_filter.mp hi).2
  have hj := (Finset.mem_filter.mp hj).2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hf := hj.2.2.2 i hlt hi.1 hi.2.1
    rw [hi.2.2.1] at hf
    exact Bool.noConfusion hf
  · have hf := hi.2.2.2 j hgt hj.1 hj.2.1
    rw [hj.2.2.1] at hf
    exact Bool.noConfusion hf

lemma freshCoords_subset_badCoords {n : ℕ} (C : Circuit) (j : Fin C.gates.length) :
    freshCoords (n := n) C j ⊆ badCoords C := by
  classical
  intro v hv
  have h := (Finset.mem_filter.mp hv).2
  exact singleton_mem_badCoords C j h.1 h.2.1 v h.2.2.1

lemma badCoords_mem_iff {n : ℕ} (C : Circuit) (v : Fin n) :
    v ∈ badCoords C ↔ ∃ j : Fin C.gates.length, (C.gates.get j).op = GateOp.or ∧
      gateValue C (fun _ : Fin n => false) j = false ∧ gateValue C (singletonInput v) j = true := by
  classical
  constructor
  · intro hv
    obtain ⟨j, hj, hjv⟩ := Finset.mem_biUnion.mp hv
    have hj := (Finset.mem_filter.mp hj).2
    exact ⟨j, hj.1, hj.2.1, (Finset.mem_filter.mp hjv).2⟩
  · rintro ⟨j, hop, hz, hv⟩
    exact singleton_mem_badCoords C j hop hz v hv

lemma badCoords_covered {n : ℕ} (C : Circuit) (v : Fin n) (hv : v ∈ badCoords C) :
    ∃ j : Fin C.gates.length, v ∈ freshCoords C j := by
  classical
  let S : Finset (Fin C.gates.length) := Finset.univ.filter fun j =>
    (C.gates.get j).op = GateOp.or ∧ gateValue C (fun _ : Fin n => false) j = false ∧
      gateValue C (singletonInput v) j = true
  obtain ⟨i, hi⟩ := (badCoords_mem_iff C v).mp hv
  have hn : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let j := S.min' hn
  have hj : j ∈ S := Finset.min'_mem S hn
  have h := (Finset.mem_filter.mp hj).2
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1, h.2.1, h.2.2, ?_⟩⟩
  intro k hk hko hkz
  cases hkv : gateValue C (singletonInput v) k with
  | false => rfl
  | true =>
    have hkm : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hko, hkz, hkv⟩
    have hjk : j ≤ k := Finset.min'_le S k hkm
    have : j.val ≤ k.val := hjk
    omega

end PEqualNP.Outside.L_meta_1896.DirtyOr

namespace PEqualNP.Outside.L_meta_1896.DirtyOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Routes
open PEqualNP.Outside.L_meta_1896.Sensitivity
open PEqualNP.Outside.L_meta_1896.FourRowsSensitivity

noncomputable def freshHits {n : ℕ} (C : Circuit) (c : Fin n → Bool) :
    Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun j => ∃ v ∈ freshCoords C j, c v = true

lemma fresh_hit_true {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (c : Fin n → Bool) (j : Fin C.gates.length) (hj : j ∈ freshHits C c) :
    (C.gates.get j).op = GateOp.or ∧ gateValue C c j = true := by
  classical
  obtain ⟨v, hv, hcv⟩ := (Finset.mem_filter.mp hj).2
  have hf := (Finset.mem_filter.mp hv).2
  refine ⟨hf.1, ?_⟩
  apply val_mono C.gates legal (singletonInput v) c _ (n + j.val) hf.2.2.1
  intro w hw
  have he : w = v := by simpa [singletonInput] using hw
  exact he ▸ hcv

lemma freshHits_card {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (c : Fin n → Bool) (k q : ℕ) (hfalse : k ≤ falseOrCount C c)
    (htotal : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ≤ q) :
    (freshHits C c).card + k ≤ q := by
  classical
  let F : Finset (Fin C.gates.length) := Finset.univ.filter fun j =>
    (C.gates.get j).op = GateOp.or ∧ gateValue C c j = false
  let B : Finset (Fin C.gates.length) := Finset.univ.filter fun j =>
    (C.gates.get j).op = GateOp.or
  have hF : F.card = falseOrCount C c := by
    simp [F, falseOrCount, Set.ncard_eq_toFinset_card']
  have hB : B.card ≤ q := by
    simpa [B, Set.ncard_eq_toFinset_card'] using htotal
  have hd : Disjoint F (freshHits C c) := by
    apply Finset.disjoint_left.mpr
    intro j hjF hjH
    have hf := (Finset.mem_filter.mp hjF).2.2
    have ht := (fresh_hit_true C legal c j hjH).2
    rw [ht] at hf
    exact Bool.noConfusion hf
  have hs : F ∪ freshHits C c ⊆ B := by
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hj with hf | hh
    · exact (Finset.mem_filter.mp hf).2.1
    · exact (fresh_hit_true C legal c j hh).1
  have hc := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd] at hc
  omega

noncomputable def freshBlocks {n : ℕ} (C : Circuit) : Finset (Finset (Fin n)) := by
  classical
  exact (Finset.univ.filter fun j : Fin C.gates.length =>
    (freshCoords (n := n) C j).Nonempty).image (fun j => freshCoords C j)

lemma freshBlocks_nonempty {n : ℕ} (C : Circuit) (B : Finset (Fin n))
    (hB : B ∈ freshBlocks C) : B.Nonempty := by
  classical
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
  exact (Finset.mem_filter.mp hj).2

lemma freshBlocks_card {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (B : Finset (Fin n)) (hB : B ∈ freshBlocks C) : B.card ≤ 2 := by
  classical
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
  exact freshCoords_card C legal j

lemma freshBlocks_disjoint {n : ℕ} (C : Circuit) :
    (freshBlocks (n := n) C : Set (Finset (Fin n))).PairwiseDisjoint id := by
  classical
  intro B hB D hD hne
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hD
  apply freshCoords_disjoint C i j
  intro he
  exact hne (congrArg (fun k => freshCoords (n := n) C k) he)

lemma freshBlocks_cover {n : ℕ} (C : Circuit) :
    (freshBlocks (n := n) C).biUnion id = badCoords C := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨B, hB, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
    exact freshCoords_subset_badCoords C j hv
  · intro hv
    obtain ⟨j, hj⟩ := badCoords_covered C v hv
    apply Finset.mem_biUnion.mpr
    refine ⟨freshCoords C j, ?_, hj⟩
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨v, hj⟩⟩, rfl⟩

lemma freshBlocks_capacity {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (c : Fin n → Bool) (k q : ℕ) (hfalse : k ≤ falseOrCount C c)
    (htotal : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ≤ q) :
    ((freshBlocks C).filter fun B => ∃ v ∈ B, c v = true).card + k ≤ q := by
  classical
  have hs : (freshBlocks C).filter (fun B => ∃ v ∈ B, c v = true) ⊆
      (freshHits C c).image (fun j => freshCoords C j) := by
    intro B hB
    obtain ⟨hB, hv⟩ := Finset.mem_filter.mp hB
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  have hc := (Finset.card_le_card hs).trans Finset.card_image_le
  have hb := freshHits_card C legal c k q hfalse htotal
  omega

lemma freshBlocks_capacity_twenty (C : Circuit) (legal : Monotone2 C)
    (pos : ∀ p l : Fin 13, PEqualNP.Outside.L_meta_1896_aux.PairRows.incidence p l →
      circuitFun 26 C (PEqualNP.Outside.L_meta_1896_aux.PairRows.pairInput p l) = true)
    (neg : ∀ a : Fin 25,
      circuitFun 26 C (PEqualNP.Outside.L_meta_1896_aux.PairRows.row a) = false)
    (small : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ≤ 20)
    (a : Fin 25) :
    ((freshBlocks C).filter fun B => ∃ v ∈ B,
      PEqualNP.Outside.L_meta_1896_aux.PairRows.row a v = true).card ≤ 2 := by
  have h := freshBlocks_capacity C legal (PEqualNP.Outside.L_meta_1896_aux.PairRows.row a)
    18 20 (eighteen_false_at_pair_row C legal pos neg a) small
  omega

end PEqualNP.Outside.L_meta_1896.DirtyOr

namespace PEqualNP.Outside.L_meta_1896.DirtyOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Routes
open PEqualNP.Outside.L_meta_1896.Sensitivity

lemma singleton_disjoint_or_below {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (v : Fin n) (x : Fin n → Bool) (hx : x v = false) :
    ∀ w : ℕ, val C.gates w (fun _ : Fin n => false) = false →
      val C.gates w (singletonInput v) = true → val C.gates w x = true →
      ∃ j : Fin C.gates.length, n + j.val ≤ w ∧ (C.gates.get j).op = GateOp.or ∧
        gateValue C (fun _ : Fin n => false) j = false ∧
        gateValue C (singletonInput v) j = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hc hv hxw
    by_cases hwn : w < n
    · rw [val_input C.gates _ w hwn] at hv hxw
      have hwv : (⟨w, hwn⟩ : Fin n) = v := by simpa [singletonInput] using hv
      rw [hwv, hx] at hxw
      exact Bool.noConfusion hxw
    · by_cases hbig : n + C.gates.length ≤ w
      · rw [val_big C.gates _ w hbig] at hv
        exact Bool.noConfusion hv
      · have hi : w - n < C.gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at hc hv hxw
        rcases (legal C.gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · have hex : ∃ a ∈ C.gates[w - n].inputs,
              val C.gates a (fun _ : Fin n => false) = false := by
            by_contra! hn
            have htrue : val C.gates (n + (w - n)) (fun _ : Fin n => false) = true := by
              apply (val_and C.gates _ (w - n) hi ha).2
              intro a hmem
              refine ⟨((val_and C.gates _ (w - n) hi ha).1 hv a hmem).1, ?_⟩
              exact Bool.eq_true_of_not_eq_false (hn a hmem)
            rw [htrue] at hc
            exact Bool.noConfusion hc
          obtain ⟨a, hmem, hafalse⟩ := hex
          obtain ⟨habound, hav⟩ := (val_and C.gates _ (w - n) hi ha).1 hv a hmem
          have hax := ((val_and C.gates _ (w - n) hi ha).1 hxw a hmem).2
          obtain ⟨j, hj, hop, hjz, hjv⟩ := ih a (by omega) hafalse hav hax
          exact ⟨j, by omega, hop, hjz, hjv⟩
        · exact ⟨⟨w - n, hi⟩, (show n + (w - n) ≤ w by omega), ho, hc, hv⟩

lemma fresh_operand_dead {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (j : Fin C.gates.length) (v : Fin n) (hv : v ∈ freshCoords C j)
    (a : ℕ) (hamem : a ∈ (C.gates.get j).inputs) (habound : a < n + j.val)
    (hav : val C.gates a (singletonInput v) = true)
    (x : Fin n → Bool) (hx : x v = false) : val C.gates a x = false := by
  classical
  have hf := (Finset.mem_filter.mp hv).2
  have haz : val C.gates a (fun _ : Fin n => false) = false := by
    cases h : val C.gates a (fun _ : Fin n => false) with
    | false => rfl
    | true =>
      have he : gateValue C (fun _ : Fin n => false) j = true :=
        (val_or C.gates _ j.val j.isLt hf.1).2 ⟨a, hamem, habound, h⟩
      have hz := hf.2.1
      rw [he] at hz
      exact Bool.noConfusion hz
  cases hax : val C.gates a x with
  | false => rfl
  | true =>
    obtain ⟨i, hi, hio, hiz, hiv⟩ := singleton_disjoint_or_below C legal v x hx a haz hav hax
    have hif := hf.2.2.2 i (by omega) hio hiz
    rw [hiv] at hif
    exact Bool.noConfusion hif

lemma fresh_or_has_dead_operand {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (j : Fin C.gates.length) (v : Fin n) (hv : v ∈ freshCoords C j) :
    ∃ a ∈ (C.gates.get j).inputs, a < n + j.val ∧
      ∀ x : Fin n → Bool, x v = false → val C.gates a x = false := by
  classical
  have hf := (Finset.mem_filter.mp hv).2
  obtain ⟨a, ha, habound, hav⟩ := (val_or C.gates _ j.val j.isLt hf.1).1 hf.2.2.1
  exact ⟨a, ha, habound, fresh_operand_dead C legal j v hv a ha habound hav⟩

end PEqualNP.Outside.L_meta_1896.DirtyOr

namespace PEqualNP.Outside.L_meta_1896.DirtyOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Sensitivity
open PEqualNP.Outside.L_meta_1896_aux.PairRows

lemma eighteen_false_of_sensitive_row (C : Circuit) (c : Fin 26 → Bool)
    (e : Fin 26 → Fin 13 × Fin 13) (legal : Monotone2 C)
    (pos : ∀ p l : Fin 13, incidence p l → circuitFun 26 C (pairInput p l) = true)
    (hc : circuitFun 26 C c = false)
    (hcard : (Finset.univ.filter fun v : Fin 26 => c v = false).card = 19)
    (hedge : ∀ v : Fin 26, c v = false → incidence (e v).1 (e v).2 ∧
      ∀ w : Fin 26, c w = false → pairInput (e v).1 (e v).2 w = true → w = v) :
    18 ≤ falseOrCount C c := by
  let M := Finset.univ.filter fun v : Fin 26 => c v = false
  let τ : Fin 26 → Fin 26 → Bool := fun v => pairInput (e v).1 (e v).2
  have one : ∀ p ∈ M, ∀ v, c v = false → τ p v = true → v = p := by
    intro p hp
    exact (hedge p (Finset.mem_filter.mp hp).2).2
  have positive : ∀ p ∈ M, circuitFun 26 C (τ p) = true := by
    intro p hp
    exact pos _ _ (hedge p (Finset.mem_filter.mp hp).2).1
  have hM : M.card = 19 := hcard
  have h := or_false_sensitivity_bound C M c τ one legal (by omega) hc positive
  omega

lemma freshBlocks_capacity_sensitive_row (C : Circuit) (c : Fin 26 → Bool)
    (e : Fin 26 → Fin 13 × Fin 13) (legal : Monotone2 C)
    (pos : ∀ p l : Fin 13, incidence p l → circuitFun 26 C (pairInput p l) = true)
    (hc : circuitFun 26 C c = false)
    (hcard : (Finset.univ.filter fun v : Fin 26 => c v = false).card = 19)
    (hedge : ∀ v : Fin 26, c v = false → incidence (e v).1 (e v).2 ∧
      ∀ w : Fin 26, c w = false → pairInput (e v).1 (e v).2 w = true → w = v)
    (q : ℕ)
    (small : {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard ≤ q) :
    ((freshBlocks C).filter fun B => ∃ v ∈ B, c v = true).card + 18 ≤ q :=
  freshBlocks_capacity C legal c 18 q
    (eighteen_false_of_sensitive_row C c e legal pos hc hcard hedge) small

end PEqualNP.Outside.L_meta_1896.DirtyOr


-- The counting argument below reuses willakone’s checked proof of L-meta-2059 (PR 4283).

namespace PEqualNP.Outside.L_meta_1896_aux.CleanOrSkip

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

lemma iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

lemma val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

lemma val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

lemma val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

lemma val_mono (gates : List Gate) {n : ℕ}
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

lemma zero_false {n : ℕ} (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (x : Fin n → Bool) (hf : val gates w x = false) :
    val gates w (fun _ : Fin n => false) = false := by
  cases hz : val gates w (fun _ : Fin n => false) with
  | false => rfl
  | true =>
    have ht := val_mono gates legal (fun _ : Fin n => false) x (by simp) w hz
    rw [hf] at ht
    cases ht

def Cl {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (i : Fin gates.length) (X : Finset (Fin m)) : Prop :=
  (gates.get i).op = GateOp.or →
    val gates (n + i.val) (fun _ : Fin n => false) = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ M, ∀ y' ∈ M,
      (val gates a (τ y) = true ∨ val gates b (τ y) = true) →
      (val gates a (τ y') = true ∨ val gates b (τ y') = true) → (y ∈ X ↔ y' ∈ X)

def Con {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) (X : Finset (Fin m)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < k → Cl gates M τ i X

def Mrg {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧
    val gates (n + g.val) (fun _ : Fin n => false) = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
      val gates w1 (τ r) = true ∧ val gates w2 (τ r') = true ∧
      ∃ X : Finset (Fin m), r ∈ X ∧ r' ∉ X ∧ Con gates M τ (g : ℕ) X

def meet {n m : ℕ} (τ : Fin m → Fin n → Bool) (p q : Fin m) : Fin n → Bool :=
  fun i => τ p i && τ q i

lemma single {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) (X : Finset (Fin m)) (hX : Con gates M τ k X) :
    ∀ w, w < n + k → ∀ y ∈ M, ∀ y' ∈ M,
      val gates w (meet τ y y') = false →
      val gates w (τ y) = true → val gates w (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw y hy y' hy' hwc h1 h2
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at hwc h1 h2
      simp [meet, h1, h2] at hwc
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      rw [← he] at hwc h1 h2
      have hinp : ∀ a ∈ gates[w - n].inputs, a < n + (w - n) := hin ⟨w - n, hi⟩
      have hlen := (legal gates[w - n] (List.getElem_mem hi)).2
      rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
      · have hex : ∃ j ∈ gates[w - n].inputs, val gates j (meet τ y y') = false := by
          by_contra hne
          have hall : val gates (n + (w - n)) (meet τ y y') = true := by
            apply (val_and gates _ (w - n) hi ha).2
            intro j hj
            refine ⟨hinp j hj, ?_⟩
            cases hv : val gates j (meet τ y y') with
            | true => rfl
            | false => exact absurd ⟨j, hj, hv⟩ hne
          rw [hall] at hwc
          exact Bool.noConfusion hwc
        obtain ⟨j, hj, hjc⟩ := hex
        exact ih j (by have := hinp j hj; omega) (by have := hinp j hj; omega)
          y hy y' hy' hjc
          ((val_and gates (τ y) (w - n) hi ha).1 h1 j hj).2
          ((val_and gates (τ y') (w - n) hi ha).1 h2 j hj).2
      · have hall : ∀ j ∈ gates[w - n].inputs, val gates j (meet τ y y') = false := by
          intro j hj
          cases hv : val gates j (meet τ y y') with
          | false => rfl
          | true =>
            have ht : val gates (n + (w - n)) (meet τ y y') = true :=
              (val_or gates _ (w - n) hi ho).2 ⟨j, hj, hinp j hj, hv⟩
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
          exact ih a (by omega) (by omega) y hy y' hy'
            (hall a (by rw [hinpe]; simp)) hv1 hv2
        · rw [hinpe] at hj1 hj2
          have d1 : val gates a (τ y) = true ∨ val gates b (τ y) = true := by
            rcases List.mem_pair.1 hj1 with e | e
            · subst e; exact Or.inl hv1
            · subst e; exact Or.inr hv1
          have d2 : val gates a (τ y') = true ∨ val gates b (τ y') = true := by
            rcases List.mem_pair.1 hj2 with e | e
            · subst e; exact Or.inl hv2
            · subst e; exact Or.inr hv2
          exact hX ⟨w - n, hi⟩ (by simp; omega) ho
            (zero_false gates legal _ _ hwc) a b hinpe y hy y' hy' d1 d2
        · rw [hinpe] at hlen
          simp at hlen

lemma con_succ {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) (hk : k < gates.length) (X : Finset (Fin m)) :
    Con gates M τ (k + 1) X ↔ Con gates M τ k X ∧ Cl gates M τ ⟨k, hk⟩ X := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases e : (i : ℕ) = k
    · have e' : i = ⟨k, hk⟩ := Fin.ext e
      rw [e']
      exact h2
    · exact h1 i (by omega)

lemma con_compl {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) (X : Finset (Fin m)) (h : Con gates M τ k X) :
    Con gates M τ k Xᶜ := by
  intro i hi ho hz a b hab y hy y' hy' h1 h2
  rw [Finset.mem_compl, Finset.mem_compl, not_iff_not]
  exact h i hi ho hz a b hab y hy y' hy' h1 h2

lemma con_symm {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin m)) (hX : Con gates M τ k X)
    (hY : Con gates M τ k Y) : Con gates M τ k (symmDiff X Y) := by
  intro i hi ho hz a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hz a b hab y hy y' hy' h1 h2
  have e2 := hY i hi ho hz a b hab y hy y' hy' h1 h2
  rw [Finset.mem_symmDiff, Finset.mem_symmDiff, e1, e2]

lemma con_inter {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) (X : Finset (Fin m)) (hX : Con gates M τ k X) :
    Con gates M τ k (X ∩ M) := by
  intro i hi ho hz a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hz a b hab y hy y' hy' h1 h2
  rw [Finset.mem_inter, Finset.mem_inter, e1]
  exact ⟨fun h => ⟨h.1, hy'⟩, fun h => ⟨h.1, hy⟩⟩

lemma cl_of {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (g : Fin gates.length) (X : Finset (Fin m)) (a b : ℕ)
    (hab : (gates.get g).inputs = [a, b])
    (sA : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates a (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (sB : ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (Q : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X)) : Cl gates M τ g X := by
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

lemma symm_flip {m : ℕ} (X Y : Finset (Fin m)) (r r' : Fin m) (hr : r ∈ Y) (hr' : r' ∉ Y) :
    (r ∈ symmDiff X Y ↔ r' ∈ symmDiff X Y) ↔ ¬ (r ∈ X ↔ r' ∈ X) := by
  by_cases h1 : r ∈ X <;> by_cases h2 : r' ∈ X <;> simp [Finset.mem_symmDiff, h1, h2, hr, hr']

open Classical in
noncomputable def P {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) : Finset (Finset (Fin m)) :=
  M.powerset.filter (fun X => Con gates M τ k X)

open Classical in
lemma symm_mem {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin m)) (hX : X ∈ P gates M τ k)
    (hY : Y ⊆ M) (hYc : Con gates M τ k Y) : symmDiff X Y ∈ P gates M τ k := by
  rw [P, Finset.mem_filter, Finset.mem_powerset] at hX ⊢
  refine ⟨?_, con_symm gates M τ k X Y hX.2 hYc⟩
  intro v hv
  rw [Finset.mem_symmDiff] at hv
  rcases hv with hv | hv
  · exact hX.1 hv.1
  · exact hY hv.1


open Classical in
lemma step {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (clean : ∀ i : Fin gates.length, (gates.get i).op = GateOp.or →
      val gates (n + i.val) (fun _ : Fin n => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q → val gates (n + i.val) (meet τ p q) = false)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (g : Fin gates.length) :
    (P gates M τ ((g : ℕ) + 1)).card * (if Mrg gates M τ g then 2 else 1)
      = (P gates M τ (g : ℕ)).card := by
  by_cases hal : (gates.get g).op = GateOp.or ∧
      val gates (n + g.val) (fun _ : Fin n => false) = false ∧
      ∃ a b : ℕ, (gates.get g).inputs = [a, b]
  swap
  · have hnm : ¬ Mrg gates M τ g := by
      rintro ⟨h1, hz, w1, w2, h3, _⟩
      exact hal ⟨h1, hz, w1, w2, h3⟩
    have hP : P gates M τ ((g : ℕ) + 1) = P gates M τ (g : ℕ) := by
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro ho hz a b hab
        exact absurd ⟨ho, hz, a, b, hab⟩ hal
    rw [hP, ite_eq_right hnm, Nat.mul_one]
  · obtain ⟨ho, hz, a, b, hab⟩ := hal
    have hma : a ∈ (gates.get g).inputs := by rw [hab]; simp
    have hmb : b ∈ (gates.get g).inputs := by rw [hab]; simp
    have ha : a < n + (g : ℕ) := hin g a hma
    have hb : b < n + (g : ℕ) := hin g b hmb
    have hac (p : Fin m) (hp : p ∈ M) (q : Fin m) (hq : q ∈ M) (hpq : p ≠ q) :
        val gates a (meet τ p q) = false := by
      cases hv : val gates a (meet τ p q) with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) (meet τ p q) = true :=
          (val_or gates _ g g.2 ho).2 ⟨a, hma, ha, hv⟩
        rw [clean g ho hz p hp q hq hpq] at ht
        cases ht
    have hbc (p : Fin m) (hp : p ∈ M) (q : Fin m) (hq : q ∈ M) (hpq : p ≠ q) :
        val gates b (meet τ p q) = false := by
      cases hv : val gates b (meet τ p q) with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) (meet τ p q) = true :=
          (val_or gates _ g g.2 ho).2 ⟨b, hmb, hb, hv⟩
        rw [clean g ho hz p hp q hq hpq] at ht
        cases ht
    have sA : ∀ X, Con gates M τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true →
        val gates a (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
      intro X hX y hy y' hy' h1 h2
      by_cases he : y = y'
      · simp [he]
      · exact single gates M τ legal hin g (le_of_lt g.2) X hX a ha y hy y' hy'
          (hac y hy y' hy' he) h1 h2
    have sB : ∀ X, Con gates M τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true →
        val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
      intro X hX y hy y' hy' h1 h2
      by_cases he : y = y'
      · simp [he]
      · exact single gates M τ legal hin g (le_of_lt g.2) X hX b hb y hy y' hy'
          (hbc y hy y' hy' he) h1 h2
    by_cases hm : ∃ r ∈ M, ∃ r' ∈ M, val gates a (τ r) = true ∧ val gates b (τ r') = true ∧
        ∃ X : Finset (Fin m), r ∈ X ∧ r' ∉ X ∧ Con gates M τ (g : ℕ) X
    · have hmrg : Mrg gates M τ g := ⟨ho, hz, a, b, hab, hm⟩
      obtain ⟨r, hr, r', hr', hra, hrb, X0, hrX, hr'X, hX0⟩ := hm
      rw [ite_eq_left hmrg]
      have hP : P gates M τ ((g : ℕ) + 1)
          = (P gates M τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X) := by
        unfold P
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro X _
        rw [con_succ gates M τ g g.2 X]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2 ho hz a b hab r hr r' hr' (Or.inl hra) (Or.inr hrb)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, cl_of gates M τ g X a b hab (sA X h1) (sB X h1) ?_⟩
          intro y hy y' hy' hya hyb
          exact ((sA X h1 y hy r hr hya hra).trans h2).trans (sB X h1 r' hr' y' hy' hrb hyb)
      rw [hP]
      have hsplit := Finset.card_filter_add_card_filter_not (s := P gates M τ (g : ℕ))
        (fun X => r ∈ X ↔ r' ∈ X)
      have hY0 : X0 ∩ M ⊆ M := Finset.inter_subset_right
      have hY0c := con_inter gates M τ g X0 hX0
      have hrY : r ∈ X0 ∩ M := Finset.mem_inter.2 ⟨hrX, hr⟩
      have hr'Y : r' ∉ X0 ∩ M := fun h => hr'X (Finset.mem_inter.1 h).1
      have hbij : ((P gates M τ (g : ℕ)).filter (fun X => ¬ (r ∈ X ↔ r' ∈ X))).card
          = ((P gates M τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X)).card := by
        refine Finset.card_bij' (fun X _ => symmDiff X (X0 ∩ M)) (fun X _ => symmDiff X (X0 ∩ M))
          ?_ ?_ ?_ ?_
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M τ g X _ hX.1 hY0 hY0c, ?_⟩
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).2 hX.2
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M τ g X _ hX.1 hY0 hY0c, ?_⟩
          intro hcon
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).1 hcon hX.2
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
      omega
    · have hnm : ¬ Mrg gates M τ g := by
        rintro ⟨_, _, w1, w2, h3, r, hr, r', hr', h4, h5, h6⟩
        rw [hab] at h3
        obtain ⟨e1, e2⟩ : a = w1 ∧ b = w2 := by simpa using h3
        subst e1
        subst e2
        exact hm ⟨r, hr, r', hr', h4, h5, h6⟩
      rw [ite_eq_right hnm, Nat.mul_one]
      congr 1
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, cl_of gates M τ g X a b hab (sA X h) (sB X h) ?_⟩
        intro y hy y' hy' hya hyb
        constructor
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, X, hyX, hn, h⟩
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, Xᶜ, Finset.mem_compl.2 hn,
            fun h' => Finset.mem_compl.1 h' hyX, con_compl gates M τ g X h⟩

open Classical in
lemma count {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (clean : ∀ i : Fin gates.length, (gates.get i).op = GateOp.or →
      val gates (n + i.val) (fun _ : Fin n => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q → val gates (n + i.val) (meet τ p q) = false)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) :
    (P gates M τ k).card *
      2 ^ (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M τ g then 1 else 0)
      = 2 ^ M.card := by
  induction k with
  | zero =>
    have h0 : P gates M τ 0 = M.powerset := by
      unfold P
      apply Finset.filter_true_of_mem
      intro X _ i hi
      exact absurd hi (Nat.not_lt_zero _)
    rw [h0, Finset.card_powerset]
    simp
  | succ k ih =>
    have hk' : k < gates.length := hk
    have hs : (P gates M τ (k + 1)).card * (if Mrg gates M τ ⟨k, hk'⟩ then 2 else 1)
        = (P gates M τ k).card := step gates M τ clean legal hin ⟨k, hk'⟩
    have hsum : (∑ g : Fin gates.length, if (g : ℕ) < k + 1 ∧ Mrg gates M τ g then 1 else 0)
        = (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M τ g then 1 else 0)
          + (if Mrg gates M τ ⟨k, hk'⟩ then 1 else 0) := by
      have hpt : ∀ g : Fin gates.length,
          (if (g : ℕ) < k + 1 ∧ Mrg gates M τ g then 1 else 0)
          = (if (g : ℕ) < k ∧ Mrg gates M τ g then 1 else 0)
            + (if g = ⟨k, hk'⟩ then (if Mrg gates M τ ⟨k, hk'⟩ then 1 else 0) else 0) := by
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
lemma mcount {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (clean : ∀ i : Fin gates.length, (gates.get i).op = GateOp.or →
      val gates (n + i.val) (fun _ : Fin n => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q → val gates (n + i.val) (meet τ p q) = false)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : 1 ≤ M.card) (o : ℕ) (hoc : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → val gates o (meet τ p q) = false)
    (hot : ∀ p ∈ M, val gates o (τ p) = true) :
    (∑ g : Fin gates.length, if Mrg gates M τ g then 1 else 0) = M.card - 1 := by
  have hne : M.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p0, hp0⟩ := hne
  have holt : o < n + gates.length := by
    by_contra h
    have hb := val_big gates (τ p0) o (by omega)
    rw [hot p0 hp0] at hb
    exact Bool.noConfusion hb
  have hfin : P gates M τ gates.length = {∅, M} := by
    ext X
    rw [P, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hX⟩
      have hs := single gates M τ legal hin gates.length le_rfl X hX o holt
      by_cases hex : ∃ y ∈ M, y ∈ X
      · obtain ⟨y, hy, hyX⟩ := hex
        right
        apply Finset.Subset.antisymm hsub
        intro z hz
        by_cases he : y = z
        · simpa [he] using hyX
        · exact (hs y hy z hz (hoc y hy z hz he) (hot y hy) (hot z hz)).1 hyX
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
  have hcnt := count gates M τ clean legal hin gates.length le_rfl
  have hpair : ({∅, M} : Finset (Finset (Fin m))).card = 2 := by
    apply Finset.card_pair
    intro h
    rw [← h] at hp0
    simp at hp0
  rw [hfin, hpair] at hcnt
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ Mrg gates M τ g then 1 else 0)
      = ∑ g : Fin gates.length, if Mrg gates M τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have hm1 : 2 ^ M.card = 2 * 2 ^ (M.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h8 : 2 ^ (∑ g : Fin gates.length, if Mrg gates M τ g then 1 else 0) = 2 ^ (M.card - 1) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcnt.trans hm1)
  exact Nat.pow_right_injective (le_refl 2) h8

lemma clean_or_bound {n m : ℕ} (C : Circuit) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (clean : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.or →
      circuitFun n {C with output := n + i.val} (fun _ => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
        circuitFun n {C with output := n + i.val} (meet τ p q) = false)
    (legal : Monotone2 C)
    (hin : ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < n + i.val)
    (hM : 1 ≤ M.card)
    (hc : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → circuitFun n C (meet τ p q) = false)
    (ht : ∀ p ∈ M, circuitFun n C (τ p) = true) :
    M.card - 1 ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard := by
  classical
  have h := mcount C.gates M τ clean legal hin hM C.output hc ht
  rw [← h]
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter]
  apply Finset.sum_le_sum
  intro g hg
  by_cases hm : Mrg C.gates M τ g
  · have hop : C.gates[g.val].op = GateOp.or := hm.1
    simp [hm, hop]
  · simp [hm]

end PEqualNP.Outside.L_meta_1896_aux.CleanOrSkip


namespace PEqualNP.Outside.L_meta_1896_aux.CleanOrSkip

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma clean_or_bound_excluding {n m : ℕ} (C : Circuit) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (clean : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.or →
      circuitFun n {C with output := n + i.val} (fun _ => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
        circuitFun n {C with output := n + i.val} (meet τ p q) = false)
    (legal : Monotone2 C)
    (hin : ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < n + i.val)
    (hM : 1 ≤ M.card)
    (hc : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → circuitFun n C (meet τ p q) = false)
    (ht : ∀ p ∈ M, circuitFun n C (τ p) = true)
    (E : Finset (Fin C.gates.length))
    (hE : ∀ j ∈ E, (C.gates.get j).op = GateOp.or)
    (exclude : ∀ j ∈ E, ¬Mrg C.gates M τ j) :
    M.card - 1 + E.card ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard := by
  classical
  have h := mcount C.gates M τ clean legal hin hM C.output hc ht
  have he : (∑ j : Fin C.gates.length, if j ∈ E then 1 else 0) = E.card := by simp
  rw [← h, ← he, ← Finset.sum_add_distrib]
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hm : Mrg C.gates M τ j
  · have hop : C.gates[j.val].op = GateOp.or := hm.1
    have hne : j ∉ E := fun hjE => exclude j hjE hm
    simp [hm, hne, hop]
  · by_cases hjE : j ∈ E
    · have hop : C.gates[j.val].op = GateOp.or := hE j hjE
      simp [hm, hjE, hop]
    · simp [hm, hjE]

lemma not_merge_of_dead_operand {n m : ℕ} (C : Circuit) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (j : Fin C.gates.length)
    (dead : ∀ a b, (C.gates.get j).inputs = [a, b] →
      (∀ p ∈ M, val C.gates a (τ p) = false) ∨
      (∀ p ∈ M, val C.gates b (τ p) = false)) :
    ¬Mrg C.gates M τ j := by
  rintro ⟨ho, hz, a, b, hab, p, hp, q, hq, ha, hb, _⟩
  rcases dead a b hab with h | h
  · exact Bool.noConfusion ((h p hp).symm.trans ha)
  · exact Bool.noConfusion ((h q hq).symm.trans hb)

end PEqualNP.Outside.L_meta_1896_aux.CleanOrSkip

namespace PEqualNP.Outside.L_meta_1896_aux.CleanOrSkip

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Normalize

lemma cleanGates_entry (k : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ((cleanGates k gs)[j]'(by simpa [cleanGates_length] using hj)) =
      cleanGate (k + j) (gs[j]'hj) := by
  induction gs generalizing k j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simpa [cleanGates, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (k + 1) j (by simpa using hj)

lemma not_merge_of_mem_dead {n m : ℕ} (C : Circuit) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (j : Fin C.gates.length)
    (dead : ∃ a ∈ (C.gates.get j).inputs, ∀ p ∈ M, val C.gates a (τ p) = false) :
    ¬Mrg C.gates M τ j := by
  apply not_merge_of_dead_operand C M τ j
  intro a b hab
  obtain ⟨w, hw, hd⟩ := dead
  rw [hab] at hw
  have hw' : w = a ∨ w = b := by simpa using hw
  rcases hw' with rfl | rfl
  · exact Or.inl hd
  · exact Or.inr hd

lemma clean_or_bound_excluding_general {n m : ℕ} (C : Circuit) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (clean : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.or →
      circuitFun n {C with output := n + i.val} (fun _ => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
        circuitFun n {C with output := n + i.val} (meet τ p q) = false)
    (legal : Monotone2 C) (hM : 1 ≤ M.card)
    (hc : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → circuitFun n C (meet τ p q) = false)
    (ht : ∀ p ∈ M, circuitFun n C (τ p) = true)
    (E : Finset (Fin C.gates.length))
    (hE : ∀ j ∈ E, (C.gates.get j).op = GateOp.or)
    (dead : ∀ j ∈ E, ∃ a ∈ (C.gates.get j).inputs, a < n + j.val ∧
      ∀ p ∈ M, circuitFun n {C with output := a} (τ p) = false) :
    M.card - 1 + E.card ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard := by
  classical
  let τ' : Fin m → Fin (n + 1) → Bool := fun p => Fin.cases false (τ p)
  let e : Fin (cleanCircuit n C).gates.length ≃ Fin C.gates.length :=
    finCongr (cleanGates_length n C.gates)
  let E' : Finset (Fin (cleanCircuit n C).gates.length) := E.map e.symm.toEmbedding
  have emem (i : Fin (cleanCircuit n C).gates.length) (hi : i ∈ E') : e i ∈ E := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    simpa using hj
  have hlen (i : Fin (cleanCircuit n C).gates.length) : i.val < C.gates.length := by
    simpa [cleanCircuit, cleanGates_length] using i.isLt
  have hsame (w : ℕ) (x : Fin n → Bool) : circuitFun (n + 1)
      {cleanCircuit n C with output := w + 1} (Fin.cases false x) =
      circuitFun n {C with output := w} x :=
    cleanCircuit_fun {C with output := w} x
  have eqmeet (p q : Fin m) : meet τ' p q = Fin.cases false (meet τ p q) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hlegal : Monotone2 (cleanCircuit n C) := cleanGates_legal n C.gates legal
  have hback : ∀ i : Fin (cleanCircuit n C).gates.length,
      ∀ a ∈ ((cleanCircuit n C).gates.get i).inputs, a < (n + 1) + i.val :=
    cleanGates_back n C.gates
  have hclean : ∀ i : Fin (cleanCircuit n C).gates.length,
      ((cleanCircuit n C).gates.get i).op = GateOp.or →
      circuitFun (n + 1) {cleanCircuit n C with output := (n + 1) + i.val} (fun _ => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
        circuitFun (n + 1) {cleanCircuit n C with output := (n + 1) + i.val}
          (meet τ' p q) = false := by
    intro i hi hz p hp q hq hpq
    have hop : (C.gates.get (e i)).op = GateOp.or :=
      (cleanGates_op n C.gates i.val (hlen i)).symm.trans hi
    have zeq : Fin.cases false (fun _ : Fin n => false) = (fun _ : Fin (n + 1) => false) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    have oldzero : circuitFun n {C with output := n + i.val} (fun _ => false) = false := by
      rw [← hsame, zeq]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz
    rw [eqmeet]
    have hs := hsame (n + i.val) (meet τ p q)
    have hc := clean (e i) hop oldzero p hp q hq hpq
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs.trans hc
  have hfalse : ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
      circuitFun (n + 1) (cleanCircuit n C) (meet τ' p q) = false := by
    intro p hp q hq hpq
    rw [eqmeet, cleanCircuit_fun]
    exact hc p hp q hq hpq
  have htrue : ∀ p ∈ M, circuitFun (n + 1) (cleanCircuit n C) (τ' p) = true := by
    intro p hp
    exact (cleanCircuit_fun C (τ p)).trans (ht p hp)
  have heop : ∀ i ∈ E', ((cleanCircuit n C).gates.get i).op = GateOp.or := by
    intro i hi
    exact (cleanGates_op n C.gates i.val (hlen i)).trans (hE (e i) (emem i hi))
  have hexclude : ∀ i ∈ E', ¬Mrg (cleanCircuit n C).gates M τ' i := by
    intro i hi
    apply not_merge_of_mem_dead (cleanCircuit n C) M τ' i
    obtain ⟨a, ha, halt, hd⟩ := dead (e i) (emem i hi)
    refine ⟨a + 1, ?_, ?_⟩
    · change a + 1 ∈ ((cleanGates n C.gates)[i.val]'(by simpa [cleanGates_length] using hlen i)).inputs
      rw [cleanGates_entry n C.gates i.val (hlen i)]
      apply List.mem_map.mpr
      refine ⟨a, ha, ?_⟩
      exact if_pos halt
    · intro p hp
      exact (hsame a (τ p)).trans (hd p hp)
  have h := clean_or_bound_excluding (cleanCircuit n C) M τ' hclean hlegal hback
    hM hfalse htrue E' heop hexclude
  have ec : E'.card = E.card := Finset.card_map _
  rwa [ec, cleanCircuit_or_count] at h

end PEqualNP.Outside.L_meta_1896_aux.CleanOrSkip


namespace PEqualNP.Outside.L_meta_1896_aux.Flags

open PEqualNP.Outside.L_meta_1896_aux.FourRows

def flag (a : Fin 52) : Fin 13 × Fin 13 :=
  ([(0, 0), (1, 0), (3, 0), (9, 0), (1, 1), (2, 1), (4, 1), (10, 1), (2, 2), (3, 2), (5, 2), (11, 2), (3, 3), (4, 3), (6, 3), (12, 3), (4, 4), (5, 4), (7, 4), (0, 4), (5, 5), (6, 5), (8, 5), (1, 5), (6, 6), (7, 6), (9, 6), (2, 6), (7, 7), (8, 7), (10, 7), (3, 7), (8, 8), (9, 8), (11, 8), (4, 8), (9, 9), (10, 9), (12, 9), (5, 9), (10, 10), (11, 10), (0, 10), (6, 10), (11, 11), (12, 11), (1, 11), (7, 11), (12, 12), (0, 12), (2, 12), (8, 12)] : List (Fin 13 × Fin 13)).getD a.val (0, 0)

def input (a : Fin 52) : Fin 26 → Bool := pairInput (flag a).1 (flag a).2

def shared (a b : Fin 52) : Fin 26 :=
  if (flag a).1 = (flag b).1 then Fin.castAdd 13 (flag a).1 else Fin.natAdd 13 (flag a).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma incidence_all : ∀ a : Fin 52, incidence (flag a).1 (flag a).2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
lemma shared_all : ∀ a b : Fin 52, a ≠ b → ∀ w : Fin 26,
    input a w = true → input b w = true → w = shared a b := by
  decide +kernel

lemma meet_small (a b : Fin 52) (hab : a ≠ b) :
    ∃ v : Fin 26, ∀ w, (input a w && input b w) = true → w = v := by
  refine ⟨shared a b, ?_⟩
  intro w hw
  simp only [Bool.and_eq_true] at hw
  exact shared_all a b hab w hw.1 hw.2

end PEqualNP.Outside.L_meta_1896_aux.Flags


namespace PEqualNP.Outside.L_meta_1896_aux.WeightedSurvivors

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Sensitivity
open PEqualNP.Outside.L_meta_1896.DirtyOr
open PEqualNP.Outside.L_meta_1896.FourRowsSensitivity
open PEqualNP.Outside.L_meta_1896_aux.PairRows

lemma survivors_and_blocks_bound (C : Circuit) (legal : Monotone2 C)
    (pos : ∀ p l : Fin 13, incidence p l → circuitFun 26 C (pairInput p l) = true)
    (neg : ∀ a : Fin 25, circuitFun 26 C (row a) = false)
    (M : Finset (Fin 52)) (hM : 1 ≤ M.card)
    (avoid : ∀ a ∈ M, ∀ v ∈ badCoords (n := 26) C, Flags.input a v = false) :
    M.card - 1 + (freshBlocks (n := 26) C).card ≤
      {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard := by
  classical
  have hclean : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.or →
      circuitFun 26 {C with output := 26 + i.val} (fun _ => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
        circuitFun 26 {C with output := 26 + i.val} (CleanOrSkip.meet Flags.input p q) = false := by
    intro i hi hz p hp q hq hpq
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨v, hv⟩ := Flags.meet_small p q hpq
    by_cases he : ∃ w, CleanOrSkip.meet Flags.input p q w = true
    · obtain ⟨w, hw⟩ := he
      have hwv : w = v := hv w hw
      have sub : ∀ u, CleanOrSkip.meet Flags.input p q u = true →
          singletonInput w u = true := by
        intro u hu
        have huv : u = v := hv u hu
        simp [singletonInput, huv, hwv]
      have hsingle : gateValue C (singletonInput w) i = true :=
        val_mono C.gates legal _ _ sub (26 + i.val) ht
      have hb := singleton_mem_badCoords C i hi hz w hsingle
      have haf := avoid p hp w hb
      have hat : Flags.input p w = true := by
        simp only [CleanOrSkip.meet, Bool.and_eq_true] at hw
        exact hw.1
      exact Bool.noConfusion (haf.symm.trans hat)
    · have zeq : CleanOrSkip.meet Flags.input p q = (fun _ => false) := by
        funext w
        apply Bool.eq_false_iff.mpr
        intro hw
        exact he ⟨w, hw⟩
      rw [zeq, hz] at ht
      exact Bool.noConfusion ht
  have hout : ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
      circuitFun 26 C (CleanOrSkip.meet Flags.input p q) = false := by
    intro p hp q hq hpq
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨v, hv⟩ := Flags.meet_small p q hpq
    obtain ⟨a, ha⟩ := rows_cover v
    have sub : ∀ w, CleanOrSkip.meet Flags.input p q w = true → row a w = true := by
      intro w hw
      exact (hv w hw) ▸ ha
    have hr : circuitFun 26 C (row a) = true :=
      val_mono C.gates legal _ _ sub C.output ht
    exact Bool.noConfusion ((neg a).symm.trans hr)
  have hpos : ∀ p ∈ M, circuitFun 26 C (Flags.input p) = true := by
    intro p hp
    exact pos (Flags.flag p).1 (Flags.flag p).2 (Flags.incidence_all p)
  let E : Finset (Fin C.gates.length) := Finset.univ.filter fun j =>
    (freshCoords (n := 26) C j).Nonempty
  have hEO : ∀ j ∈ E, (C.gates.get j).op = GateOp.or := by
    intro j hj
    obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hj).2
    exact (Finset.mem_filter.mp hv).2.1
  have dead : ∀ j ∈ E, ∃ a ∈ (C.gates.get j).inputs, a < 26 + j.val ∧
      ∀ p ∈ M, circuitFun 26 {C with output := a} (Flags.input p) = false := by
    intro j hj
    obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hj).2
    obtain ⟨a, ha, halt, hd⟩ := fresh_or_has_dead_operand C legal j v hv
    refine ⟨a, ha, halt, ?_⟩
    intro p hp
    exact hd (Flags.input p) (avoid p hp v (freshCoords_subset_badCoords C j hv))
  have hb : (freshBlocks (n := 26) C).card ≤ E.card := Finset.card_image_le
  have lower := CleanOrSkip.clean_or_bound_excluding_general C M Flags.input hclean
    legal hM hout hpos E hEO dead
  omega

end PEqualNP.Outside.L_meta_1896_aux.WeightedSurvivors
