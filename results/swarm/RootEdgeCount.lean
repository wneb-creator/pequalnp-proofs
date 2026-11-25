import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj



open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def wireFn (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireFn_mono (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (w : ℕ) :
    Monotone (wireFn n C w) := by
  intro x y hxy
  have hm : wireFn n C w x = true → wireFn n C w y = true := by
    apply wiresFrom_mono C.gates hC.1 (List.ofFn x) (List.ofFn y) (by simp)
    intro i hi
    by_cases hin : i < n
    · have hi' : x ⟨i, hin⟩ = true := by
        rw [List.getD_eq_getElem _ _ (by simpa using hin)] at hi
        simpa only [List.getElem_ofFn] using hi
      have hle := hxy ⟨i, hin⟩
      rw [List.getD_eq_getElem _ _ (by simpa using hin)]
      simpa only [List.getElem_ofFn] using (Bool.le_iff_imp.mp hle hi')
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hin)] at hi
      cases hi
  exact Bool.le_iff_imp.mpr hm

lemma wireFn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wireFn n C w x = x ⟨w, hw⟩ := by
  unfold wireFn Circuit.wires
  change (wiresFrom C.gates (List.ofFn x)).getD w false = _
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

lemma gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma binary_gate (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, a < n + j ∧ b < n + j ∧
      (gateAt C j).inputs = [a, b] ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ x, wireFn n C (n + j) x =
        (gateAt C j).op.eval [wireFn n C a x, wireFn n C b x] := by
  have hmem : gateAt C j ∈ C.gates := by
    rw [gateAt_get C j hj]
    exact List.getElem_mem hj
  have hlen := hC.2.2 _ hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have ha : a < n + j := hC.2.1 j hj a (by simp [hab])
  have hb : b < n + j := hC.2.1 j hj b (by simp [hab])
  refine ⟨a, b, ha, hb, hab, hC.1 _ hmem, ?_⟩
  intro x
  unfold wireFn
  change (wiresFrom C.gates (List.ofFn x)).getD (n + j) false = _
  have he := getD_wiresFrom_gate C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at he
  rw [he, ← gateAt_get C j hj, hab]
  simp [ha, hb, wiresFrom, Circuit.wires]

lemma safe_leaf_count {α : Type*} [DecidableEq α]
    (safe split : ℕ → Prop) [DecidablePred safe] [DecidablePred split]
    (T : ℕ → Finset α)
    (h : ∀ w, safe w → (T w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe a ∧ T w ⊆ T a) ∨
      (split w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ T w ⊆ T a ∪ T b)) :
    ∀ M (W : Finset ℕ), (∀ w ∈ W, w < M ∧ safe w) →
      (W.biUnion T).card ≤ W.card +
        ((Finset.range M).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card)).card := by
  intro M
  induction M with
  | zero =>
    intro W hW
    have : W = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro w hw
      exact Nat.not_lt_zero w (hW w hw).1
    subst W
    simp
  | succ M ih =>
    intro W hW
    let B := (Finset.range M).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card)
    let B' := (Finset.range (M + 1)).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card)
    have hmono : B.card ≤ B'.card := by
      apply Finset.card_le_card
      intro k hk
      simp only [B, B', Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨by omega, hk.2⟩
    change (W.biUnion T).card ≤ W.card + B'.card
    by_cases hM : M ∈ W
    · have hWe : W = insert M (W.erase M) := (Finset.insert_erase hM).symm
      have hW' : ∀ w ∈ W.erase M, w < M ∧ safe w := by
        intro w hw
        rw [Finset.mem_erase] at hw
        have := hW w hw.2
        exact ⟨by omega, this.2⟩
      have hcard : W.card = (W.erase M).card + 1 := by
        rw [Finset.card_erase_of_mem hM]
        have := Finset.card_pos.mpr ⟨M, hM⟩
        omega
      have hU : W.biUnion T = T M ∪ (W.erase M).biUnion T := by
        conv_lhs => rw [hWe]
        rw [Finset.biUnion_insert]
      by_cases hsmall : (T M).card ≤ 1
      · have ih1 := ih (W.erase M) hW'
        have hu := Finset.card_union_le (T M) ((W.erase M).biUnion T)
        rw [hU]
        change _ ≤ (W.erase M).card + B.card at ih1
        omega
      · rcases h M (hW M hM).2 with hs | hb | ⟨hsplit, a, b, ha, hb, hsa, hsb, hsub⟩
        · exact (hsmall hs).elim
        · obtain ⟨a, ha, hsa, hsub⟩ := hb
          let W2 := insert a (W.erase M)
          have hW2 : ∀ w ∈ W2, w < M ∧ safe w := by
            intro w hw
            simp only [W2, Finset.mem_insert] at hw
            rcases hw with rfl | hw
            · exact ⟨ha, hsa⟩
            · exact hW' w hw
          have hU2 : W.biUnion T ⊆ W2.biUnion T := by
            rw [hU]
            simp only [W2, Finset.biUnion_insert]
            exact Finset.union_subset_union_left hsub
          have hc2 : W2.card ≤ (W.erase M).card + 1 := Finset.card_insert_le ..
          have ih2 := ih W2 hW2
          change _ ≤ W2.card + B.card at ih2
          have hu2 := Finset.card_le_card hU2
          omega
        · let W2 := insert a (insert b (W.erase M))
          have hW2 : ∀ w ∈ W2, w < M ∧ safe w := by
            intro w hw
            simp only [W2, Finset.mem_insert] at hw
            rcases hw with rfl | rfl | hw
            · exact ⟨ha, hsa⟩
            · exact ⟨hb, hsb⟩
            · exact hW' w hw
          have hU2 : W.biUnion T ⊆ W2.biUnion T := by
            rw [hU]
            simp only [W2, Finset.biUnion_insert]
            rw [← Finset.union_assoc]
            exact Finset.union_subset_union_left hsub
          have hc2 : W2.card ≤ (W.erase M).card + 2 := by
            have e1 := Finset.card_insert_le a (insert b (W.erase M))
            have e2 := Finset.card_insert_le b (W.erase M)
            dsimp [W2]
            omega
          have ih2 := ih W2 hW2
          change _ ≤ W2.card + B.card at ih2
          have hu2 := Finset.card_le_card hU2
          have hB : B' = insert M B := by
            dsimp [B', B]
            rw [Finset.range_add_one, Finset.filter_insert, ite_eq_left]
            exact ⟨(hW M hM).2, hsplit, by omega⟩
          have hBc : B'.card = B.card + 1 := by
            rw [hB, Finset.card_insert_of_notMem]
            simp [B]
          omega
    · have hW' : ∀ w ∈ W, w < M ∧ safe w := by
        intro w hw
        have := hW w hw
        have hne : w ≠ M := fun he => hM (he ▸ hw)
        exact ⟨by omega, this.2⟩
      have hi := ih W hW'
      change _ ≤ W.card + B.card at hi
      omega

end PEqualNP.Outside.L_meta_4970_aux

namespace PEqualNP.Outside.L_meta_4970.SemanticSafe

variable {α : Type*} [DecidableEq α]

def outsideInput (S : Finset α) : α → Bool := fun i => decide (i ∉ S)

def Safe (S : Finset α) (f : (α → Bool) → Bool) : Prop :=
  ∀ x, f x = true → ∃ i ∈ S, x i = true

def PureOr (S : Finset α) (f : (α → Bool) → Bool) : Prop :=
  ∀ x, f x = true ↔ ∃ i ∈ S, x i = true

lemma safe_at_outside {S : Finset α} {f : (α → Bool) → Bool}
    (h : Safe S f) : f (outsideInput S) = false := by
  cases hf : f (outsideInput S)
  · rfl
  · obtain ⟨i, hi, hxi⟩ := h (outsideInput S) hf
    simp [outsideInput, hi] at hxi

lemma le_outside_of_no_member {S : Finset α} {x : α → Bool}
    (h : ¬ ∃ i ∈ S, x i = true) : x ≤ outsideInput S := by
  intro i
  by_cases hi : i ∈ S
  · have hx : x i = false := by
      cases hxi : x i
      · rfl
      · exact False.elim (h ⟨i, hi, hxi⟩)
    simp [outsideInput, hi, hx]
  · simp [outsideInput, hi]

lemma safe_of_outside {S : Finset α} {f : (α → Bool) → Bool}
    (hf : Monotone f) (h : f (outsideInput S) = false) : Safe S f := by
  intro x hx
  by_contra hnone
  have hle := hf (le_outside_of_no_member hnone)
  have hz : f (outsideInput S) = true := Bool.le_iff_imp.mp hle hx
  simp [h] at hz

lemma safe_iff_outside {S : Finset α} {f : (α → Bool) → Bool}
    (hf : Monotone f) : Safe S f ↔ f (outsideInput S) = false :=
  ⟨safe_at_outside, safe_of_outside hf⟩

lemma safe_and {S : Finset α} {f g : (α → Bool) → Bool}
    (hf : Monotone f) (hg : Monotone g)
    (h : Safe S (fun x => f x && g x)) : Safe S f ∨ Safe S g := by
  have hz := safe_at_outside h
  cases hfv : f (outsideInput S)
  · exact Or.inl (safe_of_outside hf hfv)
  · cases hgv : g (outsideInput S)
    · exact Or.inr (safe_of_outside hg hgv)
    · simp [hfv, hgv] at hz

omit [DecidableEq α] in
lemma safe_or_iff {S : Finset α} {f g : (α → Bool) → Bool} :
    Safe S (fun x => f x || g x) ↔ Safe S f ∧ Safe S g := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x (by simp [hx])
    · intro x hx
      exact h x (by simp [hx])
  · rintro ⟨hf, hg⟩ x hx
    cases hfv : f x
    · apply hg x
      simpa [hfv] using hx
    · exact hf x hfv

lemma pureOr_and_redundant {S : Finset α} {f g : (α → Bool) → Bool}
    (hf : Monotone f) (hg : Monotone g)
    (h : PureOr S (fun x => f x && g x)) : PureOr S f ∨ PureOr S g := by
  have hs : Safe S (fun x => f x && g x) := fun x hx => (h x).mp hx
  rcases safe_and hf hg hs with hsf | hsg
  · left
    intro x
    refine ⟨hsf x, ?_⟩
    intro hx
    have hfg := (h x).mpr hx
    cases hfx : f x
    · simp [hfx] at hfg
    · rfl
  · right
    intro x
    refine ⟨hsg x, ?_⟩
    intro hx
    have hfg := (h x).mpr hx
    cases hgx : g x
    · simp [hgx] at hfg
    · rfl

end PEqualNP.Outside.L_meta_4970.SemanticSafe

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SemanticSafe

def singletonSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => wireFn n C w (fun k => decide (k = i)) = true

lemma mem_singletonSupport (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ singletonSupport n C w ↔ wireFn n C w (fun k => decide (k = i)) = true := by
  simp [singletonSupport]

lemma singletonSupport_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    singletonSupport n C w = {⟨w, hw⟩} := by
  ext i
  simp [mem_singletonSupport, wireFn_input n C w hw, eq_comm]

lemma singletonSupport_safe_subset (n : ℕ) (C : Circuit) (w : ℕ) (Q : Finset (Fin n))
    (hs : Safe Q (wireFn n C w)) : singletonSupport n C w ⊆ Q := by
  intro i hi
  have hv := (mem_singletonSupport n C w i).mp hi
  obtain ⟨k, hk, hki⟩ := hs _ hv
  have : k = i := by simpa using hki
  exact this ▸ hk

lemma singletonSupport_pure (n : ℕ) (C : Circuit) (w : ℕ) (Q : Finset (Fin n))
    (hp : PureOr Q (wireFn n C w)) : singletonSupport n C w = Q := by
  ext i
  rw [mem_singletonSupport, hp]
  simp

lemma safe_singleton_structure (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) :
    ∀ w, (w < n + C.gates.length ∧ Safe Q (wireFn n C w)) →
      (singletonSupport n C w).card ≤ 1 ∨
      (∃ a, a < w ∧ (a < n + C.gates.length ∧ Safe Q (wireFn n C a)) ∧
        singletonSupport n C w ⊆ singletonSupport n C a) ∨
      ((n ≤ w ∧ (gateAt C (w - n)).op = GateOp.or) ∧
        ∃ a b, a < w ∧ b < w ∧
          (a < n + C.gates.length ∧ Safe Q (wireFn n C a)) ∧
          (b < n + C.gates.length ∧ Safe Q (wireFn n C b)) ∧
          singletonSupport n C w ⊆ singletonSupport n C a ∪ singletonSupport n C b) := by
  intro w ⟨hw, hs⟩
  by_cases hi : w < n
  · left
    rw [singletonSupport_input n C w hi]
    simp
  · have hn : n ≤ w := Nat.le_of_not_lt hi
    have hj : w - n < C.gates.length := by omega
    have heq : n + (w - n) = w := by omega
    obtain ⟨a, b, ha, hb, hab, hop, he⟩ := binary_gate n C hC (w - n) hj
    rw [heq] at ha hb he
    rcases hop with hand | hor
    · have hv : ∀ x, wireFn n C w x = (wireFn n C a x && wireFn n C b x) := by
        intro x
        rw [he, hand]
        simp [GateOp.eval]
      have hs' : Safe Q (fun x => wireFn n C a x && wireFn n C b x) := by
        simpa only [← hv] using hs
      have hbypass := safe_and (wireFn_mono n C hC a) (wireFn_mono n C hC b) hs'
      right; left
      rcases hbypass with hsa | hsb
      · refine ⟨a, ha, ⟨by omega, hsa⟩, ?_⟩
        intro i hi
        rw [mem_singletonSupport] at hi ⊢
        rw [hv] at hi
        exact (Bool.and_eq_true_iff.mp hi).1
      · refine ⟨b, hb, ⟨by omega, hsb⟩, ?_⟩
        intro i hi
        rw [mem_singletonSupport] at hi ⊢
        rw [hv] at hi
        exact (Bool.and_eq_true_iff.mp hi).2
    · have hv : ∀ x, wireFn n C w x = (wireFn n C a x || wireFn n C b x) := by
        intro x
        rw [he, hor]
        simp [GateOp.eval]
      have hs' : Safe Q (fun x => wireFn n C a x || wireFn n C b x) := by
        simpa only [← hv] using hs
      obtain ⟨hsa, hsb⟩ := safe_or_iff.mp hs'
      right; right
      refine ⟨⟨hn, hor⟩, a, b, ha, hb, ⟨by omega, hsa⟩, ⟨by omega, hsb⟩, ?_⟩
      intro i hi
      rw [mem_singletonSupport, hv, Bool.or_eq_true] at hi
      simp only [Finset.mem_union, mem_singletonSupport]
      exact hi

noncomputable def chargedOr (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.range (n + C.gates.length)).filter fun k =>
    (k < n + C.gates.length ∧ Safe Q (wireFn n C k)) ∧
    (n ≤ k ∧ (gateAt C (k - n)).op = GateOp.or) ∧
    2 ≤ (singletonSupport n C k).card

lemma pure_disjunction_or_count (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (w : ℕ) (hw : w < n + C.gates.length)
    (hp : PureOr Q (wireFn n C w)) :
    Q.card ≤ 1 + (chargedOr n C Q).card := by
  classical
  have hs : Safe Q (wireFn n C w) := fun x hx => (hp x).mp hx
  have hh := safe_leaf_count
    (fun k => k < n + C.gates.length ∧ Safe Q (wireFn n C k))
    (fun k => n ≤ k ∧ (gateAt C (k - n)).op = GateOp.or)
    (singletonSupport n C) (safe_singleton_structure n C hC Q)
    (n + C.gates.length) {w} (by simpa using And.intro hw (And.intro hw hs))
  simpa [chargedOr, singletonSupport_pure n C w Q hp] using hh

lemma frontier_or_count (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (W : Finset ℕ)
    (hW : ∀ w ∈ W, w < n + C.gates.length ∧ Safe Q (wireFn n C w)) :
    (W.biUnion (singletonSupport n C)).card ≤ W.card + (chargedOr n C Q).card := by
  classical
  apply safe_leaf_count
    (fun k => k < n + C.gates.length ∧ Safe Q (wireFn n C k))
    (fun k => n ≤ k ∧ (gateAt C (k - n)).op = GateOp.or)
    (singletonSupport n C) (safe_singleton_structure n C hC Q)
  intro w hw
  exact ⟨(hW w hw).1, hW w hw⟩

lemma chargedOr_disjoint (n : ℕ) (C : Circuit) (Q R : Finset (Fin n))
    (hQR : (Q ∩ R).card ≤ 1) : Disjoint (chargedOr n C Q) (chargedOr n C R) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k hk hr
  simp only [chargedOr, Finset.mem_filter, Finset.mem_range] at hk hr
  have hsub : singletonSupport n C k ⊆ Q ∩ R :=
    Finset.subset_inter
      (singletonSupport_safe_subset n C k Q hk.2.1.2)
      (singletonSupport_safe_subset n C k R hr.2.1.2)
  have hsmall := (Finset.card_le_card hsub).trans hQR
  have hlarge := hk.2.2.2
  omega

lemma frontier_family_or_count {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (Q : ι → Finset (Fin n)) (W : ι → Finset ℕ)
    (hQ : ∀ i ∈ I, Q i = (W i).biUnion (singletonSupport n C))
    (hW : ∀ i ∈ I, ∀ w ∈ W i,
      w < n + C.gates.length ∧ Safe (Q i) (wireFn n C w))
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (Q i ∩ Q j).card ≤ 1) :
    (∑ i ∈ I, (Q i).card) ≤ (∑ i ∈ I, (W i).card) + C.size := by
  classical
  have hlocal : ∑ i ∈ I, (Q i).card ≤
      ∑ i ∈ I, ((W i).card + (chargedOr n C (Q i)).card) := by
    apply Finset.sum_le_sum
    intro i hi
    conv_lhs => rw [hQ i hi]
    exact frontier_or_count n C hC (Q i) (W i) (hW i hi)
  have hd : (I : Set ι).PairwiseDisjoint (fun i => chargedOr n C (Q i)) := by
    intro i hi j hj hij
    exact chargedOr_disjoint n C (Q i) (Q j) (hinter i hi j hj hij)
  have hsub : I.biUnion (fun i => chargedOr n C (Q i)) ⊆
      Finset.Ico n (n + C.gates.length) := by
    intro k hk
    obtain ⟨i, hi, hk⟩ := Finset.mem_biUnion.mp hk
    simp only [chargedOr, Finset.mem_filter, Finset.mem_range] at hk
    exact Finset.mem_Ico.mpr ⟨hk.2.2.1.1, hk.1⟩
  have hsum : (∑ i ∈ I, (chargedOr n C (Q i)).card) ≤ C.size := by
    rw [← Finset.card_biUnion hd]
    have hc := Finset.card_le_card hsub
    simpa [Circuit.size] using hc
  rw [Finset.sum_add_distrib] at hlocal
  omega

lemma common_neighbours_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hno : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (a a' : Fin p) (haa : a ≠ a') (Q Q' : Finset (Fin l))
    (hQ : ∀ b ∈ Q, (a, b) ∈ E) (hQ' : ∀ b ∈ Q', (a', b) ∈ E) :
    (Q ∩ Q').card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb b' hb'
  by_contra hbb
  exact hno a a' b b' haa hbb
    ⟨hQ b (Finset.mem_inter.mp hb).1, hQ b' (Finset.mem_inter.mp hb').1,
      hQ' b (Finset.mem_inter.mp hb).2, hQ' b' (Finset.mem_inter.mp hb').2⟩

end PEqualNP.Outside.L_meta_4970_aux

namespace PEqualNP.Outside.L_meta_4970_aux.RootCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SemanticSafe

noncomputable def orWires (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.gates.length)).filter fun w =>
    (gateAt C (w - n)).op = GateOp.or

lemma chargedOr_subset_orWires (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) :
    chargedOr n C Q ⊆ orWires n C := by
  classical
  intro w hw
  simp only [chargedOr, Finset.mem_filter, Finset.mem_range] at hw
  simp only [orWires, Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨hw.2.2.1.1, hw.1⟩, hw.2.2.1.2⟩

lemma chargedOr_family_bound {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (I : Finset ι) (Q : ι → Finset (Fin n))
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (Q i ∩ Q j).card ≤ 1) :
    (∑ i ∈ I, (chargedOr n C (Q i)).card) ≤ (orWires n C).card := by
  classical
  have hd : (I : Set ι).PairwiseDisjoint (fun i => chargedOr n C (Q i)) := by
    intro i hi j hj hij
    exact chargedOr_disjoint n C (Q i) (Q j) (hinter i hi j hj hij)
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨i, hi, hw⟩ := Finset.mem_biUnion.mp hw
  exact chargedOr_subset_orWires n C (Q i) hw

lemma family_leaf_bound {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (Q : ι → Finset (Fin n)) (W : ι → Finset ℕ)
    (hQ : ∀ i ∈ I, Q i = (W i).biUnion (singletonSupport n C))
    (hW : ∀ i ∈ I, ∀ w ∈ W i,
      w < n + C.gates.length ∧ Safe (Q i) (wireFn n C w))
    (hroot : ∀ i ∈ I, ∀ w ∈ W i,
      n ≤ w ∧ (gateAt C (w - n)).op = GateOp.or ∧
        2 ≤ (singletonSupport n C w).card)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (Q i ∩ Q j).card ≤ 1) :
    (∑ i ∈ I, (Q i).card) ≤ 2 * (orWires n C).card := by
  classical
  have hlocal : ∑ i ∈ I, (Q i).card ≤
      ∑ i ∈ I, ((W i).card + (chargedOr n C (Q i)).card) := by
    apply Finset.sum_le_sum
    intro i hi
    conv_lhs => rw [hQ i hi]
    exact frontier_or_count n C hC (Q i) (W i) (hW i hi)
  have hroots : ∑ i ∈ I, (W i).card ≤
      ∑ i ∈ I, (chargedOr n C (Q i)).card := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.card_le_card
    intro w hw
    have hs := hW i hi w hw
    have hr := hroot i hi w hw
    simp only [chargedOr, Finset.mem_filter, Finset.mem_range]
    exact ⟨hs.1, hs, ⟨hr.1, hr.2.1⟩, hr.2.2⟩
  have hsum := chargedOr_family_bound n C I Q hinter
  rw [Finset.sum_add_distrib] at hlocal
  omega

lemma castAdd_injective (p l : ℕ) :
    Function.Injective (Fin.castAdd l : Fin p → Fin (p + l)) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun z : Fin (p + l) => z.val) h

lemma natAdd_injective (p l : ℕ) :
    Function.Injective (Fin.natAdd p : Fin l → Fin (p + l)) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp at hv
  omega

lemma castAdd_ne_natAdd {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have hv := congrArg Fin.val h
  dsimp at hv
  have := a.isLt
  omega

def leftRoot {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (a : Fin p) (w : ℕ) : Prop :=
  p + l ≤ w ∧ w < p + l + C.gates.length ∧
  (gateAt C (w - (p + l))).op = GateOp.or ∧
  ∃ Q : Finset (Fin l), 2 ≤ Q.card ∧ (∀ b ∈ Q, (a, b) ∈ E) ∧
    PureOr (Q.image (Fin.natAdd p)) (wireFn (p + l) C w)

def rightRoot {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (b : Fin l) (w : ℕ) : Prop :=
  p + l ≤ w ∧ w < p + l + C.gates.length ∧
  (gateAt C (w - (p + l))).op = GateOp.or ∧
  ∃ P : Finset (Fin p), 2 ≤ P.card ∧ (∀ a ∈ P, (a, b) ∈ E) ∧
    PureOr (P.image (Fin.castAdd l)) (wireFn (p + l) C w)

noncomputable def roots {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (c : Fin p ⊕ Fin l) : Finset ℕ := by
  classical
  exact (Finset.range (p + l + C.gates.length)).filter fun w =>
    match c with
    | .inl a => leftRoot E C a w
    | .inr b => rightRoot E C b w

noncomputable def leaves {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (c : Fin p ⊕ Fin l) : Finset (Fin (p + l)) :=
  (roots E C c).biUnion (singletonSupport (p + l) C)

lemma mem_roots_left {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (a : Fin p) (w : ℕ) : w ∈ roots E C (.inl a) ↔ leftRoot E C a w := by
  classical
  simp only [roots, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨h.2.1, h⟩⟩

lemma mem_roots_right {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (b : Fin l) (w : ℕ) : w ∈ roots E C (.inr b) ↔ rightRoot E C b w := by
  classical
  simp only [roots, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨h.2.1, h⟩⟩

lemma root_facts {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (c : Fin p ⊕ Fin l) (w : ℕ) (hw : w ∈ roots E C c) :
    w < p + l + C.gates.length ∧ Safe (leaves E C c) (wireFn (p + l) C w) ∧
      p + l ≤ w ∧ (gateAt C (w - (p + l))).op = GateOp.or ∧
        2 ≤ (singletonSupport (p + l) C w).card := by
  classical
  have hs : singletonSupport (p + l) C w ⊆ leaves E C c := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨w, hw, hi⟩
  cases c with
  | inl a =>
      obtain ⟨hn, hw', ho, Q, hQ, _, hp⟩ := (mem_roots_left E C a w).mp hw
      have he := singletonSupport_pure (p + l) C w _ hp
      refine ⟨hw', ?_, hn, ho, ?_⟩
      · intro x hx
        obtain ⟨i, hi, hix⟩ := (hp x).mp hx
        exact ⟨i, hs (he.symm ▸ hi), hix⟩
      · rw [he, Finset.card_image_of_injective _ (natAdd_injective p l)]
        exact hQ
  | inr b =>
      obtain ⟨hn, hw', ho, P, hP, _, hp⟩ := (mem_roots_right E C b w).mp hw
      have he := singletonSupport_pure (p + l) C w _ hp
      refine ⟨hw', ?_, hn, ho, ?_⟩
      · intro x hx
        obtain ⟨i, hi, hix⟩ := (hp x).mp hx
        exact ⟨i, hs (he.symm ▸ hi), hix⟩
      · rw [he, Finset.card_image_of_injective _ (castAdd_injective p l)]
        exact hP

lemma mem_left_leaves {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (a : Fin p) (i : Fin (p + l)) (hi : i ∈ leaves E C (.inl a)) :
    ∃ b : Fin l, (a, b) ∈ E ∧ i = Fin.natAdd p b := by
  classical
  obtain ⟨w, hw, hi⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨_, _, _, Q, _, hQ, hp⟩ := (mem_roots_left E C a w).mp hw
  rw [singletonSupport_pure (p + l) C w _ hp] at hi
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hi
  exact ⟨b, hQ b hb, rfl⟩

lemma mem_right_leaves {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (b : Fin l) (i : Fin (p + l)) (hi : i ∈ leaves E C (.inr b)) :
    ∃ a : Fin p, (a, b) ∈ E ∧ i = Fin.castAdd l a := by
  classical
  obtain ⟨w, hw, hi⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨_, _, _, P, _, hP, hp⟩ := (mem_roots_right E C b w).mp hw
  rw [singletonSupport_pure (p + l) C w _ hp] at hi
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
  exact ⟨a, hP a ha, rfl⟩

lemma leaves_inter_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hno : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (c d : Fin p ⊕ Fin l) (hne : c ≠ d) :
    (leaves E C c ∩ leaves E C d).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro u hu v hv
  rcases Finset.mem_inter.mp hu with ⟨hu1, hu2⟩
  rcases Finset.mem_inter.mp hv with ⟨hv1, hv2⟩
  cases c with
  | inl a =>
      cases d with
      | inl a' =>
          obtain ⟨b1, h1, e1⟩ := mem_left_leaves E C a u hu1
          obtain ⟨b2, h2, e2⟩ := mem_left_leaves E C a' u hu2
          obtain ⟨b3, h3, e3⟩ := mem_left_leaves E C a v hv1
          obtain ⟨b4, h4, e4⟩ := mem_left_leaves E C a' v hv2
          have h12 := natAdd_injective p l (e1.symm.trans e2)
          have h34 := natAdd_injective p l (e3.symm.trans e4)
          subst b2
          subst b4
          by_contra huv
          have haa : a ≠ a' := fun h => hne (congrArg Sum.inl h)
          have hbb : b1 ≠ b3 := by
            intro h
            apply huv
            exact e1.trans ((congrArg (Fin.natAdd p) h).trans e3.symm)
          exact hno a a' b1 b3 haa hbb ⟨h1, h3, h2, h4⟩
      | inr b =>
          obtain ⟨b', _, he⟩ := mem_left_leaves E C a u hu1
          obtain ⟨a', _, hf⟩ := mem_right_leaves E C b u hu2
          exact False.elim (castAdd_ne_natAdd a' b' (hf.symm.trans he))
  | inr b =>
      cases d with
      | inl a =>
          obtain ⟨a', _, he⟩ := mem_right_leaves E C b u hu1
          obtain ⟨b', _, hf⟩ := mem_left_leaves E C a u hu2
          exact False.elim (castAdd_ne_natAdd a' b' (he.symm.trans hf))
      | inr b' =>
          obtain ⟨a1, h1, e1⟩ := mem_right_leaves E C b u hu1
          obtain ⟨a2, h2, e2⟩ := mem_right_leaves E C b' u hu2
          obtain ⟨a3, h3, e3⟩ := mem_right_leaves E C b v hv1
          obtain ⟨a4, h4, e4⟩ := mem_right_leaves E C b' v hv2
          have h12 := castAdd_injective p l (e1.symm.trans e2)
          have h34 := castAdd_injective p l (e3.symm.trans e4)
          subst a2
          subst a4
          by_contra huv
          have hbb : b ≠ b' := fun h => hne (congrArg Sum.inr h)
          have haa : a1 ≠ a3 := by
            intro h
            apply huv
            exact e1.trans ((congrArg (Fin.castAdd l) h).trans e3.symm)
          exact hno a1 a3 b b' haa hbb ⟨h1, h2, h3, h4⟩

lemma leaves_sum_bound {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hC : IsAO2 (p + l) C)
    (hno : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) :
    (∑ c : Fin p ⊕ Fin l, (leaves E C c).card) ≤ 2 * (orWires (p + l) C).card := by
  classical
  apply family_leaf_bound (p + l) C hC Finset.univ (leaves E C) (roots E C)
  · intro c _
    rfl
  · intro c _ w hw
    have h := root_facts E C c w hw
    exact ⟨h.1, h.2.1⟩
  · intro c _ w hw
    exact (root_facts E C c w hw).2.2
  · intro c _ d _ hne
    exact leaves_inter_card_le_one E C hno c d hne

lemma edge_card_le_family {p l : ℕ} (E : Finset (Fin p × Fin l))
    (Q : Fin p ⊕ Fin l → Finset (Fin (p + l)))
    (hc : ∀ a b, (a, b) ∈ E →
      Fin.natAdd p b ∈ Q (.inl a) ∨ Fin.castAdd l a ∈ Q (.inr b)) :
    E.card ≤ ∑ c : Fin p ⊕ Fin l, (Q c).card := by
  classical
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn
    (fun e : Fin p × Fin l => if Fin.natAdd p e.2 ∈ Q (.inl e.1) then
      (⟨Sum.inl e.1, Fin.natAdd p e.2⟩ : Σ _ : Fin p ⊕ Fin l, Fin (p + l))
      else ⟨Sum.inr e.2, Fin.castAdd l e.1⟩) ?_ ?_
  · intro e he
    by_cases h : Fin.natAdd p e.2 ∈ Q (.inl e.1)
    · simp [h]
    · have hr := (hc e.1 e.2 he).resolve_left h
      simp [h, hr]
  · intro e _ e' _ hee
    dsimp only at hee
    by_cases h1 : Fin.natAdd p e.2 ∈ Q (.inl e.1) <;>
      by_cases h2 : Fin.natAdd p e'.2 ∈ Q (.inl e'.1)
    · rw [if_pos h1, if_pos h2] at hee
      obtain ⟨a, b⟩ := Sigma.mk.inj_iff.mp hee
      exact Prod.ext (Sum.inl.inj a) (natAdd_injective p l (eq_of_heq b))
    · rw [if_pos h1, if_neg h2] at hee
      cases (Sigma.mk.inj_iff.mp hee).1
    · rw [if_neg h1, if_pos h2] at hee
      cases (Sigma.mk.inj_iff.mp hee).1
    · rw [if_neg h1, if_neg h2] at hee
      obtain ⟨a, b⟩ := Sigma.mk.inj_iff.mp hee
      exact Prod.ext (castAdd_injective p l (eq_of_heq b)) (Sum.inr.inj a)

lemma left_witness_mem {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (a : Fin p) (b : Fin l) (j : ℕ) (Q : Finset (Fin l))
    (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.or)
    (hQ : 2 ≤ Q.card) (hb : b ∈ Q) (hE : ∀ b' ∈ Q, (a, b') ∈ E)
    (hfun : ∀ x : Fin (p + l) → Bool,
      (C.wires (List.ofFn x)).getD (p + l + j) false =
        decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) :
    Fin.natAdd p b ∈ leaves E C (.inl a) := by
  classical
  have hp : PureOr (Q.image (Fin.natAdd p)) (wireFn (p + l) C (p + l + j)) := by
    intro x
    change (C.wires (List.ofFn x)).getD (p + l + j) false = true ↔ _
    rw [hfun x, decide_eq_true_eq]
    constructor
    · rintro ⟨b', hb', hx⟩
      exact ⟨_, Finset.mem_image.mpr ⟨b', hb', rfl⟩, hx⟩
    · rintro ⟨i, hi, hx⟩
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hi
      exact ⟨b', hb', hx⟩
  have hw : p + l + j ∈ roots E C (.inl a) := by
    apply (mem_roots_left E C a _).mpr
    refine ⟨by omega, by omega, ?_, Q, hQ, hE, hp⟩
    simpa using ho
  apply Finset.mem_biUnion.mpr
  refine ⟨p + l + j, hw, ?_⟩
  rw [singletonSupport_pure (p + l) C _ _ hp]
  exact Finset.mem_image.mpr ⟨b, hb, rfl⟩

lemma right_witness_mem {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (a : Fin p) (b : Fin l) (j : ℕ) (P : Finset (Fin p))
    (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.or)
    (hP : 2 ≤ P.card) (ha : a ∈ P) (hE : ∀ a' ∈ P, (a', b) ∈ E)
    (hfun : ∀ x : Fin (p + l) → Bool,
      (C.wires (List.ofFn x)).getD (p + l + j) false =
        decide (∃ a' ∈ P, x (Fin.castAdd l a') = true)) :
    Fin.castAdd l a ∈ leaves E C (.inr b) := by
  classical
  have hp : PureOr (P.image (Fin.castAdd l)) (wireFn (p + l) C (p + l + j)) := by
    intro x
    change (C.wires (List.ofFn x)).getD (p + l + j) false = true ↔ _
    rw [hfun x, decide_eq_true_eq]
    constructor
    · rintro ⟨a', ha', hx⟩
      exact ⟨_, Finset.mem_image.mpr ⟨a', ha', rfl⟩, hx⟩
    · rintro ⟨i, hi, hx⟩
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hi
      exact ⟨a', ha', hx⟩
  have hw : p + l + j ∈ roots E C (.inr b) := by
    apply (mem_roots_right E C b _).mpr
    refine ⟨by omega, by omega, ?_, P, hP, hE, hp⟩
    simpa using ho
  apply Finset.mem_biUnion.mpr
  refine ⟨p + l + j, hw, ?_⟩
  rw [singletonSupport_pure (p + l) C _ _ hp]
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

lemma edge_le_twice_or_wires {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hno : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hC : IsAO2 (p + l) C)
    (hserve : ∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
      (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧
        (gateAt C j).op = GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧
        (∀ b' ∈ Q, (a, b') ∈ E) ∧ ∀ x : Fin (p + l) → Bool,
          (C.wires (List.ofFn x)).getD (p + l + j) false =
            decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨
      (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧
        (gateAt C j).op = GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧
        (∀ a' ∈ P, (a', b) ∈ E) ∧ ∀ x : Fin (p + l) → Bool,
          (C.wires (List.ofFn x)).getD (p + l + j) false =
            decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) :
    E.card ≤ 2 * (orWires (p + l) C).card := by
  have hc : ∀ a b, (a, b) ∈ E →
      Fin.natAdd p b ∈ leaves E C (.inl a) ∨
        Fin.castAdd l a ∈ leaves E C (.inr b) := by
    intro a b hab
    rcases hserve a b hab with ⟨j, Q, hj, ho, hQ, hb, hE, hf⟩ |
      ⟨j, P, hj, ho, hP, ha, hE, hf⟩
    · exact Or.inl (left_witness_mem E C a b j Q hj ho hQ hb hE hf)
    · exact Or.inr (right_witness_mem E C a b j P hj ho hP ha hE hf)
  exact (edge_card_le_family E (leaves E C) hc).trans (leaves_sum_bound E C hC hno)

noncomputable def activeCenters {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit) :
    Finset (Fin p ⊕ Fin l) := by
  classical
  exact Finset.univ.filter fun c => (roots E C c).Nonempty

def centerVertex {p l : ℕ} : Fin p ⊕ Fin l → Fin (p + l)
  | .inl a => Fin.castAdd l a
  | .inr b => Fin.natAdd p b

noncomputable def witnessCover {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit) :
    Finset (Fin (p + l)) := (activeCenters E C).image centerVertex

lemma roots_subset_charged {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (c : Fin p ⊕ Fin l) : roots E C c ⊆ chargedOr (p + l) C (leaves E C c) := by
  classical
  intro w hw
  obtain ⟨hw', hs, hn, ho, hc⟩ := root_facts E C c w hw
  simp only [chargedOr, Finset.mem_filter, Finset.mem_range]
  exact ⟨hw', ⟨hw', hs⟩, ⟨hn, ho⟩, hc⟩

lemma witnessCover_card_le_or {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hno : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) :
    (witnessCover E C).card ≤ (orWires (p + l) C).card := by
  classical
  have ha : (activeCenters E C).card ≤
      ∑ c ∈ activeCenters E C, (chargedOr (p + l) C (leaves E C c)).card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro c hc
    obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hc).2
    exact Finset.card_pos.mpr ⟨w, roots_subset_charged E C c hw⟩
  have hb : (∑ c ∈ activeCenters E C, (chargedOr (p + l) C (leaves E C c)).card) ≤
      ∑ c : Fin p ⊕ Fin l, (chargedOr (p + l) C (leaves E C c)).card :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hd := chargedOr_family_bound (p + l) C Finset.univ (leaves E C)
    (fun c _ d _ hne => leaves_inter_card_le_one E C hno c d hne)
  exact Finset.card_image_le.trans (ha.trans (hb.trans hd))

lemma witnessCover_covers {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hc : ∀ a b, (a, b) ∈ E →
      Fin.natAdd p b ∈ leaves E C (.inl a) ∨ Fin.castAdd l a ∈ leaves E C (.inr b)) :
    ∀ a b, (a, b) ∈ E →
      Fin.castAdd l a ∈ witnessCover E C ∨ Fin.natAdd p b ∈ witnessCover E C := by
  classical
  intro a b hab
  rcases hc a b hab with ha | hb
  · obtain ⟨w, hw, _⟩ := Finset.mem_biUnion.mp ha
    left
    apply Finset.mem_image.mpr
    refine ⟨Sum.inl a, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨w, hw⟩⟩
  · obtain ⟨w, hw, _⟩ := Finset.mem_biUnion.mp hb
    right
    apply Finset.mem_image.mpr
    refine ⟨Sum.inr b, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨w, hw⟩⟩

lemma full_bound_of_or_budget {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hno : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hc : ∀ a b, (a, b) ∈ E →
      Fin.natAdd p b ∈ leaves E C (.inl a) ∨ Fin.castAdd l a ∈ leaves E C (.inr b))
    (hbudget : E.card + (orWires (p + l) C).card ≤ C.size + 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
        E.card + S.card ≤ C.size + 1 := by
  refine ⟨witnessCover E C, witnessCover_covers E C hc, ?_⟩
  have hs := witnessCover_card_le_or E C hno
  omega

end PEqualNP.Outside.L_meta_4970_aux.RootCount
