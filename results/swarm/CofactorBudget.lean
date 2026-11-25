import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

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

noncomputable def allOrWires (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.gates.length)).filter fun k =>
    (gateAt C (k - n)).op = GateOp.or

lemma allOrWires_card_le (n : ℕ) (C : Circuit) : (allOrWires n C).card ≤ C.size := by
  classical
  have hc := Finset.card_filter_le (s := Finset.Ico n (n + C.gates.length))
    (p := fun k => (gateAt C (k - n)).op = GateOp.or)
  simpa [allOrWires, Circuit.size] using hc

lemma frontier_family_or_count_strong {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (Q : ι → Finset (Fin n)) (W : ι → Finset ℕ)
    (hQ : ∀ i ∈ I, Q i = (W i).biUnion (singletonSupport n C))
    (hW : ∀ i ∈ I, ∀ w ∈ W i,
      w < n + C.gates.length ∧ Safe (Q i) (wireFn n C w))
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (Q i ∩ Q j).card ≤ 1) :
    (∑ i ∈ I, (Q i).card) ≤ (∑ i ∈ I, (W i).card) + (allOrWires n C).card := by
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
      allOrWires n C := by
    intro k hk
    obtain ⟨i, hi, hk⟩ := Finset.mem_biUnion.mp hk
    simp only [chargedOr, Finset.mem_filter, Finset.mem_range] at hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hk.2.2.1.1, hk.1⟩, hk.2.2.1.2⟩
  have hsum : (∑ i ∈ I, (chargedOr n C (Q i)).card) ≤ (allOrWires n C).card := by
    rw [← Finset.card_biUnion hd]
    exact Finset.card_le_card hsub
  rw [Finset.sum_add_distrib] at hlocal
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

def essentialSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ x : Fin n → Bool,
    wireFn n C w (Function.update x i false) ≠ wireFn n C w (Function.update x i true)

lemma mem_essentialSupport (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ essentialSupport n C w ↔ ∃ x : Fin n → Bool,
      wireFn n C w (Function.update x i false) ≠ wireFn n C w (Function.update x i true) := by
  simp [essentialSupport]

lemma essentialSupport_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    essentialSupport n C w = {⟨w, hw⟩} := by
  ext i
  rw [mem_essentialSupport, Finset.mem_singleton]
  simp only [wireFn_input n C w hw]
  constructor
  · rintro ⟨x, hx⟩
    by_contra hne
    simp [Function.update_of_ne (Ne.symm hne)] at hx
  · rintro rfl
    exact ⟨fun _ => false, by simp⟩

lemma essentialSupport_binary_subset (n : ℕ) (C : Circuit) (w a b : ℕ) (op : GateOp)
    (he : ∀ x, wireFn n C w x = op.eval [wireFn n C a x, wireFn n C b x]) :
    essentialSupport n C w ⊆ essentialSupport n C a ∪ essentialSupport n C b := by
  intro i hi
  by_contra hn
  have ha : i ∉ essentialSupport n C a := fun h => hn (Finset.mem_union_left _ h)
  have hb : i ∉ essentialSupport n C b := fun h => hn (Finset.mem_union_right _ h)
  have hA : ∀ x, wireFn n C a (Function.update x i false) = wireFn n C a (Function.update x i true) := by
    intro x
    by_contra hne
    exact ha ((mem_essentialSupport n C a i).mpr ⟨x, hne⟩)
  have hB : ∀ x, wireFn n C b (Function.update x i false) = wireFn n C b (Function.update x i true) := by
    intro x
    by_contra hne
    exact hb ((mem_essentialSupport n C b i).mpr ⟨x, hne⟩)
  obtain ⟨x, hx⟩ := (mem_essentialSupport n C w i).mp hi
  apply hx
  rw [he, he, hA x, hB x]

lemma essentialSupport_count (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (w : ℕ) (hw : w < n + C.gates.length) :
    (essentialSupport n C w).card ≤ C.size + 1 := by
  classical
  have hs : ∀ k, k < n + C.gates.length → (essentialSupport n C k).card ≤ 1 ∨
      (∃ a, a < k ∧ a < n + C.gates.length ∧ essentialSupport n C k ⊆ essentialSupport n C a) ∨
      (n ≤ k ∧ ∃ a b, a < k ∧ b < k ∧ a < n + C.gates.length ∧ b < n + C.gates.length ∧
        essentialSupport n C k ⊆ essentialSupport n C a ∪ essentialSupport n C b) := by
    intro k hk
    by_cases hi : k < n
    · left
      rw [essentialSupport_input n C k hi]
      simp
    · have hn : n ≤ k := Nat.le_of_not_lt hi
      have hj : k - n < C.gates.length := by omega
      have heq : n + (k - n) = k := by omega
      obtain ⟨a, b, ha, hb, hab, hop, he⟩ := binary_gate n C hC (k - n) hj
      rw [heq] at ha hb he
      right; right
      exact ⟨hn, a, b, ha, hb, by omega, by omega,
        essentialSupport_binary_subset n C k a b _ he⟩
  have hc := safe_leaf_count (fun k => k < n + C.gates.length) (fun k => n ≤ k)
    (essentialSupport n C) hs (n + C.gates.length) {w} (by simpa using And.intro hw hw)
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
  have hsub : (Finset.range (n + C.gates.length)).filter
      (fun k => k < n + C.gates.length ∧ n ≤ k ∧ 2 ≤ (essentialSupport n C k).card) ⊆
      Finset.Ico n (n + C.gates.length) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    exact Finset.mem_Ico.mpr ⟨hk.2.2.1, hk.1⟩
  have hb := Finset.card_le_card hsub
  simp only [Nat.card_Ico, Nat.add_sub_cancel_left] at hb
  unfold Circuit.size
  omega

lemma castAdd_ne_natAdd {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at he
  have := a.isLt
  omega

lemma edge_endpoint_essential {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hF : ∀ x : Fin (p + l) → Bool,
      wireFn (p + l) C C.output x = decide (∃ (a : Fin p) (b : Fin l),
        (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (a : Fin p) (b : Fin l) (hab : (a, b) ∈ E) :
    Fin.castAdd l a ∈ essentialSupport (p + l) C C.output ∧
    Fin.natAdd p b ∈ essentialSupport (p + l) C C.output := by
  constructor
  · rw [mem_essentialSupport]
    let x : Fin (p + l) → Bool := fun i => decide (i = Fin.natAdd p b)
    refine ⟨x, ?_⟩
    have hz : wireFn (p + l) C C.output (Function.update x (Fin.castAdd l a) false) = false := by
      rw [hF, decide_eq_false_iff_not]
      rintro ⟨a', b', he, ha', hb'⟩
      by_cases heq : Fin.castAdd l a' = Fin.castAdd l a
      · simp [heq] at ha'
      · simp [Function.update_of_ne heq, x, castAdd_ne_natAdd a' b] at ha'
    have ho : wireFn (p + l) C C.output (Function.update x (Fin.castAdd l a) true) = true := by
      rw [hF, decide_eq_true_eq]
      refine ⟨a, b, hab, by simp, ?_⟩
      simp [Function.update_of_ne (castAdd_ne_natAdd a b).symm, x]
    rw [hz, ho]
    decide
  · rw [mem_essentialSupport]
    let x : Fin (p + l) → Bool := fun i => decide (i = Fin.castAdd l a)
    refine ⟨x, ?_⟩
    have hz : wireFn (p + l) C C.output (Function.update x (Fin.natAdd p b) false) = false := by
      rw [hF, decide_eq_false_iff_not]
      rintro ⟨a', b', he, ha', hb'⟩
      by_cases heq : Fin.natAdd p b' = Fin.natAdd p b
      · simp [heq] at hb'
      · simp [Function.update_of_ne heq, x, (castAdd_ne_natAdd a b').symm] at hb'
    have ho : wireFn (p + l) C C.output (Function.update x (Fin.natAdd p b) true) = true := by
      rw [hF, decide_eq_true_eq]
      refine ⟨a, b, hab, ?_, by simp⟩
      simp [Function.update_of_ne (castAdd_ne_natAdd a b), x]
    rw [hz, ho]
    decide

lemma wireFn_ge (n : ℕ) (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w)
    (x : Fin n → Bool) : wireFn n C w x = false := by
  unfold wireFn Circuit.wires
  change (wiresFrom C.gates (List.ofFn x)).getD w false = false
  apply List.getD_eq_default
  simpa only [length_wiresFrom, List.length_ofFn] using hw

lemma output_valid_of_edge {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hF : ∀ x : Fin (p + l) → Bool,
      wireFn (p + l) C C.output x = decide (∃ (a : Fin p) (b : Fin l),
        (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hE : E.Nonempty) : C.output < p + l + C.gates.length := by
  obtain ⟨⟨a,b⟩, hab⟩ := hE
  have ht : wireFn (p+l) C C.output (fun _ => true) = true := by
    rw [hF, decide_eq_true_eq]
    exact ⟨a,b,hab,rfl,rfl⟩
  by_contra hn
  rw [wireFn_ge (p+l) C C.output (Nat.le_of_not_lt hn)] at ht
  cases ht

lemma left_star_bound {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hC : IsAO2 (p+l) C)
    (hF : ∀ x : Fin (p + l) → Bool,
      wireFn (p + l) C C.output x = decide (∃ (a : Fin p) (b : Fin l),
        (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (a0 : Fin p) (hstar : ∀ e ∈ E, e.1 = a0) :
    ∃ S : Finset (Fin (p+l)),
      (∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  by_cases hE : E = ∅
  · subst E
    exact ⟨∅, by simp, by simp⟩
  have hne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
  obtain ⟨⟨a,b⟩, hab⟩ := hne
  have ha : a = a0 := hstar (a,b) hab
  have hc := (edge_endpoint_essential E C hF a b hab).1
  simp only [ha] at hc
  let L : Finset (Fin (p+l)) := E.image fun e => Fin.natAdd p e.2
  have hL : L ⊆ essentialSupport (p+l) C C.output := by
    intro k hk
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hk
    exact (edge_endpoint_essential E C hF e.1 e.2 he).2
  have hnot : Fin.castAdd l a0 ∉ L := by
    intro hk
    obtain ⟨e, he, hk⟩ := Finset.mem_image.mp hk
    exact castAdd_ne_natAdd a0 e.2 hk.symm
  have hcardL : L.card = E.card := by
    apply Finset.card_image_iff.mpr
    intro e he e' he' hee
    apply Prod.ext
    · exact (hstar e he).trans (hstar e' he').symm
    · apply Fin.ext
      have hee' := congrArg Fin.val hee
      simpa only [Fin.val_natAdd, Nat.add_left_cancel_iff] using hee'
  have hsub : insert (Fin.castAdd l a0) L ⊆ essentialSupport (p+l) C C.output :=
    Finset.insert_subset_iff.mpr ⟨hc,hL⟩
  have hb := (Finset.card_le_card hsub).trans
    (essentialSupport_count (p+l) C hC C.output (output_valid_of_edge E C hF (Finset.nonempty_iff_ne_empty.mpr hE)))
  rw [Finset.card_insert_of_notMem hnot, hcardL] at hb
  refine ⟨{Fin.castAdd l a0}, ?_, ?_⟩
  · intro a' b' hab'
    left
    have ha' : a' = a0 := hstar (a',b') hab'
    simp only [Finset.mem_singleton, ha']
  · simpa using hb

end PEqualNP.Outside.L_meta_4970_aux


namespace PEqualNP.Outside.L_meta_4970_aux.CofactorBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SemanticSafe

def forceTrue {n : ℕ} (U : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ U then true else x i

def support (n : ℕ) (C : Circuit) (U : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ x : Fin n → Bool,
    wireFn n C w (forceTrue U (Function.update x i false)) ≠
      wireFn n C w (forceTrue U (Function.update x i true))

lemma mem_support (n : ℕ) (C : Circuit) (U : Finset (Fin n)) (w : ℕ) (i : Fin n) :
    i ∈ support n C U w ↔ ∃ x : Fin n → Bool,
      wireFn n C w (forceTrue U (Function.update x i false)) ≠
        wireFn n C w (forceTrue U (Function.update x i true)) := by
  simp [support]

lemma support_input (n : ℕ) (C : Circuit) (U : Finset (Fin n)) (w : ℕ) (hw : w < n) :
    support n C U w ⊆ {⟨w, hw⟩} := by
  intro i hi
  rw [Finset.mem_singleton]
  obtain ⟨x, hx⟩ := (mem_support n C U w i).mp hi
  by_contra hne
  apply hx
  simp only [wireFn_input n C w hw, forceTrue]
  simp [Function.update_of_ne (Ne.symm hne)]

lemma support_binary (n : ℕ) (C : Circuit) (U : Finset (Fin n))
    (w a b : ℕ) (op : GateOp)
    (he : ∀ x, wireFn n C w x = op.eval [wireFn n C a x, wireFn n C b x]) :
    support n C U w ⊆ support n C U a ∪ support n C U b := by
  intro i hi
  by_contra hn
  have ha : i ∉ support n C U a := fun h => hn (Finset.mem_union_left _ h)
  have hb : i ∉ support n C U b := fun h => hn (Finset.mem_union_right _ h)
  have hA : ∀ x, wireFn n C a (forceTrue U (Function.update x i false)) =
      wireFn n C a (forceTrue U (Function.update x i true)) := by
    intro x
    by_contra hne
    exact ha ((mem_support n C U a i).mpr ⟨x, hne⟩)
  have hB : ∀ x, wireFn n C b (forceTrue U (Function.update x i false)) =
      wireFn n C b (forceTrue U (Function.update x i true)) := by
    intro x
    by_contra hne
    exact hb ((mem_support n C U b i).mpr ⟨x, hne⟩)
  obtain ⟨x, hx⟩ := (mem_support n C U w i).mp hi
  apply hx
  rw [he, he, hA x, hB x]

def erased (n : ℕ) (C : Circuit) (U : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.gates.length)).filter fun w =>
    support n C U w = ∅ ∨ ∃ a ∈ (gateAt C (w - n)).inputs, support n C U a = ∅

lemma budget (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (U : Finset (Fin n))
    (w : ℕ) (hw : w < n + C.gates.length) :
    (support n C U w).card + (erased n C U).card ≤ C.size + 1 := by
  classical
  have hs : ∀ k, k < n + C.gates.length → (support n C U k).card ≤ 1 ∨
      (∃ a, a < k ∧ a < n + C.gates.length ∧ support n C U k ⊆ support n C U a) ∨
      (k ∉ erased n C U ∧ ∃ a b, a < k ∧ b < k ∧
        a < n + C.gates.length ∧ b < n + C.gates.length ∧
        support n C U k ⊆ support n C U a ∪ support n C U b) := by
    intro k hk
    by_cases hsmall : (support n C U k).card ≤ 1
    · exact Or.inl hsmall
    right
    have hn : n ≤ k := by
      by_contra hnot
      have hc := Finset.card_le_card (support_input n C U k (by omega))
      simp only [Finset.card_singleton] at hc
      exact hsmall hc
    have hj : k - n < C.gates.length := by omega
    have heq : n + (k - n) = k := by omega
    obtain ⟨a,b,ha,hb,hab,hop,he⟩ := binary_gate n C hC (k-n) hj
    rw [heq] at ha hb he
    have hsub := support_binary n C U k a b _ he
    by_cases her : k ∈ erased n C U
    · left
      have hz := (Finset.mem_filter.mp her).2
      rcases hz with hz | ⟨v,hv,hv0⟩
      · exfalso
        apply hsmall
        simp [hz]
      · rw [hab] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact ⟨b,hb,by omega,by simpa [hv0] using hsub⟩
        · exact ⟨a,ha,by omega,by simpa [hv0] using hsub⟩
    · exact Or.inr ⟨her,a,b,ha,hb,by omega,by omega,hsub⟩
  have hc := safe_leaf_count (fun k => k < n + C.gates.length)
    (fun k => k ∉ erased n C U) (support n C U) hs (n+C.gates.length) {w}
      (by simpa using And.intro hw hw)
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
  let K := (Finset.range (n+C.gates.length)).filter fun k =>
    k < n+C.gates.length ∧ k ∉ erased n C U ∧ 2 ≤ (support n C U k).card
  have hsub : K ⊆ (Finset.Ico n (n+C.gates.length)) \ erased n C U := by
    intro k hk
    simp only [K,Finset.mem_filter,Finset.mem_range] at hk
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr ⟨?_,hk.1⟩,hk.2.2.1⟩
    by_contra hnot
    have hle := Finset.card_le_card (support_input n C U k (by omega))
    simp only [Finset.card_singleton] at hle
    omega
  have hcard := Finset.card_le_card hsub
  have her : erased n C U ⊆ Finset.Ico n (n+C.gates.length) := Finset.filter_subset _ _
  have hpart := Finset.card_sdiff_add_card_eq_card her
  simp only [Nat.card_Ico,Nat.add_sub_cancel_left] at hpart
  change (support n C U w).card ≤ 1+K.card at hc
  unfold Circuit.size
  omega

lemma support_empty_of_constant (n : ℕ) (C : Circuit) (U : Finset (Fin n))
    (w : ℕ) (v : Bool) (hc : ∀ x, wireFn n C w (forceTrue U x) = v) :
    support n C U w = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  obtain ⟨x,hx⟩ := (mem_support n C U w i).mp hi
  exact hx ((hc _).trans (hc _).symm)

lemma pureOr_erased (n : ℕ) (C : Circuit) (U Q : Finset (Fin n))
    (w : ℕ) (hw : w ∈ Finset.Ico n (n+C.gates.length))
    (hq : (Q ∩ U).Nonempty) (hp : PureOr Q (wireFn n C w)) :
    w ∈ erased n C U := by
  apply Finset.mem_filter.mpr
  refine ⟨hw,Or.inl (support_empty_of_constant n C U w true ?_)⟩
  intro x
  rw [hp]
  obtain ⟨i,hi⟩ := hq
  exact ⟨i,(Finset.mem_inter.mp hi).1,by simp [forceTrue,(Finset.mem_inter.mp hi).2]⟩

end PEqualNP.Outside.L_meta_4970_aux.CofactorBudget
