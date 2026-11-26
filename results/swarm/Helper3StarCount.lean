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

namespace PEqualNP.Outside.L_meta_4970.Connectivity

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

def Connects (F : SimpleGraph α) (S : Finset α) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, F.Reachable u v

omit [Fintype α] [DecidableEq α] in
lemma connects_mono {F F' : SimpleGraph α} {S : Finset α}
    (h : Connects F S) (hF : F ≤ F') : Connects F' S :=
  fun u hu v hv => (h u hu v hv).mono hF

omit [Fintype α] [DecidableEq α] in
lemma connects_subset {F : SimpleGraph α} {S T : Finset α}
    (h : Connects F T) (hST : S ⊆ T) : Connects F S :=
  fun u hu v hv => h u (hST hu) v (hST hv)

omit [Fintype α] [DecidableEq α] in
lemma connects_of_card_le_one (F : SimpleGraph α) (S : Finset α)
    (h : S.card ≤ 1) : Connects F S := by
  intro u hu v hv
  have he := Finset.card_le_one.mp h u hu v hv
  subst v
  exact SimpleGraph.Reachable.rfl

lemma union_bridge (F : SimpleGraph α) (A B : Finset α)
    (hA : Connects F A) (hB : Connects F B) :
    ∃ F' : SimpleGraph α, F ≤ F' ∧
      F'.edgeFinset.card ≤ F.edgeFinset.card + 1 ∧ Connects F' (A ∪ B) := by
  classical
  by_cases ha : A.Nonempty
  · by_cases hb : B.Nonempty
    · obtain ⟨a, ha⟩ := ha
      obtain ⟨b, hb⟩ := hb
      let E : SimpleGraph α := SimpleGraph.fromEdgeSet {s(a, b)}
      have hE : E.edgeFinset.card ≤ 1 := by
        have hs : E.edgeFinset ⊆ {s(a, b)} := by
          intro e he
          simp only [E, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet,
            Set.mem_sdiff, Set.mem_singleton_iff] at he
          simpa using he.1
        have hc := Finset.card_le_card hs
        simpa using hc
      have hab : (F ⊔ E).Reachable a b := by
        by_cases he : a = b
        · subst b
          exact SimpleGraph.Reachable.rfl
        · have hed : E.Adj a b := by simp [E, SimpleGraph.fromEdgeSet_adj, he]
          exact hed.reachable.mono le_sup_right
      refine ⟨F ⊔ E, le_sup_left, ?_, ?_⟩
      · have hsub : (F ⊔ E).edgeFinset ⊆ F.edgeFinset ∪ E.edgeFinset := by
          intro e he
          simpa only [SimpleGraph.mem_edgeFinset, Finset.mem_union,
            SimpleGraph.edgeSet_sup, Set.mem_union] using he
        have hc := Finset.card_le_card hsub
        have hu := Finset.card_union_le F.edgeFinset E.edgeFinset
        simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hE hc hu ⊢
        omega
      · intro u hu v hv
        rcases Finset.mem_union.mp hu with hu | hu <;>
          rcases Finset.mem_union.mp hv with hv | hv
        · exact (hA u hu v hv).mono le_sup_left
        · exact ((hA u hu a ha).mono le_sup_left).trans
            (hab.trans ((hB b hb v hv).mono le_sup_left))
        · exact ((hB u hu b hb).mono le_sup_left).trans
            (hab.symm.trans ((hA a ha v hv).mono le_sup_left))
        · exact (hB u hu v hv).mono le_sup_left
    · have hb : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
      refine ⟨F, le_rfl, by omega, ?_⟩
      simpa [hb] using hA
  · have ha : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    refine ⟨F, le_rfl, by omega, ?_⟩
    simpa [ha] using hB

lemma support_graph (safe split : ℕ → Prop) [DecidablePred safe] [DecidablePred split]
    (T : ℕ → Finset α)
    (h : ∀ w, safe w → (T w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe a ∧ T w ⊆ T a) ∨
      (split w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ T w ⊆ T a ∪ T b)) :
    ∀ M, ∃ F : SimpleGraph α,
      F.edgeFinset.card ≤
        ((Finset.range M).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card)).card ∧
      ∀ w < M, safe w → Connects F (T w) := by
  classical
  intro M
  induction M with
  | zero =>
    refine ⟨⊥, by simp, ?_⟩
    intro w hw
    exact False.elim (Nat.not_lt_zero w hw)
  | succ M ih =>
    obtain ⟨F, hF, hconn⟩ := ih
    let K := (Finset.range M).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card)
    let K' := (Finset.range (M + 1)).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card)
    change F.edgeFinset.card ≤ K.card at hF
    have hK : K.card ≤ K'.card := by
      apply Finset.card_le_card
      intro k hk
      simp only [K, K', Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨Nat.lt_succ_of_lt hk.1, hk.2⟩
    have keep : Connects F (T M) →
        ∃ F' : SimpleGraph α, F'.edgeFinset.card ≤ K'.card ∧
          ∀ w < M + 1, safe w → Connects F' (T w) := by
      intro hnew
      refine ⟨F, hF.trans hK, ?_⟩
      intro w hw hs
      by_cases he : w = M
      · simpa [he] using hnew
      · exact hconn w (by omega) hs
    by_cases hs : safe M
    · by_cases hsmall : (T M).card ≤ 1
      · exact keep (connects_of_card_le_one F (T M) hsmall)
      · rcases h M hs with hsmall' | hb | ⟨hm, a, b, ha, hb, hsa, hsb, hT⟩
        · exact False.elim (hsmall hsmall')
        · obtain ⟨a, ha, hsa, hT⟩ := hb
          exact keep (connects_subset (hconn a ha hsa) hT)
        · obtain ⟨F', hFF', hcard, hnew⟩ :=
            union_bridge F (T a) (T b) (hconn a ha hsa) (hconn b hb hsb)
          have hKe : K' = insert M K := by
            dsimp [K, K']
            rw [Finset.range_add_one, Finset.filter_insert, ite_eq_left]
            exact ⟨hs, hm, by omega⟩
          have hKc : K'.card = K.card + 1 := by
            rw [hKe, Finset.card_insert_of_notMem]
            simp [K]
          refine ⟨F', by change _ ≤ K'.card; omega, ?_⟩
          intro w hw hsw
          by_cases he : w = M
          · subst w
            exact connects_subset hnew hT
          · exact connects_mono (hconn w (by omega) hsw) hFF'
    · refine ⟨F, hF.trans hK, ?_⟩
      intro w hw hsw
      have he : w ≠ M := fun he => hs (he ▸ hsw)
      exact hconn w (by omega) hsw

lemma connected_frontier_count (safe split : ℕ → Prop)
    [DecidablePred safe] [DecidablePred split] (T : ℕ → Finset α)
    (h : ∀ w, safe w → (T w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe a ∧ T w ⊆ T a) ∨
      (split w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ T w ⊆ T a ∪ T b))
    (M : ℕ) (W : Finset ℕ) (hW : ∀ w ∈ W, w < M ∧ safe w)
    (hc : ∀ u v : α, Relation.ReflTransGen
      (fun a b => ∃ w ∈ W, a ∈ T w ∧ b ∈ T w) u v) :
    Fintype.card α ≤ 1 +
      ((Finset.range M).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card)).card := by
  classical
  obtain ⟨F, hF, hconn⟩ := support_graph safe split T h M
  have hpre : F.Preconnected := by
    intro u v
    have huv := hc u v
    induction huv with
    | refl => exact SimpleGraph.Reachable.rfl
    | @tail v z hvz hz ih =>
      obtain ⟨w, hw, hv, hz⟩ := hz
      exact ih.trans (hconn w (hW w hw).1 (hW w hw).2 v hv z hz)
  by_cases hn : Nonempty α
  · let := hn
    have hconnected : F.Connected := ⟨hpre⟩
    have hcF := hconnected.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at hcF
    omega
  · have hzero : Fintype.card α = 0 := Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hn)
    simp [hzero]

omit [Fintype α] in
lemma connected_subset_frontier_count (safe split : ℕ → Prop)
    [DecidablePred safe] [DecidablePred split] (T : ℕ → Finset α)
    (h : ∀ w, safe w → (T w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe a ∧ T w ⊆ T a) ∨
      (split w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ T w ⊆ T a ∪ T b))
    (M : ℕ) (W : Finset ℕ) (hW : ∀ w ∈ W, w < M ∧ safe w) (U : Finset α)
    (hc : ∀ u v : U, Relation.ReflTransGen
      (fun a b : U => ∃ w ∈ W, (a : α) ∈ T w ∧ (b : α) ∈ T w) u v) :
    U.card ≤ 1 +
      ((Finset.range M).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card)).card := by
  classical
  let T' : ℕ → Finset U := fun w => (T w).subtype (fun a => a ∈ U)
  have hcard : ∀ w, (T' w).card ≤ (T w).card := by
    intro w
    exact (Finset.card_subtype _ _).le.trans (Finset.card_filter_le _ _)
  have hstruct : ∀ w, safe w → (T' w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe a ∧ T' w ⊆ T' a) ∨
      (split w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ T' w ⊆ T' a ∪ T' b) := by
    intro w hw
    rcases h w hw with hs | ⟨a, ha, hsa, hTa⟩ | ⟨hsp, a, b, ha, hb, hsa, hsb, hTab⟩
    · exact Or.inl ((hcard w).trans hs)
    · right; left
      refine ⟨a, ha, hsa, ?_⟩
      intro x hx
      exact Finset.mem_subtype.mpr (hTa (Finset.mem_subtype.mp hx))
    · right; right
      refine ⟨hsp, a, b, ha, hb, hsa, hsb, ?_⟩
      intro x hx
      have hxab := hTab (Finset.mem_subtype.mp hx)
      rcases Finset.mem_union.mp hxab with hxa | hxb
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_subtype.mpr hxa))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_subtype.mpr hxb))
  have hc' : ∀ u v : U, Relation.ReflTransGen
      (fun a b => ∃ w ∈ W, a ∈ T' w ∧ b ∈ T' w) u v := by
    simpa only [T', Finset.mem_subtype] using hc
  have hb := connected_frontier_count safe split T' hstruct M W hW hc'
  have hcount : ((Finset.range M).filter
      (fun k => safe k ∧ split k ∧ 2 ≤ (T' k).card)).card ≤
      ((Finset.range M).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card)).card := by
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.trans (hcard k)⟩
  simpa only [Fintype.card_coe] using hb.trans (Nat.add_le_add_left hcount 1)

end PEqualNP.Outside.L_meta_4970.Connectivity

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SemanticSafe
open PEqualNP.Outside.L_meta_4970.Connectivity

lemma connected_star_or_count (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (W : Finset ℕ)
    (hW : ∀ w ∈ W, w < n + C.gates.length ∧ Safe Q (wireFn n C w))
    (hc : ∀ u v : Q, Relation.ReflTransGen
      (fun a b : Q => ∃ w ∈ W,
        (a : Fin n) ∈ singletonSupport n C w ∧ (b : Fin n) ∈ singletonSupport n C w) u v) :
    Q.card ≤ 1 + (chargedOr n C Q).card := by
  classical
  exact connected_subset_frontier_count
    (fun k => k < n + C.gates.length ∧ Safe Q (wireFn n C k))
    (fun k => n ≤ k ∧ (gateAt C (k - n)).op = GateOp.or)
    (singletonSupport n C) (safe_singleton_structure n C hC Q)
    (n + C.gates.length) W (fun w hw => ⟨(hW w hw).1, hW w hw⟩) Q hc

lemma connected_star_family_or_count {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (Q : ι → Finset (Fin n)) (W : ι → Finset ℕ)
    (hW : ∀ i ∈ I, ∀ w ∈ W i,
      w < n + C.gates.length ∧ Safe (Q i) (wireFn n C w))
    (hc : ∀ i ∈ I, ∀ u v : Q i, Relation.ReflTransGen
      (fun a b : Q i => ∃ w ∈ W i,
        (a : Fin n) ∈ singletonSupport n C w ∧ (b : Fin n) ∈ singletonSupport n C w) u v)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (Q i ∩ Q j).card ≤ 1) :
    (∑ i ∈ I, (Q i).card) ≤ I.card + (allOrWires n C).card := by
  classical
  have hlocal : ∑ i ∈ I, (Q i).card ≤
      ∑ i ∈ I, (1 + (chargedOr n C (Q i)).card) := by
    apply Finset.sum_le_sum
    intro i hi
    exact connected_star_or_count n C hC (Q i) (W i) (hW i hi) (hc i hi)
  have hd : (I : Set ι).PairwiseDisjoint (fun i => chargedOr n C (Q i)) := by
    intro i hi j hj hij
    exact chargedOr_disjoint n C (Q i) (Q j) (hinter i hi j hj hij)
  have hsub : I.biUnion (fun i => chargedOr n C (Q i)) ⊆ allOrWires n C := by
    intro k hk
    obtain ⟨i, hi, hk⟩ := Finset.mem_biUnion.mp hk
    simp only [chargedOr, Finset.mem_filter, Finset.mem_range] at hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hk.2.2.1.1, hk.1⟩, hk.2.2.1.2⟩
  have hsum : (∑ i ∈ I, (chargedOr n C (Q i)).card) ≤ (allOrWires n C).card := by
    rw [← Finset.card_biUnion hd]
    exact Finset.card_le_card hsub
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hlocal
  omega

end PEqualNP.Outside.L_meta_4970_aux


namespace PEqualNP.Outside.L_meta_4970.ComponentPartition

open Classical

variable {α ι : Type*} [DecidableEq α]

def CoOccurs (I : Finset ι) (Q : ι → Finset α) (a b : α) : Prop :=
  ∃ i ∈ I, a ∈ Q i ∧ b ∈ Q i

def Reach (I : Finset ι) (Q : ι → Finset α) : α → α → Prop :=
  Relation.ReflTransGen (CoOccurs I Q)

omit [DecidableEq α] in
lemma reach_symm {I : Finset ι} {Q : ι → Finset α} {a b : α}
    (h : Reach I Q a b) : Reach I Q b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    obtain ⟨i, hi, hb, hc⟩ := hbc
    exact (Relation.ReflTransGen.single ⟨i, hi, hc, hb⟩).trans ih

lemma reach_in_union {I : Finset ι} {Q : ι → Finset α} {a b : α}
    (h : Reach I Q a b) (ha : a ∈ I.biUnion Q) : b ∈ I.biUnion Q := by
  induction h with
  | refl => exact ha
  | @tail b c hab hbc ih =>
    obtain ⟨i, hi, hb, hc⟩ := hbc
    exact Finset.mem_biUnion.mpr ⟨i, hi, hc⟩

noncomputable def component (I : Finset ι) (Q : ι → Finset α) (a : α) : Finset α :=
  (I.biUnion Q).filter (Reach I Q a)

noncomputable def parts (I : Finset ι) (Q : ι → Finset α) : Finset (Finset α) :=
  (I.biUnion Q).image (component I Q)

noncomputable def rootsInPart (I : Finset ι) (Q : ι → Finset α)
    (P : Finset α) : Finset ι := I.filter fun i => Q i ⊆ P

lemma mem_component (I : Finset ι) (Q : ι → Finset α) (a b : α) :
    b ∈ component I Q a ↔ b ∈ I.biUnion Q ∧ Reach I Q a b := by
  simp [component]

lemma component_subset_union (I : Finset ι) (Q : ι → Finset α) (a : α) :
    component I Q a ⊆ I.biUnion Q := Finset.filter_subset _ _

lemma mem_own_component (I : Finset ι) (Q : ι → Finset α) (a : α)
    (ha : a ∈ I.biUnion Q) : a ∈ component I Q a :=
  (mem_component I Q a a).mpr ⟨ha, Relation.ReflTransGen.refl⟩

lemma component_eq_of_reach (I : Finset ι) (Q : ι → Finset α) (a b : α)
    (hab : Reach I Q a b) : component I Q a = component I Q b := by
  ext v
  rw [mem_component, mem_component]
  constructor
  · rintro ⟨hv, hav⟩
    exact ⟨hv, (reach_symm hab).trans hav⟩
  · rintro ⟨hv, hbv⟩
    exact ⟨hv, hab.trans hbv⟩

lemma distinct_components_disjoint (I : Finset ι) (Q : ι → Finset α) (a b : α)
    (hne : component I Q a ≠ component I Q b) :
    Disjoint (component I Q a) (component I Q b) := by
  apply Finset.disjoint_left.mpr
  intro v hv₁ hv₂
  have hav := ((mem_component I Q a v).mp hv₁).2
  have hbv := ((mem_component I Q b v).mp hv₂).2
  exact hne (component_eq_of_reach I Q a b (hav.trans (reach_symm hbv)))

lemma parts_nonempty (I : Finset ι) (Q : ι → Finset α) :
    ∀ P ∈ parts I Q, P.Nonempty := by
  intro P hP
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hP
  exact ⟨a, mem_own_component I Q a ha⟩

lemma parts_pairwise_disjoint (I : Finset ι) (Q : ι → Finset α) :
    ∀ P ∈ parts I Q, ∀ R ∈ parts I Q, P ≠ R → Disjoint P R := by
  intro P hP R hR hne
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hR
  exact distinct_components_disjoint I Q a b hne

lemma parts_union (I : Finset ι) (Q : ι → Finset α) :
    (parts I Q).biUnion id = I.biUnion Q := by
  ext a
  constructor
  · intro ha
    obtain ⟨P, hP, ha⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
    exact component_subset_union I Q b ha
  · intro ha
    exact Finset.mem_biUnion.mpr
      ⟨component I Q a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, mem_own_component I Q a ha⟩

lemma root_subset_component (I : Finset ι) (Q : ι → Finset α)
    (a : α) (i : ι) (hi : i ∈ I)
    (hmeet : (Q i ∩ component I Q a).Nonempty) : Q i ⊆ component I Q a := by
  obtain ⟨b, hb⟩ := hmeet
  have hbi := (Finset.mem_inter.mp hb).1
  have hab := ((mem_component I Q a b).mp (Finset.mem_inter.mp hb).2).2
  intro v hv
  exact (mem_component I Q a v).mpr
    ⟨Finset.mem_biUnion.mpr ⟨i, hi, hv⟩,
      hab.trans (Relation.ReflTransGen.single ⟨i, hi, hbi, hv⟩)⟩

lemma component_connected (I : Finset ι) (Q : ι → Finset α) (a : α) :
    ∀ u v : component I Q a, Relation.ReflTransGen
      (fun x y : component I Q a => ∃ i ∈ I, Q i ⊆ component I Q a ∧
        (x : α) ∈ Q i ∧ (y : α) ∈ Q i) u v := by
  have lift : ∀ {x y : α}, Reach I Q x y → ∀ hx : x ∈ component I Q a,
      ∀ hy : y ∈ component I Q a, Relation.ReflTransGen
      (fun x y : component I Q a => ∃ i ∈ I, Q i ⊆ component I Q a ∧
        (x : α) ∈ Q i ∧ (y : α) ∈ Q i) ⟨x, hx⟩ ⟨y, hy⟩ := by
    intro x y hxy
    induction hxy with
    | refl =>
      intro hx hy
      exact Relation.ReflTransGen.refl
    | @tail y z hxy hyz ih =>
      intro hx hz
      have hy : y ∈ component I Q a := by
        have hax := (mem_component I Q a x).mp hx
        exact (mem_component I Q a y).mpr
          ⟨reach_in_union hxy hax.1, hax.2.trans hxy⟩
      obtain ⟨i, hi, hyi, hzi⟩ := hyz
      have hsub : Q i ⊆ component I Q a :=
        root_subset_component I Q a i hi ⟨y, Finset.mem_inter.mpr ⟨hyi, hy⟩⟩
      exact (ih hx hy).tail ⟨i, hi, hsub, hyi, hzi⟩
  intro u v
  have hau := ((mem_component I Q a u).mp u.property).2
  have hav := ((mem_component I Q a v).mp v.property).2
  exact lift ((reach_symm hau).trans hav) u.property v.property

lemma partition_certificate (I : Finset ι) (Q : ι → Finset α) :
    ∃ P : Finset (Finset α),
      (∀ S ∈ P, S.Nonempty) ∧
      P.biUnion id = I.biUnion Q ∧
      (∀ S ∈ P, ∀ T ∈ P, S ≠ T → Disjoint S T) ∧
      ∀ S ∈ P,
        (∀ i ∈ I, (Q i ∩ S).Nonempty → Q i ⊆ S) ∧
        ∀ u v : S, Relation.ReflTransGen
          (fun a b : S => ∃ i ∈ I, Q i ⊆ S ∧ (a : α) ∈ Q i ∧ (b : α) ∈ Q i) u v := by
  refine ⟨parts I Q, parts_nonempty I Q, parts_union I Q, parts_pairwise_disjoint I Q, ?_⟩
  intro S hS
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hS
  exact ⟨fun i hi => root_subset_component I Q a i hi, component_connected I Q a⟩

lemma part_subset_union (I : Finset ι) (Q : ι → Finset α)
    (P : Finset α) (hP : P ∈ parts I Q) : P ⊆ I.biUnion Q := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hP
  exact component_subset_union I Q a

lemma root_subset_part (I : Finset ι) (Q : ι → Finset α)
    (P : Finset α) (hP : P ∈ parts I Q) (i : ι) (hi : i ∈ I)
    (hmeet : (Q i ∩ P).Nonempty) : Q i ⊆ P := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hP
  exact root_subset_component I Q a i hi hmeet

lemma root_part_existsUnique (I : Finset ι) (Q : ι → Finset α)
    (i : ι) (hi : i ∈ I) (hQi : (Q i).Nonempty) :
    ∃! P : Finset α, P ∈ parts I Q ∧ Q i ⊆ P := by
  obtain ⟨a, ha⟩ := hQi
  have haU : a ∈ I.biUnion Q := Finset.mem_biUnion.mpr ⟨i, hi, ha⟩
  have haP := mem_own_component I Q a haU
  have hP : component I Q a ∈ parts I Q := Finset.mem_image.mpr ⟨a, haU, rfl⟩
  refine ⟨component I Q a, ⟨hP, ?_⟩, ?_⟩
  · exact root_subset_component I Q a i hi ⟨a, Finset.mem_inter.mpr ⟨ha, haP⟩⟩
  · intro R hR
    by_contra hne
    have hd := parts_pairwise_disjoint I Q R hR.1 (component I Q a) hP hne
    exact Finset.disjoint_left.mp hd (hR.2 ha) haP

lemma part_roots_union (I : Finset ι) (Q : ι → Finset α)
    (P : Finset α) (hP : P ∈ parts I Q) :
    (rootsInPart I Q P).biUnion Q = P := by
  ext a
  constructor
  · intro ha
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
    exact (Finset.mem_filter.mp hi).2 hai
  · intro ha
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp (part_subset_union I Q P hP ha)
    have hs := root_subset_part I Q P hP i hi ⟨a, Finset.mem_inter.mpr ⟨hai, ha⟩⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hs⟩, hai⟩

lemma part_roots_connected (I : Finset ι) (Q : ι → Finset α)
    (P : Finset α) (hP : P ∈ parts I Q) :
    ∀ u v : P, Relation.ReflTransGen
      (fun a b : P => ∃ i ∈ rootsInPart I Q P, (a : α) ∈ Q i ∧ (b : α) ∈ Q i) u v := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hP
  simpa only [rootsInPart, Finset.mem_filter, and_assoc] using component_connected I Q a

lemma parts_sum_card (I : Finset ι) (Q : ι → Finset α) :
    (∑ P ∈ parts I Q, P.card) = (I.biUnion Q).card := by
  have hd : (parts I Q : Set (Finset α)).PairwiseDisjoint id := by
    intro P hP R hR hne
    exact parts_pairwise_disjoint I Q P hP R hR hne
  change (∑ P ∈ parts I Q, (id P).card) = _
  rw [← Finset.card_biUnion hd, parts_union]

lemma parts_card_at_least_two (I : Finset ι) (Q : ι → Finset α)
    (hQ : ∀ i ∈ I, 2 ≤ (Q i).card) :
    ∀ P ∈ parts I Q, 2 ≤ P.card := by
  intro P hP
  obtain ⟨a, ha⟩ := parts_nonempty I Q P hP
  obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp (part_subset_union I Q P hP ha)
  have hs := root_subset_part I Q P hP i hi ⟨a, Finset.mem_inter.mpr ⟨hai, ha⟩⟩
  exact (hQ i hi).trans (Finset.card_le_card hs)

lemma parts_inter_card_le_one {κ : Type*}
    (K : Finset κ) (I : κ → Finset ι) (Q : κ → ι → Finset α)
    (hinter : ∀ c ∈ K, ∀ d ∈ K, c ≠ d →
      ((I c).biUnion (Q c) ∩ (I d).biUnion (Q d)).card ≤ 1) :
    ∀ c ∈ K, ∀ P ∈ parts (I c) (Q c),
      ∀ d ∈ K, ∀ R ∈ parts (I d) (Q d),
      (c, P) ≠ (d, R) → (P ∩ R).card ≤ 1 := by
  intro c hc P hP d hd R hR hne
  by_cases hcd : c = d
  · subst d
    have hPR : P ≠ R := fun he => hne (by rw [he])
    have hdis := parts_pairwise_disjoint (I c) (Q c) P hP R hR hPR
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdis]
    simp
  · have hsub : P ∩ R ⊆ (I c).biUnion (Q c) ∩ (I d).biUnion (Q d) :=
      Finset.inter_subset_inter (part_subset_union (I c) (Q c) P hP)
        (part_subset_union (I d) (Q d) R hR)
    exact (Finset.card_le_card hsub).trans (hinter c hc d hd hcd)

end PEqualNP.Outside.L_meta_4970.ComponentPartition

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SemanticSafe
open PEqualNP.Outside.L_meta_4970.ComponentPartition

lemma component_star_family_or_count {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (W : ι → Finset ℕ)
    (hW : ∀ i ∈ I, ∀ w ∈ W i, w < n + C.gates.length ∧
      PureOr (singletonSupport n C w) (wireFn n C w))
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ((W i).biUnion (singletonSupport n C) ∩
        (W j).biUnion (singletonSupport n C)).card ≤ 1) :
    (∑ i ∈ I, ((W i).biUnion (singletonSupport n C)).card) ≤
      (∑ i ∈ I, (parts (W i) (singletonSupport n C)).card) +
        (allOrWires n C).card := by
  classical
  let J := I.sigma fun i => parts (W i) (singletonSupport n C)
  let V : (Σ _ : ι, Finset (Fin n)) → Finset (Fin n) := fun j => j.2
  let R : (Σ _ : ι, Finset (Fin n)) → Finset ℕ := fun j =>
    rootsInPart (W j.1) (singletonSupport n C) j.2
  have hr : ∀ j ∈ J, ∀ w ∈ R j,
      w < n + C.gates.length ∧ Safe (V j) (wireFn n C w) := by
    intro j hj w hw
    obtain ⟨hi, hP⟩ := Finset.mem_sigma.mp hj
    obtain ⟨hwW, hwP⟩ := Finset.mem_filter.mp hw
    refine ⟨(hW j.1 hi w hwW).1, ?_⟩
    intro x hx
    obtain ⟨a, ha, hxa⟩ := (hW j.1 hi w hwW).2 x |>.mp hx
    exact ⟨a, hwP ha, hxa⟩
  have hc : ∀ j ∈ J, ∀ u v : V j, Relation.ReflTransGen
      (fun a b : V j => ∃ w ∈ R j,
        (a : Fin n) ∈ singletonSupport n C w ∧
          (b : Fin n) ∈ singletonSupport n C w) u v := by
    intro j hj
    exact part_roots_connected (W j.1) (singletonSupport n C) j.2
      (Finset.mem_sigma.mp hj).2
  have hi : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → (V j ∩ V k).card ≤ 1 := by
    intro j hj k hk hne
    have hp : (j.1, j.2) ≠ (k.1, k.2) := by
      intro he
      cases j with
      | mk a P =>
        cases k with
        | mk b Q =>
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact hne rfl
    exact parts_inter_card_le_one I W (fun _ => singletonSupport n C) hinter
      j.1 (Finset.mem_sigma.mp hj).1 j.2 (Finset.mem_sigma.mp hj).2
      k.1 (Finset.mem_sigma.mp hk).1 k.2 (Finset.mem_sigma.mp hk).2 hp
  have hh := connected_star_family_or_count n C hC J V R hr hc hi
  simpa only [J, V, Finset.sum_sigma, Finset.card_sigma, parts_sum_card] using hh

end PEqualNP.Outside.L_meta_4970_aux

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SemanticSafe
open PEqualNP.Outside.L_meta_4970.Connectivity
open PEqualNP.Outside.L_meta_4970.ComponentPartition

/-- A support may be carried for free by any earlier safe wire containing it. -/
def HasSafeCarrier (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) (w : ℕ) : Prop :=
  ∃ a, a < w ∧ (a < n + C.gates.length ∧ Safe Q (wireFn n C a)) ∧
    singletonSupport n C w ⊆ singletonSupport n C a

noncomputable def productiveOr (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (chargedOr n C Q).filter fun w => ¬ HasSafeCarrier n C Q w

lemma productiveOr_subset (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) :
    productiveOr n C Q ⊆ chargedOr n C Q := by
  classical
  exact Finset.filter_subset _ _

lemma productiveOr_disjoint (n : ℕ) (C : Circuit) (Q R : Finset (Fin n))
    (h : (Q ∩ R).card ≤ 1) :
    Disjoint (productiveOr n C Q) (productiveOr n C R) :=
  Finset.disjoint_of_subset_left (productiveOr_subset n C Q)
    (Finset.disjoint_of_subset_right (productiveOr_subset n C R)
      (chargedOr_disjoint n C Q R h))

lemma productiveOr_no_carrier (n : ℕ) (C : Circuit) (Q : Finset (Fin n))
    (w : ℕ) (hw : w ∈ productiveOr n C Q)
    (a : ℕ) (ha : a < w) (ha' : a < n + C.gates.length)
    (hs : Safe Q (wireFn n C a)) :
    ¬ singletonSupport n C w ⊆ singletonSupport n C a := by
  classical
  intro hsub
  exact (Finset.mem_filter.mp hw).2 ⟨a, ha, ⟨ha', hs⟩, hsub⟩

lemma productive_singleton_structure (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) :
    ∀ w, (w < n + C.gates.length ∧ Safe Q (wireFn n C w)) →
      (singletonSupport n C w).card ≤ 1 ∨
      (∃ a, a < w ∧ (a < n + C.gates.length ∧ Safe Q (wireFn n C a)) ∧
        singletonSupport n C w ⊆ singletonSupport n C a) ∨
      (((n ≤ w ∧ (gateAt C (w - n)).op = GateOp.or) ∧
          ¬ HasSafeCarrier n C Q w) ∧
        ∃ a b, a < w ∧ b < w ∧
          (a < n + C.gates.length ∧ Safe Q (wireFn n C a)) ∧
          (b < n + C.gates.length ∧ Safe Q (wireFn n C b)) ∧
          singletonSupport n C w ⊆ singletonSupport n C a ∪ singletonSupport n C b) := by
  classical
  intro w hw
  by_cases hcarry : HasSafeCarrier n C Q w
  · exact Or.inr (Or.inl hcarry)
  · rcases safe_singleton_structure n C hC Q w hw with hsmall | hfree | ⟨hop, hsplit⟩
    · exact Or.inl hsmall
    · exact False.elim (hcarry hfree)
    · exact Or.inr (Or.inr ⟨⟨hop, hcarry⟩, hsplit⟩)

lemma productive_star_or_count (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (W : Finset ℕ)
    (hW : ∀ w ∈ W, w < n + C.gates.length ∧ Safe Q (wireFn n C w))
    (hc : ∀ u v : Q, Relation.ReflTransGen
      (fun a b : Q => ∃ w ∈ W,
        (a : Fin n) ∈ singletonSupport n C w ∧ (b : Fin n) ∈ singletonSupport n C w) u v) :
    Q.card ≤ 1 + (productiveOr n C Q).card := by
  classical
  have hh := connected_subset_frontier_count
    (fun k => k < n + C.gates.length ∧ Safe Q (wireFn n C k))
    (fun k => (n ≤ k ∧ (gateAt C (k - n)).op = GateOp.or) ∧
      ¬ HasSafeCarrier n C Q k)
    (singletonSupport n C) (productive_singleton_structure n C hC Q)
    (n + C.gates.length) W (fun w hw => ⟨(hW w hw).1, hW w hw⟩) Q hc
  have he : ((Finset.range (n + C.gates.length)).filter
      (fun k => (k < n + C.gates.length ∧ Safe Q (wireFn n C k)) ∧
        ((n ≤ k ∧ (gateAt C (k - n)).op = GateOp.or) ∧
          ¬ HasSafeCarrier n C Q k) ∧ 2 ≤ (singletonSupport n C k).card)) =
      productiveOr n C Q := by
    ext k
    simp only [productiveOr, chargedOr, Finset.mem_filter]
    tauto
  rwa [he] at hh

lemma productive_star_family_count {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (Q : ι → Finset (Fin n)) (W : ι → Finset ℕ)
    (hW : ∀ i ∈ I, ∀ w ∈ W i,
      w < n + C.gates.length ∧ Safe (Q i) (wireFn n C w))
    (hc : ∀ i ∈ I, ∀ u v : Q i, Relation.ReflTransGen
      (fun a b : Q i => ∃ w ∈ W i,
        (a : Fin n) ∈ singletonSupport n C w ∧ (b : Fin n) ∈ singletonSupport n C w) u v)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (Q i ∩ Q j).card ≤ 1) :
    (∑ i ∈ I, (Q i).card) ≤
      I.card + (I.biUnion fun i => productiveOr n C (Q i)).card := by
  classical
  have hlocal : ∑ i ∈ I, (Q i).card ≤
      ∑ i ∈ I, (1 + (productiveOr n C (Q i)).card) := by
    apply Finset.sum_le_sum
    intro i hi
    exact productive_star_or_count n C hC (Q i) (W i) (hW i hi) (hc i hi)
  have hd : (I : Set ι).PairwiseDisjoint (fun i => productiveOr n C (Q i)) := by
    intro i hi j hj hij
    exact productiveOr_disjoint n C (Q i) (Q j) (hinter i hi j hj hij)
  rw [Finset.card_biUnion hd]
  simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] using hlocal

lemma productive_family_subset_allOr {ι : Type*} (n : ℕ) (C : Circuit)
    (I : Finset ι) (Q : ι → Finset (Fin n)) :
    (I.biUnion fun i => productiveOr n C (Q i)) ⊆ allOrWires n C := by
  classical
  intro w hw
  obtain ⟨i, hi, hw⟩ := Finset.mem_biUnion.mp hw
  have hm := productiveOr_subset n C (Q i) hw
  simp only [chargedOr, Finset.mem_filter, Finset.mem_range] at hm
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hm.2.2.1.1, hm.1⟩, hm.2.2.1.2⟩

end PEqualNP.Outside.L_meta_4970_aux

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SemanticSafe
open PEqualNP.Outside.L_meta_4970.ComponentPartition

noncomputable def componentProductive {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (I : Finset ι) (W : ι → Finset ℕ) : Finset ℕ := by
  classical
  exact (I.sigma fun i => parts (W i) (singletonSupport n C)).biUnion
    fun j => productiveOr n C j.2

lemma component_productive_or_count {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (W : ι → Finset ℕ)
    (hW : ∀ i ∈ I, ∀ w ∈ W i, w < n + C.gates.length ∧
      PureOr (singletonSupport n C w) (wireFn n C w))
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ((W i).biUnion (singletonSupport n C) ∩
        (W j).biUnion (singletonSupport n C)).card ≤ 1) :
    (∑ i ∈ I, ((W i).biUnion (singletonSupport n C)).card) ≤
      (∑ i ∈ I, (parts (W i) (singletonSupport n C)).card) +
        (componentProductive n C I W).card := by
  classical
  let J := I.sigma fun i => parts (W i) (singletonSupport n C)
  let V : (Σ _ : ι, Finset (Fin n)) → Finset (Fin n) := fun j => j.2
  let R : (Σ _ : ι, Finset (Fin n)) → Finset ℕ := fun j =>
    rootsInPart (W j.1) (singletonSupport n C) j.2
  have hr : ∀ j ∈ J, ∀ w ∈ R j,
      w < n + C.gates.length ∧ Safe (V j) (wireFn n C w) := by
    intro j hj w hw
    obtain ⟨hi, hP⟩ := Finset.mem_sigma.mp hj
    obtain ⟨hwW, hwP⟩ := Finset.mem_filter.mp hw
    refine ⟨(hW j.1 hi w hwW).1, ?_⟩
    intro x hx
    obtain ⟨a, ha, hxa⟩ := (hW j.1 hi w hwW).2 x |>.mp hx
    exact ⟨a, hwP ha, hxa⟩
  have hc : ∀ j ∈ J, ∀ u v : V j, Relation.ReflTransGen
      (fun a b : V j => ∃ w ∈ R j,
        (a : Fin n) ∈ singletonSupport n C w ∧
          (b : Fin n) ∈ singletonSupport n C w) u v := by
    intro j hj
    exact part_roots_connected (W j.1) (singletonSupport n C) j.2
      (Finset.mem_sigma.mp hj).2
  have hi : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → (V j ∩ V k).card ≤ 1 := by
    intro j hj k hk hne
    have hp : (j.1, j.2) ≠ (k.1, k.2) := by
      intro he
      cases j with
      | mk a P =>
        cases k with
        | mk b Q =>
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact hne rfl
    exact parts_inter_card_le_one I W (fun _ => singletonSupport n C) hinter
      j.1 (Finset.mem_sigma.mp hj).1 j.2 (Finset.mem_sigma.mp hj).2
      k.1 (Finset.mem_sigma.mp hk).1 k.2 (Finset.mem_sigma.mp hk).2 hp
  have hh := productive_star_family_count n C hC J V R hr hc hi
  simpa only [componentProductive, J, V, Finset.sum_sigma, Finset.card_sigma, parts_sum_card] using hh


end PEqualNP.Outside.L_meta_4970_aux

namespace PEqualNP.Outside.L_meta_4970.ChosenForest

open Classical
open Connectivity

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
lemma bridge_support (F : SimpleGraph α) (A B S : Finset α)
    (hA : Connects F A) (hB : Connects F B) (hS : S ⊆ A ∪ B)
    (hnc : ¬ Connects F S) :
    ∃ u ∈ S, ∃ v ∈ S, ¬ F.Reachable u v ∧
      Connects (F ⊔ SimpleGraph.edge u v) S := by
  classical
  have cross : ∀ u ∈ S, ∀ v ∈ S, u ∈ A → v ∈ B → ¬ F.Reachable u v →
      Connects (F ⊔ SimpleGraph.edge u v) S := by
    intro u hu v hv huA hvB hn
    have hne : u ≠ v := fun he => hn (he ▸ SimpleGraph.Reachable.rfl)
    have hed : (SimpleGraph.edge u v).Adj u v := by simp [SimpleGraph.edge_adj, hne]
    have huv : (F ⊔ SimpleGraph.edge u v).Reachable u v := hed.reachable.mono le_sup_right
    intro x hx y hy
    rcases Finset.mem_union.mp (hS hx) with hxA | hxB <;>
      rcases Finset.mem_union.mp (hS hy) with hyA | hyB
    · exact (hA x hxA y hyA).mono le_sup_left
    · exact ((hA x hxA u huA).mono le_sup_left).trans
        (huv.trans ((hB v hvB y hyB).mono le_sup_left))
    · exact ((hB x hxB v hvB).mono le_sup_left).trans
        (huv.symm.trans ((hA u huA y hyA).mono le_sup_left))
    · exact (hB x hxB y hyB).mono le_sup_left
  dsimp [Connects] at hnc
  push Not at hnc
  obtain ⟨u, hu, v, hv, hn⟩ := hnc
  rcases Finset.mem_union.mp (hS hu) with huA | huB <;>
    rcases Finset.mem_union.mp (hS hv) with hvA | hvB
  · exact False.elim (hn (hA u huA v hvA))
  · exact ⟨u, hu, v, hv, hn, cross u hu v hv huA hvB hn⟩
  · have hnr : ¬ F.Reachable v u := fun hr => hn hr.symm
    exact ⟨v, hv, u, hu, hnr, cross v hv u hu hvA huB hnr⟩
  · exact False.elim (hn (hB u huB v hvB))


omit [Fintype α] in
lemma labelled_support_forest (safe split : ℕ → Prop) (T : ℕ → Finset α)
    (h : ∀ w, safe w → (T w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe a ∧ T w ⊆ T a) ∨
      (split w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ T w ⊆ T a ∪ T b)) :
    ∀ M, ∃ (F : SimpleGraph α) (label : Sym2 α → ℕ),
      F.IsAcyclic ∧ Set.InjOn label F.edgeSet ∧
      (∀ e ∈ F.edgeSet, label e < M ∧ safe (label e) ∧ split (label e) ∧
        2 ≤ (T (label e)).card ∧
        ∃ u ∈ T (label e), ∃ v ∈ T (label e), e = s(u, v)) ∧
      ∀ w < M, safe w → Connects F (T w) := by
  classical
  intro M
  induction M with
  | zero =>
    refine ⟨⊥, fun _ => 0, SimpleGraph.isAcyclic_bot, ?_, ?_, ?_⟩
    · intro e he
      simp at he
    · intro e he
      simp at he
    · intro w hw
      exact False.elim (Nat.not_lt_zero w hw)
  | succ M ih =>
    obtain ⟨F, label, hacyc, hinj, hlab, hconn⟩ := ih
    have keep : (safe M → Connects F (T M)) →
        ∃ (F' : SimpleGraph α) (label' : Sym2 α → ℕ),
          F'.IsAcyclic ∧ Set.InjOn label' F'.edgeSet ∧
          (∀ e ∈ F'.edgeSet, label' e < M + 1 ∧ safe (label' e) ∧ split (label' e) ∧
            2 ≤ (T (label' e)).card ∧
            ∃ u ∈ T (label' e), ∃ v ∈ T (label' e), e = s(u, v)) ∧
          ∀ w < M + 1, safe w → Connects F' (T w) := by
      intro hnew
      refine ⟨F, label, hacyc, hinj, ?_, ?_⟩
      · intro e he
        exact ⟨Nat.lt_succ_of_lt (hlab e he).1, (hlab e he).2⟩
      · intro w hw hsw
        by_cases he : w = M
        · subst w
          exact hnew hsw
        · exact hconn w (by omega) hsw
    by_cases hs : safe M
    · by_cases hc : Connects F (T M)
      · exact keep (fun _ => hc)
      · have hcard : 2 ≤ (T M).card := by
          by_contra hn
          exact hc (connects_of_card_le_one F (T M) (by omega))
        rcases h M hs with hsmall | hb | ⟨hsp, a, b, ha, hb, hsa, hsb, hT⟩
        · exact False.elim (hc (connects_of_card_le_one F (T M) hsmall))
        · obtain ⟨a, ha, hsa, hT⟩ := hb
          exact False.elim (hc (connects_subset (hconn a ha hsa) hT))
        · obtain ⟨u, hu, v, hv, hnreach, hnewconn⟩ :=
            bridge_support F (T a) (T b) (T M) (hconn a ha hsa) (hconn b hb hsb) hT hc
          have hne : u ≠ v := fun he => hnreach (he ▸ SimpleGraph.Reachable.rfl)
          have hnot : s(u, v) ∉ F.edgeSet := by
            intro he
            have hadj : F.Adj u v := by simpa using he
            exact hnreach hadj.reachable
          let label' : Sym2 α → ℕ := Function.update label s(u, v) M
          have hnew : label' s(u, v) = M := by simp [label']
          have hold : ∀ e ∈ F.edgeSet, label' e = label e := by
            intro e he
            have hne' : e ≠ s(u, v) := fun heq => hnot (heq ▸ he)
            simp [label', hne']
          have hsup : (F ⊔ SimpleGraph.edge u v).edgeSet = insert s(u, v) F.edgeSet := by
            rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge_of_ne hne]
            ext e
            simp
          refine ⟨F ⊔ SimpleGraph.edge u v, label',
            hacyc.sup_edge_of_not_reachable hnreach, ?_, ?_, ?_⟩
          · intro e he f hf heq
            rw [hsup] at he hf
            rcases Set.mem_insert_iff.mp he with rfl | he <;>
              rcases Set.mem_insert_iff.mp hf with rfl | hf
            · rfl
            · rw [hnew, hold f hf] at heq
              exact False.elim ((Nat.ne_of_lt (hlab f hf).1) heq.symm)
            · rw [hold e he, hnew] at heq
              exact False.elim ((Nat.ne_of_lt (hlab e he).1) heq)
            · rw [hold e he, hold f hf] at heq
              exact hinj he hf heq
          · intro e he
            rw [hsup] at he
            rcases Set.mem_insert_iff.mp he with rfl | he
            · rw [hnew]
              exact ⟨Nat.lt_succ_self M, hs, hsp, hcard, u, hu, v, hv, rfl⟩
            · rw [hold e he]
              exact ⟨Nat.lt_succ_of_lt (hlab e he).1, (hlab e he).2⟩
          · intro w hw hsw
            by_cases he : w = M
            · subst w
              exact hnewconn
            · exact connects_mono (hconn w (by omega) hsw) le_sup_left
    · exact keep (fun hsm => False.elim (hs hsm))


lemma chosen_support_forest (safe split : ℕ → Prop) [DecidablePred safe]
    [DecidablePred split] (T : ℕ → Finset α)
    (h : ∀ w, safe w → (T w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe a ∧ T w ⊆ T a) ∨
      (split w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ T w ⊆ T a ∪ T b))
    (M : ℕ) :
    ∃ (F : SimpleGraph α) (K : Finset ℕ) (label : Sym2 α → ℕ),
      F.IsAcyclic ∧ Set.InjOn label F.edgeSet ∧ K = F.edgeFinset.image label ∧
      K ⊆ (Finset.range M).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card) ∧
      K.card + Nat.card F.ConnectedComponent = Fintype.card α ∧
      (∀ e ∈ F.edgeSet, ∃ u ∈ T (label e), ∃ v ∈ T (label e), e = s(u, v)) ∧
      ∀ w < M, safe w → Connects F (T w) := by
  classical
  obtain ⟨F, label, hacyc, hinj, hlab, hconn⟩ := labelled_support_forest safe split T h M
  let K : Finset ℕ := F.edgeFinset.image label
  have hcard : K.card = F.edgeFinset.card := by
    apply Finset.card_image_of_injOn
    intro e he f hf hef
    exact hinj (by simpa using he) (by simpa using hf) hef
  have hedge : F.edgeSet.ncard = F.edgeFinset.card := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.edgeFinset_card]
  refine ⟨F, K, label, hacyc, hinj, rfl, ?_, ?_, ?_, hconn⟩
  · intro k hk
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hk
    have hp := hlab e (by simpa using he)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  · have hrank := hacyc.ncard_edgeSet_add_card_connectedComponent
    rw [hedge, ← hcard, @Nat.card_eq_fintype_card α _] at hrank
    exact hrank
  · intro e he
    exact (hlab e he).2.2.2.2

omit [DecidableEq α] in
lemma spanning_forest_certificate (G : SimpleGraph α) :
    ∃ F : SimpleGraph α, F ≤ G ∧ F.IsAcyclic ∧
      (∀ u v, F.Reachable u v ↔ G.Reachable u v) ∧
      F.edgeFinset.card + Nat.card F.ConnectedComponent = Fintype.card α := by
  classical
  obtain ⟨F, hle, hacyc, hreach⟩ := G.exists_isAcyclic_reachable_eq_le
  refine ⟨F, hle, hacyc, ?_, ?_⟩
  · intro u v
    rw [hreach]
  · have hrank := hacyc.ncard_edgeSet_add_card_connectedComponent
    have hedge : F.edgeSet.ncard = F.edgeFinset.card := by
      rw [← Set.fintypeCard_eq_ncard, SimpleGraph.edgeFinset_card]
    rw [hedge, @Nat.card_eq_fintype_card α _] at hrank
    exact hrank


lemma chosen_connected_frontier [Nonempty α] (safe split : ℕ → Prop)
    [DecidablePred safe] [DecidablePred split] (T : ℕ → Finset α)
    (h : ∀ w, safe w → (T w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe a ∧ T w ⊆ T a) ∨
      (split w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ T w ⊆ T a ∪ T b))
    (M : ℕ) (W : Finset ℕ) (hW : ∀ w ∈ W, w < M ∧ safe w)
    (hc : ∀ u v : α, Relation.ReflTransGen
      (fun a b => ∃ w ∈ W, a ∈ T w ∧ b ∈ T w) u v) :
    ∃ (F : SimpleGraph α) (K : Finset ℕ) (label : Sym2 α → ℕ),
      F.IsTree ∧ Set.InjOn label F.edgeSet ∧ K = F.edgeFinset.image label ∧
      K ⊆ (Finset.range M).filter (fun k => safe k ∧ split k ∧ 2 ≤ (T k).card) ∧
      K.card + 1 = Fintype.card α ∧
      (∀ e ∈ F.edgeSet, ∃ u ∈ T (label e), ∃ v ∈ T (label e), e = s(u, v)) ∧
      ∀ w < M, safe w → Connects F (T w) := by
  classical
  obtain ⟨F, K, label, hacyc, hinj, hK, hsub, _, hends, hconn⟩ :=
    chosen_support_forest safe split T h M
  have hpre : F.Preconnected := by
    intro u v
    have huv := hc u v
    induction huv with
    | refl => exact SimpleGraph.Reachable.rfl
    | @tail v z hvz hz ih =>
      obtain ⟨w, hw, hv, hz⟩ := hz
      exact ih.trans (hconn w (hW w hw).1 (hW w hw).2 v hv z hz)
  have htree : F.IsTree := ⟨⟨hpre⟩, hacyc⟩
  have hcard : K.card = F.edgeFinset.card := by
    rw [hK]
    apply Finset.card_image_of_injOn
    intro e he f hf hef
    exact hinj (by simpa using he) (by simpa using hf) hef
  refine ⟨F, K, label, htree, hinj, hK, hsub, ?_, hends, hconn⟩
  rw [hcard]
  exact htree.card_edgeFinset

end PEqualNP.Outside.L_meta_4970.ChosenForest


namespace PEqualNP.Outside.L_meta_4970.ForestLabels

open Classical

variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] in
lemma labelled_spanning_forest (G : SimpleGraph α) (label : Sym2 α → β)
    (hinj : Set.InjOn label G.edgeSet) (K : Finset β)
    (hK : ∀ e ∈ G.edgeSet, label e ∈ K) :
    ∃ (F : SimpleGraph α) (L : Finset β),
      F ≤ G ∧ F.IsAcyclic ∧ F.Reachable = G.Reachable ∧
      L ⊆ K ∧ L = F.edgeFinset.image label ∧
      L.card + Nat.card G.ConnectedComponent = Fintype.card α := by
  classical
  obtain ⟨F, hFG, hF, hreach⟩ := G.exists_isAcyclic_reachable_eq_le
  let L := F.edgeFinset.image label
  have hL : L ⊆ K := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    exact hK e (SimpleGraph.edgeSet_mono hFG (by simpa using he))
  have hcard : L.card = F.edgeFinset.card := by
    apply Finset.card_image_of_injOn
    intro e he d hd hed
    exact hinj (SimpleGraph.edgeSet_mono hFG (by simpa using he))
      (SimpleGraph.edgeSet_mono hFG (by simpa using hd)) hed
  have hcomponents : Nat.card F.ConnectedComponent = Nat.card G.ConnectedComponent := by
    unfold SimpleGraph.ConnectedComponent
    rw [hreach]
  have hcount := hF.ncard_edgeSet_add_card_connectedComponent
  have hcount' : F.edgeFinset.card + Nat.card F.ConnectedComponent = Fintype.card α := by
    have hedge : F.edgeSet.ncard = F.edgeFinset.card := by
      rw [← Set.fintypeCard_eq_ncard, SimpleGraph.edgeFinset_card]
    rw [hedge, @Nat.card_eq_fintype_card α _] at hcount
    exact hcount
  exact ⟨F, L, hFG, hF, hreach, hL, rfl, by rw [hcard, ← hcomponents]; exact hcount'⟩

end PEqualNP.Outside.L_meta_4970.ForestLabels

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970.SemanticSafe
open PEqualNP.Outside.L_meta_4970.Connectivity
open PEqualNP.Outside.L_meta_4970.ChosenForest

open Classical

lemma chosen_productive_star_tree (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (hQ : Q.Nonempty) (W : Finset ℕ)
    (hW : ∀ w ∈ W, w < n + C.gates.length ∧ Safe Q (wireFn n C w))
    (hc : ∀ u v : Q, Relation.ReflTransGen
      (fun a b : Q => ∃ w ∈ W,
        (a : Fin n) ∈ singletonSupport n C w ∧ (b : Fin n) ∈ singletonSupport n C w) u v) :
    ∃ (F : SimpleGraph Q) (K : Finset ℕ) (label : Sym2 Q → ℕ),
      F.IsTree ∧ Set.InjOn label F.edgeSet ∧ K = F.edgeFinset.image label ∧
      K ⊆ productiveOr n C Q ∧ K.card + 1 = Q.card ∧
      ∀ e ∈ F.edgeSet, ∃ u : Q, (u : Fin n) ∈ singletonSupport n C (label e) ∧
        ∃ v : Q, (v : Fin n) ∈ singletonSupport n C (label e) ∧ e = s(u, v) := by
  classical
  obtain ⟨q, hq⟩ := hQ
  let : Nonempty Q := ⟨⟨q, hq⟩⟩
  let safe := fun w => w < n + C.gates.length ∧ Safe Q (wireFn n C w)
  let split := fun w => (n ≤ w ∧ (gateAt C (w - n)).op = GateOp.or) ∧
    ¬ HasSafeCarrier n C Q w
  let T : ℕ → Finset Q := fun w => (singletonSupport n C w).subtype (fun a => a ∈ Q)
  have hcard : ∀ w, (T w).card ≤ (singletonSupport n C w).card := by
    intro w
    exact (Finset.card_subtype _ _).le.trans (Finset.card_filter_le _ _)
  have hstruct : ∀ w, safe w → (T w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe a ∧ T w ⊆ T a) ∨
      (split w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ T w ⊆ T a ∪ T b) := by
    intro w hw
    rcases productive_singleton_structure n C hC Q w hw with
      hs | ⟨a, ha, hsa, hTa⟩ | ⟨hsp, a, b, ha, hb, hsa, hsb, hTab⟩
    · exact Or.inl ((hcard w).trans hs)
    · right; left
      refine ⟨a, ha, hsa, ?_⟩
      intro x hx
      exact Finset.mem_subtype.mpr (hTa (Finset.mem_subtype.mp hx))
    · right; right
      refine ⟨hsp, a, b, ha, hb, hsa, hsb, ?_⟩
      intro x hx
      rcases Finset.mem_union.mp (hTab (Finset.mem_subtype.mp hx)) with hxa | hxb
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_subtype.mpr hxa))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_subtype.mpr hxb))
  have hc' : ∀ u v : Q, Relation.ReflTransGen
      (fun a b => ∃ w ∈ W, a ∈ T w ∧ b ∈ T w) u v := by
    simpa only [T, Finset.mem_subtype] using hc
  obtain ⟨F, K, label, htree, hinj, hK, hsub, hsize, hends, _⟩ :=
    chosen_connected_frontier safe split T hstruct (n + C.gates.length) W
      (fun w hw => ⟨(hW w hw).1, hW w hw⟩) hc'
  refine ⟨F, K, label, htree, hinj, hK, ?_, by simpa using hsize, ?_⟩
  · intro w hw
    have hh := hsub hw
    simp only [Finset.mem_filter, Finset.mem_range, safe, split] at hh
    apply Finset.mem_filter.mpr
    refine ⟨?_, hh.2.2.1.2⟩
    simp only [chargedOr, Finset.mem_filter, Finset.mem_range]
    exact ⟨hh.1, hh.2.1, hh.2.2.1.1, hh.2.2.2.trans (hcard w)⟩
  · intro e he
    simpa only [T, Finset.mem_subtype] using hends e he

end PEqualNP.Outside.L_meta_4970_aux

namespace PEqualNP.Outside.L_meta_4970.ForestLabels

open Classical

variable {α ι : Type*} [Fintype α] [DecidableEq ι]

lemma family_labelled_spanning_forest (I : Finset ι)
    (G : SimpleGraph α) (F : ι → SimpleGraph α)
    (labels : ι → Sym2 α → ℕ) (K : ι → Finset ℕ)
    (hcover : ∀ e ∈ G.edgeSet, ∃ i ∈ I, e ∈ (F i).edgeSet)
    (hinj : ∀ i ∈ I, Set.InjOn (labels i) (F i).edgeSet)
    (hK : ∀ i ∈ I, ∀ e ∈ (F i).edgeSet, labels i e ∈ K i)
    (hdis : (I : Set ι).PairwiseDisjoint K) :
    ∃ (H : SimpleGraph α) (L : Finset ℕ) (label : Sym2 α → ℕ),
      H ≤ G ∧ H.IsAcyclic ∧ H.Reachable = G.Reachable ∧
      Set.InjOn label G.edgeSet ∧ L = H.edgeFinset.image label ∧
      L ⊆ I.biUnion K ∧
      L.card + Nat.card G.ConnectedComponent = Fintype.card α ∧
      ∀ e ∈ G.edgeSet, ∃ i ∈ I, e ∈ (F i).edgeSet ∧ label e = labels i e := by
  classical
  let owner : G.edgeSet → ι := fun e => Classical.choose (hcover e e.property)
  have howner : ∀ e : G.edgeSet, owner e ∈ I ∧ (e : Sym2 α) ∈ (F (owner e)).edgeSet := by
    intro e
    exact Classical.choose_spec (hcover e e.property)
  let label : Sym2 α → ℕ := fun e =>
    if he : e ∈ G.edgeSet then labels (owner ⟨e, he⟩) e else 0
  have hlabel : ∀ (e : Sym2 α) (he : e ∈ G.edgeSet), label e ∈ K (owner ⟨e, he⟩) := by
    intro e he
    simp only [label, dite_eq_left he]
    exact hK _ (howner ⟨e, he⟩).1 e (howner ⟨e, he⟩).2
  have hlabelK : ∀ e ∈ G.edgeSet, label e ∈ I.biUnion K := by
    intro e he
    exact Finset.mem_biUnion.mpr ⟨owner ⟨e, he⟩, (howner ⟨e, he⟩).1, hlabel e he⟩
  have hlabelinj : Set.InjOn label G.edgeSet := by
    intro e he f hf hef
    let i := owner ⟨e, he⟩
    let j := owner ⟨f, hf⟩
    have hi : i ∈ I := (howner ⟨e, he⟩).1
    have hj : j ∈ I := (howner ⟨f, hf⟩).1
    have heF : e ∈ (F i).edgeSet := (howner ⟨e, he⟩).2
    have hfF : f ∈ (F j).edgeSet := (howner ⟨f, hf⟩).2
    have hei : label e ∈ K i := hlabel e he
    have hfj : label f ∈ K j := hlabel f hf
    by_cases hij : i = j
    · have hle : label e = labels i e := by simp [label, i, he]
      have hlf : label f = labels j f := by simp [label, j, hf]
      rw [hle, hlf, ← hij] at hef
      exact hinj i hi heF (by simpa only [← hij] using hfF) hef
    · exact False.elim (Finset.disjoint_left.mp (hdis hi hj hij) hei (hef.symm ▸ hfj))
  obtain ⟨H, L, hHG, hH, hreach, hL, himage, hcount⟩ :=
    labelled_spanning_forest G label hlabelinj (I.biUnion K) hlabelK
  refine ⟨H, L, label, hHG, hH, hreach, hlabelinj, himage, hL, hcount, ?_⟩
  intro e he
  exact ⟨owner ⟨e, he⟩, (howner ⟨e, he⟩).1, (howner ⟨e, he⟩).2, by simp [label, he]⟩

end PEqualNP.Outside.L_meta_4970.ForestLabels


namespace PEqualNP.Outside.L_meta_4970.MappedLabels

lemma embedding_label_transport {α β : Type*} (F : SimpleGraph α) (f : α ↪ β)
    (label : Sym2 α → ℕ) (K : Finset ℕ)
    (hinj : Set.InjOn label F.edgeSet)
    (hlabels : ∀ e ∈ F.edgeSet, label e ∈ K) :
    ∃ mappedLabel : Sym2 β → ℕ,
      Set.InjOn mappedLabel (F.map f).edgeSet ∧
      (∀ e ∈ (F.map f).edgeSet, mappedLabel e ∈ K) ∧
      (∀ e ∈ F.edgeSet, mappedLabel (f.sym2Map e) = label e) ∧
      ∀ e ∈ (F.map f).edgeSet, ∃ d ∈ F.edgeSet,
        f.sym2Map d = e ∧ mappedLabel e = label d := by
  classical
  let mappedLabel : Sym2 β → ℕ := fun e =>
    if h : ∃ d ∈ F.edgeSet, f.sym2Map d = e then label (Classical.choose h) else 0
  have hsource : ∀ e ∈ F.edgeSet, mappedLabel (f.sym2Map e) = label e := by
    intro e he
    have hx : ∃ d ∈ F.edgeSet, f.sym2Map d = f.sym2Map e := ⟨e, he, rfl⟩
    dsimp [mappedLabel]
    rw [dite_eq_left hx]
    have heq : Classical.choose hx = e := f.sym2Map.injective (Classical.choose_spec hx).2
    rw [heq]
  have hpre : ∀ e ∈ (F.map f).edgeSet, ∃ d ∈ F.edgeSet, f.sym2Map d = e := by
    intro e he
    rw [SimpleGraph.edgeSet_map] at he
    exact he
  refine ⟨mappedLabel, ?_, ?_, hsource, ?_⟩
  · intro e he d hd heq
    obtain ⟨e₀, he₀, rfl⟩ := hpre e he
    obtain ⟨d₀, hd₀, rfl⟩ := hpre d hd
    rw [hsource e₀ he₀, hsource d₀ hd₀] at heq
    exact congrArg f.sym2Map (hinj he₀ hd₀ heq)
  · intro e he
    obtain ⟨d, hd, rfl⟩ := hpre e he
    rw [hsource d hd]
    exact hlabels d hd
  · intro e he
    obtain ⟨d, hd, rfl⟩ := hpre e he
    exact ⟨d, hd, rfl, hsource d hd⟩

end PEqualNP.Outside.L_meta_4970.MappedLabels

namespace PEqualNP.Outside.L_meta_4970_aux

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SemanticSafe
open PEqualNP.Outside.L_meta_4970.ForestLabels
open PEqualNP.Outside.L_meta_4970.MappedLabels

lemma chosen_productive_family_forest {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : ι → Finset (Fin n)) (hQ : ∀ i, (Q i).Nonempty)
    (W : ι → Finset ℕ)
    (hW : ∀ i, ∀ w ∈ W i, w < n + C.gates.length ∧ Safe (Q i) (wireFn n C w))
    (hc : ∀ i, ∀ u v : Q i, Relation.ReflTransGen
      (fun a b : Q i => ∃ w ∈ W i,
        (a : Fin n) ∈ singletonSupport n C w ∧ (b : Fin n) ∈ singletonSupport n C w) u v)
    (hinter : ∀ i j, i ≠ j → (Q i ∩ Q j).card ≤ 1)
    (embed : ∀ i, Q i ↪ α) :
    ∃ (H : SimpleGraph α) (L : Finset ℕ) (label : Sym2 α → ℕ),
      H.IsAcyclic ∧ Set.InjOn label H.edgeSet ∧ L = H.edgeFinset.image label ∧
      L ⊆ allOrWires n C ∧
      L.card + Nat.card H.ConnectedComponent = Fintype.card α ∧
      (∀ i, ∀ u v : Q i, H.Reachable (embed i u) (embed i v)) ∧
      ∀ e ∈ H.edgeSet, ∃ i,
        label e ∈ productiveOr n C (Q i) ∧
        ∃ u : Q i, (u : Fin n) ∈ singletonSupport n C (label e) ∧
          ∃ v : Q i, (v : Fin n) ∈ singletonSupport n C (label e) ∧
            e = s(embed i u, embed i v) := by
  classical
  choose F K labels htree hinj hK hsub hsize hends using
    fun i => chosen_productive_star_tree n C hC (Q i) (hQ i) (W i) (hW i) (hc i)
  have hrange : ∀ i, ∀ e ∈ (F i).edgeSet, labels i e ∈ K i := by
    intro i e he
    rw [hK i]
    exact Finset.mem_image.mpr ⟨e, by simpa using he, rfl⟩
  choose mapped hinjMap hrangeMap hsourceMap hpreMap using
    fun i => embedding_label_transport (F i) (embed i) (labels i) (K i) (hinj i) (hrange i)
  let J : ι → SimpleGraph α := fun i => (F i).map (embed i)
  let G : SimpleGraph α := ⨆ i, J i
  have hcover : ∀ e ∈ G.edgeSet, ∃ i ∈ (Finset.univ : Finset ι), e ∈ (J i).edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_iSup] at he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
    exact ⟨i, Finset.mem_univ i, hi⟩
  have hdis : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint K := by
    intro i hi j hj hij
    exact Finset.disjoint_of_subset_left (hsub i)
      (Finset.disjoint_of_subset_right (hsub j) (productiveOr_disjoint n C (Q i) (Q j) (hinter i j hij)))
  obtain ⟨H, L, label, hHG, hH, hreach, hlabel, hL, hLsub, hcount, horigin⟩ :=
    family_labelled_spanning_forest Finset.univ G J mapped K hcover
      (fun i _ => hinjMap i) (fun i _ => hrangeMap i) hdis
  have hcomponents : Nat.card H.ConnectedComponent = Nat.card G.ConnectedComponent := by
    unfold SimpleGraph.ConnectedComponent
    rw [hreach]
  have hLall : L ⊆ allOrWires n C := by
    intro k hk
    obtain ⟨i, hi, hki⟩ := Finset.mem_biUnion.mp (hLsub hk)
    exact productive_family_subset_allOr n C Finset.univ Q
      (Finset.mem_biUnion.mpr ⟨i, hi, hsub i hki⟩)
  refine ⟨H, L, label, hH, ?_, hL, hLall, ?_, ?_, ?_⟩
  · intro e he f hf hef
    exact hlabel (SimpleGraph.edgeSet_mono hHG he) (SimpleGraph.edgeSet_mono hHG hf) hef
  · rw [hcomponents]
    exact hcount
  · intro i u v
    have hFi := (htree i).connected.preconnected u v
    have hJi : (J i).Reachable (embed i u) (embed i v) :=
      hFi.map (SimpleGraph.Embedding.map (embed i) (F i)).toHom
    rw [hreach]
    exact hJi.mono (le_iSup J i)
  · intro e he
    obtain ⟨i, _, hei, heiLabel⟩ := horigin e (SimpleGraph.edgeSet_mono hHG he)
    obtain ⟨d, hd, hde, hLabel⟩ := hpreMap i e hei
    have hfinal : label e = labels i d := heiLabel.trans hLabel
    have hprod : label e ∈ productiveOr n C (Q i) := by
      rw [hfinal]
      exact hsub i (hrange i d hd)
    obtain ⟨u, hu, v, hv, huv⟩ := hends i d hd
    refine ⟨i, hprod, u, ?_, v, ?_, ?_⟩
    · simpa only [hfinal] using hu
    · simpa only [hfinal] using hv
    · rw [← hde, huv]
      rfl

end PEqualNP.Outside.L_meta_4970_aux


namespace PEqualNP.Outside.L_meta_4970.OverlapReachability

def CoOccurs {ι α : Type*} {V : ι → Type*} (embed : ∀ i, V i → α)
    (x y : α) : Prop := ∃ i, ∃ u v : V i, x = embed i u ∧ y = embed i v

lemma reachable_eq_cooccurrence {ι α : Type*} {V : ι → Type*}
    (H : SimpleGraph α) (embed : ∀ i, V i → α)
    (hconn : ∀ i, ∀ u v : V i, H.Reachable (embed i u) (embed i v))
    (hedges : ∀ e ∈ H.edgeSet, ∃ i, ∃ u v : V i, e = s(embed i u, embed i v)) :
    H.Reachable = Relation.ReflTransGen (CoOccurs embed) := by
  have hrel : ∀ x y, H.Adj x y → CoOccurs embed x y := by
    intro x y hxy
    obtain ⟨i, u, v, he⟩ := hedges s(x, y) (by simpa using hxy)
    rcases Sym2.eq_iff.mp he with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨i, u, v, hx, hy⟩
    · exact ⟨i, v, u, hx, hy⟩
  funext x y
  apply propext
  constructor
  · intro hxy
    have ht := (H.reachable_iff_reflTransGen x y).mp hxy
    clear hxy
    induction ht with
    | refl => exact Relation.ReflTransGen.refl
    | @tail v z hvz hz ih => exact Relation.ReflTransGen.tail ih (hrel v z hz)
  · intro hxy
    induction hxy with
    | refl => exact SimpleGraph.Reachable.rfl
    | @tail v z hvz hz ih =>
      obtain ⟨i, a, b, rfl, rfl⟩ := hz
      exact ih.trans (hconn i a b)

lemma component_count_eq_overlap_quotient {ι α : Type*} {V : ι → Type*}
    (H : SimpleGraph α) (embed : ∀ i, V i → α)
    (hconn : ∀ i, ∀ u v : V i, H.Reachable (embed i u) (embed i v))
    (hedges : ∀ e ∈ H.edgeSet, ∃ i, ∃ u v : V i, e = s(embed i u, embed i v)) :
    Nat.card H.ConnectedComponent =
      Nat.card (Quot (Relation.ReflTransGen (CoOccurs embed))) := by
  unfold SimpleGraph.ConnectedComponent
  rw [reachable_eq_cooccurrence H embed hconn hedges]

end PEqualNP.Outside.L_meta_4970.OverlapReachability

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SemanticSafe
open PEqualNP.Outside.L_meta_4970.OverlapReachability

lemma chosen_productive_family_overlap_budget {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : ι → Finset (Fin n)) (hQ : ∀ i, (Q i).Nonempty)
    (W : ι → Finset ℕ)
    (hW : ∀ i, ∀ w ∈ W i, w < n + C.gates.length ∧ Safe (Q i) (wireFn n C w))
    (hc : ∀ i, ∀ u v : Q i, Relation.ReflTransGen
      (fun a b : Q i => ∃ w ∈ W i,
        (a : Fin n) ∈ singletonSupport n C w ∧ (b : Fin n) ∈ singletonSupport n C w) u v)
    (hinter : ∀ i j, i ≠ j → (Q i ∩ Q j).card ≤ 1)
    (embed : ∀ i, Q i ↪ α) :
    ∃ L : Finset ℕ, L ⊆ allOrWires n C ∧
      L.card + Nat.card (Quot (Relation.ReflTransGen
        (CoOccurs (fun i => (embed i : Q i → α))))) = Fintype.card α ∧
      ∀ w ∈ L, ∃ i, w ∈ productiveOr n C (Q i) := by
  classical
  obtain ⟨H, L, label, _, _, hL, hsub, hcount, hconn, hends⟩ :=
    chosen_productive_family_forest n C hC Q hQ W hW hc hinter embed
  have hedges : ∀ e ∈ H.edgeSet, ∃ i, ∃ u v : Q i,
      e = s(embed i u, embed i v) := by
    intro e he
    obtain ⟨i, _, u, _, v, _, huv⟩ := hends e he
    exact ⟨i, u, v, huv⟩
  have hcc := component_count_eq_overlap_quotient H
    (fun i => (embed i : Q i → α)) hconn hedges
  refine ⟨L, hsub, ?_, ?_⟩
  · rw [← hcc]
    exact hcount
  · intro w hw
    rw [hL] at hw
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨i, hi, _⟩ := hends e (by simpa using he)
    exact ⟨i, hi⟩

end PEqualNP.Outside.L_meta_4970_aux


namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970.SemanticSafe

lemma productiveOr_support_subset (n : ℕ) (C : Circuit) (Q : Finset (Fin n))
    (w : ℕ) (hw : w ∈ productiveOr n C Q) :
    singletonSupport n C w ⊆ Q := by
  classical
  have hm := productiveOr_subset n C Q hw
  have hs := (Finset.mem_filter.mp hm).2.1.2
  exact singletonSupport_safe_subset n C w Q hs

lemma productiveOr_binary_operands (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (w : ℕ) (hw : w ∈ productiveOr n C Q) :
    n ≤ w ∧ w < n + C.gates.length ∧
      (gateAt C (w - n)).op = GateOp.or ∧
      ∃ a b, (gateAt C (w - n)).inputs = [a, b] ∧ a < w ∧ b < w ∧
        Safe Q (wireFn n C a) ∧ Safe Q (wireFn n C b) ∧
        singletonSupport n C w = singletonSupport n C a ∪ singletonSupport n C b ∧
        (singletonSupport n C a).Nonempty ∧ (singletonSupport n C b).Nonempty ∧
        ¬ singletonSupport n C w ⊆ singletonSupport n C a ∧
        ¬ singletonSupport n C w ⊆ singletonSupport n C b := by
  classical
  have hm := productiveOr_subset n C Q hw
  obtain ⟨_, ⟨hwlim, hs⟩, ⟨hn, hor⟩, _⟩ := Finset.mem_filter.mp hm
  have hj : w - n < C.gates.length := by omega
  have heq : n + (w - n) = w := by omega
  obtain ⟨a, b, ha, hb, hab, _, heval⟩ := binary_gate n C hC (w - n) hj
  rw [heq] at ha hb heval
  have hv : ∀ x, wireFn n C w x = (wireFn n C a x || wireFn n C b x) := by
    intro x
    rw [heval x, hor]
    simp [GateOp.eval]
  have hs' : Safe Q (fun x => wireFn n C a x || wireFn n C b x) := by
    simpa only [← hv] using hs
  obtain ⟨hsa, hsb⟩ := safe_or_iff.mp hs'
  have hsup : singletonSupport n C w = singletonSupport n C a ∪ singletonSupport n C b := by
    ext i
    simp only [mem_singletonSupport, hv, Bool.or_eq_true, Finset.mem_union]
  have hna := productiveOr_no_carrier n C Q w hw a ha (by omega) hsa
  have hnb := productiveOr_no_carrier n C Q w hw b hb (by omega) hsb
  have hane : (singletonSupport n C a).Nonempty := by
    by_contra h
    have hz : singletonSupport n C a = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    apply hnb
    rw [hsup, hz, Finset.empty_union]
  have hbne : (singletonSupport n C b).Nonempty := by
    by_contra h
    have hz : singletonSupport n C b = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    apply hna
    rw [hsup, hz, Finset.union_empty]
  exact ⟨hn, hwlim, hor, a, b, hab, ha, hb, hsa, hsb, hsup, hane, hbne, hna, hnb⟩

lemma productiveOr_monochromatic {β : Type*} (n : ℕ) (C : Circuit)
    (Q : Finset (Fin n)) (w : ℕ) (hw : w ∈ productiveOr n C Q)
    (color : Fin n → β) (c : β) (hQ : ∀ i ∈ Q, color i = c) :
    ∀ i ∈ singletonSupport n C w, color i = c := by
  intro i hi
  exact hQ i (productiveOr_support_subset n C Q w hw hi)

lemma productiveOr_not_bad {β : Type*} (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (w : ℕ) (hw : w ∈ productiveOr n C Q)
    (a b : ℕ) (hab : (gateAt C (w - n)).inputs = [a, b])
    (color : Fin n → β) (c : β) (hQ : ∀ i ∈ Q, color i = c) :
    ¬ (singletonSupport n C a = ∅ ∨ singletonSupport n C b = ∅ ∨
      ∃ i ∈ singletonSupport n C w, ∃ j ∈ singletonSupport n C w,
        color i ≠ color j) := by
  obtain ⟨_, _, _, a', b', hab', _, _, _, _, _, hane, hbne, _, _⟩ :=
    productiveOr_binary_operands n C hC Q w hw
  have heq : [a', b'] = [a, b] := hab'.symm.trans hab
  have ha : a' = a := (List.cons.inj heq).1
  have hb : b' = b := (List.cons.inj (List.cons.inj heq).2).1
  subst a'
  subst b'
  intro hbad
  rcases hbad with hza | hzb | ⟨i, hi, j, hj, hij⟩
  · exact (Finset.nonempty_iff_ne_empty.mp hane) hza
  · exact (Finset.nonempty_iff_ne_empty.mp hbne) hzb
  · have hm := productiveOr_monochromatic n C Q w hw color c hQ
    exact hij ((hm i hi).trans (hm j hj).symm)

end PEqualNP.Outside.L_meta_4970_aux

namespace PEqualNP.Outside.L_meta_4970.BlendedSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4970_aux PEqualNP.Outside.L_meta_4970.SemanticSafe

lemma zsplit_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


lemma zgateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma zorFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma zorStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

lemma zorStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma zorFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact zorStep_getD_lt n cs g k hk

lemma zorSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := zsplit_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [zgateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [zorFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, zorFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, zorFold_getD_lt n post _ m (by omega)]
    exact zorStep_getD_lt n _ gk m (by omega)
  have h3 := zorStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma zqorSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [zorFold_length]
  simp

lemma zqreach_iff (n : ℕ) (C : Circuit) (k g : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ OrReaches n C w g) := by
  have e : n + k - n = k := by omega
  constructor
  · intro h
    have h2 := h.2
    rw [e] at h2
    rcases (zorSets_mem_iff n C k g hk).1 h2 with h3 | ⟨hop, w, hw, hn, hlt, hx⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, hlt, hn, hx⟩
  · intro h
    refine ⟨by omega, ?_⟩
    rw [e]
    refine (zorSets_mem_iff n C k g hk).2 ?_
    rcases h with h | ⟨hop, w, hw, hlt, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hr.1, hlt, hr.2⟩

lemma zqreach_bound (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    n ≤ w ∧ w - n < C.gates.length := by
  refine ⟨h.1, ?_⟩
  by_contra hc
  have h2 := h.2
  have hlen : (orSets n C).length ≤ w - n := by rw [zqorSets_len]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen] at h2
  simp at h2

lemma zqreach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := (zqreach_iff n C k k hk).2 (Or.inl rfl)

lemma zqmem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n) :
    b ∈ PEqualNP.TopForm.orIn n C w ↔ ((b : ℕ) = w ∨ ∃ k, k < C.gates.length ∧
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (b : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma zqorIn_eq_self (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    ∀ b ∈ PEqualNP.TopForm.orIn n C w, (b : ℕ) = w := by
  intro b hb
  rcases (zqmem_orIn n C w b).1 hb with h | ⟨k', hk', hr, hop', hi⟩
  · exact h
  · exfalso
    obtain ⟨h1, h2⟩ := zqreach_bound n C w k' hr
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have e : n + k - n = k := by omega
    rw [e] at hw h2
    rcases (zqreach_iff n C k k' h2).1 hr with h | ⟨hop, _⟩
    · rw [h] at hop'
      exact hw ⟨h1, h2, hop'⟩
    · exact hw ⟨h1, h2, hop⟩

lemma zqorIn_small (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have h1 := zqorIn_eq_self n C w hw a ha
  have h2 := zqorIn_eq_self n C w hw b hb
  exact Fin.ext (by omega)

lemma zqorIn_or (n : ℕ) (C : Circuit) (k a b : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    PEqualNP.TopForm.orIn n C (n + k) =
      PEqualNP.TopForm.orIn n C a ∪ PEqualNP.TopForm.orIn n C b := by
  have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
  have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
  ext i
  rw [Finset.mem_union, zqmem_orIn, zqmem_orIn, zqmem_orIn]
  constructor
  · rintro (h | ⟨k', hk', hr, hop', hi⟩)
    · exfalso
      have := i.2
      omega
    · rcases (zqreach_iff n C k k' hk).1 hr with h | ⟨_, w, hw, hwlt, hr'⟩
      · rw [h, hin, List.mem_cons, List.mem_singleton] at hi
        rcases hi with h4 | h4
        · exact Or.inl (Or.inl h4)
        · exact Or.inr (Or.inl h4)
      · rw [hin, List.mem_cons, List.mem_singleton] at hw
        rcases hw with h4 | h4
        · rw [h4] at hr'
          exact Or.inl (Or.inr ⟨k', hk', hr', hop', hi⟩)
        · rw [h4] at hr'
          exact Or.inr (Or.inr ⟨k', hk', hr', hop', hi⟩)
  · rintro ((h | ⟨k', hk', hr, hop', hi⟩) | (h | ⟨k', hk', hr, hop', hi⟩))
    · exact Or.inr ⟨k, hk, zqreach_self n C k hk, hop, by rw [h]; exact hma⟩
    · exact Or.inr ⟨k', hk', (zqreach_iff n C k k' hk).2 (Or.inr ⟨hop, a, hma, ha, hr⟩), hop', hi⟩
    · exact Or.inr ⟨k, hk, zqreach_self n C k hk, hop, by rw [h]; exact hmb⟩
    · exact Or.inr ⟨k', hk', (zqreach_iff n C k k' hk).2 (Or.inr ⟨hop, b, hmb, hb, hr⟩), hop', hi⟩

lemma raw_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    orIn n C w = {⟨w, hw⟩} := by
  ext i
  constructor
  · intro hi
    have he := zqorIn_eq_self n C w (by omega) i hi
    exact Finset.mem_singleton.mpr (Fin.ext he)
  · intro hi
    have he := Finset.mem_singleton.mp hi
    exact (zqmem_orIn n C w i).mpr (Or.inl (congrArg Fin.val he))

lemma raw_and_empty (n : ℕ) (C : Circuit) (w : ℕ) (hn : n ≤ w)
    (hand : (gateAt C (w - n)).op = GateOp.and) : orIn n C w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have he := zqorIn_eq_self n C w (by
    rintro ⟨_, _, hor⟩
    rw [hand] at hor
    cases hor) i hi
  have := i.isLt
  omega

lemma raw_or_union (n : ℕ) (C : Circuit) (w a b : ℕ)
    (hw : w < n + C.gates.length) (hn : n ≤ w)
    (hor : (gateAt C (w - n)).op = GateOp.or)
    (hab : (gateAt C (w - n)).inputs = [a, b]) (ha : a < w) (hb : b < w) :
    orIn n C w = orIn n C a ∪ orIn n C b := by
  have he : n + (w - n) = w := by omega
  have hraw := zqorIn_or n C (w - n) a b (by omega) hor hab
    (by omega) (by omega)
  rwa [he] at hraw

lemma raw_subset_singletonSupport (n : ℕ) (C : Circuit) (hC : IsAO2 n C) :
    ∀ w, w < n + C.gates.length → orIn n C w ⊆ singletonSupport n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · rw [raw_input n C w hin, singletonSupport_input n C w hin]
    · have hn : n ≤ w := by omega
      have hj : w - n < C.gates.length := by omega
      have he : n + (w - n) = w := by omega
      obtain ⟨a, b, ha, hb, hab, hop, heval⟩ := binary_gate n C hC (w - n) hj
      rw [he] at ha hb heval
      rcases hop with hand | hor
      · rw [raw_and_empty n C w hn hand]
        exact Finset.empty_subset _
      · rw [raw_or_union n C w a b hw hn hor hab ha hb]
        intro i hi
        rw [mem_singletonSupport, heval, hor]
        simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq,
          Bool.or_eq_true]
        rcases Finset.mem_union.mp hi with hi | hi
        · exact Or.inl ((mem_singletonSupport n C a i).mp (ih a ha (by omega) hi))
        · exact Or.inr ((mem_singletonSupport n C b i).mp (ih b hb (by omega) hi))

noncomputable def blendedSupport (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) (w : ℕ) :
    Finset (Fin n) := by
  classical
  exact if Safe Q (wireFn n C w) then singletonSupport n C w else orIn n C w

lemma blendedSupport_of_safe (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) (w : ℕ)
    (hs : Safe Q (wireFn n C w)) : blendedSupport n C Q w = singletonSupport n C w := by
  classical
  simp [blendedSupport, hs]

lemma blendedSupport_of_not_safe (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) (w : ℕ)
    (hs : ¬ Safe Q (wireFn n C w)) : blendedSupport n C Q w = orIn n C w := by
  classical
  simp [blendedSupport, hs]

lemma raw_subset_blendedSupport (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (w : ℕ) (hw : w < n + C.gates.length) :
    orIn n C w ⊆ blendedSupport n C Q w := by
  classical
  by_cases hs : Safe Q (wireFn n C w)
  · rw [blendedSupport_of_safe n C Q w hs]
    exact raw_subset_singletonSupport n C hC w hw
  · rw [blendedSupport_of_not_safe n C Q w hs]

lemma blendedSupport_subset_singletonSupport (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (w : ℕ) (hw : w < n + C.gates.length) :
    blendedSupport n C Q w ⊆ singletonSupport n C w := by
  classical
  by_cases hs : Safe Q (wireFn n C w)
  · rw [blendedSupport_of_safe n C Q w hs]
  · rw [blendedSupport_of_not_safe n C Q w hs]
    exact raw_subset_singletonSupport n C hC w hw

lemma blendedSupport_subset_Q (n : ℕ) (C : Circuit) (Q : Finset (Fin n))
    (w : ℕ) (hraw : orIn n C w ⊆ Q) : blendedSupport n C Q w ⊆ Q := by
  classical
  by_cases hs : Safe Q (wireFn n C w)
  · rw [blendedSupport_of_safe n C Q w hs]
    exact singletonSupport_safe_subset n C w Q hs
  · rw [blendedSupport_of_not_safe n C Q w hs]
    exact hraw


lemma safe_admissible (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (w : ℕ) (hw : w < n + C.gates.length)
    (hs : Safe Q (wireFn n C w)) : w < n + C.gates.length ∧ orIn n C w ⊆ Q :=
  ⟨hw, (raw_subset_singletonSupport n C hC w hw).trans
    (singletonSupport_safe_subset n C w Q hs)⟩

lemma blended_singleton_structure (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) :
    ∀ w, (w < n + C.gates.length ∧ orIn n C w ⊆ Q) →
      (blendedSupport n C Q w).card ≤ 1 ∨
      (∃ a, a < w ∧ (a < n + C.gates.length ∧ orIn n C a ⊆ Q) ∧
        blendedSupport n C Q w ⊆ blendedSupport n C Q a) ∨
      ((n ≤ w ∧ (gateAt C (w - n)).op = GateOp.or) ∧
        ∃ a b, a < w ∧ b < w ∧
          (a < n + C.gates.length ∧ orIn n C a ⊆ Q) ∧
          (b < n + C.gates.length ∧ orIn n C b ⊆ Q) ∧
          blendedSupport n C Q w ⊆ blendedSupport n C Q a ∪ blendedSupport n C Q b) := by
  classical
  intro w ⟨hw, hraw⟩
  by_cases hs : Safe Q (wireFn n C w)
  · rcases safe_singleton_structure n C hC Q w ⟨hw, hs⟩ with
      hsmall | ⟨a, ha, ⟨haw, hsa⟩, hsub⟩ |
      ⟨hor, a, b, ha, hb, ⟨haw, hsa⟩, ⟨hbw, hsb⟩, hsub⟩
    · exact Or.inl (by rwa [blendedSupport_of_safe n C Q w hs])
    · right; left
      refine ⟨a, ha, safe_admissible n C hC Q a haw hsa, ?_⟩
      rwa [blendedSupport_of_safe n C Q w hs, blendedSupport_of_safe n C Q a hsa]
    · right; right
      refine ⟨hor, a, b, ha, hb, safe_admissible n C hC Q a haw hsa,
        safe_admissible n C hC Q b hbw hsb, ?_⟩
      rwa [blendedSupport_of_safe n C Q w hs, blendedSupport_of_safe n C Q a hsa,
        blendedSupport_of_safe n C Q b hsb]
  · rw [blendedSupport_of_not_safe n C Q w hs]
    by_cases hin : w < n
    · left
      rw [raw_input n C w hin]
      simp
    · have hn : n ≤ w := by omega
      have hj : w - n < C.gates.length := by omega
      have he : n + (w - n) = w := by omega
      obtain ⟨a, b, ha, hb, hab, hop, _⟩ := binary_gate n C hC (w - n) hj
      rw [he] at ha hb
      rcases hop with hand | hor
      · left
        rw [raw_and_empty n C w hn hand]
        simp
      · have hu := raw_or_union n C w a b hw hn hor hab ha hb
        have hsuba : orIn n C a ⊆ Q := by
          intro i hi
          exact hraw (hu ▸ Finset.mem_union.mpr (Or.inl hi))
        have hsubb : orIn n C b ⊆ Q := by
          intro i hi
          exact hraw (hu ▸ Finset.mem_union.mpr (Or.inr hi))
        right; right
        refine ⟨⟨hn, hor⟩, a, b, ha, hb, ⟨by omega, hsuba⟩, ⟨by omega, hsubb⟩, ?_⟩
        rw [hu]
        exact Finset.union_subset_union (raw_subset_blendedSupport n C hC Q a (by omega))
          (raw_subset_blendedSupport n C hC Q b (by omega))

end PEqualNP.Outside.L_meta_4970.BlendedSupport

namespace PEqualNP.Outside.L_meta_4970.BlendedSupport

lemma sem_raw_choices_nested {α : Type*} (sem raw X Y : Finset α)
    (hraw : raw ⊆ sem) (hX : X = sem ∨ X = raw) (hY : Y = sem ∨ Y = raw) :
    X ⊆ Y ∨ Y ⊆ X := by
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
  · exact Or.inl (Finset.Subset.refl _)
  · exact Or.inr hraw
  · exact Or.inl hraw
  · exact Or.inl (Finset.Subset.refl _)

lemma sem_raw_large_supports_incompatible {α : Type*} [DecidableEq α]
    (sem raw X Y Q R : Finset α) (hraw : raw ⊆ sem)
    (hX : X = sem ∨ X = raw) (hY : Y = sem ∨ Y = raw)
    (hXQ : X ⊆ Q) (hYR : Y ⊆ R)
    (hXcard : 2 ≤ X.card) (hYcard : 2 ≤ Y.card) (hinter : (Q ∩ R).card ≤ 1) :
    False := by
  rcases sem_raw_choices_nested sem raw X Y hraw hX hY with hXY | hYX
  · have hsub : X ⊆ Q ∩ R := by
      intro a ha
      exact Finset.mem_inter.mpr ⟨hXQ ha, hYR (hXY ha)⟩
    have hcard := Finset.card_le_card hsub
    omega
  · have hsub : Y ⊆ Q ∩ R := by
      intro a ha
      exact Finset.mem_inter.mpr ⟨hXQ (hYX ha), hYR ha⟩
    have hcard := Finset.card_le_card hsub
    omega

lemma sem_raw_charges_disjoint {α ι : Type*} [DecidableEq α]
    (U V : Finset ι) (sem raw BQ BR : ι → Finset α) (Q R : Finset α)
    (hraw : ∀ w ∈ U, raw w ⊆ sem w)
    (hU : ∀ w ∈ U, (BQ w = sem w ∨ BQ w = raw w) ∧ BQ w ⊆ Q ∧ 2 ≤ (BQ w).card)
    (hV : ∀ w ∈ V, (BR w = sem w ∨ BR w = raw w) ∧ BR w ⊆ R ∧ 2 ≤ (BR w).card)
    (hinter : (Q ∩ R).card ≤ 1) : Disjoint U V := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwU hwV
  obtain ⟨hchoiceQ, hsubQ, hcardQ⟩ := hU w hwU
  obtain ⟨hchoiceR, hsubR, hcardR⟩ := hV w hwV
  exact sem_raw_large_supports_incompatible (sem w) (raw w) (BQ w) (BR w) Q R
    (hraw w hwU) hchoiceQ hchoiceR hsubQ hsubR hcardQ hcardR hinter

lemma sem_raw_family_charges_disjoint {α ι κ : Type*} [DecidableEq α]
    (I : Finset ι) (K : ι → Finset κ) (sem raw : κ → Finset α)
    (B : ι → κ → Finset α) (Q : ι → Finset α)
    (hraw : ∀ i ∈ I, ∀ w ∈ K i, raw w ⊆ sem w)
    (hK : ∀ i ∈ I, ∀ w ∈ K i,
      (B i w = sem w ∨ B i w = raw w) ∧ B i w ⊆ Q i ∧ 2 ≤ (B i w).card)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (Q i ∩ Q j).card ≤ 1) :
    (I : Set ι).PairwiseDisjoint K := by
  intro i hi j hj hij
  exact sem_raw_charges_disjoint (K i) (K j) sem raw (B i) (B j) (Q i) (Q j)
    (hraw i hi) (hK i hi) (hK j hj) (hinter i hi j hj hij)

end PEqualNP.Outside.L_meta_4970.BlendedSupport

namespace PEqualNP.Outside.L_meta_4970.BlendedSupport

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4970_aux PEqualNP.Outside.L_meta_4970.SemanticSafe

lemma blendedSupport_choice (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) (w : ℕ) :
    blendedSupport n C Q w = singletonSupport n C w ∨
      blendedSupport n C Q w = orIn n C w := by
  classical
  by_cases hs : Safe Q (wireFn n C w)
  · exact Or.inl (blendedSupport_of_safe n C Q w hs)
  · exact Or.inr (blendedSupport_of_not_safe n C Q w hs)

lemma blendedSupport_of_raw_eq (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (w : ℕ) (hw : w < n + C.gates.length)
    (hraw : orIn n C w = Q) : blendedSupport n C Q w = Q := by
  apply Finset.Subset.antisymm (blendedSupport_subset_Q n C Q w (by rw [hraw]))
  have hsub := raw_subset_blendedSupport n C hC Q w hw
  rwa [hraw] at hsub

lemma blendedSupport_of_pure (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) (w : ℕ)
    (hp : PureOr Q (wireFn n C w)) : blendedSupport n C Q w = Q := by
  rw [blendedSupport_of_safe n C Q w (fun x hx => (hp x).mp hx)]
  exact singletonSupport_pure n C w Q hp

noncomputable def blendedChargedOr (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) :
    Finset ℕ := by
  classical
  exact (Finset.range (n + C.gates.length)).filter fun k =>
    (k < n + C.gates.length ∧ orIn n C k ⊆ Q) ∧
    (n ≤ k ∧ (gateAt C (k - n)).op = GateOp.or) ∧
    2 ≤ (blendedSupport n C Q k).card

lemma blendedChargedOr_disjoint (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q R : Finset (Fin n)) (hQR : (Q ∩ R).card ≤ 1) :
    Disjoint (blendedChargedOr n C Q) (blendedChargedOr n C R) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwQ hwR
  simp only [blendedChargedOr, Finset.mem_filter, Finset.mem_range] at hwQ hwR
  exact sem_raw_large_supports_incompatible
    (singletonSupport n C w) (orIn n C w)
    (blendedSupport n C Q w) (blendedSupport n C R w) Q R
    (raw_subset_singletonSupport n C hC w hwQ.1)
    (blendedSupport_choice n C Q w) (blendedSupport_choice n C R w)
    (blendedSupport_subset_Q n C Q w hwQ.2.1.2)
    (blendedSupport_subset_Q n C R w hwR.2.1.2)
    hwQ.2.2.2 hwR.2.2.2 hQR

lemma blendedChargedOr_subset_allOr (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) :
    blendedChargedOr n C Q ⊆ allOrWires n C := by
  classical
  intro w hw
  simp only [blendedChargedOr, Finset.mem_filter, Finset.mem_range] at hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hw.2.2.1.1, hw.1⟩, hw.2.2.1.2⟩

lemma blended_frontier_or_count (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (W : Finset ℕ)
    (hW : ∀ w ∈ W, w < n + C.gates.length ∧ orIn n C w ⊆ Q) :
    (W.biUnion (blendedSupport n C Q)).card ≤ W.card + (blendedChargedOr n C Q).card := by
  classical
  apply safe_leaf_count
    (fun k => k < n + C.gates.length ∧ orIn n C k ⊆ Q)
    (fun k => n ≤ k ∧ (gateAt C (k - n)).op = GateOp.or)
    (blendedSupport n C Q) (blended_singleton_structure n C hC Q)
  intro w hw
  exact ⟨(hW w hw).1, hW w hw⟩

lemma blended_frontier_family_or_count {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (Q : ι → Finset (Fin n)) (W : ι → Finset ℕ)
    (hQ : ∀ i ∈ I, Q i = (W i).biUnion (blendedSupport n C (Q i)))
    (hW : ∀ i ∈ I, ∀ w ∈ W i,
      w < n + C.gates.length ∧ orIn n C w ⊆ Q i)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (Q i ∩ Q j).card ≤ 1) :
    (∑ i ∈ I, (Q i).card) ≤ (∑ i ∈ I, (W i).card) + (allOrWires n C).card := by
  classical
  have hlocal : ∑ i ∈ I, (Q i).card ≤
      ∑ i ∈ I, ((W i).card + (blendedChargedOr n C (Q i)).card) := by
    apply Finset.sum_le_sum
    intro i hi
    conv_lhs => rw [hQ i hi]
    exact blended_frontier_or_count n C hC (Q i) (W i) (hW i hi)
  have hd : (I : Set ι).PairwiseDisjoint (fun i => blendedChargedOr n C (Q i)) := by
    intro i hi j hj hij
    exact blendedChargedOr_disjoint n C hC (Q i) (Q j) (hinter i hi j hj hij)
  have hsub : I.biUnion (fun i => blendedChargedOr n C (Q i)) ⊆ allOrWires n C := by
    intro w hw
    obtain ⟨i, _, hw⟩ := Finset.mem_biUnion.mp hw
    exact blendedChargedOr_subset_allOr n C (Q i) hw
  have hsum : (∑ i ∈ I, (blendedChargedOr n C (Q i)).card) ≤ (allOrWires n C).card := by
    rw [← Finset.card_biUnion hd]
    exact Finset.card_le_card hsub
  rw [Finset.sum_add_distrib] at hlocal
  omega

end PEqualNP.Outside.L_meta_4970.BlendedSupport

namespace PEqualNP.Outside.L_meta_4970.BlendedSupport

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4970_aux PEqualNP.Outside.L_meta_4970.SemanticSafe
open PEqualNP.Outside.L_meta_4970.Connectivity PEqualNP.Outside.L_meta_4970.ChosenForest
open Classical

lemma blended_star_or_count (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (W : Finset ℕ)
    (hW : ∀ w ∈ W, w < n + C.gates.length ∧ orIn n C w ⊆ Q)
    (hc : ∀ u v : Q, Relation.ReflTransGen
      (fun a b : Q => ∃ w ∈ W,
        (a : Fin n) ∈ blendedSupport n C Q w ∧
        (b : Fin n) ∈ blendedSupport n C Q w) u v) :
    Q.card ≤ 1 + (blendedChargedOr n C Q).card := by
  classical
  exact connected_subset_frontier_count
    (fun k => k < n + C.gates.length ∧ orIn n C k ⊆ Q)
    (fun k => n ≤ k ∧ (gateAt C (k - n)).op = GateOp.or)
    (blendedSupport n C Q) (blended_singleton_structure n C hC Q)
    (n + C.gates.length) W (fun w hw => ⟨(hW w hw).1, hW w hw⟩) Q hc

lemma blended_star_family_count {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (Q : ι → Finset (Fin n)) (W : ι → Finset ℕ)
    (hW : ∀ i ∈ I, ∀ w ∈ W i,
      w < n + C.gates.length ∧ orIn n C w ⊆ Q i)
    (hc : ∀ i ∈ I, ∀ u v : Q i, Relation.ReflTransGen
      (fun a b : Q i => ∃ w ∈ W i,
        (a : Fin n) ∈ blendedSupport n C (Q i) w ∧
        (b : Fin n) ∈ blendedSupport n C (Q i) w) u v)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (Q i ∩ Q j).card ≤ 1) :
    (∑ i ∈ I, (Q i).card) ≤
      I.card + (I.biUnion fun i => blendedChargedOr n C (Q i)).card := by
  classical
  have hlocal : ∑ i ∈ I, (Q i).card ≤
      ∑ i ∈ I, (1 + (blendedChargedOr n C (Q i)).card) := by
    apply Finset.sum_le_sum
    intro i hi
    exact blended_star_or_count n C hC (Q i) (W i) (hW i hi) (hc i hi)
  have hd : (I : Set ι).PairwiseDisjoint (fun i => blendedChargedOr n C (Q i)) := by
    intro i hi j hj hij
    exact blendedChargedOr_disjoint n C hC (Q i) (Q j) (hinter i hi j hj hij)
  rw [Finset.card_biUnion hd]
  simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] using hlocal

lemma chosen_blended_star_tree (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (hQ : Q.Nonempty) (W : Finset ℕ)
    (hW : ∀ w ∈ W, w < n + C.gates.length ∧ orIn n C w ⊆ Q)
    (hc : ∀ u v : Q, Relation.ReflTransGen
      (fun a b : Q => ∃ w ∈ W,
        (a : Fin n) ∈ blendedSupport n C Q w ∧
        (b : Fin n) ∈ blendedSupport n C Q w) u v) :
    ∃ (F : SimpleGraph Q) (K : Finset ℕ) (label : Sym2 Q → ℕ),
      F.IsTree ∧ Set.InjOn label F.edgeSet ∧ K = F.edgeFinset.image label ∧
      K ⊆ blendedChargedOr n C Q ∧ K.card + 1 = Q.card ∧
      ∀ e ∈ F.edgeSet, ∃ u : Q, (u : Fin n) ∈ blendedSupport n C Q (label e) ∧
        ∃ v : Q, (v : Fin n) ∈ blendedSupport n C Q (label e) ∧ e = s(u, v) := by
  classical
  obtain ⟨q, hq⟩ := hQ
  let : Nonempty Q := ⟨⟨q, hq⟩⟩
  let safe := fun w => w < n + C.gates.length ∧ orIn n C w ⊆ Q
  let split := fun w => n ≤ w ∧ (gateAt C (w - n)).op = GateOp.or
  let T : ℕ → Finset Q := fun w => (blendedSupport n C Q w).subtype (fun a => a ∈ Q)
  have hcard : ∀ w, (T w).card ≤ (blendedSupport n C Q w).card := by
    intro w
    exact (Finset.card_subtype _ _).le.trans (Finset.card_filter_le _ _)
  have hstruct : ∀ w, safe w → (T w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe a ∧ T w ⊆ T a) ∨
      (split w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ T w ⊆ T a ∪ T b) := by
    intro w hw
    rcases blended_singleton_structure n C hC Q w hw with
      hs | ⟨a, ha, hsa, hTa⟩ | ⟨hsp, a, b, ha, hb, hsa, hsb, hTab⟩
    · exact Or.inl ((hcard w).trans hs)
    · right; left
      refine ⟨a, ha, hsa, ?_⟩
      intro x hx
      exact Finset.mem_subtype.mpr (hTa (Finset.mem_subtype.mp hx))
    · right; right
      refine ⟨hsp, a, b, ha, hb, hsa, hsb, ?_⟩
      intro x hx
      rcases Finset.mem_union.mp (hTab (Finset.mem_subtype.mp hx)) with hxa | hxb
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_subtype.mpr hxa))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_subtype.mpr hxb))
  have hc' : ∀ u v : Q, Relation.ReflTransGen
      (fun a b => ∃ w ∈ W, a ∈ T w ∧ b ∈ T w) u v := by
    simpa only [T, Finset.mem_subtype] using hc
  obtain ⟨F, K, label, htree, hinj, hK, hsub, hsize, hends, _⟩ :=
    chosen_connected_frontier safe split T hstruct (n + C.gates.length) W
      (fun w hw => ⟨(hW w hw).1, hW w hw⟩) hc'
  refine ⟨F, K, label, htree, hinj, hK, ?_, by simpa using hsize, ?_⟩
  · intro w hw
    have hh := hsub hw
    simp only [Finset.mem_filter, Finset.mem_range, safe, split] at hh
    simp only [blendedChargedOr, Finset.mem_filter, Finset.mem_range]
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.trans (hcard w)⟩
  · intro e he
    simpa only [T, Finset.mem_subtype] using hends e he

end PEqualNP.Outside.L_meta_4970.BlendedSupport

namespace PEqualNP.Outside.L_meta_4970.BlendedSupport

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970_aux PEqualNP.Outside.L_meta_4970.SemanticSafe

lemma mixed_frontier_admissible (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q R : Finset (Fin n)) (w : ℕ) (hw : w < n + C.gates.length)
    (hRQ : R ⊆ Q) (hR : R = orIn n C w ∨ PureOr R (wireFn n C w)) :
    (w < n + C.gates.length ∧ orIn n C w ⊆ Q) ∧ R ⊆ blendedSupport n C Q w := by
  rcases hR with rfl | hp
  · exact ⟨⟨hw, hRQ⟩, raw_subset_blendedSupport n C hC Q w hw⟩
  · have hs : Safe Q (wireFn n C w) := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := (hp x).mp hx
      exact ⟨i, hRQ hi, hxi⟩
    refine ⟨safe_admissible n C hC Q w hw hs, ?_⟩
    rw [blendedSupport_of_safe n C Q w hs, singletonSupport_pure n C w R hp]

lemma mixed_frontier_connectivity (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (W : Finset ℕ) (R : ℕ → Finset (Fin n))
    (hW : ∀ w ∈ W, w < n + C.gates.length)
    (hRQ : ∀ w ∈ W, R w ⊆ Q)
    (hR : ∀ w ∈ W, R w = orIn n C w ∨ PureOr (R w) (wireFn n C w))
    (hc : ∀ u v : Q, Relation.ReflTransGen
      (fun a b : Q => ∃ w ∈ W, (a : Fin n) ∈ R w ∧ (b : Fin n) ∈ R w) u v) :
    (∀ w ∈ W, w < n + C.gates.length ∧ orIn n C w ⊆ Q) ∧
    ∀ u v : Q, Relation.ReflTransGen
      (fun a b : Q => ∃ w ∈ W,
        (a : Fin n) ∈ blendedSupport n C Q w ∧
        (b : Fin n) ∈ blendedSupport n C Q w) u v := by
  have hadm := fun w hw => mixed_frontier_admissible n C hC Q (R w) w
    (hW w hw) (hRQ w hw) (hR w hw)
  refine ⟨fun w hw => (hadm w hw).1, ?_⟩
  intro u v
  induction hc u v with
  | refl => exact Relation.ReflTransGen.refl
  | @tail v z huv hvz ih =>
    obtain ⟨w, hw, hv, hz⟩ := hvz
    exact ih.tail ⟨w, hw, (hadm w hw).2 hv, (hadm w hw).2 hz⟩

lemma mixed_star_or_count (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (W : Finset ℕ) (R : ℕ → Finset (Fin n))
    (hW : ∀ w ∈ W, w < n + C.gates.length)
    (hRQ : ∀ w ∈ W, R w ⊆ Q)
    (hR : ∀ w ∈ W, R w = orIn n C w ∨ PureOr (R w) (wireFn n C w))
    (hc : ∀ u v : Q, Relation.ReflTransGen
      (fun a b : Q => ∃ w ∈ W, (a : Fin n) ∈ R w ∧ (b : Fin n) ∈ R w) u v) :
    Q.card ≤ 1 + (blendedChargedOr n C Q).card := by
  obtain ⟨hW', hc'⟩ := mixed_frontier_connectivity n C hC Q W R hW hRQ hR hc
  exact blended_star_or_count n C hC Q W hW' hc'

end PEqualNP.Outside.L_meta_4970.BlendedSupport

namespace PEqualNP.Outside.L_meta_4970.BlendedSupport

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970_aux PEqualNP.Outside.L_meta_4970.SemanticSafe
open PEqualNP.Outside.L_meta_4970.ComponentPartition

lemma mixed_component_or_count {ι : Type*} [DecidableEq ι]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (I : Finset ι) (W : ι → Finset ℕ) (S : ι → ℕ → Finset (Fin n))
    (hW : ∀ i ∈ I, ∀ w ∈ W i, w < n + C.gates.length ∧
      (S i w = orIn n C w ∨ PureOr (S i w) (wireFn n C w)))
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ((W i).biUnion (S i) ∩ (W j).biUnion (S j)).card ≤ 1) :
    (∑ i ∈ I, ((W i).biUnion (S i)).card) ≤
      (∑ i ∈ I, (parts (W i) (S i)).card) + (allOrWires n C).card := by
  classical
  let J := I.sigma fun i => parts (W i) (S i)
  let V : (Σ _ : ι, Finset (Fin n)) → Finset (Fin n) := fun j => j.2
  let R : (Σ _ : ι, Finset (Fin n)) → Finset ℕ := fun j =>
    rootsInPart (W j.1) (S j.1) j.2
  have hdata : ∀ j ∈ J,
      (∀ w ∈ R j, w < n + C.gates.length ∧ orIn n C w ⊆ V j) ∧
      ∀ u v : V j, Relation.ReflTransGen
        (fun a b : V j => ∃ w ∈ R j,
          (a : Fin n) ∈ blendedSupport n C (V j) w ∧
            (b : Fin n) ∈ blendedSupport n C (V j) w) u v := by
    intro j hj
    obtain ⟨hi, hP⟩ := Finset.mem_sigma.mp hj
    apply mixed_frontier_connectivity n C hC (V j) (R j) (S j.1)
    · intro w hw
      exact (hW j.1 hi w (Finset.mem_filter.mp hw).1).1
    · intro w hw
      exact (Finset.mem_filter.mp hw).2
    · intro w hw
      exact (hW j.1 hi w (Finset.mem_filter.mp hw).1).2
    · exact part_roots_connected (W j.1) (S j.1) j.2 hP
  have hi : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → (V j ∩ V k).card ≤ 1 := by
    intro j hj k hk hne
    have hp : (j.1, j.2) ≠ (k.1, k.2) := by
      intro he
      cases j with
      | mk a P =>
        cases k with
        | mk b Q =>
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact hne rfl
    exact parts_inter_card_le_one I W S hinter
      j.1 (Finset.mem_sigma.mp hj).1 j.2 (Finset.mem_sigma.mp hj).2
      k.1 (Finset.mem_sigma.mp hk).1 k.2 (Finset.mem_sigma.mp hk).2 hp
  have hh := blended_star_family_count n C hC J V R
    (fun j hj => (hdata j hj).1) (fun j hj => (hdata j hj).2) hi
  have hsub : (J.biUnion fun j => blendedChargedOr n C (V j)) ⊆ allOrWires n C := by
    intro w hw
    obtain ⟨j, _, hw⟩ := Finset.mem_biUnion.mp hw
    exact blendedChargedOr_subset_allOr n C (V j) hw
  have hbudget := hh.trans (Nat.add_le_add_left (Finset.card_le_card hsub) J.card)
  simpa only [J, V, Finset.sum_sigma, Finset.card_sigma, parts_sum_card] using hbudget

end PEqualNP.Outside.L_meta_4970.BlendedSupport

namespace PEqualNP.Outside.L_meta_4970.SupportFamily

open Classical

open PEqualNP.Outside.L_meta_4970.ChosenForest
open PEqualNP.Outside.L_meta_4970.ForestLabels
open PEqualNP.Outside.L_meta_4970.MappedLabels
open PEqualNP.Outside.L_meta_4970.OverlapReachability

noncomputable def supportCharges {β : Type*} (M : ℕ)
    (safe split : ℕ → Prop) (U : ℕ → Finset β) : Finset ℕ := by
  classical
  exact (Finset.range M).filter fun w => safe w ∧ split w ∧ 2 ≤ (U w).card

lemma chosen_support_tree_on_finset {β : Type*} [DecidableEq β]
    (safe split : ℕ → Prop) (U : ℕ → Finset β)
    (h : ∀ w, safe w → (U w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe a ∧ U w ⊆ U a) ∨
      (split w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ U w ⊆ U a ∪ U b))
    (M : ℕ) (Q : Finset β) (hQ : Q.Nonempty) (W : Finset ℕ)
    (hW : ∀ w ∈ W, w < M ∧ safe w)
    (hc : ∀ u v : Q, Relation.ReflTransGen
      (fun a b : Q => ∃ w ∈ W, (a : β) ∈ U w ∧ (b : β) ∈ U w) u v) :
    ∃ (F : SimpleGraph Q) (K : Finset ℕ) (label : Sym2 Q → ℕ),
      F.IsTree ∧ Set.InjOn label F.edgeSet ∧ K = F.edgeFinset.image label ∧
      K ⊆ supportCharges M safe split U ∧ K.card + 1 = Q.card ∧
      ∀ e ∈ F.edgeSet, ∃ u : Q, (u : β) ∈ U (label e) ∧
        ∃ v : Q, (v : β) ∈ U (label e) ∧ e = s(u, v) := by
  classical
  obtain ⟨q, hq⟩ := hQ
  let : Nonempty Q := ⟨⟨q, hq⟩⟩
  let T : ℕ → Finset Q := fun w => (U w).subtype (fun a => a ∈ Q)
  have hcard : ∀ w, (T w).card ≤ (U w).card := by
    intro w
    exact (Finset.card_subtype _ _).le.trans (Finset.card_filter_le _ _)
  have hstruct : ∀ w, safe w → (T w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe a ∧ T w ⊆ T a) ∨
      (split w ∧ ∃ a b, a < w ∧ b < w ∧ safe a ∧ safe b ∧ T w ⊆ T a ∪ T b) := by
    intro w hw
    rcases h w hw with hs | ⟨a, ha, hsa, hTa⟩ | ⟨hsp, a, b, ha, hb, hsa, hsb, hTab⟩
    · exact Or.inl ((hcard w).trans hs)
    · right; left
      refine ⟨a, ha, hsa, ?_⟩
      intro x hx
      exact Finset.mem_subtype.mpr (hTa (Finset.mem_subtype.mp hx))
    · right; right
      refine ⟨hsp, a, b, ha, hb, hsa, hsb, ?_⟩
      intro x hx
      rcases Finset.mem_union.mp (hTab (Finset.mem_subtype.mp hx)) with hxa | hxb
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_subtype.mpr hxa))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_subtype.mpr hxb))
  have hc' : ∀ u v : Q, Relation.ReflTransGen
      (fun a b => ∃ w ∈ W, a ∈ T w ∧ b ∈ T w) u v := by
    simpa only [T, Finset.mem_subtype] using hc
  obtain ⟨F, K, label, htree, hinj, hK, hsub, hsize, hends, _⟩ :=
    chosen_connected_frontier safe split T hstruct M W hW hc'
  refine ⟨F, K, label, htree, hinj, hK, ?_, by simpa using hsize, ?_⟩
  · intro w hw
    have hh := hsub hw
    simp only [Finset.mem_filter] at hh
    exact Finset.mem_filter.mpr ⟨hh.1, hh.2.1, hh.2.2.1,
      hh.2.2.2.trans (hcard w)⟩
  · intro e he
    simpa only [T, Finset.mem_subtype] using hends e he

lemma chosen_support_family_forest {ι α β : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq β]
    (M : ℕ) (safe split : ι → ℕ → Prop) (U : ι → ℕ → Finset β)
    (h : ∀ i w, safe i w → (U i w).card ≤ 1 ∨
      (∃ a, a < w ∧ safe i a ∧ U i w ⊆ U i a) ∨
      (split i w ∧ ∃ a b, a < w ∧ b < w ∧ safe i a ∧ safe i b ∧
        U i w ⊆ U i a ∪ U i b))
    (Q : ι → Finset β) (hQ : ∀ i, (Q i).Nonempty) (W : ι → Finset ℕ)
    (hW : ∀ i, ∀ w ∈ W i, w < M ∧ safe i w)
    (hc : ∀ i, ∀ u v : Q i, Relation.ReflTransGen
      (fun a b : Q i => ∃ w ∈ W i, (a : β) ∈ U i w ∧ (b : β) ∈ U i w) u v)
    (hdis : ∀ i j, i ≠ j → Disjoint
      (supportCharges M (safe i) (split i) (U i))
      (supportCharges M (safe j) (split j) (U j)))
    (embed : ∀ i, Q i ↪ α) :
    ∃ (H : SimpleGraph α) (L : Finset ℕ) (label : Sym2 α → ℕ),
      H.IsAcyclic ∧ Set.InjOn label H.edgeSet ∧ L = H.edgeFinset.image label ∧
      L ⊆ Finset.univ.biUnion (fun i => supportCharges M (safe i) (split i) (U i)) ∧
      L.card + Nat.card H.ConnectedComponent = Fintype.card α ∧
      H.Reachable = Relation.ReflTransGen (CoOccurs (fun i => (embed i : Q i → α))) ∧
      ∀ e ∈ H.edgeSet, ∃ i,
        label e ∈ supportCharges M (safe i) (split i) (U i) ∧
        ∃ u : Q i, (u : β) ∈ U i (label e) ∧
          ∃ v : Q i, (v : β) ∈ U i (label e) ∧ e = s(embed i u, embed i v) := by
  classical
  choose F K labels htree hinj hK hsub hsize hends using
    fun i => chosen_support_tree_on_finset (safe i) (split i) (U i) (h i)
      M (Q i) (hQ i) (W i) (hW i) (hc i)
  have hrange : ∀ i, ∀ e ∈ (F i).edgeSet, labels i e ∈ K i := by
    intro i e he
    rw [hK i]
    exact Finset.mem_image.mpr ⟨e, by simpa using he, rfl⟩
  choose mapped hinjMap hrangeMap hsourceMap hpreMap using
    fun i => embedding_label_transport (F i) (embed i) (labels i) (K i) (hinj i) (hrange i)
  let J : ι → SimpleGraph α := fun i => (F i).map (embed i)
  let G : SimpleGraph α := ⨆ i, J i
  have hcover : ∀ e ∈ G.edgeSet, ∃ i ∈ (Finset.univ : Finset ι), e ∈ (J i).edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_iSup] at he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
    exact ⟨i, Finset.mem_univ i, hi⟩
  have hdisK : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint K := by
    intro i hi j hj hij
    exact Finset.disjoint_of_subset_left (hsub i)
      (Finset.disjoint_of_subset_right (hsub j) (hdis i j hij))
  obtain ⟨H, L, label, hHG, hH, hreach, hlabel, hL, hLsub, hcount, horigin⟩ :=
    family_labelled_spanning_forest Finset.univ G J mapped K hcover
      (fun i _ => hinjMap i) (fun i _ => hrangeMap i) hdisK
  have hcomponents : Nat.card H.ConnectedComponent = Nat.card G.ConnectedComponent := by
    unfold SimpleGraph.ConnectedComponent
    rw [hreach]
  have hLall : L ⊆ Finset.univ.biUnion
      (fun i => supportCharges M (safe i) (split i) (U i)) := by
    intro k hk
    obtain ⟨i, hi, hki⟩ := Finset.mem_biUnion.mp (hLsub hk)
    exact Finset.mem_biUnion.mpr ⟨i, hi, hsub i hki⟩
  have hconn : ∀ i, ∀ u v : Q i, H.Reachable (embed i u) (embed i v) := by
    intro i u v
    have hFi := (htree i).connected.preconnected u v
    have hJi : (J i).Reachable (embed i u) (embed i v) :=
      hFi.map (SimpleGraph.Embedding.map (embed i) (F i)).toHom
    rw [hreach]
    exact hJi.mono (le_iSup J i)
  have hfinal : ∀ e ∈ H.edgeSet, ∃ i,
      label e ∈ supportCharges M (safe i) (split i) (U i) ∧
      ∃ u : Q i, (u : β) ∈ U i (label e) ∧
        ∃ v : Q i, (v : β) ∈ U i (label e) ∧ e = s(embed i u, embed i v) := by
    intro e he
    obtain ⟨i, _, hei, heiLabel⟩ := horigin e (SimpleGraph.edgeSet_mono hHG he)
    obtain ⟨d, hd, hde, hLabel⟩ := hpreMap i e hei
    have hsame : label e = labels i d := heiLabel.trans hLabel
    have hprod : label e ∈ supportCharges M (safe i) (split i) (U i) := by
      rw [hsame]
      exact hsub i (hrange i d hd)
    obtain ⟨u, hu, v, hv, huv⟩ := hends i d hd
    refine ⟨i, hprod, u, ?_, v, ?_, ?_⟩
    · simpa only [hsame] using hu
    · simpa only [hsame] using hv
    · rw [← hde, huv]
      rfl
  refine ⟨H, L, label, hH, ?_, hL, hLall, ?_, ?_, hfinal⟩
  · intro e he f hf hef
    exact hlabel (SimpleGraph.edgeSet_mono hHG he) (SimpleGraph.edgeSet_mono hHG hf) hef
  · rw [hcomponents]
    exact hcount
  · apply reachable_eq_cooccurrence H (fun i => (embed i : Q i → α)) hconn
    intro e he
    obtain ⟨i, _, u, _, v, _, huv⟩ := hfinal e he
    exact ⟨i, u, v, huv⟩

end PEqualNP.Outside.L_meta_4970.SupportFamily

namespace PEqualNP.Outside.L_meta_4970.BlendedSupport

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970_aux PEqualNP.Outside.L_meta_4970.SupportFamily
open PEqualNP.Outside.L_meta_4970.OverlapReachability

lemma chosen_blended_family_forest {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : ι → Finset (Fin n)) (hQ : ∀ i, (Q i).Nonempty)
    (W : ι → Finset ℕ)
    (hW : ∀ i, ∀ w ∈ W i, w < n + C.gates.length ∧ orIn n C w ⊆ Q i)
    (hc : ∀ i, ∀ u v : Q i, Relation.ReflTransGen
      (fun a b : Q i => ∃ w ∈ W i,
        (a : Fin n) ∈ blendedSupport n C (Q i) w ∧
        (b : Fin n) ∈ blendedSupport n C (Q i) w) u v)
    (hinter : ∀ i j, i ≠ j → (Q i ∩ Q j).card ≤ 1)
    (embed : ∀ i, Q i ↪ α) :
    ∃ (H : SimpleGraph α) (L : Finset ℕ) (label : Sym2 α → ℕ),
      H.IsAcyclic ∧ Set.InjOn label H.edgeSet ∧ L = H.edgeFinset.image label ∧
      L ⊆ allOrWires n C ∧
      L.card + Nat.card H.ConnectedComponent = Fintype.card α ∧
      H.Reachable = Relation.ReflTransGen (CoOccurs (fun i => (embed i : Q i → α))) ∧
      ∀ e ∈ H.edgeSet, ∃ i, label e ∈ blendedChargedOr n C (Q i) ∧
        ∃ u : Q i, (u : Fin n) ∈ blendedSupport n C (Q i) (label e) ∧
          ∃ v : Q i, (v : Fin n) ∈ blendedSupport n C (Q i) (label e) ∧
            e = s(embed i u, embed i v) := by
  classical
  let safe := fun i w => w < n + C.gates.length ∧ orIn n C w ⊆ Q i
  let split := fun (_ : ι) w => n ≤ w ∧ (gateAt C (w - n)).op = GateOp.or
  let U := fun i => blendedSupport n C (Q i)
  have hcharge : ∀ i, supportCharges (n + C.gates.length) (safe i) (split i) (U i) =
      blendedChargedOr n C (Q i) := by
    intro i
    ext w
    simp only [supportCharges, blendedChargedOr, Finset.mem_filter, safe, split, U]
  obtain ⟨H, L, label, hacyc, hinj, hL, hsub, hcount, hreach, hends⟩ :=
    chosen_support_family_forest (n + C.gates.length) safe split U
      (fun i => blended_singleton_structure n C hC (Q i)) Q hQ W
      (fun i w hw => ⟨(hW i w hw).1, hW i w hw⟩) hc
      (fun i j hij => by
        rw [hcharge i, hcharge j]
        exact blendedChargedOr_disjoint n C hC (Q i) (Q j) (hinter i j hij)) embed
  refine ⟨H, L, label, hacyc, hinj, hL, ?_, hcount, hreach, ?_⟩
  · intro w hw
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hsub hw)
    rw [hcharge i] at hi
    exact blendedChargedOr_subset_allOr n C (Q i) hi
  · intro e he
    obtain ⟨i, hi, u, hu, v, hv, huv⟩ := hends e he
    rw [hcharge i] at hi
    exact ⟨i, hi, u, hu, v, hv, huv⟩

end PEqualNP.Outside.L_meta_4970.BlendedSupport

namespace PEqualNP.Outside.L_meta_4970.BlendedSupport

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970_aux PEqualNP.Outside.L_meta_4970.SemanticSafe
open PEqualNP.Outside.L_meta_4970.SupportFamily
open PEqualNP.Outside.L_meta_4970.OverlapReachability

/-- An earlier admissible wire that already contains the blended support. -/
def HasBlendedCarrier (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) (w : ℕ) : Prop :=
  ∃ a, a < w ∧ (a < n + C.gates.length ∧ orIn n C a ⊆ Q) ∧
    blendedSupport n C Q w ⊆ blendedSupport n C Q a

noncomputable def productiveBlendedOr (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) :
    Finset ℕ := (blendedChargedOr n C Q).filter fun w => ¬ HasBlendedCarrier n C Q w

lemma productiveBlendedOr_subset (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) :
    productiveBlendedOr n C Q ⊆ blendedChargedOr n C Q :=
  Finset.filter_subset _ _

lemma productiveBlendedOr_disjoint (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q R : Finset (Fin n)) (h : (Q ∩ R).card ≤ 1) :
    Disjoint (productiveBlendedOr n C Q) (productiveBlendedOr n C R) :=
  Finset.disjoint_of_subset_left (productiveBlendedOr_subset n C Q)
    (Finset.disjoint_of_subset_right (productiveBlendedOr_subset n C R)
      (blendedChargedOr_disjoint n C hC Q R h))

lemma productiveBlendedOr_subset_allOr (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) :
    productiveBlendedOr n C Q ⊆ allOrWires n C :=
  (productiveBlendedOr_subset n C Q).trans (blendedChargedOr_subset_allOr n C Q)

lemma productiveBlendedOr_no_carrier (n : ℕ) (C : Circuit) (Q : Finset (Fin n))
    (w : ℕ) (hw : w ∈ productiveBlendedOr n C Q)
    (a : ℕ) (ha : a < w) (ha' : a < n + C.gates.length) (hraw : orIn n C a ⊆ Q) :
    ¬ blendedSupport n C Q w ⊆ blendedSupport n C Q a := by
  intro hsub
  exact (Finset.mem_filter.mp hw).2 ⟨a, ha, ⟨ha', hraw⟩, hsub⟩

lemma productive_blended_singleton_structure (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) :
    ∀ w, (w < n + C.gates.length ∧ orIn n C w ⊆ Q) →
      (blendedSupport n C Q w).card ≤ 1 ∨
      (∃ a, a < w ∧ (a < n + C.gates.length ∧ orIn n C a ⊆ Q) ∧
        blendedSupport n C Q w ⊆ blendedSupport n C Q a) ∨
      (((n ≤ w ∧ (gateAt C (w - n)).op = GateOp.or) ∧
          ¬ HasBlendedCarrier n C Q w) ∧
        ∃ a b, a < w ∧ b < w ∧
          (a < n + C.gates.length ∧ orIn n C a ⊆ Q) ∧
          (b < n + C.gates.length ∧ orIn n C b ⊆ Q) ∧
          blendedSupport n C Q w ⊆ blendedSupport n C Q a ∪ blendedSupport n C Q b) := by
  intro w hw
  by_cases hcarry : HasBlendedCarrier n C Q w
  · exact Or.inr (Or.inl hcarry)
  · rcases blended_singleton_structure n C hC Q w hw with hsmall | hfree | ⟨hop, hsplit⟩
    · exact Or.inl hsmall
    · exact False.elim (hcarry hfree)
    · exact Or.inr (Or.inr ⟨⟨hop, hcarry⟩, hsplit⟩)

lemma blended_or_operands (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (w : ℕ) (hw : w < n + C.gates.length)
    (hn : n ≤ w) (hor : (gateAt C (w - n)).op = GateOp.or)
    (hraw : orIn n C w ⊆ Q) :
    ∃ a b, (gateAt C (w - n)).inputs = [a, b] ∧ a < w ∧ b < w ∧
      (a < n + C.gates.length ∧ orIn n C a ⊆ Q) ∧
      (b < n + C.gates.length ∧ orIn n C b ⊆ Q) ∧
      blendedSupport n C Q w ⊆ blendedSupport n C Q a ∪ blendedSupport n C Q b := by
  have heq : n + (w - n) = w := by omega
  obtain ⟨a, b, ha, hb, hab, _, heval⟩ := binary_gate n C hC (w - n) (by omega)
  rw [heq] at ha hb heval
  have hrawunion := raw_or_union n C w a b hw hn hor hab ha hb
  have hrawa : orIn n C a ⊆ Q := by
    intro i hi
    exact hraw (hrawunion ▸ Finset.mem_union.mpr (Or.inl hi))
  have hrawb : orIn n C b ⊆ Q := by
    intro i hi
    exact hraw (hrawunion ▸ Finset.mem_union.mpr (Or.inr hi))
  refine ⟨a, b, hab, ha, hb, ⟨by omega, hrawa⟩, ⟨by omega, hrawb⟩, ?_⟩
  by_cases hs : Safe Q (wireFn n C w)
  · have hv : ∀ x, wireFn n C w x = (wireFn n C a x || wireFn n C b x) := by
      intro x
      rw [heval x, hor]
      simp [GateOp.eval]
    have hs' : Safe Q (fun x => wireFn n C a x || wireFn n C b x) := by
      simpa only [← hv] using hs
    obtain ⟨hsa, hsb⟩ := safe_or_iff.mp hs'
    rw [blendedSupport_of_safe n C Q w hs,
      blendedSupport_of_safe n C Q a hsa, blendedSupport_of_safe n C Q b hsb]
    intro i hi
    simpa only [mem_singletonSupport, hv, Bool.or_eq_true, Finset.mem_union] using hi
  · rw [blendedSupport_of_not_safe n C Q w hs, hrawunion]
    exact Finset.union_subset_union (raw_subset_blendedSupport n C hC Q a (by omega))
      (raw_subset_blendedSupport n C hC Q b (by omega))

lemma productiveBlendedOr_binary_operands (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (w : ℕ) (hw : w ∈ productiveBlendedOr n C Q) :
    n ≤ w ∧ w < n + C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or ∧
      ∃ a b, (gateAt C (w - n)).inputs = [a, b] ∧ a < w ∧ b < w ∧
        (a < n + C.gates.length ∧ orIn n C a ⊆ Q) ∧
        (b < n + C.gates.length ∧ orIn n C b ⊆ Q) ∧
        blendedSupport n C Q w ⊆ blendedSupport n C Q a ∪ blendedSupport n C Q b ∧
        (blendedSupport n C Q a).Nonempty ∧ (blendedSupport n C Q b).Nonempty ∧
        (singletonSupport n C a).Nonempty ∧ (singletonSupport n C b).Nonempty ∧
        ¬ blendedSupport n C Q w ⊆ blendedSupport n C Q a ∧
        ¬ blendedSupport n C Q w ⊆ blendedSupport n C Q b := by
  have hm := productiveBlendedOr_subset n C Q hw
  obtain ⟨_, ⟨hwlim, hraw⟩, ⟨hn, hor⟩, _⟩ := Finset.mem_filter.mp hm
  obtain ⟨a, b, hab, ha, hb, hadm, hbdm, hsub⟩ :=
    blended_or_operands n C hC Q w hwlim hn hor hraw
  have hna := productiveBlendedOr_no_carrier n C Q w hw a ha hadm.1 hadm.2
  have hnb := productiveBlendedOr_no_carrier n C Q w hw b hb hbdm.1 hbdm.2
  have hane : (blendedSupport n C Q a).Nonempty := by
    by_contra h
    have hz := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hz, Finset.empty_union] at hsub
    exact hnb hsub
  have hbne : (blendedSupport n C Q b).Nonempty := by
    by_contra h
    have hz := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hz, Finset.union_empty] at hsub
    exact hna hsub
  exact ⟨hn, hwlim, hor, a, b, hab, ha, hb, hadm, hbdm, hsub, hane, hbne,
    hane.mono (blendedSupport_subset_singletonSupport n C hC Q a hadm.1),
    hbne.mono (blendedSupport_subset_singletonSupport n C hC Q b hbdm.1), hna, hnb⟩

lemma productiveBlendedOr_no_empty_semantic_child (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (w : ℕ) (hw : w ∈ productiveBlendedOr n C Q)
    (a b : ℕ) (hab : (gateAt C (w - n)).inputs = [a, b]) :
    singletonSupport n C a ≠ ∅ ∧ singletonSupport n C b ≠ ∅ := by
  obtain ⟨_, _, _, a', b', hab', _, _, _, _, _, _, _, hane, hbne, _, _⟩ :=
    productiveBlendedOr_binary_operands n C hC Q w hw
  have heq : [a', b'] = [a, b] := hab'.symm.trans hab
  have ha : a' = a := (List.cons.inj heq).1
  have hb : b' = b := (List.cons.inj (List.cons.inj heq).2).1
  subst a'
  subst b'
  exact ⟨Finset.nonempty_iff_ne_empty.mp hane, Finset.nonempty_iff_ne_empty.mp hbne⟩

end PEqualNP.Outside.L_meta_4970.BlendedSupport

namespace PEqualNP.Outside.L_meta_4970.BlendedSupport

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970_aux PEqualNP.Outside.L_meta_4970.SemanticSafe
open PEqualNP.Outside.L_meta_4970.SupportFamily
open PEqualNP.Outside.L_meta_4970.OverlapReachability

lemma chosen_productive_blended_star_tree (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (hQ : Q.Nonempty) (W : Finset ℕ)
    (hW : ∀ w ∈ W, w < n + C.gates.length ∧ orIn n C w ⊆ Q)
    (hc : ∀ u v : Q, Relation.ReflTransGen
      (fun a b : Q => ∃ w ∈ W,
        (a : Fin n) ∈ blendedSupport n C Q w ∧
        (b : Fin n) ∈ blendedSupport n C Q w) u v) :
    ∃ (F : SimpleGraph Q) (K : Finset ℕ) (label : Sym2 Q → ℕ),
      F.IsTree ∧ Set.InjOn label F.edgeSet ∧ K = F.edgeFinset.image label ∧
      K ⊆ productiveBlendedOr n C Q ∧ K.card + 1 = Q.card ∧
      ∀ e ∈ F.edgeSet, ∃ u : Q, (u : Fin n) ∈ blendedSupport n C Q (label e) ∧
        ∃ v : Q, (v : Fin n) ∈ blendedSupport n C Q (label e) ∧ e = s(u, v) := by
  let safe := fun w => w < n + C.gates.length ∧ orIn n C w ⊆ Q
  let split := fun w => (n ≤ w ∧ (gateAt C (w - n)).op = GateOp.or) ∧
    ¬ HasBlendedCarrier n C Q w
  let U := blendedSupport n C Q
  have hcharge : supportCharges (n + C.gates.length) safe split U =
      productiveBlendedOr n C Q := by
    ext w
    simp only [supportCharges, productiveBlendedOr, blendedChargedOr,
      Finset.mem_filter, safe, split, U]
    tauto
  obtain ⟨F, K, label, htree, hinj, hK, hsub, hsize, hends⟩ :=
    chosen_support_tree_on_finset safe split U (productive_blended_singleton_structure n C hC Q)
      (n + C.gates.length) Q hQ W (fun w hw => ⟨(hW w hw).1, hW w hw⟩) hc
  rw [hcharge] at hsub
  exact ⟨F, K, label, htree, hinj, hK, hsub, hsize, hends⟩

end PEqualNP.Outside.L_meta_4970.BlendedSupport

namespace PEqualNP.Outside.L_meta_4970.BlendedSupport

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970_aux PEqualNP.Outside.L_meta_4970.SupportFamily
open PEqualNP.Outside.L_meta_4970.OverlapReachability

lemma chosen_productive_blended_family_forest {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : ι → Finset (Fin n)) (hQ : ∀ i, (Q i).Nonempty)
    (W : ι → Finset ℕ)
    (hW : ∀ i, ∀ w ∈ W i, w < n + C.gates.length ∧ orIn n C w ⊆ Q i)
    (hc : ∀ i, ∀ u v : Q i, Relation.ReflTransGen
      (fun a b : Q i => ∃ w ∈ W i,
        (a : Fin n) ∈ blendedSupport n C (Q i) w ∧
        (b : Fin n) ∈ blendedSupport n C (Q i) w) u v)
    (hinter : ∀ i j, i ≠ j → (Q i ∩ Q j).card ≤ 1)
    (embed : ∀ i, Q i ↪ α) :
    ∃ (H : SimpleGraph α) (L : Finset ℕ) (label : Sym2 α → ℕ),
      H.IsAcyclic ∧ Set.InjOn label H.edgeSet ∧ L = H.edgeFinset.image label ∧
      L ⊆ allOrWires n C ∧
      L.card + Nat.card H.ConnectedComponent = Fintype.card α ∧
      H.Reachable = Relation.ReflTransGen (CoOccurs (fun i => (embed i : Q i → α))) ∧
      ∀ e ∈ H.edgeSet, ∃ i, label e ∈ productiveBlendedOr n C (Q i) ∧
        ∃ u : Q i, (u : Fin n) ∈ blendedSupport n C (Q i) (label e) ∧
          ∃ v : Q i, (v : Fin n) ∈ blendedSupport n C (Q i) (label e) ∧
            e = s(embed i u, embed i v) := by
  classical
  let safe := fun i w => w < n + C.gates.length ∧ orIn n C w ⊆ Q i
  let split := fun i w => (n ≤ w ∧ (gateAt C (w - n)).op = GateOp.or) ∧
    ¬ HasBlendedCarrier n C (Q i) w
  let U := fun i => blendedSupport n C (Q i)
  have hcharge : ∀ i, supportCharges (n + C.gates.length) (safe i) (split i) (U i) =
      productiveBlendedOr n C (Q i) := by
    intro i
    ext w
    simp only [supportCharges, productiveBlendedOr, blendedChargedOr,
      Finset.mem_filter, safe, split, U]
    tauto
  obtain ⟨H, L, label, hacyc, hinj, hL, hsub, hcount, hreach, hends⟩ :=
    chosen_support_family_forest (n + C.gates.length) safe split U
      (fun i => productive_blended_singleton_structure n C hC (Q i)) Q hQ W
      (fun i w hw => ⟨(hW i w hw).1, hW i w hw⟩) hc
      (fun i j hij => by
        rw [hcharge i, hcharge j]
        exact productiveBlendedOr_disjoint n C hC (Q i) (Q j) (hinter i j hij)) embed
  refine ⟨H, L, label, hacyc, hinj, hL, ?_, hcount, hreach, ?_⟩
  · intro w hw
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hsub hw)
    rw [hcharge i] at hi
    exact productiveBlendedOr_subset_allOr n C (Q i) hi
  · intro e he
    obtain ⟨i, hi, u, hu, v, hv, huv⟩ := hends e he
    rw [hcharge i] at hi
    exact ⟨i, hi, u, hu, v, hv, huv⟩

end PEqualNP.Outside.L_meta_4970.BlendedSupport

namespace PEqualNP.Outside.L_meta_4970.AppendPurePairs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970_aux

def pairGate {n : ℕ} (p : Fin n × Fin n) : Gate :=
  ⟨GateOp.or, [p.1.val, p.2.val]⟩

def appendPurePairs {n : ℕ} (C : Circuit) (P : List (Fin n × Fin n)) : Circuit :=
  ⟨C.gates ++ P.map pairGate, C.output⟩

lemma appendPurePairs_size {n : ℕ} (C : Circuit) (P : List (Fin n × Fin n)) :
    (appendPurePairs C P).size = C.size + P.length := by
  simp [appendPurePairs, Circuit.size]

lemma appendPurePairs_output {n : ℕ} (C : Circuit) (P : List (Fin n × Fin n)) :
    (appendPurePairs C P).output = C.output := rfl

lemma appendPurePairs_old_gate {n : ℕ} (C : Circuit) (P : List (Fin n × Fin n))
    (j : ℕ) (hj : j < C.gates.length) :
    gateAt (appendPurePairs C P) j = gateAt C j := by
  unfold gateAt appendPurePairs
  exact List.getD_append _ _ _ _ hj

lemma appendPurePairs_new_gate {n : ℕ} (C : Circuit) (P : List (Fin n × Fin n))
    (j : ℕ) (hj : j < P.length) :
    gateAt (appendPurePairs C P) (C.gates.length + j) = pairGate P[j] := by
  simp [gateAt, appendPurePairs, hj]

lemma appendPurePairs_old_wires {n : ℕ} (C : Circuit) (P : List (Fin n × Fin n))
    (x : List Bool) (w : ℕ) (hw : w < x.length + C.gates.length) :
    ((appendPurePairs C P).wires x).getD w false = (C.wires x).getD w false := by
  change (wiresFrom (C.gates ++ P.map pairGate) x).getD w false =
    (wiresFrom C.gates x).getD w false
  rw [wiresFrom_append, getD_wiresFrom_lt]
  simpa [length_wiresFrom] using hw

lemma appendPurePairs_old_wireFn {n : ℕ} (C : Circuit) (P : List (Fin n × Fin n))
    (w : ℕ) (hw : w < n + C.gates.length) (x : Fin n → Bool) :
    wireFn n (appendPurePairs C P) w x = wireFn n C w x := by
  apply appendPurePairs_old_wires
  simpa using hw

lemma appendPurePairs_eval {n : ℕ} (C : Circuit) (P : List (Fin n × Fin n))
    (houtput : C.output < n + C.gates.length) (x : Fin n → Bool) :
    (appendPurePairs C P).eval (List.ofFn x) = C.eval (List.ofFn x) :=
  appendPurePairs_old_wireFn C P C.output houtput x

lemma appendPurePairs_AO2 {n : ℕ} (C : Circuit) (P : List (Fin n × Fin n))
    (hC : IsAO2 n C) : IsAO2 n (appendPurePairs C P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hC.1 g hg
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
      exact Or.inr rfl
  · intro j hj i hi
    by_cases hold : j < C.gates.length
    · rw [appendPurePairs_old_gate C P j hold] at hi
      exact hC.2.1 j hold i hi
    · have hjp : j - C.gates.length < P.length := by
        simp only [appendPurePairs, List.length_append, List.length_map] at hj
        omega
      have he : C.gates.length + (j - C.gates.length) = j := by omega
      have hgate := appendPurePairs_new_gate C P (j - C.gates.length) hjp
      rw [he] at hgate
      rw [hgate] at hi
      simp [pairGate] at hi
      rcases hi with rfl | rfl <;> omega
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hC.2.2 g hg
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
      rfl

lemma appendPurePairs_new_wireFn {n : ℕ} (C : Circuit) (P : List (Fin n × Fin n))
    (hC : IsAO2 n C) (j : ℕ) (hj : j < P.length) (x : Fin n → Bool) :
    wireFn n (appendPurePairs C P) (n + C.gates.length + j) x =
      (x P[j].1 || x P[j].2) := by
  have hk : C.gates.length + j < (appendPurePairs C P).gates.length := by
    simp only [appendPurePairs, List.length_append, List.length_map]
    omega
  obtain ⟨a, b, ha, hb, hab, hop, heval⟩ :=
    binary_gate n (appendPurePairs C P) (appendPurePairs_AO2 C P hC)
      (C.gates.length + j) hk
  rw [appendPurePairs_new_gate C P j hj] at hab heval
  have he : [P[j].1.val, P[j].2.val] = [a, b] := hab
  have ha' := (List.cons.inj he).1
  have hb' := (List.cons.inj (List.cons.inj he).2).1
  subst a
  subst b
  have hv := heval x
  simp only [pairGate, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq] at hv
  rw [wireFn_input n _ _ P[j].1.isLt, wireFn_input n _ _ P[j].2.isLt] at hv
  simpa [Nat.add_assoc] using hv


lemma appendPurePairs_new_pureOr {n : ℕ} (C : Circuit) (P : List (Fin n × Fin n))
    (hC : IsAO2 n C) (j : ℕ) (hj : j < P.length) :
    SemanticSafe.PureOr {P[j].1, P[j].2}
      (wireFn n (appendPurePairs C P) (n + C.gates.length + j)) := by
  intro x
  rw [appendPurePairs_new_wireFn C P hC j hj x]
  simp

lemma output_valid_of_true (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hx : C.eval (List.ofFn x) = true) : C.output < n + C.gates.length := by
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    change (wiresFrom C.gates (List.ofFn x)).length = _
    simp [length_wiresFrom]
  by_contra hn
  have hout : (C.wires (List.ofFn x)).length ≤ C.output := by omega
  rw [Circuit.eval, List.getD_eq_default _ _ hout] at hx
  exact Bool.noConfusion hx

end PEqualNP.Outside.L_meta_4970.AppendPurePairs


namespace PEqualNP.Outside.L_meta_4970.CompletionReduction

lemma diagonal_cover_card (p : ℕ) (S : Finset (Fin (p + p)))
    (hS : ∀ a : Fin p, Fin.castAdd p a ∈ S ∨ Fin.natAdd p a ∈ S) :
    p ≤ S.card := by
  classical
  let f : Fin p → Fin (p + p) := fun a =>
    if Fin.castAdd p a ∈ S then Fin.castAdd p a else Fin.natAdd p a
  have hf : ∀ a ∈ (Finset.univ : Finset (Fin p)), f a ∈ S := by
    intro a _
    dsimp [f]
    split_ifs with ha
    · exact ha
    · exact (hS a).resolve_left ha
  have hi : ∀ a ∈ (Finset.univ : Finset (Fin p)),
      ∀ b ∈ (Finset.univ : Finset (Fin p)), f a = f b → a = b := by
    intro a _ b _ hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    dsimp [f] at hv
    split_ifs at hv <;> simp only [Fin.val_castAdd, Fin.val_natAdd] at hv <;> omega
  have hh := Finset.card_le_card_of_injOn f hf hi
  simpa using hh

lemma paired_completion_budget (p k : ℕ)
    (E : Finset (Fin p × Fin p))
    (C D : PEqualNP.CircuitLowerBounds.Circuit)
    (hdiag : ∀ a : Fin p, (a, a) ∈ E)
    (hcard : E.card = 2 * k)
    (hsize : D.size ≤ C.size + p + k)
    (hbound : ∃ S : Finset (Fin (p + p)),
      (∀ a b, (a,b) ∈ E → Fin.castAdd p a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
        E.card + S.card ≤ D.size + 1) :
    k ≤ C.size + 1 := by
  obtain ⟨S, hS, hb⟩ := hbound
  have hs := diagonal_cover_card p S (fun a => hS a a (hdiag a))
  omega

end PEqualNP.Outside.L_meta_4970.CompletionReduction

namespace PEqualNP.Outside.L_meta_4970

namespace Interval

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma run_append (gs hs : List Gate) (x : List Bool) :
    run (gs ++ hs) x = run hs (run gs x) := by
  simp [run, List.foldl_append]

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = step (run gs x) g := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
      change (run gs (step x g)).length = _
      rw [ih]
      simp [step]
      omega

lemma getD_append_left (a b : List Bool) (i : ℕ) (hi : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right (a b : List Bool) (i : ℕ) (hi : a.length ≤ i) :
    (a ++ b).getD i false = b.getD (i - a.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_ge (a : List Bool) (i : ℕ) (hi : a.length ≤ i) :
    a.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_snoc (a : List Bool) (b : Bool) (i : ℕ) :
    (a ++ [b]).getD i false = if i = a.length then b else a.getD i false := by
  by_cases hi : i < a.length
  · rw [getD_append_left _ _ _ hi, ite_eq_right (by omega)]
  · rw [getD_append_right _ _ _ (by omega)]
    by_cases he : i = a.length
    · simp [he]
    · rw [ite_eq_right he]
      rw [getD_ge [b] (i - a.length) (by simp only [List.length_singleton]; omega)]
      rw [getD_ge a i (by omega)]

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma no_direct_left_tCount_zero (p l : ℕ) (C : Circuit)
    (h : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, p ≤ i) :
    PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 := by
  classical
  unfold PEqualNP.TwoColour.tCount PEqualNP.TwoColour.twoColour
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g hg hmix
  obtain ⟨_, _, ⟨i, hi, hcol⟩, _⟩ := hmix
  have hlt : (i : ℕ) < p := by simpa using hcol
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain heq | ⟨j, hj, _, hop, hin⟩ := hi
  · have := i.isLt
    omega
  · have := h j hj hop i hin
    omega

def copies (a k : ℕ) : List Gate :=
  (List.range k).map fun i => ⟨GateOp.and, [a + i, a + i]⟩

lemma copies_length (a k : ℕ) : (copies a k).length = k := by simp [copies]

lemma copies_succ (a k : ℕ) :
    copies a (k + 1) = copies a k ++ [⟨GateOp.and, [a + k, a + k]⟩] := by
  simp [copies, List.range_succ]

lemma copies_run (a k : ℕ) (x : List Bool) (hk : a + k ≤ x.length) :
    run (copies a k) x = x ++ (x.drop a).take k := by
  induction k with
  | zero => simp [copies, run]
  | succ k ih =>
      rw [copies_succ, run_snoc, ih (by omega)]
      have hi : a + k < x.length := by omega
      have hd : k < (x.drop a).length := by simp; omega
      have hv : (x ++ (x.drop a).take k).getD (a + k) false = (x.drop a)[k] := by
        rw [getD_append_left _ _ _ hi]
        simp [List.getD_eq_getElem?_getD, hi]
      simp only [step, List.map_cons, List.map_nil, hv, GateOp.eval, List.all_cons,
        List.all_nil, id_eq, Bool.and_true, Bool.and_self]
      rw [List.take_succ_eq_append_getElem hd, List.append_assoc]

def redirect (n a k w : ℕ) : ℕ :=
  if a ≤ w ∧ w < a + k then n + (w - a) else if w < n then w else k + w

def redirectGate (n a k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (redirect n a k)⟩

def transform (n a k : ℕ) (C : Circuit) : Circuit :=
  ⟨copies a k ++ C.gates.map (redirectGate n a k), redirect n a k C.output⟩

lemma redirect_avoids (n a k w : ℕ) (h : a + k ≤ n) :
    ¬ (a ≤ redirect n a k w ∧ redirect n a k w < a + k) := by
  unfold redirect
  split_ifs <;> omega

lemma redirect_gate_wire (n a k j : ℕ) (h : a + k ≤ n) :
    redirect n a k (n + j) = k + (n + j) := by
  simp [redirect, show ¬ (a ≤ n + j ∧ n + j < a + k) by omega,
    show ¬ n + j < n by omega]

lemma redirect_eq_last (n a k j w : ℕ) (h : a + k ≤ n) :
    redirect n a k w = n + k + j ↔ w = n + j := by
  unfold redirect
  split_ifs <;> omega

lemma redirect_initial (n a k : ℕ) (h : a + k ≤ n)
    (x : List Bool) (hx : x.length = n) (w : ℕ) :
    (run (copies a k) x).getD (redirect n a k w) false = x.getD w false := by
  rw [copies_run _ _ _ (by omega)]
  unfold redirect
  split_ifs with hw hn
  · rw [getD_append_right _ _ _ (by omega)]
    have hwk : w - a < k := by omega
    have hwa : a + (w - a) = w := by omega
    simp only [hx, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, hwk, List.getElem?_drop, hwa]
  · exact getD_append_left _ _ _ (by omega)
  · rw [getD_ge (x ++ (x.drop a).take k) (k + w) (by simp only [List.length_append, List.length_take, List.length_drop, hx]; omega)]
    exact (getD_ge x w (by omega)).symm

lemma redirect_run (n a k : ℕ) (h : a + k ≤ n) (gs : List Gate)
    (x : List Bool) (hx : x.length = n) (w : ℕ) :
    (run (copies a k ++ gs.map (redirectGate n a k)) x).getD (redirect n a k w) false =
      (run gs x).getD w false := by
  induction gs using List.reverseRecOn generalizing w with
  | nil => simpa [run] using redirect_initial n a k h x hx w
  | append_singleton gs g ih =>
      have hv : g.op.eval (g.inputs.map fun i =>
          (run (copies a k ++ gs.map (redirectGate n a k)) x).getD (redirect n a k i) false) =
          g.op.eval (g.inputs.map fun i => (run gs x).getD i false) := by
        congr 1
        apply List.map_congr_left
        intro i _
        exact ih i
      simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
        run_snoc, step, redirectGate, List.map_map]
      rw [getD_snoc, getD_snoc]
      have hlen : (run (copies a k ++ gs.map (redirectGate n a k)) x).length =
          n + k + gs.length := by simp [run_length, hx, copies_length, Nat.add_assoc]
      have hlen' : (run gs x).length = n + gs.length := by rw [run_length, hx]
      simp only [hlen, hlen', redirect_eq_last n a k gs.length w h]
      split_ifs
      · exact hv
      · exact ih w

lemma transform_wires (n a k : ℕ) (h : a + k ≤ n)
    (C : Circuit) (x : Fin n → Bool) (w : ℕ) :
    ((transform n a k C).wires (List.ofFn x)).getD (redirect n a k w) false =
      (C.wires (List.ofFn x)).getD w false := by
  exact redirect_run n a k h C.gates (List.ofFn x) (by simp) w

lemma transform_fun (n a k : ℕ) (h : a + k ≤ n) (C : Circuit) :
    circuitFun n (transform n a k C) = circuitFun n C := by
  funext x
  exact transform_wires n a k h C x C.output

lemma transform_size (n a k : ℕ) (C : Circuit) :
    (transform n a k C).size = C.size + k := by
  simp [transform, Circuit.size, copies_length, Nat.add_comm]

lemma gateAt_transform_before (n a k : ℕ) (C : Circuit) (j : ℕ) (hj : j < k) :
    gateAt (transform n a k C) j = ⟨GateOp.and, [a + j, a + j]⟩ := by
  simp only [gateAt, transform, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (show j < (copies a k).length by simpa [copies_length] using hj)]
  simp [copies, hj]

lemma gateAt_transform_after (n a k : ℕ) (C : Circuit) (j : ℕ)
    (hj : j < C.gates.length) :
    gateAt (transform n a k C) (k + j) = redirectGate n a k (gateAt C j) := by
  simp [gateAt, transform, List.getD_eq_getElem?_getD, copies_length, hj]

lemma redirect_lt (n a k j w : ℕ) (_h : a + k ≤ n) (hw : w < n + j) :
    redirect n a k w < n + (k + j) := by
  unfold redirect
  split_ifs <;> omega

lemma transform_ao2 (n a k : ℕ) (h : a + k ≤ n) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.TopForm.IsAO2 n (transform n a k C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    change g ∈ copies a k ++ C.gates.map (redirectGate n a k) at hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
      exact Or.inl rfl
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      exact hC.1 u hu
  · intro j hj i hi
    have hlen : (transform n a k C).gates.length = k + C.gates.length := by
      simp [transform, copies_length]
    by_cases hjk : j < k
    · rw [gateAt_transform_before n a k C j hjk] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
      subst i
      omega
    · obtain ⟨q, rfl⟩ : ∃ q, j = k + q := ⟨j - k, by omega⟩
      have hq : q < C.gates.length := by omega
      rw [gateAt_transform_after n a k C q hq] at hi
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
      exact redirect_lt n a k q w h (hC.2.1 q hq w hw)
  · intro g hg
    change g ∈ copies a k ++ C.gates.map (redirectGate n a k) at hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
      rfl
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      simpa [redirectGate] using hC.2.2 u hu

lemma transform_or_avoids (n a k : ℕ) (h : a + k ≤ n) (C : Circuit) :
    ∀ j < (transform n a k C).gates.length,
      (gateAt (transform n a k C) j).op = GateOp.or →
      ∀ i ∈ (gateAt (transform n a k C) j).inputs, ¬ (a ≤ i ∧ i < a + k) := by
  intro j hj hop i hi
  have hg := gateAt_mem (transform n a k C) j hj
  change gateAt (transform n a k C) j ∈ copies a k ++ C.gates.map (redirectGate n a k) at hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨q, _, heq⟩ := List.mem_map.mp hg
    rw [← heq] at hop
    cases hop
  · obtain ⟨g, _, heq⟩ := List.mem_map.mp hg
    rw [← heq] at hi
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hi
    exact redirect_avoids n a k w h

lemma no_direct_right_tCount_zero (p l : ℕ) (C : Circuit)
    (h : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ∀ i ∈ (gateAt C j).inputs, ¬ (p ≤ i ∧ i < p + l)) :
    PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 := by
  classical
  unfold PEqualNP.TwoColour.tCount PEqualNP.TwoColour.twoColour
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g hg hmix
  obtain ⟨_, _, _, ⟨i, hi, hcol⟩⟩ := hmix
  have hle : p ≤ (i : ℕ) := by simpa using hcol
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain heq | ⟨j, hj, _, hop, hin⟩ := hi
  · have := i.isLt
    omega
  · exact h j hj hop i hin ⟨hle, i.isLt⟩

lemma transform_left_tCount (p l : ℕ) (C : Circuit) :
    PEqualNP.TwoColour.tCount (p + l) (transform (p + l) 0 p C)
      (fun i => decide (p ≤ i)) = 0 := by
  apply no_direct_left_tCount_zero
  intro j hj hop i hi
  have h := transform_or_avoids (p + l) 0 p (by omega) C j hj hop i hi
  omega

lemma transform_right_tCount (p l : ℕ) (C : Circuit) :
    PEqualNP.TwoColour.tCount (p + l) (transform (p + l) p l C)
      (fun i => decide (p ≤ i)) = 0 := by
  apply no_direct_right_tCount_zero
  exact transform_or_avoids (p + l) p l (by omega) C

lemma transform_gate (n a k : ℕ) (h : a + k ≤ n)
    (C : Circuit) (x : Fin n → Bool) (j : ℕ) :
    ((transform n a k C).wires (List.ofFn x)).getD (n + (k + j)) false =
      (C.wires (List.ofFn x)).getD (n + j) false := by
  have hw := transform_wires n a k h C x (n + j)
  rw [redirect_gate_wire n a k j h] at hw
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw

lemma transform_or_witness (n a k : ℕ) (h : a + k ≤ n) (C : Circuit)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = f x) :
    ∃ q : ℕ, q < (transform n a k C).gates.length ∧
      (gateAt (transform n a k C) q).op = GateOp.or ∧
      ∀ x : Fin n → Bool,
        ((transform n a k C).wires (List.ofFn x)).getD (n + q) false = f x := by
  refine ⟨k + j, ?_, ?_, ?_⟩
  · simpa [transform, copies_length] using Nat.add_lt_add_left hj k
  · rw [gateAt_transform_after n a k C j hj]
    exact hop
  · intro x
    rw [transform_gate n a k h C x j, hf x]

lemma exists_zero_mixed_min (p l : ℕ) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 (p + l) C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (p + l) D ∧ D.size = C.size + min p l ∧
      circuitFun (p + l) D = circuitFun (p + l) C ∧
      PEqualNP.TwoColour.tCount (p + l) D (fun i => decide (p ≤ i)) = 0 ∧
      (∀ j < C.gates.length, (gateAt D (min p l + j)).op = (gateAt C j).op) ∧
      (∀ (j : ℕ) (x : Fin (p + l) → Bool),
        (D.wires (List.ofFn x)).getD (p + l + (min p l + j)) false =
          (C.wires (List.ofFn x)).getD (p + l + j) false) := by
  by_cases hp : p ≤ l
  · rw [Nat.min_eq_left hp]
    refine ⟨transform (p + l) 0 p C, transform_ao2 _ _ _ (by omega) C hC,
      transform_size _ _ _ C, transform_fun _ _ _ (by omega) C,
      transform_left_tCount p l C, ?_, ?_⟩
    · intro j hj
      rw [gateAt_transform_after (p + l) 0 p C j hj]
      rfl
    · intro j x
      exact transform_gate (p + l) 0 p (by omega) C x j
  · rw [Nat.min_eq_right (by omega)]
    refine ⟨transform (p + l) p l C, transform_ao2 _ _ _ (by omega) C hC,
      transform_size _ _ _ C, transform_fun _ _ _ (by omega) C,
      transform_right_tCount p l C, ?_, ?_⟩
    · intro j hj
      rw [gateAt_transform_after (p + l) p l C j hj]
      rfl
    · intro j x
      exact transform_gate (p + l) p l (by omega) C x j

end Interval
end PEqualNP.Outside.L_meta_4970

namespace PEqualNP.Outside.L_meta_4970.CompletionReduction

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970.AppendPurePairs
open PEqualNP.Outside.L_meta_4970.Interval

/-- The posted gap, used only as an explicit hypothesis in the diagnostic below. -/
def PostedClaim : Prop := ∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) → PEqualNP.TopForm.IsAO2 (p + l) C → (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x = decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) → PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 → (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨ (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) → ∃ S : Finset (Fin (p + l)), (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧ E.card + S.card ≤ C.size + 1

/-- Conditional diagnostic, not a proof of the posted claim. -/
lemma posted_claim_implies_paired_lower_bound
    (hgap : PostedClaim) (p : ℕ) (hp : 0 < p)
    (E : Finset (Fin p × Fin p)) (P : List (Fin p × Fin p)) (C : Circuit)
    (hC4 : ∀ a a' : Fin p, ∀ b b' : Fin p, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hC : IsAO2 (p + p) C)
    (hF : ∀ x : Fin (p + p) → Bool, circuitFun (p + p) C x =
      decide (∃ a b : Fin p, (a,b) ∈ E ∧ x (Fin.castAdd p a) = true ∧
        x (Fin.natAdd p b) = true))
    (hdiag : ∀ a : Fin p, (a,a) ∈ E)
    (hneq : ∀ j, (hj : j < P.length) → P[j].1 ≠ P[j].2)
    (hserve : ∀ a b, (a,b) ∈ E → ∃ j, ∃ hj : j < P.length,
      (b = P[j].1 ∨ b = P[j].2) ∧ (a,P[j].1) ∈ E ∧ (a,P[j].2) ∈ E)
    (hcard : E.card = 2 * P.length) :
    P.length ≤ C.size + 1 := by
  classical
  let R : List (Fin (p + p) × Fin (p + p)) :=
    P.map fun z => (Fin.natAdd p z.1, Fin.natAdd p z.2)
  let D0 := appendPurePairs C R
  have hD0 : IsAO2 (p + p) D0 := appendPurePairs_AO2 C R hC
  have htrue : C.eval (List.ofFn (fun _ : Fin (p + p) => true)) = true := by
    change circuitFun (p + p) C (fun _ => true) = true
    rw [hF]
    simp only [decide_eq_true_eq]
    exact ⟨⟨0,hp⟩, ⟨0,hp⟩, hdiag ⟨0,hp⟩, trivial, trivial⟩
  have houtput := output_valid_of_true (p + p) C (fun _ => true) htrue
  obtain ⟨D, hD, hsize, hfun, hT, hops, hwires⟩ := exists_zero_mixed_min p p D0 hD0
  simp only [Nat.min_self] at hsize hops hwires
  have hF' : ∀ x : Fin (p + p) → Bool, circuitFun (p + p) D x =
      decide (∃ a b : Fin p, (a,b) ∈ E ∧ x (Fin.castAdd p a) = true ∧
        x (Fin.natAdd p b) = true) := by
    intro x
    rw [hfun]
    change D0.eval (List.ofFn x) = _
    rw [appendPurePairs_eval C R houtput x]
    exact hF x
  have hsize0 : D0.size = C.size + P.length := by
    simpa only [R, List.length_map] using appendPurePairs_size C R
  have hbound : ∃ S : Finset (Fin (p + p)),
      (∀ a b, (a,b) ∈ E → Fin.castAdd p a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
        E.card + S.card ≤ D.size + 1 := by
    apply hgap p p E D hC4 hD hF' hT
    intro a b hab
    obtain ⟨j, hj, hb, h1, h2⟩ := hserve a b hab
    have hjR : j < R.length := by simpa [R] using hj
    have hj0 : C.gates.length + j < D0.gates.length := by
      simp only [D0, appendPurePairs, List.length_append, List.length_map, R]
      omega
    have hnew := appendPurePairs_new_gate C R j hjR
    left
    refine ⟨p + (C.gates.length + j), {P[j].1,P[j].2}, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hlen : D.gates.length = D0.gates.length + p := hsize
      omega
    · rw [hops (C.gates.length + j) hj0]
      change (gateAt (appendPurePairs C R) (C.gates.length+j)).op = GateOp.or
      rw [hnew]
      rfl
    · simp [hneq j hj]
    · simpa using hb
    · intro b' hb'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
      rcases hb' with rfl | rfl
      · exact h1
      · exact h2
    · intro x
      rw [hwires (C.gates.length + j) x]
      have hv := appendPurePairs_new_wireFn C R hC j hjR x
      change (D0.wires (List.ofFn x)).getD (p + p + C.gates.length + j) false = _ at hv
      rw [← Nat.add_assoc, hv]
      simp [R]
  apply paired_completion_budget p P.length E C D hdiag hcard _ hbound
  omega

end PEqualNP.Outside.L_meta_4970.CompletionReduction

namespace PEqualNP.Outside.L_meta_4970.RawSingleton

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970_aux PEqualNP.Outside.L_meta_4970.BlendedSupport

/-- Disjoint raw supports at AND operands prevent semantic singleton leakage everywhere. -/
lemma singleton_eq_raw_of_and_disjoint (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (hdis : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ a b, (gateAt C j).inputs = [a,b] → Disjoint (orIn n C a) (orIn n C b)) :
    ∀ w, w < n + C.gates.length → singletonSupport n C w = orIn n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · rw [raw_input n C w hin, singletonSupport_input n C w hin]
    · have hn : n ≤ w := by omega
      have hj : w - n < C.gates.length := by omega
      have he : n + (w - n) = w := by omega
      obtain ⟨a,b,ha,hb,hab,hop,heval⟩ := binary_gate n C hC (w-n) hj
      rw [he] at ha hb heval
      have hsa := ih a ha (by omega)
      have hsb := ih b hb (by omega)
      rcases hop with hand | hor
      · rw [raw_and_empty n C w hn hand]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        rw [mem_singletonSupport, heval, hand] at hi
        have hi' : wireFn n C a (fun k => decide (k=i)) = true ∧
            wireFn n C b (fun k => decide (k=i)) = true := by
          simpa [GateOp.eval] using hi
        have ha' : i ∈ orIn n C a := by
          rw [← hsa, mem_singletonSupport]; exact hi'.1
        have hb' : i ∈ orIn n C b := by
          rw [← hsb, mem_singletonSupport]; exact hi'.2
        exact Finset.disjoint_left.mp (hdis (w-n) hj hand a b hab) ha' hb'
      · rw [raw_or_union n C w a b hw hn hor hab ha hb]
        ext i
        rw [mem_singletonSupport, heval, hor]
        simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq,
          Bool.or_eq_true, Finset.mem_union]
        rw [← hsa, ← hsb, mem_singletonSupport, mem_singletonSupport]

lemma and_singleton_empty_of_raw_disjoint (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (hdis : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ a b, (gateAt C j).inputs = [a,b] → Disjoint (orIn n C a) (orIn n C b))
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) :
    singletonSupport n C (n+j) = ∅ := by
  rw [singleton_eq_raw_of_and_disjoint n C hC hdis (n+j) (by omega)]
  apply raw_and_empty n C (n+j) (by omega)
  simpa using hand

/-- Conversely, equality of raw and semantic singleton supports forces disjoint AND operands. -/
lemma and_disjoint_of_singleton_eq_raw (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (heq : ∀ w, w < n + C.gates.length → singletonSupport n C w = orIn n C w)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (a b : ℕ) (hab : (gateAt C j).inputs = [a,b]) :
    Disjoint (orIn n C a) (orIn n C b) := by
  obtain ⟨a',b',ha,hb,hab',_,heval⟩ := binary_gate n C hC j hj
  have hlist : [a,b] = [a',b'] := hab.symm.trans hab'
  have haa : a = a' := (List.cons.inj hlist).1
  have hbb : b = b' := (List.cons.inj (List.cons.inj hlist).2).1
  subst a'; subst b'
  apply Finset.disjoint_left.mpr
  intro i hiA hiB
  rw [← heq a (by omega), mem_singletonSupport] at hiA
  rw [← heq b (by omega), mem_singletonSupport] at hiB
  have hi : i ∈ singletonSupport n C (n+j) := by
    rw [mem_singletonSupport, heval, hand]
    simp [GateOp.eval, hiA, hiB]
  rw [heq (n+j) (by omega), raw_and_empty n C (n+j) (by omega) (by simpa using hand)] at hi
  exact Finset.notMem_empty i hi

end PEqualNP.Outside.L_meta_4970.RawSingleton

namespace PEqualNP.Outside.L_meta_4970.RawSingleton

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970_aux PEqualNP.Outside.L_meta_4970.BlendedSupport

/-- An AND gate false on every singleton has disjoint raw operand supports. -/
lemma and_raw_disjoint_of_singleton_empty (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hempty : singletonSupport n C (n+j) = ∅)
    (a b : ℕ) (hab : (gateAt C j).inputs = [a,b]) :
    Disjoint (orIn n C a) (orIn n C b) := by
  obtain ⟨a',b',ha,hb,hab',_,heval⟩ := binary_gate n C hC j hj
  have hlist : [a,b] = [a',b'] := hab.symm.trans hab'
  have haa : a = a' := (List.cons.inj hlist).1
  have hbb : b = b' := (List.cons.inj (List.cons.inj hlist).2).1
  subst a'; subst b'
  apply Finset.disjoint_left.mpr
  intro i hiA hiB
  have hsA := raw_subset_singletonSupport n C hC a (by omega) hiA
  have hsB := raw_subset_singletonSupport n C hC b (by omega) hiB
  rw [mem_singletonSupport] at hsA hsB
  have hi : i ∈ singletonSupport n C (n+j) := by
    rw [mem_singletonSupport, heval, hand]
    simp [GateOp.eval, hsA, hsB]
  rw [hempty] at hi
  exact Finset.notMem_empty i hi

/-- Empty semantic singleton supports at every AND imply raw/semantic equality everywhere. -/
lemma singleton_eq_raw_of_and_singleton_empty (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (hempty : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      singletonSupport n C (n+j) = ∅) :
    ∀ w, w < n + C.gates.length → singletonSupport n C w = orIn n C w := by
  apply singleton_eq_raw_of_and_disjoint n C hC
  intro j hj hand a b hab
  exact and_raw_disjoint_of_singleton_empty n C hC j hj hand
    (hempty j hj hand) a b hab

lemma singleton_eq_raw_iff_and_singleton_empty (n : ℕ) (C : Circuit) (hC : IsAO2 n C) :
    (∀ w, w < n + C.gates.length → singletonSupport n C w = orIn n C w) ↔
    (∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      singletonSupport n C (n+j) = ∅) := by
  constructor
  · intro heq j hj hand
    rw [heq (n+j) (by omega)]
    apply raw_and_empty n C (n+j) (by omega)
    simpa using hand
  · exact singleton_eq_raw_of_and_singleton_empty n C hC

end PEqualNP.Outside.L_meta_4970.RawSingleton

namespace PEqualNP.Outside.L_meta_4970.RectanglePrivate

/-- A rectangle with both neighborhood controllers meets the graph only in its center's stars. -/
lemma edge_touches_center {α β : Type*} (E : Finset (α × β))
    (hC4 : ∀ a a' : α, ∀ b b' : β, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (A : Finset α) (B : Finset β) (p : α) (q : β)
    (hp : p ∈ A) (_hq : q ∈ B)
    (hA : ∀ a ∈ A, (a,q) ∈ E) (hB : ∀ b ∈ B, (p,b) ∈ E)
    (a : α) (b : β) (ha : a ∈ A) (hb : b ∈ B) (he : (a,b) ∈ E) :
    a = p ∨ b = q := by
  classical
  by_cases hap : a = p
  · exact Or.inl hap
  by_cases hbq : b = q
  · exact Or.inr hbq
  exact False.elim (hC4 a p b q hap hbq ⟨he, hA a ha, hB b hb, hA p hp⟩)

/-- Injective row and column controllers give each rectangle an edge private to that rectangle. -/
lemma center_unique {α β ι : Type*} (E : Finset (α × β))
    (hC4 : ∀ a a' : α, ∀ b b' : β, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (A : ι → Finset α) (B : ι → Finset β) (p : ι → α) (q : ι → β)
    (hp : ∀ g, p g ∈ A g) (hq : ∀ g, q g ∈ B g)
    (hA : ∀ g a, a ∈ A g → (a,q g) ∈ E)
    (hB : ∀ g b, b ∈ B g → (p g,b) ∈ E)
    (hpi : Function.Injective p) (hqi : Function.Injective q)
    (g h : ι) (hpg : p g ∈ A h) (hqg : q g ∈ B h) : g = h := by
  have hc : (p g,q g) ∈ E := hA g (p g) (hp g)
  rcases edge_touches_center E hC4 (A h) (B h) (p h) (q h) (hp h) (hq h)
    (hA h) (hB h) (p g) (q g) hpg hqg hc with he | he
  · exact hpi he
  · exact hqi he

/-- Two disjoint rectangle families cannot both cover every edge when all controllers saturate. -/
lemma no_disjoint_double_cover {α β ι : Type*} (E : Finset (α × β))
    (hC4 : ∀ a a' : α, ∀ b b' : β, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (A : ι → Finset α) (B : ι → Finset β) (p : ι → α) (q : ι → β)
    (hp : ∀ g, p g ∈ A g) (hq : ∀ g, q g ∈ B g)
    (hA : ∀ g a, a ∈ A g → (a,q g) ∈ E)
    (hB : ∀ g b, b ∈ B g → (p g,b) ∈ E)
    (hpi : Function.Injective p) (hqi : Function.Injective q)
    (R S : Finset ι) (hRS : Disjoint R S) (g : ι)
    (hcover : ∀ a b, (a,b) ∈ E →
      (∃ h ∈ R, a ∈ A h ∧ b ∈ B h) ∧ (∃ h ∈ S, a ∈ A h ∧ b ∈ B h)) :
    False := by
  obtain ⟨⟨r,hr,hpr,hqr⟩,⟨s,hs,hps,hqs⟩⟩ := hcover (p g) (q g) (hA g (p g) (hp g))
  have hgr := center_unique E hC4 A B p q hp hq hA hB hpi hqi g r hpr hqr
  have hgs := center_unique E hC4 A B p q hp hq hA hB hpi hqi g s hps hqs
  subst r; subst s
  exact Finset.disjoint_left.mp hRS hr hs

end PEqualNP.Outside.L_meta_4970.RectanglePrivate

namespace PEqualNP.Outside.L_meta_4970.RectangleControllers

def RectAccept {p l : ℕ} {ι : Type*} (A : ι → Finset (Fin p))
    (B : ι → Finset (Fin l)) (I : Finset ι) (X : Finset (Fin p))
    (Y : Finset (Fin l)) : Prop :=
  ∃ i ∈ I, ∃ a ∈ A i, ∃ b ∈ B i, a ∈ X ∧ b ∈ Y

def EdgeAccept {p l : ℕ} (E : Finset (Fin p × Fin l))
    (X : Finset (Fin p)) (Y : Finset (Fin l)) : Prop :=
  ∃ a ∈ X, ∃ b ∈ Y, (a,b) ∈ E

lemma rectAccept_singletons {p l : ℕ} {ι : Type*}
    (A : ι → Finset (Fin p)) (B : ι → Finset (Fin l)) (I : Finset ι)
    (a : Fin p) (b : Fin l) :
    RectAccept A B I {a} {b} ↔ ∃ i ∈ I, a ∈ A i ∧ b ∈ B i := by
  constructor
  · rintro ⟨i,hi,a',ha,b',hb,hax,hby⟩
    have ea : a' = a := Finset.mem_singleton.mp hax
    have eb : b' = b := Finset.mem_singleton.mp hby
    subst a'; subst b'
    exact ⟨i,hi,ha,hb⟩
  · rintro ⟨i,hi,ha,hb⟩
    exact ⟨i,hi,a,ha,b,hb,Finset.mem_singleton_self a,Finset.mem_singleton_self b⟩

lemma point_controller {p l : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Finset (Fin p × Fin l)) (A : ι → Finset (Fin p))
    (B : ι → Finset (Fin l)) (R S : Finset ι)
    (hfull : ∀ X Y, (RectAccept A B R X Y ∧ RectAccept A B S X Y) ↔
      EdgeAccept E X Y)
    (a : Fin p) (b : Fin l) (hab : (a,b) ∈ E) :
    ∃ g ∈ R ∪ S, a ∈ A g ∧ b ∈ B g ∧ ∀ a' ∈ A g, (a',b) ∈ E := by
  classical
  have hpair := (hfull {a} {b}).mpr
    (show EdgeAccept E {a} {b} from ⟨a,by simp,b,by simp,hab⟩)
  obtain ⟨i,hi,hai,hbi⟩ := (rectAccept_singletons A B R a b).mp hpair.1
  obtain ⟨j,hj,haj,hbj⟩ := (rectAccept_singletons A B S a b).mp hpair.2
  let X : Finset (Fin p) := Finset.univ.filter (fun a' => (a',b) ∉ E)
  have hfalse : ¬ (RectAccept A B R X {b} ∧ RectAccept A B S X {b}) := by
    intro hh
    obtain ⟨a',ha',b',hb',he⟩ := (hfull X {b}).mp hh
    have hb : b' = b := Finset.mem_singleton.mp hb'
    subst b'
    exact (Finset.mem_filter.mp ha').2 he
  by_cases hR : RectAccept A B R X {b}
  · refine ⟨j,Finset.mem_union_right R hj,haj,hbj,?_⟩
    intro a' ha'
    by_contra hn
    exact hfalse ⟨hR,j,hj,a',ha',b,hbj,by simp [X,hn],by simp⟩
  · refine ⟨i,Finset.mem_union_left S hi,hai,hbi,?_⟩
    intro a' ha'
    by_contra hn
    exact hR ⟨i,hi,a',ha',b,hbi,by simp [X,hn],by simp⟩

lemma line_controller {p l : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Finset (Fin p × Fin l)) (A : ι → Finset (Fin p))
    (B : ι → Finset (Fin l)) (R S : Finset ι)
    (hfull : ∀ X Y, (RectAccept A B R X Y ∧ RectAccept A B S X Y) ↔
      EdgeAccept E X Y)
    (a : Fin p) (b : Fin l) (hab : (a,b) ∈ E) :
    ∃ g ∈ R ∪ S, a ∈ A g ∧ b ∈ B g ∧ ∀ b' ∈ B g, (a,b') ∈ E := by
  classical
  have hpair := (hfull {a} {b}).mpr
    (show EdgeAccept E {a} {b} from ⟨a,by simp,b,by simp,hab⟩)
  obtain ⟨i,hi,hai,hbi⟩ := (rectAccept_singletons A B R a b).mp hpair.1
  obtain ⟨j,hj,haj,hbj⟩ := (rectAccept_singletons A B S a b).mp hpair.2
  let Y : Finset (Fin l) := Finset.univ.filter (fun b' => (a,b') ∉ E)
  have hfalse : ¬ (RectAccept A B R {a} Y ∧ RectAccept A B S {a} Y) := by
    intro hh
    obtain ⟨a',ha',b',hb',he⟩ := (hfull {a} Y).mp hh
    have ha : a' = a := Finset.mem_singleton.mp ha'
    subst a'
    exact (Finset.mem_filter.mp hb').2 he
  by_cases hR : RectAccept A B R {a} Y
  · refine ⟨j,Finset.mem_union_right R hj,haj,hbj,?_⟩
    intro b' hb'
    by_contra hn
    exact hfalse ⟨hR,j,hj,a,haj,b',hb',by simp,by simp [Y,hn]⟩
  · refine ⟨i,Finset.mem_union_left S hi,hai,hbi,?_⟩
    intro b' hb'
    by_contra hn
    exact hR ⟨i,hi,a,hai,b',hb',by simp,by simp [Y,hn]⟩

lemma point_controller_injective {p l : ℕ} {ι : Type*}
    (E M : Finset (Fin p × Fin l)) (A : ι → Finset (Fin p))
    (hleft : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hright : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (hC4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (f : {e // e ∈ M} → ι)
    (hf : ∀ e, e.val.1 ∈ A (f e) ∧ ∀ a ∈ A (f e), (a,e.val.2) ∈ E) :
    Function.Injective f := by
  intro e d hed
  apply Subtype.ext
  by_contra hne
  have ha : e.val.1 ≠ d.val.1 := fun h => hne (hleft _ e.property _ d.property h)
  have hb : e.val.2 ≠ d.val.2 := fun h => hne (hright _ e.property _ d.property h)
  have he := hf e
  have hd := hf d
  exact hC4 _ _ _ _ ha hb
    ⟨he.2 _ he.1, hd.2 _ (hed ▸ he.1), he.2 _ (hed.symm ▸ hd.1), hd.2 _ hd.1⟩

lemma line_controller_injective {p l : ℕ} {ι : Type*}
    (E M : Finset (Fin p × Fin l)) (B : ι → Finset (Fin l))
    (hleft : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hright : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (hC4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (f : {e // e ∈ M} → ι)
    (hf : ∀ e, e.val.2 ∈ B (f e) ∧ ∀ b ∈ B (f e), (e.val.1,b) ∈ E) :
    Function.Injective f := by
  intro e d hed
  apply Subtype.ext
  by_contra hne
  have ha : e.val.1 ≠ d.val.1 := fun h => hne (hleft _ e.property _ d.property h)
  have hb : e.val.2 ≠ d.val.2 := fun h => hne (hright _ e.property _ d.property h)
  have he := hf e
  have hd := hf d
  exact hC4 _ _ _ _ ha hb
    ⟨he.2 _ he.1, he.2 _ (hed.symm ▸ hd.1), hd.2 _ (hed ▸ he.1), hd.2 _ hd.1⟩

end PEqualNP.Outside.L_meta_4970.RectangleControllers

namespace PEqualNP.Outside.L_meta_4970.RectangleControllers

lemma matching_card_le_union_and_saturation {p l : ℕ} {ι : Type*} [DecidableEq ι]
    (E M : Finset (Fin p × Fin l)) (hME : M ⊆ E)
    (hleft : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hright : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (hC4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (A : ι → Finset (Fin p)) (B : ι → Finset (Fin l)) (R S : Finset ι)
    (hfull : ∀ X Y, (RectAccept A B R X Y ∧ RectAccept A B S X Y) ↔
      EdgeAccept E X Y) :
    M.card ≤ (R ∪ S).card ∧ (M.card = (R ∪ S).card → R = S) := by
  classical
  let G := R ∪ S
  have hexP : ∀ e : {e // e ∈ M}, ∃ g : {g // g ∈ G},
      e.val.1 ∈ A g.val ∧ e.val.2 ∈ B g.val ∧
        ∀ a ∈ A g.val, (a,e.val.2) ∈ E := by
    intro e
    obtain ⟨g,hg,ha,hb,hn⟩ := point_controller E A B R S hfull
      e.val.1 e.val.2 (hME e.property)
    exact ⟨⟨g,hg⟩,ha,hb,hn⟩
  have hexL : ∀ e : {e // e ∈ M}, ∃ g : {g // g ∈ G},
      e.val.1 ∈ A g.val ∧ e.val.2 ∈ B g.val ∧
        ∀ b ∈ B g.val, (e.val.1,b) ∈ E := by
    intro e
    obtain ⟨g,hg,ha,hb,hn⟩ := line_controller E A B R S hfull
      e.val.1 e.val.2 (hME e.property)
    exact ⟨⟨g,hg⟩,ha,hb,hn⟩
  let fp := fun e : {e // e ∈ M} => Classical.choose (hexP e)
  let fl := fun e : {e // e ∈ M} => Classical.choose (hexL e)
  have hfp := fun e : {e // e ∈ M} => Classical.choose_spec (hexP e)
  have hfl := fun e : {e // e ∈ M} => Classical.choose_spec (hexL e)
  have hpi : Function.Injective fp := point_controller_injective E M
    (fun g : {g // g ∈ G} => A g.val) hleft hright hC4 fp
    (fun e => ⟨(hfp e).1,(hfp e).2.2⟩)
  have hli : Function.Injective fl := line_controller_injective E M
    (fun g : {g // g ∈ G} => B g.val) hleft hright hC4 fl
    (fun e => ⟨(hfl e).2.1,(hfl e).2.2⟩)
  have hle : M.card ≤ G.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective fp hpi
  refine ⟨hle,?_⟩
  intro heq
  have hcard : Fintype.card {e // e ∈ M} = Fintype.card {g // g ∈ G} := by
    simpa only [Fintype.card_coe] using heq
  have hps : Function.Surjective fp :=
    ((Fintype.bijective_iff_injective_and_card fp).mpr ⟨hpi,hcard⟩).2
  have hls : Function.Surjective fl :=
    ((Fintype.bijective_iff_injective_and_card fl).mpr ⟨hli,hcard⟩).2
  let ep := fun g : {g // g ∈ G} => Classical.choose (hps g)
  let el := fun g : {g // g ∈ G} => Classical.choose (hls g)
  have hep : ∀ g, fp (ep g) = g := fun g => Classical.choose_spec (hps g)
  have hel : ∀ g, fl (el g) = g := fun g => Classical.choose_spec (hls g)
  let pc := fun g : {g // g ∈ G} => (el g).val.1
  let qc := fun g : {g // g ∈ G} => (ep g).val.2
  have hpc : ∀ g, pc g ∈ A g.val := by
    intro g
    have hh := (hfl (el g)).1
    change (el g).val.1 ∈ A (fl (el g)).val at hh
    simpa only [hel] using hh
  have hqc : ∀ g, qc g ∈ B g.val := by
    intro g
    have hh := (hfp (ep g)).2.1
    change (ep g).val.2 ∈ B (fp (ep g)).val at hh
    simpa only [hep] using hh
  have hA : ∀ g a, a ∈ A g.val → (a,qc g) ∈ E := by
    intro g a ha
    have hh := (hfp (ep g)).2.2
    change (∀ a ∈ A (fp (ep g)).val, (a,(ep g).val.2) ∈ E) at hh
    rw [hep] at hh
    exact hh a ha
  have hB : ∀ g b, b ∈ B g.val → (pc g,b) ∈ E := by
    intro g b hb
    have hh := (hfl (el g)).2.2
    change (∀ b ∈ B (fl (el g)).val, ((el g).val.1,b) ∈ E) at hh
    rw [hel] at hh
    exact hh b hb
  have hpci : Function.Injective pc := by
    intro g h he
    have hmatch : el g = el h := Subtype.ext
      (hleft _ (el g).property _ (el h).property he)
    calc
      g = fl (el g) := (hel g).symm
      _ = fl (el h) := congrArg fl hmatch
      _ = h := hel h
  have hqci : Function.Injective qc := by
    intro g h he
    have hmatch : ep g = ep h := Subtype.ext
      (hright _ (ep g).property _ (ep h).property he)
    calc
      g = fp (ep g) := (hep g).symm
      _ = fp (ep h) := congrArg fp hmatch
      _ = h := hep h
  have hshared : ∀ g : {g // g ∈ G}, g.val ∈ R ∧ g.val ∈ S := by
    intro g
    have hc : (pc g,qc g) ∈ E := hA g _ (hpc g)
    have hpair := (hfull {pc g} {qc g}).mpr
      (show EdgeAccept E {pc g} {qc g} from ⟨pc g,by simp,qc g,by simp,hc⟩)
    obtain ⟨r,hr,har,hbr⟩ := (rectAccept_singletons A B R _ _).mp hpair.1
    obtain ⟨s,hs,has,hbs⟩ := (rectAccept_singletons A B S _ _).mp hpair.2
    let rr : {g // g ∈ G} := ⟨r,Finset.mem_union_left S hr⟩
    let ss : {g // g ∈ G} := ⟨s,Finset.mem_union_right R hs⟩
    have hgr : g = rr := RectanglePrivate.center_unique E hC4
      (fun g : {g // g ∈ G} => A g.val) (fun g : {g // g ∈ G} => B g.val)
      pc qc hpc hqc hA hB hpci hqci g rr har hbr
    have hgs : g = ss := RectanglePrivate.center_unique E hC4
      (fun g : {g // g ∈ G} => A g.val) (fun g : {g // g ∈ G} => B g.val)
      pc qc hpc hqc hA hB hpci hqci g ss has hbs
    exact ⟨hgr.symm ▸ hr,hgs.symm ▸ hs⟩
  apply Finset.ext
  intro g
  constructor
  · intro hg
    exact (hshared ⟨g,Finset.mem_union_left S hg⟩).2
  · intro hg
    exact (hshared ⟨g,Finset.mem_union_right R hg⟩).1

lemma matching_card_lt_union_of_ne {p l : ℕ} {ι : Type*} [DecidableEq ι]
    (E M : Finset (Fin p × Fin l)) (hME : M ⊆ E)
    (hleft : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hright : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (hC4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (A : ι → Finset (Fin p)) (B : ι → Finset (Fin l)) (R S : Finset ι)
    (hfull : ∀ X Y, (RectAccept A B R X Y ∧ RectAccept A B S X Y) ↔
      EdgeAccept E X Y) (hne : R ≠ S) :
    M.card < (R ∪ S).card := by
  obtain ⟨hle,hsat⟩ := matching_card_le_union_and_saturation E M hME hleft hright
    hC4 A B R S hfull
  by_contra hn
  exact hne (hsat (Nat.le_antisymm hle (Nat.le_of_not_gt hn)))

end PEqualNP.Outside.L_meta_4970.RectangleControllers

namespace PEqualNP.Outside.L_meta_4970.RectangleControllers

/-- For disjoint nonempty factors, every matching has size at most the total rectangle count minus one. -/
lemma matching_card_add_one_le_sum {p l : ℕ} {ι : Type*} [DecidableEq ι]
    (E M : Finset (Fin p × Fin l)) (hE : E.Nonempty) (hME : M ⊆ E)
    (hleft : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hright : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (hC4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (A : ι → Finset (Fin p)) (B : ι → Finset (Fin l)) (R S : Finset ι)
    (hRS : Disjoint R S)
    (hfull : ∀ X Y, (RectAccept A B R X Y ∧ RectAccept A B S X Y) ↔
      EdgeAccept E X Y) :
    M.card + 1 ≤ R.card + S.card := by
  have hne : R ≠ S := by
    intro hrs
    obtain ⟨e,he⟩ := hE
    have hpair := (hfull {e.1} {e.2}).mpr
      (show EdgeAccept E {e.1} {e.2} from ⟨e.1,by simp,e.2,by simp,he⟩)
    obtain ⟨r,hr,_,_⟩ := (rectAccept_singletons A B R _ _).mp hpair.1
    exact Finset.disjoint_left.mp hRS hr (hrs ▸ hr)
  have hlt := matching_card_lt_union_of_ne E M hME hleft hright hC4 A B R S hfull hne
  rw [Finset.card_union_of_disjoint hRS] at hlt
  exact Nat.succ_le_of_lt hlt

end PEqualNP.Outside.L_meta_4970.RectangleControllers

namespace PEqualNP.Outside.L_meta_4970.RectangleDecoder

open PEqualNP.Outside.L_meta_4970.RectangleControllers

noncomputable def atomSet {p l : ℕ} {ι : Type*} (A : ι → Finset (Fin p))
    (B : ι → Finset (Fin l)) (G : Finset ι) (X : Finset (Fin p))
    (Y : Finset (Fin l)) : Finset ι := by
  classical
  exact G.filter (fun g => RectAccept A B {g} X Y)

lemma mem_atomSet {p l : ℕ} {ι : Type*} (A : ι → Finset (Fin p))
    (B : ι → Finset (Fin l)) (G : Finset ι) (X : Finset (Fin p))
    (Y : Finset (Fin l)) (g : ι) :
    g ∈ atomSet A B G X Y ↔ g ∈ G ∧ RectAccept A B {g} X Y := by
  classical
  simp [atomSet]

lemma mem_atomSet_singletons {p l : ℕ} {ι : Type*}
    (A : ι → Finset (Fin p)) (B : ι → Finset (Fin l)) (G : Finset ι)
    (a : Fin p) (b : Fin l) (g : ι) :
    g ∈ atomSet A B G {a} {b} ↔ g ∈ G ∧ a ∈ A g ∧ b ∈ B g := by
  simp [mem_atomSet,rectAccept_singletons]

lemma atomSet_empty {p l : ℕ} {ι : Type*}
    (A : ι → Finset (Fin p)) (B : ι → Finset (Fin l)) (G : Finset ι) :
    atomSet A B G ∅ ∅ = ∅ := by
  classical
  simp [atomSet,RectAccept]

lemma point_controller {p l : ℕ} {ι : Type*}
    (E : Finset (Fin p × Fin l)) (A : ι → Finset (Fin p))
    (B : ι → Finset (Fin l)) (G : Finset ι) (D : Finset ι → Prop)
    (hmono : ∀ U V, U ⊆ V → D U → D V)
    (hfull : ∀ X Y, D (atomSet A B G X Y) ↔ EdgeAccept E X Y)
    (a : Fin p) (b : Fin l) (hab : (a,b) ∈ E) :
    ∃ g ∈ G, a ∈ A g ∧ b ∈ B g ∧ ∀ a' ∈ A g, (a',b) ∈ E := by
  classical
  have hp : D (atomSet A B G {a} {b}) := (hfull {a} {b}).mpr
    ⟨a,by simp,b,by simp,hab⟩
  let X : Finset (Fin p) := Finset.univ.filter (fun a' => (a',b) ∉ E)
  have hn : ¬ D (atomSet A B G X {b}) := by
    intro hh
    obtain ⟨a',ha',b',hb',he⟩ := (hfull X {b}).mp hh
    have eb : b' = b := Finset.mem_singleton.mp hb'
    subst b'
    exact (Finset.mem_filter.mp ha').2 he
  have hex : ∃ g, g ∈ atomSet A B G {a} {b} ∧ g ∉ atomSet A B G X {b} := by
    by_contra hh
    apply hn
    apply hmono _ _ _ hp
    intro g hg
    by_contra hng
    exact hh ⟨g,hg,hng⟩
  obtain ⟨g,hg,hng⟩ := hex
  obtain ⟨hgG,ha,hb⟩ := (mem_atomSet_singletons A B G a b g).mp hg
  refine ⟨g,hgG,ha,hb,?_⟩
  intro a' ha'
  by_contra he
  apply hng
  apply (mem_atomSet A B G X {b} g).mpr
  exact ⟨hgG,g,by simp,a',ha',b,hb,by simp [X,he],by simp⟩

lemma line_controller {p l : ℕ} {ι : Type*}
    (E : Finset (Fin p × Fin l)) (A : ι → Finset (Fin p))
    (B : ι → Finset (Fin l)) (G : Finset ι) (D : Finset ι → Prop)
    (hmono : ∀ U V, U ⊆ V → D U → D V)
    (hfull : ∀ X Y, D (atomSet A B G X Y) ↔ EdgeAccept E X Y)
    (a : Fin p) (b : Fin l) (hab : (a,b) ∈ E) :
    ∃ g ∈ G, a ∈ A g ∧ b ∈ B g ∧ ∀ b' ∈ B g, (a,b') ∈ E := by
  classical
  have hp : D (atomSet A B G {a} {b}) := (hfull {a} {b}).mpr
    ⟨a,by simp,b,by simp,hab⟩
  let Y : Finset (Fin l) := Finset.univ.filter (fun b' => (a,b') ∉ E)
  have hn : ¬ D (atomSet A B G {a} Y) := by
    intro hh
    obtain ⟨a',ha',b',hb',he⟩ := (hfull {a} Y).mp hh
    have ea : a' = a := Finset.mem_singleton.mp ha'
    subst a'
    exact (Finset.mem_filter.mp hb').2 he
  have hex : ∃ g, g ∈ atomSet A B G {a} {b} ∧ g ∉ atomSet A B G {a} Y := by
    by_contra hh
    apply hn
    apply hmono _ _ _ hp
    intro g hg
    by_contra hng
    exact hh ⟨g,hg,hng⟩
  obtain ⟨g,hg,hng⟩ := hex
  obtain ⟨hgG,ha,hb⟩ := (mem_atomSet_singletons A B G a b g).mp hg
  refine ⟨g,hgG,ha,hb,?_⟩
  intro b' hb'
  by_contra he
  apply hng
  apply (mem_atomSet A B G {a} Y g).mpr
  exact ⟨hgG,g,by simp,a,ha,b',hb',by simp,by simp [Y,he]⟩

end PEqualNP.Outside.L_meta_4970.RectangleDecoder

namespace PEqualNP.Outside.L_meta_4970.RectangleDecoder

open PEqualNP.Outside.L_meta_4970.RectangleControllers

/-- A monotone decoder needs at least one rectangle atom per matching edge. At equality,
its truth value on every atom set contained in G is exactly nonemptiness, and every atom is safe. -/
lemma matching_card_le_atoms_and_saturation {p l : ℕ} {ι : Type*}
    (E M : Finset (Fin p × Fin l)) (hME : M ⊆ E)
    (hleft : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hright : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (hC4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (A : ι → Finset (Fin p)) (B : ι → Finset (Fin l)) (G : Finset ι)
    (D : Finset ι → Prop) (hmono : ∀ U V, U ⊆ V → D U → D V)
    (hfull : ∀ X Y, D (atomSet A B G X Y) ↔ EdgeAccept E X Y) :
    M.card ≤ G.card ∧ (M.card = G.card →
      (∀ V, V ⊆ G → (D V ↔ V.Nonempty)) ∧
      (∀ g ∈ G, ∀ a ∈ A g, ∀ b ∈ B g, (a,b) ∈ E)) := by
  classical
  have hexP : ∀ e : {e // e ∈ M}, ∃ g : {g // g ∈ G},
      e.val.1 ∈ A g.val ∧ e.val.2 ∈ B g.val ∧
        ∀ a ∈ A g.val, (a,e.val.2) ∈ E := by
    intro e
    obtain ⟨g,hg,ha,hb,hn⟩ := point_controller E A B G D hmono hfull
      e.val.1 e.val.2 (hME e.property)
    exact ⟨⟨g,hg⟩,ha,hb,hn⟩
  have hexL : ∀ e : {e // e ∈ M}, ∃ g : {g // g ∈ G},
      e.val.1 ∈ A g.val ∧ e.val.2 ∈ B g.val ∧
        ∀ b ∈ B g.val, (e.val.1,b) ∈ E := by
    intro e
    obtain ⟨g,hg,ha,hb,hn⟩ := line_controller E A B G D hmono hfull
      e.val.1 e.val.2 (hME e.property)
    exact ⟨⟨g,hg⟩,ha,hb,hn⟩
  let fp := fun e : {e // e ∈ M} => Classical.choose (hexP e)
  let fl := fun e : {e // e ∈ M} => Classical.choose (hexL e)
  have hfp := fun e : {e // e ∈ M} => Classical.choose_spec (hexP e)
  have hfl := fun e : {e // e ∈ M} => Classical.choose_spec (hexL e)
  have hpi : Function.Injective fp := point_controller_injective E M
    (fun g : {g // g ∈ G} => A g.val) hleft hright hC4 fp
    (fun e => ⟨(hfp e).1,(hfp e).2.2⟩)
  have hli : Function.Injective fl := line_controller_injective E M
    (fun g : {g // g ∈ G} => B g.val) hleft hright hC4 fl
    (fun e => ⟨(hfl e).2.1,(hfl e).2.2⟩)
  have hle : M.card ≤ G.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective fp hpi
  refine ⟨hle,?_⟩
  intro heq
  have hcard : Fintype.card {e // e ∈ M} = Fintype.card {g // g ∈ G} := by
    simpa only [Fintype.card_coe] using heq
  have hps : Function.Surjective fp :=
    ((Fintype.bijective_iff_injective_and_card fp).mpr ⟨hpi,hcard⟩).2
  have hls : Function.Surjective fl :=
    ((Fintype.bijective_iff_injective_and_card fl).mpr ⟨hli,hcard⟩).2
  let ep := fun g : {g // g ∈ G} => Classical.choose (hps g)
  let el := fun g : {g // g ∈ G} => Classical.choose (hls g)
  have hep : ∀ g, fp (ep g) = g := fun g => Classical.choose_spec (hps g)
  have hel : ∀ g, fl (el g) = g := fun g => Classical.choose_spec (hls g)
  let pc := fun g : {g // g ∈ G} => (el g).val.1
  let qc := fun g : {g // g ∈ G} => (ep g).val.2
  have hpc : ∀ g, pc g ∈ A g.val := by
    intro g
    have hh := (hfl (el g)).1
    change (el g).val.1 ∈ A (fl (el g)).val at hh
    simpa only [hel] using hh
  have hqc : ∀ g, qc g ∈ B g.val := by
    intro g
    have hh := (hfp (ep g)).2.1
    change (ep g).val.2 ∈ B (fp (ep g)).val at hh
    simpa only [hep] using hh
  have hA : ∀ g a, a ∈ A g.val → (a,qc g) ∈ E := by
    intro g a ha
    have hh := (hfp (ep g)).2.2
    change (∀ a ∈ A (fp (ep g)).val, (a,(ep g).val.2) ∈ E) at hh
    rw [hep] at hh
    exact hh a ha
  have hB : ∀ g b, b ∈ B g.val → (pc g,b) ∈ E := by
    intro g b hb
    have hh := (hfl (el g)).2.2
    change (∀ b ∈ B (fl (el g)).val, ((el g).val.1,b) ∈ E) at hh
    rw [hel] at hh
    exact hh b hb
  have hpci : Function.Injective pc := by
    intro g h he
    have hmatch : el g = el h := Subtype.ext
      (hleft _ (el g).property _ (el h).property he)
    calc
      g = fl (el g) := (hel g).symm
      _ = fl (el h) := congrArg fl hmatch
      _ = h := hel h
  have hqci : Function.Injective qc := by
    intro g h he
    have hmatch : ep g = ep h := Subtype.ext
      (hright _ (ep g).property _ (ep h).property he)
    calc
      g = fp (ep g) := (hep g).symm
      _ = fp (ep h) := congrArg fp hmatch
      _ = h := hep h
  have hsingle : ∀ g ∈ G, D {g} := by
    intro i hi
    let g : {g // g ∈ G} := ⟨i,hi⟩
    have hc : (pc g,qc g) ∈ E := hA g _ (hpc g)
    have hatom : atomSet A B G {pc g} {qc g} = {i} := by
      apply Finset.ext
      intro j
      constructor
      · intro hj
        obtain ⟨hjG,haj,hbj⟩ := (mem_atomSet_singletons A B G _ _ j).mp hj
        let jj : {g // g ∈ G} := ⟨j,hjG⟩
        have he : g = jj := RectanglePrivate.center_unique E hC4
          (fun g : {g // g ∈ G} => A g.val) (fun g : {g // g ∈ G} => B g.val)
          pc qc hpc hqc hA hB hpci hqci g jj haj hbj
        exact Finset.mem_singleton.mpr (congrArg Subtype.val he).symm
      · intro hj
        have hji : j = i := Finset.mem_singleton.mp hj
        subst j
        exact (mem_atomSet_singletons A B G _ _ i).mpr ⟨hi,hpc g,hqc g⟩
    have hd := (hfull {pc g} {qc g}).mpr
      (show EdgeAccept E {pc g} {qc g} from ⟨pc g,by simp,qc g,by simp,hc⟩)
    rwa [hatom] at hd
  have hzero : ¬ D ∅ := by
    intro hd
    have he := (hfull ∅ ∅).mp (show D (atomSet A B G ∅ ∅) by
      simpa only [atomSet_empty] using hd)
    simp [EdgeAccept] at he
  refine ⟨?_,?_⟩
  · intro V hVG
    constructor
    · intro hd
      by_contra hn
      have hempty : V = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
        (fun i hi => hn ⟨i,hi⟩)
      exact hzero (hempty ▸ hd)
    · rintro ⟨i,hi⟩
      exact hmono {i} V (Finset.singleton_subset_iff.mpr hi) (hsingle i (hVG hi))
  · intro g hg a ha b hb
    have hmem : g ∈ atomSet A B G {a} {b} :=
      (mem_atomSet_singletons A B G a b g).mpr ⟨hg,ha,hb⟩
    have hd := hmono {g} (atomSet A B G {a} {b})
      (Finset.singleton_subset_iff.mpr hmem) (hsingle g hg)
    simpa [EdgeAccept] using (hfull {a} {b}).mp hd

end PEqualNP.Outside.L_meta_4970.RectangleDecoder

namespace PEqualNP.Outside.L_meta_4970.RectangleHull

open PEqualNP.Outside.L_meta_4970.RectangleControllers
open PEqualNP.Outside.L_meta_4970.RectangleDecoder

noncomputable def actualSet {p l : ℕ} {ι : Type*}
    (f : ι → Finset (Fin p) → Finset (Fin l) → Prop) (G : Finset ι)
    (X : Finset (Fin p)) (Y : Finset (Fin l)) : Finset ι := by
  classical
  exact G.filter (fun g => f g X Y)

lemma mem_actualSet {p l : ℕ} {ι : Type*}
    (f : ι → Finset (Fin p) → Finset (Fin l) → Prop) (G : Finset ι)
    (X : Finset (Fin p)) (Y : Finset (Fin l)) (g : ι) :
    g ∈ actualSet f G X Y ↔ g ∈ G ∧ f g X Y := by
  classical
  simp [actualSet]

/-- Replacing monotone atoms by their exact rectangular pair shadows preserves a quadratic output. -/
lemma monotone_hull_reduction {p l : ℕ} {ι : Type*}
    (E : Finset (Fin p × Fin l)) (A : ι → Finset (Fin p))
    (B : ι → Finset (Fin l)) (G : Finset ι)
    (f : ι → Finset (Fin p) → Finset (Fin l) → Prop)
    (hfmono : ∀ g ∈ G, ∀ X Y X' Y', X ⊆ X' → Y ⊆ Y' → f g X Y → f g X' Y')
    (hpair : ∀ g ∈ G, ∀ a b, f g {a} {b} ↔ a ∈ A g ∧ b ∈ B g)
    (D : Finset ι → Prop) (hmono : ∀ U V, U ⊆ V → D U → D V)
    (hfull : ∀ X Y, D (actualSet f G X Y) ↔ EdgeAccept E X Y) :
    ∀ X Y, D (atomSet A B G X Y) ↔ EdgeAccept E X Y := by
  classical
  have hle : ∀ X Y, atomSet A B G X Y ⊆ actualSet f G X Y := by
    intro X Y g hg
    obtain ⟨hgG,i,hi,a,ha,b,hb,hax,hby⟩ := (mem_atomSet A B G X Y g).mp hg
    have hig : i = g := Finset.mem_singleton.mp hi
    subst i
    have hp : f g {a} {b} := (hpair g hgG a b).mpr ⟨ha,hb⟩
    exact (mem_actualSet f G X Y g).mpr ⟨hgG,
      hfmono g hgG {a} {b} X Y (Finset.singleton_subset_iff.mpr hax)
        (Finset.singleton_subset_iff.mpr hby) hp⟩
  have hpeq : ∀ a b, actualSet f G {a} {b} = atomSet A B G {a} {b} := by
    intro a b
    apply Finset.ext
    intro g
    rw [mem_actualSet,mem_atomSet_singletons]
    constructor
    · rintro ⟨hg,hf⟩
      exact ⟨hg,(hpair g hg a b).mp hf⟩
    · rintro ⟨hg,ha,hb⟩
      exact ⟨hg,(hpair g hg a b).mpr ⟨ha,hb⟩⟩
  intro X Y
  constructor
  · intro hd
    exact (hfull X Y).mp (hmono _ _ (hle X Y) hd)
  · rintro ⟨a,ha,b,hb,hab⟩
    have hd : D (actualSet f G {a} {b}) := (hfull {a} {b}).mpr
      ⟨a,by simp,b,by simp,hab⟩
    rw [hpeq] at hd
    apply hmono _ _ _ hd
    intro g hg
    obtain ⟨hgG,hag,hbg⟩ := (mem_atomSet_singletons A B G a b g).mp hg
    exact (mem_atomSet A B G X Y g).mpr ⟨hgG,g,by simp,a,hag,b,hbg,ha,hb⟩

/-- The matching bound and decoder rigidity extend to arbitrary monotone atoms with rectangular
pair shadows. At saturation every full atom, not just its pair shadow, is below the graph function. -/
lemma matching_card_le_atoms_and_full_saturation {p l : ℕ} {ι : Type*}
    (E M : Finset (Fin p × Fin l)) (hME : M ⊆ E)
    (hleft : ∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d)
    (hright : ∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d)
    (hC4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (A : ι → Finset (Fin p)) (B : ι → Finset (Fin l)) (G : Finset ι)
    (f : ι → Finset (Fin p) → Finset (Fin l) → Prop)
    (hfmono : ∀ g ∈ G, ∀ X Y X' Y', X ⊆ X' → Y ⊆ Y' → f g X Y → f g X' Y')
    (hpair : ∀ g ∈ G, ∀ a b, f g {a} {b} ↔ a ∈ A g ∧ b ∈ B g)
    (D : Finset ι → Prop) (hmono : ∀ U V, U ⊆ V → D U → D V)
    (hfull : ∀ X Y, D (actualSet f G X Y) ↔ EdgeAccept E X Y) :
    M.card ≤ G.card ∧ (M.card = G.card →
      (∀ V, V ⊆ G → (D V ↔ V.Nonempty)) ∧
      (∀ g ∈ G, ∀ X Y, f g X Y → EdgeAccept E X Y)) := by
  classical
  have hhull := monotone_hull_reduction E A B G f hfmono hpair D hmono hfull
  obtain ⟨hle,hsat⟩ := matching_card_le_atoms_and_saturation E M hME hleft hright
    hC4 A B G D hmono hhull
  refine ⟨hle,?_⟩
  intro heq
  obtain ⟨hdecode,_⟩ := hsat heq
  refine ⟨hdecode,?_⟩
  intro g hg X Y hf
  have hsub : actualSet f G X Y ⊆ G := by
    intro i hi
    exact ((mem_actualSet f G X Y i).mp hi).1
  have hnonempty : (actualSet f G X Y).Nonempty :=
    ⟨g,(mem_actualSet f G X Y g).mpr ⟨hg,hf⟩⟩
  exact (hfull X Y).mp ((hdecode _ hsub).mpr hnonempty)

end PEqualNP.Outside.L_meta_4970.RectangleHull
