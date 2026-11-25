import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PEqualNP.Outside.L_meta_4970_aux.Structural

def IsIncreasing {α : Type*} (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

lemma below_or_of_complement {α : Type*} [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool)
    (hf : IsIncreasing f)
    (hzero : f (fun i => decide (i ∉ Q)) ≠ true) :
    ∀ x, f x = true → ∃ i ∈ Q, x i = true := by
  intro x hx
  by_contra hn
  apply hzero
  apply hf x (fun i => decide (i ∉ Q)) _ hx
  intro i hi
  simp only [decide_eq_true_eq]
  intro hiQ
  exact hn ⟨i, hiQ, hi⟩

lemma and_below_or_child {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : IsIncreasing f) (hg : IsIncreasing g)
    (hbound : ∀ x, (f x && g x) = true → ∃ i ∈ Q, x i = true) :
    (∀ x, f x = true → ∃ i ∈ Q, x i = true) ∨
      (∀ x, g x = true → ∃ i ∈ Q, x i = true) := by
  let z : α → Bool := fun i => decide (i ∉ Q)
  have hz : ¬ (f z = true ∧ g z = true) := by
    intro h
    obtain ⟨i, hiQ, hiz⟩ := hbound z (by simp [h.1, h.2])
    simp [z, hiQ] at hiz
  by_cases h : f z = true
  · exact Or.inr (below_or_of_complement Q g hg (fun h' => hz ⟨h, h'⟩))
  · exact Or.inl (below_or_of_complement Q f hf h)

lemma and_eq_or_child {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : IsIncreasing f) (hg : IsIncreasing g)
    (heq : ∀ x, (f x && g x) = decide (∃ i ∈ Q, x i = true)) :
    (∀ x, f x = decide (∃ i ∈ Q, x i = true)) ∨
      (∀ x, g x = decide (∃ i ∈ Q, x i = true)) := by
  have hb : ∀ x, (f x && g x) = true → ∃ i ∈ Q, x i = true := by
    intro x hx
    rw [heq x] at hx
    exact of_decide_eq_true hx
  rcases and_below_or_child Q f g hf hg hb with h | h
  · left
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · exact h x
    · intro hx
      have hx' : (f x && g x) = true := by
        rw [heq x]
        exact decide_eq_true hx
      rw [Bool.and_eq_true] at hx'
      exact hx'.1
  · right
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · exact h x
    · intro hx
      have hx' : (f x && g x) = true := by
        rw [heq x]
        exact decide_eq_true hx
      rw [Bool.and_eq_true] at hx'
      exact hx'.2

lemma countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

lemma pure_or_rt_count {α : Type*} [DecidableEq α] [Fintype α]
    (k N : ℕ) (Q : Finset α)
    (W : ℕ → (α → Bool) → Bool) (S : ℕ → Finset α)
    (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (hmono : ∀ w < N, IsIncreasing (W w))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hsupport : ∀ w < N, ∀ i,
      i ∈ S w ↔ W w (fun j => decide (j = i)) = true)
    (heval : ∀ w, k ≤ w → w < N → ∀ x,
      W w x = if isAnd w then (W (a w) x && W (b w) x)
        else (W (a w) x || W (b w) x))
    (R : Finset ℕ)
    (hR : ∀ w ∈ R, w < N ∧ (∀ x, W w x = true → ∃ i ∈ Q, x i = true)) :
    (R.biUnion S).card ≤ R.card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ isAnd w = false ∧
        1 < (S w).card ∧ ∀ x, W w x = true → ∃ i ∈ Q, x i = true)).card := by
  classical
  let below (w : ℕ) := ∀ x, W w x = true → ∃ i ∈ Q, x i = true
  let F (w : ℕ) := if w < N ∧ below w then S w else ∅
  let paid := (Finset.range N).filter fun w =>
    k ≤ w ∧ isAnd w = false ∧ 1 < (S w).card ∧ below w
  have hstep : ∀ w < N, 1 < (F w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ F w ⊆ cs.biUnion F ∧
        cs.card ≤ 1 + (if w ∈ paid then 1 else 0) := by
    intro w hw hlarge
    have hgood : w < N ∧ below w := by
      by_contra hn
      simp [F, hn] at hlarge
    have hF : F w = S w := ite_eq_left hgood
    have hk : k ≤ w := by
      by_contra hn
      have ht := hsmall w (by omega)
      rw [hF] at hlarge
      omega
    have ⟨ha, hb⟩ := hparents w hk hw
    cases hop : isAnd w with
    | true =>
      have hbound : ∀ x, (W (a w) x && W (b w) x) = true → ∃ i ∈ Q, x i = true := by
        intro x hx
        apply hgood.2 x
        simpa [heval w hk hw x, hop] using hx
      have hchoice := and_below_or_child Q (W (a w)) (W (b w))
        (hmono _ (ha.trans hw)) (hmono _ (hb.trans hw)) hbound
      have hsubA : S w ⊆ S (a w) := by
        intro i hi
        apply (hsupport _ (ha.trans hw) i).mpr
        have ht := (hsupport w hw i).mp hi
        rw [heval w hk hw, hop] at ht
        simp only [ite_true, Bool.and_eq_true] at ht
        exact ht.1
      have hsubB : S w ⊆ S (b w) := by
        intro i hi
        apply (hsupport _ (hb.trans hw) i).mpr
        have ht := (hsupport w hw i).mp hi
        rw [heval w hk hw, hop] at ht
        simp only [ite_true, Bool.and_eq_true] at ht
        exact ht.2
      rcases hchoice with hA | hB
      · have hFA : F (a w) = S (a w) := ite_eq_left ⟨ha.trans hw, hA⟩
        refine ⟨{a w}, by simpa using ha, ?_, by simp⟩
        simpa [hF, hFA] using hsubA
      · have hFB : F (b w) = S (b w) := ite_eq_left ⟨hb.trans hw, hB⟩
        refine ⟨{b w}, by simpa using hb, ?_, by simp⟩
        simpa [hF, hFB] using hsubB
    | false =>
      have hA : below (a w) := by
        intro x hx
        apply hgood.2 x
        simp [heval w hk hw x, hop, hx]
      have hB : below (b w) := by
        intro x hx
        apply hgood.2 x
        simp [heval w hk hw x, hop, hx]
      have hFA : F (a w) = S (a w) := ite_eq_left ⟨ha.trans hw, hA⟩
      have hFB : F (b w) = S (b w) := ite_eq_left ⟨hb.trans hw, hB⟩
      have hsub : S w ⊆ S (a w) ∪ S (b w) := by
        intro i hi
        have ht := (hsupport w hw i).mp hi
        rw [heval w hk hw, hop] at ht
        simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true] at ht
        rcases ht with ht | ht
        · exact Finset.mem_union_left _ ((hsupport _ (ha.trans hw) i).mpr ht)
        · exact Finset.mem_union_right _ ((hsupport _ (hb.trans hw) i).mpr ht)
      have hp : w ∈ paid := by
        simp only [paid, Finset.mem_filter, Finset.mem_range]
        exact ⟨hw, hk, hop, hF ▸ hlarge, hgood.2⟩
      refine ⟨{a w, b w}, ?_, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hv]
          exact Finset.mem_range.mpr hb
      · simpa [hF, hFA, hFB] using hsub
      · simp only [hp, ite_true]
        exact Finset.card_le_two
  have hRrange : R ⊆ Finset.range N := by
    intro w hw
    exact Finset.mem_range.mpr (hR w hw).1
  have hroots : R.biUnion F = R.biUnion S := by
    apply Finset.biUnion_congr rfl
    intro w hw
    exact ite_eq_left (hR w hw)
  have hpaid : Finset.range N ∩ paid = paid := by
    exact Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
  have hc := countUnion F paid N hstep R hRrange
  simpa only [hroots, hpaid] using hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

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

def wireValue (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireValue_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n)
    (x : Fin n → Bool) : wireValue n C w x = x ⟨w, hw⟩ := by
  change (wiresFrom C.gates (List.ofFn x)).getD w false = _
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_ofFn]

lemma wireValue_increasing (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (w : ℕ) :
    IsIncreasing (wireValue n C w) := by
  intro x y hxy htrue
  change (wiresFrom C.gates (List.ofFn y)).getD w false = true
  apply wiresFrom_mono C.gates hC.1 (List.ofFn x) (List.ofFn y) (by simp) _ w htrue
  intro i hi
  by_cases hin : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hin), List.getElem_ofFn] at hi ⊢
    exact hxy _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    contradiction

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma gateAt_inputs_two (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen := hC.2.2 (gateAt C j) (gateAt_mem C j hj)
  obtain ⟨a, b, heq⟩ := List.length_eq_two.mp hlen
  simp [opnd, heq]

lemma gateAt_ops (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
  hC.1 _ (gateAt_mem C j hj)

lemma wireValue_parents (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hread := hC.2.1 j hj
  have hi := gateAt_inputs_two n C hC j hj
  constructor
  · exact hread _ (by rw [hi]; simp)
  · exact hread _ (by rw [hi]; simp)

lemma wireValue_gate (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    wireValue n C (n + j) x = (gateAt C j).op.eval
      [wireValue n C (opnd C j 0) x, wireValue n C (opnd C j 1) x] := by
  have h := getD_wiresFrom_gate C.gates (List.ofFn x) j hj
  have hgate : C.gates[j] = gateAt C j := by
    unfold gateAt
    exact (List.getD_eq_getElem _ _ hj).symm
  have hs := gateAt_inputs_two n C hC j hj
  have hp := wireValue_parents n C hC j hj
  simpa only [List.length_ofFn, hgate, hs, List.map_cons, List.map_nil,
    ite_eq_left hp.1, ite_eq_left hp.2, wireValue, Circuit.wires, wiresFrom] using h

lemma wireValue_gate_and (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireValue n C (n + j) x =
      (wireValue n C (opnd C j 0) x && wireValue n C (opnd C j 1) x) := by
  rw [wireValue_gate n C hC j hj, hop]
  simp [GateOp.eval]

lemma wireValue_gate_or (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireValue n C (n + j) x =
      (wireValue n C (opnd C j 0) x || wireValue n C (opnd C j 1) x) := by
  rw [wireValue_gate n C hC j hj, hop]
  simp [GateOp.eval]

def wireSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => wireValue n C w (fun j => decide (j = i)) = true

lemma wireSupport_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ wireSupport n C w ↔ wireValue n C w (fun j => decide (j = i)) = true := by
  simp [wireSupport]

lemma wireSupport_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    wireSupport n C w = {⟨w, hw⟩} := by
  ext i
  simp [wireSupport_mem, wireValue_input n C w hw, eq_comm]

def wireAnd (n : ℕ) (C : Circuit) (w : ℕ) : Bool :=
  match (gateAt C (w - n)).op with
  | GateOp.and => true
  | _ => false

def wireLeft (n : ℕ) (C : Circuit) (w : ℕ) : ℕ := opnd C (w - n) 0

def wireRight (n : ℕ) (C : Circuit) (w : ℕ) : ℕ := opnd C (w - n) 1

lemma wireModel_parents (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    wireLeft n C w < w ∧ wireRight n C w < w := by
  have hj : w - n < C.gates.length := by change w - n < C.size; omega
  have hp := wireValue_parents n C hC (w - n) hj
  simpa only [wireLeft, wireRight, Nat.add_sub_of_le hn] using hp

lemma wireModel_eval (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) (x : Fin n → Bool) :
    wireValue n C w x = if wireAnd n C w then
      (wireValue n C (wireLeft n C w) x && wireValue n C (wireRight n C w) x)
      else (wireValue n C (wireLeft n C w) x || wireValue n C (wireRight n C w) x) := by
  have hj : w - n < C.gates.length := by change w - n < C.size; omega
  rcases gateAt_ops n C hC (w - n) hj with hop | hop
  · have he := wireValue_gate_and n C hC (w - n) hj hop x
    simpa only [wireAnd, hop, ite_true, wireLeft, wireRight, Nat.add_sub_of_le hn] using he
  · have he := wireValue_gate_or n C hC (w - n) hj hop x
    simpa only [wireAnd, hop, Bool.false_eq_true, ite_false, wireLeft, wireRight,
      Nat.add_sub_of_le hn] using he

def pureOrPaid (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + C.size)).filter fun w =>
    n ≤ w ∧ wireAnd n C w = false ∧ 1 < (wireSupport n C w).card ∧
      ∀ x, wireValue n C w x = true → ∃ i ∈ Q, x i = true

lemma circuit_pure_or_count (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (R : Finset ℕ)
    (hR : ∀ w ∈ R, w < n + C.size ∧
      ∀ x, wireValue n C w x = true → ∃ i ∈ Q, x i = true) :
    (R.biUnion (wireSupport n C)).card ≤ R.card + (pureOrPaid n C Q).card := by
  have hs : ∀ w < n, (wireSupport n C w).card ≤ 1 := by
    intro w hw
    simp [wireSupport_input n C w hw]
  have hc := pure_or_rt_count n (n + C.size) Q (wireValue n C) (wireSupport n C)
    (wireLeft n C) (wireRight n C) (wireAnd n C)
    (fun w _ => wireValue_increasing n C hC w) hs
    (fun w hn hw => wireModel_parents n C hC w hn hw)
    (fun w _ i => wireSupport_mem n C w i)
    (fun w hn hw x => wireModel_eval n C hC w hn hw x) R hR
  convert hc using 2
  congr 1
  ext w
  simp only [pureOrPaid, Finset.mem_filter, Finset.mem_range]

lemma wireSupport_below (n : ℕ) (C : Circuit) (w : ℕ) (Q : Finset (Fin n))
    (hbelow : ∀ x, wireValue n C w x = true → ∃ i ∈ Q, x i = true) :
    wireSupport n C w ⊆ Q := by
  intro i hi
  obtain ⟨j, hj, hji⟩ := hbelow (fun k => decide (k = i)) ((wireSupport_mem n C w i).mp hi)
  have heq : j = i := of_decide_eq_true hji
  exact heq ▸ hj

lemma wireValue_of_support (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (w : ℕ) (i : Fin n) (hi : i ∈ wireSupport n C w)
    (x : Fin n → Bool) (hxi : x i = true) : wireValue n C w x = true := by
  apply wireValue_increasing n C hC w (fun j => decide (j = i)) x
  · intro j hj
    have heq : j = i := of_decide_eq_true hj
    exact heq ▸ hxi
  · exact (wireSupport_mem n C w i).mp hi

lemma pureOrPaid_true (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (x : Fin n → Bool) (hx : ∀ i ∈ Q, x i = true)
    (w : ℕ) (hw : w ∈ pureOrPaid n C Q) : wireValue n C w x = true := by
  have hp := (Finset.mem_filter.mp hw).2
  have hne : (wireSupport n C w).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hne
  apply wireValue_of_support n C hC w i hi x
  exact hx i (wireSupport_below n C w Q hp.2.2.2 hi)

lemma pureOrPaid_disjoint_false (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) (x : Fin n → Bool) (hx : ∀ i ∈ Q, x i = true)
    (A : Finset ℕ) (hA : ∀ w ∈ A, wireValue n C w x = false) :
    Disjoint (pureOrPaid n C Q) A := by
  apply Finset.disjoint_left.mpr
  intro w hw hwA
  have ht := pureOrPaid_true n C hC Q x hx w hw
  rw [hA w hwA] at ht
  contradiction

lemma pureOrPaid_sub_gates (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) :
    pureOrPaid n C Q ⊆ Finset.Ico n (n + C.size) := by
  intro w hw
  have hp := Finset.mem_filter.mp hw
  exact Finset.mem_Ico.mpr ⟨hp.2.1, Finset.mem_range.mp hp.1⟩

lemma pureOrPaid_card_le_size (n : ℕ) (C : Circuit) (Q : Finset (Fin n)) :
    (pureOrPaid n C Q).card ≤ C.size := by
  have h := Finset.card_le_card (pureOrPaid_sub_gates n C Q)
  simpa using h

def edgeGraph {α : Type*} (E : Finset (α × α)) : SimpleGraph α :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ E

lemma edgeGraph_mono {α : Type*} {E F : Finset (α × α)} (h : E ⊆ F) :
    edgeGraph E ≤ edgeGraph F := by
  intro a b hab
  exact ⟨hab.1, hab.2.imp (fun h' => h h') (fun h' => h h')⟩

lemma edgeGraph_link {α : Type*} [DecidableEq α] (E : Finset (α × α))
    (a b : α) : (edgeGraph (insert (a,b) E)).Reachable a b := by
  by_cases h : a = b
  · subst b
    exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    exact ⟨h, Or.inl (Finset.mem_insert_self _ _)⟩

lemma edgeGraph_union_connected {α : Type*} [DecidableEq α]
    (E : Finset (α × α)) (A B : Finset α)
    (hA : ∀ x ∈ A, ∀ y ∈ A, (edgeGraph E).Reachable x y)
    (hB : ∀ x ∈ B, ∀ y ∈ B, (edgeGraph E).Reachable x y)
    (a : α) (ha : a ∈ A) (b : α) (hb : b ∈ B) :
    ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B,
      (edgeGraph (insert (a,b) E)).Reachable x y := by
  have hmono := edgeGraph_mono (Finset.subset_insert (a,b) E)
  have hleg : ∀ x ∈ A ∪ B, (edgeGraph (insert (a,b) E)).Reachable x a := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (hA x hx a ha).mono hmono
    · exact ((hB x hx b hb).mono hmono).trans (edgeGraph_link E a b).symm
  intro x hx y hy
  exact (hleg x hx).trans (hleg y hy).symm

lemma support_connected_edges {α : Type*} [DecidableEq α]
    (U : Finset α) (S : ℕ → Finset α) (paid : Finset ℕ) (N : ℕ)
    (hU : ∀ w < N, S w ⊆ U)
    (step : ∀ w < N, 1 < (S w).card →
      (∃ a < w, S w ⊆ S a) ∨
        (w ∈ paid ∧ ∃ a < w, ∃ b < w, S w ⊆ S a ∪ S b)) :
    ∃ E : Finset (α × α), E ⊆ U ×ˢ U ∧ E.card ≤ (Finset.range N ∩ paid).card ∧
      ∀ w < N, ∀ x ∈ S w, ∀ y ∈ S w, (edgeGraph E).Reachable x y := by
  classical
  induction N with
  | zero =>
    refine ⟨∅, by simp, by simp, ?_⟩
    intro w hw
    omega
  | succ N ih =>
    obtain ⟨E, hEU, hcard, hconn⟩ := ih (fun w hw => hU w (by omega))
      (fun w hw => step w (by omega))
    have hcard' : E.card ≤ (Finset.range (N + 1) ∩ paid).card := by
      apply hcard.trans
      apply Finset.card_le_card
      intro w hw
      have hm := Finset.mem_inter.mp hw
      exact Finset.mem_inter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hm.1; omega), hm.2⟩
    have extend (F : Finset (α × α)) (hEF : E ⊆ F)
        (hnew : ∀ x ∈ S N, ∀ y ∈ S N, (edgeGraph F).Reachable x y) :
        ∀ w < N + 1, ∀ x ∈ S w, ∀ y ∈ S w, (edgeGraph F).Reachable x y := by
      intro w hw x hx y hy
      by_cases h : w < N
      · exact (hconn w h x hx y hy).mono (edgeGraph_mono hEF)
      · have he : w = N := by omega
        subst w
        exact hnew x hx y hy
    by_cases hlarge : 1 < (S N).card
    · rcases step N (by omega) hlarge with ⟨a, ha, hsub⟩ | ⟨hp, a, ha, b, hb, hsub⟩
      · refine ⟨E, hEU, hcard', extend E (fun _ h => h) ?_⟩
        exact fun x hx y hy => hconn a ha x (hsub hx) y (hsub hy)
      · by_cases hA : (S a).Nonempty
        · by_cases hB : (S b).Nonempty
          · obtain ⟨u, hu⟩ := hA
            obtain ⟨v, hv⟩ := hB
            have hpaid : (Finset.range (N + 1) ∩ paid).card =
                (Finset.range N ∩ paid).card + 1 := by
              have heq : Finset.range (N + 1) ∩ paid = insert N (Finset.range N ∩ paid) := by
                ext j
                by_cases hj : j = N <;> simp [Finset.range_add_one, hj, hp]
              rw [heq]
              simp
            refine ⟨insert (u,v) E, ?_, ?_, extend _ (Finset.subset_insert _ _) ?_⟩
            · intro z hz
              rcases Finset.mem_insert.mp hz with rfl | hz
              · exact Finset.mem_product.mpr ⟨hU a (by omega) hu, hU b (by omega) hv⟩
              · exact hEU hz
            · have hi := Finset.card_insert_le (u,v) E
              omega
            · intro x hx y hy
              exact edgeGraph_union_connected E (S a) (S b) (hconn a ha) (hconn b hb)
                u hu v hv x (hsub hx) y (hsub hy)
          · have hB' : S b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
            have hs : S N ⊆ S a := by simpa [hB'] using hsub
            exact ⟨E, hEU, hcard', extend E (fun _ h => h)
              (fun x hx y hy => hconn a ha x (hs hx) y (hs hy))⟩
        · have hA' : S a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
          have hs : S N ⊆ S b := by simpa [hA'] using hsub
          exact ⟨E, hEU, hcard', extend E (fun _ h => h)
            (fun x hx y hy => hconn b hb x (hs hx) y (hs hy))⟩
    · have hsmall : (S N).card ≤ 1 := by omega
      refine ⟨E, hEU, hcard', extend E (fun _ h => h) ?_⟩
      intro x hx y hy
      have heq : x = y := Finset.card_le_one.mp hsmall x hx y hy
      subst y
      exact SimpleGraph.Reachable.refl _

lemma circuit_pure_or_graph (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (Q : Finset (Fin n)) :
    ∃ E : Finset (Fin n × Fin n), E ⊆ Q ×ˢ Q ∧ E.card ≤ (pureOrPaid n C Q).card ∧
      ∀ w < n + C.size, (∀ x, wireValue n C w x = true → ∃ i ∈ Q, x i = true) →
        ∀ u ∈ wireSupport n C w, ∀ v ∈ wireSupport n C w, (edgeGraph E).Reachable u v := by
  classical
  let below (w : ℕ) := ∀ x, wireValue n C w x = true → ∃ i ∈ Q, x i = true
  let F (w : ℕ) := if w < n + C.size ∧ below w then wireSupport n C w else ∅
  have hFsub : ∀ w < n + C.size, F w ⊆ Q := by
    intro w hw
    by_cases hg : w < n + C.size ∧ below w
    · simpa only [F, ite_eq_left hg] using wireSupport_below n C w Q hg.2
    · simp [F, hg]
  have step : ∀ w < n + C.size, 1 < (F w).card →
      (∃ a < w, F w ⊆ F a) ∨
        (w ∈ pureOrPaid n C Q ∧ ∃ a < w, ∃ b < w, F w ⊆ F a ∪ F b) := by
    intro w hw hlarge
    have hg : w < n + C.size ∧ below w := by
      by_contra hn
      simp [F, hn] at hlarge
    have hF : F w = wireSupport n C w := ite_eq_left hg
    have hn : n ≤ w := by
      by_contra! hn
      rw [hF, wireSupport_input n C w hn] at hlarge
      simp at hlarge
    have hp := wireModel_parents n C hC w hn hw
    cases hop : wireAnd n C w with
    | true =>
      have hbound : ∀ x,
          (wireValue n C (wireLeft n C w) x && wireValue n C (wireRight n C w) x) = true →
            ∃ i ∈ Q, x i = true := by
        intro x hx
        apply hg.2 x
        rw [wireModel_eval n C hC w hn hw, hop]
        exact hx
      have hchoice := and_below_or_child Q
        (wireValue n C (wireLeft n C w)) (wireValue n C (wireRight n C w))
        (wireValue_increasing n C hC _) (wireValue_increasing n C hC _) hbound
      have hsub : wireSupport n C w ⊆ wireSupport n C (wireLeft n C w) ∩
          wireSupport n C (wireRight n C w) := by
        intro i hi
        have ht := (wireSupport_mem n C w i).mp hi
        rw [wireModel_eval n C hC w hn hw, hop] at ht
        simp only [ite_true, Bool.and_eq_true] at ht
        exact Finset.mem_inter.mpr ⟨(wireSupport_mem n C _ i).mpr ht.1,
          (wireSupport_mem n C _ i).mpr ht.2⟩
      left
      rcases hchoice with hA | hB
      · refine ⟨wireLeft n C w, hp.1, ?_⟩
        have hFA : F (wireLeft n C w) = wireSupport n C (wireLeft n C w) :=
          ite_eq_left ⟨hp.1.trans hw, hA⟩
        rw [hF, hFA]
        exact hsub.trans Finset.inter_subset_left
      · refine ⟨wireRight n C w, hp.2, ?_⟩
        have hFB : F (wireRight n C w) = wireSupport n C (wireRight n C w) :=
          ite_eq_left ⟨hp.2.trans hw, hB⟩
        rw [hF, hFB]
        exact hsub.trans Finset.inter_subset_right
    | false =>
      have hA : below (wireLeft n C w) := by
        intro x hx
        apply hg.2 x
        simp [wireModel_eval n C hC w hn hw, hop, hx]
      have hB : below (wireRight n C w) := by
        intro x hx
        apply hg.2 x
        simp [wireModel_eval n C hC w hn hw, hop, hx]
      have hFA : F (wireLeft n C w) = wireSupport n C (wireLeft n C w) :=
        ite_eq_left ⟨hp.1.trans hw, hA⟩
      have hFB : F (wireRight n C w) = wireSupport n C (wireRight n C w) :=
        ite_eq_left ⟨hp.2.trans hw, hB⟩
      right
      refine ⟨?_, wireLeft n C w, hp.1, wireRight n C w, hp.2, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw, hn, hop, hF ▸ hlarge, hg.2⟩
      · rw [hF, hFA, hFB]
        intro i hi
        have ht := (wireSupport_mem n C w i).mp hi
        rw [wireModel_eval n C hC w hn hw, hop] at ht
        simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true] at ht
        rcases ht with ht | ht
        · exact Finset.mem_union_left _ ((wireSupport_mem n C _ i).mpr ht)
        · exact Finset.mem_union_right _ ((wireSupport_mem n C _ i).mpr ht)
  obtain ⟨E, hEQ, hcard, hconn⟩ := support_connected_edges Q F (pureOrPaid n C Q)
    (n + C.size) hFsub step
  have hcard' : E.card ≤ (pureOrPaid n C Q).card := by
    exact hcard.trans (Finset.card_le_card Finset.inter_subset_right)
  refine ⟨E, hEQ, hcard', ?_⟩
  intro w hw hbelow u hu v hv
  have heq : F w = wireSupport n C w := ite_eq_left ⟨hw, hbelow⟩
  apply hconn w hw u _ v _
  · simpa only [heq] using hu
  · simpa only [heq] using hv

lemma wireSupport_eq_pure (n : ℕ) (C : Circuit) (w : ℕ) (Q : Finset (Fin n))
    (heq : ∀ x, wireValue n C w x = decide (∃ i ∈ Q, x i = true)) :
    wireSupport n C w = Q := by
  ext i
  rw [wireSupport_mem, heq]
  simp

end PEqualNP.Outside.L_meta_4970_aux.Structural

namespace PEqualNP.Outside.L_meta_4970_aux.Restriction

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4970_aux.Structural

def aliasVal (w : List Bool) : Option ℕ → Bool
  | none => false
  | some j => w.getD j false

def aliasValid (m : ℕ) (s : Option ℕ) : Prop := ∀ j ∈ s, j < m

def reduceAnd (m : ℕ) : Option ℕ → Option ℕ → Option Gate × Option ℕ
  | some a, some b => (some ⟨GateOp.and, [a,b]⟩, some m)
  | _, _ => (none, none)

def reduceOr (m : ℕ) : Option ℕ → Option ℕ → Option Gate × Option ℕ
  | none, b => (none, b)
  | some a, none => (none, some a)
  | some a, some b => (some ⟨GateOp.or, [a,b]⟩, some m)

def reduce (op : GateOp) (m : ℕ) (a b : Option ℕ) : Option Gate × Option ℕ :=
  match op with
  | .and => reduceAnd m a b
  | .or => reduceOr m a b
  | _ => (none, none)

def gateOK (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

lemma aliasValid_mono {m k : ℕ} (h : m ≤ k) (s : Option ℕ)
    (hs : aliasValid m s) : aliasValid k s := by
  intro j hj
  exact Nat.lt_of_lt_of_le (hs j hj) h

lemma aliasVal_append (w t : List Bool) (s : Option ℕ)
    (hs : aliasValid w.length s) : aliasVal (w ++ t) s = aliasVal w s := by
  cases s with
  | none => rfl
  | some j =>
    exact List.getD_append _ _ _ _ (hs j rfl)

lemma reduce_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (a b : Option ℕ)
    (ha : aliasValid w.length a) (hb : aliasValid w.length b) :
    aliasValid (w.length + (reduce op w.length a b).1.toList.length)
      (reduce op w.length a b).2 ∧
    aliasVal (wiresFrom (reduce op w.length a b).1.toList w)
      (reduce op w.length a b).2 = op.eval [aliasVal w a, aliasVal w b] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [reduce, reduceAnd, reduceOr, aliasValid, aliasVal, wiresFrom, GateOp.eval]

def step (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate) :
    List (Option ℕ) × List Gate :=
  let r := reduce g.op (n + acc.2.length)
    (acc.1.getD (g.inputs.getD 0 0) none) (acc.1.getD (g.inputs.getD 1 0) none)
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def run (n : ℕ) (gs : List Gate) (acc : List (Option ℕ) × List Gate) :
    List (Option ℕ) × List Gate := gs.foldl (step n) acc

lemma run_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List (Option ℕ) × List Gate) :
    run n (g :: gs) acc = run n gs (step n acc g) := rfl

lemma snoc_getD_ne {α : Type*} (l : List α) (a d : α) (i : ℕ) (h : i ≠ l.length) :
    (l ++ [a]).getD i d = l.getD i d := by
  by_cases hi : i < l.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

lemma snoc_getD_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by simp

lemma run_getD (n k : ℕ) (gs : List Gate) : ∀ acc : List (Option ℕ) × List Gate,
    k < acc.1.length → (run n gs acc).1.getD k none = acc.1.getD k none := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [run_cons, ih (step n acc g) (by simp [step]; omega)]
    exact snoc_getD_ne _ _ _ _ (by omega)

lemma run_length (n : ℕ) (gs : List Gate) : ∀ acc : List (Option ℕ) × List Gate,
    (run n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [run_cons, ih]
    simp [step]
    omega

lemma option_length_le (o : Option Gate) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma run_size (n : ℕ) (gs : List Gate) : ∀ acc : List (Option ℕ) × List Gate,
    (run n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [run]
  | cons g gs ih =>
    intro acc
    have h := ih (step n acc g)
    have hs := option_length_le (reduce g.op (n + acc.2.length)
      (acc.1.getD (g.inputs.getD 0 0) none) (acc.1.getD (g.inputs.getD 1 0) none)).1
    have hh : (step n acc g).2.length ≤ acc.2.length + 1 := by
      simp [step]
    rw [run_cons, List.length_cons]
    omega

lemma inputs_two (g : Gate) (hg : gateOK g) : ∃ a b, g.inputs = [a,b] := by
  rcases g with ⟨op,l⟩
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp_all [gateOK]

def Inv (n : ℕ) (y w : List Bool) (acc : List (Option ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    aliasValid (n + acc.2.length) (acc.1.getD i none) ∧
    aliasVal (wiresFrom acc.2 y) (acc.1.getD i none) = w.getD i false

lemma inv_run (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Option ℕ) × List Gate),
    (∀ g ∈ gs, gateOK g) → Inv n y w acc →
    Inv n y (wiresFrom gs w) (run n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (step n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    have hg := hok g List.mem_cons_self
    obtain ⟨a,b,hab⟩ := inputs_two g hg
    let w' := wiresFrom acc.2 y
    have lw' : w'.length = n + acc.2.length := by simp [w', length_wiresFrom, hy]
    let r := reduce g.op (n + acc.2.length) (acc.1.getD a none) (acc.1.getD b none)
    have hs := reduce_sound g.op hg.1 w' (acc.1.getD a none) (acc.1.getD b none)
      (by rw [lw']; exact (hi a).1) (by rw [lw']; exact (hi b).1)
    rw [lw'] at hs
    change aliasValid (n + acc.2.length + r.1.toList.length) r.2 ∧
      aliasVal (wiresFrom r.1.toList w') r.2 =
      g.op.eval [aliasVal w' (acc.1.getD a none), aliasVal w' (acc.1.getD b none)] at hs
    have hstep : step n acc g = (acc.1 ++ [r.2], acc.2 ++ r.1.toList) := by
      simp [step, hab, r]
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      exact wiresFrom_append _ _ _
    obtain ⟨t,ht,htl⟩ := wiresFrom_ext r.1.toList w'
    rw [hstep]
    refine ⟨by simp [hl], ?_⟩
    intro i
    rw [List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst i
      rw [snoc_getD_eq, hl, Structural.getD_snoc_eq]
      constructor
      · exact hs.1
      · rw [hnew, hs.2]
        simp only [hab, List.map_cons, List.map_nil]
        change g.op.eval [aliasVal (wiresFrom acc.2 y) (acc.1.getD a none),
          aliasVal (wiresFrom acc.2 y) (acc.1.getD b none)] =
          g.op.eval [w.getD a false, w.getD b false]
        rw [(hi a).2, (hi b).2]
    · rw [snoc_getD_ne _ _ _ _ hil,
        snoc_getD_ne _ _ _ _ (by omega)]
      refine ⟨aliasValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [hnew, ht, aliasVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

lemma reduce_none (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (m : ℕ) (a b : Option ℕ) (h : a = none ∨ b = none) :
    (reduce op m a b).1 = none := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [reduce, reduceAnd, reduceOr]

lemma step_none (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate)
    (hg : gateOK g) (k : ℕ) (hk : k ∈ g.inputs) (hc : acc.1.getD k none = none) :
    (step n acc g).2.length = acc.2.length := by
  obtain ⟨a,b,hab⟩ := inputs_two g hg
  have h : acc.1.getD a none = none ∨ acc.1.getD b none = none := by
    simp only [hab, List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with h | h
    · exact Or.inl (by simpa only [h] using hc)
    · exact Or.inr (by simpa only [h] using hc)
  have hn := reduce_none g.op hg.1 (n + acc.2.length)
    (acc.1.getD a none) (acc.1.getD b none) h
  simpa [step, hab] using congrArg (fun o : Option Gate => acc.2.length + o.toList.length) hn

lemma run_count (n k : ℕ) (gs : List Gate) : ∀ acc : List (Option ℕ) × List Gate,
    (∀ g ∈ gs, gateOK g) → k < acc.1.length → acc.1.getD k none = none →
    (run n gs acc).2.length + gs.countP (fun g => g.inputs.contains k)
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [run]
  | cons g gs ih =>
    intro acc hok hk hc
    have h1 := ih (step n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [step]; omega)
      (by
        change (acc.1 ++ [_]).getD k none = none
        rw [snoc_getD_ne _ _ _ _ (by omega)]
        exact hc)
    rw [run_cons, List.length_cons, List.countP_cons]
    by_cases hkg : k ∈ g.inputs
    · have h2 := step_none n acc g (hok g List.mem_cons_self) k hkg hc
      have hct : g.inputs.contains k = true := by simpa using hkg
      simp only [hct, ↓reduceIte]
      omega
    · have h2 : (step n acc g).2.length ≤ acc.2.length + 1 := by
        have := option_length_le (reduce g.op (n + acc.2.length)
          (acc.1.getD (g.inputs.getD 0 0) none) (acc.1.getD (g.inputs.getD 1 0) none)).1
        simp [step]
      have hct : g.inputs.contains k = false := by simpa using hkg
      simp only [hct, Bool.false_eq_true, ↓reduceIte]
      omega

def initial (n x : ℕ) : List (Option ℕ) :=
  List.ofFn (fun i : Fin n => if i.val = x then none else some i.val)

lemma inv_initial (n : ℕ) (x : Fin n) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Function.update y x false)) (initial n x.val, []) := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  by_cases hi : i < n
  · by_cases hix : i = x.val
    · have he : (⟨i,hi⟩ : Fin n) = x := Fin.ext hix
      simp [initial, hix, aliasValid, aliasVal]
    · have he : (⟨i,hi⟩ : Fin n) ≠ x := fun h => hix (congrArg Fin.val h)
      simp [initial, hix, aliasValid, aliasVal, wiresFrom, hi, Function.update_of_ne he]
  · rw [List.getD_eq_default _ _ (by simp [initial]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    simp [aliasValid, aliasVal]


lemma circuit_gateOK (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∀ g ∈ C.gates, gateOK g := by
  intro g hg
  exact ⟨hC.1 g hg, hC.2.2 g hg⟩

def data (n : ℕ) (C : Circuit) (x : ℕ) : List (Option ℕ) × List Gate :=
  run n C.gates (initial n x, [])

def circuit (n : ℕ) (C : Circuit) (x : ℕ) : Circuit :=
  let acc := data n C x
  ⟨acc.2, (acc.1.getD C.output none).getD (n + acc.2.length)⟩

lemma data_inv (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (C.wires (List.ofFn (Function.update y x false))) (data n C x.val) := by
  exact inv_run n (List.ofFn y) (by simp) C.gates _ _ (circuit_gateOK n C hC)
    (inv_initial n x y)

lemma data_alias (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (y : Fin n → Bool) (w : ℕ) :
    aliasVal ((circuit n C x.val).wires (List.ofFn y))
      ((data n C x.val).1.getD w none) = wireValue n C w (Function.update y x false) := by
  exact ((data_inv n C hC x y).2 w).2

lemma circuit_eval (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (y : Fin n → Bool) :
    (circuit n C x.val).eval (List.ofFn y) = C.eval (List.ofFn (Function.update y x false)) := by
  have hv := data_alias n C hC x y C.output
  change aliasVal ((circuit n C x.val).wires (List.ofFn y))
    ((data n C x.val).1.getD C.output none) =
    C.eval (List.ofFn (Function.update y x false)) at hv
  cases hs : (data n C x.val).1.getD C.output none with
  | none =>
    rw [hs] at hv
    change false = _ at hv
    rw [← hv]
    change (wiresFrom (data n C x.val).2 (List.ofFn y)).getD
      (((data n C x.val).1.getD C.output none).getD (n + (data n C x.val).2.length)) false = false
    rw [hs]
    exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp)
  | some j =>
    rw [hs] at hv
    simpa only [circuit, Circuit.eval, hs, Option.getD_some, aliasVal] using hv

lemma circuit_size_saved (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) :
    (circuit n C x.val).size + C.gates.countP (fun g => g.inputs.contains x.val) ≤ C.size := by
  have h := run_count n x.val C.gates (initial n x.val, []) (circuit_gateOK n C hC)
    (by simp [initial]) (by simp [initial, x.isLt])
  simpa [circuit, data, Circuit.size] using h


def listOK (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), gateOK gs[j] ∧ ∀ k ∈ gs[j].inputs, k < n + j

lemma listOK_append (n : ℕ) (gs : List Gate) (g : Gate) (hs : listOK n gs)
    (hg : gateOK g ∧ ∀ k ∈ g.inputs, k < n + gs.length) : listOK n (gs ++ [g]) := by
  intro j hj
  by_cases h : j < gs.length
  · simpa only [List.getElem_append_left h] using hs j h
  · have he : j = gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    simpa using hg

lemma reduce_emitted (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (m : ℕ) (a b : Option ℕ) (ha : aliasValid m a) (hb : aliasValid m b)
    (g : Gate) (hg : (reduce op m a b).1 = some g) :
    gateOK g ∧ ∀ k ∈ g.inputs, k < m := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [reduce, reduceAnd, reduceOr, gateOK, aliasValid]
  all_goals rcases hg with rfl; simp_all

def Safe (n : ℕ) (acc : List (Option ℕ) × List Gate) : Prop :=
  listOK n acc.2 ∧ ∀ i, aliasValid (n + acc.2.length) (acc.1.getD i none)

lemma step_safe (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate)
    (hg : gateOK g) (h : Safe n acc) : Safe n (step n acc g) := by
  obtain ⟨a,b,hab⟩ := inputs_two g hg
  let r := reduce g.op (n + acc.2.length) (acc.1.getD a none) (acc.1.getD b none)
  have hstep : step n acc g = (acc.1 ++ [r.2], acc.2 ++ r.1.toList) := by simp [step,hab,r]
  have hv : aliasValid (n + acc.2.length + r.1.toList.length) r.2 := by
    have hh := (reduce_sound g.op hg.1 (List.replicate (n + acc.2.length) false)
      (acc.1.getD a none) (acc.1.getD b none) (by simpa using h.2 a) (by simpa using h.2 b)).1
    simpa [r] using hh
  rw [hstep]
  constructor
  · cases hr : r.1 with
    | none => simpa only [hr, Option.toList_none, List.append_nil] using h.1
    | some q =>
      have hq := reduce_emitted g.op hg.1 (n + acc.2.length)
        (acc.1.getD a none) (acc.1.getD b none) (h.2 a) (h.2 b) q hr
      simpa only [hr, Option.toList_some] using listOK_append n acc.2 q h.1 hq
  · intro i
    change aliasValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i none)
    rw [List.length_append, ← Nat.add_assoc]
    by_cases hi : i = acc.1.length
    · subst i
      rw [snoc_getD_eq]
      exact hv
    · rw [snoc_getD_ne _ _ _ _ hi]
      exact aliasValid_mono (by omega) _ (h.2 i)

lemma run_safe (n : ℕ) (gs : List Gate) : ∀ acc : List (Option ℕ) × List Gate,
    (∀ g ∈ gs, gateOK g) → Safe n acc → Safe n (run n gs acc) := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hok h
    exact ih (step n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (step_safe n acc g (hok g List.mem_cons_self) h)

lemma circuit_isAO2 (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) : PEqualNP.TopForm.IsAO2 n (circuit n C x.val) := by
  have hi : Safe n (initial n x.val, []) := by
    constructor
    · intro j hj; simp at hj
    · intro i
      exact ((inv_initial n x (fun _ => false)).2 i).1
  have hs := (run_safe n C.gates (initial n x.val, []) (circuit_gateOK n C hC) hi).1
  change listOK n (data n C x.val).2 at hs
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    exact (hs j hj).1.1
  · intro j hj i hi
    have hv := (hs j hj).2
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, circuit] at hi
    have hh : j < (data n C x.val).2.length := hj
    rw [List.getD_eq_getElem _ _ hh] at hi
    exact hv i hi
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    exact (hs j hj).1.2


lemma run_append (n : ℕ) (pre post : List Gate) (acc : List (Option ℕ) × List Gate) :
    run n (pre ++ post) acc = run n post (run n pre acc) := by
  simp [run, List.foldl_append]

lemma step_and_none (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate)
    (hg : gateOK g) (hand : g.op = GateOp.and) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k none = none) :
    (step n acc g).1.getD acc.1.length none = none := by
  obtain ⟨a,b,hab⟩ := inputs_two g hg
  have h : acc.1.getD a none = none ∨ acc.1.getD b none = none := by
    simp only [hab, List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with h | h
    · exact Or.inl (by simpa only [h] using hc)
    · exact Or.inr (by simpa only [h] using hc)
  change (acc.1 ++ [_]).getD acc.1.length none = none
  rw [snoc_getD_eq]
  simp only [hab, List.getD_cons_zero, List.getD_cons_succ, hand, reduce]
  cases ha : acc.1.getD a none <;> cases hb : acc.1.getD b none <;> simp_all [reduceAnd]

lemma step_zero (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate)
    (hg : gateOK g) (k : ℕ) (hk : k ∈ g.inputs) (hc : acc.1.getD k none = none)
    (hzero : g.op = GateOp.and ∨ g.inputs = [k,k]) :
    (step n acc g).1.getD acc.1.length none = none := by
  rcases hzero with hand | hdup
  · exact step_and_none n acc g hg hand k hk hc
  · change (acc.1 ++ [_]).getD acc.1.length none = none
    rw [snoc_getD_eq]
    rcases hg.1 with hand | hor
    · simp only [hdup,List.getD_cons_zero,List.getD_cons_succ,hand,reduce,hc,reduceAnd]
    · simp only [hdup,List.getD_cons_zero,List.getD_cons_succ,hor,reduce,hc,reduceOr]

lemma run_two_zero (n : ℕ) (x : Fin n) (pre post : List Gate) (g : Gate)
    (hok : ∀ h ∈ pre ++ g :: post, gateOK h)
    (hzero : g.op = GateOp.and ∨ g.inputs = [x.val,x.val]) (hx : x.val ∈ g.inputs)
    (hreader : ∃ h ∈ post, n + pre.length ∈ h.inputs) :
    (run n (pre ++ g :: post) (initial n x.val, [])).2.length + 2 ≤
      (pre ++ g :: post).length := by
  let a := run n pre (initial n x.val, [])
  let b := step n a g
  have haLen : a.1.length = n + pre.length := by simp [a, run_length, initial]
  have haSize : a.2.length ≤ pre.length := by
    simpa [a] using run_size n pre (initial n x.val, [])
  have haZero : a.1.getD x.val none = none := by
    rw [show a = run n pre (initial n x.val, []) from rfl,
      run_getD n x.val pre _ (by simp [initial])]
    simp [initial, x.isLt]
  have hg : gateOK g := hok g (by simp)
  have hbSize : b.2.length = a.2.length := step_none n a g hg x.val hx haZero
  have hbZero : b.1.getD (n + pre.length) none = none := by
    rw [← haLen]
    exact step_zero n a g hg x.val hx haZero hzero
  have hbLen : n + pre.length < b.1.length := by simp [b,step,haLen]
  have hp := run_count n (n + pre.length) post b
    (fun h hh => hok h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))) hbLen hbZero
  have hr : 1 ≤ post.countP (fun h => h.inputs.contains (n + pre.length)) := by
    obtain ⟨h,hh,hr⟩ := hreader
    exact List.countP_pos_iff.mpr ⟨h,hh,by simpa using hr⟩
  rw [run_append,run_cons]
  change (run n post b).2.length + 2 ≤ _
  simp only [List.length_append,List.length_cons]
  omega

lemma circuit_size_two_and (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (pre post : List Gate) (g : Gate) (hgs : C.gates = pre ++ g :: post)
    (hand : g.op = GateOp.and) (hx : x.val ∈ g.inputs)
    (hreader : ∃ h ∈ post, n + pre.length ∈ h.inputs) :
    (circuit n C x.val).size + 2 ≤ C.size := by
  have hh := run_two_zero n x pre post g
    (by rw [← hgs]; exact circuit_gateOK n C hC) (Or.inl hand) hx hreader
  simpa [circuit,data,Circuit.size,hgs] using hh


lemma circuit_size_two_zero (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (pre post : List Gate) (g : Gate) (hgs : C.gates = pre ++ g :: post)
    (hzero : g.op = GateOp.and ∨ g.inputs = [x.val,x.val]) (hx : x.val ∈ g.inputs)
    (hreader : ∃ h ∈ post, n + pre.length ∈ h.inputs) :
    (circuit n C x.val).size + 2 ≤ C.size := by
  have hh := run_two_zero n x pre post g
    (by rw [← hgs]; exact circuit_gateOK n C hC) hzero hx hreader
  simpa [circuit,data,Circuit.size,hgs] using hh

lemma circuit_wire_alias (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (w : ℕ)
    (hnz : ∃ y : Fin n → Bool, wireValue n C w (Function.update y x false) = true) :
    ∃ j < n + (circuit n C x.val).size, ∀ y : Fin n → Bool,
      wireValue n (circuit n C x.val) j y = wireValue n C w (Function.update y x false) := by
  obtain ⟨z,hz⟩ := hnz
  cases hs : (data n C x.val).1.getD w none with
  | none =>
    have hv := data_alias n C hC x z w
    rw [hs] at hv
    change false = _ at hv
    rw [hz] at hv
    cases hv
  | some j =>
    refine ⟨j,?_,?_⟩
    · have hv := ((data_inv n C hC x z).2 w).1
      exact hv j hs
    · intro y
      have hv := data_alias n C hC x y w
      rw [hs] at hv
      exact hv


lemma countP_two {α : Type*} (l : List α) (p : α → Bool)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hne : i ≠ j)
    (hpi : p l[i] = true) (hpj : p l[j] = true) : 2 ≤ l.countP p := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a l ih =>
    simp only [List.length_cons] at hi hj
    cases i with
    | zero =>
      cases j with
      | zero => exact (hne rfl).elim
      | succ j =>
        change p a = true at hpi
        change p l[j] = true at hpj
        have hh : 0 < l.countP p := List.countP_pos_iff.mpr ⟨l[j],List.getElem_mem _,hpj⟩
        simp only [List.countP_cons,hpi,↓reduceIte]
        omega
    | succ i =>
      cases j with
      | zero =>
        change p a = true at hpj
        change p l[i] = true at hpi
        have hh : 0 < l.countP p := List.countP_pos_iff.mpr ⟨l[i],List.getElem_mem _,hpi⟩
        simp only [List.countP_cons,hpj,↓reduceIte]
        omega
      | succ j =>
        have hh := ih i j (by omega) (by omega) (by omega) hpi hpj
        simp only [List.countP_cons]
        split_ifs <;> omega

lemma circuit_size_two_readers (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (i j : ℕ) (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hne : i ≠ j)
    (hri : x.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs)
    (hrj : x.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) :
    (circuit n C x.val).size + 2 ≤ C.size := by
  have hpi : (C.gates[i]).inputs.contains x.val = true := by
    rw [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD_eq_getElem _ _ hi] at hri
    simpa using hri
  have hpj : (C.gates[j]).inputs.contains x.val = true := by
    rw [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD_eq_getElem _ _ hj] at hrj
    simpa using hrj
  have hh := countP_two C.gates (fun g => g.inputs.contains x.val) i j hi hj hne hpi hpj
  have hs := circuit_size_saved n C hC x
  omega

lemma circuit_size_two_zero_at (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n) (j : ℕ) (hj : j < C.gates.length)
    (hzero : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [x.val,x.val])
    (hx : x.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs)
    (hreader : ∃ k < C.gates.length, j < k ∧
      n + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) :
    (circuit n C x.val).size + 2 ≤ C.size := by
  have he : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    exact List.getD_eq_getElem _ _ hj
  rw [he] at hzero hx
  have hgs : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by
    have hh := (List.take_append_drop j C.gates).symm
    rw [List.drop_eq_getElem_cons hj] at hh
    exact hh
  apply circuit_size_two_zero n C hC x (C.gates.take j) (C.gates.drop (j+1)) C.gates[j]
    hgs hzero hx
  obtain ⟨k,hk,hjk,hr⟩ := hreader
  have hkt : k-(j+1) < (C.gates.drop (j+1)).length := by simp; omega
  refine ⟨(C.gates.drop (j+1))[k-(j+1)],List.getElem_mem hkt,?_⟩
  rw [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD_eq_getElem _ _ hk] at hr
  have helem : (C.gates.drop (j+1))[k-(j+1)] = C.gates[k] := by
    rw [List.getElem_drop]
    congr 1
    omega
  rw [helem,List.length_take,min_eq_left (Nat.le_of_lt hj)]
  exact hr

end PEqualNP.Outside.L_meta_4970_aux.Restriction
