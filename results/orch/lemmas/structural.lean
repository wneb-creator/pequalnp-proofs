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


lemma wireValue_constant (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (b : Bool) (w : ℕ) (hw : w < n + C.size) :
    wireValue n C w (fun _ => b) = b := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · exact wireValue_input n C w hn _
    · have hp := wireModel_parents n C hC w (by omega) hw
      rw [wireModel_eval n C hC w (by omega) hw,
        ih _ hp.1 (by omega), ih _ hp.2 (by omega)]
      cases wireAnd n C w <;> cases b <;> rfl

def pointDependent (n : ℕ) (C : Circuit) (P : Finset (Fin n)) (w : ℕ) : Prop :=
  ∃ x y : Fin n → Bool, (∀ i ∉ P, x i = y i) ∧
    wireValue n C w x ≠ wireValue n C w y

lemma pointDependent_direct_reader (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (P : Finset (Fin n)) (a : Fin n) (ha : a ∈ P)
    (j : ℕ) (hj : j < C.size)
    (hr : opnd C j 0 = a.val ∨ opnd C j 1 = a.val) :
    pointDependent n C P (n + j) := by
  classical
  have hj' : j < C.gates.length := hj
  rcases gateAt_ops n C hC j hj' with hand | hor
  · refine ⟨(fun _ => true), (fun i => if i = a then false else true), ?_, ?_⟩
    · intro i hi
      have hia : i ≠ a := by rintro rfl; exact hi ha
      simp [hia]
    · have hz := wireValue_constant n C hC true (n + j) (by omega)
      rw [hz, wireValue_gate_and n C hC j hj' hand]
      rcases hr with hr | hr
      · rw [hr, wireValue_input n C a.val a.isLt]
        simp
      · rw [hr, wireValue_input n C a.val a.isLt]
        simp
  · refine ⟨(fun _ => false), (fun i => if i = a then true else false), ?_, ?_⟩
    · intro i hi
      have hia : i ≠ a := by rintro rfl; exact hi ha
      simp [hia]
    · have hz := wireValue_constant n C hC false (n + j) (by omega)
      rw [hz, wireValue_gate_or n C hC j hj' hor]
      rcases hr with hr | hr
      · rw [hr, wireValue_input n C a.val a.isLt]
        simp
      · rw [hr, wireValue_input n C a.val a.isLt]
        simp

lemma gate_values_eq_of_cut (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (P : Finset (Fin n)) (j₀ : ℕ)
    (x y : Fin n → Bool)
    (hxy : ∀ i ∉ P, x i = y i)
    (hcut : wireValue n C (n + j₀) x = wireValue n C (n + j₀) y)
    (hread : ∀ j < C.size, j ≠ j₀ → ∀ a ∈ P,
      opnd C j 0 ≠ a.val ∧ opnd C j 1 ≠ a.val) :
    ∀ j < C.size, wireValue n C (n + j) x = wireValue n C (n + j) y := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hsame : j = j₀
    · simpa [hsame] using hcut
    · have hp := wireValue_parents n C hC j hj
      have hpar : ∀ k, (k = opnd C j 0 ∨ k = opnd C j 1) →
          wireValue n C k x = wireValue n C k y := by
        intro k hk
        have hlt : k < n + j := by rcases hk with rfl | rfl <;> omega
        by_cases hkn : k < n
        · rw [wireValue_input n C k hkn x, wireValue_input n C k hkn y]
          apply hxy
          intro hmem
          have hn := hread j hj hsame ⟨k, hkn⟩ hmem
          rcases hk with rfl | rfl
          · exact hn.1 rfl
          · exact hn.2 rfl
        · have hsmall : k - n < j := by omega
          have heq : n + (k - n) = k := by omega
          simpa only [heq] using ih (k - n) hsmall (by omega)
      rw [wireValue_gate n C hC j hj x, wireValue_gate n C hC j hj y,
        hpar _ (Or.inl rfl), hpar _ (Or.inr rfl)]


lemma single_reader_or_merge (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (a b : Fin n) (j₀ : ℕ) (hj₀ : j₀ < C.size)
    (hop : (gateAt C j₀).op = GateOp.or)
    (hl : opnd C j₀ 0 = a.val) (hr : opnd C j₀ 1 = b.val)
    (hread : ∀ j < C.size, j ≠ j₀ →
      (opnd C j 0 ≠ a.val ∧ opnd C j 1 ≠ a.val) ∧
      (opnd C j 0 ≠ b.val ∧ opnd C j 1 ≠ b.val))
    (x y : Fin n → Bool)
    (hxy : ∀ i, i ≠ a → i ≠ b → x i = y i)
    (hsum : (x a || x b) = (y a || y b)) :
    ∀ j < C.size, wireValue n C (n + j) x = wireValue n C (n + j) y := by
  classical
  apply gate_values_eq_of_cut n C hC {a, b} j₀ x y
  · intro i hi
    apply hxy i
    · intro h; apply hi; simp [h]
    · intro h; apply hi; simp [h]
  · rw [wireValue_gate_or n C hC j₀ hj₀ hop x,
      wireValue_gate_or n C hC j₀ hj₀ hop y, hl, hr,
      wireValue_input n C a.val a.isLt x,
      wireValue_input n C b.val b.isLt x,
      wireValue_input n C a.val a.isLt y,
      wireValue_input n C b.val b.isLt y]
    exact hsum
  · intro j hj hne i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact (hread j hj hne).1
    · exact (hread j hj hne).2

lemma wireValue_before_read_eq (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (P : Finset (Fin n)) (k : ℕ) (hk : k ≤ C.size)
    (x y : Fin n → Bool) (hxy : ∀ i ∉ P, x i = y i)
    (hread : ∀ j < k, ∀ a ∈ P,
      opnd C j 0 ≠ a.val ∧ opnd C j 1 ≠ a.val) :
    ∀ w < n + k, (∀ hw : w < n, (⟨w, hw⟩ : Fin n) ∉ P) →
      wireValue n C w x = wireValue n C w y := by
  have hlen : C.gates.length = C.size := rfl
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hinput
    by_cases hwn : w < n
    · rw [wireValue_input n C w hwn x, wireValue_input n C w hwn y]
      exact hxy _ (hinput hwn)
    · have heq : n + (w - n) = w := by omega
      have hj : w - n < k := by omega
      have hp := wireValue_parents n C hC (w - n) (by omega)
      have hpar : ∀ v, (v = opnd C (w - n) 0 ∨ v = opnd C (w - n) 1) →
          wireValue n C v x = wireValue n C v y := by
        intro v hv
        have hvw : v < w := by rcases hv with rfl | rfl <;> omega
        apply ih v hvw (by omega)
        intro hvn hmem
        have hh := hread (w - n) hj ⟨v, hvn⟩ hmem
        rcases hv with rfl | rfl
        · exact hh.1 rfl
        · exact hh.2 rfl
      conv_lhs => rw [← heq, wireValue_gate n C hC (w - n) (by omega) x]
      conv_rhs => rw [← heq, wireValue_gate n C hC (w - n) (by omega) y]
      rw [hpar _ (Or.inl rfl), hpar _ (Or.inr rfl)]


def pointInput (n : ℕ) (P : Finset (Fin n)) (a : Option (Fin n))
    (y : Fin n → Bool) (i : Fin n) : Bool :=
  if i ∈ P then decide (some i = a) else y i

lemma single_reader_or_coeff_equal (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (P : Finset (Fin n)) (a b : Fin n) (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b)
    (j₀ : ℕ) (hj₀ : j₀ < C.size)
    (hop : (gateAt C j₀).op = GateOp.or)
    (hl : opnd C j₀ 0 = a.val) (hr : opnd C j₀ 1 = b.val)
    (hread : ∀ j < C.size, j ≠ j₀ →
      (opnd C j 0 ≠ a.val ∧ opnd C j 1 ≠ a.val) ∧
      (opnd C j 0 ≠ b.val ∧ opnd C j 1 ≠ b.val))
    (y : Fin n → Bool) :
    ∀ j < C.size,
      wireValue n C (n + j) (pointInput n P (some a) y) =
      wireValue n C (n + j) (pointInput n P (some b) y) := by
  apply single_reader_or_merge n C hC a b j₀ hj₀ hop hl hr hread
  · intro i hia hib
    simp only [pointInput]
    split
    · simp [hia, hib]
    · rfl
  · simp [pointInput, ha, hb, hab, Ne.symm hab]

lemma early_or_absorbed (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (P : Finset (Fin n)) (a : Fin n) (ha : a ∈ P)
    (j₀ : ℕ) (hj₀ : j₀ < C.size)
    (hop : (gateAt C j₀).op = GateOp.or) (v : ℕ)
    (hports : (opnd C j₀ 0 = a.val ∧ opnd C j₀ 1 = v) ∨
      (opnd C j₀ 0 = v ∧ opnd C j₀ 1 = a.val))
    (hvp : ∀ hv : v < n, (⟨v, hv⟩ : Fin n) ∉ P)
    (hfirst : ∀ j < j₀, ∀ b ∈ P,
      opnd C j 0 ≠ b.val ∧ opnd C j 1 ≠ b.val)
    (hread : ∀ j < C.size, j ≠ j₀ →
      opnd C j 0 ≠ a.val ∧ opnd C j 1 ≠ a.val) :
    ∀ j < C.size,
      wireValue n C (n + j) (pointInput n P none (fun _ => true)) =
      wireValue n C (n + j) (pointInput n P (some a) (fun _ => true)) := by
  classical
  have hparents := wireValue_parents n C hC j₀ hj₀
  have hv : v < n + j₀ := by
    rcases hports with ⟨_, rfl⟩ | ⟨rfl, _⟩ <;> omega
  have hparam : ∀ z : Option (Fin n),
      wireValue n C v (pointInput n P z (fun _ => true)) = true := by
    intro z
    have h := wireValue_before_read_eq n C hC P j₀ (by omega)
      (pointInput n P z (fun _ => true)) (fun _ => true)
      (by intro i hi; simp [pointInput, hi]) hfirst v hv hvp
    rw [wireValue_constant n C hC true v (by omega)] at h
    exact h
  apply gate_values_eq_of_cut n C hC {a} j₀
  · intro i hi
    have hia : i ≠ a := by simpa using hi
    simp only [pointInput]
    split
    · simp [hia]
    · rfl
  · rw [wireValue_gate_or n C hC j₀ hj₀ hop,
      wireValue_gate_or n C hC j₀ hj₀ hop]
    rcases hports with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · rw [hr, hparam none, hparam (some a)]
      simp
    · rw [hl, hparam none, hparam (some a)]
      simp
  · intro j hj hne b hb
    have hba : b = a := by simpa using hb
    subst b
    exact hread j hj hne


lemma earliest_reader_zero (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (P : Finset (Fin n)) (o : ℕ) (ho : o < C.size)
    (hbase : wireValue n C (n + o) (pointInput n P none (fun _ => true)) = false)
    (hone : ∀ a ∈ P,
      wireValue n C (n + o) (pointInput n P (some a) (fun _ => true)) = true)
    (hdist : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → ∃ y : Fin n → Bool,
      wireValue n C (n + o) (pointInput n P (some a) y) ≠
      wireValue n C (n + o) (pointInput n P (some b) y))
    (hsingle : ∀ a ∈ P, ∀ j < C.size, ∀ k < C.size,
      (opnd C j 0 = a.val ∨ opnd C j 1 = a.val) →
      (opnd C k 0 = a.val ∨ opnd C k 1 = a.val) → j = k)
    (k : ℕ) (hk : k < C.size) (a : Fin n) (ha : a ∈ P)
    (hka : opnd C k 0 = a.val ∨ opnd C k 1 = a.val)
    (hfirst : ∀ j < k, ∀ b ∈ P,
      opnd C j 0 ≠ b.val ∧ opnd C j 1 ≠ b.val) :
    (gateAt C k).op = GateOp.and ∨
      (opnd C k 0 = a.val ∧ opnd C k 1 = a.val) := by
  classical
  rcases gateAt_ops n C hC k hk with hand | hor
  · exact Or.inl hand
  · right
    have hread : ∀ b ∈ P,
        (opnd C k 0 = b.val ∨ opnd C k 1 = b.val) →
        ∀ j < C.size, j ≠ k → opnd C j 0 ≠ b.val ∧ opnd C j 1 ≠ b.val := by
      intro b hb hkb j hj hne
      constructor
      · intro h; exact hne (hsingle b hb j hj k hk (Or.inl h) hkb)
      · intro h; exact hne (hsingle b hb j hj k hk (Or.inr h) hkb)
    obtain ⟨v, hv⟩ : ∃ v,
        (opnd C k 0 = a.val ∧ opnd C k 1 = v) ∨
        (opnd C k 0 = v ∧ opnd C k 1 = a.val) := by
      rcases hka with hka | hka
      · exact ⟨opnd C k 1, Or.inl ⟨hka, rfl⟩⟩
      · exact ⟨opnd C k 0, Or.inr ⟨rfl, hka⟩⟩
    have habsorb : (∀ h : v < n, (⟨v, h⟩ : Fin n) ∉ P) → False := by
      intro hnot
      have h := early_or_absorbed n C hC P a ha k hk hor v hv hnot hfirst
        (hread a ha hka) o ho
      rw [hbase, hone a ha] at h
      contradiction
    have hvn : v < n := by
      by_contra hn
      exact habsorb (by intro h; omega)
    let b : Fin n := ⟨v, hvn⟩
    have hb : b ∈ P := by
      by_contra hnb
      exact habsorb (by intro h; exact hnb)
    have hab : a = b := by
      by_contra hne
      obtain ⟨y, hy⟩ := hdist a ha b hb hne
      have hkb : opnd C k 0 = b.val ∨ opnd C k 1 = b.val := by
        rcases hv with ⟨_, h⟩ | ⟨h, _⟩
        · exact Or.inr h
        · exact Or.inl h
      rcases hv with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · have heq := single_reader_or_coeff_equal n C hC P a b ha hb hne k hk hor hl hr
          (by intro j hj hjk; exact ⟨hread a ha hka j hj hjk, hread b hb hkb j hj hjk⟩) y o ho
        exact hy heq
      · have heq := single_reader_or_coeff_equal n C hC P b a hb ha (Ne.symm hne) k hk hor hl hr
          (by intro j hj hjk; exact ⟨hread b hb hkb j hj hjk, hread a ha hka j hj hjk⟩) y o ho
        exact hy heq.symm
    have hvval : v = a.val := by rw [hab]
    rcases hv with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact ⟨hl, hr.trans hvval⟩
    · exact ⟨hl.trans hvval, hr⟩

end PEqualNP.Outside.L_meta_4970_aux.Structural
