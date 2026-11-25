import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux

namespace SafeLineSets

variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]

lemma unique_center (E : Finset (α × β))
    (hE : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : α} {Q : Finset β} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : a = a' := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  by_contra hn
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.mp (show 1 < Q.card by omega)
  exact hE a a' b c hn hbc ⟨ha b hb, ha c hc, ha' b hb, ha' c hc⟩

lemma cover_of_line_sets (E : Finset (α × β)) (A : Finset ι) (Q : ι → Finset β)
    (hE : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hserve : ∀ a b, (a, b) ∈ E →
      ∃ i ∈ A, b ∈ Q i ∧ ∀ c ∈ Q i, (a, c) ∈ E) :
    ∃ S : Finset (α ⊕ β), S.card ≤ A.card ∧
      ∀ a b, (a, b) ∈ E → Sum.inl a ∈ S ∨ Sum.inr b ∈ S := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  classical
  let U := A.filter fun i => (Q i).Nonempty ∧ ∃ a, ∀ b ∈ Q i, (a, b) ∈ E
  have hu : ∀ i : U, (Q i.val).Nonempty ∧ ∃ a, ∀ b ∈ Q i.val, (a, b) ∈ E := by
    intro i
    exact (Finset.mem_filter.mp i.property).2
  let center : U → α ⊕ β := fun i =>
    if 2 ≤ (Q i.val).card then Sum.inl (hu i).2.choose
    else Sum.inr (hu i).1.choose
  let S := U.attach.image center
  refine ⟨S, ?_, ?_⟩
  · calc
      S.card ≤ U.attach.card := Finset.card_image_le
      _ = U.card := Finset.card_attach
      _ ≤ A.card := Finset.card_le_card (Finset.filter_subset _ _)
  · intro a b hab
    obtain ⟨i, hi, hbi, hrow⟩ := hserve a b hab
    have hiU : i ∈ U := Finset.mem_filter.mpr ⟨hi, ⟨⟨b, hbi⟩, ⟨a, hrow⟩⟩⟩
    let ii : U := ⟨i, hiU⟩
    have hmem : center ii ∈ S := Finset.mem_image.mpr ⟨ii, Finset.mem_attach _ _, rfl⟩
    by_cases hlarge : 2 ≤ (Q i).card
    · have hcenter : (hu ii).2.choose = a := unique_center E hE hlarge
        (hu ii).2.choose_spec hrow
      left
      simpa [center, ii, hlarge, hcenter] using hmem
    · have hc : (hu ii).1.choose ∈ Q i := (hu ii).1.choose_spec
      have heq : (hu ii).1.choose = b := (Finset.card_le_one.mp (show (Q i).card ≤ 1 by omega)) _ hc _ hbi
      right
      simpa [center, ii, hlarge, heq] using hmem

lemma and_child_cover_budget (E : Finset (α × β)) (A : Finset ι)
    (L R : ι → Finset β)
    (hE : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hserve : ∀ a b, (a, b) ∈ E → ∃ i ∈ A,
      (b ∈ L i ∧ ∀ c ∈ L i, (a, c) ∈ E) ∨
      (b ∈ R i ∧ ∀ c ∈ R i, (a, c) ∈ E)) :
    ∃ S : Finset (α ⊕ β),
      S.card ≤ A.card + (A.filter fun i => (L i).Nonempty ∧ (R i).Nonempty).card ∧
      ∀ a b, (a, b) ∈ E → Sum.inl a ∈ S ∨ Sum.inr b ∈ S := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  classical
  let AL := A.filter fun i => (L i).Nonempty
  let AR := A.filter fun i => (R i).Nonempty
  have hserve' : ∀ a b, (a, b) ∈ E →
      ∃ i ∈ AL.disjSum AR, b ∈ Sum.elim L R i ∧
        ∀ c ∈ Sum.elim L R i, (a, c) ∈ E := by
    intro a b hab
    obtain ⟨i, hi, hh⟩ := hserve a b hab
    rcases hh with hh | hh
    · exact ⟨Sum.inl i, by simp [AL, hi, Finset.nonempty_iff_ne_empty, Finset.ne_empty_of_mem hh.1], hh⟩
    · exact ⟨Sum.inr i, by simp [AR, hi, Finset.nonempty_iff_ne_empty, Finset.ne_empty_of_mem hh.1], hh⟩
  obtain ⟨S, hcard, hcover⟩ := cover_of_line_sets E (AL.disjSum AR) (Sum.elim L R) hE hserve'
  refine ⟨S, ?_, hcover⟩
  have hunion : (AL ∪ AR).card ≤ A.card := Finset.card_le_card (by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (Finset.mem_filter.mp hi).1
    · exact (Finset.mem_filter.mp hi).1)
  have hinter : AL ∩ AR = A.filter fun i => (L i).Nonempty ∧ (R i).Nonempty := by
    ext i
    simp [AL, AR, and_assoc, and_left_comm, and_comm]
  have hsum := Finset.card_union_add_card_inter AL AR
  rw [hinter] at hsum
  rw [Finset.card_disjSum] at hcard
  omega

lemma safe_trace (n W : ℕ) (isAnd : ℕ → Bool) (left right : ℕ → ℕ)
    (neg pos : ℕ → Bool) (Q : ℕ → Finset β) (N : Finset β) (b : β)
    (hinputs : ∀ w < n, neg w = false → pos w = true → b ∈ Q w)
    (hchildren : ∀ w, n ≤ w → w < W → left w < w ∧ right w < w)
    (hsem : ∀ w, n ≤ w → w < W →
      if isAnd w then
        neg w = (neg (left w) && neg (right w)) ∧ pos w = (pos (left w) && pos (right w))
      else neg w = (neg (left w) || neg (right w)) ∧ pos w = (pos (left w) || pos (right w)))
    (hreach : ∀ w, n ≤ w → w < W → isAnd w = false → Q w = Q (left w) ∪ Q (right w))
    (hsafe : ∀ w < W, neg w = false → Q w ⊆ N) :
    ∀ w < W, neg w = false → pos w = true →
      b ∈ Q w ∨ ∃ g, n ≤ g ∧ g < W ∧ isAnd g = true ∧ pos g = true ∧
        ((b ∈ Q (left g) ∧ Q (left g) ⊆ N ∧ neg (left g) = false) ∨
         (b ∈ Q (right g) ∧ Q (right g) ⊆ N ∧ neg (right g) = false)) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hn hp
    by_cases hin : w < n
    · exact Or.inl (hinputs w hin hn hp)
    have hge : n ≤ w := by omega
    obtain ⟨hl, hr⟩ := hchildren w hge hw
    have hlW : left w < W := by omega
    have hrW : right w < W := by omega
    have hv := hsem w hge hw
    cases ha : isAnd w with
    | true =>
      simp [ha] at hv
      have hnp : neg (left w) = false ∨ neg (right w) = false := by
        rw [hv.1] at hn
        simpa only [Bool.and_eq_false_iff] using hn
      have hpp : pos (left w) = true ∧ pos (right w) = true := by
        rw [hv.2] at hp
        simpa only [Bool.and_eq_true] using hp
      rcases hnp with hnl | hnr
      · rcases ih (left w) hl hlW hnl hpp.1 with hh | hh
        · exact Or.inr ⟨w, hge, hw, ha, hp, Or.inl ⟨hh, hsafe _ hlW hnl, hnl⟩⟩
        · exact Or.inr hh
      · rcases ih (right w) hr hrW hnr hpp.2 with hh | hh
        · exact Or.inr ⟨w, hge, hw, ha, hp, Or.inr ⟨hh, hsafe _ hrW hnr, hnr⟩⟩
        · exact Or.inr hh
    | false =>
      simp [ha] at hv
      have hnp : neg (left w) = false ∧ neg (right w) = false := by
        rw [hv.1] at hn
        simpa only [Bool.or_eq_false_iff] using hn
      have hpp : pos (left w) = true ∨ pos (right w) = true := by
        rw [hv.2] at hp
        simpa only [Bool.or_eq_true] using hp
      rcases hpp with hpl | hpr
      · rcases ih (left w) hl hlW hnp.1 hpl with hh | hh
        · exact Or.inl ((hreach w hge hw ha).symm ▸ Finset.mem_union_left _ hh)
        · exact Or.inr hh
      · rcases ih (right w) hr hrW hnp.2 hpr with hh | hh
        · exact Or.inl ((hreach w hge hw ha).symm ▸ Finset.mem_union_right _ hh)
        · exact Or.inr hh

end SafeLineSets

namespace SafeLineSets.CircuitInterface

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
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
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
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
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
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
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
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
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
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
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold wireFn Circuit.wires
  change (wiresFrom C.gates (List.ofFn x)).getD w false = _
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

lemma gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  simp [gateAt, hj]

lemma binary_gate (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, a < n + j ∧ b < n + j ∧
      (gateAt C j).inputs = [a, b] ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ x, wireFn n C (n + j) x =
        (gateAt C j).op.eval [wireFn n C a x, wireFn n C b x] := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
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


def leftWire (n : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (gateAt C (w - n)).inputs.getD 0 0

def rightWire (n : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (gateAt C (w - n)).inputs.getD 1 0

def lineReach (p l : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin l) :=
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  if w < p + l then Finset.univ.filter fun b => p + b.val = w
  else if (gateAt C (w - (p + l))).op = GateOp.or then
    if h : leftWire (p + l) C w < w ∧ rightWire (p + l) C w < w then
      lineReach p l C (leftWire (p + l) C w) ∪ lineReach p l C (rightWire (p + l) C w)
    else ∅
  else ∅
termination_by w

def rowInput {p l : ℕ} (a : Fin p) (y : Fin l → Bool) (i : Fin (p + l)) : Bool :=
  if hi : i.val < p then decide (i.val = a.val)
  else y ⟨i.val - p, by omega⟩

lemma binary_wire_data (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (w : ℕ) (hge : n ≤ w) (hw : w < n + C.gates.length) :
    leftWire n C w < w ∧ rightWire n C w < w ∧
      ((gateAt C (w - n)).op = GateOp.and ∨ (gateAt C (w - n)).op = GateOp.or) ∧
      ∀ x, wireFn n C w x = (gateAt C (w - n)).op.eval
        [wireFn n C (leftWire n C w) x, wireFn n C (rightWire n C w) x] := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hj : w - n < C.gates.length := by omega
  obtain ⟨a, b, ha, hb, hab, hop, hv⟩ := binary_gate n C hC (w - n) hj
  have hsum : n + (w - n) = w := by omega
  simpa [leftWire, rightWire, hab, hsum] using And.intro ha (And.intro hb (And.intro hop hv))

lemma lineReach_or (p l : ℕ) (C : Circuit) (hC : IsAO2 (p + l) C)
    (w : ℕ) (hge : p + l ≤ w) (hw : w < p + l + C.gates.length)
    (hop : (gateAt C (w - (p + l))).op = GateOp.or) :
    lineReach p l C w = lineReach p l C (leftWire (p + l) C w) ∪
      lineReach p l C (rightWire (p + l) C w) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hd := binary_wire_data (p + l) C hC w hge hw
  rw [lineReach]
  simp [show ¬ w < p + l by omega, hop, hd.1, hd.2.1]

lemma lineReach_sound (p l : ℕ) (C : Circuit) (hC : IsAO2 (p + l) C) :
    ∀ w < p + l + C.gates.length, ∀ b ∈ lineReach p l C w,
      ∀ x : Fin (p + l) → Bool, x (Fin.natAdd p b) = true → wireFn (p + l) C w x = true := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw b hb x hx
    by_cases hin : w < p + l
    · have he : p + b.val = w := by simpa [lineReach, hin] using hb
      rw [wireFn_input (p + l) C w hin]
      convert hx using 1
      apply congrArg x
      apply Fin.ext
      simpa using he.symm
    · have hge : p + l ≤ w := by omega
      have hd := binary_wire_data (p + l) C hC w hge hw
      have hop : (gateAt C (w - (p + l))).op = GateOp.or := by
        by_contra hno
        simpa [lineReach, hin, hno] using hb
      rw [lineReach_or p l C hC w hge hw hop] at hb
      rw [hd.2.2.2 x, hop]
      simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]
      rcases Finset.mem_union.mp hb with hb | hb
      · simp [ih _ hd.1 (by omega) b hb x hx]
      · simp [ih _ hd.2.1 (by omega) b hb x hx]


lemma rowInput_line {p l : ℕ} (a : Fin p) (y : Fin l → Bool) (b : Fin l) :
    rowInput a y (Fin.natAdd p b) = y b := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  simp [rowInput, show ¬ p + b.val < p by omega]

def allLines (p l : ℕ) (i : Fin (p + l)) : Bool := decide (p ≤ i.val)

lemma allLines_line (p l : ℕ) (b : Fin l) : allLines p l (Fin.natAdd p b) = true := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  simp [allLines]

lemma circuit_safe_slot (p l : ℕ) (C : Circuit) (hC : IsAO2 (p + l) C)
    (a : Fin p) (b : Fin l) (N : Finset (Fin l))
    (hout : C.output < p + l + C.gates.length)
    (hneg : wireFn (p + l) C C.output (rowInput a (fun c => decide (c ∉ N))) = false)
    (hpos : wireFn (p + l) C C.output (rowInput a (fun c => decide (c = b))) = true)
    (hlines : wireFn (p + l) C C.output (allLines p l) = false) :
    ∃ g, p + l ≤ g ∧ g < p + l + C.gates.length ∧
      (gateAt C (g - (p + l))).op = GateOp.and ∧
      wireFn (p + l) C g (rowInput a (fun c => decide (c = b))) = true ∧
      ((b ∈ lineReach p l C (leftWire (p + l) C g) ∧
        lineReach p l C (leftWire (p + l) C g) ⊆ N ∧
        wireFn (p + l) C (leftWire (p + l) C g) (rowInput a (fun c => decide (c ∉ N))) = false) ∨
       (b ∈ lineReach p l C (rightWire (p + l) C g) ∧
        lineReach p l C (rightWire (p + l) C g) ⊆ N ∧
        wireFn (p + l) C (rightWire (p + l) C g) (rowInput a (fun c => decide (c ∉ N))) = false)) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  classical
  let neg := fun w => wireFn (p + l) C w (rowInput a (fun c => decide (c ∉ N)))
  let pos := fun w => wireFn (p + l) C w (rowInput a (fun c => decide (c = b)))
  let isAnd := fun w => decide ((gateAt C (w - (p + l))).op = GateOp.and)
  have hinputs : ∀ w < p + l, neg w = false → pos w = true → b ∈ lineReach p l C w := by
    intro w hw hn hp
    change wireFn (p + l) C w _ = false at hn
    change wireFn (p + l) C w _ = true at hp
    rw [wireFn_input (p + l) C w hw] at hn hp
    by_cases hpoint : w < p
    · simp [rowInput, hpoint] at hn hp
      contradiction
    · have hb : (⟨w - p, by omega⟩ : Fin l) = b := by
        simpa [rowInput, hpoint] using hp
      have hv := congrArg Fin.val hb
      change w - p = b.val at hv
      simp [lineReach, hw]
      omega
  have hchildren : ∀ w, p + l ≤ w → w < p + l + C.gates.length →
      leftWire (p + l) C w < w ∧ rightWire (p + l) C w < w := by
    intro w hge hw
    have hd := binary_wire_data (p + l) C hC w hge hw
    exact ⟨hd.1, hd.2.1⟩
  have hsem : ∀ w, p + l ≤ w → w < p + l + C.gates.length →
      if isAnd w then
        neg w = (neg (leftWire (p + l) C w) && neg (rightWire (p + l) C w)) ∧
        pos w = (pos (leftWire (p + l) C w) && pos (rightWire (p + l) C w))
      else neg w = (neg (leftWire (p + l) C w) || neg (rightWire (p + l) C w)) ∧
        pos w = (pos (leftWire (p + l) C w) || pos (rightWire (p + l) C w)) := by
    intro w hge hw
    have hd := binary_wire_data (p + l) C hC w hge hw
    have hn := hd.2.2.2 (rowInput a (fun c => decide (c ∉ N)))
    have hp := hd.2.2.2 (rowInput a (fun c => decide (c = b)))
    rcases hd.2.2.1 with hop | hop <;>
      simpa [isAnd, neg, pos, hop, GateOp.eval] using And.intro hn hp
  have hreach : ∀ w, p + l ≤ w → w < p + l + C.gates.length → isAnd w = false →
      lineReach p l C w = lineReach p l C (leftWire (p + l) C w) ∪
        lineReach p l C (rightWire (p + l) C w) := by
    intro w hge hw hn
    have hd := binary_wire_data (p + l) C hC w hge hw
    rcases hd.2.2.1 with hop | hop
    · simp [isAnd, hop] at hn
    · exact lineReach_or p l C hC w hge hw hop
  have hsafe : ∀ w < p + l + C.gates.length, neg w = false → lineReach p l C w ⊆ N := by
    intro w hw hn c hc
    by_contra hcn
    have hv := lineReach_sound p l C hC w hw c hc (rowInput a (fun c => decide (c ∉ N)))
      (by simp [rowInput_line, hcn])
    change neg w = true at hv
    simp [hn] at hv
  have hroot : lineReach p l C C.output = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hv := lineReach_sound p l C hC C.output hout c hc (allLines p l) (allLines_line p l c)
    simp [hlines] at hv
  have ht := safe_trace (p + l) (p + l + C.gates.length) isAnd
    (leftWire (p + l) C) (rightWire (p + l) C) neg pos (lineReach p l C) N b
    hinputs hchildren hsem hreach hsafe C.output hout hneg hpos
  rcases ht with ht | ⟨g, hg, hgW, hgAnd, hgPos, hslot⟩
  · simp [hroot] at ht
  · exact ⟨g, hg, hgW, of_decide_eq_true hgAnd, hgPos, hslot⟩


lemma rowInput_point {p l : ℕ} (a a' : Fin p) (y : Fin l → Bool) :
    rowInput a y (Fin.castAdd l a') = decide (a' = a) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  simp [rowInput, a'.isLt, Fin.ext_iff]

def andWires (n : ℕ) (C : Circuit) : Finset ℕ :=
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  (Finset.Ico n (n + C.gates.length)).filter fun w => (gateAt C (w - n)).op = GateOp.and

def doubleLineWires (p l : ℕ) (C : Circuit) : Finset ℕ :=
  (andWires (p + l) C).filter fun w =>
    (lineReach p l C (leftWire (p + l) C w)).Nonempty ∧
    (lineReach p l C (rightWire (p + l) C w)).Nonempty

lemma graph_circuit_slot_cover_strong (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : IsAO2 (p + l) C)
    (hf : ∀ x, wireFn (p + l) C C.output x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∀ a b, (a, b) ∈ E → ∃ w ∈ andWires (p + l) C,
      wireFn (p + l) C w (rowInput a (fun c => decide (c = b))) = true ∧
      ((b ∈ lineReach p l C (leftWire (p + l) C w) ∧
         (∀ c ∈ lineReach p l C (leftWire (p + l) C w), (a, c) ∈ E) ∧
        wireFn (p + l) C (leftWire (p + l) C w) (rowInput a (fun c => decide ((a, c) ∉ E))) = false) ∨
      (b ∈ lineReach p l C (rightWire (p + l) C w) ∧
         (∀ c ∈ lineReach p l C (rightWire (p + l) C w), (a, c) ∈ E) ∧
        wireFn (p + l) C (rightWire (p + l) C w) (rowInput a (fun c => decide ((a, c) ∉ E))) = false)) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro a b hab
  let N : Finset (Fin l) := Finset.univ.filter fun c => (a, c) ∈ E
  have hneg : wireFn (p + l) C C.output (rowInput a (fun c => decide (c ∉ N))) = false := by
    rw [hf]
    simp only [decide_eq_false_iff_not]
    rintro ⟨a', b', he, hpa, hlb⟩
    have haa : a' = a := by simpa only [rowInput_point, decide_eq_true_eq] using hpa
    subst a'
    have hnb : b' ∉ N := by simpa only [rowInput_line, decide_eq_true_eq] using hlb
    exact hnb (by simp [N, he])
  have hpos : wireFn (p + l) C C.output (rowInput a (fun c => decide (c = b))) = true := by
    rw [hf]
    apply decide_eq_true
    exact ⟨a, b, hab, by simp [rowInput_point], by simp [rowInput_line]⟩
  have hlines : wireFn (p + l) C C.output (allLines p l) = false := by
    rw [hf]
    simp [allLines]
  have hout : C.output < p + l + C.gates.length := by
    by_contra hn
    have hwlen : (C.wires (List.ofFn (rowInput a (fun c => decide (c = b))))).length =
        p + l + C.gates.length := by
      change (wiresFrom C.gates _).length = _
      rw [length_wiresFrom, List.length_ofFn]
    change (C.wires _).getD C.output false = true at hpos
    rw [List.getD_eq_default _ _ (by rw [hwlen]; omega)] at hpos
    cases hpos
  obtain ⟨w, hwlo, hwhi, hop, hgatepos, hslot⟩ := circuit_safe_slot p l C hC a b N hout hneg hpos hlines
  refine ⟨w, by simp [andWires, hwlo, hwhi, hop], hgatepos, ?_⟩
  rcases hslot with hslot | hslot
  · exact Or.inl ⟨hslot.1, (fun c hc => (Finset.mem_filter.mp (hslot.2.1 hc)).2), by simpa [N] using hslot.2.2⟩
  · exact Or.inr ⟨hslot.1, (fun c hc => (Finset.mem_filter.mp (hslot.2.1 hc)).2), by simpa [N] using hslot.2.2⟩

lemma graph_circuit_slot_cover (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : IsAO2 (p + l) C)
    (hf : ∀ x, wireFn (p + l) C C.output x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∀ a b, (a, b) ∈ E → ∃ w ∈ andWires (p + l) C,
      (b ∈ lineReach p l C (leftWire (p + l) C w) ∧
        ∀ c ∈ lineReach p l C (leftWire (p + l) C w), (a, c) ∈ E) ∨
      (b ∈ lineReach p l C (rightWire (p + l) C w) ∧
        ∀ c ∈ lineReach p l C (rightWire (p + l) C w), (a, c) ∈ E) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro a b hab
  obtain ⟨w, hw, _, hh⟩ := graph_circuit_slot_cover_strong p l E C hC hf a b hab
  refine ⟨w, hw, ?_⟩
  rcases hh with hh | hh
  · exact Or.inl ⟨hh.1, hh.2.1⟩
  · exact Or.inr ⟨hh.1, hh.2.1⟩

lemma graph_circuit_cover_budget (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : IsAO2 (p + l) C)
    (hE : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hf : ∀ x, wireFn (p + l) C C.output x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∃ S : Finset (Fin (p + l)),
      S.card ≤ (andWires (p + l) C).card + (doubleLineWires p l C).card ∧
      ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  obtain ⟨S, hcard, hcover⟩ := and_child_cover_budget E (andWires (p + l) C)
    (fun w => lineReach p l C (leftWire (p + l) C w))
    (fun w => lineReach p l C (rightWire (p + l) C w)) hE (graph_circuit_slot_cover p l E C hC hf)
  let f : Fin p ⊕ Fin l → Fin (p + l) := Sum.elim (Fin.castAdd l) (Fin.natAdd p)
  refine ⟨S.image f, le_trans Finset.card_image_le hcard, ?_⟩
  intro a b hab
  rcases hcover a b hab with ha | hb
  · exact Or.inl (Finset.mem_image.mpr ⟨Sum.inl a, ha, rfl⟩)
  · exact Or.inr (Finset.mem_image.mpr ⟨Sum.inr b, hb, rfl⟩)

lemma no_doubleLineWires_of_and_false_on_allLines (p l : ℕ) (C : Circuit)
    (hC : IsAO2 (p + l) C)
    (hfalse : ∀ w ∈ andWires (p + l) C, wireFn (p + l) C w (allLines p l) = false) :
    doubleLineWires p l C = ∅ := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hm := Finset.mem_filter.mp hw
  have hg := Finset.mem_filter.mp hm.1
  have hbound := Finset.mem_Ico.mp hg.1
  have hd := binary_wire_data (p + l) C hC w hbound.1 hbound.2
  obtain ⟨b, hb⟩ := hm.2.1
  obtain ⟨c, hc⟩ := hm.2.2
  have hvb := lineReach_sound p l C hC _ (by omega) b hb (allLines p l) (allLines_line p l b)
  have hvc := lineReach_sound p l C hC _ (by omega) c hc (allLines p l) (allLines_line p l c)
  have hv := hd.2.2.2 (allLines p l)
  have hh := hfalse w hm.1
  rw [hv] at hh
  simp [hg.2, GateOp.eval, hvb, hvc] at hh

lemma graph_circuit_and_cover (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : IsAO2 (p + l) C)
    (hE : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hf : ∀ x, wireFn (p + l) C C.output x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hfalse : ∀ w ∈ andWires (p + l) C, wireFn (p + l) C w (allLines p l) = false) :
    ∃ S : Finset (Fin (p + l)), S.card ≤ (andWires (p + l) C).card ∧
      ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  simpa [no_doubleLineWires_of_and_false_on_allLines p l C hC hfalse] using
    graph_circuit_cover_budget p l E C hC hE hf

end SafeLineSets.CircuitInterface

namespace SafeLineSets.CircuitInterface

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.TwoColour


lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

lemma orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

lemma orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega

lemma orReaches_trans (n : ℕ) (C : Circuit) (k g : ℕ) (hkg : PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w k → PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
    obtain ⟨hm, h3⟩ := (orReaches_iff n C m k).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]; exact hkg
    · exact orReaches_step n C m i g hm hop hi hlt (ih i hlt hri)

lemma orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

lemma orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩


lemma orIn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    orIn n C w = {⟨w, hw⟩} := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  ext i
  rw [mem_orIn, Finset.mem_singleton]
  constructor
  · rintro (he | ⟨j, hj, hr, ho, hi⟩)
    · exact Fin.ext he
    · have := hr.1
      omega
  · intro he
    exact Or.inl (congrArg Fin.val he)

lemma orIn_invalid (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : orIn n C w = ∅ := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  rcases (mem_orIn n C w i).mp hi with he | ⟨j, hj, hr, ho, hi⟩
  · have := i.isLt
    omega
  · have := (orReaches_bound n C j w hr).2
    omega

lemma orIn_gate (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    orIn n C (n + j) = @ite (Finset (Fin n)) ((gateAt C j).op = .or) (Classical.propDecidable _)
      ((gateAt C j).inputs.toFinset.biUnion (orIn n C)) ∅ := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  classical
  ext a
  rw [mem_orIn]
  by_cases hop : (gateAt C j).op = .or
  · simp only [hop, ↓reduceIte, Finset.mem_biUnion]
    constructor
    · rintro (he | ⟨k, hk, hr, hok, hai⟩)
      · have := a.isLt
        omega
      · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨_, w, hw, hlt, hrw⟩⟩
        · subst k
          exact ⟨a.val, List.mem_toFinset.mpr hai, orIn_self n C a⟩
        · exact ⟨w, List.mem_toFinset.mpr hw,
            (mem_orIn n C w a).mpr (Or.inr ⟨k, hk, hrw, hok, hai⟩)⟩
    · rintro ⟨w, hw, haw⟩
      have hw' := List.mem_toFinset.mp hw
      exact (mem_orIn n C (n+j) a).mp
        (orIn_up n C j w a hj hop hw' (hC j hj w hw') haw)
  · simp only [hop, ↓reduceIte]
    simp only [Finset.notMem_empty, iff_false]
    rintro (he | ⟨k, hk, hr, hok, hai⟩)
    · have := a.isLt
      omega
    · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨ho, _⟩⟩
      · subst k
        exact hop hok
      · exact hop ho

lemma tCount_zero_iff_gate (n : ℕ) (C : Circuit) (lin : ℕ → Bool) :
    tCount n C lin = 0 ↔ ∀ j < C.gates.length, (gateAt C j).op = .or →
      ∀ a ∈ orIn n C (n+j), ∀ b ∈ orIn n C (n+j), lin a.val = lin b.val := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  classical
  rw [tCount, Finset.card_eq_zero]
  constructor
  · intro hz j hj hop a ha b hb
    by_contra hne
    have hm : (∃ i ∈ orIn n C (n+j), lin i.val = false) ∧
        (∃ i ∈ orIn n C (n+j), lin i.val = true) := by
      cases hla : lin a.val <;> cases hlb : lin b.val
      · exact (hne (hla.trans hlb.symm)).elim
      · exact ⟨⟨a,ha,hla⟩,⟨b,hb,hlb⟩⟩
      · exact ⟨⟨b,hb,hlb⟩,⟨a,ha,hla⟩⟩
      · exact (hne (hla.trans hlb.symm)).elim
    have hmem : j ∈ twoColour n C lin :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hj, hop, hm⟩
    rw [hz] at hmem
    exact Finset.notMem_empty j hmem
  · intro h
    apply Finset.eq_empty_of_forall_notMem
    intro j hj
    obtain ⟨_, hj', hop, ⟨a,ha,hla⟩, ⟨b,hb,hlb⟩⟩ := Finset.mem_filter.mp hj
    have he := h j hj' hop a ha b hb
    rw [hla, hlb] at he
    cases he

lemma tCount_zero_all_wires (n : ℕ) (C : Circuit) (lin : ℕ → Bool)
    (hC : ReadsBack n C) (hT : tCount n C lin = 0) :
    ∀ w, ∀ a ∈ orIn n C w, ∀ b ∈ orIn n C w, lin a.val = lin b.val := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  classical
  intro w a ha b hb
  by_cases hw : w < n
  · rw [orIn_input n C w hw, Finset.mem_singleton] at ha hb
    rw [ha, hb]
  · by_cases hv : w < n+C.gates.length
    · have hj : w-n < C.gates.length := by omega
      have he : n+(w-n) = w := by omega
      by_cases hop : (gateAt C (w-n)).op = .or
      · exact (tCount_zero_iff_gate n C lin).mp hT (w-n) hj hop a
          (by simpa [he] using ha) b (by simpa [he] using hb)
      · have hempty : orIn n C w = ∅ := by
          rw [← he, orIn_gate n C hC (w-n) hj]
          simp only [hop, ↓reduceIte]
        rw [hempty] at ha
        exact (Finset.notMem_empty a ha).elim
    · rw [orIn_invalid n C w (by omega)] at ha
      exact (Finset.notMem_empty a ha).elim


lemma procedural_reach_in_orIn {α : Type*} [DecidableEq α]
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (embed : α → Fin n) (Q : ℕ → Finset α)
    (hinput : ∀ w < n, ∀ a ∈ Q w, (embed a).val = w)
    (hgate : ∀ j < C.gates.length, Q (n + j) =
      @ite (Finset α) ((gateAt C j).op = GateOp.or) (gateOpDecEq _ _)
        (Q (leftWire n C (n + j)) ∪ Q (rightWire n C (n + j))) ∅) :
    ∀ w < n + C.gates.length, ∀ a ∈ Q w, embed a ∈ orIn n C w := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw a ha
    by_cases hin : w < n
    · have he := hinput w hin a ha
      rw [← he]
      exact orIn_self n C (embed a)
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hd := binary_wire_data n C hC (n + j) (by omega) hw
      obtain ⟨u, v, hu, hv, huv, hop, _⟩ := binary_gate n C hC j hj
      have hleft : leftWire n C (n + j) ∈ (gateAt C j).inputs := by
        simp [leftWire, huv]
      have hright : rightWire n C (n + j) ∈ (gateAt C j).inputs := by
        simp [rightWire, huv]
      rw [hgate j hj] at ha
      by_cases hor : (gateAt C j).op = GateOp.or
      · simp only [hor, ↓reduceIte, Finset.mem_union] at ha
        rcases ha with ha | ha
        · exact orIn_up n C j _ (embed a) hj hor hleft hd.1
            (ih _ hd.1 (by omega) a ha)
        · exact orIn_up n C j _ (embed a) hj hor hright hd.2.1
            (ih _ hd.2.1 (by omega) a ha)
      · simp [hor] at ha

lemma lineReach_in_orIn (p l : ℕ) (C : Circuit) (hC : IsAO2 (p + l) C) :
    ∀ w < p + l + C.gates.length, ∀ b ∈ lineReach p l C w,
      Fin.natAdd p b ∈ orIn (p + l) C w := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  apply procedural_reach_in_orIn (p + l) C hC (Fin.natAdd p) (lineReach p l C)
  · intro w hw b hb
    simpa [lineReach, hw] using hb
  · intro j hj
    have hd := binary_wire_data (p + l) C hC (p + l + j) (by omega) (by omega)
    rw [lineReach]
    simp [show ¬ p + l + j < p + l by omega, hd.1, hd.2.1]

lemma palette_disjoint_of_tCount (p l : ℕ) (C : Circuit) (hC : IsAO2 (p + l) C)
    (P : ℕ → Finset (Fin p))
    (hP : ∀ w < p + l + C.gates.length, ∀ a ∈ P w,
      Fin.castAdd l a ∈ orIn (p + l) C w)
    (hT : tCount (p + l) C (fun i => decide (p ≤ i)) = 0) :
    ∀ w < p + l + C.gates.length, P w = ∅ ∨ lineReach p l C w = ∅ := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro w hw
  by_cases hp : P w = ∅
  · exact Or.inl hp
  right
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hp
  have he := tCount_zero_all_wires (p + l) C (fun i => decide (p ≤ i)) hC.2.1 hT w
    (Fin.castAdd l a) (hP w hw a ha) (Fin.natAdd p b) (lineReach_in_orIn p l C hC w hw b hb)
  simp [show ¬ p ≤ a.val by omega] at he

end SafeLineSets.CircuitInterface

namespace SafeLineSets.CircuitInterface

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm


def pointReach (p l : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin p) :=
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  if w < p + l then Finset.univ.filter fun b => b.val = w
  else if (gateAt C (w - (p + l))).op = GateOp.or then
    if h : leftWire (p + l) C w < w ∧ rightWire (p + l) C w < w then
      pointReach p l C (leftWire (p + l) C w) ∪ pointReach p l C (rightWire (p + l) C w)
    else ∅
  else ∅
termination_by w

def columnInput {p l : ℕ} (b : Fin l) (x : Fin p → Bool) (i : Fin (p + l)) : Bool :=
  if hi : i.val < p then x ⟨i.val, hi⟩
  else decide (i.val - p = b.val)

lemma pointReach_or (p l : ℕ) (C : Circuit) (hC : IsAO2 (p + l) C)
    (w : ℕ) (hge : p + l ≤ w) (hw : w < p + l + C.gates.length)
    (hop : (gateAt C (w - (p + l))).op = GateOp.or) :
    pointReach p l C w = pointReach p l C (leftWire (p + l) C w) ∪
      pointReach p l C (rightWire (p + l) C w) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hd := binary_wire_data (p + l) C hC w hge hw
  rw [pointReach]
  simp [show ¬ w < p + l by omega, hop, hd.1, hd.2.1]

lemma pointReach_sound (p l : ℕ) (C : Circuit) (hC : IsAO2 (p + l) C) :
    ∀ w < p + l + C.gates.length, ∀ b ∈ pointReach p l C w,
      ∀ x : Fin (p + l) → Bool, x (Fin.castAdd l b) = true → wireFn (p + l) C w x = true := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw b hb x hx
    by_cases hin : w < p + l
    · have he : b.val = w := by simpa [pointReach, hin] using hb
      rw [wireFn_input (p + l) C w hin]
      convert hx using 1
      apply congrArg x
      apply Fin.ext
      simpa using he.symm
    · have hge : p + l ≤ w := by omega
      have hd := binary_wire_data (p + l) C hC w hge hw
      have hop : (gateAt C (w - (p + l))).op = GateOp.or := by
        by_contra hno
        simpa [pointReach, hin, hno] using hb
      rw [pointReach_or p l C hC w hge hw hop] at hb
      rw [hd.2.2.2 x, hop]
      simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]
      rcases Finset.mem_union.mp hb with hb | hb
      · simp [ih _ hd.1 (by omega) b hb x hx]
      · simp [ih _ hd.2.1 (by omega) b hb x hx]


lemma columnInput_point {p l : ℕ} (b : Fin l) (x : Fin p → Bool) (a : Fin p) :
    columnInput b x (Fin.castAdd l a) = x a := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  simp [columnInput, a.isLt]

def allPoints (p l : ℕ) (i : Fin (p + l)) : Bool := decide (i.val < p)

lemma allPoints_point (p l : ℕ) (a : Fin p) : allPoints p l (Fin.castAdd l a) = true := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  simp [allPoints, a.isLt]

lemma circuit_point_safe_slot (p l : ℕ) (C : Circuit) (hC : IsAO2 (p + l) C)
    (b : Fin l) (a : Fin p) (N : Finset (Fin p))
    (hout : C.output < p + l + C.gates.length)
    (hneg : wireFn (p + l) C C.output (columnInput b (fun c => decide (c ∉ N))) = false)
    (hpos : wireFn (p + l) C C.output (columnInput b (fun c => decide (c = a))) = true)
    (hlines : wireFn (p + l) C C.output (allPoints p l) = false) :
    ∃ g, p + l ≤ g ∧ g < p + l + C.gates.length ∧
      (gateAt C (g - (p + l))).op = GateOp.and ∧
      wireFn (p + l) C g (columnInput b (fun c => decide (c = a))) = true ∧
      ((a ∈ pointReach p l C (leftWire (p + l) C g) ∧
        pointReach p l C (leftWire (p + l) C g) ⊆ N ∧
        wireFn (p + l) C (leftWire (p + l) C g) (columnInput b (fun c => decide (c ∉ N))) = false) ∨
       (a ∈ pointReach p l C (rightWire (p + l) C g) ∧
        pointReach p l C (rightWire (p + l) C g) ⊆ N ∧
        wireFn (p + l) C (rightWire (p + l) C g) (columnInput b (fun c => decide (c ∉ N))) = false)) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  classical
  let neg := fun w => wireFn (p + l) C w (columnInput b (fun c => decide (c ∉ N)))
  let pos := fun w => wireFn (p + l) C w (columnInput b (fun c => decide (c = a)))
  let isAnd := fun w => decide ((gateAt C (w - (p + l))).op = GateOp.and)
  have hinputs : ∀ w < p + l, neg w = false → pos w = true → a ∈ pointReach p l C w := by
    intro w hw hn hp
    change wireFn (p + l) C w _ = false at hn
    change wireFn (p + l) C w _ = true at hp
    rw [wireFn_input (p + l) C w hw] at hn hp
    by_cases hpoint : w < p
    · have ha : (⟨w, hpoint⟩ : Fin p) = a := by
        simpa [columnInput, hpoint] using hp
      have hv := congrArg Fin.val ha
      change w = a.val at hv
      rw [pointReach]
      simp only [if_pos hw, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hv.symm
    · simp [columnInput, hpoint] at hn hp
      contradiction
  have hchildren : ∀ w, p + l ≤ w → w < p + l + C.gates.length →
      leftWire (p + l) C w < w ∧ rightWire (p + l) C w < w := by
    intro w hge hw
    have hd := binary_wire_data (p + l) C hC w hge hw
    exact ⟨hd.1, hd.2.1⟩
  have hsem : ∀ w, p + l ≤ w → w < p + l + C.gates.length →
      if isAnd w then
        neg w = (neg (leftWire (p + l) C w) && neg (rightWire (p + l) C w)) ∧
        pos w = (pos (leftWire (p + l) C w) && pos (rightWire (p + l) C w))
      else neg w = (neg (leftWire (p + l) C w) || neg (rightWire (p + l) C w)) ∧
        pos w = (pos (leftWire (p + l) C w) || pos (rightWire (p + l) C w)) := by
    intro w hge hw
    have hd := binary_wire_data (p + l) C hC w hge hw
    have hn := hd.2.2.2 (columnInput b (fun c => decide (c ∉ N)))
    have hp := hd.2.2.2 (columnInput b (fun c => decide (c = a)))
    rcases hd.2.2.1 with hop | hop <;>
      simpa [isAnd, neg, pos, hop, GateOp.eval] using And.intro hn hp
  have hreach : ∀ w, p + l ≤ w → w < p + l + C.gates.length → isAnd w = false →
      pointReach p l C w = pointReach p l C (leftWire (p + l) C w) ∪
        pointReach p l C (rightWire (p + l) C w) := by
    intro w hge hw hn
    have hd := binary_wire_data (p + l) C hC w hge hw
    rcases hd.2.2.1 with hop | hop
    · simp [isAnd, hop] at hn
    · exact pointReach_or p l C hC w hge hw hop
  have hsafe : ∀ w < p + l + C.gates.length, neg w = false → pointReach p l C w ⊆ N := by
    intro w hw hn c hc
    by_contra hcn
    have hv := pointReach_sound p l C hC w hw c hc (columnInput b (fun c => decide (c ∉ N)))
      (by simp [columnInput_point, hcn])
    change neg w = true at hv
    simp [hn] at hv
  have hroot : pointReach p l C C.output = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hv := pointReach_sound p l C hC C.output hout c hc (allPoints p l) (allPoints_point p l c)
    simp [hlines] at hv
  have ht := safe_trace (p + l) (p + l + C.gates.length) isAnd
    (leftWire (p + l) C) (rightWire (p + l) C) neg pos (pointReach p l C) N a
    hinputs hchildren hsem hreach hsafe C.output hout hneg hpos
  rcases ht with ht | ⟨g, hg, hgW, hgAnd, hgPos, hslot⟩
  · simp [hroot] at ht
  · exact ⟨g, hg, hgW, of_decide_eq_true hgAnd, hgPos, hslot⟩


lemma columnInput_line {p l : ℕ} (b b' : Fin l) (x : Fin p → Bool) :
    columnInput b x (Fin.natAdd p b') = decide (b' = b) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  simp [columnInput, show ¬ p + b'.val < p by omega, Fin.ext_iff]

end SafeLineSets.CircuitInterface

namespace SafeLineSets.CircuitInterface

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma graph_circuit_point_slot_cover_strong (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : IsAO2 (p + l) C)
    (hf : ∀ x, wireFn (p + l) C C.output x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∀ a b, (a, b) ∈ E → ∃ w ∈ andWires (p + l) C,
      wireFn (p + l) C w (columnInput b (fun c => decide (c = a))) = true ∧
      ((a ∈ pointReach p l C (leftWire (p + l) C w) ∧
         (∀ c ∈ pointReach p l C (leftWire (p + l) C w), (c, b) ∈ E) ∧
        wireFn (p + l) C (leftWire (p + l) C w) (columnInput b (fun c => decide ((c, b) ∉ E))) = false) ∨
      (a ∈ pointReach p l C (rightWire (p + l) C w) ∧
         (∀ c ∈ pointReach p l C (rightWire (p + l) C w), (c, b) ∈ E) ∧
        wireFn (p + l) C (rightWire (p + l) C w) (columnInput b (fun c => decide ((c, b) ∉ E))) = false)) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro a b hab
  let N : Finset (Fin p) := Finset.univ.filter fun c => (c, b) ∈ E
  have hneg : wireFn (p + l) C C.output (columnInput b (fun c => decide (c ∉ N))) = false := by
    rw [hf]
    simp only [decide_eq_false_iff_not]
    rintro ⟨a', b', he, hpa, hlb⟩
    have hbb : b' = b := by simpa only [columnInput_line, decide_eq_true_eq] using hlb
    subst b'
    have hna : a' ∉ N := by simpa only [columnInput_point, decide_eq_true_eq] using hpa
    exact hna (by simp [N, he])
  have hpos : wireFn (p + l) C C.output (columnInput b (fun c => decide (c = a))) = true := by
    rw [hf]
    apply decide_eq_true
    exact ⟨a, b, hab, by simp [columnInput_point], by simp [columnInput_line]⟩
  have hpoints : wireFn (p + l) C C.output (allPoints p l) = false := by
    rw [hf]
    simp [allPoints]
  have hout : C.output < p + l + C.gates.length := by
    by_contra hn
    have hwlen : (C.wires (List.ofFn (columnInput b (fun c => decide (c = a))))).length =
        p + l + C.gates.length := by
      change (wiresFrom C.gates _).length = _
      rw [length_wiresFrom, List.length_ofFn]
    change (C.wires _).getD C.output false = true at hpos
    rw [List.getD_eq_default _ _ (by rw [hwlen]; omega)] at hpos
    cases hpos
  obtain ⟨w, hwlo, hwhi, hop, hgatepos, hslot⟩ := circuit_point_safe_slot p l C hC b a N hout hneg hpos hpoints
  refine ⟨w, by simp [andWires, hwlo, hwhi, hop], hgatepos, ?_⟩
  rcases hslot with hslot | hslot
  · exact Or.inl ⟨hslot.1, (fun c hc => (Finset.mem_filter.mp (hslot.2.1 hc)).2), by simpa [N] using hslot.2.2⟩
  · exact Or.inr ⟨hslot.1, (fun c hc => (Finset.mem_filter.mp (hslot.2.1 hc)).2), by simpa [N] using hslot.2.2⟩

lemma graph_circuit_point_slot_cover (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : IsAO2 (p + l) C)
    (hf : ∀ x, wireFn (p + l) C C.output x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∀ a b, (a, b) ∈ E → ∃ w ∈ andWires (p + l) C,
      (a ∈ pointReach p l C (leftWire (p + l) C w) ∧
        ∀ c ∈ pointReach p l C (leftWire (p + l) C w), (c, b) ∈ E) ∨
      (a ∈ pointReach p l C (rightWire (p + l) C w) ∧
        ∀ c ∈ pointReach p l C (rightWire (p + l) C w), (c, b) ∈ E) := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro a b hab
  obtain ⟨w, hw, _, hh⟩ := graph_circuit_point_slot_cover_strong p l E C hC hf a b hab
  refine ⟨w, hw, ?_⟩
  rcases hh with hh | hh
  · exact Or.inl ⟨hh.1, hh.2.1⟩
  · exact Or.inr ⟨hh.1, hh.2.1⟩

end SafeLineSets.CircuitInterface

namespace SafeLineSets.CircuitInterface

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour


lemma pointReach_in_orIn (p l : ℕ) (C : Circuit) (hC : IsAO2 (p + l) C) :
    ∀ w < p + l + C.gates.length, ∀ a ∈ pointReach p l C w,
      Fin.castAdd l a ∈ orIn (p + l) C w := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  apply procedural_reach_in_orIn (p + l) C hC (Fin.castAdd l) (pointReach p l C)
  · intro w hw a ha
    simpa [pointReach, hw] using ha
  · intro j hj
    have hd := binary_wire_data (p + l) C hC (p + l + j) (by omega) (by omega)
    rw [pointReach]
    simp [show ¬ p + l + j < p + l by omega, hd.1, hd.2.1]

lemma circuit_palette_monochromatic (p l : ℕ) (C : Circuit) (hC : IsAO2 (p + l) C)
    (hT : tCount (p + l) C (fun i => decide (p ≤ i)) = 0) :
    ∀ w < p + l + C.gates.length,
      pointReach p l C w = ∅ ∨ lineReach p l C w = ∅ :=
  palette_disjoint_of_tCount p l C hC (pointReach p l C) (pointReach_in_orIn p l C hC) hT

end SafeLineSets.CircuitInterface

namespace DualSlots

variable {α β ι ε : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι] [DecidableEq ε]

lemma doubled_slot_card (M : Finset ε) (A : Finset ι)
    (L P : ε → ι × Bool)
    (hL : ∀ e ∈ M, (L e).1 ∈ A) (hP : ∀ e ∈ M, (P e).1 ∈ A)
    (hiL : Set.InjOn L (↑M : Set ε)) (hiP : Set.InjOn P (↑M : Set ε))
    (hdis : ∀ e ∈ M, ∀ f ∈ M, L e ≠ P f) : M.card ≤ A.card := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  classical
  have hcL : (M.image L).card = M.card := Finset.card_image_iff.mpr hiL
  have hcP : (M.image P).card = M.card := Finset.card_image_iff.mpr hiP
  have hd : Disjoint (M.image L) (M.image P) := by
    apply Finset.disjoint_left.mpr
    intro s hs ht
    obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hs
    obtain ⟨f,hf,hfq⟩ := Finset.mem_image.mp ht
    exact hdis e he f hf (heq.trans hfq.symm)
  have hsub : M.image L ∪ M.image P ⊆ A ×ˢ (Finset.univ : Finset Bool) := by
    intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_product.mpr ⟨hL e he,Finset.mem_univ _⟩
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_product.mpr ⟨hP e he,Finset.mem_univ _⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd,hcL,hcP,Finset.card_product] at hh
  have hb : (Finset.univ : Finset Bool).card = 2 := by decide
  rw [hb] at hh
  omega

lemma matching_card_le_and_of_dual_slots (E M : Finset (α × β)) (A : Finset ι)
    (pointReach : ι × Bool → Finset α) (lineReach : ι × Bool → Finset β)
    (L P : α × β → ι × Bool)
    (hE : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hl : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hr : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (hmono : ∀ s : ι × Bool, s.1 ∈ A → pointReach s = ∅ ∨ lineReach s = ∅)
    (hL : ∀ e ∈ M, (L e).1 ∈ A ∧ e.2 ∈ lineReach (L e) ∧
      ∀ b ∈ lineReach (L e), (e.1,b) ∈ E)
    (hP : ∀ e ∈ M, (P e).1 ∈ A ∧ e.1 ∈ pointReach (P e) ∧
      ∀ a ∈ pointReach (P e), (a,e.2) ∈ E) : M.card ≤ A.card := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  classical
  apply doubled_slot_card M A L P (fun e he => (hL e he).1) (fun e he => (hP e he).1)
  · intro e he f hf heq
    by_contra hn
    have ha : e.1 ≠ f.1 := fun h => hn (hl e he f hf h)
    have hb : e.2 ≠ f.2 := fun h => hn (hr e he f hf h)
    have hle := hL e he
    have hlf := hL f hf
    rw [← heq] at hlf
    exact hE e.1 f.1 e.2 f.2 ha hb
      ⟨hle.2.2 _ hle.2.1,hle.2.2 _ hlf.2.1,hlf.2.2 _ hle.2.1,hlf.2.2 _ hlf.2.1⟩
  · intro e he f hf heq
    by_contra hn
    have ha : e.1 ≠ f.1 := fun h => hn (hl e he f hf h)
    have hb : e.2 ≠ f.2 := fun h => hn (hr e he f hf h)
    have hpe := hP e he
    have hpf := hP f hf
    rw [← heq] at hpf
    exact hE e.1 f.1 e.2 f.2 ha hb
      ⟨hpe.2.2 _ hpe.2.1,hpf.2.2 _ hpe.2.1,hpe.2.2 _ hpf.2.1,hpf.2.2 _ hpf.2.1⟩
  · intro e he f hf heq
    have hle := hL e he
    have hpf := hP f hf
    rw [← heq] at hpf
    rcases hmono (L e) hle.1 with hp | hl'
    · rw [hp] at hpf
      exact Finset.notMem_empty _ hpf.2.1
    · rw [hl'] at hle
      exact Finset.notMem_empty _ hle.2.1

end DualSlots
namespace MatchingCharge.Konig

-- One side of a least cover is matched into the uncovered part of the other side (Hall).
lemma side {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (P : Finset α) (Q : Finset β)
    (hmin : ∀ (P' : Finset α) (Q' : Finset β), (∀ e ∈ E, e.1 ∈ P' ∨ e.2 ∈ Q') →
      P.card + Q.card ≤ P'.card + Q'.card)
    (hcov : ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) :
    ∃ f : {p // p ∈ P} → β, Function.Injective f ∧ ∀ p, (p.val, f p) ∈ E ∧ f p ∉ Q := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let t : {p // p ∈ P} → Finset β :=
    fun p => ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q
  have hall : ∀ S : Finset {p // p ∈ P}, S.card ≤ (S.biUnion t).card := by
    intro S
    have hsub : S.image Subtype.val ⊆ P := by
      intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      exact p.property
    have hc := hmin (P \ S.image Subtype.val) (Q ∪ S.biUnion t) (by
      intro e he
      rcases hcov e he with h | h
      · by_cases hS : e.1 ∈ S.image Subtype.val
        · right
          by_cases hq : e.2 ∈ Q
          · exact Finset.mem_union_left _ hq
          · apply Finset.mem_union_right
            obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hS
            rw [Finset.mem_biUnion]
            refine ⟨p, hp, ?_⟩
            show e.2 ∈ ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q
            rw [Finset.mem_sdiff]
            exact ⟨Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hpe.symm⟩, rfl⟩, hq⟩
        · left
          exact Finset.mem_sdiff.mpr ⟨h, hS⟩
      · right
        exact Finset.mem_union_left _ h)
    have h1 : (P \ S.image Subtype.val).card + (S.image Subtype.val).card = P.card :=
      Finset.card_sdiff_add_card_eq_card hsub
    have h2 : (S.image Subtype.val).card = S.card :=
      Finset.card_image_of_injective S Subtype.val_injective
    have h3 := Finset.card_union_le Q (S.biUnion t)
    omega
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  refine ⟨f, hinj, fun p => ?_⟩
  have := hf p
  have h' : f p ∈ ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q := this
  rw [Finset.mem_sdiff] at h'
  obtain ⟨e, he, hef⟩ := Finset.mem_image.mp h'.1
  obtain ⟨heE, hep⟩ := Finset.mem_filter.mp he
  refine ⟨?_, h'.2⟩
  have : e = (p.val, f p) := Prod.ext hep hef
  rw [← this]
  exact heE

lemma konig {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β)) :
    ∃ (M : Finset (α × β)) (P : Finset α) (Q : Finset β), M ⊆ E ∧
      (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧ (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e') ∧
      (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧ P.card + Q.card ≤ M.card := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  classical
  have hex : ∃ k : ℕ, ∃ (P : Finset α) (Q : Finset β),
      (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧ P.card + Q.card = k :=
    ⟨_, E.image Prod.fst, ∅, fun e he => Or.inl (Finset.mem_image_of_mem _ he), rfl⟩
  obtain ⟨P, Q, hcov, hk⟩ := Nat.find_spec hex
  have hmin : ∀ (P' : Finset α) (Q' : Finset β), (∀ e ∈ E, e.1 ∈ P' ∨ e.2 ∈ Q') →
      P.card + Q.card ≤ P'.card + Q'.card := by
    intro P' Q' h
    rw [hk]
    exact Nat.find_min' hex ⟨P', Q', h, rfl⟩
  obtain ⟨f, hfi, hf⟩ := side E P Q hmin hcov
  have hswap : ∀ (a : α) (b : β), (b, a) ∈ E.image Prod.swap ↔ (a, b) ∈ E := by
    intro a b
    constructor
    · intro h
      obtain ⟨e, he, hab⟩ := Finset.mem_image.mp h
      have : e = (a, b) := by
        rw [← Prod.swap_swap e, hab]; rfl
      rw [← this]; exact he
    · intro h
      exact Finset.mem_image.mpr ⟨(a, b), h, rfl⟩
  obtain ⟨g, hgi, hg⟩ := side (E.image Prod.swap) Q P (by
      intro Q' P' h
      have := hmin P' Q' (fun e he => by
        have := h (e.2, e.1) ((hswap e.1 e.2).mpr he)
        exact this.symm)
      omega) (by
      intro e he
      have h1 : (e.2, e.1) ∈ E := (hswap e.2 e.1).mp he
      exact (hcov _ h1).symm)
  have hg' : ∀ q : {q // q ∈ Q}, (g q, q.val) ∈ E ∧ g q ∉ P :=
    fun q => ⟨(hswap _ _).mp (hg q).1, (hg q).2⟩
  let M1 : Finset (α × β) := P.attach.image (fun p => (p.val, f p))
  let M2 : Finset (α × β) := Q.attach.image (fun q => (g q, q.val))
  have m1 : ∀ e ∈ M1, ∃ p : {p // p ∈ P}, e = (p.val, f p) := by
    intro e he
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp he
    exact ⟨p, hp.symm⟩
  have m2 : ∀ e ∈ M2, ∃ q : {q // q ∈ Q}, e = (g q, q.val) := by
    intro e he
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp he
    exact ⟨q, hq.symm⟩
  refine ⟨M1 ∪ M2, P, Q, ?_, ?_, ?_, hcov, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · obtain ⟨p, rfl⟩ := m1 e h
      exact (hf p).1
    · obtain ⟨q, rfl⟩ := m2 e h
      exact (hg' q).1
  · intro e he e' he' h
    rcases Finset.mem_union.mp he with h1 | h1 <;> rcases Finset.mem_union.mp he' with h2 | h2
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨p', rfl⟩ := m1 e' h2
      have : p = p' := Subtype.ext h
      rw [this]
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨q, rfl⟩ := m2 e' h2
      exfalso
      apply (hg' q).2
      have h' : p.val = g q := h
      rw [← h']
      exact p.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨p, rfl⟩ := m1 e' h2
      exfalso
      apply (hg' q).2
      have h' : g q = p.val := h
      rw [h']
      exact p.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨q', rfl⟩ := m2 e' h2
      have : q = q' := hgi h
      rw [this]
  · intro e he e' he' h
    rcases Finset.mem_union.mp he with h1 | h1 <;> rcases Finset.mem_union.mp he' with h2 | h2
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨p', rfl⟩ := m1 e' h2
      have : p = p' := hfi h
      rw [this]
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨q, rfl⟩ := m2 e' h2
      exfalso
      apply (hf p).2
      have h' : f p = q.val := h
      rw [h']
      exact q.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨p, rfl⟩ := m1 e' h2
      exfalso
      apply (hf p).2
      have h' : q.val = f p := h
      rw [← h']
      exact q.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨q', rfl⟩ := m2 e' h2
      have : q = q' := Subtype.ext h
      rw [this]
  · have hd : Disjoint M1 M2 := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨q, hq⟩ := m2 _ h2
      apply (hg' q).2
      have h' : p.val = g q := congrArg Prod.fst hq
      rw [← h']
      exact p.property
    have c1 : M1.card = P.card := by
      rw [Finset.card_image_of_injective _ (fun p p' h => Subtype.ext (congrArg Prod.fst h)),
        Finset.card_attach]
    have c2 : M2.card = Q.card := by
      rw [Finset.card_image_of_injective _ (fun q q' h => Subtype.ext (congrArg Prod.snd h)),
        Finset.card_attach]
    rw [Finset.card_union_of_disjoint hd, c1, c2]

end MatchingCharge.Konig

namespace DualSlots

lemma cover_card_le_and_of_dual_slots {ι : Type*} [DecidableEq ι]
    (p l : ℕ) (E : Finset (Fin p × Fin l)) (A : Finset ι)
    (pointReach : ι × Bool → Finset (Fin p)) (lineReach : ι × Bool → Finset (Fin l))
    (hE : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hmono : ∀ s : ι × Bool, s.1 ∈ A → pointReach s = ∅ ∨ lineReach s = ∅)
    (hL : ∀ a b, (a,b) ∈ E → ∃ s : ι × Bool, s.1 ∈ A ∧ b ∈ lineReach s ∧
      ∀ b' ∈ lineReach s, (a,b') ∈ E)
    (hP : ∀ a b, (a,b) ∈ E → ∃ s : ι × Bool, s.1 ∈ A ∧ a ∈ pointReach s ∧
      ∀ a' ∈ pointReach s, (a',b) ∈ E) :
    ∃ S : Finset (Fin (p+l)), S.card ≤ A.card ∧
      ∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  classical
  obtain ⟨M,U,V,hME,hl,hr,hcover,hcard⟩ :=
    PEqualNP.Outside.L_meta_4970_aux.MatchingCharge.Konig.konig E
  by_cases hm : M.Nonempty
  · obtain ⟨e,he⟩ := hm
    obtain ⟨s0,_,_,_⟩ := hL e.1 e.2 (hME he)
    have hcL : ∀ e : Fin p × Fin l, ∃ s : ι × Bool, e ∈ M →
        s.1 ∈ A ∧ e.2 ∈ lineReach s ∧ ∀ b ∈ lineReach s, (e.1,b) ∈ E := by
      intro e
      by_cases he : e ∈ M
      · obtain ⟨s,hs⟩ := hL e.1 e.2 (hME he)
        exact ⟨s,fun _ => hs⟩
      · exact ⟨s0,fun hh => False.elim (he hh)⟩
    have hcP : ∀ e : Fin p × Fin l, ∃ s : ι × Bool, e ∈ M →
        s.1 ∈ A ∧ e.1 ∈ pointReach s ∧ ∀ a ∈ pointReach s, (a,e.2) ∈ E := by
      intro e
      by_cases he : e ∈ M
      · obtain ⟨s,hs⟩ := hP e.1 e.2 (hME he)
        exact ⟨s,fun _ => hs⟩
      · exact ⟨s0,fun hh => False.elim (he hh)⟩
    choose L hL' using hcL
    choose P hP' using hcP
    have hbound := matching_card_le_and_of_dual_slots E M A pointReach lineReach L P
      hE hl hr hmono hL' hP'
    let S : Finset (Fin (p+l)) := U.image (Fin.castAdd l) ∪ V.image (Fin.natAdd p)
    refine ⟨S,?_,?_⟩
    · have hs : S.card ≤ U.card + V.card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
      omega
    · intro a b hab
      rcases hcover (a,b) hab with ha | hb
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb))
  · have hm0 : M = ∅ := Finset.not_nonempty_iff_eq_empty.mp hm
    have hu0 : U = ∅ := Finset.card_eq_zero.mp (by simpa [hm0] using Nat.le_trans (Nat.le_add_right U.card V.card) hcard)
    have hv0 : V = ∅ := Finset.card_eq_zero.mp (by simpa [hm0] using Nat.le_trans (Nat.le_add_left V.card U.card) hcard)
    refine ⟨∅,by simp,?_⟩
    intro a b hab
    have hh := hcover (a,b) hab
    simp [hu0,hv0] at hh

end DualSlots

namespace SafeLineSets.CircuitInterface

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def dualChild (p l : ℕ) (C : Circuit) (s : ℕ × Bool) : ℕ :=
  if s.2 then rightWire (p+l) C s.1 else leftWire (p+l) C s.1

lemma graph_circuit_and_cover_of_palette_mono (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : IsAO2 (p+l) C)
    (hE : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hf : ∀ x, wireFn (p+l) C C.output x =
      decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hmono : ∀ w < p+l+C.gates.length,
      pointReach p l C w = ∅ ∨ lineReach p l C w = ∅) :
    ∃ S : Finset (Fin (p+l)), S.card ≤ (andWires (p+l) C).card ∧
      ∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  apply PEqualNP.Outside.L_meta_4970_aux.DualSlots.cover_card_le_and_of_dual_slots
    p l E (andWires (p+l) C) (fun s => pointReach p l C (dualChild p l C s))
    (fun s => lineReach p l C (dualChild p l C s)) hE
  · intro s hs
    have hbound := Finset.mem_filter.mp hs
    have hbounds := Finset.mem_Ico.mp hbound.1
    have hd := binary_wire_data (p+l) C hC s.1 hbounds.1 hbounds.2
    apply hmono
    cases hh : s.2 <;> simp [dualChild,hh] <;> omega
  · intro a b hab
    obtain ⟨w,hw,hh⟩ := graph_circuit_slot_cover p l E C hC hf a b hab
    rcases hh with hh | hh
    · exact ⟨(w,false),hw,by simpa [dualChild] using hh⟩
    · exact ⟨(w,true),hw,by simpa [dualChild] using hh⟩
  · intro a b hab
    obtain ⟨w,hw,_,hh⟩ := graph_circuit_point_slot_cover_strong p l E C hC hf a b hab
    rcases hh with hh | hh
    · exact ⟨(w,false),hw,by simpa [dualChild] using And.intro hh.1 hh.2.1⟩
    · exact ⟨(w,true),hw,by simpa [dualChild] using And.intro hh.1 hh.2.1⟩

end SafeLineSets.CircuitInterface

namespace SafeLineSets.CircuitInterface

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma graph_circuit_and_cover_tCount_zero (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : IsAO2 (p+l) C)
    (hE : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hf : ∀ x, PEqualNP.MetaComplexity.circuitFun (p+l) C x =
      decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hT : PEqualNP.TwoColour.tCount (p+l) C (fun i => decide (p ≤ i)) = 0) :
    ∃ S : Finset (Fin (p+l)), S.card ≤ (andWires (p+l) C).card ∧
      ∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  exact graph_circuit_and_cover_of_palette_mono p l E C hC hE hf
    (circuit_palette_monochromatic p l C hC hT)

end SafeLineSets.CircuitInterface

namespace SafeLineSets.CircuitInterface

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def orWires (n : ℕ) (C : Circuit) : Finset ℕ := by
  letI : DecidableEq GateOp := gateOpDecEq
  exact (Finset.Ico n (n+C.gates.length)).filter fun w => (gateAt C (w-n)).op = GateOp.or

lemma and_or_card_size (n : ℕ) (C : Circuit) (hC : IsAO2 n C) :
    (andWires n C).card + (orWires n C).card = C.size := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  have hu : andWires n C ∪ orWires n C = Finset.Ico n (n+C.gates.length) := by
    ext w
    simp only [andWires,orWires,Finset.mem_union,Finset.mem_filter]
    constructor
    · intro h
      exact h.elim And.left And.left
    · intro h
      have hh := Finset.mem_Ico.mp h
      have hd := binary_wire_data n C hC w hh.1 hh.2
      exact hd.2.2.1.elim (fun ha => Or.inl ⟨h,ha⟩) (fun ho => Or.inr ⟨h,ho⟩)
  have hd : Disjoint (andWires n C) (orWires n C) := by
    apply Finset.disjoint_left.mpr
    intro w ha ho
    have ha' := (Finset.mem_filter.mp ha).2
    have ho' := (Finset.mem_filter.mp ho).2
    have hh : GateOp.and = GateOp.or := ha'.symm.trans ho'
    cases hh
  have hh := congrArg Finset.card hu
  rw [Finset.card_union_of_disjoint hd,Nat.card_Ico] at hh
  simpa [Circuit.size] using hh

lemma full_bound_of_or_count (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hC : IsAO2 (p+l) C)
    (hE : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hf : ∀ x, PEqualNP.MetaComplexity.circuitFun (p+l) C x =
      decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hT : PEqualNP.TwoColour.tCount (p+l) C (fun i => decide (p ≤ i)) = 0)
    (hOR : E.card ≤ (orWires (p+l) C).card + 1) :
    ∃ S : Finset (Fin (p+l)),
      (∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  obtain ⟨S,hs,hcover⟩ := graph_circuit_and_cover_tCount_zero p l E C hC hE hf hT
  have hsize := and_or_card_size (p+l) C hC
  exact ⟨S,hcover,by omega⟩

end SafeLineSets.CircuitInterface

end PEqualNP.Outside.L_meta_4970_aux
