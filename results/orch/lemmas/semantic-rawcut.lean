import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.SemanticRawCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _


def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L


def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}


def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

lemma agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

lemma agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]


def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

lemma cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

lemma essential_card_le (n : ℕ) (C : Circuit) (T : Finset (Fin n))
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool,
      circuitFun n C (Function.update x i (!x i)) ≠ circuitFun n C x) :
    T.card ≤ C.size + 1 := by
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hsub : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hlen cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  exact le_trans (Finset.card_le_card hsub) hc

structure RawState (n : ℕ) where
  ann : List (Finset (Fin n) × Bool)
  roots : Finset ℕ
  pureGates : ℕ
  mixedGates : ℕ

def rawSupp (s : RawState n) (w : ℕ) := (s.ann.getD w (∅, false)).1

def hasPayload (s : RawState n) (w : ℕ) := (s.ann.getD w (∅, false)).2

def pureSupps (s : RawState n) :=
  s.ann.map fun a => if a.2 then ∅ else a.1

lemma pureSupps_getD (s : RawState n) (w : ℕ) :
    (pureSupps s).getD w ∅ = if hasPayload s w then ∅ else rawSupp s w := by
  simp [pureSupps, hasPayload, rawSupp, List.getD_eq_getElem?_getD]
  cases s.ann[w]? <;> rfl

def RawInv (s : RawState n) : Prop :=
  Cnt s.pureGates (pureSupps s) ∧ s.roots.card ≤ s.mixedGates ∧
    (∀ w ∈ s.roots, w < s.ann.length) ∧
    ∀ w, rawSupp s w ⊆ (pureSupps s).getD w ∅ ∪
      s.roots.biUnion (fun z => (pureSupps s).getD z ∅)

def boundary (s : RawState n) (p q : ℕ) : Finset ℕ :=
  if hasPayload s p then (if hasPayload s q then ∅ else {q})
  else (if hasPayload s q then {p} else ∅)

def rawStep (s : RawState n) (g : ℕ × ℕ) : RawState n where
  ann := s.ann ++ [(rawSupp s g.1 ∪ rawSupp s g.2, hasPayload s g.1 || hasPayload s g.2)]
  roots := s.roots ∪ boundary s g.1 g.2
  pureGates := s.pureGates + if hasPayload s g.1 || hasPayload s g.2 then 0 else 1
  mixedGates := s.mixedGates + if hasPayload s g.1 = hasPayload s g.2 then 0 else 1

lemma cnt_append_empty (t : ℕ) (L : List (Finset (Fin n))) (h : Cnt t L) :
    Cnt t (L ++ [∅]) := by
  intro W
  have he : ∀ w, (L ++ [∅]).getD w ∅ = L.getD w ∅ := by
    intro w
    by_cases hw : w = L.length
    · subst w
      rw [getD_snoc_eq, List.getD_eq_default _ _ (by omega)]
    · exact getD_snoc_ne L ∅ ∅ w hw
  simpa only [he] using h W

lemma cnt_append_union (t : ℕ) (L : List (Finset (Fin n))) (p q : ℕ) (h : Cnt t L) :
    Cnt (t + 1) (L ++ [L.getD p ∅ ∪ L.getD q ∅]) := by
  simpa [gateSupp] using cnt_step t L ⟨GateOp.or, [p, q]⟩ (by simp) h

lemma step_proj_old (s : RawState n) (p q w : ℕ) (hw : w < s.ann.length) :
    (pureSupps (rawStep s (p, q))).getD w ∅ = (pureSupps s).getD w ∅ := by
  simp only [pureSupps, rawStep, List.map_append, List.map_cons, List.map_nil]
  exact List.getD_append _ _ _ _ (by simpa using hw)

lemma raw_step_inv (s : RawState n) (p q : ℕ)
    (hp : p < s.ann.length) (hq : q < s.ann.length) (hs : RawInv s) :
    RawInv (rawStep s (p, q)) := by
  obtain ⟨hcnt, hcard, hroots, hcover⟩ := hs
  have hB : ∀ w ∈ boundary s p q, w < s.ann.length := by
    intro w hw
    unfold boundary at hw
    split_ifs at hw <;> simp_all
  have hroot : ∀ w ∈ (rawStep s (p, q)).roots, w < s.ann.length := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact hroots w hw
    · exact hB w hw
  have hmono : s.roots.biUnion (fun z => (pureSupps s).getD z ∅) ⊆
      (rawStep s (p, q)).roots.biUnion (fun z => (pureSupps (rawStep s (p, q))).getD z ∅) := by
    intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
    apply Finset.mem_biUnion.mpr
    refine ⟨w, Finset.mem_union_left _ hw, ?_⟩
    rwa [step_proj_old s p q w (hroots w hw)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hP : hasPayload s p <;> cases hQ : hasPayload s q
    · have hc := cnt_append_union s.pureGates (pureSupps s) p q hcnt
      rw [pureSupps_getD, pureSupps_getD, hP, hQ] at hc
      simpa [rawStep, pureSupps, hP, hQ] using hc
    · simpa [rawStep, pureSupps, hP, hQ] using cnt_append_empty s.pureGates (pureSupps s) hcnt
    · simpa [rawStep, pureSupps, hP, hQ] using cnt_append_empty s.pureGates (pureSupps s) hcnt
    · simpa [rawStep, pureSupps, hP, hQ] using cnt_append_empty s.pureGates (pureSupps s) hcnt
  · have hu := Finset.card_union_le s.roots (boundary s p q)
    cases hP : hasPayload s p <;> cases hQ : hasPayload s q <;>
      simp [rawStep, boundary, hP, hQ] at * <;> omega
  · intro w hw
    have := hroot w hw
    simp only [rawStep, List.length_append, List.length_singleton]
    omega
  · intro w
    by_cases hw : w = s.ann.length
    · subst w
      have heS : rawSupp (rawStep s (p, q)) s.ann.length = rawSupp s p ∪ rawSupp s q := by
        simp [rawSupp, rawStep]
      have heQ : (pureSupps (rawStep s (p, q))).getD s.ann.length ∅ =
          if hasPayload s p || hasPayload s q then ∅ else rawSupp s p ∪ rawSupp s q := by
        simp [pureSupps, rawStep]
      have hboundary (z : ℕ) (hz : z ∈ boundary s p q) : rawSupp s z ⊆
          (rawStep s (p, q)).roots.biUnion (fun u => (pureSupps (rawStep s (p, q))).getD u ∅) := by
        intro i hi
        rcases Finset.mem_union.mp (hcover z hi) with hc | hc
        · apply Finset.mem_biUnion.mpr
          refine ⟨z, Finset.mem_union_right _ hz, ?_⟩
          rwa [step_proj_old s p q z (hB z hz)]
        · exact hmono hc
      have hpayload (z : ℕ) (hz : hasPayload s z = true) : rawSupp s z ⊆
          (rawStep s (p, q)).roots.biUnion (fun u => (pureSupps (rawStep s (p, q))).getD u ∅) := by
        intro i hi
        rcases Finset.mem_union.mp (hcover z hi) with hc | hc
        · rw [pureSupps_getD, hz] at hc
          simp at hc
        · exact hmono hc
      rw [heS, heQ]
      cases hP : hasPayload s p <;> cases hQ : hasPayload s q
      · exact Finset.subset_union_left
      · change rawSupp s p ∪ rawSupp s q ⊆ ∅ ∪ _
        rw [Finset.empty_union]
        exact Finset.union_subset (hboundary p (by simp [boundary, hP, hQ])) (hpayload q hQ)
      · change rawSupp s p ∪ rawSupp s q ⊆ ∅ ∪ _
        rw [Finset.empty_union]
        exact Finset.union_subset (hpayload p hP) (hboundary q (by simp [boundary, hP, hQ]))
      · change rawSupp s p ∪ rawSupp s q ⊆ ∅ ∪ _
        rw [Finset.empty_union]
        exact Finset.union_subset (hpayload p hP) (hpayload q hQ)
    · have heS : rawSupp (rawStep s (p, q)) w = rawSupp s w := by
        unfold rawSupp rawStep
        rw [getD_snoc_ne _ _ _ _ hw]
      have heQ : (pureSupps (rawStep s (p, q))).getD w ∅ = (pureSupps s).getD w ∅ := by
        unfold pureSupps rawStep
        simp only [List.map_append, List.map_cons, List.map_nil]
        exact getD_snoc_ne _ _ _ _ (by simpa using hw)
      rw [heS, heQ]
      exact (hcover w).trans (Finset.union_subset_union (Finset.Subset.refl _) hmono)

lemma raw_cut_bound (s : RawState n) (hs : RawInv s) (outs : Finset ℕ) (T : Finset (Fin n))
    (hcover : T ⊆ outs.biUnion (rawSupp s)) :
    T.card ≤ s.pureGates + s.mixedGates +
      (outs.filter fun w => hasPayload s w = false).card := by
  let W := s.roots ∪ outs.filter fun w => hasPayload s w = false
  have hsub : T ⊆ W.biUnion fun w => (pureSupps s).getD w ∅ := by
    intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp (hcover hi)
    rcases Finset.mem_union.mp (hs.2.2.2 w hiw) with hp | hp
    · apply Finset.mem_biUnion.mpr
      refine ⟨w, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, ?_⟩), hp⟩
      cases hP : hasPayload s w
      · rfl
      · rw [pureSupps_getD, hP] at hp
        simp at hp
    · obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp hp
      exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_union_left _ hz, hiz⟩
  have hcnt := hs.1 W
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le s.roots (outs.filter fun w => hasPayload s w = false)
  have hr := hs.2.1
  dsimp [W] at hcnt hc
  omega

end PEqualNP.Outside.L_meta_4675.SemanticRawCut
