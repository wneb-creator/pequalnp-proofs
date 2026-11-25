import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.PruningTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour PEqualNP.Outside.L_meta_4675.Pruning
  PEqualNP.Outside.L_meta_4675.OrReachAPI

def AliasReach (n : ℕ) (C : Circuit) (gs : List Gate) (o : Option ℕ) (i : ℕ) : Prop :=
  ∀ w, o = some w → orIn n ⟨gs, 0⟩ w ⊆ orIn n C i

def ReachValid (n : ℕ) (C : Circuit) (s : List Gate × List (Option ℕ)) : Prop :=
  ∀ i, AliasReach n C s.1 (s.2.getD i none) i

def OrTrace (n : ℕ) (C : Circuit) (gs : List Gate) : Prop :=
  ∀ g < gs.length, (gateAt ⟨gs, 0⟩ g).op = GateOp.or →
    ∃ h < C.gates.length, (gateAt C h).op = GateOp.or ∧
      orIn n ⟨gs, 0⟩ (n + g) ⊆ orIn n C (n + h)

lemma emitPair_reach_prior (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (w : ℕ) (hw : w < n + gs.length) :
    orIn n ⟨(emitPair n gs a x y).1, 0⟩ w = orIn n ⟨gs, 0⟩ w := by
  cases x <;> cases y <;> simp only [emitPair]
  exact orIn_append_prefix n gs [_] w hw

lemma emitPair_alias_prior (n : ℕ) (C : Circuit) (gs : List Gate) (a : Bool) (x y o : Option ℕ)
    (i : ℕ) (ho : Bounded n gs o) (ha : AliasReach n C gs o i) :
    AliasReach n C (emitPair n gs a x y).1 o i := by
  intro w hw
  rw [emitPair_reach_prior n gs a x y w (ho w hw)]
  exact ha w hw

lemma emitPair_output_reach (n : ℕ) (C : Circuit) (gs : List Gate) (hAO : IsAO2 n ⟨gs, 0⟩)
    (a : Bool) (x y : Option ℕ) (hx : Bounded n gs x) (hy : Bounded n gs y)
    (i j k : ℕ) (hxi : AliasReach n C gs x i) (hyj : AliasReach n C gs y j)
    (hr : orIn n C k = if a then ∅ else orIn n C i ∪ orIn n C j) :
    AliasReach n C (emitPair n gs a x y).1 (emitPair n gs a x y).2 k := by
  cases x with
  | none =>
    cases y with
    | none => simp [AliasReach, emitPair]
    | some v =>
      cases a
      · intro w hw
        have he : v = w := by simpa [emitPair] using hw
        subst w
        rw [hr]
        exact (hyj v rfl).trans Finset.subset_union_right
      · simp [AliasReach, emitPair]
  | some u =>
    cases y with
    | none =>
      cases a
      · intro w hw
        have he : u = w := by simpa [emitPair] using hw
        subst w
        rw [hr]
        exact (hxi u rfl).trans Finset.subset_union_left
      · simp [AliasReach, emitPair]
    | some v =>
      intro w hw
      have he : n + gs.length = w := by simpa [emitPair] using hw
      subst w
      have hu : u < n + gs.length := hx u rfl
      have hv : v < n + gs.length := hy v rfl
      have hao := append_pair_ao n gs hAO a u v hu hv
      change orIn n ⟨gs ++ [pairGate a u v], 0⟩ (n + gs.length) ⊆ _
      cases a with
      | false =>
        rw [orIn_or_pair n _ gs.length u v (by simp) (by rw [gateAt_snoc_last]; rfl)
          (by rw [gateAt_snoc_last]; rfl) hao.2.1]
        rw [orIn_append_prefix n gs [_] u hu, orIn_append_prefix n gs [_] v hv, hr]
        exact Finset.union_subset_union (hxi u rfl) (hyj v rfl)
      | true =>
        rw [orIn_non_or n _ gs.length (by simp) (by rw [gateAt_snoc_last]; simp [pairGate])]
        exact Finset.empty_subset _

lemma emitPair_trace (n : ℕ) (C : Circuit) (gs : List Gate) (hAO : IsAO2 n ⟨gs, 0⟩)
    (ht : OrTrace n C gs) (a : Bool) (x y : Option ℕ) (hx : Bounded n gs x) (hy : Bounded n gs y)
    (i j k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = if a then GateOp.and else GateOp.or)
    (hxi : AliasReach n C gs x i) (hyj : AliasReach n C gs y j)
    (hr : orIn n C (n + k) = if a then ∅ else orIn n C i ∪ orIn n C j) :
    OrTrace n C (emitPair n gs a x y).1 := by
  cases x with
  | none => cases y <;> exact ht
  | some u =>
    cases y with
    | none => exact ht
    | some v =>
      intro g hg hgo
      change g < (gs ++ [pairGate a u v]).length at hg
      change (gateAt ⟨gs ++ [pairGate a u v], 0⟩ g).op = GateOp.or at hgo
      by_cases hgold : g < gs.length
      · rw [gateAt_snoc_old gs _ g hgold] at hgo
        obtain ⟨h, hh, hho, hsub⟩ := ht g hgold hgo
        refine ⟨h, hh, hho, ?_⟩
        change orIn n ⟨gs ++ [pairGate a u v], 0⟩ (n + g) ⊆ _
        rw [orIn_append_prefix n gs [_] (n + g) (by omega)]
        exact hsub
      · have hge : g = gs.length := by simp only [List.length_append, List.length_cons, List.length_nil] at hg; omega
        subst g
        rw [gateAt_snoc_last] at hgo
        have ha : a = false := by cases a <;> simp_all [pairGate]
        refine ⟨k, hk, by simpa [ha] using hop, ?_⟩
        exact emitPair_output_reach n C gs hAO a (some u) (some v) hx hy i j (n + k) hxi hyj hr
          (n + gs.length) rfl

lemma alias_extend (n : ℕ) (C : Circuit) (gs : List Gate) (m : List (Option ℕ)) (o : Option ℕ)
    (hprior : ∀ i, AliasReach n C gs (m.getD i none) i)
    (hlast : AliasReach n C gs o m.length) : ReachValid n C (gs, m ++ [o]) := by
  intro i w hw
  change (m ++ [o]).getD i none = some w at hw
  change orIn n ⟨gs, 0⟩ w ⊆ orIn n C i
  rcases Nat.lt_trichotomy i m.length with hi | hi | hi
  · rw [getD_append_lt m [o] i none hi] at hw
    exact hprior i w hw
  · subst i
    rw [getD_append_last] at hw
    exact hlast w hw
  · rw [getD_ge _ _ _ (by simp; omega)] at hw
    cases hw

lemma gateAt_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k ∈ C.gates := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma original_pair_reach (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) :
    orIn n C (n + k) = if isAnd (gateAt C k).op then ∅ else
      orIn n C ((gateAt C k).inputs.getD 0 0) ∪ orIn n C ((gateAt C k).inputs.getD 1 0) := by
  have hm := gateAt_mem C k hk
  have hlen := hAO.2.2 (gateAt C k) hm
  obtain ⟨i, j, hij⟩ := List.length_eq_two.mp hlen
  rcases hAO.1 (gateAt C k) hm with hop | hop
  · simp only [hop, isAnd, ↓reduceIte]
    exact orIn_non_or n C k hk (by rw [hop]; intro he; cases he)
  · simp only [hop, isAnd, hij, List.getD_cons_zero, List.getD_cons_succ]
    exact orIn_or_pair n C k i j hk hop hij hAO.2.1

lemma original_gate_kind (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) :
    (gateAt C k).op = if isAnd (gateAt C k).op then GateOp.and else GateOp.or := by
  rcases hAO.1 (gateAt C k) (gateAt_mem C k hk) with hop | hop <;> simp [hop, isAnd]

lemma compileStep_reaches (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (s : List Gate × List (Option ℕ)) (hs : Valid n s) (hr : ReachValid n C s)
    (ht : OrTrace n C s.1) (hl : s.2.length = n + j) :
    ReachValid n C (compileStep n q s (gateAt C j)) ∧
      OrTrace n C (compileStep n q s (gateAt C j)).1 := by
  have hx := bounded_getD n s hs.2 ((gateAt C j).inputs.getD 0 0)
  have hy := bounded_getD n s hs.2 ((gateAt C j).inputs.getD 1 0)
  have hpair := original_pair_reach n C hAO j hj
  unfold compileStep
  split_ifs <;> dsimp only
  · refine ⟨alias_extend n C s.1 s.2 none hr ?_, ht⟩
    simp [AliasReach]
  · constructor
    · apply alias_extend
      · intro i
        exact emitPair_alias_prior n C s.1 _ _ _ (s.2.getD i none) i
          (bounded_getD n s hs.2 i) (hr i)
      · rw [hl]
        exact emitPair_output_reach n C s.1 hs.1 _ _ _ hx hy _ _ (n + j) (hr _) (hr _) hpair
    · exact emitPair_trace n C s.1 hs.1 ht _ _ _ hx hy _ _ j hj
        (original_gate_kind n C hAO j hj) (hr _) (hr _) hpair

lemma initial_reaches (n : ℕ) (C : Circuit) : ReachValid n C (initial n) ∧ OrTrace n C (initial n).1 := by
  constructor
  · intro i w hw
    by_cases hi : i < n
    · have hget : (initial n).2.getD i none = some i := by
        simp [initial, List.getD_eq_getElem?_getD, hi]
      rw [hget] at hw
      have he : i = w := Option.some.inj hw
      subst w
      change orIn n ⟨[], 0⟩ i ⊆ orIn n C i
      rw [orIn_input n _ i hi, orIn_input n C i hi]
    · have hget : (initial n).2.getD i none = none := by
        simp [initial, List.getD_eq_getElem?_getD, hi]
      rw [hget] at hw
      cases hw
  · intro g hg
    simp [initial] at hg

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma compiled_reaches (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ReachValid n C (compiled n q C.gates) ∧ OrTrace n C (compiled n q C.gates).1 := by
  have h : ∀ j, j ≤ C.gates.length →
      Valid n (compiled n q (C.gates.take j)) ∧
      ReachValid n C (compiled n q (C.gates.take j)) ∧
      OrTrace n C (compiled n q (C.gates.take j)).1 := by
    intro j
    induction j with
    | zero =>
      intro hj
      simpa [compiled] using (show Valid n (initial n) ∧ ReachValid n C (initial n) ∧
        OrTrace n C (initial n).1 from ⟨initial_valid n, initial_reaches n C⟩)
    | succ j ih =>
      intro hj
      obtain ⟨hv, hr, ht⟩ := ih (by omega)
      have hlt : j < C.gates.length := by omega
      rw [compiled_take_succ n q C.gates j hlt, ← gateAt_eq_getElem C j hlt]
      refine ⟨compileStep_valid n q _ (gateAt C j) hv, ?_⟩
      apply compileStep_reaches n q C hAO j hlt _ hv hr ht
      rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
  simpa using (h C.gates.length le_rfl).2

lemma trace_count_zero (n : ℕ) (C : Circuit) (gs : List Gate) (s : ℕ → Bool)
    (ht : OrTrace n C gs) (hz : tCount n C s = 0) : tCount n ⟨gs, 0⟩ s = 0 := by
  have he : twoColour n C s = ∅ := Finset.card_eq_zero.mp hz
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have htwo : IsTwoColour n ⟨gs, 0⟩ s g := (Finset.mem_filter.mp hg).2
  obtain ⟨h, hh, hop, hsub⟩ := ht g htwo.1 htwo.2.1
  have hold : IsTwoColour n C s h := by
    refine ⟨hh, hop, ?_, ?_⟩
    · obtain ⟨i, hi, hsi⟩ := htwo.2.2.1
      exact ⟨i, hsub hi, hsi⟩
    · obtain ⟨i, hi, hsi⟩ := htwo.2.2.2
      exact ⟨i, hsub hi, hsi⟩
  have hm : h ∈ twoColour n C s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hold⟩
  rw [he] at hm
  simp at hm

lemma pruned_count_zero (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) (s : ℕ → Bool)
    (hz : tCount n C s = 0) : tCount n (pruned n q C) s = 0 := by
  exact trace_count_zero n C (compiled n q C.gates).1 s (compiled_reaches n q C hAO).2 hz

end PEqualNP.Outside.L_meta_4675.PruningTrace
