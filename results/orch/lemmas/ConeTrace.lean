import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.ConeTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_meta_4675.Pruning
  PEqualNP.Outside.L_meta_4675.ConeAPI

def AliasCone (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ → ℕ)
    (a : Option ℕ) (i : ℕ) : Prop :=
  ∀ w, a = some w → ∀ k < gs.length, WireCone n ⟨gs, 0⟩ w k → WireCone n C i (o k)

def GateTrace (n : ℕ) (C : Circuit) (j : ℕ)
    (s : List Gate × List (Option ℕ)) (o : ℕ → ℕ) : Prop :=
  (∀ k < s.1.length, o k < j) ∧
  (∀ a b, a < b → b < s.1.length → o a < o b) ∧
  (∀ k < s.1.length, (gateAt ⟨s.1, 0⟩ k).op = (gateAt C (o k)).op) ∧
  (∀ k < s.1.length, s.2.getD (n + o k) none = some (n + k)) ∧
  (∀ i, AliasCone n C s.1 o (s.2.getD i none) i)

lemma alias_none (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ → ℕ) (i : ℕ) :
    AliasCone n C gs o none i := by
  intro w hw
  cases hw

lemma alias_parent (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ → ℕ) (a : Option ℕ)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i ∈ (gateAt C j).inputs)
    (hib : i < n + j) (ha : AliasCone n C gs o a i) : AliasCone n C gs o a (n + j) := by
  intro w hw k hk hcone
  exact wireCone_of_input n C j hj i hi hib _ (ha w hw k hk hcone)

lemma alias_lookup_append (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ → ℕ)
    (m : List (Option ℕ)) (a : Option ℕ)
    (hprior : ∀ i, AliasCone n C gs o (m.getD i none) i)
    (hlast : AliasCone n C gs o a m.length) :
    ∀ i, AliasCone n C gs o ((m ++ [a]).getD i none) i := by
  intro i
  rcases Nat.lt_trichotomy i m.length with hi | hi | hi
  · rw [getD_append_lt m [a] i none hi]
    exact hprior i
  · subst i
    rw [getD_append_last]
    exact hlast
  · rw [getD_ge _ _ _ (by simp; omega)]
    exact alias_none n C gs o i

lemma trace_drop (n : ℕ) (C : Circuit) (j : ℕ) (s : List Gate × List (Option ℕ))
    (o : ℕ → ℕ) (ht : GateTrace n C j s o) (hl : s.2.length = n + j)
    (a : Option ℕ) (ha : AliasCone n C s.1 o a (n + j)) :
    GateTrace n C (j + 1) (s.1, s.2 ++ [a]) o := by
  refine ⟨fun k hk => Nat.lt_succ_of_lt (ht.1 k hk), ht.2.1, ht.2.2.1, ?_, ?_⟩
  · intro k hk
    rw [getD_append_lt s.2 [a] (n + o k) none (by rw [hl]; have := ht.1 k hk; omega)]
    exact ht.2.2.2.1 k hk
  · apply alias_lookup_append n C s.1 o s.2 a ht.2.2.2.2
    rwa [hl]

def extendOrigin (o : ℕ → ℕ) (N j k : ℕ) : ℕ := if k < N then o k else j

lemma alias_append_gate (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ → ℕ)
    (j : ℕ) (g : Gate) (a : Option ℕ) (i : ℕ) (ha : Bounded n gs a)
    (hc : AliasCone n C gs o a i) :
    AliasCone n C (gs ++ [g]) (extendOrigin o gs.length j) a i := by
  intro w hw k hk hcone
  have hwb := ha w hw
  have hkb := wireCone_bound n ⟨gs ++ [g], 0⟩ w k hcone
  have hko : k < gs.length := by omega
  have hold := (wireCone_append_prefix n gs [g] w hwb k).mp hcone
  simpa [extendOrigin, hko] using hc w hw k hko hold

lemma alias_emitted (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ → ℕ)
    (j a b u v : ℕ) (hj : j < C.gates.length) (hinputs : (gateAt C j).inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j) (hu : u < n + gs.length) (hv : v < n + gs.length)
    (hca : AliasCone n C gs o (some u) a) (hcb : AliasCone n C gs o (some v) b)
    (isA : Bool) :
    AliasCone n C (gs ++ [pairGate isA u v]) (extendOrigin o gs.length j)
      (some (n + gs.length)) (n + j) := by
  intro w hw k hk hcone
  have hwe : w = n + gs.length := (Option.some.inj hw).symm
  subst w
  have hc := (wireCone_gate_iff n ⟨gs ++ [pairGate isA u v], 0⟩ gs.length
    (by simp) k).mp hcone
  rcases hc with rfl | ⟨z, hz, hzb, hzc⟩
  · simp only [extendOrigin, lt_self_iff_false, ↓reduceIte]
    exact Or.inl rfl
  · have hzmem : z = u ∨ z = v := by
      rw [gateAt_snoc_last] at hz
      simpa [pairGate] using hz
    have hko : k < gs.length := by
      have hbound := wireCone_bound n ⟨gs ++ [pairGate isA u v], 0⟩ z k hzc
      omega
    simp only [extendOrigin, hko, ↓reduceIte]
    rcases hzmem with hzu | hzv
    · subst z
      have hco := (wireCone_append_prefix n gs [_] u hu k).mp hzc
      exact wireCone_of_input n C j hj a (by simp [hinputs]) ha _ (hca u rfl k hko hco)
    · subst z
      have hco := (wireCone_append_prefix n gs [_] v hv k).mp hzc
      exact wireCone_of_input n C j hj b (by simp [hinputs]) hb _ (hcb v rfl k hko hco)

lemma trace_emit (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (s : List Gate × List (Option ℕ)) (o : ℕ → ℕ) (ht : GateTrace n C j s o)
    (hvld : Valid n s) (hl : s.2.length = n + j)
    (a b u v : ℕ) (hinputs : (gateAt C j).inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j)
    (hua : s.2.getD a none = some u) (hvb : s.2.getD b none = some v)
    (hop : (pairGate (isAnd (gateAt C j).op) u v).op = (gateAt C j).op) :
    GateTrace n C (j + 1)
      (s.1 ++ [pairGate (isAnd (gateAt C j).op) u v], s.2 ++ [some (n + s.1.length)])
      (extendOrigin o s.1.length j) := by
  have hu := bounded_getD n s hvld.2 a u hua
  have hv := bounded_getD n s hvld.2 b v hvb
  have hlen : (s.1 ++ [pairGate (isAnd (gateAt C j).op) u v]).length = s.1.length + 1 := by simp
  have hsplit : ∀ k < (s.1 ++ [pairGate (isAnd (gateAt C j).op) u v]).length,
      k < s.1.length ∨ k = s.1.length := by intro k hk; rw [hlen] at hk; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases hsplit k hk with hk | rfl
    · simp only [extendOrigin, hk, ↓reduceIte]
      exact Nat.lt_succ_of_lt (ht.1 k hk)
    · simp [extendOrigin]
  · intro r t hrt htlen
    rcases hsplit t htlen with hto | rfl
    · have hro : r < s.1.length := by omega
      simp only [extendOrigin, hro, hto, ↓reduceIte]
      exact ht.2.1 r t hrt hto
    · simp only [extendOrigin, hrt, lt_self_iff_false, ↓reduceIte]
      exact ht.1 r hrt
  · intro k hk
    rcases hsplit k hk with hk | rfl
    · rw [gateAt_snoc_old s.1 _ k hk]
      simp only [extendOrigin, hk, ↓reduceIte]
      exact ht.2.2.1 k hk
    · rw [gateAt_snoc_last]
      simpa [extendOrigin] using hop
  · intro k hk
    rcases hsplit k hk with hk | rfl
    · simp only [extendOrigin, hk, ↓reduceIte]
      rw [getD_append_lt s.2 [_] _ none (by rw [hl]; have := ht.1 k hk; omega)]
      exact ht.2.2.2.1 k hk
    · simp only [extendOrigin, lt_self_iff_false, ↓reduceIte]
      rw [← hl, getD_append_last]
  · apply alias_lookup_append
    · intro i
      exact alias_append_gate n C s.1 o j _ (s.2.getD i none) i
        (bounded_getD n s hvld.2 i) (ht.2.2.2.2 i)
    · rw [hl]
      apply alias_emitted n C s.1 o j a b u v hj hinputs ha hb hu hv
      · rw [← hua]
        exact ht.2.2.2.2 a
      · rw [← hvb]
        exact ht.2.2.2.2 b

lemma compileStep_trace (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (s : List Gate × List (Option ℕ)) (o : ℕ → ℕ)
    (ht : GateTrace n C j s o) (hvld : Valid n s) (hl : s.2.length = n + j) :
    ∃ o', GateTrace n C (j + 1) (compileStep n q s (gateAt C j)) o' := by
  have hm : gateAt C j ∈ C.gates := by
    rw [PEqualNP.Outside.L_meta_4675.PruningTrace.gateAt_eq_getElem C j hj]
    exact List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ hm)
  have ha : a < n + j := hAO.2.1 j hj a (by simp [hab])
  have hb : b < n + j := hAO.2.1 j hj b (by simp [hab])
  by_cases hkill : s.2.length = n + q
  · simp only [compileStep, hkill, ↓reduceIte]
    exact ⟨o, trace_drop n C j s o ht hl none (alias_none n C s.1 o (n + j))⟩
  · simp only [compileStep, hkill, ↓reduceIte, hab, List.getD_cons_zero, List.getD_cons_succ]
    cases hx : s.2.getD a none with
    | none =>
      cases hy : s.2.getD b none with
      | none =>
        simp only [emitPair]
        exact ⟨o, trace_drop n C j s o ht hl none (alias_none n C s.1 o (n + j))⟩
      | some v =>
        cases his : isAnd (gateAt C j).op
        · simp only [emitPair, Bool.false_eq_true, ↓reduceIte]
          refine ⟨o, trace_drop n C j s o ht hl (some v) ?_⟩
          apply alias_parent n C s.1 o (some v) j b hj (by simp [hab]) hb
          rw [← hy]
          exact ht.2.2.2.2 b
        · simp only [emitPair, ↓reduceIte]
          exact ⟨o, trace_drop n C j s o ht hl none (alias_none n C s.1 o (n + j))⟩
    | some u =>
      cases hy : s.2.getD b none with
      | none =>
        cases his : isAnd (gateAt C j).op
        · simp only [emitPair, Bool.false_eq_true, ↓reduceIte]
          refine ⟨o, trace_drop n C j s o ht hl (some u) ?_⟩
          apply alias_parent n C s.1 o (some u) j a hj (by simp [hab]) ha
          rw [← hx]
          exact ht.2.2.2.2 a
        · simp only [emitPair, ↓reduceIte]
          exact ⟨o, trace_drop n C j s o ht hl none (alias_none n C s.1 o (n + j))⟩
      | some v =>
        simp only [emitPair]
        refine ⟨extendOrigin o s.1.length j, trace_emit n C j hj s o ht hvld hl a b u v hab ha hb hx hy ?_⟩
        exact (PEqualNP.Outside.L_meta_4675.PruningTrace.original_gate_kind n C hAO j hj).symm

lemma initial_trace (n : ℕ) (C : Circuit) : GateTrace n C 0 (initial n) (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk; simp [initial] at hk
  · intro a b hab hb; simp [initial] at hb
  · intro k hk; simp [initial] at hk
  · intro k hk; simp [initial] at hk
  · intro i w hw k hk; simp [initial] at hk

lemma compiled_trace (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∃ o, GateTrace n C C.gates.length (compiled n q C.gates) o := by
  have h : ∀ j, j ≤ C.gates.length → Valid n (compiled n q (C.gates.take j)) ∧
      ∃ o, GateTrace n C j (compiled n q (C.gates.take j)) o := by
    intro j
    induction j with
    | zero =>
      intro hj
      simpa [compiled] using (show Valid n (initial n) ∧
        ∃ o, GateTrace n C 0 (initial n) o from ⟨initial_valid n, _, initial_trace n C⟩)
    | succ j ih =>
      intro hj
      obtain ⟨hv, o, ht⟩ := ih (by omega)
      have hlt : j < C.gates.length := by omega
      rw [compiled_take_succ n q C.gates j hlt,
        ← PEqualNP.Outside.L_meta_4675.PruningTrace.gateAt_eq_getElem C j hlt]
      refine ⟨compileStep_valid n q _ (gateAt C j) hv, ?_⟩
      apply compileStep_trace n q C hAO j hlt _ o ht hv
      rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
  simpa using (h C.gates.length le_rfl).2

lemma pruned_gate_cone_embedding (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∃ o : ℕ → ℕ,
      (∀ k < (pruned n q C).gates.length, o k < C.gates.length) ∧
      (∀ a b, a < b → b < (pruned n q C).gates.length → o a < o b) ∧
      (∀ k < (pruned n q C).gates.length,
        (gateAt (pruned n q C) k).op = (gateAt C (o k)).op) ∧
      (∀ a b, a < (pruned n q C).gates.length → b < (pruned n q C).gates.length →
        InCone n (pruned n q C) a b → InCone n C (o a) (o b)) ∧
      (∀ k < (pruned n q C).gates.length, o k ≠ q) := by
  obtain ⟨o, ht⟩ := compiled_trace n q C hAO
  refine ⟨o, ht.1, ht.2.1, ht.2.2.1, ?_, ?_⟩
  · intro a b ha hb hc
    have hab : a < b := PEqualNP.Outside.L_meta_4675.OneJunk.inCone_lt n (pruned n q C) b a hc
    have horig := ht.2.1 a b hab hb
    have hnew : WireCone n ⟨(compiled n q C.gates).1, 0⟩ (n + b) a :=
      Or.inr ⟨by omega, by simpa only [Nat.add_sub_cancel_left, InCone, cones, pruned] using hc⟩
    have hold := ht.2.2.2.2 (n + o b) (n + b) (ht.2.2.2.1 b hb) a ha hnew
    rcases hold with he | ⟨_, hold⟩
    · omega
    · simpa using hold
  · intro k hk he
    by_cases hq : q < C.gates.length
    · have hlookup := ht.2.2.2.1 k hk
      rw [he, killed_alias n q C.gates hq] at hlookup
      cases hlookup
    · have hb := ht.1 k hk
      omega

lemma pruned_andPairs_le (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    andPairs n (pruned n q C) ≤ andPairs n C := by
  obtain ⟨o, hb, hs, hop, hc, _⟩ := pruned_gate_cone_embedding n q C hAO
  have hi : ∀ a b, a < (pruned n q C).gates.length → b < (pruned n q C).gates.length →
      o a = o b → a = b := by
    intro a b ha hb he
    rcases Nat.lt_trichotomy a b with h | h | h
    · have := hs a b h hb; omega
    · exact h
    · have := hs b a h ha; omega
  unfold andPairs
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (o p.1, o p.2))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    exact ⟨⟨hb p.1 hp.1.1, hb p.2 hp.1.2⟩,
      (hop p.1 hp.1.1).symm.trans hp.2.1,
      (hop p.2 hp.1.2).symm.trans hp.2.2.1,
      hc p.1 p.2 hp.1.1 hp.1.2 hp.2.2.2⟩
  · intro a ha b hb he
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ha hb
    have he1 : o a.1 = o b.1 := congrArg Prod.fst he
    have he2 : o a.2 = o b.2 := congrArg Prod.snd he
    exact Prod.ext (hi a.1 b.1 ha.1.1 hb.1.1 he1) (hi a.2 b.2 ha.1.2 hb.1.2 he2)

end PEqualNP.Outside.L_meta_4675.ConeTrace
