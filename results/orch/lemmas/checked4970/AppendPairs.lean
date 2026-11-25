import Shield

namespace PEqualNP.Outside.L_meta_4970_aux.AppendPair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour
  PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_4970_aux.Shield

abbrev Pair (p l : Nat) := Fin p × (Fin l × Fin l)

def PairValid {p l : Nat} (E : Finset (Fin p × Fin l)) (pairs : List (Pair p l)) : Prop :=
  ∀ t ∈ pairs, t.2.1 ≠ t.2.2 ∧ (t.1, t.2.1) ∈ E ∧ (t.1, t.2.2) ∈ E

def PairCovers {p l : Nat} (E : Finset (Fin p × Fin l)) (pairs : List (Pair p l)) : Prop :=
  ∀ a b, (a,b) ∈ E → ∃ t ∈ pairs, t.1 = a ∧ (t.2.1 = b ∨ t.2.2 = b)

def pairGate {p l : Nat} (t : Pair p l) : Gate :=
  ⟨GateOp.or, [p + t.2.1.val, p + t.2.2.val]⟩

def appendPairs {p l : Nat} (C : Circuit) (pairs : List (Pair p l)) : Circuit :=
  ⟨C.gates ++ pairs.map pairGate, C.output⟩

theorem size_append {p l : Nat} (C : Circuit) (pairs : List (Pair p l)) :
    (appendPairs C pairs).size = C.size + pairs.length := by
  simp [appendPairs, Circuit.size]

theorem gate_prefix (C : Circuit) (gs : List Gate) {j : Nat} (hj : j < C.gates.length) :
    gateAt ⟨C.gates ++ gs, C.output⟩ j = gateAt C j := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem gate_pair {p l : Nat} (C : Circuit) (pairs : List (Pair p l))
    {k : Nat} (hk : k < pairs.length) :
    gateAt (appendPairs C pairs) (C.gates.length + k) = pairGate pairs[k] := by
  simp [gateAt, appendPairs, List.getD_eq_getElem?_getD,
    hk]

theorem append_ao {p l : Nat} {C : Circuit} (hC : IsAO2 (p+l) C)
    (pairs : List (Pair p l)) : IsAO2 (p+l) (appendPairs C pairs) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [appendPairs, List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨t, _, rfl⟩
    · exact hC.1 g hg
    · exact Or.inr rfl
  · intro j hj i hi
    by_cases hj0 : j < C.gates.length
    · rw [show gateAt (appendPairs C pairs) j = gateAt C j from gate_prefix C _ hj0] at hi
      exact hC.2.1 j hj0 i hi
    · have hk : j - C.gates.length < pairs.length := by
        simp only [appendPairs, List.length_append, List.length_map] at hj
        omega
      have hjk : j = C.gates.length + (j - C.gates.length) := by omega
      rw [hjk, gate_pair C pairs hk] at hi
      simp only [pairGate, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have := pairs[j - C.gates.length].2.1.isLt; omega
      · have := pairs[j - C.gates.length].2.2.isLt; omega
  · intro g hg
    simp only [appendPairs, List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨t, _, rfl⟩
    · exact hC.2.2 g hg
    · rfl

theorem append_fun {p l : Nat} {C : Circuit}
    (hout : C.output < p+l+C.gates.length) (pairs : List (Pair p l)) :
    circuitFun (p+l) (appendPairs C pairs) = circuitFun (p+l) C := by
  funext x
  rw [circuitFun_W, circuitFun_W]
  change (W (C.gates ++ pairs.map pairGate) (List.ofFn x)).getD C.output false = _
  rw [W_append, W_prefix _ _ _ (by simp only [W_length, List.length_ofFn]; exact hout)]

theorem prefix_reaches (n : Nat) (C : Circuit) (gs : List Gate) :
    ∀ w, w < n + C.gates.length → ∀ g,
      OrReaches n ⟨C.gates ++ gs, C.output⟩ w g ↔ OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw g
    by_cases hn : n ≤ w
    · obtain ⟨k, rfl⟩ : ∃ k, w = n+k := ⟨w-n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hkd : k < C.gates.length + gs.length := by omega
      rw [orReaches_iff, orReaches_iff, gate_prefix C gs hk]
      simp only [List.length_append, hk, hkd, true_and]
      constructor
      · rintro (hh | ⟨hop, i, hi, hil, hir⟩)
        · exact Or.inl hh
        · exact Or.inr ⟨hop, i, hi, hil, (ih i hil (by omega) g).mp hir⟩
      · rintro (hh | ⟨hop, i, hi, hil, hir⟩)
        · exact Or.inl hh
        · exact Or.inr ⟨hop, i, hi, hil, (ih i hil (by omega) g).mpr hir⟩
    · exact ⟨fun hh => False.elim (hn hh.1), fun hh => False.elim (hn hh.1)⟩

theorem prefix_orIn (n : Nat) (C : Circuit) (gs : List Gate) {w : Nat}
    (hw : w < n+C.gates.length) :
    orIn n ⟨C.gates ++ gs, C.output⟩ w = orIn n C w := by
  ext i
  rw [mem_orIn, mem_orIn]
  constructor
  · rintro (hh | ⟨k, _, hr, hop, hi⟩)
    · exact Or.inl hh
    · have hbound := (orReaches_bound n ⟨C.gates ++ gs, C.output⟩ k w hr).1
      have hk : k < C.gates.length := by omega
      rw [gate_prefix C gs hk] at hop hi
      exact Or.inr ⟨k, hk, (prefix_reaches n C gs w hw k).mp hr, hop, hi⟩
  · rintro (hh | ⟨k, hk, hr, hop, hi⟩)
    · exact Or.inl hh
    · refine Or.inr ⟨k, by simp; omega, (prefix_reaches n C gs w hw k).mpr hr, ?_, ?_⟩
      · simpa only [gate_prefix C gs hk] using hop
      · simpa only [gate_prefix C gs hk] using hi

theorem pair_reaches {p l : Nat} (C : Circuit) (pairs : List (Pair p l))
    {k : Nat} (hk : k < pairs.length) {g : Nat}
    (hr : OrReaches (p+l) (appendPairs C pairs) (p+l+(C.gates.length+k)) g) :
    g = C.gates.length+k := by
  rw [orReaches_iff, gate_pair C pairs hk] at hr
  rcases hr.2 with hh | ⟨_, i, hi, _, hir⟩
  · exact hh
  · simp only [pairGate, List.mem_cons, List.not_mem_nil, or_false] at hi
    have hn := hir.1
    rcases hi with rfl | rfl
    · have := pairs[k].2.1.isLt; omega
    · have := pairs[k].2.2.isLt; omega

theorem pair_orIn_line {p l : Nat} (C : Circuit) (pairs : List (Pair p l))
    {k : Nat} (hk : k < pairs.length) {i : Fin (p+l)}
    (hi : i ∈ orIn (p+l) (appendPairs C pairs) (p+l+(C.gates.length+k))) : p ≤ i.val := by
  rw [mem_orIn] at hi
  rcases hi with hi | ⟨g, _, hr, _, hin⟩
  · have := i.isLt; omega
  · have hg := pair_reaches C pairs hk hr
    rw [hg, gate_pair C pairs hk] at hin
    simp only [pairGate, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with hin | hin <;> omega

theorem append_t0 {p l : Nat} {C : Circuit}
    (hC : tCount (p+l) C (fun i => decide (p ≤ i)) = 0)
    (pairs : List (Pair p l)) :
    tCount (p+l) (appendPairs C pairs) (fun i => decide (p ≤ i)) = 0 := by
  have hnone : ∀ j, ¬ IsTwoColour (p+l) C (fun i => decide (p ≤ i)) j := by
    intro j hj
    have hm : j ∈ twoColour (p+l) C (fun i => decide (p ≤ i)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj.1, hj⟩
    have hz : twoColour (p+l) C (fun i => decide (p ≤ i)) = ∅ := Finset.card_eq_zero.mp hC
    rw [hz] at hm
    exact Finset.notMem_empty j hm
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro j hj
  obtain ⟨_, hj, hop, ⟨i, hi, hif⟩, ⟨i', hi', hit⟩⟩ := Finset.mem_filter.mp hj
  by_cases hj0 : j < C.gates.length
  · apply hnone j
    refine ⟨hj0, ?_, ⟨i, ?_, hif⟩, ⟨i', ?_, hit⟩⟩
    · simpa only [show gateAt (appendPairs C pairs) j = gateAt C j from gate_prefix C _ hj0] using hop
    · simpa only [appendPairs, prefix_orIn (p+l) C (pairs.map pairGate) (w := p+l+j) (by omega)] using hi
    · simpa only [appendPairs, prefix_orIn (p+l) C (pairs.map pairGate) (w := p+l+j) (by omega)] using hi'
  · have hk : j - C.gates.length < pairs.length := by
      simp only [appendPairs, List.length_append, List.length_map] at hj
      omega
    have hjk : j = C.gates.length + (j-C.gates.length) := by omega
    rw [hjk] at hi
    have hpi := pair_orIn_line C pairs hk hi
    simp [hpi] at hif

theorem pair_value {p l : Nat} (C : Circuit) (pairs : List (Pair p l))
    {k : Nat} (hk : k < pairs.length) (x : Fin (p+l) → Bool) :
    ((appendPairs C pairs).wires (List.ofFn x)).getD (p+l+(C.gates.length+k)) false =
      decide (∃ b ∈ ({pairs[k].2.1, pairs[k].2.2} : Finset (Fin l)),
        x (Fin.natAdd p b) = true) := by
  let D := appendPairs C pairs
  have hj : C.gates.length+k < D.gates.length := by simp [D, appendPairs]; omega
  have hb : ∀ i ∈ (gateAt D (C.gates.length+k)).inputs, i < p+l+(C.gates.length+k) := by
    intro i hi
    rw [show gateAt D (C.gates.length+k) = pairGate pairs[k] from gate_pair C pairs hk] at hi
    simp only [pairGate, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · have := pairs[k].2.1.isLt; omega
    · have := pairs[k].2.2.isLt; omega
  change val D (List.ofFn x) (p+l+(C.gates.length+k)) = _
  rw [val_gate_rb (by simp) hj hb]
  rw [show gateAt D (C.gates.length+k) = pairGate pairs[k] from gate_pair C pairs hk]
  have h1 : val D (List.ofFn x) (p+pairs[k].2.1.val) = x (Fin.natAdd p pairs[k].2.1) :=
    val_ofFn D x (Fin.natAdd p pairs[k].2.1)
  have h2 : val D (List.ofFn x) (p+pairs[k].2.2.val) = x (Fin.natAdd p pairs[k].2.2) :=
    val_ofFn D x (Fin.natAdd p pairs[k].2.2)
  simp only [pairGate, List.map_cons, List.map_nil, h1, h2]
  cases hxa : x (Fin.natAdd p pairs[k].2.1) <;>
    cases hxb : x (Fin.natAdd p pairs[k].2.2) <;> simp [GateOp.eval, hxa, hxb]

theorem append_serves {p l : Nat} (C : Circuit) (E : Finset (Fin p × Fin l))
    (pairs : List (Pair p l)) (hv : PairValid E pairs) (hc : PairCovers E pairs) :
    ∀ a b, (a,b) ∈ E → ∃ j : Nat, ∃ Q : Finset (Fin l),
      j < (appendPairs C pairs).gates.length ∧
      (gateAt (appendPairs C pairs) j).op = GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧
      (∀ b' ∈ Q, (a,b') ∈ E) ∧ ∀ x : Fin (p+l) → Bool,
        ((appendPairs C pairs).wires (List.ofFn x)).getD (p+l+j) false =
          decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true) := by
  intro a b he
  obtain ⟨t, ht, hta, htb⟩ := hc a b he
  obtain ⟨k, hk, hkt⟩ := List.mem_iff_getElem.mp ht
  have hvalid := hv t ht
  subst t
  refine ⟨C.gates.length+k, {pairs[k].2.1, pairs[k].2.2}, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [appendPairs]; omega
  · rw [gate_pair C pairs hk]; rfl
  · rw [Finset.card_pair hvalid.1]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    exact htb.imp Eq.symm Eq.symm
  · intro b' hb'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
    rcases hb' with rfl | rfl
    · simpa only [hta] using hvalid.2.1
    · simpa only [hta] using hvalid.2.2
  · exact pair_value C pairs hk

theorem output_valid {p l : Nat} {C : Circuit} {E : Finset (Fin p × Fin l)}
    (hE : E.Nonempty)
    (hfun : ∀ x : Fin (p+l) → Bool, circuitFun (p+l) C x =
      decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    C.output < p+l+C.gates.length := by
  obtain ⟨⟨a,b⟩, hab⟩ := hE
  have ht : circuitFun (p+l) C (fun _ => true) = true := by
    rw [hfun]
    exact decide_eq_true ⟨a,b,hab,rfl,rfl⟩
  by_contra hn
  have hz := W_ge C.gates (List.ofFn (fun _ : Fin (p+l) => true)) C.output
    (by simp only [List.length_ofFn]; omega)
  rw [circuitFun_W, hz] at ht
  cases ht

theorem append_main {p l : Nat} {C : Circuit} {E : Finset (Fin p × Fin l)}
    (hC : IsAO2 (p+l) C)
    (hT : tCount (p+l) C (fun i => decide (p ≤ i)) = 0)
    (hout : C.output < p+l+C.gates.length)
    (pairs : List (Pair p l)) (hv : PairValid E pairs) (hc : PairCovers E pairs) :
    ∃ D : Circuit, IsAO2 (p+l) D ∧
      tCount (p+l) D (fun i => decide (p ≤ i)) = 0 ∧
      D.size = C.size + pairs.length ∧ circuitFun (p+l) D = circuitFun (p+l) C ∧
      ∀ a b, (a,b) ∈ E → ∃ j : Nat, ∃ Q : Finset (Fin l),
        j < D.gates.length ∧ (gateAt D j).op = GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧
        (∀ b' ∈ Q, (a,b') ∈ E) ∧ ∀ x : Fin (p+l) → Bool,
          (D.wires (List.ofFn x)).getD (p+l+j) false =
            decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true) :=
  ⟨appendPairs C pairs, append_ao hC pairs, append_t0 hT pairs,
    size_append C pairs, append_fun hout pairs, append_serves C E pairs hv hc⟩

end PEqualNP.Outside.L_meta_4970_aux.AppendPair
