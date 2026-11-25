import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2685_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

def back (B : ℕ) (gs : List Gate) : Prop :=
  ∀ i < gs.length, ∀ u ∈ (gs.getD i ⟨GateOp.or, []⟩).inputs, u < B + i

lemma back_append (B : ℕ) (gs hs : List Gate)
    (hg : back B gs) (hh : back (B + gs.length) hs) : back B (gs ++ hs) := by
  intro i hi u hu
  by_cases h : i < gs.length
  · have he : (gs ++ hs).getD i ⟨GateOp.or, []⟩ = gs.getD i ⟨GateOp.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    rw [he] at hu
    exact hg i h u hu
  · have he : (gs ++ hs).getD i ⟨GateOp.or, []⟩ =
        hs.getD (i - gs.length) ⟨GateOp.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (show gs.length ≤ i by omega)]
    rw [he] at hu
    have hix : i - gs.length < hs.length := by simp only [List.length_append] at hi; omega
    have hu' := hh (i - gs.length) hix u hu
    omega

lemma block_length (B a t v : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  cases lead <;> simp [blockGates]

lemma chain_wire_lt (B v : ℕ) (rest : List ℕ) (hv : v < B) (i : ℕ)
    (hi : i ≤ rest.length) :
    (v :: (List.range rest.length).map (fun j => B + j)).getD i 0 < B + i := by
  cases i with
  | zero => simpa using hv
  | succ i =>
    have hi' : i < rest.length := by omega
    simp [List.getD_cons_succ, List.getD_eq_getElem?_getD, hi']

lemma block_back (B a t v : ℕ) (rest : List ℕ) (lead : Bool)
    (ha : lead = false → a < B) (ht : t < B) (hv : v < B)
    (hr : ∀ u ∈ rest, u < B) : back B (blockGates B a t v rest lead) := by
  unfold blockGates
  apply back_append
  · intro i hi u hu
    have hi' : i < rest.length := by simpa using hi
    have hp := chain_wire_lt B v rest hv i hi'.le
    have hrest : rest.getD i 0 < B := by
      rw [List.getD_eq_getElem _ _ hi']
      exact hr _ (List.getElem_mem hi')
    have he : ((List.range rest.length).map (fun i =>
        (⟨GateOp.or, [(v :: (List.range rest.length).map (fun j => B + j)).getD i 0,
          rest.getD i 0]⟩ : Gate))).getD i ⟨GateOp.or, []⟩ =
        ⟨GateOp.or, [(v :: (List.range rest.length).map (fun j => B + j)).getD i 0,
          rest.getD i 0]⟩ := by
      simp [List.getD_eq_getElem?_getD, hi']
    rw [he] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> omega
  · have hp := chain_wire_lt B v rest hv rest.length le_rfl
    simp only [List.length_map, List.length_range]
    intro i hi u hu
    cases lead with
    | true =>
      have hi0 : i = 0 := by simpa using hi
      subst i
      simp only [ite_true, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> omega
    | false =>
      have hab := ha rfl
      have hil : i < 2 := by simpa using hi
      interval_cases i <;>
        simp only [Bool.false_eq_true, ite_false, List.getD_cons_zero, List.getD_cons_succ,
          List.mem_cons, List.not_mem_nil, or_false] at hu
      · rcases hu with rfl | rfl <;> omega
      · rcases hu with rfl | rfl <;> omega

lemma gates_back : ∀ (own : List (ℕ × List ℕ)) (n B : ℕ) (lead : Bool) (a : ℕ),
    n ≤ B → (lead = false → a < B) →
    (∀ tx ∈ own, tx.1 < n ∧ ∀ u ∈ tx.2, u < n) →
    back B (coverGatesB B lead a own)
  | [], _, _, _, _, _, _, _ => by simp [back, coverGatesB]
  | (_, []) :: os, n, B, lead, a, hn, ha, ho => by
      exact gates_back os n B lead a hn ha (fun tx htx => ho tx (List.mem_cons_of_mem _ htx))
  | (t, v :: rest) :: os, n, B, lead, a, hn, ha, ho => by
      have ht := (ho (t, v :: rest) (by simp)).1
      have hv := (ho (t, v :: rest) (by simp)).2 v (by simp)
      have hr (u : ℕ) (hu : u ∈ rest) := (ho (t, v :: rest) (by simp)).2 u (by simp [hu])
      have hlen : 0 < (blockGates B a t v rest lead).length := by rw [block_length]; omega
      apply back_append
      · exact block_back B a t v rest lead ha (by omega) (by omega)
          (fun u hu => by have := hr u hu; omega)
      · exact gates_back os n _ false _ (by omega) (fun _ => by omega)
          (fun tx htx => ho tx (List.mem_cons_of_mem _ htx))

lemma block_shape (B a t v : ℕ) (rest : List ℕ) (lead : Bool) :
    ∀ g ∈ blockGates B a t v rest lead,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  cases lead <;> simp [blockGates] at hg <;> rcases hg with ⟨i, _, rfl⟩ | rfl | rfl <;> simp

lemma gates_shape : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
    ∀ g ∈ coverGatesB B lead a own,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  | [], _, _, _ => by intro g hg; simp [coverGatesB] at hg
  | (_, []) :: os, B, lead, a => by
      intro g hg
      exact gates_shape os B lead a g hg
  | (t, v :: rest) :: os, B, lead, a => by
      intro g hg
      simp only [coverGatesB, List.mem_append] at hg
      rcases hg with hg | hg
      · exact block_shape B a t v rest lead g hg
      · exact gates_shape os _ false _ g hg

lemma coverCircuitB_isAO2 (n : ℕ) (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own, tx.1 < n ∧ ∀ u ∈ tx.2, u < n) :
    IsAO2 n (coverCircuitB n own) := by
  have hg := gates_shape own n true 0
  have hb := gates_back own n n true 0 le_rfl (by simp) ho
  unfold coverCircuitB
  split_ifs
  · simp [IsAO2, AndOrOnly, ReadsBack]
  · exact ⟨fun g h => (hg g h).1, hb, fun g h => (hg g h).2⟩

def closed (B : ℕ) (gs : List Gate) (base S : Finset ℕ) : Prop :=
  ∀ w ∈ S, w ∈ base ∨ ∃ i < gs.length, w = B + i ∧
    (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.or ∧
    ∀ u ∈ (gs.getD i ⟨GateOp.or, []⟩).inputs, u ∈ S

def shaped (B : ℕ) (gs : List Gate) (P0 L0 P L : Finset ℕ) : Prop :=
  closed B gs P0 P ∧ closed B gs L0 L ∧
  ∀ i < gs.length, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ a b, (gs.getD i ⟨GateOp.or, []⟩).inputs = [a,b] ∧
      ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))

lemma gate_append_left (gs hs : List Gate) (i : ℕ) (hi : i < gs.length) :
    (gs ++ hs).getD i ⟨GateOp.or, []⟩ = gs.getD i ⟨GateOp.or, []⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma gate_append_right (gs hs : List Gate) (i : ℕ) :
    (gs ++ hs).getD (gs.length + i) ⟨GateOp.or, []⟩ = hs.getD i ⟨GateOp.or, []⟩ := by
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (show gs.length ≤ gs.length + i by omega),
    Nat.add_sub_cancel_left]

lemma closed_append (B : ℕ) (gs hs : List Gate) (base S T : Finset ℕ)
    (hS : closed B gs base S) (hT : closed (B + gs.length) hs base T) :
    closed B (gs ++ hs) base (S ∪ T) := by
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · rcases hS w hw with hw | ⟨i,hi,he,hop,hu⟩
    · exact Or.inl hw
    · refine Or.inr ⟨i,by simp; omega,he,?_,?_⟩
      · simpa only [gate_append_left gs hs i hi] using hop
      · intro u hum
        have hu' : u ∈ S := hu u (by simpa only [gate_append_left gs hs i hi] using hum)
        exact Finset.mem_union_left T hu'
  · rcases hT w hw with hw | ⟨i,hi,he,hop,hu⟩
    · exact Or.inl hw
    · refine Or.inr ⟨gs.length+i,by simp; omega,by omega,?_,?_⟩
      · simpa only [gate_append_right] using hop
      · intro u hum
        have hu' : u ∈ T := hu u (by simpa only [gate_append_right] using hum)
        exact Finset.mem_union_right S hu'

lemma shaped_append (B : ℕ) (gs hs : List Gate) (P0 L0 P L P' L' : Finset ℕ)
    (hg : shaped B gs P0 L0 P L) (hh : shaped (B + gs.length) hs P0 L0 P' L') :
    shaped B (gs ++ hs) P0 L0 (P ∪ P') (L ∪ L') := by
  refine ⟨closed_append B gs hs P0 P P' hg.1 hh.1,
    closed_append B gs hs L0 L L' hg.2.1 hh.2.1,?_⟩
  intro i hi hop
  by_cases hx : i < gs.length
  · obtain ⟨a,b,he,ha⟩ := hg.2.2 i hx (by simpa only [gate_append_left gs hs i hx] using hop)
    refine ⟨a,b,by simpa only [gate_append_left gs hs i hx] using he,?_⟩
    rcases ha with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨Finset.mem_union_left _ ha,Finset.mem_union_left _ hb⟩
    · exact Or.inr ⟨Finset.mem_union_left _ ha,Finset.mem_union_left _ hb⟩
  · have hie : i = gs.length + (i-gs.length) := by omega
    have hix : i-gs.length < hs.length := by simp only [List.length_append] at hi; omega
    rw [hie,gate_append_right] at hop
    obtain ⟨a,b,he,ha⟩ := hh.2.2 (i-gs.length) hix hop
    refine ⟨a,b,?_,?_⟩
    · rw [hie,gate_append_right]
      exact he
    rcases ha with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨Finset.mem_union_right _ ha,Finset.mem_union_right _ hb⟩
    · exact Or.inr ⟨Finset.mem_union_right _ ha,Finset.mem_union_right _ hb⟩

lemma shaped_swap (B : ℕ) (gs : List Gate) (P0 L0 P L : Finset ℕ)
    (h : shaped B gs P0 L0 P L) : shaped B gs L0 P0 L P := by
  refine ⟨h.2.1,h.1,?_⟩
  intro i hi hop
  obtain ⟨a,b,he,ha⟩ := h.2.2 i hi hop
  exact ⟨a,b,he,ha.symm⟩

def chainWires (B : ℕ) (rest : List ℕ) : Finset ℕ :=
  (Finset.range rest.length).image (fun i => B+i)

lemma chain_wire_mem (B v : ℕ) (rest : List ℕ) (L0 : Finset ℕ) (hv : v ∈ L0)
    (i : ℕ) (hi : i ≤ rest.length) :
    (v :: (List.range rest.length).map (fun j => B+j)).getD i 0 ∈ L0 ∪ chainWires B rest := by
  cases i with
  | zero => exact Finset.mem_union_left _ hv
  | succ i =>
    have hi' : i < rest.length := by omega
    have he : (v :: (List.range rest.length).map (fun j => B+j)).getD (i+1) 0 = B+i := by
      simp [List.getD_eq_getElem?_getD,hi']
    rw [he]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi',rfl⟩)

lemma block_chain (B a t v : ℕ) (rest : List ℕ) (lead : Bool) (i : ℕ) (hi : i < rest.length) :
    (blockGates B a t v rest lead).getD i ⟨GateOp.or,[]⟩ =
      ⟨GateOp.or,[(v :: (List.range rest.length).map (fun j => B+j)).getD i 0,rest.getD i 0]⟩ := by
  unfold blockGates
  rw [gate_append_left _ _ i (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD,hi]

lemma block_and (B a t v : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v rest lead).getD rest.length ⟨GateOp.or,[]⟩ =
      ⟨GateOp.and,[t,(v :: (List.range rest.length).map (fun j => B+j)).getD rest.length 0]⟩ := by
  unfold blockGates
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp)]
  simp

lemma block_is_and (B a t v : ℕ) (rest : List ℕ) (lead : Bool) (i : ℕ)
    (hi : i < (blockGates B a t v rest lead).length)
    (hop : ((blockGates B a t v rest lead).getD i ⟨GateOp.or,[]⟩).op = GateOp.and) :
    i = rest.length := by
  by_cases h : i < rest.length
  · rw [block_chain B a t v rest lead i h] at hop
    contradiction
  · rw [block_length] at hi
    have hc : i = rest.length ∨ i = rest.length+1 := by split_ifs at hi <;> omega
    rcases hc with he | he
    · exact he
    · have hl : lead = false := by cases lead <;> simp_all
      subst lead
      subst i
      unfold blockGates at hop
      rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp)] at hop
      simp at hop

lemma block_shaped (B a t v : ℕ) (rest : List ℕ) (lead : Bool) (P0 L0 : Finset ℕ)
    (ht : t ∈ P0) (hv : v ∈ L0) (hr : ∀ u ∈ rest, u ∈ L0) :
    shaped B (blockGates B a t v rest lead) P0 L0 P0 (L0 ∪ chainWires B rest) := by
  refine ⟨fun w hw => Or.inl hw,?_,?_⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Or.inl hw
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
      have hi' : i < rest.length := Finset.mem_range.mp hi
      refine Or.inr ⟨i,?_,rfl,?_,?_⟩
      · rw [block_length]; omega
      · simp only [block_chain B a t v rest lead i hi']
      · rw [block_chain B a t v rest lead i hi']
        intro u hu
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
        rcases hu with rfl | rfl
        · exact chain_wire_mem B v rest L0 hv i hi'.le
        · apply Finset.mem_union_left
          rw [List.getD_eq_getElem _ _ hi']
          exact hr _ (List.getElem_mem hi')
  · intro i hi hop
    have he := block_is_and B a t v rest lead i hi hop
    subst i
    rw [block_and]
    exact ⟨t,_,rfl,Or.inl ⟨ht,chain_wire_mem B v rest L0 hv rest.length le_rfl⟩⟩

lemma gates_shaped : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ)
    (P0 L0 : Finset ℕ),
    (∀ tx ∈ own, (tx.1 ∈ P0 ∧ ∀ u ∈ tx.2, u ∈ L0) ∨
      (tx.1 ∈ L0 ∧ ∀ u ∈ tx.2, u ∈ P0)) →
    ∃ P L : Finset ℕ, shaped B (coverGatesB B lead a own) P0 L0 P L
  | [], B, lead, a, P0, L0, _ => by
      refine ⟨P0,L0,fun w hw => Or.inl hw,fun w hw => Or.inl hw,?_⟩
      simp [coverGatesB]
  | (_, []) :: os, B, lead, a, P0, L0, ho => by
      exact gates_shaped os B lead a P0 L0 (fun tx htx => ho tx (List.mem_cons_of_mem _ htx))
  | (t, v :: rest) :: os, B, lead, a, P0, L0, ho => by
      obtain ⟨P,L,hPL⟩ := gates_shaped os
        (B + (blockGates B a t v rest lead).length) false
        (B + (blockGates B a t v rest lead).length - 1) P0 L0
        (fun tx htx => ho tx (List.mem_cons_of_mem _ htx))
      rcases ho (t,v :: rest) (by simp) with ⟨ht,hr⟩ | ⟨ht,hr⟩
      · have hblock := block_shaped B a t v rest lead P0 L0 ht
          (hr v (by simp)) (fun u hu => hr u (by simp [hu]))
        exact ⟨_,_,shaped_append B _ _ P0 L0 _ _ P L hblock hPL⟩
      · have hblock := shaped_swap B _ L0 P0 _ _
          (block_shaped B a t v rest lead L0 P0 ht
            (hr v (by simp)) (fun u hu => hr u (by simp [hu])))
        exact ⟨_,_,shaped_append B _ _ P0 L0 _ _ P L hblock hPL⟩

lemma coverCircuitB_gates (n : ℕ) (own : List (ℕ × List ℕ)) :
    (coverCircuitB n own).gates = coverGatesB n true 0 own := by
  unfold coverCircuitB
  split_ifs with h
  · exact h.symm
  · rfl

lemma coverCircuitB_twoLevel (Np Nl : ℕ) (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own,
      (tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np+Nl) ∨
      (Np ≤ tx.1 ∧ tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np)) :
    ∃ P L : Finset ℕ, IsAO2 (Np+Nl) (coverCircuitB (Np+Nl) own) ∧
      (∀ w ∈ P, w < Np ∨ ∃ i < (coverCircuitB (Np+Nl) own).gates.length,
        w = Np+Nl+i ∧ (gateAt (coverCircuitB (Np+Nl) own) i).op = GateOp.or ∧
        ∀ u ∈ (gateAt (coverCircuitB (Np+Nl) own) i).inputs, u ∈ P) ∧
      (∀ w ∈ L, (Np ≤ w ∧ w < Np+Nl) ∨
        ∃ i < (coverCircuitB (Np+Nl) own).gates.length,
        w = Np+Nl+i ∧ (gateAt (coverCircuitB (Np+Nl) own) i).op = GateOp.or ∧
        ∀ u ∈ (gateAt (coverCircuitB (Np+Nl) own) i).inputs, u ∈ L) ∧
      ∀ i < (coverCircuitB (Np+Nl) own).gates.length,
        (gateAt (coverCircuitB (Np+Nl) own) i).op = GateOp.and →
        ∃ a b : ℕ, (gateAt (coverCircuitB (Np+Nl) own) i).inputs = [a,b] ∧
          ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  have htag : ∀ tx ∈ own,
      (tx.1 ∈ Finset.range Np ∧ ∀ u ∈ tx.2, u ∈ Finset.Ico Np (Np+Nl)) ∨
      (tx.1 ∈ Finset.Ico Np (Np+Nl) ∧ ∀ u ∈ tx.2, u ∈ Finset.range Np) := by
    simpa only [Finset.mem_range,Finset.mem_Ico,and_assoc] using ho
  obtain ⟨P,L,hshape⟩ := gates_shaped own (Np+Nl) true 0 (Finset.range Np)
    (Finset.Ico Np (Np+Nl)) htag
  have hb : ∀ tx ∈ own, tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np+Nl := by
    intro tx htx
    rcases ho tx htx with ⟨ht,hu⟩ | ⟨ht,ht',hu⟩
    · exact ⟨by omega,fun u h => (hu u h).2⟩
    · exact ⟨ht',fun u h => by have := hu u h; omega⟩
  refine ⟨P,L,coverCircuitB_isAO2 (Np+Nl) own hb,?_,?_,?_⟩
  · simpa only [closed,Finset.mem_range,gateAt,coverCircuitB_gates] using hshape.1
  · simpa only [closed,Finset.mem_Ico,gateAt,coverCircuitB_gates] using hshape.2.1
  · simpa only [gateAt,coverCircuitB_gates] using hshape.2.2




lemma gates_length_false : ∀ (own : List (ℕ × List ℕ)) (B a : ℕ), (∀ p ∈ own, p.2 ≠ []) →
    (coverGatesB B false a own).length =
      (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length
  | [], _, _, _ => by simp [coverGatesB]
  | (t, []) :: os, B, a, h => by simp at h
  | (t, v1 :: rest) :: os, B, a, h => by
      have ih := gates_length_false os (B + (blockGates B a t v1 rest false).length)
        (B + (blockGates B a t v1 rest false).length - 1)
        (fun p hp => h p (List.mem_cons_of_mem _ hp))
      simp only [coverGatesB, List.length_append]
      rw [ih, block_length]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      simp
      omega

lemma circuit_size (n : ℕ) (own : List (ℕ × List ℕ)) (hne : own ≠ [])
    (h : ∀ p ∈ own, p.2 ≠ []) :
    (coverCircuitB n own).size + 1 =
      (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length := by
  match own, hne, h with
  | (t, []) :: os, _, h => simp at h
  | (t, v1 :: rest) :: os, _, h =>
      have ih := gates_length_false os (n + (blockGates n 0 t v1 rest true).length)
        (n + (blockGates n 0 t v1 rest true).length - 1)
        (fun p hp => h p (List.mem_cons_of_mem _ hp))
      have hgl : (coverGatesB n true 0 ((t, v1 :: rest) :: os)).length =
          rest.length + 1 + ((os.map (fun p : ℕ × List ℕ => p.2.length)).sum + os.length) := by
        simp only [coverGatesB, List.length_append]
        rw [ih, block_length]
        simp
      have hnn : coverGatesB n true 0 ((t, v1 :: rest) :: os) ≠ [] := by
        intro h0
        have h1 := congrArg List.length h0
        rw [hgl] at h1
        simp at h1
      unfold coverCircuitB Circuit.size
      rw [if_neg hnn]
      simp only [hgl, List.map_cons, List.sum_cons, List.length_cons]
      omega




def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma fold_app (gs : List Gate) : ∀ w : List Bool, ∃ t : List Bool,
    gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: t, ?_, ?_⟩
    · rw [List.foldl_cons, ht]; simp [step]
    · simp [hl]

lemma getD_app_left {w t : List Bool} {i : ℕ} (h : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

lemma getD_app_right {w t : List Bool} {i : ℕ} :
    (w ++ t).getD (w.length + i) false = t.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    ← List.getD_eq_getElem?_getD]

lemma getD_snoc' (l : List Bool) (b : Bool) (i : ℕ) (h : i = l.length) :
    (l ++ [b]).getD i false = b := by
  subst h
  simpa using getD_app_right (w := l) (t := [b]) (i := 0)

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_app gs w
  rw [ht, List.length_append, hl]

lemma fold_keep (gs : List Gate) (w : List Bool) {i : ℕ} (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_app gs w
  rw [ht, getD_app_left h]

lemma any_congr_mem {l : List ℕ} {f g : ℕ → Bool} (h : ∀ u ∈ l, f u = g u) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.any_cons]
    rw [h b (by simp), ih (fun u hu => h u (by simp [hu]))]


def cv (w : List Bool) (v1 : ℕ) (rest : List ℕ) (k : ℕ) : Bool :=
  w.getD v1 false || (rest.take k).any (fun u => w.getD u false)

lemma chain_read (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
    (hv1 : v1 < B) (k : ℕ) (hk : k ≤ rest.length) :
    (w ++ (List.range k).map (fun i => cv w v1 rest (i + 1))).getD
        ((v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0) false
      = cv w v1 rest k := by
  cases k with
  | zero =>
    simp only [List.getD_cons_zero]
    rw [getD_app_left (by omega)]
    simp [cv]
  | succ j =>
    have hj : j < rest.length := by omega
    have e1 : (v1 :: (List.range rest.length).map (fun j => B + j)).getD (j + 1) 0 = B + j := by
      simp [List.getD_cons_succ, List.getD_eq_getElem?_getD, hj]
    rw [e1, ← hw, getD_app_right]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show j < j + 1 by omega)]

lemma chain (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
    (hv1 : v1 < B) (hrest : ∀ u ∈ rest, u < B) :
    ∀ k ≤ rest.length,
      ((List.range k).map (fun i => (⟨GateOp.or,
          [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0, rest.getD i 0]⟩ : Gate))).foldl
        step w = w ++ (List.range k).map (fun i => cv w v1 rest (i + 1)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step]
    rw [List.append_assoc]
    congr 2
    have hkr : k < rest.length := by omega
    have hrk : rest.getD k 0 = rest[k] := by
      simp [List.getD_eq_getElem?_getD, hkr]
    have hlt : rest[k] < w.length := by rw [hw]; exact hrest _ (List.getElem_mem hkr)
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    rw [chain_read w B v1 rest hw hv1 k (by omega), hrk, getD_app_left hlt]
    simp only [cv, List.take_succ, List.getElem?_eq_getElem hkr, Option.toList_some,
      List.any_append, List.any_cons, List.any_nil, List.any_cons, Bool.or_false, id]
    simp [Bool.or_assoc, List.getElem?_eq_getElem hkr]

lemma block_val (w : List Bool) (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool)
    (hw : w.length = B) (ha : lead = false → a < B) (ht : t < B) (hv1 : v1 < B)
    (hrest : ∀ u ∈ rest, u < B) :
    ((blockGates B a t v1 rest lead).foldl step w).getD
        (B + (blockGates B a t v1 rest lead).length - 1) false
      = if lead then (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))
        else (w.getD a false ||
          (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))) := by
  have hc := chain w B v1 rest hw hv1 hrest rest.length le_rfl
  have hr := chain_read w B v1 rest hw hv1 rest.length le_rfl
  have hcvr : cv w v1 rest rest.length = (w.getD v1 false || rest.any (fun u => w.getD u false)) := by
    simp [cv]
  set L := (List.range rest.length).map (fun i => cv w v1 rest (i + 1)) with hL
  have hLl : L.length = rest.length := by simp [hL]
  have htW : (w ++ L).getD t false = w.getD t false := getD_app_left (by omega)
  rw [block_length]
  cases lead with
  | true =>
    simp only [blockGates, ↓reduceIte, List.foldl_append, hc, List.foldl_cons, List.foldl_nil,
      step]
    rw [getD_snoc']
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
      rw [htW, hr, hcvr]
      simp
    · simp [hLl, hw]
  | false =>
    have ha' : a < B := ha rfl
    simp only [blockGates, Bool.false_eq_true, ↓reduceIte, List.foldl_append, hc, List.foldl_cons,
      List.foldl_nil, step]
    rw [getD_snoc']
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
      rw [getD_app_left (by simp; omega), getD_app_left (by omega), getD_snoc']
      · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
        rw [htW, hr, hcvr]
        simp
      · simp [hLl, hw]
    · simp [hLl, hw]


def F (x : List Bool) (own : List (ℕ × List ℕ)) : Bool :=
  own.any (fun p => x.getD p.1 false && p.2.any (fun u => x.getD u false))

lemma gates_nil_F (x : List Bool) : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
    coverGatesB B lead a own = [] → F x own = false
  | [], _, _, _, _ => rfl
  | (t, []) :: os, B, lead, a, h => by
      simp only [coverGatesB] at h
      have := gates_nil_F x os B lead a h
      simp only [F, List.any_cons, List.any_nil, Bool.and_false, Bool.false_or] at this ⊢
      exact this
  | (t, v1 :: rest) :: os, B, lead, a, h => by
      simp only [coverGatesB] at h
      cases lead <;> simp [blockGates] at h

lemma main (n : ℕ) (x : List Bool) :
    ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ) (w : List Bool),
      (∀ p ∈ own, p.1 < n ∧ ∀ u ∈ p.2, u < n) → w.length = B → n ≤ B →
      (∀ i < n, w.getD i false = x.getD i false) → (lead = false → a < B) →
      coverGatesB B lead a own ≠ [] →
      ((coverGatesB B lead a own).foldl step w).getD
          (B + (coverGatesB B lead a own).length - 1) false
        = if lead then F x own else (w.getD a false || F x own)
  | [], _, _, _, _, _, _, _, _, _, hne => by simp [coverGatesB] at hne
  | (t, []) :: os, B, lead, a, w, hown, hw, hnB, hwx, ha, hne => by
      simp only [coverGatesB] at hne ⊢
      rw [main n x os B lead a w (fun p hp => hown p (List.mem_cons_of_mem _ hp)) hw hnB hwx ha
        hne]
      simp [F]
  | (t, v1 :: rest) :: os, B, lead, a, w, hown, hw, hnB, hwx, ha, _ => by
      have hp := hown (t, v1 :: rest) (by simp)
      have ht : t < n := hp.1
      have hv1 : v1 < n := hp.2 v1 (by simp)
      have hrest : ∀ u ∈ rest, u < n := fun u hu => hp.2 u (by simp [hu])
      have hos : ∀ p ∈ os, p.1 < n ∧ ∀ u ∈ p.2, u < n :=
        fun p hp => hown p (List.mem_cons_of_mem _ hp)
      have hbv := block_val w B a t v1 rest lead hw ha (by omega) (by omega)
        (fun u hu => by have := hrest u hu; omega)
      have hrx : rest.any (fun u => w.getD u false) = rest.any (fun u => x.getD u false) :=
        any_congr_mem (fun u hu => hwx u (hrest u hu))
      rw [hrx, hwx t ht, hwx v1 hv1] at hbv
      set bg := blockGates B a t v1 rest lead with hbg
      have hm : 0 < bg.length := by rw [hbg, block_length]; omega
      set W1 := bg.foldl step w with hW1
      have hW1l : W1.length = B + bg.length := by rw [hW1, fold_length, hw]
      have hW1x : ∀ i < n, W1.getD i false = x.getD i false := by
        intro i hi
        rw [hW1, fold_keep bg w (by omega)]
        exact hwx i hi
      have hW1a : lead = false → W1.getD a false = w.getD a false := by
        intro hl
        rw [hW1, fold_keep bg w (by have := ha hl; omega)]
      have hcons : F x ((t, v1 :: rest) :: os) =
          ((x.getD t false && (x.getD v1 false || rest.any (fun u => x.getD u false))) || F x os) :=
        rfl
      rw [hcons]
      simp only [coverGatesB]
      rw [← hbg, List.foldl_append, ← hW1, List.length_append]
      by_cases hnil : coverGatesB (B + bg.length) false (B + bg.length - 1) os = []
      · have hF := gates_nil_F x os _ false _ hnil
        rw [hnil, List.foldl_nil, List.length_nil, Nat.add_zero, hbv]
        rw [hF]
        cases lead <;> simp
      · have ih := main n x os (B + bg.length) false (B + bg.length - 1) W1 hos hW1l (by omega)
          hW1x (fun _ => by omega) hnil
        have hidx : B + (bg.length + (coverGatesB (B + bg.length) false (B + bg.length - 1) os).length) - 1
            = B + bg.length + (coverGatesB (B + bg.length) false (B + bg.length - 1) os).length - 1 := by
          omega
        rw [hidx, ih, hbv]
        cases lead <;> simp [Bool.or_assoc]

lemma circuit_fun (n : ℕ) (own : List (ℕ × List ℕ))
    (h : ∀ p ∈ own, p.1 < n ∧ ∀ w ∈ p.2, w < n) (x : Fin n → Bool) :
    ((coverCircuitB n own).eval (List.ofFn x) = true ↔
      ∃ p ∈ own, (List.ofFn x).getD p.1 false = true ∧
        ∃ w ∈ p.2, (List.ofFn x).getD w false = true) := by
  have hF : (∃ p ∈ own, (List.ofFn x).getD p.1 false = true ∧
        ∃ w ∈ p.2, (List.ofFn x).getD w false = true) ↔ F (List.ofFn x) own = true := by
    simp [F, List.any_eq_true]
  rw [hF]
  unfold coverCircuitB Circuit.eval
  split_ifs with hnil
  · rw [gates_nil_F _ own n true 0 hnil, wires_eq]
    simp [List.getD_eq_getElem?_getD]
  · rw [wires_eq]
    simp only
    rw [main n (List.ofFn x) own n true 0 (List.ofFn x) h (by simp) le_rfl (fun _ _ => rfl)
      (by simp) hnil]
    simp


lemma coverCircuitB_size_eq (n : ℕ) (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own, tx.2 ≠ []) :
    (coverCircuitB n own).size = (own.map (fun tx => tx.2.length)).sum + own.length - 1 := by
  by_cases hn : own = []
  · subst own
    simp [coverCircuitB,coverGatesB,Circuit.size]
  · have hs := circuit_size n own hn ho
    omega

lemma read_fin (n : ℕ) (z : Fin n → Bool) (i : Fin n) :
    (List.ofFn z).getD i.val false = z i := by
  simp [List.getD_eq_getElem?_getD]

lemma coverCircuitB_incidence (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop)
    [DecidableRel I] (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own,
      (tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np+Nl) ∨
      (Np ≤ tx.1 ∧ tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np))
    (hc : ∀ p l, I p l ↔ ∃ tx ∈ own,
      (tx.1 = p.val ∧ Np+l.val ∈ tx.2) ∨
      (tx.1 = Np+l.val ∧ p.val ∈ tx.2)) :
    ∀ z : Fin (Np+Nl) → Bool, circuitFun (Np+Nl) (coverCircuitB (Np+Nl) own) z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) := by
  have hb : ∀ tx ∈ own, tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np+Nl := by
    intro tx htx
    rcases ho tx htx with ⟨ht,hu⟩ | ⟨ht,ht',hu⟩
    · exact ⟨by omega,fun u h => (hu u h).2⟩
    · exact ⟨ht',fun u h => by have := hu u h; omega⟩
  intro z
  apply Bool.eq_iff_iff.mpr
  change ((coverCircuitB (Np+Nl) own).eval (List.ofFn z) = true) ↔ _
  rw [circuit_fun (Np+Nl) own hb z]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨tx,htx,ht,u,hu,huv⟩
    rcases ho tx htx with ⟨hleft,hr⟩ | ⟨hlo,hhi,hr⟩
    · obtain ⟨hul,huh⟩ := hr u hu
      let p : Fin Np := ⟨tx.1,hleft⟩
      let l : Fin Nl := ⟨u-Np,by omega⟩
      have he : Np+l.val = u := by dsimp [l]; omega
      have hI : I p l := (hc p l).mpr ⟨tx,htx,Or.inl ⟨rfl,he.symm ▸ hu⟩⟩
      have hp : (List.ofFn z).getD tx.1 false = z (Fin.castAdd Nl p) :=
        read_fin (Np+Nl) z (Fin.castAdd Nl p)
      have hl : (List.ofFn z).getD u false = z (Fin.natAdd Np l) := by
        have hh := read_fin (Np+Nl) z (Fin.natAdd Np l)
        simpa only [Fin.val_natAdd,he] using hh
      exact ⟨p,l,hI,hp.symm.trans ht,hl.symm.trans huv⟩
    · have hup := hr u hu
      let p : Fin Np := ⟨u,hup⟩
      let l : Fin Nl := ⟨tx.1-Np,by omega⟩
      have he : Np+l.val = tx.1 := by dsimp [l]; omega
      have hI : I p l := (hc p l).mpr ⟨tx,htx,Or.inr ⟨he.symm,hu⟩⟩
      have hp : (List.ofFn z).getD u false = z (Fin.castAdd Nl p) :=
        read_fin (Np+Nl) z (Fin.castAdd Nl p)
      have hl : (List.ofFn z).getD tx.1 false = z (Fin.natAdd Np l) := by
        have hh := read_fin (Np+Nl) z (Fin.natAdd Np l)
        simpa only [Fin.val_natAdd,he] using hh
      exact ⟨p,l,hI,hp.symm.trans huv,hl.symm.trans ht⟩
  · rintro ⟨p,l,hI,hp,hl⟩
    obtain ⟨tx,htx,h⟩ := (hc p l).mp hI
    have hpv : (List.ofFn z).getD p.val false = true :=
      (read_fin (Np+Nl) z (Fin.castAdd Nl p)).trans hp
    have hlv : (List.ofFn z).getD (Np+l.val) false = true :=
      (read_fin (Np+Nl) z (Fin.natAdd Np l)).trans hl
    rcases h with ⟨ht,hu⟩ | ⟨ht,hu⟩
    · exact ⟨tx,htx,ht ▸ hpv,Np+l.val,hu,hlv⟩
    · exact ⟨tx,htx,ht ▸ hlv,p.val,hu,hpv⟩

lemma normal_form_of_ownership (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop)
    [DecidableRel I] (C : Circuit) (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own, tx.2 ≠ [] ∧
      ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np+Nl) ∨
      (Np ≤ tx.1 ∧ tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np)))
    (hc : ∀ p l, I p l ↔ ∃ tx ∈ own,
      (tx.1 = p.val ∧ Np+l.val ∈ tx.2) ∨
      (tx.1 = Np+l.val ∧ p.val ∈ tx.2))
    (hb : (own.map (fun tx => tx.2.length)).sum + own.length - 1 ≤ C.size) :
    ∃ (D : Circuit) (P L : Finset ℕ), IsAO2 (Np+Nl) D ∧
      (∀ z : Fin (Np+Nl) → Bool, circuitFun (Np+Nl) D z =
        decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) ∧
      D.size ≤ C.size ∧
      (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np+Nl+i ∧
        (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ P) ∧
      (∀ w ∈ L, (Np ≤ w ∧ w < Np+Nl) ∨ ∃ i < D.gates.length, w = Np+Nl+i ∧
        (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ L) ∧
      ∀ i < D.gates.length, (gateAt D i).op = GateOp.and →
        ∃ a b, (gateAt D i).inputs = [a,b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  obtain ⟨P,L,hao,hP,hL,hands⟩ := coverCircuitB_twoLevel Np Nl own (fun tx htx => (ho tx htx).2)
  refine ⟨coverCircuitB (Np+Nl) own,P,L,hao,
    coverCircuitB_incidence Np Nl I own (fun tx htx => (ho tx htx).2) hc,?_,hP,hL,hands⟩
  rwa [coverCircuitB_size_eq (Np+Nl) own (fun tx htx => (ho tx htx).1)]

lemma point_ne_line (Np Nl : ℕ) (p : Fin Np) (l : Fin Nl) :
    Fin.castAdd Nl p ≠ Fin.natAdd Np l := by
  intro h
  have he := congrArg Fin.val h
  have hp := p.isLt
  simp only [Fin.val_castAdd,Fin.val_natAdd] at he
  omega

lemma point_essential (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
    (C : Circuit)
    (hfun : ∀ z : Fin (Np+Nl) → Bool, circuitFun (Np+Nl) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true))
    (p : Fin Np) (l : Fin Nl) (hI : I p l) :
    ∃ x : Fin (Np+Nl) → Bool,
      circuitFun (Np+Nl) C (Function.update x (Fin.castAdd Nl p) (!x (Fin.castAdd Nl p))) ≠
      circuitFun (Np+Nl) C x := by
  let x : Fin (Np+Nl) → Bool := fun i => decide (i = Fin.natAdd Np l)
  have hx (q : Fin Np) : x (Fin.castAdd Nl q) = false := by
    simp [x,point_ne_line Np Nl q l]
  have old : circuitFun (Np+Nl) C x = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    rw [hfun] at h
    obtain ⟨q,s,_,hq,_⟩ := of_decide_eq_true h
    rw [hx q] at hq
    contradiction
  have fresh : circuitFun (Np+Nl) C (Function.update x (Fin.castAdd Nl p) (!x (Fin.castAdd Nl p))) = true := by
    rw [hfun]
    apply decide_eq_true_iff.mpr
    refine ⟨p,l,hI,?_,?_⟩
    · simp [hx p]
    · rw [Function.update_of_ne (point_ne_line Np Nl p l).symm]
      simp [x]
  exact ⟨x,by rw [old,fresh]; decide⟩

lemma line_essential (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
    (C : Circuit)
    (hfun : ∀ z : Fin (Np+Nl) → Bool, circuitFun (Np+Nl) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true))
    (p : Fin Np) (l : Fin Nl) (hI : I p l) :
    ∃ x : Fin (Np+Nl) → Bool,
      circuitFun (Np+Nl) C (Function.update x (Fin.natAdd Np l) (!x (Fin.natAdd Np l))) ≠
      circuitFun (Np+Nl) C x := by
  let x : Fin (Np+Nl) → Bool := fun i => decide (i = Fin.castAdd Nl p)
  have hx (s : Fin Nl) : x (Fin.natAdd Np s) = false := by
    simp [x,(point_ne_line Np Nl p s).symm]
  have old : circuitFun (Np+Nl) C x = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    rw [hfun] at h
    obtain ⟨q,s,_,_,hs⟩ := of_decide_eq_true h
    rw [hx s] at hs
    contradiction
  have fresh : circuitFun (Np+Nl) C (Function.update x (Fin.natAdd Np l) (!x (Fin.natAdd Np l))) = true := by
    rw [hfun]
    apply decide_eq_true_iff.mpr
    refine ⟨p,l,hI,?_,?_⟩
    · rw [Function.update_of_ne (point_ne_line Np Nl p l)]
      simp [x]
    · simp [hx l]
  exact ⟨x,by rw [old,fresh]; decide⟩

lemma owner_vertices_incident (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop)
    [DecidableRel I] (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own, tx.2 ≠ [] ∧
      ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np+Nl) ∨
      (Np ≤ tx.1 ∧ tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np)))
    (hc : ∀ p l, I p l ↔ ∃ tx ∈ own,
      (tx.1 = p.val ∧ Np+l.val ∈ tx.2) ∨
      (tx.1 = Np+l.val ∧ p.val ∈ tx.2)) :
    ∀ w ∈ own.flatMap (fun tx => tx.1 :: tx.2),
      ∃ (p : Fin Np) (l : Fin Nl), I p l ∧ (w = p.val ∨ w = Np+l.val) := by
  intro w hw
  obtain ⟨tx,htx,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨hne,htag⟩ := ho tx htx
  obtain ⟨u,hu,hw⟩ : ∃ u ∈ tx.2, w = tx.1 ∨ w = u := by
    rcases List.mem_cons.mp hw with hw | hw
    · obtain ⟨u,hu⟩ := List.exists_mem_of_ne_nil _ hne
      exact ⟨u,hu,Or.inl hw⟩
    · exact ⟨w,hw,Or.inr rfl⟩
  rcases htag with ⟨ht,hr⟩ | ⟨ht,ht',hr⟩
  · obtain ⟨hul,huh⟩ := hr u hu
    let p : Fin Np := ⟨tx.1,ht⟩
    let l : Fin Nl := ⟨u-Np,by omega⟩
    have he : Np+l.val = u := by dsimp [l]; omega
    refine ⟨p,l,(hc p l).mpr ⟨tx,htx,Or.inl ⟨rfl,he.symm ▸ hu⟩⟩,?_⟩
    simpa only [p,Fin.val_mk,he] using hw
  · have hup := hr u hu
    let p : Fin Np := ⟨u,hup⟩
    let l : Fin Nl := ⟨tx.1-Np,by omega⟩
    have he : Np+l.val = tx.1 := by dsimp [l]; omega
    refine ⟨p,l,(hc p l).mpr ⟨tx,htx,Or.inr ⟨he.symm,hu⟩⟩,?_⟩
    simpa only [p,Fin.val_mk,he] using hw.symm

lemma owner_vertices_length (own : List (ℕ × List ℕ)) :
    (own.flatMap (fun tx => tx.1 :: tx.2)).length =
      (own.map (fun tx => tx.2.length)).sum + own.length := by
  induction own with
  | nil => simp
  | cons tx own ih => simp [ih]; omega

lemma disjoint_owner_support (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop)
    [DecidableRel I] (C : Circuit) (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own, tx.2 ≠ [] ∧
      ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np+Nl) ∨
      (Np ≤ tx.1 ∧ tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np)))
    (hc : ∀ p l, I p l ↔ ∃ tx ∈ own,
      (tx.1 = p.val ∧ Np+l.val ∈ tx.2) ∨
      (tx.1 = Np+l.val ∧ p.val ∈ tx.2))
    (hfun : ∀ z : Fin (Np+Nl) → Bool, circuitFun (Np+Nl) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true))
    (hn : (own.flatMap (fun tx => tx.1 :: tx.2)).Nodup) :
    ∃ S : Finset (Fin (Np+Nl)),
      S.card = (own.map (fun tx => tx.2.length)).sum + own.length ∧
      ∀ i ∈ S, ∃ x : Fin (Np+Nl) → Bool,
        circuitFun (Np+Nl) C (Function.update x i (!x i)) ≠ circuitFun (Np+Nl) C x := by
  let R := own.flatMap (fun tx => tx.1 :: tx.2)
  let T := R.toFinset
  let S : Finset (Fin (Np+Nl)) := Finset.univ.filter (fun i => i.val ∈ T)
  have hbound : ∀ w ∈ T, w < Np+Nl := by
    intro w hw
    obtain ⟨p,l,_,he⟩ := owner_vertices_incident Np Nl I own ho hc w (List.mem_toFinset.mp hw)
    have hp := p.isLt
    have hl := l.isLt
    rcases he with he | he <;> omega
  have heq : S.image Fin.val = T := by
    ext w
    constructor
    · intro hw
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hi).2
    · intro hw
      refine Finset.mem_image.mpr ⟨⟨w,hbound w hw⟩,?_,rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩
  have hcard : S.card = R.length := by
    calc
      S.card = T.card := by rw [← heq,Finset.card_image_of_injective _ Fin.val_injective]
      _ = R.length := List.toFinset_card_of_nodup hn
  refine ⟨S,?_,?_⟩
  · rw [hcard]
    exact owner_vertices_length own
  · intro i hi
    have hiR : i.val ∈ R := List.mem_toFinset.mp (Finset.mem_filter.mp hi).2
    obtain ⟨p,l,hI,he⟩ := owner_vertices_incident Np Nl I own ho hc i.val hiR
    rcases he with he | he
    · have hia : i = Fin.castAdd Nl p := Fin.ext he
      rw [hia]
      exact point_essential Np Nl I C hfun p l hI
    · have hia : i = Fin.natAdd Np l := Fin.ext he
      rw [hia]
      exact line_essential Np Nl I C hfun p l hI

lemma star_forest_budget (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop)
    [DecidableRel I] (C : Circuit) (own : List (ℕ × List ℕ))
    (ho : ∀ tx ∈ own, tx.2 ≠ [] ∧
      ((tx.1 < Np ∧ ∀ u ∈ tx.2, Np ≤ u ∧ u < Np+Nl) ∨
      (Np ≤ tx.1 ∧ tx.1 < Np+Nl ∧ ∀ u ∈ tx.2, u < Np)))
    (hc : ∀ p l, I p l ↔ ∃ tx ∈ own,
      (tx.1 = p.val ∧ Np+l.val ∈ tx.2) ∨
      (tx.1 = Np+l.val ∧ p.val ∈ tx.2))
    (hfun : ∀ z : Fin (Np+Nl) → Bool, circuitFun (Np+Nl) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true))
    (hn : (own.flatMap (fun tx => tx.1 :: tx.2)).Nodup)
    (lower : ∀ S : Finset (Fin (Np+Nl)),
      (∀ i ∈ S, ∃ x : Fin (Np+Nl) → Bool,
        circuitFun (Np+Nl) C (Function.update x i (!x i)) ≠ circuitFun (Np+Nl) C x) →
      S.card ≤ C.size+1) :
    (own.map (fun tx => tx.2.length)).sum + own.length - 1 ≤ C.size := by
  obtain ⟨S,hs,hdep⟩ := disjoint_owner_support Np Nl I C own ho hc hfun hn
  have h := lower S hdep
  omega

end PEqualNP.Outside.L_meta_2685_aux
