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

end PEqualNP.Outside.L_meta_2685_aux
