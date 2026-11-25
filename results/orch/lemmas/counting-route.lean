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

end PEqualNP.Outside.L_meta_2685_aux
