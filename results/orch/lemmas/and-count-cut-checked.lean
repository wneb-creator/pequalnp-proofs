import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970.TypedCompression

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def andGate (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | _ => false

def andNum (gs : List Gate) : ℕ := gs.countP andGate

lemma andGate_true (g : Gate) : andGate g = true ↔ g.op = GateOp.and := by
  cases g with
  | mk op ins => cases op <;> simp [andGate]

open Classical in
lemma andNum_filter (gs : List Gate) :
    andNum gs = ((Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or,[]⟩).op = GateOp.and).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil => simp [andNum]
  | append_singleton gs g ih =>
    have he : (gs ++ [g]).getD gs.length ⟨GateOp.or,[]⟩ = g := by
      simp [List.getD_eq_getElem?_getD]
    have hf : ((Finset.range gs.length).filter fun i =>
        ((gs ++ [g]).getD i ⟨GateOp.or,[]⟩).op = GateOp.and) =
        ((Finset.range gs.length).filter fun i =>
        (gs.getD i ⟨GateOp.or,[]⟩).op = GateOp.and) := by
      apply Finset.filter_congr
      intro i hi
      have hit : i < gs.length := Finset.mem_range.mp hi
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hit]
    rw [List.length_append,List.length_singleton,Finset.range_add_one,
      Finset.filter_insert,he,hf]
    have hn : gs.length ∉ ((Finset.range gs.length).filter fun i =>
        (gs.getD i ⟨GateOp.or,[]⟩).op = GateOp.and) := by simp
    have hc : andNum (gs ++ [g]) = andNum gs + [g].countP andGate := by simp [andNum]
    rw [hc,ih]
    by_cases hg : g.op = GateOp.and
    · have hb := (andGate_true g).mpr hg
      simp [hg,hb,Finset.card_insert_of_notMem hn]
    · have hb : andGate g = false := by
        cases he : andGate g
        · rfl
        · exact False.elim (hg ((andGate_true g).mp he))
      simp [hg,hb]

open Classical in
lemma andNum_deleted_lt (C : Circuit) (gs : List Gate) (j : ℕ)
    (hj : j < C.gates.length) (hAND : (gateAt C j).op = GateOp.and)
    (hbound : andNum gs ≤ ((Finset.range C.gates.length).filter fun i =>
      (gateAt C i).op = GateOp.and ∧ i ∉ ({j} : Finset ℕ)).card) :
    andNum gs < andNum C.gates := by
  classical
  let S := (Finset.range C.gates.length).filter fun i => (gateAt C i).op = GateOp.and
  have hjS : j ∈ S := by simp [S,hj,hAND]
  have hfilter : ((Finset.range C.gates.length).filter fun i =>
      (gateAt C i).op = GateOp.and ∧ i ∉ ({j} : Finset ℕ)) = S.erase j := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton,
      Finset.mem_erase,S]
    tauto
  have hcount : S.card = andNum C.gates := by
    rw [andNum_filter]
    rfl
  rw [hfilter] at hbound
  have hc := Finset.card_erase_add_one hjS
  omega

lemma andNum_join_or (gs : List Gate) (s t : ℕ) :
    andNum (gs ++ [⟨GateOp.or,[s,t]⟩]) = andNum gs := by
  simp [andNum,andGate]

end PEqualNP.Outside.L_meta_4970.TypedCompression
