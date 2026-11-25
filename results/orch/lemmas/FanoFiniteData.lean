import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.Fano

def fanoEdges : Finset (Fin 7 × Fin 7) :=
  {(0, 1), (0, 3), (0, 5), (1, 0), (1, 3), (1, 4), (2, 2), (2, 3), (2, 6), (3, 0), (3, 1), (3, 2), (4, 1), (4, 4), (4, 6), (5, 0), (5, 5), (5, 6), (6, 2), (6, 4), (6, 5)}

abbrev fanoInc (p l : Fin 7) : Prop := (p, l) ∈ fanoEdges

theorem fanoEdgeCard : fanoEdges.card = 21 := by decide

theorem fanoLineDegree : ∀ l : Fin 7,
    (Finset.univ.filter fun p => fanoInc p l).card = 3 := by decide

theorem fanoPointDegree : ∀ p : Fin 7,
    (Finset.univ.filter fun l => fanoInc p l).card = 3 := by decide

theorem fanoUniqueLine : ∀ p p' : Fin 7, p ≠ p' →
    ∃! l : Fin 7, fanoInc p l ∧ fanoInc p' l := by
  have hc : ∀ p p' : Fin 7, p ≠ p' →
      (Finset.univ.filter fun l => fanoInc p l ∧ fanoInc p' l).card = 1 := by decide
  intro p p' hpp
  obtain ⟨l, hl⟩ := Finset.card_eq_one.mp (hc p p' hpp)
  refine ⟨l, ?_, ?_⟩
  · have hm : l ∈ Finset.univ.filter (fun k => fanoInc p k ∧ fanoInc p' k) := by
      rw [hl]
      exact Finset.mem_singleton_self l
    exact (Finset.mem_filter.mp hm).2
  · intro m hm
    have hmem : m ∈ Finset.univ.filter (fun k => fanoInc p k ∧ fanoInc p' k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩
    rw [hl] at hmem
    exact Finset.mem_singleton.mp hmem

theorem fanoNoRectangle : ∀ p p' l l' : Fin 7, p ≠ p' → l ≠ l' →
    ¬ (fanoInc p l ∧ fanoInc p l' ∧ fanoInc p' l ∧ fanoInc p' l') := by
  intro p p' l l' hpp hll h
  obtain ⟨a, _, hu⟩ := fanoUniqueLine p p' hpp
  exact hll ((hu l ⟨h.1, h.2.2.1⟩).trans (hu l' ⟨h.2.1, h.2.2.2⟩).symm)

def fanoMatch (p : Fin 7) : Fin 7 :=
  match p.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 4
  | 5 => 6
  | _ => 5

theorem fanoMatchInvolutive : Function.Involutive fanoMatch := by
  unfold Function.Involutive
  decide

def fanoPerm : Equiv.Perm (Fin 7) where
  toFun := fanoMatch
  invFun := fanoMatch
  left_inv := fanoMatchInvolutive
  right_inv := fanoMatchInvolutive

theorem fanoMatching : ∀ p : Fin 7, fanoInc p (fanoPerm p) := by decide

end PEqualNP.Outside.L_meta_2583_aux.Fano
