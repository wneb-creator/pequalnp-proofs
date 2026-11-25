import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

abbrev fanoIncidence (p l : Fin 7) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3

lemma fano_columns : ∀ l : Fin 7,
    (Finset.univ.filter fun p => fanoIncidence p l).card = 2 + 1 := by
  decide

lemma fano_unique_line : ∀ p p' : Fin 7, p ≠ p' →
    ∃! l : Fin 7, fanoIncidence p l ∧ fanoIncidence p' l := by
  unfold ExistsUnique
  decide

def fanoStarCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [14, 3]⟩, ⟨.and, [15, 7]⟩,
    ⟨.or, [1, 2]⟩, ⟨.or, [17, 4]⟩, ⟨.and, [18, 8]⟩,
    ⟨.or, [2, 3]⟩, ⟨.or, [20, 5]⟩, ⟨.and, [21, 9]⟩,
    ⟨.or, [3, 4]⟩, ⟨.or, [23, 6]⟩, ⟨.and, [24, 10]⟩,
    ⟨.or, [0, 4]⟩, ⟨.or, [26, 5]⟩, ⟨.and, [27, 11]⟩,
    ⟨.or, [1, 5]⟩, ⟨.or, [29, 6]⟩, ⟨.and, [30, 12]⟩,
    ⟨.or, [0, 2]⟩, ⟨.or, [32, 6]⟩, ⟨.and, [33, 13]⟩,
    ⟨.or, [16, 19]⟩, ⟨.or, [35, 22]⟩, ⟨.or, [36, 25]⟩,
    ⟨.or, [37, 28]⟩, ⟨.or, [38, 31]⟩, ⟨.or, [39, 34]⟩], 40⟩

lemma fanoStarCircuit_size : fanoStarCircuit.size = 27 := rfl

lemma fanoStarCircuit_ao : PEqualNP.TopForm.IsAO2 14 fanoStarCircuit := by
  decide

set_option maxRecDepth 10000 in
lemma fanoStarCircuit_reads_pair : ∀ p l : Fin 7, fanoIncidence p l →
    PEqualNP.ReadK.readsAtMost fanoStarCircuit 14 [p.val, 7 + l.val] 1 = true := by
  decide

lemma fano_bool_identity (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : Bool) :
    (((a0 || a1 || a3) && a7 || (a1 || a2 || a4) && a8 ||
      (a2 || a3 || a5) && a9 || (a3 || a4 || a6) && a10 ||
      (a0 || a4 || a5) && a11 || (a1 || a5 || a6) && a12 ||
      (a0 || a2 || a6) && a13)) =
    (a0 && a7 || (a0 && a11 || a0 && a13) ||
      (a1 && a8 || (a1 && a7 || a1 && a12) ||
        (a2 && a9 || (a2 && a8 || a2 && a13) ||
          (a3 && a10 || (a3 && a7 || a3 && a9) ||
            (a4 && a11 || (a4 && a8 || a4 && a10) ||
              (a5 && a12 || (a5 && a9 || a5 && a11) ||
                (a6 && a13 || (a6 && a10 || a6 && a12)))))))) := by
  simp only [Bool.and_or_distrib_right]
  ac_rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma fanoStarCircuit_eval (z : Fin 14 → Bool) :
    PEqualNP.MetaComplexity.circuitFun 14 fanoStarCircuit z =
    decide (∃ p l : Fin 7, fanoIncidence p l ∧
      z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true) := by
  simp [fanoStarCircuit, PEqualNP.MetaComplexity.circuitFun,
    PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
    PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ, Fin.exists_fin_succ,
    fanoIncidence]
  exact fano_bool_identity (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6)
    (z 7) (z 8) (z 9) (z 10) (z 11) (z 12) (z 13)

lemma fano_pair_setList : ∀ p l : Fin 7,
    PEqualNP.ReadK.setList ({Fin.castAdd 7 p, Fin.natAdd 7 l} : Finset (Fin 14)) =
    [p.val, 7 + l.val] := by
  decide

lemma fanoStarCircuit_read1 : PEqualNP.ReadK.IsReadK 14 fanoStarCircuit 1 := by
  intro S hs
  have hon := hs.1
  rw [fanoStarCircuit_eval] at hon
  obtain ⟨p, l, hi, hp, hl⟩ := of_decide_eq_true hon
  have hp' : Fin.castAdd 7 p ∈ S := of_decide_eq_true hp
  have hl' : Fin.natAdd 7 l ∈ S := of_decide_eq_true hl
  let T : Finset (Fin 14) := {Fin.castAdd 7 p, Fin.natAdd 7 l}
  have hsub : T ⊆ S := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hp'
    · exact (Finset.mem_singleton.mp hi) ▸ hl'
  have ht : PEqualNP.MetaComplexity.circuitFun 14 fanoStarCircuit
      (PEqualNP.ReadK.setInput T) = true := by
    rw [fanoStarCircuit_eval]
    apply decide_eq_true
    refine ⟨p, l, hi, ?_, ?_⟩ <;> simp [PEqualNP.ReadK.setInput, T]
  have heq : T = S := by
    by_contra hne
    have hstrict : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    have hoff := hs.2 T (Finset.mem_ssubsets.mpr hstrict)
    exact Bool.noConfusion (ht.symm.trans hoff)
  rw [← heq, fano_pair_setList p l]
  exact fanoStarCircuit_reads_pair p l hi

end PEqualNP.Outside.L_meta_2583
