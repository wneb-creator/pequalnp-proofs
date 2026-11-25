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

end PEqualNP.Outside.L_meta_2583
