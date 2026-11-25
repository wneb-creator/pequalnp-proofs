import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.augmented

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

abbrev graph : SimpleGraph (Fin 12) := edgeGraph 12
  [(0,1),(2,3),(0,4),(2,4),(0,5),(3,5),(1,6),(2,6),(1,7),(3,7),
   (4,8),(5,9),(6,10),(7,11)]

def hybrid : Circuit := ⟨[
  ⟨.or,[0,2]⟩, ⟨.or,[0,3]⟩, ⟨.or,[1,2]⟩, ⟨.or,[1,3]⟩,
  ⟨.and,[12,13]⟩, ⟨.and,[14,15]⟩, ⟨.and,[16,17]⟩,
  ⟨.or,[12,8]⟩, ⟨.and,[4,19]⟩,
  ⟨.or,[13,9]⟩, ⟨.and,[5,21]⟩,
  ⟨.or,[14,10]⟩, ⟨.and,[6,23]⟩,
  ⟨.or,[15,11]⟩, ⟨.and,[7,25]⟩,
  ⟨.or,[18,20]⟩, ⟨.or,[27,22]⟩, ⟨.or,[28,24]⟩, ⟨.or,[29,26]⟩],30⟩

def repaired : Circuit := ⟨[
  ⟨.or,[0,2]⟩, ⟨.or,[0,3]⟩, ⟨.or,[1,2]⟩, ⟨.or,[1,3]⟩,
  ⟨.and,[0,1]⟩, ⟨.and,[2,3]⟩, ⟨.or,[16,17]⟩,
  ⟨.or,[12,8]⟩, ⟨.and,[4,19]⟩,
  ⟨.or,[13,9]⟩, ⟨.and,[5,21]⟩,
  ⟨.or,[14,10]⟩, ⟨.and,[6,23]⟩,
  ⟨.or,[15,11]⟩, ⟨.and,[7,25]⟩,
  ⟨.or,[18,20]⟩, ⟨.or,[27,22]⟩, ⟨.or,[28,24]⟩, ⟨.or,[29,26]⟩],30⟩

lemma hybrid_size : hybrid.size = 19 := rfl
lemma repaired_size : repaired.size = hybrid.size := rfl

lemma hybrid_mono : Monotone2 hybrid := by
  simp [Monotone2, hybrid]

lemma repaired_mono : Monotone2 repaired := by
  simp [Monotone2, repaired]


end PEqualNP.Outside.L_meta_1772_aux.augmented
