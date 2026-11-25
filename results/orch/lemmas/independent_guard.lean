import map_rigidity

namespace PEqualNP.Outside.L_meta_1886_aux.IndependentGuard

open MapRigidity

def maximalMasks : List (Fin 1024) :=
  [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]

def row (m : Fin 1024) (i : Fin 10) : Bool := m.val.testBit i.val

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma maximal_masks_false : ∀ m ∈ maximalMasks, edge10 (row m) = false := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma independent_extension : ∀ x : Fin 10 → Bool, edge10 x = false →
    ∃ m ∈ maximalMasks, ∀ i : Fin 10, x i ≤ row m i := by
  decide +kernel

lemma maximal_guard_witness (g : (Fin 10 → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i ≤ y i) → g x ≤ g y)
    (notDominated : ¬ ∀ x, g x ≤ edge10 x) :
    ∃ m ∈ maximalMasks, g (row m) = true ∧ edge10 (row m) = false := by
  obtain ⟨x,hx⟩ := not_forall.mp notDominated
  have gx : g x = true := by
    cases h : g x <;> simp_all [Bool.le_iff_imp]
  have fx : edge10 x = false := by
    cases h : edge10 x <;> simp_all [Bool.le_iff_imp]
  obtain ⟨m,hm,extension⟩ := independent_extension x fx
  have lower := mono x (row m) extension
  have gm : g (row m) = true := by
    cases h : g (row m) <;> simp_all [Bool.le_iff_imp]
  exact ⟨m,hm,gm,maximal_masks_false m hm⟩

lemma dominated_iff_maximal_false (g : (Fin 10 → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i ≤ y i) → g x ≤ g y) :
    (∀ x, g x ≤ edge10 x) ↔ ∀ m ∈ maximalMasks, g (row m) = false := by
  constructor
  · intro dominated m hm
    have h := dominated (row m)
    rw [maximal_masks_false m hm] at h
    cases hgm : g (row m) <;> simp_all [Bool.le_iff_imp]
  · intro noWitness
    by_contra hn
    obtain ⟨m,hm,yes,_⟩ := maximal_guard_witness g mono hn
    rw [noWitness m hm] at yes
    cases yes

end PEqualNP.Outside.L_meta_1886_aux.IndependentGuard
