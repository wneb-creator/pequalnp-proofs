import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_231_aux

def edgeEnds : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def canonicalEdges : Fin 3 → Fin 3 → Fin 6 :=
  ![![0,1,2], ![0,1,3], ![0,3,5]]

def SameUnorderedEnds (a b : Fin 4 × Fin 4) : Prop :=
  (a.1 = b.1 ∧ a.2 = b.2) ∨ (a.1 = b.2 ∧ a.2 = b.1)

noncomputable def orbitVertex : Fin 24 → Equiv.Perm (Fin 4) :=
  ![
    Equiv.ofBijective (![0, 1, 2, 3] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![0, 1, 3, 2] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![0, 2, 1, 3] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![0, 2, 3, 1] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![0, 3, 1, 2] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![0, 3, 2, 1] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![1, 0, 2, 3] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![1, 0, 3, 2] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![1, 2, 0, 3] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![1, 2, 3, 0] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![1, 3, 0, 2] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![1, 3, 2, 0] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![2, 0, 1, 3] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![2, 0, 3, 1] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![2, 1, 0, 3] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![2, 1, 3, 0] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![2, 3, 0, 1] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![2, 3, 1, 0] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![3, 0, 1, 2] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![3, 0, 2, 1] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![3, 1, 0, 2] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![3, 1, 2, 0] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![3, 2, 0, 1] : Fin 4 → Fin 4) (by decide),
    Equiv.ofBijective (![3, 2, 1, 0] : Fin 4 → Fin 4) (by decide)]

noncomputable def orbitCoordinate : Fin 6 → Equiv.Perm (Fin 3) :=
  ![
    Equiv.ofBijective (![0, 1, 2] : Fin 3 → Fin 3) (by decide),
    Equiv.ofBijective (![0, 2, 1] : Fin 3 → Fin 3) (by decide),
    Equiv.ofBijective (![1, 0, 2] : Fin 3 → Fin 3) (by decide),
    Equiv.ofBijective (![1, 2, 0] : Fin 3 → Fin 3) (by decide),
    Equiv.ofBijective (![2, 0, 1] : Fin 3 → Fin 3) (by decide),
    Equiv.ofBijective (![2, 1, 0] : Fin 3 → Fin 3) (by decide)]

def orbitWitness : Fin 6 → Fin 6 → Fin 6 → Fin 24 × Fin 6 × Fin 3 :=
  ![
    ![![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,1), (8,2,2), (6,0,2)], ![(0,0,0), (0,1,0), (0,0,0), (9,2,2), (1,0,1), (7,0,2)], ![(0,0,0), (0,1,1), (9,4,2), (0,0,0), (6,0,0), (0,0,2)], ![(0,0,0), (8,4,2), (1,1,1), (6,1,0), (0,0,0), (1,0,2)], ![(0,0,0), (6,1,2), (7,1,2), (0,1,2), (1,1,2), (0,0,0)]],
    ![![(0,0,0), (0,0,0), (0,2,0), (0,2,1), (8,0,2), (6,2,2)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(0,4,0), (0,0,0), (0,0,0), (11,2,2), (10,0,2), (4,0,1)], ![(0,4,1), (0,0,0), (11,4,2), (0,0,0), (2,0,2), (8,0,0)], ![(8,1,2), (0,0,0), (10,1,2), (2,1,2), (0,0,0), (4,1,2)], ![(6,4,2), (0,0,0), (4,1,1), (8,1,0), (4,0,2), (0,0,0)]],
    ![![(0,0,0), (0,3,0), (0,0,0), (9,0,2), (1,2,1), (7,2,2)], ![(0,5,0), (0,0,0), (0,0,0), (11,0,2), (10,2,2), (4,2,1)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(9,1,2), (11,1,2), (0,0,0), (0,0,0), (3,1,2), (5,1,2)], ![(1,4,1), (10,4,2), (0,0,0), (3,0,2), (0,0,0), (9,0,0)], ![(7,4,2), (4,4,1), (0,0,0), (5,0,2), (9,1,0), (0,0,0)]],
    ![![(0,0,0), (0,3,1), (9,5,2), (0,0,0), (6,2,0), (0,2,2)], ![(0,5,1), (0,0,0), (11,5,2), (0,0,0), (2,2,2), (8,2,0)], ![(9,3,2), (11,3,2), (0,0,0), (0,0,0), (3,3,2), (5,3,2)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(6,4,0), (2,4,2), (3,5,2), (0,0,0), (0,0,0), (18,0,1)], ![(0,4,2), (8,4,0), (5,5,2), (0,0,0), (18,1,1), (0,0,0)]],
    ![![(0,0,0), (8,5,2), (1,3,1), (6,3,0), (0,0,0), (1,2,2)], ![(8,3,2), (0,0,0), (10,3,2), (2,3,2), (0,0,0), (4,3,2)], ![(1,5,1), (10,5,2), (0,0,0), (3,2,2), (0,0,0), (9,2,0)], ![(6,5,0), (2,5,2), (3,4,2), (0,0,0), (0,0,0), (18,2,1)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(1,4,2), (4,5,2), (9,4,0), (18,4,1), (0,0,0), (0,0,0)]],
    ![![(0,0,0), (6,3,2), (7,3,2), (0,3,2), (1,3,2), (0,0,0)], ![(6,5,2), (0,0,0), (4,3,1), (8,3,0), (4,2,2), (0,0,0)], ![(7,5,2), (4,5,1), (0,0,0), (5,2,2), (9,3,0), (0,0,0)], ![(0,5,2), (8,5,0), (5,4,2), (0,0,0), (18,3,1), (0,0,0)], ![(1,5,2), (4,4,2), (9,5,0), (18,5,1), (0,0,0), (0,0,0)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem orbitWitness_valid :
    ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c → ∀ k : Fin 3,
      let w := orbitWitness a b c
      let p := orbitVertex w.1
      let q := orbitCoordinate w.2.1
      SameUnorderedEnds
        (p (edgeEnds (![a,b,c] (q k))).1, p (edgeEnds (![a,b,c] (q k))).2)
        (edgeEnds (canonicalEdges w.2.2 k)) := by
  unfold SameUnorderedEnds
  decide

theorem three_edge_orbits :
    ∀ pick : Fin 3 → Fin 6, Function.Injective pick →
      ∃ p : Equiv.Perm (Fin 4), ∃ q : Equiv.Perm (Fin 3), ∃ kind : Fin 3,
        ∀ k : Fin 3, SameUnorderedEnds
          (p (edgeEnds (pick (q k))).1, p (edgeEnds (pick (q k))).2)
          (edgeEnds (canonicalEdges kind k)) := by
  intro pick hi
  let w := orbitWitness (pick 0) (pick 1) (pick 2)
  refine ⟨orbitVertex w.1, orbitCoordinate w.2.1, w.2.2, ?_⟩
  have h01 : pick 0 ≠ pick 1 := fun h => by have := hi h; contradiction
  have h02 : pick 0 ≠ pick 2 := fun h => by have := hi h; contradiction
  have h12 : pick 1 ≠ pick 2 := fun h => by have := hi h; contradiction
  have hv : ![pick 0, pick 1, pick 2] = pick := by
    funext k
    fin_cases k <;> rfl
  intro k
  simpa only [hv] using orbitWitness_valid (pick 0) (pick 1) (pick 2) h01 h02 h12 k

end PEqualNP.Outside.L_gct_231_aux
