import Mono18RectangleLookup
import Mono18RectangleBank
import Mono18RectangleLabels
import Mono18RectangleTotals

namespace PEqualNP.Outside.L_meta_2373.Mono18Rectangle9611

open Live1024 Mono18Rectangle

def signal : Fin 12 → Sig := ![
  0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,
  0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee]

def record : Fin 12 → Nat := ![0x11d6e8031,0x126f70043,0x11bba8086,0x135e5810c,0x13e9b0218,0x133f94420,0x13fc8b040,0x13e478c80,0x10e3fe100,0x2192a80b7,0x201ff9b00,0x200661b73]
def labels9611 : Fin 12 → List (Fin 12) := ![
  [0,0,0,1,2,2,3,4,5,6,7,8,10,11,11],
  [0,0,1,1,2,2,3,4,5,6,7,8,10,11,11],
  [0,0,1,2,2,2,3,4,5,6,7,8,10,11,11],
  [0,0,1,2,2,3,3,4,5,6,7,8,10,11,11],
  [0,0,1,2,2,3,4,4,5,6,7,8,10,11,11],
  [0,0,1,2,2,3,4,5,5,6,7,8,10,11,11],
  [0,0,1,2,2,3,4,5,6,6,7,8,10,11,11],
  [0,0,1,2,2,3,4,5,6,7,7,8,10,11,11],
  [0,0,1,2,2,3,4,5,6,7,8,8,10,11,11],
  [0,0,1,2,2,3,4,5,6,7,8,10,10,11,11],
  [0,0,1,2,2,3,4,5,6,7,8,10,11,11,11],
  [0,1,2,3,4,5,6,7,8,9,9,10,11,11]]

def childSignals9611 (i : Fin 12) : List Sig := (labels9611 i).map signal
def childPairs9611 (i : Fin 12) : List (Sig × Nat) :=
  (labels9611 i).map (fun j => (signal j, record j))

lemma record_valid : ∀ i : Fin 12, checkRecord 0 (record i) = true := by
  intro i; fin_cases i
  · exact certifiedAt_valid 3 49
  · exact certifiedAt_valid 4 30
  · exact certifiedAt_valid 6 33
  · exact certifiedAt_valid 9 25
  · exact certifiedAt_valid 13 6
  · exact certifiedAt_valid 38 57
  · exact certifiedAt_valid 31 20
  · exact certifiedAt_valid 20 26
  · exact certifiedAt_valid 45 24
  · exact certifiedAt_valid 7 35
  · exact certifiedAt_valid 27 18
  · exact certifiedAt_valid 27 53

lemma support_valid : ∀ i : Fin 12, supportCheck 0 (record i) (signal i) = true := by
  intro i; fin_cases i <;> decide +kernel

lemma cost_gap : ∀ i : Fin 12,
    ((childPairs9611 i).map (fun a => recordCap (matrixWeight 0) a.2)).sum <
      weightTotals.getD (matrixWeight 0) 0 := by
  decide +kernel

lemma gap (i : Fin 12) :
    ((childPairs9611 i).map (fun a => recordCap (matrixWeight 0) a.2)).sum < targetCost 0 := by
  rw [targetCost_eq (0 : Fin 39)]
  exact cost_gap i

lemma child_cut9611 (i : Fin 12) {k : Nat}
    (cap : k + 1 ≤ (childSignals9611 i).length) :
    ¬ Run false (observe graph) k ((childSignals9611 i).map observe) := by
  intro trace
  apply run_exclusion_of_records 0 (childPairs9611 i) _ _
    (sample_positive 0) (sample_negative 0) (gap i)
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    exact record_valid j
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    exact support_valid j
  · simpa only [childPairs9611, childSignals9611, List.length_map] using cap
  · simpa only [childPairs9611, childSignals9611, List.map_map] using trace

end PEqualNP.Outside.L_meta_2373.Mono18Rectangle9611
