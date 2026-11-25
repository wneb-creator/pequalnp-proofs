import Mono18RectangleLookup
import Mono18RectangleBank
import Mono18RectangleLabels

namespace PEqualNP.Outside.L_meta_2373.Mono18RectangleNode38

open Live1024 Mono18Rectangle

def raw : Fin 12 → Sig := ![
  0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,
  0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa]

def record : Fin 12 → Nat := ![0x11d6e8031,0x126f70043,0x11bba8086,0x135e5810c,0x13e9b0218,0x133f94420,0x13fc8b040,0x13e478c80,0x10e3fe100,0x101ff9a00,0x104660073,0x2192a80b7]
def labels : List (Fin 12) := [0,1,2,3,3,3,4,5,5,6,6,7,8,9,10,11,11]
def rootPairs : List (Sig × Nat) := labels.map (fun i => (raw i, record i))

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
  · exact certifiedAt_valid 25 23
  · exact certifiedAt_valid 5 13
  · exact certifiedAt_valid 7 35

lemma support_valid : ∀ i : Fin 12, supportCheck 0 (record i) (raw i) = true := by
  intro i; fin_cases i <;> decide +kernel

lemma gap : (rootPairs.map (fun a => recordCap (matrixWeight 0) a.2)).sum < targetCost 0 := by
  decide +kernel

lemma run_exclusion {k : Nat} (cap : k ≤ 16)
    (trace : Run false (observe graph) k (rootPairs.map (fun a => observe a.1))) : False := by
  apply run_exclusion_of_records 0 rootPairs _ _ (sample_positive 0) (sample_negative 0) gap _ trace
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact record_valid i
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact support_valid i
  · change k + 1 ≤ 17
    omega

end PEqualNP.Outside.L_meta_2373.Mono18RectangleNode38
