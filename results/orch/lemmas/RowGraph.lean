import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502

def adjGraph : Fin 33 → Fin 33 → Bool := (fun a b : Fin 33 => decide (∃ i : Fin 11, ((a.val = i.val ∨ a.val = 11 + i.val) ∧ (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨ ((b.val = i.val ∨ b.val = 11 + i.val) ∧ (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val))))

def adjRows : List Nat :=
  [6292482, 8390661, 16781322, 33562644, 67125288, 134250576, 268501152, 537002304, 1074004608, 2148009216, 4296016385, 4194306, 8388612, 16777224, 33554448, 67108896, 134217792, 268435584, 536871168, 1073742336, 2147484672, 4294967297, 2049, 4098, 8196, 16392, 32784, 65568, 131136, 262272, 524544, 1049088, 2098176]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma adjRows_correct : ∀ a b : Fin 33,
    (BitVec.ofNat 33 (adjRows.getD a.val 0)).getLsbD b.val = adjGraph a b := by
  decide +kernel

end PEqualNP.Outside.L_meta_9502
