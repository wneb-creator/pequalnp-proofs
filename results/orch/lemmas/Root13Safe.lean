import KernelFirstTables
import RootShardAdapter
namespace PEqualNP.Outside.L_meta_10760_first
def root13Q : List (Nat × Nat) := pick acc_extraFive [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
lemma root13Q_bounds : ∀ e ∈ root13Q, Imp [] e.1 e.2 := pickI accBounds_extraFive
def masks13 : List (Nat × Nat) := [(0, 1), (((2 ^ 26 - 1) <<< 0), 0), (((2 ^ 27 - 1) <<< 26), 0), (((2 ^ 27 - 1) <<< 53), 0), (((2 ^ 27 - 1) <<< 80), 0), (((2 ^ 26 - 1) <<< 107), 0), (((2 ^ 27 - 1) <<< 133), 0), (((2 ^ 27 - 1) <<< 160), 0), (((2 ^ 27 - 1) <<< 187), 0)]
def masks13_full : mFull masks13 = true := by decide +kernel
noncomputable def run13 (p : Nat × Nat) : Bool := chkT topC [] root13Q (1, 0) 0 12 (List.range 13) p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shard13_0 : run13 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shard13_1 : run13 (((2 ^ 26 - 1) <<< 0), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shard13_2 : run13 (((2 ^ 27 - 1) <<< 26), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shard13_3 : run13 (((2 ^ 27 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shard13_4 : run13 (((2 ^ 27 - 1) <<< 80), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shard13_5 : run13 (((2 ^ 26 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shard13_6 : run13 (((2 ^ 27 - 1) <<< 133), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shard13_7 : run13 (((2 ^ 27 - 1) <<< 160), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shard13_8 : run13 (((2 ^ 27 - 1) <<< 187), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma bound13 : Imp [] 0 13 := by
  have hc : ∀ p ∈ masks13, run13 p = false := by
    intro p hp
    simp only [masks13, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact shard13_0
    · exact shard13_1
    · exact shard13_2
    · exact shard13_3
    · exact shard13_4
    · exact shard13_5
    · exact shard13_6
    · exact shard13_7
    · exact shard13_8
  exact root13_of_shards root13Q_bounds (by decide +kernel) masks13_full hc
end PEqualNP.Outside.L_meta_10760_first
