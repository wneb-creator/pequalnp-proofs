import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Binary17
abbrev Sig := BitVec 512
def zero : Sig := 0
abbrev Row := Fin 512
def bit (r : Row) (a : Sig) : Bool := a.getLsbD r.val
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
namespace Extended
abbrev Sig := BitVec 1024
def zero : Sig := 0
abbrev Row := Fin 1024
def bit (r : Row) (a : Sig) : Bool := a.getLsbD r.val
def pins : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc]
def initial : List Sig := pins
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
end Extended

def pinAt (i : Fin 10) : Extended.Sig := Extended.pins.getD i.val Extended.zero
def pinPosition (i : Fin 10) : Nat := ![9,7,5,8,6,4,2,0,3,1] i
def sourcePosition (i j : Fin 10) : Nat :=
  ![![9,7,5,8,6,4,2,0,3,1],
    ![7,9,6,8,5,2,4,1,3,0],
    ![5,7,9,6,8,0,2,4,1,3],
    ![8,5,7,9,6,3,0,2,4,1],
    ![7,5,8,6,9,2,0,3,1,4],
    ![7,5,8,3,2,9,0,6,4,1],
    ![5,7,2,1,0,8,9,3,6,4],
    ![8,5,7,2,3,6,0,9,1,4],
    ![1,0,5,7,2,6,4,8,9,3],
    ![5,8,3,2,7,0,6,4,1,9]] i j
def permutedRow (i : Fin 10) (r : Nat) : Nat :=
  ![r,
    ((r &&& 16) >>> 2) ||| ((r &&& 66) >>> 1) ||| (r &&& 264) ||| ((r &&& 33) <<< 1) ||| ((r &&& 132) <<< 2),
    ((r &&& 16) >>> 4) ||| ((r &&& 264) >>> 2) ||| (r &&& 132) ||| ((r &&& 66) <<< 2) ||| ((r &&& 33) <<< 4),
    ((r &&& 132) >>> 2) ||| ((r &&& 16) >>> 1) ||| (r &&& 66) ||| ((r &&& 264) <<< 1) ||| ((r &&& 33) <<< 2),
    ((r &&& 280) >>> 3) ||| ((r &&& 231) <<< 2),
    ((r &&& 64) >>> 6) ||| ((r &&& 256) >>> 3) ||| ((r &&& 16) >>> 1) ||| (r &&& 2) ||| ((r &&& 161) <<< 2) ||| ((r &&& 4) <<< 4) ||| ((r &&& 8) <<< 5),
    ((r &&& 256) >>> 4) ||| ((r &&& 88) >>> 3) ||| (r &&& 128) ||| ((r &&& 4) <<< 3) ||| ((r &&& 32) <<< 4) ||| ((r &&& 1) <<< 6) ||| ((r &&& 2) <<< 7),
    ((r &&& 16) >>> 3) ||| ((r &&& 192) >>> 2) ||| ((r &&& 256) <<< 1) ||| ((r &&& 35) <<< 2) ||| ((r &&& 8) <<< 3) ||| ((r &&& 4) <<< 6),
    ((r &&& 256) >>> 8) ||| ((r &&& 88) >>> 2) ||| (r &&& 32) ||| ((r &&& 128) <<< 1) ||| ((r &&& 4) <<< 4) ||| ((r &&& 1) <<< 7) ||| ((r &&& 2) <<< 8),
    ((r &&& 80) >>> 4) ||| ((r &&& 384) >>> 1) ||| ((r &&& 10) <<< 2) ||| ((r &&& 33) <<< 4) ||| ((r &&& 4) <<< 6)] i
def pinRows (i : Fin 10) (r : Row) : Extended.Row :=
  ⟨permutedRow i r.val % 1024, Nat.mod_lt _ (by decide)⟩
def pinProjection (i j : Fin 10) : Sig := inputs.getD (sourcePosition i j) zero

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_target_0 : ∀ r : Row,
    Extended.bit (pinRows 0 r) Extended.target = bit r graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_target_1 : ∀ r : Row,
    Extended.bit (pinRows 1 r) Extended.target = bit r graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_target_2 : ∀ r : Row,
    Extended.bit (pinRows 2 r) Extended.target = bit r graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_target_3 : ∀ r : Row,
    Extended.bit (pinRows 3 r) Extended.target = bit r graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_target_4 : ∀ r : Row,
    Extended.bit (pinRows 4 r) Extended.target = bit r graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_target_5 : ∀ r : Row,
    Extended.bit (pinRows 5 r) Extended.target = bit r graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_target_6 : ∀ r : Row,
    Extended.bit (pinRows 6 r) Extended.target = bit r graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_target_7 : ∀ r : Row,
    Extended.bit (pinRows 7 r) Extended.target = bit r graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_target_8 : ∀ r : Row,
    Extended.bit (pinRows 8 r) Extended.target = bit r graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_target_9 : ∀ r : Row,
    Extended.bit (pinRows 9 r) Extended.target = bit r graph := by
  decide +kernel

lemma pinRows_target (i : Fin 10) (r : Row) :
    Extended.bit (pinRows i r) Extended.target = bit r graph := by
  fin_cases i
  · exact pinRows_target_0 r
  · exact pinRows_target_1 r
  · exact pinRows_target_2 r
  · exact pinRows_target_3 r
  · exact pinRows_target_4 r
  · exact pinRows_target_5 r
  · exact pinRows_target_6 r
  · exact pinRows_target_7 r
  · exact pinRows_target_8 r
  · exact pinRows_target_9 r

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_0_0 : ∀ r : Row,
    Extended.bit (pinRows 0 r) (pinAt 0) = bit r (pinProjection 0 0) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_0_1 : ∀ r : Row,
    Extended.bit (pinRows 0 r) (pinAt 1) = bit r (pinProjection 0 1) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_0_2 : ∀ r : Row,
    Extended.bit (pinRows 0 r) (pinAt 2) = bit r (pinProjection 0 2) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_0_3 : ∀ r : Row,
    Extended.bit (pinRows 0 r) (pinAt 3) = bit r (pinProjection 0 3) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_0_4 : ∀ r : Row,
    Extended.bit (pinRows 0 r) (pinAt 4) = bit r (pinProjection 0 4) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_0_5 : ∀ r : Row,
    Extended.bit (pinRows 0 r) (pinAt 5) = bit r (pinProjection 0 5) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_0_6 : ∀ r : Row,
    Extended.bit (pinRows 0 r) (pinAt 6) = bit r (pinProjection 0 6) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_0_7 : ∀ r : Row,
    Extended.bit (pinRows 0 r) (pinAt 7) = bit r (pinProjection 0 7) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_0_8 : ∀ r : Row,
    Extended.bit (pinRows 0 r) (pinAt 8) = bit r (pinProjection 0 8) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_0_9 : ∀ r : Row,
    Extended.bit (pinRows 0 r) (pinAt 9) = bit r (pinProjection 0 9) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_1_0 : ∀ r : Row,
    Extended.bit (pinRows 1 r) (pinAt 0) = bit r (pinProjection 1 0) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_1_1 : ∀ r : Row,
    Extended.bit (pinRows 1 r) (pinAt 1) = bit r (pinProjection 1 1) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_1_2 : ∀ r : Row,
    Extended.bit (pinRows 1 r) (pinAt 2) = bit r (pinProjection 1 2) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_1_3 : ∀ r : Row,
    Extended.bit (pinRows 1 r) (pinAt 3) = bit r (pinProjection 1 3) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_1_4 : ∀ r : Row,
    Extended.bit (pinRows 1 r) (pinAt 4) = bit r (pinProjection 1 4) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_1_5 : ∀ r : Row,
    Extended.bit (pinRows 1 r) (pinAt 5) = bit r (pinProjection 1 5) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_1_6 : ∀ r : Row,
    Extended.bit (pinRows 1 r) (pinAt 6) = bit r (pinProjection 1 6) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_1_7 : ∀ r : Row,
    Extended.bit (pinRows 1 r) (pinAt 7) = bit r (pinProjection 1 7) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_1_8 : ∀ r : Row,
    Extended.bit (pinRows 1 r) (pinAt 8) = bit r (pinProjection 1 8) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_1_9 : ∀ r : Row,
    Extended.bit (pinRows 1 r) (pinAt 9) = bit r (pinProjection 1 9) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_2_0 : ∀ r : Row,
    Extended.bit (pinRows 2 r) (pinAt 0) = bit r (pinProjection 2 0) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_2_1 : ∀ r : Row,
    Extended.bit (pinRows 2 r) (pinAt 1) = bit r (pinProjection 2 1) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_2_2 : ∀ r : Row,
    Extended.bit (pinRows 2 r) (pinAt 2) = bit r (pinProjection 2 2) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_2_3 : ∀ r : Row,
    Extended.bit (pinRows 2 r) (pinAt 3) = bit r (pinProjection 2 3) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_2_4 : ∀ r : Row,
    Extended.bit (pinRows 2 r) (pinAt 4) = bit r (pinProjection 2 4) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_2_5 : ∀ r : Row,
    Extended.bit (pinRows 2 r) (pinAt 5) = bit r (pinProjection 2 5) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_2_6 : ∀ r : Row,
    Extended.bit (pinRows 2 r) (pinAt 6) = bit r (pinProjection 2 6) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_2_7 : ∀ r : Row,
    Extended.bit (pinRows 2 r) (pinAt 7) = bit r (pinProjection 2 7) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_2_8 : ∀ r : Row,
    Extended.bit (pinRows 2 r) (pinAt 8) = bit r (pinProjection 2 8) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_2_9 : ∀ r : Row,
    Extended.bit (pinRows 2 r) (pinAt 9) = bit r (pinProjection 2 9) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_3_0 : ∀ r : Row,
    Extended.bit (pinRows 3 r) (pinAt 0) = bit r (pinProjection 3 0) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_3_1 : ∀ r : Row,
    Extended.bit (pinRows 3 r) (pinAt 1) = bit r (pinProjection 3 1) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_3_2 : ∀ r : Row,
    Extended.bit (pinRows 3 r) (pinAt 2) = bit r (pinProjection 3 2) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_3_3 : ∀ r : Row,
    Extended.bit (pinRows 3 r) (pinAt 3) = bit r (pinProjection 3 3) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_3_4 : ∀ r : Row,
    Extended.bit (pinRows 3 r) (pinAt 4) = bit r (pinProjection 3 4) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_3_5 : ∀ r : Row,
    Extended.bit (pinRows 3 r) (pinAt 5) = bit r (pinProjection 3 5) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_3_6 : ∀ r : Row,
    Extended.bit (pinRows 3 r) (pinAt 6) = bit r (pinProjection 3 6) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_3_7 : ∀ r : Row,
    Extended.bit (pinRows 3 r) (pinAt 7) = bit r (pinProjection 3 7) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_3_8 : ∀ r : Row,
    Extended.bit (pinRows 3 r) (pinAt 8) = bit r (pinProjection 3 8) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_3_9 : ∀ r : Row,
    Extended.bit (pinRows 3 r) (pinAt 9) = bit r (pinProjection 3 9) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_4_0 : ∀ r : Row,
    Extended.bit (pinRows 4 r) (pinAt 0) = bit r (pinProjection 4 0) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_4_1 : ∀ r : Row,
    Extended.bit (pinRows 4 r) (pinAt 1) = bit r (pinProjection 4 1) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_4_2 : ∀ r : Row,
    Extended.bit (pinRows 4 r) (pinAt 2) = bit r (pinProjection 4 2) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_4_3 : ∀ r : Row,
    Extended.bit (pinRows 4 r) (pinAt 3) = bit r (pinProjection 4 3) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_4_4 : ∀ r : Row,
    Extended.bit (pinRows 4 r) (pinAt 4) = bit r (pinProjection 4 4) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_4_5 : ∀ r : Row,
    Extended.bit (pinRows 4 r) (pinAt 5) = bit r (pinProjection 4 5) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_4_6 : ∀ r : Row,
    Extended.bit (pinRows 4 r) (pinAt 6) = bit r (pinProjection 4 6) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_4_7 : ∀ r : Row,
    Extended.bit (pinRows 4 r) (pinAt 7) = bit r (pinProjection 4 7) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_4_8 : ∀ r : Row,
    Extended.bit (pinRows 4 r) (pinAt 8) = bit r (pinProjection 4 8) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_4_9 : ∀ r : Row,
    Extended.bit (pinRows 4 r) (pinAt 9) = bit r (pinProjection 4 9) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_5_0 : ∀ r : Row,
    Extended.bit (pinRows 5 r) (pinAt 0) = bit r (pinProjection 5 0) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_5_1 : ∀ r : Row,
    Extended.bit (pinRows 5 r) (pinAt 1) = bit r (pinProjection 5 1) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_5_2 : ∀ r : Row,
    Extended.bit (pinRows 5 r) (pinAt 2) = bit r (pinProjection 5 2) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_5_3 : ∀ r : Row,
    Extended.bit (pinRows 5 r) (pinAt 3) = bit r (pinProjection 5 3) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_5_4 : ∀ r : Row,
    Extended.bit (pinRows 5 r) (pinAt 4) = bit r (pinProjection 5 4) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_5_5 : ∀ r : Row,
    Extended.bit (pinRows 5 r) (pinAt 5) = bit r (pinProjection 5 5) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_5_6 : ∀ r : Row,
    Extended.bit (pinRows 5 r) (pinAt 6) = bit r (pinProjection 5 6) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_5_7 : ∀ r : Row,
    Extended.bit (pinRows 5 r) (pinAt 7) = bit r (pinProjection 5 7) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_5_8 : ∀ r : Row,
    Extended.bit (pinRows 5 r) (pinAt 8) = bit r (pinProjection 5 8) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_5_9 : ∀ r : Row,
    Extended.bit (pinRows 5 r) (pinAt 9) = bit r (pinProjection 5 9) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_6_0 : ∀ r : Row,
    Extended.bit (pinRows 6 r) (pinAt 0) = bit r (pinProjection 6 0) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_6_1 : ∀ r : Row,
    Extended.bit (pinRows 6 r) (pinAt 1) = bit r (pinProjection 6 1) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_6_2 : ∀ r : Row,
    Extended.bit (pinRows 6 r) (pinAt 2) = bit r (pinProjection 6 2) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_6_3 : ∀ r : Row,
    Extended.bit (pinRows 6 r) (pinAt 3) = bit r (pinProjection 6 3) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_6_4 : ∀ r : Row,
    Extended.bit (pinRows 6 r) (pinAt 4) = bit r (pinProjection 6 4) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_6_5 : ∀ r : Row,
    Extended.bit (pinRows 6 r) (pinAt 5) = bit r (pinProjection 6 5) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_6_6 : ∀ r : Row,
    Extended.bit (pinRows 6 r) (pinAt 6) = bit r (pinProjection 6 6) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_6_7 : ∀ r : Row,
    Extended.bit (pinRows 6 r) (pinAt 7) = bit r (pinProjection 6 7) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_6_8 : ∀ r : Row,
    Extended.bit (pinRows 6 r) (pinAt 8) = bit r (pinProjection 6 8) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_6_9 : ∀ r : Row,
    Extended.bit (pinRows 6 r) (pinAt 9) = bit r (pinProjection 6 9) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_7_0 : ∀ r : Row,
    Extended.bit (pinRows 7 r) (pinAt 0) = bit r (pinProjection 7 0) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_7_1 : ∀ r : Row,
    Extended.bit (pinRows 7 r) (pinAt 1) = bit r (pinProjection 7 1) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_7_2 : ∀ r : Row,
    Extended.bit (pinRows 7 r) (pinAt 2) = bit r (pinProjection 7 2) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_7_3 : ∀ r : Row,
    Extended.bit (pinRows 7 r) (pinAt 3) = bit r (pinProjection 7 3) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_7_4 : ∀ r : Row,
    Extended.bit (pinRows 7 r) (pinAt 4) = bit r (pinProjection 7 4) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_7_5 : ∀ r : Row,
    Extended.bit (pinRows 7 r) (pinAt 5) = bit r (pinProjection 7 5) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_7_6 : ∀ r : Row,
    Extended.bit (pinRows 7 r) (pinAt 6) = bit r (pinProjection 7 6) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_7_7 : ∀ r : Row,
    Extended.bit (pinRows 7 r) (pinAt 7) = bit r (pinProjection 7 7) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_7_8 : ∀ r : Row,
    Extended.bit (pinRows 7 r) (pinAt 8) = bit r (pinProjection 7 8) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_7_9 : ∀ r : Row,
    Extended.bit (pinRows 7 r) (pinAt 9) = bit r (pinProjection 7 9) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_8_0 : ∀ r : Row,
    Extended.bit (pinRows 8 r) (pinAt 0) = bit r (pinProjection 8 0) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_8_1 : ∀ r : Row,
    Extended.bit (pinRows 8 r) (pinAt 1) = bit r (pinProjection 8 1) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_8_2 : ∀ r : Row,
    Extended.bit (pinRows 8 r) (pinAt 2) = bit r (pinProjection 8 2) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_8_3 : ∀ r : Row,
    Extended.bit (pinRows 8 r) (pinAt 3) = bit r (pinProjection 8 3) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_8_4 : ∀ r : Row,
    Extended.bit (pinRows 8 r) (pinAt 4) = bit r (pinProjection 8 4) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_8_5 : ∀ r : Row,
    Extended.bit (pinRows 8 r) (pinAt 5) = bit r (pinProjection 8 5) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_8_6 : ∀ r : Row,
    Extended.bit (pinRows 8 r) (pinAt 6) = bit r (pinProjection 8 6) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_8_7 : ∀ r : Row,
    Extended.bit (pinRows 8 r) (pinAt 7) = bit r (pinProjection 8 7) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_8_8 : ∀ r : Row,
    Extended.bit (pinRows 8 r) (pinAt 8) = bit r (pinProjection 8 8) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_8_9 : ∀ r : Row,
    Extended.bit (pinRows 8 r) (pinAt 9) = bit r (pinProjection 8 9) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_9_0 : ∀ r : Row,
    Extended.bit (pinRows 9 r) (pinAt 0) = bit r (pinProjection 9 0) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_9_1 : ∀ r : Row,
    Extended.bit (pinRows 9 r) (pinAt 1) = bit r (pinProjection 9 1) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_9_2 : ∀ r : Row,
    Extended.bit (pinRows 9 r) (pinAt 2) = bit r (pinProjection 9 2) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_9_3 : ∀ r : Row,
    Extended.bit (pinRows 9 r) (pinAt 3) = bit r (pinProjection 9 3) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_9_4 : ∀ r : Row,
    Extended.bit (pinRows 9 r) (pinAt 4) = bit r (pinProjection 9 4) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_9_5 : ∀ r : Row,
    Extended.bit (pinRows 9 r) (pinAt 5) = bit r (pinProjection 9 5) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_9_6 : ∀ r : Row,
    Extended.bit (pinRows 9 r) (pinAt 6) = bit r (pinProjection 9 6) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_9_7 : ∀ r : Row,
    Extended.bit (pinRows 9 r) (pinAt 7) = bit r (pinProjection 9 7) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_9_8 : ∀ r : Row,
    Extended.bit (pinRows 9 r) (pinAt 8) = bit r (pinProjection 9 8) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pinRows_pin_9_9 : ∀ r : Row,
    Extended.bit (pinRows 9 r) (pinAt 9) = bit r (pinProjection 9 9) := by
  decide +kernel

lemma pinRows_pin (i j : Fin 10) (r : Row) :
    Extended.bit (pinRows i r) (pinAt j) = bit r (pinProjection i j) := by
  fin_cases i <;> fin_cases j
  · exact pinRows_pin_0_0 r
  · exact pinRows_pin_0_1 r
  · exact pinRows_pin_0_2 r
  · exact pinRows_pin_0_3 r
  · exact pinRows_pin_0_4 r
  · exact pinRows_pin_0_5 r
  · exact pinRows_pin_0_6 r
  · exact pinRows_pin_0_7 r
  · exact pinRows_pin_0_8 r
  · exact pinRows_pin_0_9 r
  · exact pinRows_pin_1_0 r
  · exact pinRows_pin_1_1 r
  · exact pinRows_pin_1_2 r
  · exact pinRows_pin_1_3 r
  · exact pinRows_pin_1_4 r
  · exact pinRows_pin_1_5 r
  · exact pinRows_pin_1_6 r
  · exact pinRows_pin_1_7 r
  · exact pinRows_pin_1_8 r
  · exact pinRows_pin_1_9 r
  · exact pinRows_pin_2_0 r
  · exact pinRows_pin_2_1 r
  · exact pinRows_pin_2_2 r
  · exact pinRows_pin_2_3 r
  · exact pinRows_pin_2_4 r
  · exact pinRows_pin_2_5 r
  · exact pinRows_pin_2_6 r
  · exact pinRows_pin_2_7 r
  · exact pinRows_pin_2_8 r
  · exact pinRows_pin_2_9 r
  · exact pinRows_pin_3_0 r
  · exact pinRows_pin_3_1 r
  · exact pinRows_pin_3_2 r
  · exact pinRows_pin_3_3 r
  · exact pinRows_pin_3_4 r
  · exact pinRows_pin_3_5 r
  · exact pinRows_pin_3_6 r
  · exact pinRows_pin_3_7 r
  · exact pinRows_pin_3_8 r
  · exact pinRows_pin_3_9 r
  · exact pinRows_pin_4_0 r
  · exact pinRows_pin_4_1 r
  · exact pinRows_pin_4_2 r
  · exact pinRows_pin_4_3 r
  · exact pinRows_pin_4_4 r
  · exact pinRows_pin_4_5 r
  · exact pinRows_pin_4_6 r
  · exact pinRows_pin_4_7 r
  · exact pinRows_pin_4_8 r
  · exact pinRows_pin_4_9 r
  · exact pinRows_pin_5_0 r
  · exact pinRows_pin_5_1 r
  · exact pinRows_pin_5_2 r
  · exact pinRows_pin_5_3 r
  · exact pinRows_pin_5_4 r
  · exact pinRows_pin_5_5 r
  · exact pinRows_pin_5_6 r
  · exact pinRows_pin_5_7 r
  · exact pinRows_pin_5_8 r
  · exact pinRows_pin_5_9 r
  · exact pinRows_pin_6_0 r
  · exact pinRows_pin_6_1 r
  · exact pinRows_pin_6_2 r
  · exact pinRows_pin_6_3 r
  · exact pinRows_pin_6_4 r
  · exact pinRows_pin_6_5 r
  · exact pinRows_pin_6_6 r
  · exact pinRows_pin_6_7 r
  · exact pinRows_pin_6_8 r
  · exact pinRows_pin_6_9 r
  · exact pinRows_pin_7_0 r
  · exact pinRows_pin_7_1 r
  · exact pinRows_pin_7_2 r
  · exact pinRows_pin_7_3 r
  · exact pinRows_pin_7_4 r
  · exact pinRows_pin_7_5 r
  · exact pinRows_pin_7_6 r
  · exact pinRows_pin_7_7 r
  · exact pinRows_pin_7_8 r
  · exact pinRows_pin_7_9 r
  · exact pinRows_pin_8_0 r
  · exact pinRows_pin_8_1 r
  · exact pinRows_pin_8_2 r
  · exact pinRows_pin_8_3 r
  · exact pinRows_pin_8_4 r
  · exact pinRows_pin_8_5 r
  · exact pinRows_pin_8_6 r
  · exact pinRows_pin_8_7 r
  · exact pinRows_pin_8_8 r
  · exact pinRows_pin_8_9 r
  · exact pinRows_pin_9_0 r
  · exact pinRows_pin_9_1 r
  · exact pinRows_pin_9_2 r
  · exact pinRows_pin_9_3 r
  · exact pinRows_pin_9_4 r
  · exact pinRows_pin_9_5 r
  · exact pinRows_pin_9_6 r
  · exact pinRows_pin_9_7 r
  · exact pinRows_pin_9_8 r
  · exact pinRows_pin_9_9 r

lemma sourcePosition_self (i : Fin 10) : sourcePosition i i = 9 := by
  revert i
  decide +kernel

lemma pinProjection_self (i : Fin 10) : pinProjection i i = zero := by
  simp [pinProjection,sourcePosition_self,inputs]

lemma pinAt_mem (i : Fin 10) : pinAt i ∈ Extended.initial := by
  revert i
  decide +kernel

lemma mem_pinAt (a : Extended.Sig) (h : a ∈ Extended.initial) :
    ∃ i : Fin 10, a = pinAt i := by
  have : ∀ a ∈ Extended.initial, ∃ i : Fin 10, a = pinAt i := by decide +kernel
  exact this a h

lemma pinProjection_supply (i j : Fin 10) :
    pinProjection i j = zero ∨ pinProjection i j ∈ inputs := by
  revert i j
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.Binary17
