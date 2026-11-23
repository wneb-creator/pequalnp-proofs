import Seed0PackedBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed0NoGoal : Bool :=
  (List.range 10).all fun s => (List.range (seed0Count s)).all fun i =>
    !(seed0States s i == [Live.goal seed0K])

theorem seed0_noGoal_checked : seed0NoGoal = true := by decide +kernel

theorem seed0_noGoal (s : Nat) (hs : s ≤ 9) (i : Nat) (hi : i < seed0Count s) :
    seed0States s i ≠ [Live.goal seed0K] := by
  have h1 := List.all_eq_true.1 seed0_noGoal_checked s (List.mem_range.2 (by omega))
  have h2 := List.all_eq_true.1 h1 i (List.mem_range.2 hi)
  simpa using h2

theorem seed0_root_perm : (seed0States 9 0).Perm seed0Inputs := by decide +kernel

end PEqualNP.Outside.L_meta_982_aux.Finite
