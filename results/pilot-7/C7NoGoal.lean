import C7PackedBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed8NoGoal : Bool :=
  (List.range 10).all fun s => (List.range (seed8Count s)).all fun i =>
    !(seed8States s i == [Live.goal seed8K])

theorem seed8_noGoal_checked : seed8NoGoal = true := by decide +kernel

theorem seed8_noGoal (s : Nat) (hs : s ≤ 9) (i : Nat) (hi : i < seed8Count s) :
    seed8States s i ≠ [Live.goal seed8K] := by
  have h1 := List.all_eq_true.1 seed8_noGoal_checked s (List.mem_range.2 (by omega))
  have h2 := List.all_eq_true.1 h1 i (List.mem_range.2 hi)
  simpa using h2

theorem seed8_root_perm : (seed8States 9 0).Perm seed8Inputs := by decide +kernel

end PEqualNP.Outside.L_meta_982_aux.Finite
