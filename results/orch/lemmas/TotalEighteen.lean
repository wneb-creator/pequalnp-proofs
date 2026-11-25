import GenericBounds
import RealizeMode

namespace PEqualNP.Outside.Pilot113TotalEighteen

open PEqualNP.Outside.L_meta_6581 PEqualNP.CircuitLowerBounds

theorem monotone_eighteen (hMonoFloor : Lower false inputs graph 16)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (mono : ∀ g ∈ C.gates, Extended.isNot g = false)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    18 ≤ C.size := by
  obtain ⟨k, S, hk, run, raw⟩ :=
    Pilot113RealizeMode.realize_mode false C legal (fun _ => mono) computes
  have floor := Pilot113GenericBounds.monotone_eighteen hMonoFloor run raw
  exact floor.trans (hk.trans List.countP_le_length)

theorem total_eighteen (hMonoFloor : Lower false inputs graph 16)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    18 ≤ C.size := by
  by_cases mono : ∀ g ∈ C.gates, Extended.isNot g = false
  · exact monotone_eighteen hMonoFloor C legal mono computes
  · have strict : C.gates.countP (fun g => !Extended.isNot g) < C.gates.length := by
      by_contra! hn
      have heq := Nat.le_antisymm List.countP_le_length hn
      have all := List.countP_eq_length.mp heq
      apply mono
      intro g hg
      simpa only [Bool.not_eq_true'] using all g hg
    have floor := Pilot113GlobalCount.nonNot_seventeen nineFloor C legal computes
    change 18 ≤ C.gates.length
    omega

end PEqualNP.Outside.Pilot113TotalEighteen
