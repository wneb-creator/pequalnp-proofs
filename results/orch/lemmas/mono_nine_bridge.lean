import PEqualNP.Outside.L_meta_2592
import mono_nine
import nine_actual

namespace PEqualNP.Outside.L_meta_1886_aux.MonoBridge
open PEqualNP.Outside.L_meta_2592_aux.Stronger

lemma reach_to_monoNine {R : Type} (u : Bool) (roots : List (Wire R))
    (k : Nat) (bank : List (Wire R)) (path : Reach u roots k bank) :
    MonoNine.Reach u roots k bank := by
  induction k generalizing bank with
  | zero => exact path
  | succ k ih =>
    obtain ⟨op, earlier, a, b, prior, ha, hb, rfl⟩ := path
    exact ⟨op, earlier, a, b, ih earlier prior, ha, hb, rfl⟩

lemma lower16 : Lower false inputs graph 16 := by
  intro k bank path hit
  exact MonoNine.lower16 k bank (reach_to_monoNine _ _ _ _ path) hit

lemma live_to_monoNine {u target k S} (run : Live u target k S) :
    MonoNine.Live u target k S := by
  induction k generalizing S with
  | zero => exact run
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,hs,ha,hb,hab,hfresh,tail⟩ := run
    exact ⟨U,a,b,d,hd,hs,ha,hb,hab,hfresh,ih tail⟩

lemma monoImpossible : Impossible false graph 15 inputs.toFinset := by
  intro k hk run
  exact MonoNine.monoRoot k hk (live_to_monoNine run)

lemma actualNineLower16 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 edge 15 :=
  NineActual.of_monoRoot monoImpossible

end PEqualNP.Outside.L_meta_1886_aux.MonoBridge
