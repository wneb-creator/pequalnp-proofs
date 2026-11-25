import ForcedTrueCompile
import DirectFilterCore
import SharedFilterSafety
import Unary18Check

namespace PEqualNP.Outside.L_meta_1884.SafeOperandImpossible

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem impossible (pre post : List Gate) (ins : List Nat) (o : Nat)
    (hp : ∀ g ∈ pre, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hs : ∀ g ∈ post, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hsize : pre.length + post.length + 1 ≤ 18)
    (hcompute : ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ ⟨.not,ins⟩ :: post,o⟩ (DirectFilter.seed x) =
        SoleOrPartner.target x)
    (hsafe : ∀ x : Fin 10 → Bool, DirectFilter.operand pre ins x = true →
      SoleOrPartner.target x = true) : False := by
  have hforced := SafeNot.replace_safe_not_function pre post ins o DirectFilter.seed
    SoleOrPartner.target (fun g hg => (hs g hg).1) hcompute hsafe
  have hnonconstant : ∃ x y : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ ⟨.and,[]⟩ :: post,o⟩ (DirectFilter.seed x) ≠
        Circuit.eval ⟨pre ++ ⟨.and,[]⟩ :: post,o⟩ (DirectFilter.seed y) := by
    refine ⟨fun _ => false,fun _ => true,?_⟩
    rw [hforced,hforced]
    decide
  obtain ⟨D,hm,hsmall,heval⟩ := ForcedTrueCompile.compile 11 pre post o DirectFilter.seed
    (by intro x; simp [DirectFilter.seed]) hp hs hnonconstant
  have hfloor := Unary18.unary_mono_size_eighteen D id Bool.not hm (by
    intro x
    change D.eval (DirectFilter.seed x) = SoleOrPartner.target x
    exact (heval x).trans (hforced x))
  simp only [List.length_append,List.length_cons] at hsmall
  omega

end PEqualNP.Outside.L_meta_1884.SafeOperandImpossible
