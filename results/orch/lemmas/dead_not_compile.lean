import constant_sweep_mono
import one_not_compile

namespace PEqualNP.Outside.L_meta_1886_aux.DeadNotCompile

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.ConstantSweep
open PEqualNP.Outside.L_meta_2592_aux.OneNotCompile
open ConstantSweepMono

lemma compile_constant_suffix {X : Type} {n : ℕ} (input : X → List Bool) (inputLength : ∀ x, (input x).length = n) (F : X → Bool)
    (pre suffix : List Gate) (outIdx : ℕ) (b : Bool)
    (hs : ∀ g ∈ suffix, monoGood g)
    (correct : ∀ x, (run suffix (run pre (input x) ++ [b])).getD outIdx false = F x)
    (nonconstant : ∃ x y, F x ≠ F y) :
    ∃ (out : List Gate) (j : ℕ),
      (∀ g ∈ out, monoGood g) ∧
      out.length + (suffix.filter (touched {n + pre.length})).length ≤ suffix.length ∧
      ∀ x, (Circuit.mk (pre ++ out) j).eval (input x) = F x := by
  let m := n + pre.length
  obtain ⟨out, extras, hout, _, hsize, hsem⟩ :=
    ConstantSweepMono.sweep {m} suffix hs (seed m b) m
      (by
        intro i hi
        have : i = m := by simpa using hi
        subst i
        simp [seed])
      (by
        intro i hi
        have : i = m := by simpa using hi
        subst i
        exact ⟨b, seed_last _ _⟩)
  let refs := seed m b ++ extras
  have result : ∀ x, value (run out (run pre (input x))) (read refs outIdx) = F x := by
    intro x
    have hw : (run pre (input x)).length = m := by simp [run_length,m,inputLength]
    have hr : related (seed m b) (run pre (input x)) (run pre (input x) ++ [b]) := by
      simpa only [hw] using seed_related (run pre (input x)) b
    exact (read_value (hsem _ _ hw hr) outIdx).trans (correct x)
  cases he : read refs outIdx with
  | inl c =>
    obtain ⟨x,y,hne⟩ := nonconstant
    have hx := result x
    have hy := result y
    simp only [he, value] at hx hy
    exact False.elim (hne (hx.symm.trans hy))
  | inr j =>
    refine ⟨out,j,hout,hsize,?_⟩
    intro x
    have h := result x
    simp only [he, value] at h
    change (run (pre ++ out) (input x)).getD j false = F x
    rw [run_append]
    exact h

end PEqualNP.Outside.L_meta_1886_aux.DeadNotCompile
