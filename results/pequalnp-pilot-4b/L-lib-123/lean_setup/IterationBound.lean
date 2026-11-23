import Mathlib
import PEqualNP.Library.Machines.IterMeasure

namespace IterationBound

open Turing PEqualNP.Library PEqualNP.Library.Machines

def pointBound (C data passes : ℕ) : ℕ :=
  passes * (C * data + C + 2 * data + 3) + 4 * data + passes + 5

def totalBound (C n : ℕ) : ℕ := n * (C * n + C + 2 * n + 3) + 5 * n + 5

lemma pointBound_le_totalBound (C data passes : ℕ) :
    pointBound C data passes ≤ totalBound C (data + passes) := by
  have hinner : C * data + C + 2 * data + 3 ≤
      C * (data + passes) + C + 2 * (data + passes) + 3 := by
    gcongr <;> omega
  have hmul := Nat.mul_le_mul (show passes ≤ data + passes by omega) hinner
  dsimp [pointBound, totalBound]
  omega

lemma iterate_length (g : List Bool → List Bool)
    (hg : ∀ x, (g x).length ≤ x.length) (x : List Bool) (n : ℕ) :
    (g^[n] x).length ≤ x.length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hg _).trans ih

lemma linear_iteration (g : List Bool → List Bool) (C : ℕ)
    (hg : ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) g
      (fun n => C * n + C))
    (hlen : ∀ x, (g x).length ≤ x.length) :
    ∃ c : TM2ComputableInTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1),
      ∀ y u, (c.outputsFun (y, u)).steps ≤ pointBound C y.length u.length := by
  obtain ⟨c, hc⟩ := hg
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let d₀ : c.tm.Γ c.tm.k₀ → Bool := c.inputAlphabet
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let p : Polynomial ℕ := Polynomial.C C * Polynomial.X + Polynomial.C C
  have hd : ∀ b, d₀ (e₀ b) = b := fun b => c.inputAlphabet.right_inv b
  have hrun : ∀ z : List Bool, ∃ (s : ℕ) (out : List (c.tm.Γ c.tm.k₁)),
      s ≤ p.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm out) ∧ out.map e₁ = g z := by
    intro z
    refine ⟨(c.outputsFun z).steps, (g z).map c.outputAlphabet.invFun, ?_,
      (c.outputsFun z).evals_in_steps, ?_⟩
    · simpa [p] using (c.outputsFun z).steps_le_m.trans (hc z.length)
    · simp only [List.map_map]
      conv_rhs => rw [← List.map_id (g z)]
      exact List.map_congr_left fun b _ => c.outputAlphabet.right_inv b
  have key : ∀ y u : List Bool, ∃ n, n ≤ pointBound C y.length u.length ∧
      (flip bind (TM2.step (Iter.iterProg c.tm e₀ d₀ e₁)))^[n]
        (some (initList (Iter.iterM c.tm e₀ d₀ e₁) (encodePair (y, u)))) =
        some (haltList (Iter.iterM c.tm e₀ d₀ e₁) (g^[u.length] y)) := by
    intro y u
    obtain ⟨n, hn, hr⟩ := Iter.iter_run_bdd e₀ d₀ e₁ g p hd hrun y u y.length
      (by intro j _; exact iterate_length g hlen y j)
    refine ⟨n, ?_, hr⟩
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at hn
    dsimp [pointBound]
    omega
  let result : TM2ComputableInTime encodePair (fun x : List Bool => x)
      (fun q : List Bool × List Bool => g^[q.2.length] q.1) := {
    tm := Iter.iterM c.tm e₀ d₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := totalBound C
    outputsFun := fun q => {
      steps := Classical.choose (key q.1 q.2)
      evals_in_steps := by
        have hm : ∀ (γ : Type) (xs : List γ), List.map (Equiv.refl γ).invFun xs = xs :=
          fun _ _ => by simp
        exact (congrArg (fun xs =>
          (flip bind (TM2.step (Iter.iterProg c.tm e₀ d₀ e₁)))^[Classical.choose (key q.1 q.2)]
            (some (initList (Iter.iterM c.tm e₀ d₀ e₁) xs))) (hm _ (encodePair q))).trans
          ((Classical.choose_spec (key q.1 q.2)).2.trans
            (congrArg (fun xs => some (haltList (Iter.iterM c.tm e₀ d₀ e₁) xs))
              (hm _ (g^[q.2.length] q.1))).symm)
      steps_le_m := (Classical.choose_spec (key q.1 q.2)).1.trans (by
        simpa [encodePair] using pointBound_le_totalBound C q.1.length q.2.length)
    }
  }
  exact ⟨result, fun y u => (Classical.choose_spec (key y u)).1⟩

end IterationBound
