import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.MacroBudget

open Turing

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

def stmtBound : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => stmtBound q + 1
  | .peek _ _ q => stmtBound q + 2
  | .pop _ _ q => stmtBound q + 1
  | .load _ q => stmtBound q + 1
  | .branch _ q₁ q₂ => stmtBound q₁ + stmtBound q₂ + 1
  | .goto _ => 1
  | .halt => 1

lemma stepAux_length_le [DecidableEq K] (q : TM2.Stmt Γ Λ σ)
    (v : σ) (stk : ∀ k, List (Γ k)) (j : K) :
    ((TM2.stepAux q v stk).stk j).length ≤ (stk j).length + stmtBound q := by
  induction q generalizing v stk with
  | push k f q ih =>
      have h := ih v (Function.update stk k (f v :: stk k))
      simp only [TM2.stepAux, stmtBound]
      by_cases hj : j = k
      · subst j
        simp only [Function.update_self, List.length_cons] at h
        omega
      · simp only [Function.update_of_ne hj] at h
        omega
  | peek k f q ih =>
      have h := ih (f v (stk k).head?) stk
      simp only [TM2.stepAux, stmtBound]
      omega
  | pop k f q ih =>
      have h := ih (f v (stk k).head?) (Function.update stk k (stk k).tail)
      simp only [TM2.stepAux, stmtBound]
      by_cases hj : j = k
      · subst j
        simp only [Function.update_self, List.length_tail] at h
        omega
      · simp only [Function.update_of_ne hj] at h
        omega
  | load f q ih =>
      have h := ih (f v) stk
      simp only [TM2.stepAux, stmtBound]
      omega
  | branch f q₁ q₂ ih₁ ih₂ =>
      have h₁ := ih₁ v stk
      have h₂ := ih₂ v stk
      simp only [TM2.stepAux, stmtBound]
      cases f v <;> simp only [Bool.cond_false, Bool.cond_true] <;> omega
  | goto f => simp [TM2.stepAux, stmtBound]
  | halt => simp [TM2.stepAux, stmtBound]

noncomputable def machineBound (tm : FinTM2) : ℕ := by
  let := tm.ΛFin
  exact 1 + ∑ l : tm.Λ, stmtBound (tm.m l)

lemma stmt_le_machine (tm : FinTM2) (l : tm.Λ) : stmtBound (tm.m l) ≤ machineBound tm := by
  let := tm.ΛFin
  have h : stmtBound (tm.m l) ≤ ∑ z : tm.Λ, stmtBound (tm.m z) :=
    Finset.single_le_sum (f := fun z : tm.Λ => stmtBound (tm.m z))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  unfold machineBound
  dsimp only
  omega

lemma step_length_le (tm : FinTM2) (a b : tm.Cfg) (hb : b ∈ tm.step a) (k : tm.K) :
    (b.stk k).length ≤ (a.stk k).length + machineBound tm := by
  cases a with
  | mk label v stk =>
    cases label with
    | none => exact False.elim (Option.not_mem_none b hb)
    | some l =>
      have heq := Option.mem_some.mp hb
      subst b
      exact (stepAux_length_le (tm.m l) v stk k).trans
        (Nat.add_le_add_left (stmt_le_machine tm l) _)

def paddedStep (tm : FinTM2) (cfg : tm.Cfg) : tm.Cfg := (tm.step cfg).getD cfg

lemma paddedStep_length_le (tm : FinTM2) (cfg : tm.Cfg) (k : tm.K) :
    ((paddedStep tm cfg).stk k).length ≤ (cfg.stk k).length + machineBound tm := by
  unfold paddedStep
  cases h : tm.step cfg with
  | none => simp
  | some next =>
      simpa using step_length_le tm cfg next (by rw [h]; exact Option.mem_some.mpr rfl) k

def paddedRun (tm : FinTM2) (cfg : tm.Cfg) : ℕ → tm.Cfg
  | 0 => cfg
  | n + 1 => paddedStep tm (paddedRun tm cfg n)

lemma paddedRun_length_le (tm : FinTM2) (cfg : tm.Cfg) (n : ℕ) (k : tm.K) :
    ((paddedRun tm cfg n).stk k).length ≤ (cfg.stk k).length + n * machineBound tm := by
  induction n with
  | zero => simp [paddedRun]
  | succ n ih =>
      have h := paddedStep_length_le tm (paddedRun tm cfg n) k
      simp only [paddedRun]
      nlinarith

end PEqualNP.Outside.MacroBudget
