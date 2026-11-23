import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.AlphabetBound

open Turing

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

def pushed : TM2.Stmt Γ Λ σ → Set (Sigma Γ)
  | .push k f q => by
      classical
      exact (Set.range fun v : σ => (⟨k, f v⟩ : Sigma Γ)) ∪ pushed q
  | .peek _ _ q => pushed q
  | .pop _ _ q => pushed q
  | .load _ q => pushed q
  | .branch _ q₁ q₂ => by
      classical
      exact pushed q₁ ∪ pushed q₂
  | .goto _ => ∅
  | .halt => ∅

def supported (S : Set (Sigma Γ)) (stk : ∀ k, List (Γ k)) : Prop :=
  ∀ k a, a ∈ stk k → (⟨k, a⟩ : Sigma Γ) ∈ S

lemma stepAux_supported [Fintype σ] [DecidableEq K]
    (q : TM2.Stmt Γ Λ σ) (v : σ) (stk : ∀ k, List (Γ k))
    (S : Set (Sigma Γ)) (hp : pushed q ⊆ S) (hs : supported S stk) :
    supported S (TM2.stepAux q v stk).stk := by
  classical
  induction q generalizing v stk with
  | push k f q ih =>
      apply ih v (Function.update stk k (f v :: stk k))
      · exact fun x hx => hp (Or.inr hx)
      · intro j a ha
        by_cases h : j = k
        · subst j
          simp only [Function.update_self, List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact hp (Or.inl ⟨v, rfl⟩)
          · exact hs k a ha
        · exact hs j a (by simpa [Function.update_of_ne h] using ha)
  | peek k f q ih => exact ih _ _ hp hs
  | pop k f q ih =>
      apply ih (f v (stk k).head?) (Function.update stk k (stk k).tail) hp
      intro j a ha
      by_cases h : j = k
      · subst j
        apply hs k a
        exact List.mem_of_mem_tail (by simpa only [Function.update_self] using ha)
      · exact hs j a (by simpa [Function.update_of_ne h] using ha)
  | load f q ih => exact ih _ _ hp hs
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.stepAux]
      cases h : f v
      · exact ih₂ _ _ (fun x hx => hp (Or.inr hx)) hs
      · exact ih₁ _ _ (fun x hx => hp (Or.inl hx)) hs
  | goto f => exact hs
  | halt => exact hs

def machineAlphabet (tm : FinTM2) : Set (Sigma tm.Γ) :=
  (Set.range fun a : tm.Γ tm.k₀ => (⟨tm.k₀, a⟩ : Sigma tm.Γ)) ∪
    ⋃ l : tm.Λ, pushed (tm.m l)

lemma pushed_finite [Fintype σ] (q : TM2.Stmt Γ Λ σ) : (pushed q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek k f q ih | pop k f q ih | load f q ih => exact ih
  | branch f q₁ q₂ ih₁ ih₂ => exact ih₁.union ih₂
  | goto f | halt => exact Set.finite_empty

lemma machineAlphabet_finite (tm : FinTM2) : (machineAlphabet tm).Finite := by
  let := tm.σFin
  let := tm.ΛFin
  let := tm.Γk₀Fin
  exact (Set.finite_range _).union (Set.finite_iUnion fun l => pushed_finite (tm.m l))

lemma init_supported (tm : FinTM2) (input : List (tm.Γ tm.k₀)) :
    supported (machineAlphabet tm) (Turing.initList tm input).stk := by
  classical
  intro k a ha
  by_cases h : k = tm.k₀
  · subst k
    exact Or.inl ⟨a, rfl⟩
  · simp [Turing.initList, h] at ha

lemma step_supported (tm : FinTM2) (a b : tm.Cfg) (hb : b ∈ tm.step a)
    (ha : supported (machineAlphabet tm) a.stk) :
    supported (machineAlphabet tm) b.stk := by
  classical
  let := tm.σFin
  let := tm.ΛFin
  cases a with
  | mk label v stk =>
    cases label with
    | none => exact False.elim (Option.not_mem_none b hb)
    | some label =>
      have heq := Option.mem_some.mp hb
      subst b
      apply stepAux_supported _ _ _ _ ?_ ha
      intro x hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨label, hx⟩)

lemma reachable_supported (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (cfg : tm.Cfg)
    (h : Relation.ReflTransGen (fun a b => b ∈ tm.step a) (Turing.initList tm input) cfg) :
    supported (machineAlphabet tm) cfg.stk := by
  induction h with
  | refl => exact init_supported tm input
  | @tail b c hab hbc ih => exact step_supported tm b c hbc ih

end PEqualNP.Outside.AlphabetBound
