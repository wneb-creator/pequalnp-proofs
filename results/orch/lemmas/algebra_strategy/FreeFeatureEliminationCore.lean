import Mathlib
import PEqualNP.MetaComplexity.Helpers.Elim
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.MetaComplexity.Helpers.Hardwire
import PEqualNP.MetaComplexity.L106

namespace PEqualNP.Outside.L_meta_650_aux.FreeFeatureElimination

open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds

theorem gate_elim_false_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool)
    (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y, f (Function.update x p false) ≠ f (Function.update y p false))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize (n + 1) (fun x => f (Function.update x p false)) s := by
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n)
  have hg := Helpers.PermInputs.relabel_size (⇑σ) f (s + 1) h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [σ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    simp [σ, Equiv.symm_swap]
  have hd : ∃ x : Fin (n + 1) → Bool,
      (fun y => f (y ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun y => f (y ∘ σ)) x := by
    obtain ⟨x, hx⟩ := hdep
    refine ⟨x ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    simpa [σ] using hx
  have hn : ∃ x y : Fin n → Bool,
      f (Fin.snoc x false ∘ σ) ≠ f (Fin.snoc y false ∘ σ) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simpa [σ, Helpers.PermInputs.snoc_swap] using hxy
  have he := Helpers.gate_elim n (fun x => f (x ∘ σ)) false s hd hn hg
  have hr := Helpers.PermInputs.relabel_size (fun j : Fin n => σ j.castSucc) _ s he
  have e : (fun x : Fin (n + 1) → Bool =>
      f (Fin.snoc (x ∘ fun j : Fin n => σ j.castSucc) false ∘ σ)) =
      (fun x => f (Function.update x p false)) := by
    funext x
    exact congrArg f (Helpers.PermInputs.snoc_swap n p x false)
  rwa [e] at hr

def HasEncoded {R N : ℕ} (E : (Fin R → Bool) → Fin N → Bool)
    (f : (Fin R → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn (E x)) = f x

theorem encoded_elim {R n : ℕ}
    (E E' : (Fin R → Bool) → Fin (n + 1) → Bool)
    (f f' : (Fin R → Bool) → Bool) (σ : Fin (n + 1) → Fin (n + 1))
    (p : Fin (n + 1)) (ρ : (Fin R → Bool) → Fin R → Bool)
    (hfix : ∀ x, E x ∘ σ = E x)
    (hnext : ∀ x, E' x = E (ρ x)) (hfnext : ∀ x, f' x = f (ρ x))
    (hzero : ∀ x, E' x p = false)
    (x0 x1 : Fin R → Bool)
    (hw : Function.update (E x0) p (!(E x0 p)) ∘ σ = E x1)
    (hf : f x1 ≠ f x0)
    (hnc : ∃ x y, f' x ≠ f' y)
    (s : ℕ) (h : HasEncoded E f (s + 1)) : HasEncoded E' f' s := by
  obtain ⟨C, hfan, hsize, hev⟩ := h
  let g : (Fin (n + 1) → Bool) → Bool := fun y => C.eval (List.ofFn (y ∘ σ))
  have hg : HasCircuitSize (n + 1) g (s + 1) :=
    Helpers.PermInputs.relabel_size σ _ (s + 1) ⟨C, hfan, hsize, fun _ => rfl⟩
  have hc : ∀ x, g (E x) = f x := by
    intro x
    change C.eval (List.ofFn (E x ∘ σ)) = f x
    rw [hfix, hev]
  have hc' : ∀ x, g (Function.update (E' x) p false) = f' x := by
    intro x
    rw [← hzero x, Function.update_eq_self, hnext, hc, ← hfnext]
  have hd : ∃ y, g (Function.update y p (!y p)) ≠ g y := by
    refine ⟨E x0, ?_⟩
    change C.eval (List.ofFn (Function.update (E x0) p (!(E x0 p)) ∘ σ)) ≠ g (E x0)
    rw [hw, hev, hc]
    exact hf
  have hn : ∃ x y, g (Function.update x p false) ≠ g (Function.update y p false) := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨E' x, E' y, by simpa only [hc'] using hxy⟩
  obtain ⟨D, hdFan, hdSize, hdEval⟩ := gate_elim_false_at n g p s hd hn hg
  exact ⟨D, hdFan, hdSize, fun x => (hdEval (E' x)).trans (hc' x)⟩

end PEqualNP.Outside.L_meta_650_aux.FreeFeatureElimination
