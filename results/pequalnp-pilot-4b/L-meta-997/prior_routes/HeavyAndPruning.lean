import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_997.HeavyAndPruning

def Sound {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f x = true → ∃ p ∈ S, x p = true

def Increasing {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ p, x p = true → y p = true) → f x = true → f y = true

theorem sound_and {n : ℕ} (S : Finset (Fin n)) (f g : (Fin n → Bool) → Bool)
    (hf : Increasing f) (hg : Increasing g)
    (hfg : Sound S (fun x => f x && g x)) : Sound S f ∨ Sound S g := by
  classical
  by_contra h
  push Not at h
  obtain ⟨x, hx0⟩ := not_forall.mp h.1
  obtain ⟨hfx, hx⟩ := not_imp.mp hx0
  obtain ⟨y, hy0⟩ := not_forall.mp h.2
  obtain ⟨hgy, hy⟩ := not_imp.mp hy0
  let z : Fin n → Bool := fun p => x p || y p
  have hfz : f z = true := hf x z (fun p hp => by simp [z, hp]) hfx
  have hgz : g z = true := hg y z (fun p hp => by simp [z, hp]) hgy
  obtain ⟨p, hp, hz⟩ := hfg z (by simp [hfz, hgz])
  have hz1 : x p = true ∨ y p = true := by simpa [z] using hz
  rcases hz1 with hpx | hpy
  · exact hx ⟨p, hp, hpx⟩
  · exact hy ⟨p, hp, hpy⟩

end PEqualNP.Outside.L_meta_997.HeavyAndPruning
