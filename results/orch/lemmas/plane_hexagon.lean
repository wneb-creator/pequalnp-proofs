import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2583

lemma regular_plane_dual {N k : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hk : 0 < k)
    (hrow : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = k)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = k)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (l m : Fin N) (hlm : l ≠ m) : ∃! p : Fin N, I p l ∧ I p m := by
  classical
  have hex : ∃ p : Fin N, I p l ∧ I p m := by
    by_contra h
    have hdisj : ∀ p : Fin N, ¬ (I p l ∧ I p m) := by
      intro p hp
      exact h ⟨p, hp⟩
    have hpos : 0 < (Finset.univ.filter (fun p => I p l)).card := by
      rw [hcol]
      exact hk
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    have hpl : I p l := (Finset.mem_filter.mp hp).2
    have hpm : ¬ I p m := fun hpm => hdisj p ⟨hpl, hpm⟩
    choose! f hf using fun (r : Fin N) (hr : I r m) =>
      (hu p r (by intro he; exact hpm (he.symm ▸ hr))).exists
    let A : Finset (Fin N) := Finset.univ.filter (fun r => I r m)
    let B : Finset (Fin N) := (Finset.univ.filter (fun n => I p n)).erase l
    have hfA (r : Fin N) (hr : r ∈ A) : I p (f r) ∧ I r (f r) :=
      hf r (Finset.mem_filter.mp hr).2
    have hsub : A.image f ⊆ B := by
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hn
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hfA r hr).1⟩⟩
      intro he
      exact hdisj r ⟨he ▸ (hfA r hr).2, (Finset.mem_filter.mp hr).2⟩
    have hinj : Set.InjOn f (A : Set (Fin N)) := by
      intro r hr s hs he
      by_contra hrs
      have hm : I r m ∧ I s m :=
        ⟨(Finset.mem_filter.mp hr).2, (Finset.mem_filter.mp hs).2⟩
      have hn : I r (f r) ∧ I s (f r) := ⟨(hfA r hr).2, he.symm ▸ (hfA s hs).2⟩
      have hfm : f r = m := (hu r s hrs).unique hn hm
      exact hpm (hfm ▸ (hfA r hr).1)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_iff.mpr hinj] at hcard
    have hA : A.card = k := hcol m
    have hB : B.card = k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hrow]
    omega
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, hp, ?_⟩
  intro r hr
  by_contra hrp
  exact hlm ((hu r p hrp).unique ⟨hr.1, hp.1⟩ ⟨hr.2, hp.2⟩)

lemma incidence_induced_hexagon {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hv : ∀ l l' : Fin N, l ≠ l' → ∃! p : Fin N, I p l ∧ I p l')
    (p r l m : Fin N) (hpl : I p l) (hrm : I r m)
    (hpm : ¬ I p m) (hrl : ¬ I r l) :
    ∃ s n : Fin N, p ≠ r ∧ p ≠ s ∧ r ≠ s ∧ l ≠ m ∧ l ≠ n ∧ m ≠ n ∧
      I p l ∧ I r m ∧ I p n ∧ I r n ∧ I s l ∧ I s m ∧ ¬ I s n := by
  have hpr : p ≠ r := by intro h; exact hrl (h ▸ hpl)
  have hlm : l ≠ m := by intro h; exact hpm (h ▸ hpl)
  obtain ⟨n, hn, _⟩ := hu p r hpr
  obtain ⟨s, hs, _⟩ := hv l m hlm
  have hps : p ≠ s := by intro h; exact hpm (h.symm ▸ hs.2)
  have hrs : r ≠ s := by intro h; exact hrl (h.symm ▸ hs.1)
  have hln : l ≠ n := by intro h; exact hrl (h.symm ▸ hn.2)
  have hmn : m ≠ n := by intro h; exact hpm (h.symm ▸ hn.1)
  refine ⟨s, n, hpr, hps, hrs, hlm, hln, hmn, hpl, hrm, hn.1, hn.2, hs.1, hs.2, ?_⟩
  intro hsn
  exact hln ((hu p s hps).unique ⟨hpl, hs.1⟩ ⟨hn.1, hsn⟩)

end PEqualNP.Outside.L_meta_2583
