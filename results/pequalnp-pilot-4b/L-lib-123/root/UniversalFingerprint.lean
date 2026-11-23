import Mathlib

namespace PEqualNP.Outside.UniversalFingerprint

lemma avoid_all_small_sets {Certificate Seed : Type*}
    [Fintype Certificate] [Fintype Seed]
    (bad : Certificate → Finset Seed) (D : ℕ)
    (hcard : ∀ c, (bad c).card ≤ D)
    (hbudget : Fintype.card Certificate * D < Fintype.card Seed) :
    ∃ seed : Seed, ∀ c : Certificate, seed ∉ bad c := by
  classical
  let forbidden := Finset.univ.biUnion bad
  have hbound : forbidden.card ≤ Fintype.card Certificate * D := by
    calc
      forbidden.card ≤ ∑ c : Certificate, (bad c).card := Finset.card_biUnion_le
      _ ≤ ∑ _c : Certificate, D := Finset.sum_le_sum (fun c _ => hcard c)
      _ = Fintype.card Certificate * D := by simp
  have hne : forbidden ≠ Finset.univ := by
    intro heq
    have := hbound.trans_lt hbudget
    simp [heq] at this
  have hex : ∃ seed : Seed, seed ∉ forbidden := by
    by_contra! h
    apply hne
    ext seed
    simp [h seed]
  obtain ⟨seed, hseed⟩ := hex
  refine ⟨seed, fun c hc => hseed ?_⟩
  exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, hc⟩

lemma avoid_all_polynomial_roots {Certificate F : Type*}
    [Fintype Certificate] [Field F] [Fintype F]
    (errors : Certificate → Polynomial F) (D : ℕ)
    (hnonzero : ∀ c, errors c ≠ 0)
    (hdegree : ∀ c, (errors c).natDegree ≤ D)
    (hbudget : Fintype.card Certificate * D < Fintype.card F) :
    ∃ seed : F, ∀ c : Certificate, (errors c).eval seed ≠ 0 := by
  classical
  obtain ⟨seed, hseed⟩ := avoid_all_small_sets
    (fun c => (errors c).roots.toFinset) D
    (fun c => ((errors c).roots.toFinset_card_le).trans
      ((Polynomial.card_roots' (errors c)).trans (hdegree c))) hbudget
  refine ⟨seed, fun c hc => hseed c ?_⟩
  exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hnonzero c)).mpr hc)

lemma adaptive_certificates_rejected {Certificate Seed : Type*}
    [Fintype Certificate] [Fintype Seed]
    (accept : Seed → Certificate → Prop) (bad : Certificate → Finset Seed) (D : ℕ)
    (hsound : ∀ seed c, accept seed c → seed ∈ bad c)
    (hcard : ∀ c, (bad c).card ≤ D)
    (hbudget : Fintype.card Certificate * D < Fintype.card Seed) :
    ¬ ∀ seed : Seed, ∃ c : Certificate, accept seed c := by
  obtain ⟨seed, hseed⟩ := avoid_all_small_sets bad D hcard hbudget
  intro h
  obtain ⟨c, hc⟩ := h seed
  exact hseed c (hsound seed c hc)

end PEqualNP.Outside.UniversalFingerprint
