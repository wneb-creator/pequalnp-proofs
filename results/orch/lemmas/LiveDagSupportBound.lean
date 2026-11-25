import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.LiveDagCredit

theorem extra_arc_leaf_budget (V R L B : Finset ℕ) (C : ℕ → Finset ℕ)
    (hR : R ⊆ V) (hL : L ⊆ V)
    (hleaf : ∀ p ∈ L, C p = ∅)
    (hbranch : ∀ p ∈ V, p ∉ L → (C p).card ≤ 1 + (if p ∈ B then 1 else 0))
    (hlive : ∀ v ∈ V, v ∉ R → ∃ p ∈ V, v ∈ C p)
    (hextra : (∃ r ∈ R, ∃ p ∈ V, r ∈ C p) ∨
      (∃ p ∈ V, ∃ q ∈ V, ∃ v, p ≠ q ∧ v ∈ C p ∧ v ∈ C q)) :
    L.card + 1 ≤ R.card + B.card := by
  classical
  let E : Finset (ℕ × ℕ) := V.biUnion fun p => (C p).image fun v => (p,v)
  let D := E.image Prod.snd
  have memE (p v : ℕ) (hp : p ∈ V) (hv : v ∈ C p) : (p,v) ∈ E :=
    Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  have memD (p v : ℕ) (hp : p ∈ V) (hv : v ∈ C p) : v ∈ D :=
    Finset.mem_image.mpr ⟨(p,v), memE p v hp hv, rfl⟩
  have hsub : V \ R ⊆ D := by
    intro v hv
    obtain ⟨hvV, hvR⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨p, hp, hvp⟩ := hlive v hvV hvR
    exact memD p v hp hvp
  have hlower : (V \ R).card + 1 ≤ E.card := by
    rcases hextra with ⟨r, hr, p, hp, hrp⟩ | ⟨p, hp, q, hq, v, hpq, hvp, hvq⟩
    · have hsub' : insert r (V \ R) ⊆ D :=
        Finset.insert_subset_iff.mpr ⟨memD p r hp hrp, hsub⟩
      have hnot : r ∉ V \ R := by simp [hr]
      have hcard := Finset.card_le_card hsub'
      have himage : D.card ≤ E.card := Finset.card_image_le
      rw [Finset.card_insert_of_notMem hnot] at hcard
      omega
    · have hlt : D.card < E.card := by
        have hle : D.card ≤ E.card := Finset.card_image_le
        have hne : D.card ≠ E.card := by
          intro heq
          have hinj : Set.InjOn (fun z : ℕ × ℕ => z.2) (E : Set (ℕ × ℕ)) :=
            Finset.card_image_iff.mp heq
          have he := hinj (memE p v hp hvp) (memE q v hq hvq) rfl
          exact hpq (congrArg Prod.fst he)
        omega
      have hcard := Finset.card_le_card hsub
      omega
  have harcs : E.card ≤ ∑ p ∈ V, (C p).card := by
    calc
      E.card ≤ ∑ p ∈ V, ((C p).image fun v => (p,v)).card := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum fun _ _ => Finset.card_image_le
  have hdegree : ∀ p ∈ V, (C p).card + (if p ∈ L then 1 else 0) ≤
      1 + (if p ∈ B then 1 else 0) := by
    intro p hp
    by_cases hl : p ∈ L
    · simp [hl, hleaf p hl]
    · simpa only [hl, ite_false, Nat.add_zero] using hbranch p hp hl
  have hfL : V.filter (fun p => p ∈ L) = L := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hL h, h⟩⟩
  have hsL : (∑ p ∈ V, if p ∈ L then 1 else 0) = L.card := by
    rw [← Finset.card_filter, hfL]
  have hsB : (∑ p ∈ V, if p ∈ B then 1 else 0) ≤ B.card := by
    rw [← Finset.card_filter]
    exact Finset.card_le_card fun _ h => (Finset.mem_filter.mp h).2
  have hsum := Finset.sum_le_sum hdegree
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  rw [hsL] at hsum
  have hVR := Finset.card_sdiff_add_card_eq_card hR
  omega

theorem labels_covered_by_leaves {α : Type*} [DecidableEq α]
    (V L : Finset ℕ) (C : ℕ → Finset ℕ) (f : ℕ → Finset α)
    (hchild : ∀ p ∈ V, ∀ q ∈ C p, q ∈ V ∧ q < p)
    (hstep : ∀ p ∈ V, p ∉ L → f p ⊆ (C p).biUnion f) :
    ∀ p ∈ V, f p ⊆ L.biUnion f := by
  intro p
  induction p using Nat.strong_induction_on with
  | ind p ih =>
    intro hp a ha
    by_cases hl : p ∈ L
    · exact Finset.mem_biUnion.mpr ⟨p, hl, ha⟩
    · obtain ⟨q, hq, haq⟩ := Finset.mem_biUnion.mp (hstep p hp hl ha)
      obtain ⟨hqV, hqp⟩ := hchild p hp q hq
      exact ih q hqp hqV haq

theorem extra_arc_double_leaf_bound {α : Type*} [DecidableEq α]
    (V R L B : Finset ℕ) (C : ℕ → Finset ℕ) (f : ℕ → Finset α) (d : ℕ)
    (hR : R ⊆ V) (hL : L ⊆ V)
    (hleaf : ∀ p ∈ L, C p = ∅)
    (hbranch : ∀ p ∈ V, p ∉ L → (C p).card ≤ 1 + (if p ∈ B then 1 else 0))
    (hlive : ∀ v ∈ V, v ∉ R → ∃ p ∈ V, v ∈ C p)
    (hextra : (∃ r ∈ R, ∃ p ∈ V, r ∈ C p) ∨
      (∃ p ∈ V, ∃ q ∈ V, ∃ v, p ≠ q ∧ v ∈ C p ∧ v ∈ C q))
    (hchild : ∀ p ∈ V, ∀ q ∈ C p, q ∈ V ∧ q < p)
    (hstep : ∀ p ∈ V, p ∉ L → f p ⊆ (C p).biUnion f)
    (hsmall : ∀ p ∈ L, p ≠ d → (f p).card ≤ 1)
    (hdouble : (f d).card ≤ 2) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  have hcover := labels_covered_by_leaves V L C f hchild hstep
  have hsub : R.biUnion f ⊆ L.biUnion f := by
    intro a ha
    obtain ⟨p, hp, hap⟩ := Finset.mem_biUnion.mp ha
    exact hcover p (hR hp) hap
  have hsize : ∀ p ∈ L, (f p).card ≤ 1 + (if p = d then 1 else 0) := by
    intro p hp
    by_cases hd : p = d
    · simpa [hd] using hdouble
    · simpa [hd] using hsmall p hp hd
  have hsum := Finset.sum_le_sum hsize
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  have hfilter : L.filter (fun p => p = d) ⊆ {d} := by
    intro p hp
    exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hp).2
  have hbonus : (∑ p ∈ L, if p = d then 1 else 0) ≤ 1 := by
    rw [← Finset.card_filter]
    simpa using Finset.card_le_card hfilter
  have hleaves : (L.biUnion f).card ≤ L.card + 1 :=
    Finset.card_biUnion_le.trans (by omega)
  have hcredit := extra_arc_leaf_budget V R L B C hR hL hleaf hbranch hlive hextra
  exact (Finset.card_le_card hsub).trans (hleaves.trans hcredit)

end PEqualNP.Outside.L_meta_2732_aux.LiveDagCredit
