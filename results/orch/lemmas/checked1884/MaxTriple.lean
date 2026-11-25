import I4Bridge
import PairOrbit

namespace PEqualNP.Outside.L_meta_1884.MaxTriple

open PEqualNP.Outside.L_meta_2590_aux.Surplus
open PEqualNP.Outside.L_meta_1884_aux.I4Bridge

def I : Finset (Fin 10) := {1, 4, 5}
def O : Finset (Fin 10) := {2, 3, 6, 7, 8, 9}
def Simple (D : Dag) (c : Fin 10) : Prop :=
  ∃ Z, ∀ e ∈ sem_W 10 D c, e ≠ Z → (0 : Fin 10) ∈ supp 10 D (src D e)

lemma simple_of_slots {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    {c : Fin 10} (hc : c ≠ 0) (S : Finset (Nat × Bool))
    (hS : S ⊆ sem_W 10 D c)
    (h0 : ∀ e ∈ S, (0 : Fin 10) ∈ supp 10 D (src D e))
    (hcount : (sem_W 10 D c).card ≤ S.card + 1) : Simple D c := by
  classical
  obtain ⟨Z, hZ, hZ0⟩ := sem_antichain sem_petersen_gr h.1 hD hc
  refine ⟨Z, ?_⟩
  intro e he heZ
  by_contra he0
  have hZn : Z ∉ S := fun hz => hZ0 (h0 Z hz)
  have hen : e ∉ insert Z S := by
    simp only [Finset.mem_insert]
    rintro (heq | hes)
    · exact heZ heq
    · exact he0 (h0 e hes)
  have hh := Finset.card_le_card
    (Finset.insert_subset he (Finset.insert_subset hZ hS))
  rw [Finset.card_insert_of_notMem hen, Finset.card_insert_of_notMem hZn] at hh
  omega

lemma simple_of_profile_empty {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hI : ineligSet 10 D = I) (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    {c : Fin 10} (hc : c ∈ O) (hempty : profile D b c = ∅) : Simple D c := by
  classical
  have he : c ∈ eligSet 10 D := by
    have hnot : c ∉ I := by
      have hh : ∀ c : Fin 10, c ∈ O → c ∉ I := by decide
      exact hh c hc
    by_contra hne
    exact hnot (hI ▸ (sem_mem_inelig.mpr hne))
  have hc0 : c ≠ 0 := by
    have hh : ∀ c : Fin 10, c ∈ O → c ≠ 0 := by decide
    exact hh c hc
  have hn : ∃ i ∈ I, Adj i c ∧ Adj i 0 := by
    have hh : ∀ c : Fin 10, c ∈ O → ∃ i ∈ I, Adj i c ∧ Adj i 0 := by decide +kernel
    exact hh c hc
  obtain ⟨i, hi, hic, hi0⟩ := hn
  obtain ⟨pos, hp⟩ := k4_assigned sem_petersen_gr h hD
  obtain ⟨hg, hz, hn, -⟩ := hp.1 i (hI ▸ hi)
  have hw : pos i ∈ sem_W 10 D c := sem_mem_W.mpr
    ⟨hg, hn c hic, by rw [hz]; simp⟩
  have hcount := sem_code_count sem_petersen_gr h hD b hb c
  rw [show ({c} ∩ eligSet 10 D).card = 1 by simp [he]] at hcount
  change _ + _ = _ + (profile D b c).card at hcount
  rw [hempty, Finset.card_empty] at hcount
  apply simple_of_slots h hD hc0 {pos i}
  · simpa using hw
  · simpa using hn 0 hi0
  · simp only [Finset.card_singleton]
    omega

lemma simple_of_profile_subset {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    {c : Fin 10} (hc : c ∈ eligSet 10 D) (hc0 : c ≠ 0)
    (hne : (profile D b c).Nonempty) (hsub : profile D b c ⊆ profile D b 0) :
    Simple D c := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨hur, huc⟩ := Finset.mem_filter.mp hu
  have hu0 := (Finset.mem_filter.mp (hsub hu)).2
  exact ri_gen sem_petersen_gr h hD b hb hc0 hc
    (fun v hv hcv => (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hv, hcv⟩))).2)
    (w := u.1) ⟨huc, hu0⟩

lemma outside_eligible {D : Dag} (hI : ineligSet 10 D = I)
    {c : Fin 10} (hc : c ∈ O) : c ∈ eligSet 10 D := by
  have hh : ∀ c : Fin 10, c ∈ O → c ∉ I := by decide
  by_contra hne
  exact hh c hc (hI ▸ sem_mem_inelig.mpr hne)

lemma pivot_eligible {D : Dag} (hI : ineligSet 10 D = I) :
    (0 : Fin 10) ∈ eligSet 10 D := by
  by_contra hne
  have hh : (0 : Fin 10) ∈ I := hI ▸ sem_mem_inelig.mpr hne
  exact (by decide : (0 : Fin 10) ∉ I) hh

lemma profile_budget {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hsize : D.length ≤ 18) (hI : ineligSet 10 D = I)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b) :
    (residualUnits 10 D b).card ≤ 2 ∧ (profile D b 0).Nonempty := by
  classical
  have he := Finset.card_le_univ (eligSet 10 D)
  have hp : (eligSet 10 D).card = 7 := by
    have hc : (ineligSet 10 D).card + (eligSet 10 D).card = 10 := by
      rw [ineligSet, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin]
      simp only [Fintype.card_fin] at he
      omega
    rw [hI, show I.card = 3 by decide] at hc
    omega
  have hcount := card_residual h.1 b hb
  have hs := surplus_identity h
  rw [totalSurplus_split] at hs
  have hr : (residualUnits 10 D b).card ≤ 2 := by omega
  refine ⟨hr, ?_⟩
  have hc := SixOrbit.two_ineligible_neighbors_three h hD
    (i := 1) (j := 4) (x := 0) (by rw [hI]; decide) (by rw [hI]; decide)
    (by decide) (by decide) (by decide)
  have hf := sem_code_count sem_petersen_gr h hD b hb 0
  rw [show ({(0 : Fin 10)} ∩ eligSet 10 D).card = 1 by simp [pivot_eligible hI]] at hf
  change _ + _ = _ + (profile D b 0).card at hf
  exact Finset.card_pos.mp (by omega)

lemma simple_of_pivot_subset {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hI : ineligSet 10 D = I) (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    (hr : (residualUnits 10 D b).card ≤ 2) (hn : (profile D b 0).Nonempty)
    {c : Fin 10} (hc : c ∈ O) (hsub : profile D b 0 ⊆ profile D b c) : Simple D c := by
  classical
  obtain ⟨pos, hp⟩ := k4_assigned sem_petersen_gr h hD
  have hcE := outside_eligible hI hc
  have hc0 : c ≠ 0 := by
    have hh : ∀ c : Fin 10, c ∈ O → c ≠ 0 := by decide
    exact hh c hc
  have hS : I.image pos ⊆ sem_W 10 D c := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    have hh : ∀ i ∈ I, Adj i 0 := by decide +kernel
    exact profile_assigned h hD b hb hp (pivot_eligible hI) hcE hn hsub (hI ▸ hi) (hh i hi)
  have h0 : ∀ e ∈ I.image pos, (0 : Fin 10) ∈ supp 10 D (src D e) := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    have hh : ∀ i ∈ I, Adj i 0 := by decide +kernel
    exact (hp.1 i (hI ▸ hi)).2.2.1 0 (hh i hi)
  have hcard : (I.image pos).card = 3 := by
    rw [Finset.card_image_of_injOn (fun i hi j hj hij => hp.2 i (hI ▸ hi) j (hI ▸ hj) hij)]
    decide
  have hf := sem_code_count sem_petersen_gr h hD b hb c
  rw [show ({c} ∩ eligSet 10 D).card = 1 by simp [hcE]] at hf
  change _ + _ = _ + (profile D b c).card at hf
  have hpc := Finset.card_le_card (show profile D b c ⊆ residualUnits 10 D b from Finset.filter_subset _ _)
  exact simple_of_slots h hD hc0 (I.image pos) hS h0 (by omega)

lemma incomparable_singletons {α : Type*} [DecidableEq α]
    {R A B : Finset α} (hR : R.card ≤ 2) (hA : A ⊆ R) (hB : B ⊆ R)
    (hab : ¬ A ⊆ B) (hba : ¬ B ⊆ A) : A.card = 1 ∧ B.card = 1 := by
  classical
  obtain ⟨a, ha, han⟩ := Finset.not_subset.mp hab
  obtain ⟨b, hb, hbn⟩ := Finset.not_subset.mp hba
  have habn : a ≠ b := by rintro rfl; exact han hb
  have habR : ({a, b} : Finset α) = R := Finset.eq_of_subset_of_card_le
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hA ha
        · exact hB hb)
    (by simpa [Finset.card_pair habn] using hR)
  have hAs : A = {a} := by
    ext x
    constructor
    · intro hx
      have hxR := hA hx
      rw [← habR, Finset.mem_insert, Finset.mem_singleton] at hxR
      rcases hxR with hxa | rfl
      · simpa using hxa
      · exact (hbn hx).elim
    · simp only [Finset.mem_singleton]
      rintro rfl
      exact ha
  have hBs : B = {b} := by
    ext x
    constructor
    · intro hx
      have hxR := hB hx
      rw [← habR, Finset.mem_insert, Finset.mem_singleton] at hxR
      rcases hxR with rfl | hxb
      · exact (han hx).elim
      · simpa using hxb
    · simp only [Finset.mem_singleton]
      rintro rfl
      exact hb
  simp [hAs, hBs]

lemma singleton_complements_equal {α : Type*} [DecidableEq α]
    {R A B C : Finset α} (hR : R.card ≤ 2)
    (hA : A ⊆ R) (hB : B ⊆ R) (hC : C ⊆ R) (ha : A.Nonempty)
    (hb : B.card = 1) (hc : C.card = 1) (hba : ¬ B ⊆ A) (hca : ¬ C ⊆ A) : B = C := by
  classical
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hb
  obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hc
  have hbn : b ∉ A := by simpa using hba
  have hcn : c ∉ A := by simpa using hca
  have hab : a ≠ b := by rintro rfl; exact hbn ha
  have hac : a ≠ c := by rintro rfl; exact hcn ha
  by_cases hbc : b = c
  · rw [hbc]
  have hsub : ({a, b, c} : Finset α) ⊆ R := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hA ha
    · exact hB (Finset.mem_singleton_self _)
    · exact hC (Finset.mem_singleton_self _)
  have hh := Finset.card_le_card hsub
  simp [hab, hac, hbc] at hh
  omega

lemma nonsimple_profiles {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hI : ineligSet 10 D = I) (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    (hr : (residualUnits 10 D b).card ≤ 2) (hn : (profile D b 0).Nonempty)
    {c x : Fin 10} (hc : c ∈ O) (hx : x ∈ O)
    (hcn : ¬ Simple D c) (hxn : ¬ Simple D x) :
    (profile D b c).card = 1 ∧ profile D b x = profile D b c := by
  have hnp {v : Fin 10} (hv : v ∈ O) (hvS : ¬ Simple D v) :
      ¬ profile D b v ⊆ profile D b 0 := by
    intro hsub
    by_cases he : profile D b v = ∅
    · exact hvS (simple_of_profile_empty h hD hI b hb hv he)
    have hn := Finset.nonempty_iff_ne_empty.mpr he
    have hv0 : v ≠ 0 := by
      have hh : ∀ v : Fin 10, v ∈ O → v ≠ 0 := by decide
      exact hh v hv
    exact hvS (simple_of_profile_subset h hD b hb (outside_eligible hI hv) hv0 hn hsub)
  have hpn {v : Fin 10} (hv : v ∈ O) (hvS : ¬ Simple D v) :
      ¬ profile D b 0 ⊆ profile D b v := by
    intro hsub
    exact hvS (simple_of_pivot_subset h hD hI b hb hr hn hv hsub)
  have hc1 := (incomparable_singletons hr (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    (hpn hc hcn) (hnp hc hcn)).2
  have hx1 := (incomparable_singletons hr (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    (hpn hx hxn) (hnp hx hxn)).2
  refine ⟨hc1, singleton_complements_equal hr (Finset.filter_subset _ _)
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) hn hx1 hc1 (hnp hx hxn) (hnp hc hcn)⟩

lemma nonsimple_same_center {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hI : ineligSet 10 D = I) (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    (hr : (residualUnits 10 D b).card ≤ 2) (hn : (profile D b 0).Nonempty)
    {c x i j : Fin 10} (hc : c ∈ O) (hx : x ∈ O)
    (hcn : ¬ Simple D c) (hxn : ¬ Simple D x)
    (hi : i ∈ I) (hj : j ∈ I) (hic : Adj i c) (hjx : Adj j x) : i = j := by
  classical
  obtain ⟨hc1, hxc⟩ := nonsimple_profiles h hD hI b hb hr hn hc hx hcn hxn
  have hxnP : (profile D b x).Nonempty := Finset.card_pos.mp (by rw [hxc, hc1]; omega)
  have hcnP : (profile D b c).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨pos, hp⟩ := k4_assigned sem_petersen_gr h hD
  have hcE := outside_eligible hI hc
  have hxE := outside_eligible hI hx
  have hpi : pos i ∈ sem_W 10 D c :=
    profile_assigned h hD b hb hp hcE hcE hcnP (Finset.Subset.refl _) (hI ▸ hi) hic
  have hpj : pos j ∈ sem_W 10 D c :=
    profile_assigned h hD b hb hp hxE hcE hxnP (by rw [hxc]) (hI ▸ hj) hjx
  by_contra hij
  have hpij : pos i ≠ pos j := fun he => hij (hp.2 i (hI ▸ hi) j (hI ▸ hj) he)
  have hc0 : c ≠ 0 := by
    have hh : ∀ c : Fin 10, c ∈ O → c ≠ 0 := by decide
    exact hh c hc
  apply hcn
  apply simple_of_slots h hD hc0 {pos i, pos j}
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> assumption
  · intro e he
    have hh : ∀ i ∈ I, Adj i 0 := by decide +kernel
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact (hp.1 i (hI ▸ hi)).2.2.1 0 (hh i hi)
    · exact (hp.1 j (hI ▸ hj)).2.2.1 0 (hh j hj)
  · have hf := sem_code_count sem_petersen_gr h hD b hb c
    rw [show ({c} ∩ eligSet 10 D).card = 1 by simp [hcE]] at hf
    change _ + _ = _ + (profile D b c).card at hf
    rw [hc1] at hf
    rw [Finset.card_pair hpij]
    omega

lemma nonsimple_pivot_slots {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hI : ineligSet 10 D = I) (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    (hr : (residualUnits 10 D b).card ≤ 2) (hn : (profile D b 0).Nonempty)
    {pos : Fin 10 → Nat × Bool} (hp : k4_Pos 10 Adj D pos)
    {c : Fin 10} (hc : c ∈ O) (hcn : ¬ Simple D c) :
    sem_W 10 D 0 = I.image pos ∧ merges 10 D (carrierT 10 D {0}) = ∅ := by
  classical
  have hc0 : c ≠ 0 := by
    have hh : ∀ c : Fin 10, c ∈ O → c ≠ 0 := by decide
    exact hh c hc
  have hcp : ¬ profile D b c ⊆ profile D b 0 := by
    intro hsub
    by_cases he : profile D b c = ∅
    · exact hcn (simple_of_profile_empty h hD hI b hb hc he)
    exact hcn (simple_of_profile_subset h hD b hb (outside_eligible hI hc) hc0
      (Finset.nonempty_iff_ne_empty.mpr he) hsub)
  have hpc : ¬ profile D b 0 ⊆ profile D b c := by
    intro hsub
    exact hcn (simple_of_pivot_subset h hD hI b hb hr hn hc hsub)
  have hp1 := (incomparable_singletons hr (Finset.filter_subset _ _)
    (Finset.filter_subset _ _) hpc hcp).1
  change (profile D b 0).card = 1 at hp1
  have hS : I.image pos ⊆ sem_W 10 D 0 := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hg, hz, hn, -⟩ := hp.1 i (hI ▸ hi)
    have hh : ∀ i ∈ I, Adj i 0 := by decide +kernel
    exact sem_mem_W.mpr ⟨hg, hn 0 (hh i hi), by rw [hz]; simp⟩
  have hcard : (I.image pos).card = 3 := by
    rw [Finset.card_image_of_injOn (fun i hi j hj hij => hp.2 i (hI ▸ hi) j (hI ▸ hj) hij)]
    decide
  have hl := Finset.card_le_card hS
  have hf := sem_code_count sem_petersen_gr h hD b hb 0
  rw [show ({(0 : Fin 10)} ∩ eligSet 10 D).card = 1 by simp [pivot_eligible hI]] at hf
  change _ + _ = _ + (profile D b 0).card at hf
  rw [hp1] at hf
  refine ⟨(Finset.eq_of_subset_of_card_le hS (by omega)).symm, ?_⟩
  exact Finset.card_eq_zero.mp (by omega)

lemma simple_off_one_center {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hI : ineligSet 10 D = I) (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    (hr : (residualUnits 10 D b).card ≤ 2) (hn : (profile D b 0).Nonempty)
    {c : Fin 10} (hc : c ∈ O) (hcn : ¬ Simple D c) :
    ∃ i ∈ I, ∀ x ∈ O, ¬ Adj i x → Simple D x := by
  have hnbr : ∃ i ∈ I, Adj i c := by
    have hh : ∀ c : Fin 10, c ∈ O → ∃ i ∈ I, Adj i c := by decide +kernel
    exact hh c hc
  obtain ⟨i, hi, hic⟩ := hnbr
  refine ⟨i, hi, ?_⟩
  intro x hx hnix
  by_contra hxn
  have hnbr : ∃ j ∈ I, Adj j x := by
    have hh : ∀ c : Fin 10, c ∈ O → ∃ i ∈ I, Adj i c := by decide +kernel
    exact hh x hx
  obtain ⟨j, hj, hjx⟩ := hnbr
  have hij := nonsimple_same_center h hD hI b hb hr hn hc hx hcn hxn hi hj hic hjx
  exact hnix (hij ▸ hjx)

end PEqualNP.Outside.L_meta_1884.MaxTriple
