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

end PEqualNP.Outside.L_meta_1884.MaxTriple
