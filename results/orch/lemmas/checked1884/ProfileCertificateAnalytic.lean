import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884_aux.ProfileCertificate

def endpoints (e : Fin 6) : Finset (Fin 4) :=
  ([{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}] : List (Finset (Fin 4))).getD e.val ∅

def bits (k : Fin 7) : Finset (Fin 3) :=
  Finset.univ.filter fun t => (k.val + 1).testBit t.val

def profile (f : Fin 6 → Fin 7) (e : Fin 6) : Finset (Fin 3) := bits (f e)

def dominated (f : Fin 6 → Fin 7) (e : Fin 6) : Finset (Fin 4) :=
  (Finset.univ.filter fun x => profile f x ⊆ profile f e).biUnion endpoints

theorem ends_card : ∀ e : Fin 6, (endpoints e).card = 2 := by decide +kernel

theorem ends_all : (Finset.univ.biUnion endpoints : Finset (Fin 4)) = Finset.univ := by
  decide +kernel

theorem ends_union : ∀ e d : Fin 6, e ≠ d → 3 ≤ (endpoints e ∪ endpoints d).card := by
  decide +kernel

theorem ends_difference : ∀ e d : Fin 6, e ≠ d → ∃ i ∈ endpoints e, i ∉ endpoints d := by
  decide +kernel

theorem bits_positive : ∀ k : Fin 7, 1 ≤ (bits k).card := by decide +kernel

theorem bits_at_most_three : ∀ k : Fin 7, (bits k).card ≤ 3 := by decide +kernel

theorem avoiding_card : ∀ a : Fin 3,
    (Finset.univ.filter fun k : Fin 7 => a ∉ bits k).card = 3 := by decide +kernel

theorem large_card : (Finset.univ.filter fun k : Fin 7 => 2 ≤ (bits k).card).card = 4 := by
  decide +kernel

theorem own_subset (f : Fin 6 → Fin 7) (e : Fin 6) : endpoints e ⊆ dominated f e := by
  intro i hi
  exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩, hi⟩

theorem full_dominated (f : Fin 6 → Fin 7) (e : Fin 6) (h : (profile f e).card = 3) :
    (dominated f e).card = 4 := by
  have hfull : profile f e = Finset.univ := Finset.eq_of_subset_of_card_le
    (Finset.subset_univ _) (by simpa using Nat.le_of_eq h.symm)
  have hf : (Finset.univ.filter fun x => profile f x ⊆ profile f e) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro x _
    rw [hfull]
    exact Finset.subset_univ _
  rw [dominated, hf, ends_all]
  decide

theorem closure (f : Fin 6 → Fin 7)
    (budget : ∀ c, (dominated f c).card ≤ (profile f c).card + 1) :
    ∃ v x c : Fin 6,
      (dominated f v).card = (profile f v).card + 1 ∧
      profile f x ⊆ profile f c ∧
      ∃ i : Fin 4, i ∈ endpoints v ∧ i ∈ endpoints x ∧ i ∉ endpoints c := by
  classical
  by_contra hn
  have no_cross (v x c : Fin 6)
      (hs : (dominated f v).card = (profile f v).card + 1)
      (hsub : profile f x ⊆ profile f c) (i : Fin 4)
      (hiv : i ∈ endpoints v) (hix : i ∈ endpoints x) : i ∈ endpoints c := by
    by_contra hic
    exact hn ⟨v, x, c, hs, hsub, i, hiv, hix, hic⟩
  have hinj : Function.Injective f := by
    intro v c hvc
    by_contra hne
    have hp : profile f v = profile f c := by simp only [profile, hvc]
    have hcsub : endpoints c ⊆ dominated f v := by
      intro i hi
      exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by rw [hp]⟩, hi⟩
    have hu := Finset.card_le_card (Finset.union_subset (own_subset f v) hcsub)
    have hthree := ends_union v c hne
    have hb := budget v
    have hmax := bits_at_most_three (f v)
    change (profile f v).card ≤ 3 at hmax
    have hsat : (dominated f v).card = (profile f v).card + 1 := by
      by_cases hfull : (profile f v).card = 3
      · rw [full_dominated f v hfull, hfull]
      · omega
    obtain ⟨i, hiv, hic⟩ := ends_difference v c hne
    exact hic (no_cross v v c hsat (by rw [hp]) i hiv hiv)
  have hlarge (v : Fin 6) : 2 ≤ (profile f v).card := by
    by_contra hsmall
    have hpos := bits_positive (f v)
    change 1 ≤ (profile f v).card at hpos
    have hone : (profile f v).card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
    have hlow := Finset.card_le_card (own_subset f v)
    rw [ends_card] at hlow
    have hb := budget v
    have hsat : (dominated f v).card = (profile f v).card + 1 := by omega
    have avoids (c : Fin 6) (hcv : c ≠ v) : a ∉ profile f c := by
      intro hac
      obtain ⟨i, hiv, hic⟩ := ends_difference v c (Ne.symm hcv)
      have hs : profile f v ⊆ profile f c := by
        rw [ha]
        exact Finset.singleton_subset_iff.mpr hac
      exact hic (no_cross v v c hsat hs i hiv hiv)
    have hsub : ((Finset.univ.erase v).image f) ⊆
        (Finset.univ.filter fun k : Fin 7 => a ∉ bits k) := by
      intro k hk
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, avoids c (Finset.mem_erase.mp hc).1⟩
    have hcount := Finset.card_le_card hsub
    have himage : ((Finset.univ.erase v).image f).card = (Finset.univ.erase v).card :=
      Finset.card_image_of_injOn (fun _ _ _ _ he => hinj he)
    rw [himage, avoiding_card] at hcount
    have he : (Finset.univ.erase v).card = 5 := by simp
    omega
  have hsub : Finset.univ.image f ⊆ (Finset.univ.filter fun k : Fin 7 => 2 ≤ (bits k).card) := by
    intro k hk
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlarge e⟩
  have hcount := Finset.card_le_card hsub
  have himage : (Finset.univ.image f).card = (Finset.univ : Finset (Fin 6)).card :=
    Finset.card_image_of_injOn (fun _ _ _ _ he => hinj he)
  rw [himage, large_card] at hcount
  norm_num at hcount

end PEqualNP.Outside.L_meta_1884_aux.ProfileCertificate
