import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.Averaging

lemma touch_double_count {V R : Type*} [DecidableEq V] [Fintype R]
    (blocks : Finset (Finset V)) (rows : R → V → Bool) :
    (∑ B ∈ blocks, (Finset.univ.filter fun r : R => ∃ v ∈ B, rows r v = true).card) =
      ∑ r : R, (blocks.filter fun B => ∃ v ∈ B, rows r v = true).card := by
  classical
  simp only [Finset.card_filter]
  exact Finset.sum_comm

lemma union_card_le_eight {V R : Type*} [DecidableEq V] [Fintype R]
    (blocks : Finset (Finset V)) (rows : R → V → Bool)
    (hrows : Fintype.card R = 468)
    (hdis : (blocks : Set (Finset V)).PairwiseDisjoint id)
    (hsize : ∀ B ∈ blocks, B.card ≤ 2)
    (htouch : ∀ B ∈ blocks, 78 * B.card + 48 ≤
      (Finset.univ.filter fun r : R => ∃ v ∈ B, rows r v = true).card)
    (hcap : ∀ r : R, (blocks.filter fun B => ∃ v ∈ B, rows r v = true).card ≤ 2) :
    (blocks.biUnion id).card ≤ 8 := by
  classical
  let u := (blocks.biUnion id).card
  have hu : u = ∑ B ∈ blocks, B.card := Finset.card_biUnion hdis
  have hsmall : u ≤ 2 * blocks.card := by
    rw [hu]
    calc
      (∑ B ∈ blocks, B.card) ≤ ∑ B ∈ blocks, 2 := Finset.sum_le_sum hsize
      _ = 2 * blocks.card := by simp [Nat.mul_comm]
  have hlower : 78 * u + 48 * blocks.card ≤
      ∑ B ∈ blocks, (Finset.univ.filter fun r : R => ∃ v ∈ B, rows r v = true).card := by
    calc
      78 * u + 48 * blocks.card = ∑ B ∈ blocks, (78 * B.card + 48) := by
        rw [hu]
        simp [Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum htouch
  rw [touch_double_count] at hlower
  have hupper : (∑ r : R, (blocks.filter fun B => ∃ v ∈ B, rows r v = true).card) ≤ 936 := by
    calc
      _ ≤ ∑ r : R, 2 := Finset.sum_le_sum (fun r _ => hcap r)
      _ = 936 := by simp [hrows]
  change u ≤ 8
  omega

lemma block_touch_lower {V R : Type*} [DecidableEq V] [Fintype R]
    (rows : R → V → Bool)
    (hsingle : ∀ v : V, 126 ≤ (Finset.univ.filter fun r : R => rows r v = true).card)
    (hpair : ∀ u v : V, u ≠ v → 204 ≤
      (Finset.univ.filter fun r : R => rows r u = true ∨ rows r v = true).card)
    (B : Finset V) (hne : B.Nonempty) (hsize : B.card ≤ 2) :
    78 * B.card + 48 ≤
      (Finset.univ.filter fun r : R => ∃ v ∈ B, rows r v = true).card := by
  classical
  have hpos : 0 < B.card := Finset.card_pos.mpr hne
  have hc : B.card = 1 ∨ B.card = 2 := by omega
  rcases hc with hc | hc
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    simpa using hsingle v
  · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hc
    simpa [huv] using hpair u v huv

lemma packing_union_card_le_eight {V R : Type*} [DecidableEq V] [Fintype R]
    (blocks : Finset (Finset V)) (rows : R → V → Bool)
    (hrows : Fintype.card R = 468)
    (hdis : (blocks : Set (Finset V)).PairwiseDisjoint id)
    (hne : ∀ B ∈ blocks, B.Nonempty)
    (hsize : ∀ B ∈ blocks, B.card ≤ 2)
    (hsingle : ∀ v : V, 126 ≤ (Finset.univ.filter fun r : R => rows r v = true).card)
    (hpair : ∀ u v : V, u ≠ v → 204 ≤
      (Finset.univ.filter fun r : R => rows r u = true ∨ rows r v = true).card)
    (hcap : ∀ r : R, (blocks.filter fun B => ∃ v ∈ B, rows r v = true).card ≤ 2) :
    (blocks.biUnion id).card ≤ 8 :=
  union_card_le_eight blocks rows hrows hdis hsize
    (fun B hB => block_touch_lower rows hsingle hpair B (hne B hB) (hsize B hB)) hcap

end PEqualNP.Outside.L_meta_1896_aux.Averaging
