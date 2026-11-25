import TwoPrefixFloor

namespace PEqualNP.Outside.L_meta_1884.TwoPrefixAndRaw

open PEqualNP.Outside.L_meta_2592.Binary17
open PEqualNP.Outside.L_meta_2592.Binary17.Geometry
open PEqualNP.Outside.L_meta_1884.TwoPrefixFloor

lemma second_raw_and_eighteen (a b v w : Fin 10)
    (hva : v ≠ a) (hvb : v ≠ b) (hvw : v ≠ w)
    {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ z ∈ S, z ∈ Extended.initial ∨
      z = Extended.bin 1 (pin a) (pin b) ∨ z = Extended.bin 0 (pin v) (pin w))
    (hr : Extended.bin 0 (pin v) (pin w) ∈ S)
    (hne : Extended.bin 0 (pin v) (pin w) ≠ pin v) : 18 ≤ k + 2 := by
  have qeq : Extended.bit (witness v w 0).1 (Extended.bin 1 (pin a) (pin b)) =
      Extended.bit (witness v w 0).2 (Extended.bin 1 (pin a) (pin b)) := by
    have h := congrArg₂ Bool.or (witness_other_pin v w 0 a hva.symm)
      (witness_other_pin v w 0 b hvb.symm)
    simpa [Extended.bin, Extended.bit] using h
  have hv : pin v ∈ S := by
    obtain ⟨z, hz, diff⟩ := Extended.live_row_difference run (witness_target v w 0 hvw)
    rcases raw z hz with hp | hq | hrr
    · obtain ⟨i, rfl⟩ := (pin_mem_iff z).mp hp
      by_cases hi : i = v
      · simpa [hi] using hz
      · exact False.elim (diff (witness_other_pin v w 0 i hi))
    · rw [hq] at diff
      exact False.elim (diff qeq)
    · rw [hrr] at diff
      exact False.elim (diff (witness_binary v w 0 hvw))
  have hz : projectV v (Extended.bin 0 (pin v) (pin w)) = zero := by
    rw [project_bin_commute, project_self]
    simp [bin, zero]
  have bound := suffix_sixteen v a b _ run raw hv hr hne hz
  omega

def exclusiveNeighbor (a b : Fin 10) : Fin 10 :=
  ((List.finRange 10).find? fun t =>
    (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List Nat).getD a.val 0).testBit t.val &&
    !(([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List Nat).getD b.val 0).testBit t.val &&
      decide (t ≠ a ∧ t ≠ b)).getD 0

def swapRows (a b : Fin 10) : Extended.Row × Extended.Row :=
  let t := exclusiveNeighbor a b
  (Fin.ofNat 1024 (2 ^ position t + 2 ^ position a),
   Fin.ofNat 1024 (2 ^ position t + 2 ^ position b))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma swap_rows : ∀ a b : Fin 10, a ≠ b →
    Extended.bit (swapRows a b).1 Extended.target ≠
      Extended.bit (swapRows a b).2 Extended.target ∧
    Extended.bit (swapRows a b).1 (Extended.bin 1 (pin a) (pin b)) =
      Extended.bit (swapRows a b).2 (Extended.bin 1 (pin a) (pin b)) ∧
    Extended.bit (swapRows a b).1 (Extended.bin 0 (pin a) (pin b)) =
      Extended.bit (swapRows a b).2 (Extended.bin 0 (pin a) (pin b)) ∧
    ∀ i : Fin 10, i ≠ a → i ≠ b →
      Extended.bit (swapRows a b).1 (pin i) =
        Extended.bit (swapRows a b).2 (pin i) := by
  decide +kernel

lemma second_same_and_eighteen (a b : Fin 10) (hab : a ≠ b)
    {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ z ∈ S, z ∈ Extended.initial ∨
      z = Extended.bin 1 (pin a) (pin b) ∨ z = Extended.bin 0 (pin a) (pin b))
    (hr : Extended.bin 0 (pin a) (pin b) ∈ S)
    (hna : Extended.bin 0 (pin a) (pin b) ≠ pin a)
    (hnb : Extended.bin 0 (pin a) (pin b) ≠ pin b) : 18 ≤ k + 2 := by
  have props := swap_rows a b hab
  have retained : pin a ∈ S ∨ pin b ∈ S := by
    obtain ⟨z, hz, diff⟩ := Extended.live_row_difference run props.1
    rcases raw z hz with hp | hq | hrr
    · obtain ⟨i, rfl⟩ := (pin_mem_iff z).mp hp
      by_cases hia : i = a
      · exact Or.inl (hia ▸ hz)
      by_cases hib : i = b
      · exact Or.inr (hib ▸ hz)
      exact False.elim (diff (props.2.2.2 i hia hib))
    · rw [hq] at diff
      exact False.elim (diff props.2.1)
    · rw [hrr] at diff
      exact False.elim (diff props.2.2.1)
  rcases retained with ha | hb
  · have hz : projectV a (Extended.bin 0 (pin a) (pin b)) = zero := by
      rw [project_bin_commute, project_self]
      simp [bin, zero]
    have bound := suffix_sixteen a a b _ run raw ha hr hna hz
    omega
  · have hz : projectV b (Extended.bin 0 (pin a) (pin b)) = zero := by
      rw [project_bin_commute, project_self]
      simp [bin, zero]
    have bound := suffix_sixteen b a b _ run raw hb hr hnb hz
    omega

end PEqualNP.Outside.L_meta_1884.TwoPrefixAndRaw
