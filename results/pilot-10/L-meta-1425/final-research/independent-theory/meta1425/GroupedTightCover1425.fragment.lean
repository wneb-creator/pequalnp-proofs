def dirGroupsGood (width y : Nat) (groups : List (Nat × Nat)) : Bool :=
  groups.all fun p => (p.2 < 2 ^ width) && (!y.testBit p.1) &&
    (List.range width).all fun j => !p.2.testBit j || y.testBit j

theorem dirGroupsGood_sound {width y : Nat} {groups : List (Nat × Nat)}
    (hg : dirGroupsGood width y groups = true) :
    ∀ p ∈ groups, ∀ j, p.2.testBit j = true →
      y.testBit p.1 = false ∧ y.testBit j = true := by
  intro p hp j hj
  have hp' := List.all_eq_true.1 hg p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp'
  have hlt := mask_bit_lt hp'.1.1 hj
  have hc := List.all_eq_true.1 hp'.2 j (List.mem_range.2 hlt)
  exact ⟨hp'.1.2, by simpa only [hj, Bool.not_true, Bool.false_or] using hc⟩

theorem dirCover_tight_ok {m y s ws} (h : NatRun m y s ws)
    (hlen : ws.length = s + 1) (groups : List (Nat × Nat))
    (hpairs : ∀ p ∈ groups, ∀ j, p.2.testBit j = true →
      y.testBit p.1 = false ∧ y.testBit j = true) : dirCover groups ws = true := by
  apply dirCover_of_witness
  intro p hp j hj
  obtain ⟨hneg, hpos⟩ := hpairs p hp j hj
  by_contra hn
  have hle : ∀ w ∈ ws, w.testBit j = true → w.testBit p.1 = true := by
    intro w hw hj'
    cases hi : w.testBit p.1 with
    | false => exact False.elim (hn ⟨w, hw, hi, hj'⟩)
    | true => rfl
  have hf := run_tight_bits h j p.1 hlen hle hpos
  rw [hneg] at hf
  contradiction

theorem dirCover_tight_ok_of_good {width m y s ws groups}
    (h : NatRun m y s ws) (hlen : ws.length = s + 1)
    (hg : dirGroupsGood width y groups = true) : dirCover groups ws = true :=
  dirCover_tight_ok h hlen groups (dirGroupsGood_sound hg)
