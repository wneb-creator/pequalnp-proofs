import PEqualNP.Outside.L_meta_6581

namespace PEqualNP.Outside.Pilot113FirstStep

open PEqualNP.Outside.L_meta_6581

abbrev pin (j : Fin 10) : Extended.Sig := Extended.pins.getD j.val Extended.zero

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma initial_eq_ofFn : Extended.initial = List.ofFn pin := by
  decide +kernel

lemma raw_index {a : Extended.Sig} (ha : a ∈ Extended.initial) :
    ∃ i : Fin 10, pin i = a := by
  rw [initial_eq_ofFn] at ha
  exact List.mem_ofFn.mp ha

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma target_not_raw : Extended.target ∉ Extended.initial := by
  decide +kernel

lemma live_first_split {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) :
    ∃ (n : Nat) (U : Finset Extended.Sig) (i j : Fin 10) (d : Nat),
      k = n + 1 ∧ i ≠ j ∧ Extended.allowed true d ∧
      (∀ a ∈ U, a ∈ Extended.initial) ∧
      Extended.Live true Extended.target n (insert (Extended.bin d (pin i) (pin j)) U) := by
  cases k with
  | zero =>
    obtain ⟨rfl, _⟩ := run
    exact False.elim (target_not_raw (raw _ (Finset.mem_singleton_self _)))
  | succ n =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, _, tailRun⟩ := run
    obtain ⟨i, rfl⟩ := raw_index (raw a (Finset.mem_insert_self _ _))
    obtain ⟨j, rfl⟩ := raw_index (raw b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    refine ⟨n, U, i, j, d, rfl, ?_, hd, ?_, tailRun⟩
    · intro h
      exact hab (congrArg pin h)
    · intro a ha
      exact raw a (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha))

lemma all_first_steps_floor
    (firstBound : ∀ (n : Nat) (U : Finset Extended.Sig) (i j : Fin 10) (d : Nat),
      i ≠ j → Extended.allowed true d →
      (∀ a ∈ U, a ∈ Extended.initial) →
      Extended.Live true Extended.target n (insert (Extended.bin d (pin i) (pin j)) U) →
      17 ≤ n + 1)
    {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : 17 ≤ k := by
  obtain ⟨n, U, i, j, d, rfl, hij, hd, hraw, htail⟩ := live_first_split run raw
  exact firstBound n U i j d hij hd hraw htail

end PEqualNP.Outside.Pilot113FirstStep
