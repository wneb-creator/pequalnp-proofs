import EntryGateChecker

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem pairColumn_bits (i : Row) (d : Nat) (a b : Sig) :
    bit i (bin d a b) =
      (if d = 0 then bit i a && bit i b else if d = 1 then bit i a || bit i b else
        if d = 2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]

theorem pairColumn_gate (u : Bool) (d : Nat) (a b : Sig) (legal : allowed u d) :
    pairColumn u (bin d a b) ⊆ pairColumn u a ∪ pairColumn u b := by
  intro p hp
  change rowSeparates u p.1 p.2 a = true ∨ rowSeparates u p.1 p.2 b = true
  change rowSeparates u p.1 p.2 (bin d a b) = true at hp
  have bound : d < 4 := by rcases legal with h | h <;> omega
  interval_cases d <;> cases u <;> simp [allowed] at legal
  all_goals
    cases ha : bit p.1 a <;> cases hb : bit p.1 b <;>
      cases hc : bit p.2 a <;> cases he : bit p.2 b <;>
      simp [rowSeparates, pairColumn_bits, ha, hb, hc, he] at hp ⊢

theorem pairColumn_cover (u : Bool) (T : Sig) (k : Nat) (S : Finset Sig)
    (run : Live u T k S) :
    ∀ p ∈ pairColumn u T, ∃ v ∈ S, p ∈ pairColumn u v := by
  intro p hp
  exact live_rowSeparates run hp

end PEqualNP.Outside.L_meta_2373.Live1024
