import Mathlib
import PEqualNP.Defs

-- The twelve incident pairs are the minimal true inputs. Each choice of active points
-- has one maximal false input on the wires that the given proxies read.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2426_811
    (monotone : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C → Monotone (PEqualNP.MetaComplexity.circuitFun 26 C))
    (witness :
      let proxy : List (List ℕ) := [[0], [1], [2], [13], [14], [15], [17], [18], [19], [23], [24], [25],
        [13, 15], [14, 17], [15, 17], [15, 17, 18], [19, 23], [18, 19, 23], [17, 24],
        [17, 19, 24], [18, 25], [13, 19], [14, 23], [15, 23], [15, 23, 24], [24, 25]]
      let pos : List ℕ := [8193, 131073, 8388609, 33554433, 8194, 16386, 262146, 16777218,
        16388, 32772, 524292, 33554436]
      let neg : List ℕ := [59695104, 17612801, 42631170, 557059, 25567236, 17039365, 8519686, 7]
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ 13 ∧
        (∀ r ∈ pos, PEqualNP.MetaComplexity.circuitFun 26 C
          (fun i => (proxy.getD i.val []).any r.testBit) = true) ∧
        ∀ r ∈ neg, PEqualNP.MetaComplexity.circuitFun 26 C
          (fun i => (proxy.getD i.val []).any r.testBit) = false) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
    have x2 : List (List ℕ) :=
      [[(0 : ℕ)],
       [(1 : ℕ)], [(2 : ℕ)], [(13 : ℕ)], [(14 : ℕ)], [(15 : ℕ)], [(17 : ℕ)], [(18 : ℕ)], [(19 : ℕ)], [(23 : ℕ)],
       [(24 : ℕ)], [(25 : ℕ)], [(13 : ℕ), (15 : ℕ)], [(14 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ)],
       [(15 : ℕ), (17 : ℕ), (18 : ℕ)], [(19 : ℕ), (23 : ℕ)], [(18 : ℕ), (19 : ℕ), (23 : ℕ)], [(17 : ℕ), (24 : ℕ)],
       [(17 : ℕ), (19 : ℕ), (24 : ℕ)], [(18 : ℕ), (25 : ℕ)], [(13 : ℕ), (19 : ℕ)], [(14 : ℕ), (23 : ℕ)],
       [(15 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ), (24 : ℕ)], [(24 : ℕ), (25 : ℕ)]];
    ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3
      ∧ x3.size ≤ (13 : ℕ) ∧ ∀ (x4 : Fin (26 : ℕ) → Bool),
      (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x3 fun (x5 : Fin (26 : ℕ)) => (x2.getD ↑x5 []).any fun (x6 : ℕ) => x4 (Fin.ofNat (26 : ℕ) x6)) =
        Decidable.decide (∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), ↑x5 < (3 : ℕ)
          ∧ (∃ x7 ∈ x1, x5 = x6 + x7) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) := by
  let lines : Finset (Fin 13) := {0, 1, 3, 9}
  let proxy : List (List ℕ) := [[0], [1], [2], [13], [14], [15], [17], [18], [19], [23], [24], [25],
        [13, 15], [14, 17], [15, 17], [15, 17, 18], [19, 23], [18, 19, 23], [17, 24],
        [17, 19, 24], [18, 25], [13, 19], [14, 23], [15, 23], [15, 23, 24], [24, 25]]
  let pos : List ℕ := [8193, 131073, 8388609, 33554433, 8194, 16386, 262146, 16777218,
    16388, 32772, 524292, 33554436]
  let neg : List ℕ := [59695104, 17612801, 42631170, 557059, 25567236, 17039365, 8519686, 7]
  let edge : Fin 13 → Fin 13 → Prop := fun p l => p.val < 3 ∧ ∃ d ∈ lines, p = l + d
  let pack : (Fin 26 → Bool) → Fin 26 → Bool :=
    fun x i => (proxy.getD i.val []).any (fun j => x (Fin.ofNat 26 j))
  let row : ℕ → Fin 26 → Bool := fun r i => (proxy.getD i.val []).any r.testBit
  let used : List ℕ := proxy.flatten
  have used_bound : ∀ j ∈ used, j < 26 := by decide +kernel
  have positive : ∀ p l : Fin 13, edge p l →
      ∃ r ∈ pos, ∀ j : Fin 26, r.testBit j.val = true ↔
        j = Fin.castAdd 13 p ∨ j = Fin.natAdd 13 l := by decide +kernel
  have negative : ∀ (c : Fin 8) (j : Fin 26), j.val ∈ used →
      (j.val < 3 ∧ (neg.getD c.val 0).testBit j.val = c.val.testBit j.val) ∨
      (neg.getD c.val 0).testBit j.val = true ∨
      ∃ p l : Fin 13, edge p l ∧ c.val.testBit p.val = true ∧ j = Fin.natAdd 13 l := by
    decide +kernel
  have proxy_used (i : Fin 26) (j : ℕ) (hj : j ∈ proxy.getD i.val []) : j ∈ used := by
    apply List.mem_flatten.mpr
    refine ⟨proxy.getD i.val [], ?_, hj⟩
    have hi : i.val < proxy.length := by simp [proxy]
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have ofNat_val (j : ℕ) (hj : j ∈ used) : (Fin.ofNat 26 j).val = j :=
    Nat.mod_eq_of_lt (used_bound j hj)
  obtain ⟨C, hC, size, yes, no⟩ := witness
  change ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
    C.size ≤ 13 ∧ ∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 C (pack x) =
    decide (∃ p l : Fin 13, p.val < 3 ∧ (∃ d ∈ lines, p = l + d) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
  refine ⟨C, hC, size, ?_⟩
  intro x
  let f := PEqualNP.MetaComplexity.circuitFun 26 C
  have hmono : Monotone f := monotone C hC
  by_cases hx : ∃ p l : Fin 13, p.val < 3 ∧ (∃ d ∈ lines, p = l + d) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  · rw [decide_eq_true hx]
    obtain ⟨p, l, hp, hl, hpt, hln⟩ := hx
    obtain ⟨r, hr, hrow⟩ := positive p l ⟨hp, hl⟩
    have hle : row r ≤ pack x := by
      intro i
      apply Bool.le_iff_imp.mpr
      intro hi
      obtain ⟨j, hj, hjtrue⟩ := List.any_eq_true.mp hi
      apply List.any_eq_true.mpr
      refine ⟨j, hj, ?_⟩
      have hv := ofNat_val j (proxy_used i j hj)
      have hit := (hrow (Fin.ofNat 26 j)).mp (by simpa only [hv] using hjtrue)
      rcases hit with he | he
      · simpa only [he] using hpt
      · simpa only [he] using hln
    exact Bool.eq_true_of_true_le (yes r hr ▸ hmono hle)
  · rw [decide_eq_false hx]
    have hc : ∃ c : Fin 8, ∀ j : Fin 26, j.val < 3 → c.val.testBit j.val = x j := by
      have d : ∀ a b c : Bool, ∃ m : Fin 8,
          m.val.testBit 0 = a ∧ m.val.testBit 1 = b ∧ m.val.testBit 2 = c := by decide +kernel
      obtain ⟨m, h0, h1, h2⟩ := d (x 0) (x 1) (x 2)
      refine ⟨m, ?_⟩
      intro j hj
      have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
    obtain ⟨c, hc⟩ := hc
    let r := neg.getD c.val 0
    have hr : r ∈ neg := by
      have hlen : c.val < neg.length := by simp [neg]
      change neg.getD c.val 0 ∈ neg
      rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem hlen
    have hle : pack x ≤ row r := by
      intro i
      apply Bool.le_iff_imp.mpr
      intro hi
      obtain ⟨j, hj, hjtrue⟩ := List.any_eq_true.mp hi
      apply List.any_eq_true.mpr
      refine ⟨j, hj, ?_⟩
      let k : Fin 26 := Fin.ofNat 26 j
      have hused := proxy_used i j hj
      have hk : k.val = j := ofNat_val j hused
      have kn := negative c k (by simpa only [hk] using hused)
      rcases kn with ⟨hsmall, hp⟩ | hp | ⟨p, l, he, hpb, hl⟩
      · simpa only [hk, r] using hp.trans ((hc k hsmall).trans hjtrue)
      · simpa only [hk, r] using hp
      · exfalso
        apply hx
        have hp : x (Fin.castAdd 13 p) = true := by
          have hval : (Fin.castAdd 13 p).val = p.val := rfl
          rw [← hc _ (by simpa only [hval] using he.1), hval]
          exact hpb
        have hline : x k = true := hjtrue
        exact ⟨p, l, he.1, he.2, hp, hl ▸ hline⟩
    exact Bool.eq_false_of_le_false (no r hr ▸ hmono hle)
