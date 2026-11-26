import Mathlib
import PEqualNP.Defs

-- Retain a wire only until its last reader. Each retained family must
-- still separate every positive row from every negative row.
-- Going backward from the target, skip an unused output and replace a
-- retained output with its operands.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3188_482
    (lastUse : ∀ (base xs : List (BitVec 24)) (target : BitVec 24),
      target ∈ base ++ xs →
      (∀ j : Fin xs.length, let old := base ++ xs.take j.val
        xs.get j ∉ old ∧ xs.get j ≠ 0 ∧ xs.get j ≠ -1 ∧
          ∃ a ∈ old, ∃ b ∈ old, xs.get j = a &&& b ∨ xs.get j = a ||| b) →
      ∃ states : List (Finset (BitVec 24)), states.length ≤ xs.length + 1 ∧
        states.headD ∅ ⊆ base.toFinset ∧ states.getLastD ∅ = {target} ∧
        ∀ i : Fin (states.length - 1),
          let S := states.getD i.val ∅
          let T := states.getD (i.val + 1) ∅
          ∃ a ∈ S, ∃ b ∈ S, ∃ c : BitVec 24,
            a ≠ b ∧ c ∉ S ∧ c ≠ 0 ∧ c ≠ -1 ∧ (c = a &&& b ∨ c = a ||| b) ∧
              insert c (S \ {a, b}) ⊆ T ∧ T ⊆ insert c S)
    (noPath : ∀ states : List (Finset (BitVec 24)), states.length ≤ 15 →
      states.headD ∅ ⊆ {202052, 276515, 549652, 1097833, 101010,
        10616859, 4456668, 2624736, 13635328, 751444} →
      states.getLastD ∅ = {16773120} →
      (∀ i : Fin (states.length - 1),
        let S := states.getD i.val ∅
        let T := states.getD (i.val + 1) ∅
        ∃ a ∈ S, ∃ b ∈ S, ∃ c : BitVec 24,
          a ≠ b ∧ c ∉ S ∧ c ≠ 0 ∧ c ≠ -1 ∧ (c = a &&& b ∨ c = a ||| b) ∧
            insert c (S \ {a, b}) ⊆ T ∧ T ⊆ insert c S) →
      (∀ S ∈ states, ∀ p n : Fin 24,
        (16773120 : BitVec 24).getLsbD p.val = true → (16773120 : BitVec 24).getLsbD n.val = false →
        ∃ w ∈ S, w.getLsbD p.val = true ∧ w.getLsbD n.val = false) → False) :
    have x1 : Fin (9 : ℕ) → BitVec (24 : ℕ) := fun (x1 : Fin (9 : ℕ)) =>   have x2 : ℕ × ℕ := [((49 : ℕ), (1348 : ℕ)), ((67 : ℕ), (2083 : ℕ)), ((134 : ℕ), (788 : ℕ)), ((268 : ℕ), (105 : ℕ)), ((24 : ℕ), (2706 : ℕ)), ((2592 : ℕ), (27 : ℕ)), ((1088 : ℕ), (220 : ℕ)), ((640 : ℕ), (3296 : ℕ)), ((3328 : ℕ), (3840 : ℕ))].getD ↑x1 ((0 : ℕ), (0 : ℕ));   BitVec.ofNat (24 : ℕ) ((4096 : ℕ) * x2.1 + x2.2); have x2 : List (BitVec (24 : ℕ)) := List.ofFn x1 ++ [x1 (0 : Fin (9 : ℕ)) ||| x1 (2 : Fin (9 : ℕ))]; ∀ (x3 : List (BitVec (24 : ℕ))),   BitVec.ofNat (24 : ℕ) ((4095 : ℕ) * (4096 : ℕ)) ∈ x2 ++ x3 →     (∀ (x5 : Fin x3.length),         have x6 : List (BitVec (24 : ℕ)) := x2 ++ List.take (↑x5) x3;         x3.get x5 ∉ x6 ∧ x3.get x5 ≠ (0 : BitVec (24 : ℕ)) ∧ x3.get x5 ≠ (-1 : BitVec (24 : ℕ)) ∧ ∃ x7 ∈ x6, ∃ x8 ∈ x6, x3.get x5 = x7 &&& x8 ∨ x3.get x5 = x7 ||| x8) →       (15 : ℕ) ≤ x3.length := by
  classical
  let base : List (BitVec 24) := [202052, 276515, 549652, 1097833, 101010,
    10616859, 4456668, 2624736, 13635328, 751444]
  let target : BitVec 24 := 16773120
  let follows (S T : Finset (BitVec 24)) : Prop :=
    ∃ a ∈ S, ∃ b ∈ S, ∃ c : BitVec 24,
      a ≠ b ∧ c ∉ S ∧ c ≠ 0 ∧ c ≠ -1 ∧ (c = a &&& b ∨ c = a ||| b) ∧
        insert c (S \ {a, b}) ⊆ T ∧ T ⊆ insert c S
  let separates (S : Finset (BitVec 24)) : Prop :=
    ∀ p n : Fin 24, target.getLsbD p.val = true → target.getLsbD n.val = false →
      ∃ w ∈ S, w.getLsbD p.val = true ∧ w.getLsbD n.val = false
  have back {S T} (edge : follows S T) (after : separates T) : separates S := by
    intro p n hp hn
    obtain ⟨w, hw, wp, wn⟩ := after p n hp hn
    obtain ⟨a, ha, b, hb, c, _, _, _, _, op, _, old⟩ := edge
    rcases Finset.mem_insert.mp (old hw) with rfl | stay
    · rcases op with eq | eq
      · have both : a.getLsbD p.val = true ∧ b.getLsbD p.val = true := by
          simpa [eq] using wp
        cases an : a.getLsbD n.val
        · exact ⟨a, ha, both.1, an⟩
        · exact ⟨b, hb, both.2, by simpa [eq, an] using wn⟩
      · have neither : a.getLsbD n.val = false ∧ b.getLsbD n.val = false := by
          simpa [eq] using wn
        have either : a.getLsbD p.val = true ∨ b.getLsbD p.val = true := by
          simpa [eq] using wp
        rcases either with ap | bp
        · exact ⟨a, ha, ap, neither.1⟩
        · exact ⟨b, hb, bp, neither.2⟩
    · exact ⟨w, stay, wp, wn⟩
  have allStates : ∀ states : List (Finset (BitVec 24)),
      states.getLastD ∅ = {target} →
      (∀ i : Fin (states.length - 1), follows (states.getD i.val ∅) (states.getD (i.val + 1) ∅)) →
      ∀ S ∈ states, separates S := by
    intro states
    induction states with
    | nil => simp
    | cons S tail ih =>
      intro last edges T ht
      cases tail with
      | nil =>
        have same : T = S := List.mem_singleton.mp ht
        have only : S = {target} := by simpa using last
        rw [same, only]
        exact fun p n hp hn => ⟨target, Finset.mem_singleton_self target, hp, hn⟩
      | cons U rest =>
        have next : ∀ i : Fin ((U :: rest).length - 1),
            follows ((U :: rest).getD i.val ∅) ((U :: rest).getD (i.val + 1) ∅) := by
          intro i
          let j : Fin ((S :: U :: rest).length - 1) := ⟨i.val + 1, by
            have hi := i.isLt
            simp only [List.length_cons] at hi ⊢
            omega⟩
          exact edges j
        have covered := ih (by simpa using last) next
        rcases List.mem_cons.mp ht with same | memTail
        · rw [same]
          exact back (edges ⟨0, by simp⟩) (covered U (by simp))
        · exact covered T memTail
  intro _ raw xs reached valid
  have seed : raw = base := by decide +kernel
  have reached' : target ∈ raw ++ xs := reached
  by_contra! short
  obtain ⟨states, len, start, last, edges⟩ := lastUse raw xs target reached' valid
  have seeds : base.toFinset = ({202052, 276515, 549652, 1097833, 101010,
    10616859, 4456668, 2624736, 13635328, 751444} : Finset (BitVec 24)) := by decide +kernel
  exact noPath states (by omega) (by simpa only [seed, seeds] using start) last edges (allStates states last edges)
