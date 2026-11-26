import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4231_1
    (threeStars :
      have decode : List ℕ → ℕ → Fin 20 → Bool := fun data r i =>
        (data.getD (r / 3) 0).testBit (20 * (r % 3) + i.val)
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 13 ∧
        (∀ m ∈ ([34, 66, 656386, 32770, 40, 136, 655624, 4104, 80, 655632, 528, 8208] : List ℕ),
          circuitFun 20 C (fun i => m.testBit i.val) = true) ∧
        ∀ r : Fin 44, circuitFun 20 C (decode [4665232155738143, 13518504604999695, 725368754528096277, 730724029253162005, 866973350870287389, 875963053248350355, 884986756446568478, 903000063497490454, 954792603833647132, 1012212425860929682, 1041183516279060867, 1062218301194542225, 1078371242023506996, 1142983005070916482, 1099479117384] r.val) = false)
    (combine :
      ∀ C D : Circuit, Monotone2 C → Monotone2 D →
        ∃ E : Circuit, Monotone2 E ∧ E.size ≤ C.size + D.size + 1 ∧
          ∀ x : Fin 20 → Bool, E.eval (List.ofFn x) = (C.eval (List.ofFn x) || D.eval (List.ofFn x))) :
    have x1 : List ℕ → ℕ → Fin (20 : ℕ) → Bool := fun (x1 : List ℕ) (x2 : ℕ) (x3 : Fin (20 : ℕ)) => (x1.getD (x2 / (3 : ℕ)) (0 : ℕ)).testBit ((20 : ℕ) * (x2 % (3 : ℕ)) + ↑x3); ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (23 : ℕ) ∧ (∀ (x3 : Fin (20 : ℕ)), PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x2 (x1 [(882706627014164513 : ℕ), (72567803150337 : ℕ), (74801153180674 : ℕ), (72062818869837956 : ℕ), (720866211591618600 : ℕ), (720875007625924616 : ℕ), (8606712336 : ℕ)] ↑x3) = Bool.true) ∧ ∀ (x3 : Fin (44 : ℕ)), PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x2 (x1 [(4665232155738143 : ℕ), (13518504604999695 : ℕ), (725368754528096277 : ℕ), (730724029253162005 : ℕ), (866973350870287389 : ℕ), (875963053248350355 : ℕ), (884986756446568478 : ℕ), (903000063497490454 : ℕ), (954792603833647132 : ℕ), (1012212425860929682 : ℕ), (1041183516279060867 : ℕ), (1062218301194542225 : ℕ), (1078371242023506996 : ℕ), (1142983005070916482 : ℕ), (1099479117384 : ℕ)] ↑x3) = Bool.false := by
  let mask (data : List ℕ) (r : ℕ) : ℕ :=
    ((data.getD (r / 3) 0) >>> (20 * (r % 3))) % 2^20
  let decode (data : List ℕ) (r : ℕ) (i : Fin 20) : Bool :=
    (data.getD (r / 3) 0).testBit (20 * (r % 3) + i.val)
  let positives : List ℕ := [882706627014164513, 72567803150337, 74801153180674, 72062818869837956, 720866211591618600, 720875007625924616, 8606712336]
  let negatives : List ℕ := [4665232155738143, 13518504604999695, 725368754528096277, 730724029253162005, 866973350870287389, 875963053248350355, 884986756446568478, 903000063497490454, 954792603833647132, 1012212425860929682, 1041183516279060867, 1062218301194542225, 1078371242023506996, 1142983005070916482, 1099479117384]
  let other : List ℕ := [34, 66, 656386, 32770, 40, 136, 655624, 4104, 80, 655632, 528, 8208]
  let D : Circuit :=
    ⟨[⟨.or,[5,9]⟩, ⟨.or,[14,16]⟩, ⟨.or,[20,21]⟩, ⟨.and,[0,22]⟩,
      ⟨.or,[6,7]⟩, ⟨.or,[11,16]⟩, ⟨.or,[24,25]⟩, ⟨.and,[2,26]⟩,
      ⟨.or,[23,27]⟩], 28⟩
  have hdMono : Monotone2 D := by
    intro g hg
    simp only [D, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hdSize : D.size = 9 := rfl
  have hdNeg : ∀ r : Fin 44, circuitFun 20 D (decode negatives r.val) = false := by
    dsimp only [D, decode, negatives]
    decide +kernel
  have covers : ∀ r : Fin 20, mask positives r.val ∈ other ∨
      circuitFun 20 D (decode positives r.val) = true := by
    dsimp only [mask, positives, other, D, decode]
    decide +kernel
  have rowEq : ∀ (r : Fin 20) (i : Fin 20),
      (mask positives r.val).testBit i.val = decode positives r.val i := by
    dsimp only [mask, positives, decode]
    decide +kernel
  obtain ⟨C, hc, hsize, hp, hn⟩ := threeStars
  obtain ⟨E, he, hes, heval⟩ := combine C D hc hdMono
  change ∃ E : Circuit, Monotone2 E ∧ E.size ≤ 23 ∧
    (∀ r : Fin 20, circuitFun 20 E (decode positives r.val) = true) ∧
      ∀ r : Fin 44, circuitFun 20 E (decode negatives r.val) = false
  refine ⟨E, he, by omega, ?_, ?_⟩
  · intro r
    change E.eval (List.ofFn (decode positives r.val)) = true
    rw [heval]
    rcases covers r with h | h
    · have eq : (fun i : Fin 20 => (mask positives r.val).testBit i.val) = decode positives r.val :=
        funext (rowEq r)
      have hval := hp (mask positives r.val) h
      rw [eq] at hval
      change C.eval (List.ofFn (decode positives r.val)) = true at hval
      rw [hval]
      rfl
    · change D.eval (List.ofFn (decode positives r.val)) = true at h
      rw [h, Bool.or_true]
  · intro r
    change E.eval (List.ofFn (decode negatives r.val)) = false
    rw [heval]
    have hc0 := hn r
    have hd0 := hdNeg r
    change C.eval (List.ofFn (decode negatives r.val)) = false at hc0
    change D.eval (List.ofFn (decode negatives r.val)) = false at hd0
    rw [hc0, hd0]
    rfl
