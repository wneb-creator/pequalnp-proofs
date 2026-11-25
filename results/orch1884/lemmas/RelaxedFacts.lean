import ClosedOrSafety
import SoleReaderFactor
import StrongRelaxRows

namespace PEqualNP.Outside.L_meta_1884.RelaxedFacts

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.LiftFix
open StrongRelaxRows

lemma singleton_cover : ∀ t : Fin 9,
    negatives.any (fun m => decide (below (fun i => decide (i = t)) (row m))) = true := by decide

lemma singleton_rejected (D : Circuit) (hM : Monotone2 D)
    (hn : ∀ m ∈ negatives, circuitFun 9 D (row m) = false) (t : Fin 9) :
    circuitFun 9 D (fun i => decide (i = t)) = false :=
  negative_below (circuitFun 9 D) (ClosedOrSafety.output_mono 9 D hM) hn _ (singleton_cover t)

lemma row_two_rejected (D : Circuit) (hM : Monotone2 D)
    (hn : ∀ m ∈ negatives, circuitFun 9 D (row m) = false) :
    circuitFun 9 D (row 2) = false :=
  negative_below (circuitFun 9 D) (ClosedOrSafety.output_mono 9 D hM) hn _ (by decide)

lemma nonconstant (D : Circuit)
    (hp : ∀ m ∈ positives, circuitFun 9 D (row m) = true)
    (hn : ∀ m ∈ negatives, circuitFun 9 D (row m) = false) :
    ∃ x y : Fin 9 → Bool, circuitFun 9 D x ≠ circuitFun 9 D y := by
  refine ⟨row 3, row 25, ?_⟩
  rw [hp 3 (by decide), hn 25 (by decide)]
  decide

lemma output_not_two (D : Circuit)
    (hp : ∀ m ∈ positives, circuitFun 9 D (row m) = true) : D.output ≠ 2 := by
  intro hout
  have hpos := hp 3 (by decide)
  change (D.wires (List.ofFn (row 3))).getD D.output false = true at hpos
  rw [hout, LowMergeProof.wires_input D _ 2 (by simp)] at hpos
  change false = true at hpos
  cases hpos

lemma some_reader_two (D : Circuit) (hM : Monotone2 D)
    (hp : ∀ m ∈ positives, circuitFun 9 D (row m) = true)
    (hn : ∀ m ∈ negatives, circuitFun 9 D (row m) = false) :
    ∃ g ∈ D.gates, 2 ∈ g.inputs := by
  by_contra hnone
  have haway : ∀ g ∈ D.gates, 2 ∉ g.inputs := by
    intro g hg ht
    exact hnone ⟨g, hg, ht⟩
  have hagree := SoleReader.ofFn_agree (2 : Fin 9) (row 2) (row 6) (by decide)
  have hf := (SoleReader.run_agree D.gates _ _ hagree haway).2.2 D.output (output_not_two D hp)
  change circuitFun 9 D (row 2) = circuitFun 9 D (row 6) at hf
  rw [row_two_rejected D hM hn, hp 6 (by decide)] at hf
  cases hf

lemma no_repeated_operand (n : Nat) (D : Circuit) (hM : Monotone2 D) (hR : ReadsBack n D)
    (hmin : ∀ E : Circuit, Monotone2 E → circuitFun n E = circuitFun n D → D.size ≤ E.size)
    (k a : Nat) (g : Gate) (hg : D.gates[k]? = some g) (hin : g.inputs = [a, a]) : False := by
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa using (hM g (List.mem_of_getElem? hg)).1
  apply ClosedOrSet.no_copy n D hM hR hmin k a (List.getElem?_eq_some_iff.mp hg).1
    (readsBack_get n D hR k g hg a (by simp [hin]))
  intro x
  rw [ClosedOrSafety.gate_value n D hR k g hg x]
  rcases hop with hop | hop <;> simp [hop, hin, GateOp.eval]

end PEqualNP.Outside.L_meta_1884.RelaxedFacts
