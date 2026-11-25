import Forced13Compile
import PairReaderCharge
import DirectFilterRows
import SafeNotRaise

namespace PEqualNP.Outside.L_meta_1884.TwoFilterAuxBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open SharedFilter StrongRelaxRows ElimManyCount

def input (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [!x 0]

def operand (pre : List Gate) (ins : List Nat) (x : Fin 10 → Bool) : Bool :=
  (ins.map fun i => (SafeNot.run pre (input x)).getD i false).headD false

lemma seed_row (m : Nat) : Forced13Compile.seed (StrongRelaxRows.row m) =
    input (DirectFilterRows.row10 m) := by
  simp [Forced13Compile.seed, StrongRelaxRows.row, input, DirectFilterRows.row10,
    List.ofFn_succ]

theorem auxiliary (pre post : List Gate) (ins : List Nat) (o : Nat)
    (hp : ∀ g ∈ pre, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hs : ∀ g ∈ post, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hsize : pre.length + post.length + 1 ≤ 18)
    (hread : 2 ≤ pre.countP (reads Forced13Compile.rails) +
      post.countP (reads Forced13Compile.rails))
    (hfilter1 : (⟨GateOp.and,[1,11 + pre.length]⟩ : Gate) ∈ post)
    (hfilter5 : (⟨GateOp.and,[5,11 + pre.length]⟩ : Gate) ∈ post)
    (hcompute : ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ ⟨.not,ins⟩ :: post,o⟩ (input x) = SoleOrPartner.target x)
    (hm : fiberMono (operand pre ins))
    (hi1 : independent 1 (operand pre ins)) (hi5 : independent 5 (operand pre ins))
    (hf1 : factor 1 (operand pre ins)) (hf5 : factor 5 (operand pre ins)) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 13 ∧
      (∀ m ∈ positives, D.eval (List.ofFn (StrongRelaxRows.row m)) = true) ∧
      (∀ m ∈ negatives, D.eval (List.ofFn (StrongRelaxRows.row m)) = false) := by
  let forced : Circuit := ⟨pre ++ ⟨GateOp.and,[]⟩ :: post,o⟩
  have hallowed : ∀ g ∈ post, g.op = .and ∨ g.op = .or := fun g hg => (hs g hg).1
  have hpositive : ∀ m ∈ positives,
      forced.eval (input (DirectFilterRows.row10 m)) = true := by
    intro m hm
    have ht := List.all_eq_true.mp DirectFilterRows.positives_true m hm
    have hc := hcompute (DirectFilterRows.row10 m)
    rw [ht] at hc
    have hle := SafeNot.replace_not_le pre post ins o
      (input (DirectFilterRows.row10 m)) hallowed
    exact Bool.le_iff_imp.mp hle hc
  have hnegative : ∀ m ∈ negatives,
      forced.eval (input (DirectFilterRows.row10 m)) = false := by
    intro m hmem
    have hh := DirectFilterRows.negative_rows (operand pre ins) hm hi1 hi5 hf1 hf5 m hmem
    have heq := SafeNot.replace_not_false pre post ins o
      (input (DirectFilterRows.row10 m)) hh
    have ht := (of_decide_eq_true (List.all_eq_true.mp DirectFilterRows.geometry m hmem)).1
    exact heq.trans ((hcompute _).trans ht)
  have hcharge : 4 ≤ pre.countP (reads Forced13Compile.rails) +
      post.countP (reads (insert (11 + pre.length) Forced13Compile.rails)) := by
    apply PairReaderCharge.direct_filters Forced13Compile.rails (11 + pre.length) 1 5 pre post
    · simp only [Forced13Compile.rails, Finset.mem_insert, Finset.mem_singleton, not_or]
      omega
    · decide
    · decide
    · decide
    · exact hread
    · exact hfilter1
    · exact hfilter5
  have hnonconstant : ∃ x y : Fin 9 → Bool,
      forced.eval (Forced13Compile.seed x) ≠ forced.eval (Forced13Compile.seed y) := by
    refine ⟨StrongRelaxRows.row 3, StrongRelaxRows.row 25, ?_⟩
    rw [seed_row, seed_row, hpositive 3 (by decide), hnegative 25 (by decide)]
    decide
  obtain ⟨D,hDmono,hDsize,hDeval⟩ := Forced13Compile.compile pre post o hp hs hsize
    hcharge hnonconstant
  refine ⟨D,hDmono,hDsize,?_,?_⟩
  · intro m hm
    rw [hDeval,seed_row]
    exact hpositive m hm
  · intro m hm
    rw [hDeval,seed_row]
    exact hnegative m hm

end PEqualNP.Outside.L_meta_1884.TwoFilterAuxBridge
