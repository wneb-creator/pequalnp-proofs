import ReaderDeletionCount
import RepairAssembly

namespace PEqualNP.Outside.L_meta_2448_aux.ReaderRepairCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2448_aux.ReaderDeletion
open PEqualNP.Outside.L_meta_2448_aux.ReaderDeletionCount
open PEqualNP.Outside.L_meta_2448_aux.RepairAssembly

lemma four_count (w : List Bool) (a b c d out : Nat)
    (ha : a < w.length) (hd : d < w.length) :
    count (fourGates w.length a b c d out) w =
      weight GateOp.and (w.getD c false && w.getD b false) +
      weight GateOp.and (w.getD d false && w.getD a false) := by
  let u := w.getD c false && w.getD b false
  have hs : step ⟨GateOp.and, [c, b]⟩ w = w ++ [u] := by
    simp [step, u, GateOp.eval]
  simp only [fourGates, count, contribution, weight, Nat.zero_add, Nat.add_zero]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  rw [hs, getD_snoc_lt w u d hd, getD_snoc_lt w u a ha]

theorem attach_count_eq (n : Nat) (D : Circuit) (a b c d : Nat)
    (ha : a < n + D.size) (hd : d < n + D.size) (x : Fin n → Bool)
    (hU : ((D.wires (List.ofFn x)).getD c false &&
      (D.wires (List.ofFn x)).getD b false) = false)
    (hV : ((D.wires (List.ofFn x)).getD d false &&
      (D.wires (List.ofFn x)).getD a false) = false) :
    count (attach n D a b c d).gates (List.ofFn x) =
      count D.gates (List.ofFn x) := by
  let w := wiresFrom D.gates (List.ofFn x)
  have hw : w.length = n + D.size := by simp [w, length_wiresFrom, Circuit.size]
  have hc := four_count w a b c d D.output (by omega) (by omega)
  change (w.getD c false && w.getD b false) = false at hU
  change (w.getD d false && w.getD a false) = false at hV
  rw [hU, hV] at hc
  simp only [weight, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hc
  change count (D.gates ++ fourGates (n + D.size) a b c d D.output)
    (List.ofFn x) = _
  rw [count_append]
  change count D.gates (List.ofFn x) +
    count (fourGates (n + D.size) a b c d D.output) w = _
  rw [← hw, hc, Nat.add_zero]

theorem weighted_attach_count_eq {I : Type} (s : Finset I) (n : Nat)
    (D : Circuit) (a b c d : Nat) (ha : a < n + D.size) (hd : d < n + D.size)
    (inputs : I → Fin n → Bool)
    (hU : ∀ i ∈ s, ((D.wires (List.ofFn (inputs i))).getD c false &&
      (D.wires (List.ofFn (inputs i))).getD b false) = false)
    (hV : ∀ i ∈ s, ((D.wires (List.ofFn (inputs i))).getD d false &&
      (D.wires (List.ofFn (inputs i))).getD a false) = false) :
    (∑ i ∈ s, count (attach n D a b c d).gates (List.ofFn (inputs i))) =
      ∑ i ∈ s, count D.gates (List.ofFn (inputs i)) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact attach_count_eq n D a b c d ha hd (inputs i) (hU i hi) (hV i hi)

theorem weighted_repair_count_lt {I : Type} (s : Finset I) (n : Nat)
    (pre post : List Gate) (g : Gate) (hpost : ∀ q ∈ post, MonoGate q)
    (D : Circuit) (hD : D.gates = (lowered n pre post).2)
    (a b c d : Nat) (ha : a < n + D.size) (hd : d < n + D.size)
    (inputs : I → Fin n → Bool)
    (hU : ∀ i ∈ s, ((D.wires (List.ofFn (inputs i))).getD c false &&
      (D.wires (List.ofFn (inputs i))).getD b false) = false)
    (hV : ∀ i ∈ s, ((D.wires (List.ofFn (inputs i))).getD d false &&
      (D.wires (List.ofFn (inputs i))).getD a false) = false)
    (j : I) (hj : j ∈ s)
    (hg : contribution g (wiresFrom pre (List.ofFn (inputs j))) = 1) :
    (∑ i ∈ s, count (attach n D a b c d).gates (List.ofFn (inputs i))) <
      ∑ i ∈ s, count (pre ++ g :: post) (List.ofFn (inputs i)) := by
  rw [weighted_attach_count_eq s n D a b c d ha hd inputs hU hV, hD]
  exact weighted_lowered_count_lt s n pre post g hpost inputs j hj hg

end PEqualNP.Outside.L_meta_2448_aux.ReaderRepairCount
