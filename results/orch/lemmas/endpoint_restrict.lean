import constant_not_cut
import endpoint_consumers
import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_1886_aux.EndpointRestrict

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.ConstantSweep
open PEqualNP.Outside.L_meta_2592_aux.Stronger
open ConstantSweepMono MapRigidity

def embed (x : Fin 9 → Bool) : Fin 10 → Bool :=
  ![false,x 7,x 5,x 8,x 6,x 4,x 2,x 0,x 3,x 1]

def initialRefs : List Ref :=
  [.inl false,.inr 7,.inr 5,.inr 8,.inr 6,.inr 4,.inr 2,.inr 0,.inr 3,.inr 1,.inl false]

def marks : Finset ℕ := {0,10}

lemma cofactor (x : Fin 9 → Bool) : edge10 (embed x) = edge x := by
  simp [embed,edge10,edge,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm,Bool.and_comm]

lemma initial_related (x : Fin 9 → Bool) :
    related initialRefs (List.ofFn x) (EndpointOrder.initial (embed x)) := by
  constructor
  · rfl
  · simp [initialRefs,valid]

lemma marks_within : ∀ i ∈ marks, i < initialRefs.length := by
  intro i hi
  have h : i = 0 ∨ i = 10 := by simpa [marks] using hi
  rcases h with rfl | rfl <;> decide +kernel

lemma marks_constant : ∀ i ∈ marks, ∃ b : Bool, read initialRefs i = .inl b := by
  intro i hi
  have h : i = 0 ∨ i = 10 := by simpa [marks] using hi
  rcases h with rfl | rfl <;> exact ⟨false,rfl⟩

lemma monoGood_of_mono (gs : List Gate) (outIdx : ℕ) (h : Monotone2 (Circuit.mk gs outIdx)) :
    ∀ q ∈ gs, monoGood q := by
  intro q hq
  simpa only [monoGood,Set.mem_insert_iff,Set.mem_singleton_iff] using h q hq

lemma restrict (pre suffix : List Gate) (outIdx : ℕ)
    (monoPre : Monotone2 (Circuit.mk pre 0))
    (monoSuffix : Monotone2 (Circuit.mk suffix outIdx))
    (computes : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,[0]⟩ :: suffix) outIdx).eval (EndpointOrder.initial x) = edge10 x) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + (pre.filter (touched marks)).length +
        (suffix.filter (touched (insert (11 + pre.length) marks))).length + 1 ≤
          (Circuit.mk (pre ++ ⟨.not,[0]⟩ :: suffix) outIdx).size ∧
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = edge x := by
  obtain ⟨out,extraRefs,hout,hlen,hsize,hsem⟩ :=
    ConstantNotCut.cut marks pre suffix 0 false (monoGood_of_mono pre 0 monoPre)
      (monoGood_of_mono suffix outIdx monoSuffix) initialRefs 9 marks_within marks_constant
      (by decide +kernel) rfl
  have result : ∀ x : Fin 9 → Bool,
      value (run out (List.ofFn x)) (read (initialRefs ++ extraRefs) outIdx) = edge x := by
    intro x
    have hr := hsem (List.ofFn x) (EndpointOrder.initial (embed x)) (by simp) (initial_related x)
    have hv := read_value hr outIdx
    exact hv.trans ((computes (embed x)).trans (cofactor x))
  cases he : read (initialRefs ++ extraRefs) outIdx with
  | inl b =>
    have low := result (fun _ => false)
    have high := result (fun _ => true)
    simp only [he,value] at low high
    have diff : edge (fun _ => false) ≠ edge (fun _ => true) := by decide +kernel
    exact False.elim (diff (low.symm.trans high))
  | inr j =>
    refine ⟨Circuit.mk out j,?_,?_,?_⟩
    · intro q hq
      have h := hout q hq
      simpa only [monoGood,Set.mem_insert_iff,Set.mem_singleton_iff] using h
    · change out.length + (pre.filter (touched marks)).length +
        (suffix.filter (touched (insert (11 + pre.length) marks))).length + 1 ≤
          (pre ++ ⟨GateOp.not,[0]⟩ :: suffix).length
      change out.length + (pre.filter (touched marks)).length +
        (suffix.filter (touched (insert (11 + pre.length) marks))).length ≤
          pre.length + suffix.length at hsize
      simp only [List.length_append,List.length_cons]
      omega
    · intro x
      have h := result x
      change (run out (List.ofFn x)).getD j false = edge x
      simpa only [he,value] using h

end PEqualNP.Outside.L_meta_1886_aux.EndpointRestrict
