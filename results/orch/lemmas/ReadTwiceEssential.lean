import ReadTwiceCounts
import BinarySixteen

namespace PEqualNP.Outside.L_meta_2592_aux.ReadTwiceCollapse

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_7493.CircuitProof
open PEqualNP.Outside.L_meta_7493.CircuitProof.Readers
open PEqualNP.Outside.L_meta_2592_aux.Restriction

lemma primary_origin_unary (n : ℕ) (gs : List Gate) (clean : CleanL n gs) :
    ∀ w, w < n + gs.length → ∀ small : origin n gs w < n,
      ∃ h : Bool → Bool, ∀ x : Fin n → Bool, vl gs x w = h (x ⟨origin n gs w, small⟩) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro bound small
    by_cases input : w < n
    · refine ⟨id, fun x => ?_⟩
      rw [vl_input gs x w input]
      change x ⟨w,input⟩ = x ⟨origin n gs w, small⟩
      congr 1
      apply Fin.ext
      exact (origin_input n gs w input).symm
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < gs.length := by omega
      let g := gs[j]
      have atGate : gs[j]? = some g := by simp [g]
      rcases clean j g atGate with ⟨op, i, before, inputs⟩ | ⟨op, a, b, _, _, inputs⟩
      · have copied : origin n gs (n + j) = origin n gs i := by
          rw [origin_gate n gs clean j g atGate]
          simp [op,isNotGate,inputs]
        have sourceSmall : origin n gs i < n := by omega
        obtain ⟨h, value⟩ := ih i before (by omega) sourceSmall
        refine ⟨fun b => !(h b), fun x => ?_⟩
        rw [vl_gate gs clean x j g atGate, op, inputs]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
        rw [value x]
        congr 2
        apply Fin.ext
        exact copied.symm
      · have born : origin n gs (n + j) = n + j := by
          rw [origin_gate n gs clean j g atGate]
          rcases op with op | op <;> simp [op,isNotGate]
        omega

lemma output_origin_nonprimary {n : ℕ} {f : (Fin n → Bool) → Bool}
    {gs : List Gate} {out : ℕ} (least : Least n f gs out)
    (nonconstant : ∃ x y, f x ≠ f y)
    (notUnary : ∀ v : Fin n, ∀ h : Bool → Bool, ¬ ∀ x, f x = h (x v)) :
    n ≤ origin n gs out := by
  have bound : out < n + gs.length := by
    by_contra tooBig
    obtain ⟨x,y,different⟩ := nonconstant
    apply different
    rw [← least.hev x, ← least.hev y,
      vl_beyond gs x out (by omega), vl_beyond gs y out (by omega)]
  by_contra small
  have small : origin n gs out < n := by omega
  obtain ⟨h, value⟩ := primary_origin_unary n gs least.hcl out bound small
  apply notUnary ⟨origin n gs out,small⟩ h
  intro x
  exact (least.hev x).symm.trans (value x)

lemma primary_read_positive (n : ℕ) (gs : List Gate) (out : ℕ) (clean : CleanL n gs)
    (live : ∀ j, j < gs.length → out ≠ n + j → ∃ q, j < q ∧ Reads gs q (n + j))
    (output : n ≤ origin n gs out) (v : Fin n) (used : ∃ q, Reads gs q v.val) :
    1 ≤ primaryReads n gs v := by
  obtain ⟨q,g,atGate,read⟩ := used
  have hq := (List.getElem?_eq_some_iff.mp atGate).1
  have occurs : ∃ s ∈ slots gs, slotOrigin n gs s = v.val := by
    cases flag : isNotGate g.op with
    | false =>
      simpa [origin_input n gs v.val v.isLt] using
        binary_read_slot n gs clean q v.val g atGate flag read
    | true =>
      have shape : g.inputs = [v.val] := by
        rcases clean q g atGate with ⟨_, i, _, inputs⟩ | ⟨op, _⟩
        · have eq : v.val = i := by simpa [inputs] using read
          simpa [eq] using inputs
        · rcases op with op | op <;> simp [op,isNotGate] at flag
      have copied : origin n gs (n + q) = v.val := by
        rw [origin_gate n gs clean q g atGate,flag]
        simpa [shape] using origin_input n gs v.val v.isLt
      rcases origin_reaches_slot n gs out clean live q hq with equal | occurs
      · have := v.isLt
        omega
      · simpa [copied] using occurs
  obtain ⟨s,member,equal⟩ := occurs
  apply Finset.one_le_card.mpr
  exact ⟨s,Finset.mem_filter.mpr ⟨member,equal⟩⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma petersen_dependent : ∀ i : Fin 10, Dep petersen i := by
  unfold Dep
  decide +kernel

lemma petersen_not_unary : ∀ v : Fin 10, ∀ h : Bool → Bool, ¬ ∀ x, petersen x = h (x v) := by
  intro v h value
  have low := value (Function.update (fun _ => false) v false)
  have high := value (Function.update (fun _ => true) v false)
  rw [(FirstOrigin.petersen_cofactor_values v false).1] at low
  rw [(FirstOrigin.petersen_cofactor_values v false).2] at high
  simp only [Function.update_self] at low high
  exact Bool.noConfusion (low.trans high.symm)

lemma least_petersen_reads {gs : List Gate} {out : ℕ} (least : Least 10 petersen gs out) :
    ∀ v : Fin 10, 1 ≤ primaryReads 10 gs v := by
  have nonconstant := BinarySixteen.petersen_nonconstant
  have output := output_origin_nonprimary least nonconstant petersen_not_unary
  intro v
  apply primary_read_positive 10 gs out least.hcl (least.live nonconstant) output v
  apply least.dep_read v (petersen_dependent v)
  intro b
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  rw [(FirstOrigin.petersen_cofactor_values v b).1, (FirstOrigin.petersen_cofactor_values v b).2]
  decide

lemma least_petersen_singleton_count {gs : List Gate} {out : ℕ}
    (least : Least 10 petersen gs out) :
    19 ≤ nonNotCount gs + (Finset.univ.filter (fun i => primaryReads 10 gs i = 1)).card := by
  have budget := least_primaryReads_sum least BinarySixteen.petersen_nonconstant
  have lower := singleton_bound (primaryReads 10 gs) (least_petersen_reads least)
  omega

lemma least_sixteen_three_singletons {gs : List Gate} {out : ℕ}
    (least : Least 10 petersen gs out) (small : nonNotCount gs ≤ 16) :
    3 ≤ (Finset.univ.filter (fun i => primaryReads 10 gs i = 1)).card := by
  have := least_petersen_singleton_count least
  omega

lemma least_seventeen_two_singletons {gs : List Gate} {out : ℕ}
    (least : Least 10 petersen gs out) (small : nonNotCount gs ≤ 17) :
    2 ≤ (Finset.univ.filter (fun i => primaryReads 10 gs i = 1)).card := by
  have := least_petersen_singleton_count least
  omega

end PEqualNP.Outside.L_meta_2592_aux.ReadTwiceCollapse
