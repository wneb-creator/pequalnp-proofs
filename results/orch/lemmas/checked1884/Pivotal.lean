import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.Pivotal

def adj (p l : Fin 10) : Bool :=
  ([50,69,138,276,521,385,770,548,104,208] : List Nat).getD p.val 0 |>.testBit l.val

-- Every independent assignment to two auxiliary variables can coexist with a
-- witness that toggling the pivot alone makes the graph edge function change.
-- Either a selected auxiliary already neighbors p, or a fresh neighbor can be
-- activated while preserving independence and the two prescribed bits.
set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem extend_two :
    ∀ p a b : Fin 10, p ≠ a → p ≠ b → a ≠ b →
    ∀ A B : Bool, ¬ (A = true ∧ B = true ∧ adj a b = true) →
      (A = true ∧ adj p a = true) ∨ (B = true ∧ adj p b = true) ∨
      ∃ z : Fin 10, z ≠ a ∧ z ≠ b ∧ z ≠ p ∧ adj p z = true ∧
        (A = true → adj a z = false) ∧ (B = true → adj b z = false) := by
  decide +kernel

def target (x : Fin 10 → Bool) : Bool :=
  decide (∃ p l : Fin 10, x p = true ∧ x l = true ∧ adj p l = true)

theorem loopless : ∀ i : Fin 10, adj i i = false := by decide +kernel

theorem symmetric : ∀ i j : Fin 10, adj i j = adj j i := by decide +kernel

theorem pivotal_two (i j k : Fin 10) (a b : Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hab : ¬ (a = true ∧ b = true ∧ adj j k = true)) :
    ∃ x : Fin 10 → Bool, x j = a ∧ x k = b ∧
      ∀ z : Bool, target (Function.update x i z) = z := by
  have neg : a = true → b = true → adj j k = false := by grind
  obtain ⟨n, hpn, hjn, hkn, hja, hkb⟩ :
      ∃ n : Fin 10, adj i n = true ∧ (n = j → a = true) ∧ (n = k → b = true) ∧
        (a = true → adj j n = false) ∧ (b = true → adj k n = false) := by
    rcases extend_two i j k hij hik hjk a b hab with ⟨ha, hn⟩ | ⟨hb, hn⟩ | ⟨n,nj,nk,_,hi,hj,hk⟩
    · exact ⟨j, hn, fun _ => ha, fun h => (hjk h).elim, fun _ => loopless _, fun hb => (symmetric k j).trans (neg ha hb)⟩
    · exact ⟨k, hn, fun h => (hjk h.symm).elim, fun _ => hb, fun ha => neg ha hb, fun _ => loopless _⟩
    · exact ⟨n, hi, fun h => (nj h).elim, fun h => (nk h).elim, hj, hk⟩
  have hni : n ≠ i := by rintro rfl; simp [loopless] at hpn
  let x (v : Fin 10) : Bool := decide ((v = j ∧ a = true) ∨ (v = k ∧ b = true) ∨ v = n)
  have hfree (u v : Fin 10) (hu : x u = true) (hv : x v = true) : adj u v = false := by
    simp only [x, decide_eq_true_eq] at hu hv
    rcases hu with ⟨rfl,ha⟩ | ⟨rfl,hb⟩ | rfl <;>
      rcases hv with ⟨rfl,ha'⟩ | ⟨rfl,hb'⟩ | rfl <;>
      first | exact loopless _ | solve_by_elim | rw [symmetric]; solve_by_elim
  refine ⟨x, ?_, ?_, ?_⟩
  · cases a <;> simp_all [x]; grind
  · cases b <;> simp_all [x]; grind
  · intro z
    cases z with
    | false =>
      apply decide_eq_false_iff_not.mpr
      rintro ⟨u,v,hu,hv,he⟩
      have drop (w : Fin 10) (hw : Function.update x i false w = true) : x w = true := by
        by_cases h : w = i <;> simp_all [Function.update]
      exact Bool.noConfusion ((hfree u v (drop u hu) (drop v hv)).symm.trans he)
    | true =>
      apply decide_eq_true
      exact ⟨i,n,by simp,by simp [Function.update_of_ne hni, x],hpn⟩

end PEqualNP.Outside.L_meta_1884.Pivotal

theorem PEqualNP.Outside.L_meta_1884.Pivotal.statement : ∀ (i j k : Fin 10) (a b : Bool), i ≠ j → i ≠ k → j ≠ k → ¬ (a = true ∧ b = true ∧ ((([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD j.val 0).testBit k.val) = true) → ∃ x : Fin 10 → Bool, x j = a ∧ x k = b ∧ ∀ z : Bool, (decide (∃ p l : Fin 10, Function.update x i z p = true ∧ Function.update x i z l = true ∧ ((([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD p.val 0).testBit l.val) = true)) = z := PEqualNP.Outside.L_meta_1884.Pivotal.pivotal_two
