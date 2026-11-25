import PullPositiveKeep

namespace PEqualNP.Outside.L_meta_2373.Live1024.OneForcedBank
open PEqualNP.CircuitLowerBounds OneNotFirstAnd PEqualNP.Outside.L_meta_2373 LiftSeventeen

def bankOrder (r s : Row) (w : List Sig) : Prop :=
  ∀ v ∈ w, bit r v = true → bit s v = true

lemma positive_bin_order (r s : Row) (d : Nat) (a b : Sig) (hd : allowed false d)
    (ha : bit r a = true → bit s a = true) (hb : bit r b = true → bit s b = true) :
    bit r (bin d a b) = true → bit s (bin d a b) = true := by
  have hd' : d = 0 ∨ d = 1 := by
    rcases hd with hd | ⟨bad, hd⟩
    · omega
    · cases bad
  rcases hd' with rfl | rfl <;>
    simp only [bin, ↓reduceIte, bit, BitVec.getLsbD_and, BitVec.getLsbD_or] at *
  all_goals
    cases ar : a.getLsbD r.val <;> cases br : b.getLsbD r.val <;>
      cases ass : a.getLsbD s.val <;> cases bs : b.getLsbD s.val <;> simp_all

lemma positive_gate_order (r s : Row) (w : List Sig) (g : Gate)
    (legal : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (mono : isNot g = false) (order : bankOrder r s w) :
    bit r (gv w g) = true → bit s (gv w g) = true := by
  have rep := FreeBank.gate_rep_free w [] g legal mono
  simp only [List.append_nil] at rep
  rcases rep with rep | ⟨_, d, a, b, hd, ha, hb, pa, pb, ne, eq⟩
  · rcases rep with mem | constant
    · exact order _ mem
    · have cases' : gv w g = zero ∨ gv w g = one := by
        by_contra bad
        exact constant ⟨fun h => bad (Or.inl h), fun h => bad (Or.inr h)⟩
      rcases cases' with h | h
      · simp [h, bit, zero]
      · rw [h]
        intro _
        unfold bit one
        rw [BitVec.getLsbD_allOnes]
        simp
  · rw [eq]
    exact positive_bin_order r s d a b hd (order _ ha) (order _ hb)

lemma positive_execute_order (r s : Row) (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (mono : ∀ g ∈ gs, isNot g = false) (order : bankOrder r s w) :
    bankOrder r s (execute gs w) := by
  induction gs generalizing w with
  | nil => exact order
  | cons g gs ih =>
    apply ih (w ++ [gv w g]) (fun q hq => legal q (by simp [hq]))
      (fun q hq => mono q (by simp [hq]))
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact order v hv
    · have eq := List.mem_singleton.mp hv
      rw [eq]
      exact positive_gate_order r s w g (legal g (by simp)) (mono g (by simp)) order

set_option maxHeartbeats 1000000 in
lemma input_zero : ∀ a : Fin 10, bit (0 : Row) (input a) = false := by
  decide +kernel

lemma inputs_order (s : Row) : bankOrder 0 s inputs := by
  intro v hv
  obtain ⟨i, rfl⟩ := input_index v hv
  intro h
  have bad : false = true := (input_zero i).symm.trans h
  cases bad

lemma neg_drop_rows (h : Sig) (a : Fin 10) (forces : forcesInput h a) (hp : proper h) :
    ∃ s : Row, bit (0 : Row) (neg h) = true ∧ bit s (neg h) = false := by
  have hz : bit (0 : Row) h = false := by
    cases eq : bit (0 : Row) h
    · rfl
    · have bad := forces 0 eq
      rw [input_zero] at bad
      cases bad
  have some : ∃ s : Row, bit s h = true := by
    by_contra none
    have all : ∀ s : Row, bit s h = false := by
      intro s
      cases eq : bit s h
      · rfl
      · exact False.elim (none ⟨s, eq⟩)
    apply hp.1
    apply bit_ext
    intro s
    exact (all s).trans (by simp [bit, zero])
  obtain ⟨s, hs⟩ := some
  exact ⟨s, by rw [neg_bit, hz]; rfl, by rw [neg_bit, hs]; rfl⟩

lemma positive_prefix_safe (r s : Row) (gs : List Gate) (w : List Sig) (keep : Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (mono : ∀ g ∈ gs, isNot g = false) (order : bankOrder r s w)
    (on : bit r keep = true) (off : bit s keep = false) :
    ∀ pre post g, gs = pre ++ g :: post → gv (execute pre w) g ≠ keep := by
  intro pre post g eq same
  have legalPre : ∀ q ∈ pre, q.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      q.inputs.length ≤ 2 := fun q hq => legal q (by rw [eq]; simp [hq])
  have monoPre : ∀ q ∈ pre, isNot q = false := fun q hq => mono q (by rw [eq]; simp [hq])
  have preOrder := positive_execute_order r s pre w legalPre monoPre order
  have gateOrder := positive_gate_order r s (execute pre w) g
    (legal g (by rw [eq]; simp)) (mono g (by rw [eq]; simp)) preOrder
  rw [same] at gateOrder
  have bad := gateOrder on
  rw [off] at bad
  cases bad

end PEqualNP.Outside.L_meta_2373.Live1024.OneForcedBank
