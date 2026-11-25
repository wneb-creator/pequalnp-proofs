import OneNotForcedPair

namespace PEqualNP.Outside.L_meta_2373.Live1024.OneForcedBank
open PEqualNP.Outside.L_meta_2373 LiftSeventeen OneNotFirstAnd

def forcesInput (h : Sig) (a : Fin 10) : Prop :=
  ∀ r : Row, bit r h = true → bit r (input a) = true

lemma live_row_order {T : Sig} {k : Nat} {S : Finset Sig}
    (run : Live false T k S) (r s : Row)
    (ordered : ∀ w ∈ S, bit r w = true → bit s w = true) :
    bit r T = true → bit s T = true := by
  induction run using Live.ind with
  | stop hp => exact ordered T (by simp)
  | @binary k U a b d hd pa pb hab fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have ha := ordered a (by simp)
      have hb := ordered b (by simp)
      have hd' : d = 0 ∨ d = 1 := by
        rcases hd with hd | ⟨bad, hd⟩
        · omega
        · cases bad
      rcases hd' with rfl | rfl <;>
        simp only [bin, ↓reduceIte, bit, BitVec.getLsbD_and, BitVec.getLsbD_or] at *
      all_goals
        cases ar : a.getLsbD r.val <;> cases br : b.getLsbD r.val <;>
          cases ass : a.getLsbD s.val <;> cases bs : b.getLsbD s.val <;>
          simp_all
    · exact ordered w (by simp [hw])

set_option maxHeartbeats 1000000 in
lemma influence_values : ∀ a : Fin 10,
    bit (absentRow a) graph = false ∧ bit (presentRow a) graph = true ∧
    bit (absentRow a) (input a) = false := by
  decide +kernel

lemma value_zero (h : Sig) (a : Fin 10) (forces : forcesInput h a) :
    projected (rowMap a) h = (fun _ => false) := by
  funext r
  change bit (rowMap a r) h = false
  cases he : bit (rowMap a r) h
  · rfl
  · have bad := forces _ he
    have missing : bit (rowMap a r) (input a) = false := rowMap_missing a r
    rw [missing] at bad
    cases bad

lemma neg_value_one (h : Sig) (a : Fin 10) (forces : forcesInput h a) :
    projected (rowMap a) (neg h) = (fun _ => true) := by
  funext r
  change bit (rowMap a r) (neg h) = true
  have hz := congrFun (value_zero h a forces) r
  change bit (rowMap a r) h = false at hz
  rw [neg_bit, hz]
  rfl

lemma retained_positive (h : Sig) (a : Fin 10) (forces : forcesInput h a)
    {S : Finset Sig} {k : Nat} (sub : S ⊆ OneNotForcedPair.bank h)
    (run : Live false graph k S) : input a ∈ S ∨ h ∈ S := by
  by_contra missing
  have ma : input a ∉ S := fun ha => missing (Or.inl ha)
  have mh : h ∉ S := fun hh => missing (Or.inr hh)
  have hz : bit (absentRow a) h = false := by
    cases he : bit (absentRow a) h
    · rfl
    · have bad := forces _ he
      rw [(influence_values a).2.2] at bad
      cases bad
  have order : ∀ w ∈ S, bit (presentRow a) w = true → bit (absentRow a) w = true := by
    intro w hw
    have mem := sub hw
    rcases Finset.mem_insert.mp mem with rfl | mem
    · exact False.elim (mh hw)
    rcases Finset.mem_insert.mp mem with rfl | mem
    · intro _
      rw [neg_bit, hz]
      rfl
    · obtain ⟨i, rfl⟩ := input_index w (List.mem_toFinset.mp mem)
      have different : a ≠ i := by
        rintro rfl
        exact ma hw
      rw [requiredInputs.2 a i different]
      exact id
  have bad := live_row_order run (presentRow a) (absentRow a) order
    (influence_values a).2.1
  rw [(influence_values a).1] at bad
  cases bad

lemma bank_covered (h : Sig) (a : Fin 10) (forces : forcesInput h a)
    (w : Sig) (mem : w ∈ OneNotForcedPair.bank h) :
    Available false (NineSigned.inputs.map NineSigned.observe) (projected (rowMap a) w) := by
  rcases Finset.mem_insert.mp mem with eq | mem
  · rw [eq, value_zero h a forces]
    exact Or.inr (Or.inl ⟨false, rfl⟩)
  rcases Finset.mem_insert.mp mem with rfl | mem
  · rw [neg_value_one h a forces]
    exact Or.inr (Or.inl ⟨true, rfl⟩)
  · obtain ⟨i, rfl⟩ := input_index w (List.mem_toFinset.mp mem)
    exact ZeroProfiles.rows_available a i

lemma positive_tail_lower_used (h : Sig) (a : Fin 10) (forces : forcesInput h a)
    {S : Finset Sig} {k : Nat} (sub : S ⊆ OneNotForcedPair.bank h)
    (used : neg h ∈ S) (run : Live false graph k S) : 18 ≤ k := by
  have nt := neg_value_one h a forces
  have nonzero (v : Sig) (hv : projected (rowMap a) v = fun _ => false) : v ≠ neg h := by
    intro eq
    rw [eq, nt] at hv
    have bad := congrFun hv 0
    cases bad
  apply projected_mono_lower_two (rowMap a) (funext (rowMap_graph a)) S k run
    (fun w hw => bank_covered h a forces w (sub hw))
  rcases retained_positive h a forces sub run with ha | hh
  · have az : projected (rowMap a) (input a) = fun _ => false := funext (rowMap_missing a)
    exact ⟨input a, ha, neg h, used, nonzero _ az, ⟨false, az⟩, ⟨true, nt⟩⟩
  · have hz := value_zero h a forces
    exact ⟨h, hh, neg h, used, nonzero _ hz, ⟨false, hz⟩, ⟨true, nt⟩⟩

end PEqualNP.Outside.L_meta_2373.Live1024.OneForcedBank
