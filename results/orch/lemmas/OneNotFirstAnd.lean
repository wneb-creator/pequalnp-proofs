import ZeroProfilesMonotone16
import PetersenEighteenExtension

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

lemma mono_reach_bridge {q : Nat} {bank : List (Live1024.Wire NineSigned.Row)}
    (h : Live1024.Reach false (NineSigned.inputs.map NineSigned.observe) q bank) :
    NineSigned.Reach false (NineSigned.inputs.map NineSigned.observe) q bank := by
  induction h using Live1024.Reach.ind with
  | start => rfl
  | two op h ha hb ih => exact NineSigned.Reach.two op ih ha hb

lemma projected_mono_lower_two (rows : NineSigned.Row → Live1024.Row)
    (goal : projected rows Live1024.graph = NineSigned.observe NineSigned.graph)
    (S : Finset Live1024.Sig) (k : Nat) (run : Live1024.Live false Live1024.graph k S)
    (covered : ∀ a ∈ S, Live1024.Available false (NineSigned.inputs.map NineSigned.observe)
      (projected rows a))
    (constants : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      Live1024.Constant (projected rows a) ∧ Live1024.Constant (projected rows b)) : 18 ≤ k := by
  have trace := Live1024.list_run run S.toList (Finset.nodup_toList S) (by simp)
  have nc : ¬ Live1024.Constant (Live1024.restrictRows rows (Live1024.observe Live1024.graph)) := by
    change ¬ Live1024.Constant (projected rows Live1024.graph)
    rw [goal]
    exact NineSigned.observe_proper NineSigned.graph_proper
  have supply : Live1024.supply false (NineSigned.inputs.map NineSigned.observe)
      ((S.toList.map Live1024.observe).map (Live1024.restrictRows rows)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact covered a (Finset.mem_toList.mp ha)
  have prior (q : Nat) (bank : List (Live1024.Wire NineSigned.Row))
      (h : Live1024.Reach false (NineSigned.inputs.map NineSigned.observe) q bank)
      (hv : Live1024.Available false bank
        (Live1024.restrictRows rows (Live1024.observe Live1024.graph))) : 16 ≤ q := by
    change Live1024.Available false bank (projected rows Live1024.graph) at hv
    rw [goal] at hv
    exact NineSigned.nine_monotone_reach_lower q bank (mono_reach_bridge h) hv
  have bound := Live1024.projected_bound rows trace nc Live1024.Reach.start supply prior
  obtain ⟨a, ha, b, hb, hne, ca, cb⟩ := constants
  have mass := mass_two (projected rows) (Finset.mem_toList.mpr ha)
    (Finset.mem_toList.mpr hb) hne ca cb
  have eq : ((S.toList.map Live1024.observe).map (Live1024.restrictRows rows)) =
      S.toList.map (projected rows) := by simp [List.map_map, projected, Function.comp_def]
  rw [eq] at bound
  omega

end PEqualNP.Outside.L_meta_2373.LiftSeventeen

namespace PEqualNP.Outside.L_meta_2373.Live1024.OneNotFirstAnd

open PEqualNP.Outside.L_meta_2373
open LiftSeventeen

def andColumn (a b : Fin 10) : Sig := bin 0 (input a) (input b)
def bank (a b : Fin 10) : Finset Sig :=
  insert (andColumn a b) (insert (neg (andColumn a b)) inputs.toFinset)

lemma neg_bit (r : Row) (a : Sig) : bit r (neg a) = !(bit r a) := by
  simp [bit, neg, r.isLt]

lemma retained_left (a b : Fin 10) (ab : a ≠ b) {S : Finset Sig} {k : Nat}
    (sub : S ⊆ bank a b) (run : Live false graph k S) : input a ∈ S := by
  by_contra missing
  obtain ⟨r, s, oldSame, newSame, different⟩ :=
    no_binary_identification_left_rows 0 (by decide) a b ab
  obtain ⟨w, hw, diff⟩ := live_row_difference run different
  have mem := sub hw
  rcases Finset.mem_insert.mp mem with rfl | mem
  · exact diff newSame
  rcases Finset.mem_insert.mp mem with rfl | mem
  · apply diff
    rw [neg_bit, neg_bit]
    exact congrArg Bool.not newSame
  · obtain ⟨i, rfl⟩ := input_index w (List.mem_toFinset.mp mem)
    exact diff (oldSame i (by rintro rfl; exact missing hw))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma input_distinct : ∀ a b : Fin 10, a ≠ b →
    input a ≠ andColumn a b ∧ input a ≠ neg (andColumn a b) := by
  decide +kernel

lemma and_zero (a b : Fin 10) : projected (rowMap a) (andColumn a b) = (fun _ => false) := by
  rw [andColumn, projected_bin]
  have fixed : projected (rowMap a) (input a) = (fun _ => false) := funext (rowMap_missing a)
  rw [fixed]
  rfl

lemma neg_and_one (a b : Fin 10) :
    projected (rowMap a) (neg (andColumn a b)) = (fun _ => true) := by
  funext r
  change bit (rowMap a r) (neg (andColumn a b)) = true
  rw [neg_bit]
  have zero := congrFun (and_zero a b) r
  change bit (rowMap a r) (andColumn a b) = false at zero
  rw [zero]
  rfl

lemma bank_covered (a b : Fin 10) (w : Sig) (mem : w ∈ bank a b) :
    Available false (NineSigned.inputs.map NineSigned.observe) (projected (rowMap a) w) := by
  rcases Finset.mem_insert.mp mem with rfl | mem
  · rw [and_zero]
    exact Or.inr (Or.inl ⟨false, rfl⟩)
  rcases Finset.mem_insert.mp mem with rfl | mem
  · rw [neg_and_one]
    exact Or.inr (Or.inl ⟨true, rfl⟩)
  · obtain ⟨i, rfl⟩ := input_index w (List.mem_toFinset.mp mem)
    exact ZeroProfiles.rows_available a i

lemma positive_tail_lower (a b : Fin 10) (ab : a ≠ b) {S : Finset Sig} {k : Nat}
    (sub : S ⊆ bank a b)
    (used : andColumn a b ∈ S ∨ neg (andColumn a b) ∈ S)
    (run : Live false graph k S) : 18 ≤ k := by
  have ha := retained_left a b ab sub run
  have ca : Constant (projected (rowMap a) (input a)) := ⟨false, funext (rowMap_missing a)⟩
  apply projected_mono_lower_two (rowMap a) (funext (rowMap_graph a)) S k run
    (fun w hw => bank_covered a b w (sub hw))
  rcases used with used | used
  · exact ⟨input a, ha, andColumn a b, used, (input_distinct a b ab).1,
      ca, ⟨false, and_zero a b⟩⟩
  · exact ⟨input a, ha, neg (andColumn a b), used, (input_distinct a b ab).2,
      ca, ⟨true, neg_and_one a b⟩⟩

lemma prefix_exclusion (a b : Fin 10) (ab : a ≠ b) {S : Finset Sig} {k : Nat}
    (sub : S ⊆ bank a b)
    (used : andColumn a b ∈ S ∨ neg (andColumn a b) ∈ S)
    (budget : k + 2 ≤ 19) : ¬ Live false graph k S := by
  intro run
  have lower := positive_tail_lower a b ab sub used run
  omega

end PEqualNP.Outside.L_meta_2373.Live1024.OneNotFirstAnd
