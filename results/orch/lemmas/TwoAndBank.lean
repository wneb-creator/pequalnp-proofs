import PetersenEighteenExtension
import FreeBankExtraction

namespace PEqualNP.Outside.L_meta_2373.Live1024.TwoAndBank
open LiftSeventeen

def andCol (a b : Fin 10) : Sig := bin 0 (input a) (input b)
def bank (a b c d : Fin 10) : Finset Sig :=
  insert (andCol a b) (insert (neg (andCol a b))
    (insert (andCol c d) (insert (neg (andCol c d)) inputs.toFinset)))

lemma neg_bit (r : Row) (v : Sig) : bit r (neg v) = !(bit r v) := by
  simp [bit, neg, r.isLt]

lemma projected_neg (rows : NineSigned.Row → Row) (v : Sig) :
    projected rows (neg v) = inv (projected rows v) := by
  funext r
  exact neg_bit (rows r) v

lemma and_zero (a b : Fin 10) : projected (rowMap a) (andCol a b) = (fun _ => false) := by
  rw [andCol, projected_bin]
  have fixed : projected (rowMap a) (input a) = (fun _ => false) := funext (rowMap_missing a)
  rw [fixed]
  rfl

lemma neg_and_one (a b : Fin 10) :
    projected (rowMap a) (neg (andCol a b)) = (fun _ => true) := by
  rw [projected_neg, and_zero]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma input_distinct : ∀ a b : Fin 10, a ≠ b →
    input a ≠ andCol a b ∧ input a ≠ neg (andCol a b) := by
  decide +kernel

lemma live_up {target : Sig} {k : Nat} {S : Finset Sig} (run : Live false target k S) :
    Live true target k S := by
  induction run using Live.ind with
  | stop hp => exact Live.stop hp
  | @binary k U a b d hd ha hb hab hf trace ih =>
    have hu : allowed true d := by
      rcases hd with h | ⟨bad, _⟩
      · exact Or.inl h
      · cases bad
    exact Live.binary hu ha hb hab hf ih

def paidBank (a c d : Fin 10) : List (Wire NineSigned.Row) :=
  combine false (projected (rowMap a) (input c)) (projected (rowMap a) (input d)) ::
    NineSigned.inputs.map NineSigned.observe

lemma paid_reach (a c d : Fin 10) :
    Reach true (NineSigned.inputs.map NineSigned.observe) 1 (paidBank a c d) :=
  Reach.two false Reach.start
    (rowMap_available_of rowMap_missing rowMap_input a c)
    (rowMap_available_of rowMap_missing rowMap_input a d)

lemma bank_covered (a b c d : Fin 10) (w : Sig) (mem : w ∈ bank a b c d) :
    Available true (paidBank a c d) (projected (rowMap a) w) := by
  rcases Finset.mem_insert.mp mem with rfl | mem
  · rw [and_zero]
    exact Or.inr (Or.inl ⟨false, rfl⟩)
  rcases Finset.mem_insert.mp mem with rfl | mem
  · rw [neg_and_one]
    exact Or.inr (Or.inl ⟨true, rfl⟩)
  rcases Finset.mem_insert.mp mem with rfl | mem
  · rw [andCol, projected_bin]
    exact Or.inl List.mem_cons_self
  rcases Finset.mem_insert.mp mem with rfl | mem
  · rw [projected_neg, andCol, projected_bin]
    exact avail_inv rfl (Or.inl List.mem_cons_self)
  · obtain ⟨i, rfl⟩ := input_index w (List.mem_toFinset.mp mem)
    exact available_cons _ (rowMap_available_of rowMap_missing rowMap_input a i)

lemma paid_tail_lower (a b c d : Fin 10) {S : Finset Sig} {k : Nat}
    (sub : S ⊆ bank a b c d) (run : Live false graph k S)
    (constants : ∃ v ∈ S, ∃ w ∈ S, v ≠ w ∧
      Constant (projected (rowMap a) v) ∧ Constant (projected (rowMap a) w)) : 16 ≤ k := by
  have trace := list_run (live_up run) S.toList (Finset.nodup_toList S) (by simp)
  have nc : ¬Constant (restrictRows (rowMap a) (observe graph)) := by
    change ¬Constant (projected (rowMap a) graph)
    rw [show projected (rowMap a) graph = NineSigned.observe NineSigned.graph from funext (rowMap_graph a)]
    exact NineSigned.observe_proper NineSigned.graph_proper
  have supply : Live1024.supply true (paidBank a c d)
      ((S.toList.map observe).map (restrictRows (rowMap a))) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
    exact bank_covered a b c d w (sub (Finset.mem_toList.mp hw))
  have prior (q : Nat) (bs : List (Wire NineSigned.Row))
      (hr : Reach true (NineSigned.inputs.map NineSigned.observe) q bs)
      (hv : Available true bs (restrictRows (rowMap a) (observe graph))) : 15 ≤ q := by
    change Available true bs (projected (rowMap a) graph) at hv
    rw [show projected (rowMap a) graph = NineSigned.observe NineSigned.graph from funext (rowMap_graph a)] at hv
    exact NineSigned.nine_reach_lower q bs (reach_bridge hr) hv
  have bound := projected_bound (rowMap a) trace nc (paid_reach a c d) supply prior
  obtain ⟨v, hv, w, hw, ne, cv, cw⟩ := constants
  have mass := mass_two (projected (rowMap a)) (Finset.mem_toList.mpr hv)
    (Finset.mem_toList.mpr hw) ne cv cw
  have eq : ((S.toList.map observe).map (restrictRows (rowMap a))) =
      S.toList.map (projected (rowMap a)) := by simp [List.map_map, projected, Function.comp_def]
  rw [eq] at bound
  omega

end PEqualNP.Outside.L_meta_2373.Live1024.TwoAndBank
