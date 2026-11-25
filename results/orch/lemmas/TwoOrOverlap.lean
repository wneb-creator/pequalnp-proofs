import TwoAndBank

namespace PEqualNP.Outside.L_meta_2373.Live1024.TwoOrOverlap
open PEqualNP.Outside.L_meta_2373 LiftSeventeen

def source (a b : Fin 10) : Sig := bin 1 (input a) (input b)
def bank (a b c : Fin 10) : Finset Sig :=
  insert (source a b) (insert (neg (source a b))
    (insert (source a c) (insert (neg (source a c)) inputs.toFinset)))

lemma source_projected (a b : Fin 10) :
    projected (rowMap a) (source a b) = projected (rowMap a) (input b) := by
  rw [source, projected_bin]
  have fixed : projected (rowMap a) (input a) = (fun _ => false) :=
    funext (rowMap_missing a)
  rw [fixed]
  rfl

lemma source_available (a b : Fin 10) :
    Available true (NineSigned.inputs.map NineSigned.observe)
      (projected (rowMap a) (source a b)) := by
  rw [source_projected]
  exact rowMap_available_of rowMap_missing rowMap_input a b

lemma neg_projected (rows : NineSigned.Row → Row) (h : Sig) :
    projected rows (neg h) = inv (projected rows h) := by
  unfold projected
  rw [obs_neg]
  rfl

lemma negative_available (a b : Fin 10) :
    Available true (NineSigned.inputs.map NineSigned.observe)
      (projected (rowMap a) (neg (source a b))) := by
  rw [neg_projected]
  exact avail_inv rfl (source_available a b)

lemma bank_covered (a b c : Fin 10) (w : Sig) (member : w ∈ bank a b c) :
    Available true (NineSigned.inputs.map NineSigned.observe) (projected (rowMap a) w) := by
  rcases Finset.mem_insert.mp member with rfl | member
  · exact source_available a b
  rcases Finset.mem_insert.mp member with rfl | member
  · exact negative_available a b
  rcases Finset.mem_insert.mp member with rfl | member
  · exact source_available a c
  rcases Finset.mem_insert.mp member with rfl | member
  · exact negative_available a c
  · obtain ⟨i, rfl⟩ := input_index w (List.mem_toFinset.mp member)
    exact rowMap_available_of rowMap_missing rowMap_input a i

lemma retained_overlap_lower (a b c : Fin 10) {S : Finset Sig} {k : Nat}
    (sub : S ⊆ bank a b c) (retained : input a ∈ S)
    (run : Live false graph k S) : 16 ≤ k := by
  apply projected_tail_lower (rowMap a) (funext (rowMap_graph a)) S k (TwoAndBank.live_up run)
  · exact fun w hw => bank_covered a b c w (sub hw)
  · exact ⟨input a, retained, false, funext (rowMap_missing a)⟩

lemma retained_overlap_excluded (a b c : Fin 10) {S : Finset Sig} {k : Nat}
    (sub : S ⊆ bank a b c) (retained : input a ∈ S) (small : k ≤ 15) :
    ¬ Live false graph k S := by
  intro run
  have lower := retained_overlap_lower a b c sub retained run
  omega

end PEqualNP.Outside.L_meta_2373.Live1024.TwoOrOverlap
