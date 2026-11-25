import Expansion126663Compact
import SliceProfiles

namespace PEqualNP.Outside.L_meta_2373.Live1024.Expansion126663

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
lemma profile_matches : ∀ i : Fin 14,
    domain i.val = SliceProfiles.domains.getD i.val zero ∧
    lower i.val = SliceProfiles.bounds.getD i.val 0 := by
  decide +kernel

theorem completed_subtree : Impossible true graph 12 rawState.toFinset := by
  apply closed_of_slices
  intro i
  rw [(profile_matches i).1, (profile_matches i).2]
  exact SliceProfiles.all_slices i

def foldedFour : Sig :=
  bin 3 (inputs.getD 4 zero)
    (bin 1 (bin 1 (inputs.getD 2 zero) (inputs.getD 3 zero))
      (bin 1 (inputs.getD 9 zero) (bin 1 (inputs.getD 0 zero) (inputs.getD 1 zero))))

def frontier : List Sig :=
  [inputs.getD 0 zero, inputs.getD 1 zero, inputs.getD 2 zero, inputs.getD 3 zero,
   inputs.getD 5 zero, inputs.getD 6 zero, inputs.getD 7 zero, inputs.getD 8 zero,
   inputs.getD 9 zero, foldedFour]

lemma rawState_eq_frontier : rawState = frontier := by decide +kernel

theorem frontier_impossible : Impossible true graph 12 frontier.toFinset :=
  rawState_eq_frontier ▸ completed_subtree

def essentialRows : Fin 10 → Row × Row :=
  ![(3, 2), (3, 1), (6, 2), (12, 4), (33, 1), (66, 2), (132, 4), (264, 8), (528, 0), (17, 1)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
lemma frontier_required :
    (∀ i : Fin 10, bit (essentialRows i).1 graph ≠ bit (essentialRows i).2 graph) ∧
    ∀ i j : Fin 10, i ≠ j →
      bit (essentialRows i).1 (frontier.getD j.val zero) =
        bit (essentialRows i).2 (frontier.getD j.val zero) := by
  decide +kernel

lemma frontier_index (a : Sig) (ha : a ∈ frontier) :
    ∃ i : Fin 10, frontier.getD i.val zero = a := by
  obtain ⟨i, hi, hv⟩ := List.mem_iff_getElem.mp ha
  have hi10 : i < 10 := by simpa only [frontier, List.length_cons, List.length_nil] using hi
  refine ⟨⟨i, hi10⟩, ?_⟩
  have he : frontier[i]? = some a := List.getElem?_eq_some_iff.mpr ⟨hi, hv⟩
  change frontier.getD i zero = a
  rw [List.getD_eq_getElem?_getD, he]
  rfl

theorem frontier_lower_thirteen : Lower true frontier graph 13 := by
  apply lower_impossible graph_proper (by decide +kernel) (by decide +kernel) ?_ frontier_impossible
  intro a ha
  obtain ⟨i, rfl⟩ := frontier_index a ha
  refine ⟨(essentialRows i).1, (essentialRows i).2, frontier_required.1 i, ?_⟩
  intro v hv hn
  obtain ⟨j, rfl⟩ := frontier_index v hv
  exact frontier_required.2 i j (fun hij =>
    hn (congrArg (fun t : Fin 10 => frontier.getD t.val zero) hij.symm))

end PEqualNP.Outside.L_meta_2373.Live1024.Expansion126663
