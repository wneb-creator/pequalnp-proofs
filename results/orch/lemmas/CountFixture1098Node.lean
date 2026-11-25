import CountFixture1098Children
import Node1098CutBudgets
import CountVectorCutTransport

namespace PEqualNP.Outside.L_meta_2373.CountFixture1098
open Live1024 CountVector

lemma cutSound {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin 12)
    (same : count tag roots = total) (A : Finset α) (v : Sig) (sub : A ⊆ roots)
    (member : (count tag A, v) ∈ cuts) :
    BudgetRunCut (compressRoots roots A)
      (duplicateRaw (fun r => signal (tag r)) v) false graph 1 := by
  rw [cut_table] at member
  obtain ⟨i, eq⟩ := List.mem_ofFn.mp member
  obtain ⟨counts, value⟩ := Prod.mk.inj eq
  rw [← value]
  exact compress_cut_transport basisTag tag signal Finset.univ (cutSupport i) roots A
    (by simp) sub (fun j => congrFun (basis_counts.trans same.symm) j)
    (fun j => congrFun ((cutSupport_counts i).trans counts) j) _ false graph 1 (cutBudget i)

lemma copiesSound {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin 12)
    (same : count tag roots = total) (A : Finset α) (v : Sig) (sub : A ⊆ roots)
    (member : (count tag A, v) ∈ entries) :
    BudgetRunCut (duplicateRoots roots A)
      (duplicateRaw (fun r => signal (tag r)) v) false graph 0 := by
  rw [entry_table] at member
  obtain ⟨i, eq⟩ := List.mem_ofFn.mp member
  obtain ⟨counts, value⟩ := Prod.mk.inj eq
  rw [← value]
  exact duplicate_cut_transport basisTag tag signal Finset.univ (entrySupport i) roots A
    (by simp) sub (fun j => congrFun (basis_counts.trans same.symm) j)
    (fun j => congrFun ((entrySupport_counts i).trans counts) j) _ false graph 0 (childBudget i)

lemma completedNode {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin 12)
    (same : count tag roots = total) :
    PrunedNode (pairColumn false) (pairColumn false graph) false graph 1 α roots
      (fun r => signal (tag r)) (countCert roots tag (fun c v => (c, v) ∈ entries)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    apply countCert_leaf roots tag signal (fun c v => (c, v) ∈ entries) r hr
    apply countLeafCheck_sound checked_leaves
    rw [← same]
    exact count_positive_of_mem tag roots r hr
  · apply prunedGateClosed_of_count roots tag signal (pairColumn false)
      (pairColumn false graph) (fun c v => (c, v) ∈ entries) (fun c v => (c, v) ∈ cuts)
      false graph 1
    · simpa only [same] using closed
    · exact cutSound roots tag same
  · intro member
    apply missing
    simpa only [same] using member.2
  · intro A v sub _ member
    exact Or.inl (copiesSound roots tag same A v sub member.2)

lemma canonicalNode : PrunedNode (pairColumn false) (pairColumn false graph) false graph 1
    (Fin 16) Finset.univ (fun r => signal (basisTag r))
    (countCert Finset.univ basisTag (fun c v => (c, v) ∈ entries)) :=
  completedNode Finset.univ basisTag basis_counts

end PEqualNP.Outside.L_meta_2373.CountFixture1098
