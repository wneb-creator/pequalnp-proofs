import Weak80905Budgets
import CountNodeBuild
import CountVectorCutTransport
import PairColumnSemantics

namespace PEqualNP.Outside.L_meta_2373.Weak80905
open Live1024 CountVector

lemma cutsSound76616 {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin 11)
    (same : count tag roots = total76616) (A : Finset α) (v : Sig) (sub : A ⊆ roots)
    (member : (count tag A, v) ∈ cuts76616) :
    BudgetRunCut (compressRoots roots A)
      (duplicateRaw (fun r => signal (tag r)) v) false graph 2 := by
  rw [gate_table] at member
  obtain ⟨i, eq⟩ := List.mem_ofFn.mp member
  obtain ⟨counts, value⟩ := Prod.mk.inj eq
  rw [← value]
  exact compress_cut_transport tag76616 tag signal Finset.univ gateSupport roots A
    (by simp) sub (fun j => congrFun (counts76616.trans same.symm) j)
    (fun j => congrFun (gateSupport_counts.trans counts) j) _ false graph 2 (gateBudget i)

lemma copiesCut76616 {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin 11)
    (same : count tag roots = total76616) (A : Finset α) (v : Sig) (sub : A ⊆ roots)
    (member : (count tag A, v) ∈ entries) :
    BudgetRunCut (duplicateRoots roots A)
      (duplicateRaw (fun r => signal (tag r)) v) false graph 1 := by
  rw [entries] at member
  obtain ⟨i, eq⟩ := List.mem_ofFn.mp member
  obtain ⟨counts, value⟩ := Prod.mk.inj eq
  rw [← value]
  exact duplicate_cut_transport tag76616 tag signal Finset.univ (support76616 i) roots A
    (by simp) sub (fun j => congrFun (counts76616.trans same.symm) j)
    (fun j => congrFun ((support_counts76616 i).trans counts) j) _ false graph 1
    (childBudget76616 i)

lemma node76616 : CountNode total76616 signal (pairColumn false) (pairColumn false graph)
    false graph 2 (fun c v => (c, v) ∈ entries) := by
  apply countNode_succ total76616 signal (pairColumn false) (pairColumn false graph)
    false graph 1 (fun c v => (c, v) ∈ entries) (fun c v => (c, v) ∈ cuts76616)
    (countLeafCheck_sound checked_leaves76616) (countGateCheck_sound checked_gates76616)
    missing76616
  · exact cutsSound76616
  · intro α inst roots tag same A v sub _ member
    exact Or.inl (copiesCut76616 roots tag same A v sub member)

lemma copiesCut80905 {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin 11)
    (same : count tag roots = total80905) (A : Finset α) (sub : A ⊆ roots)
    (i : Fin 11) (notMemo : i ≠ 7) (selected : count tag A = unit i) :
    BudgetRunCut (duplicateRoots roots A)
      (duplicateRaw (fun r => signal (tag r)) (signal i)) false graph 2 := by
  exact duplicate_cut_transport tag80905 tag signal Finset.univ (support80905 i) roots A
    (by simp) sub (fun j => congrFun (counts80905.trans same.symm) j)
    (fun j => congrFun ((support_counts80905 i).trans selected.symm) j) _ false graph 2
    (childBudget80905 i notMemo)

lemma memo80913 {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin 11)
    (same : count tag roots = total80905) (A : Finset α) (sub : A ⊆ roots)
    (selected : count tag A = unit 7) :
    ∃ Cert2 : Finset (Sum α Bool) → Sig → Prop,
      PrunedBridge roots (fun r => signal (tag r)) (pairColumn false) (pairColumn false graph)
        (countCert roots tag (fun c v => (c, v) ∈ entries)) Cert2 false graph 2 A (signal 7) ∧
      PrunedNode (pairColumn false) (pairColumn false graph) false graph 2 (Sum α Bool)
        (duplicateRoots roots A) (duplicateRaw (fun r => signal (tag r)) (signal 7)) Cert2 := by
  apply copied_count_node_bridge roots tag total80905 signal same A sub (unit 7) selected
    (signal 7) id 7 total76616 signal (fun c v => (c, v) ∈ entries)
    (by decide +kernel) (by intro j hj; rfl) rfl
    (pairColumn false) (pairColumn false graph) false graph 2 node76616
    entries sources checked_provenance 0
  exact pairColumn_gate false

lemma node80905 : CountNode total80905 signal (pairColumn false) (pairColumn false graph)
    false graph 3 (fun c v => (c, v) ∈ entries) := by
  apply countNode_succ total80905 signal (pairColumn false) (pairColumn false graph)
    false graph 2 (fun c v => (c, v) ∈ entries) (fun c v => (c, v) ∈ cuts80905)
    (countLeafCheck_sound checked_leaves80905) (countGateCheck_sound checked_gates80905)
    missing80905
  · intro α inst roots tag same A v sub member
    simp [cuts80905] at member
  · intro α inst roots tag same A v sub proper member
    rw [entries] at member
    obtain ⟨i, eq⟩ := List.mem_ofFn.mp member
    obtain ⟨counts, value⟩ := Prod.mk.inj eq
    rw [← value]
    by_cases memo : i = 7
    · subst i
      exact Or.inr (memo80913 roots tag same A sub counts.symm)
    · exact Or.inl (copiesCut80905 roots tag same A sub i memo counts.symm)

end PEqualNP.Outside.L_meta_2373.Weak80905
