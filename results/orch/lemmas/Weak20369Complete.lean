import Weak20369Budgets
import CountNodeBuild
import CountNodeMemo
import CountVectorCutTransport
import PairColumnSemantics

namespace PEqualNP.Outside.L_meta_2373.Weak20369
open Live1024 CountVector

lemma cutsSound9611 {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin 11)
    (same : count tag roots = total9611) (A : Finset α) (v : Sig) (sub : A ⊆ roots)
    (member : (count tag A, v) ∈ cuts9611) :
    BudgetRunCut (compressRoots roots A)
      (duplicateRaw (fun r => signal9611 (tag r)) v) false graph 1 := by
  rw [gate_table] at member
  obtain ⟨i, eq⟩ := List.mem_ofFn.mp member
  obtain ⟨counts, value⟩ := Prod.mk.inj eq
  rw [← value]
  exact compress_cut_transport tag9611 tag signal9611 Finset.univ (gateSupport i) roots A
    (by simp) sub (fun j => congrFun (counts9611.trans same.symm) j)
    (fun j => congrFun ((gateSupport_counts i).trans counts) j) _ false graph 1 (gateBudget i)

lemma copiesCut9611 {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin 11)
    (same : count tag roots = total9611) (A : Finset α) (v : Sig) (sub : A ⊆ roots)
    (member : (count tag A, v) ∈ entries9611) :
    BudgetRunCut (duplicateRoots roots A)
      (duplicateRaw (fun r => signal9611 (tag r)) v) false graph 0 := by
  rw [entry_table9611] at member
  obtain ⟨i, eq⟩ := List.mem_ofFn.mp member
  obtain ⟨counts, value⟩ := Prod.mk.inj eq
  rw [← value]
  exact duplicate_cut_transport tag9611 tag signal9611 Finset.univ (support9611 i) roots A
    (by simp) sub (fun j => congrFun (counts9611.trans same.symm) j)
    (fun j => congrFun ((support_counts9611 i).trans counts) j) _ false graph 0
    (childBudget9611 i)

lemma node9611 : CountNode total9611 signal9611 (pairColumn false) (pairColumn false graph)
    false graph 1 (fun c v => (c, v) ∈ entries9611) := by
  apply countNode_succ total9611 signal9611 (pairColumn false) (pairColumn false graph)
    false graph 0 (fun c v => (c, v) ∈ entries9611) (fun c v => (c, v) ∈ cuts9611)
    (countLeafCheck_sound checked_leaves9611) (countGateCheck_sound checked_gates9611)
    missing9611
  · exact cutsSound9611
  · intro α inst roots tag same A v sub _ member
    exact Or.inl (copiesCut9611 roots tag same A v sub member)

def memoTable (c : Fin 11 → Nat) (v : Sig) : Prop :=
  (regroup Memo20376.classMap c, rename Memo20376.rows v) ∈ entries9611

lemma memoNode20376 : CountNode Memo20376.sourceTotal signal20369
    (pairColumn false) (pairColumn false graph) false graph 1 memoTable := by
  rw [signal20369_memo]
  apply countNode_rename_regroup Memo20376.rows Memo20376.rows_onto false graph
    Memo20376.target_fixed 1 Memo20376.sourceTotal Memo20376.sourceSignal
    Memo20376.classMap Memo20376.priorTotal Memo20376.priorSignal
    (fun c v => (c, v) ∈ entries9611) Memo20376.totals
    (fun j _ => Memo20376.signals j)
  intro α inst roots tag same
  have same' : count tag roots = total9611 := by
    simpa only [total9611_memo] using same
  simpa only [signal9611_memo] using (node9611 roots tag same')

lemma copiesCut20369 {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin 11)
    (same : count tag roots = total20369) (A : Finset α) (sub : A ⊆ roots)
    (i : Fin 11) (notMemo : i ≠ 6) (selected : count tag A = entryVector20369 i) :
    BudgetRunCut (duplicateRoots roots A)
      (duplicateRaw (fun r => signal20369 (tag r)) (entryValue20369 i)) false graph 1 := by
  exact duplicate_cut_transport tag20369 tag signal20369 Finset.univ (support20369 i) roots A
    (by simp) sub (fun j => congrFun (counts20369.trans same.symm) j)
    (fun j => congrFun ((support_counts20369 i).trans selected.symm) j) _ false graph 1
    (childBudget20369 i notMemo)

lemma memoBridge20376 {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin 11)
    (same : count tag roots = total20369) (A : Finset α) (sub : A ⊆ roots)
    (selected : count tag A = entryVector20369 6) :
    ∃ Cert2 : Finset (Sum α Bool) → Sig → Prop,
      PrunedBridge roots (fun r => signal20369 (tag r)) (pairColumn false) (pairColumn false graph)
        (countCert roots tag (fun c v => (c, v) ∈ entries20369)) Cert2 false graph 1 A
          (entryValue20369 6) ∧
      PrunedNode (pairColumn false) (pairColumn false graph) false graph 1 (Sum α Bool)
        (duplicateRoots roots A) (duplicateRaw (fun r => signal20369 (tag r)) (entryValue20369 6)) Cert2 := by
  apply copied_count_node_bridge roots tag total20369 signal20369 same A sub
    (entryVector20369 6) selected (entryValue20369 6) id 6 Memo20376.sourceTotal
    signal20369 memoTable (by decide +kernel) (by intro j hj; rfl) (by decide +kernel)
    (pairColumn false) (pairColumn false graph) false graph 1 memoNode20376
    entries20369 sources20369 checked_provenance20369 0
  exact pairColumn_gate false

lemma node20369 : CountNode total20369 signal20369 (pairColumn false) (pairColumn false graph)
    false graph 2 (fun c v => (c, v) ∈ entries20369) := by
  apply countNode_succ total20369 signal20369 (pairColumn false) (pairColumn false graph)
    false graph 1 (fun c v => (c, v) ∈ entries20369) (fun c v => (c, v) ∈ cuts20369)
    (countLeafCheck_sound checked_leaves20369) (countGateCheck_sound checked_gates20369)
    missing20369
  · intro α inst roots tag same A v sub member
    simp [cuts20369] at member
  · intro α inst roots tag same A v sub proper member
    rw [entry_table20369] at member
    obtain ⟨i, eq⟩ := List.mem_ofFn.mp member
    obtain ⟨counts, value⟩ := Prod.mk.inj eq
    rw [← value]
    by_cases memo : i = 6
    · subst i
      exact Or.inr (memoBridge20376 roots tag same A sub counts.symm)
    · exact Or.inl (copiesCut20369 roots tag same A sub i memo counts.symm)

end PEqualNP.Outside.L_meta_2373.Weak20369
