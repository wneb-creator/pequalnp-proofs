import CountDagCheck

namespace PEqualNP.Outside.L_meta_2373.CountVector
open Live1024

theorem dag_replay_on {α β Ω : Type} [DecidableEq α] [DecidableEq β] [Fintype β]
    (roots eligible : Finset α) (raw : α → Sig) (tag : α → β) (signal : β → Sig)
    (agrees : ∀ r ∈ eligible, raw r = signal (tag r))
    (col : Sig → Set Ω) (need : Set Ω) (Cert : Finset α → Sig → Prop)
    (u : Bool) (T : Sig) (depth : Nat)
    (initial : ∀ r ∈ roots, Cert {r} (raw r))
    (closed : PrunedGateClosed roots raw col need Cert u T depth)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (valid : Nat → Prop) (counts : Nat → β → Nat) (values : Nat → Sig)
    (steps : ∀ i, valid i →
      (∃ c, counts i = (fun j => if c = j then 1 else 0) ∧ values i = signal c) ∨
      ∃ l r d, l < i ∧ r < i ∧ valid l ∧ valid r ∧
        counts i = (fun j => counts l j + counts r j) ∧
        values i = bin d (values l) (values r) ∧ allowed u d ∧
        values l ≠ values r ∧ bin d (values l) (values r) ≠ values l ∧
        bin d (values l) (values r) ≠ values r ∧ proper (bin d (values l) (values r)))
    (i : Nat) (A : Finset α) (vi : valid i) (same : count tag A = counts i)
    (sub : A ⊆ roots) (inside : A ⊆ eligible) :
    ReadOnce raw u A (values i) ∧ ColumnSupport raw col A (values i) ∧
      ProvenanceBridge roots raw col need Cert u T depth A (values i) := by
  let P : Nat → Finset α → Sig → Prop :=
    fun n B v => valid n ∧ B ⊆ eligible ∧ count tag B = counts n ∧ v = values n
  apply provenance_replay roots raw col need Cert u T depth initial closed gateCol
    P ?_ i A (values i) ⟨vi, inside, same, rfl⟩ sub
  intro n B v entry
  obtain ⟨vn, insideB, sameB, valueB⟩ := entry
  rcases steps n vn with leaf | binary
  · obtain ⟨c, unit, value⟩ := leaf
    have units : ∀ j, count tag B j = if c = j then 1 else 0 :=
      fun j => congrFun (sameB.trans unit) j
    obtain ⟨r, support, tagged⟩ := unit_support tag B c units
    have hr : r ∈ eligible := insideB (by rw [support]; exact Finset.mem_singleton_self r)
    left
    refine ⟨r, support, ?_⟩
    rw [valueB, value, agrees r hr, tagged]
  · obtain ⟨l, r, d, llt, rlt, vl, vr, sum, value, legal,
      distinct, freshLeft, freshRight, properOut⟩ := binary
    have sums : ∀ j, count tag B j = counts l j + counts r j :=
      fun j => congrFun (sameB.trans sum) j
    obtain ⟨L, R, disjoint, union, leftCounts, rightCounts⟩ :=
      count_split tag B (counts l) (counts r) sums
    have insideL : L ⊆ eligible := by
      intro x hx
      apply insideB
      rw [← union]
      exact Finset.mem_union_left R hx
    have insideR : R ⊆ eligible := by
      intro x hx
      apply insideB
      rw [← union]
      exact Finset.mem_union_right L hx
    right
    refine ⟨l, r, L, R, values l, values r, d, llt, rlt,
      ⟨vl, insideL, funext leftCounts, rfl⟩, ⟨vr, insideR, funext rightCounts, rfl⟩,
      union.symm, valueB.trans value, disjoint, legal, distinct, freshLeft, freshRight, properOut⟩

theorem dagCheck_replay_on {α Ω : Type} [DecidableEq α] {m : Nat}
    (roots eligible : Finset α) (raw : α → Sig) (tag : α → Fin m) (signal : Fin m → Sig)
    (agrees : ∀ r ∈ eligible, raw r = signal (tag r))
    (col : Sig → Set Ω) (need : Set Ω) (Cert : Finset α → Sig → Prop)
    (u : Bool) (T : Sig) (depth : Nat)
    (initial : ∀ r ∈ roots, Cert {r} (raw r))
    (closed : PrunedGateClosed roots raw col need Cert u T depth)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (entries : List (DagEntry m)) (sources : List (Sum (Fin m) (Nat × Nat × Nat)))
    (checked : dagCheck u signal entries sources = true)
    (i : Nat) (hi : i < entries.length) (A : Finset α)
    (same : count tag A = (dagEntry entries i).1) (sub : A ⊆ roots) (inside : A ⊆ eligible) :
    ReadOnce raw u A (dagEntry entries i).2 ∧ ColumnSupport raw col A (dagEntry entries i).2 ∧
      ProvenanceBridge roots raw col need Cert u T depth A (dagEntry entries i).2 :=
  dag_replay_on roots eligible raw tag signal agrees col need Cert u T depth initial closed gateCol
    (fun i => i < entries.length) (fun i => (dagEntry entries i).1)
    (fun i => (dagEntry entries i).2) (dagCheck_steps checked) i A hi same sub inside

end PEqualNP.Outside.L_meta_2373.CountVector
