import CountDagReplay

namespace PEqualNP.Outside.L_meta_2373.CountVector
open Live1024

abbrev DagEntry (m : Nat) := (Fin m → Nat) × Sig

def dagEntry {m : Nat} (entries : List (DagEntry m)) (i : Nat) : DagEntry m :=
  entries.getD i ((fun _ => 0), zero)

def dagCheck {m : Nat} (u : Bool) (signal : Fin m → Sig) (entries : List (DagEntry m))
    (sources : List (Sum (Fin m) (Nat × Nat × Nat))) : Bool :=
  (List.range entries.length).all fun i =>
    let e := dagEntry entries i
    match sources.getD i (.inr (0, 0, 0)) with
    | .inl c => decide (e.1 = (fun j => if c = j then 1 else 0) ∧ e.2 = signal c)
    | .inr (l, r, d) =>
      let left := dagEntry entries l
      let right := dagEntry entries r
      let z := bin d left.2 right.2
      decide (l < i ∧ r < i ∧ e.1 = (fun j => left.1 j + right.1 j) ∧ e.2 = z ∧
        (d < 2 ∨ (u = true ∧ d < 4)) ∧ left.2 ≠ right.2 ∧
        z ≠ left.2 ∧ z ≠ right.2 ∧ z ≠ zero ∧ z ≠ one)

theorem dagCheck_steps {m : Nat} {u : Bool} {signal : Fin m → Sig}
    {entries : List (DagEntry m)} {sources : List (Sum (Fin m) (Nat × Nat × Nat))}
    (checked : dagCheck u signal entries sources = true) :
    ∀ i, i < entries.length →
      (∃ c, (dagEntry entries i).1 = (fun j => if c = j then 1 else 0) ∧
        (dagEntry entries i).2 = signal c) ∨
      ∃ l r d, l < i ∧ r < i ∧ l < entries.length ∧ r < entries.length ∧
        (dagEntry entries i).1 = (fun j => (dagEntry entries l).1 j + (dagEntry entries r).1 j) ∧
        (dagEntry entries i).2 = bin d (dagEntry entries l).2 (dagEntry entries r).2 ∧
        allowed u d ∧ (dagEntry entries l).2 ≠ (dagEntry entries r).2 ∧
        bin d (dagEntry entries l).2 (dagEntry entries r).2 ≠ (dagEntry entries l).2 ∧
        bin d (dagEntry entries l).2 (dagEntry entries r).2 ≠ (dagEntry entries r).2 ∧
        proper (bin d (dagEntry entries l).2 (dagEntry entries r).2) := by
  intro i hi
  have test := List.all_eq_true.mp checked i (List.mem_range.mpr hi)
  cases hs : sources.getD i (.inr (0, 0, 0)) with
  | inl c =>
    simp only [hs, decide_eq_true_eq] at test
    exact Or.inl ⟨c, test⟩
  | inr refs =>
    obtain ⟨l, r, d⟩ := refs
    simp only [hs, decide_eq_true_eq] at test
    obtain ⟨lt, rt, counts, value, legal, distinct, freshLeft, freshRight, nz, no⟩ := test
    exact Or.inr ⟨l, r, d, lt, rt, by omega, by omega, counts, value,
      legal, distinct, freshLeft, freshRight, nz, no⟩

theorem dagCheck_replay {α Ω : Type} [DecidableEq α] {m : Nat}
    (roots : Finset α) (tag : α → Fin m) (signal : Fin m → Sig)
    (col : Sig → Set Ω) (need : Set Ω) (Cert : Finset α → Sig → Prop)
    (u : Bool) (T : Sig) (depth : Nat)
    (initial : ∀ r ∈ roots, Cert {r} (signal (tag r)))
    (closed : PrunedGateClosed roots (fun r => signal (tag r)) col need Cert u T depth)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (entries : List (DagEntry m)) (sources : List (Sum (Fin m) (Nat × Nat × Nat)))
    (checked : dagCheck u signal entries sources = true)
    (i : Nat) (hi : i < entries.length) (A : Finset α)
    (same : count tag A = (dagEntry entries i).1) (sub : A ⊆ roots) :
    ReadOnce (fun r => signal (tag r)) u A (dagEntry entries i).2 ∧
      ColumnSupport (fun r => signal (tag r)) col A (dagEntry entries i).2 ∧
      ProvenanceBridge roots (fun r => signal (tag r)) col need Cert u T depth
        A (dagEntry entries i).2 :=
  dag_replay roots tag signal col need Cert u T depth initial closed gateCol
    (fun i => i < entries.length) (fun i => (dagEntry entries i).1)
    (fun i => (dagEntry entries i).2) (dagCheck_steps checked) i A hi same sub

end PEqualNP.Outside.L_meta_2373.CountVector
