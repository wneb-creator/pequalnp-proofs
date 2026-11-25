import CountVectorTransport

namespace PEqualNP.Outside.L_meta_2373.CountVector

open Live1024

variable {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

lemma count_tag_inl (tag : α → β) (A : Finset α) (j : Sum β Bool) :
    count (fun r => Sum.inl (tag r) : α → Sum β Bool) A j =
      Sum.elim (count tag A) (fun _ => 0) j := by
  cases j <;> simp [count]

lemma compress_cut_transport (left : α → β) (right : γ → β) (signal : β → Sig)
    (rootsA A : Finset α) (rootsB B : Finset γ) (subA : A ⊆ rootsA) (subB : B ⊆ rootsB)
    (bases : ∀ j, count left rootsA j = count right rootsB j)
    (removed : ∀ j, count left A j = count right B j)
    (v : Sig) (u : Bool) (T : Sig) (depth : Nat)
    (blocked : BudgetRunCut (compressRoots rootsA A)
      (duplicateRaw (fun r => signal (left r)) v) u T depth) :
    BudgetRunCut (compressRoots rootsB B) (duplicateRaw (fun r => signal (right r)) v) u T depth := by
  let ltag : α → Sum β Bool := fun r => Sum.inl (left r)
  let rtag : γ → Sum β Bool := fun r => Sum.inl (right r)
  let lnew := Sum.elim ltag (fun _ : Bool => Sum.inr false)
  let rnew := Sum.elim rtag (fun _ : Bool => Sum.inr false)
  let values := Sum.elim signal (fun _ : Bool => v)
  have same : ∀ j, count lnew (compressRoots rootsA A) j =
      count rnew (compressRoots rootsB B) j := by
    intro j
    rw [count_compress ltag rootsA A subA, count_compress rtag rootsB B subB]
    simp only [ltag, rtag, count_tag_inl]
    cases j with
    | inl j => simp [bases j, removed j]
    | inr b => rfl
  have leq : duplicateRaw (fun r => signal (left r)) v =
      (fun r => values (lnew r)) := by funext r; cases r <;> rfl
  have req : duplicateRaw (fun r => signal (right r)) v =
      (fun r => values (rnew r)) := by funext r; cases r <;> rfl
  rw [leq] at blocked
  rw [req]
  exact budgetRunCut_transport lnew rnew values _ _ same u T depth blocked

lemma duplicate_cut_transport (left : α → β) (right : γ → β) (signal : β → Sig)
    (rootsA A : Finset α) (rootsB B : Finset γ) (subA : A ⊆ rootsA) (subB : B ⊆ rootsB)
    (bases : ∀ j, count left rootsA j = count right rootsB j)
    (removed : ∀ j, count left A j = count right B j)
    (v : Sig) (u : Bool) (T : Sig) (depth : Nat)
    (blocked : BudgetRunCut (duplicateRoots rootsA A)
      (duplicateRaw (fun r => signal (left r)) v) u T depth) :
    BudgetRunCut (duplicateRoots rootsB B) (duplicateRaw (fun r => signal (right r)) v) u T depth := by
  let ltag : α → Sum β Bool := fun r => Sum.inl (left r)
  let rtag : γ → Sum β Bool := fun r => Sum.inl (right r)
  let lnew := Sum.elim ltag (fun _ : Bool => Sum.inr false)
  let rnew := Sum.elim rtag (fun _ : Bool => Sum.inr false)
  let values := Sum.elim signal (fun _ : Bool => v)
  have same : ∀ j, count lnew (duplicateRoots rootsA A) j =
      count rnew (duplicateRoots rootsB B) j := by
    intro j
    rw [count_duplicate ltag rootsA A subA, count_duplicate rtag rootsB B subB]
    simp only [ltag, rtag, count_tag_inl]
    cases j with
    | inl j => simp [bases j, removed j]
    | inr b => rfl
  have leq : duplicateRaw (fun r => signal (left r)) v =
      (fun r => values (lnew r)) := by funext r; cases r <;> rfl
  have req : duplicateRaw (fun r => signal (right r)) v =
      (fun r => values (rnew r)) := by funext r; cases r <;> rfl
  rw [leq] at blocked
  rw [req]
  exact budgetRunCut_transport lnew rnew values _ _ same u T depth blocked

end PEqualNP.Outside.L_meta_2373.CountVector
