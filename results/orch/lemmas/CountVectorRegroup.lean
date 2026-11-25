import CountVectorAdapters

namespace PEqualNP.Outside.L_meta_2373.CountVector
open Live1024

variable {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ] [Fintype β]

def regroup (map : β → γ) (v : β → Nat) (j : γ) : Nat :=
  ∑ i, if map i = j then v i else 0

lemma count_regroup (tag : α → β) (map : β → γ) (A : Finset α) :
    count (fun r => map (tag r)) A = regroup map (count tag A) := by
  funext k
  change (A.filter (fun r => map (tag r) = k)).card = _
  rw [← count_sum tag (A.filter (fun r => map (tag r) = k))]
  apply Finset.sum_congr rfl
  intro j hj
  have filtered : (A.filter (fun r => map (tag r) = k)).filter (fun r => tag r = j) =
      if map j = k then A.filter (fun r => tag r = j) else ∅ := by
    ext r
    by_cases eq : map j = k <;> by_cases tagEq : tag r = j <;> simp [eq, tagEq]
  simp only [count, filtered]
  by_cases eq : map j = k <;> simp [eq]

lemma count_duplicate_regroup (tag : α → β) (map : β → γ)
    (roots A : Finset α) (sub : A ⊆ roots) (w j : γ) :
    count (Sum.elim (fun r => map (tag r)) (fun _ : Bool => w)) (duplicateRoots roots A) j =
      regroup map (count tag roots) j - regroup map (count tag A) j +
        if w = j then 2 else 0 := by
  rw [count_duplicate _ roots A sub, count_regroup tag map roots, count_regroup tag map A]

lemma duplicateRaw_regroup (tag : α → β) (map : β → γ)
    (roots A : Finset α) (sub : A ⊆ roots)
    (signal : β → Sig) (next : γ → Sig) (w : γ) (v : Sig)
    (same : ∀ j, count tag A j < count tag roots j → next (map j) = signal j)
    (inserted : next w = v) :
    ∀ r ∈ duplicateRoots roots A,
      next (Sum.elim (fun r => map (tag r)) (fun _ : Bool => w) r) =
        duplicateRaw (fun r => signal (tag r)) v r := by
  intro r hr
  cases r with
  | inl a =>
    have mem : a ∈ roots ∧ a ∉ A := by simpa [duplicateRoots, liftLabels] using hr
    have residual := (outside_iff tag roots A sub (tag a)).mp ⟨a, mem.1, mem.2, rfl⟩
    exact same (tag a) residual
  | inr b => exact inserted

end PEqualNP.Outside.L_meta_2373.CountVector
