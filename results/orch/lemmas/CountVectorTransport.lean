import CountVectorAdapters

namespace PEqualNP.Outside.L_meta_2373.CountVector

open Live1024

variable {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

lemma list_count (tag : α → β) (A : Finset α) (j : β) :
    (A.toList.map tag).count j = count tag A j := by
  rw [List.count, List.countP_map, List.countP_eq_length_filter]
  change (A.toList.filter (fun r => tag r == j)).length = count tag A j
  have nd := (Finset.nodup_toList A).filter (fun r => tag r == j)
  have eq : (A.toList.filter (fun r => tag r == j)).toFinset =
      A.filter (fun r => tag r = j) := by
    ext r
    simp
  rw [← List.toFinset_card_of_nodup nd, eq]
  rfl

lemma classList_perm (left : α → β) (right : γ → β) (A : Finset α) (B : Finset γ)
    (same : ∀ j, count left A j = count right B j) :
    (A.toList.map left).Perm (B.toList.map right) := by
  apply List.perm_iff_count.mpr
  intro j
  rw [list_count, list_count, same]

lemma budgetRunCut_transport (left : α → β) (right : γ → β) (signal : β → Sig)
    (A : Finset α) (B : Finset γ) (same : ∀ j, count left A j = count right B j)
    (u : Bool) (T : Sig) (depth : Nat)
    (blocked : BudgetRunCut A (fun r => signal (left r)) u T depth) :
    BudgetRunCut B (fun r => signal (right r)) u T depth := by
  have perm := classList_perm left right A B same
  have sizes := perm.length_eq
  simp only [List.length_map, Finset.length_toList] at sizes
  intro n hn run
  apply blocked n (by omega)
  apply Run.perm ?_ run
  simpa only [List.map_map, Function.comp_def] using
    perm.symm.map (fun j => observe (signal j))

lemma duplicate_counts_congr (tag : α → β) (roots A B : Finset α)
    (subA : A ⊆ roots) (subB : B ⊆ roots)
    (same : ∀ j, count tag A j = count tag B j) (w j : β) :
    count (Sum.elim tag (fun _ : Bool => w)) (duplicateRoots roots A) j =
      count (Sum.elim tag (fun _ : Bool => w)) (duplicateRoots roots B) j := by
  rw [count_duplicate tag roots A subA, count_duplicate tag roots B subB, same]

lemma compress_counts_congr (tag : α → β) (roots A B : Finset α)
    (subA : A ⊆ roots) (subB : B ⊆ roots)
    (same : ∀ j, count tag A j = count tag B j) (w j : β) :
    count (Sum.elim tag (fun _ : Bool => w)) (compressRoots roots A) j =
      count (Sum.elim tag (fun _ : Bool => w)) (compressRoots roots B) j := by
  rw [count_compress tag roots A subA, count_compress tag roots B subB, same]

lemma duplicate_budgetRunCut_congr (tag : α → β) (signal : β → Sig)
    (roots A B : Finset α) (subA : A ⊆ roots) (subB : B ⊆ roots)
    (same : ∀ j, count tag A j = count tag B j) (w : β) (u : Bool) (T : Sig) (depth : Nat)
    (blocked : BudgetRunCut (duplicateRoots roots A)
      (duplicateRaw (fun r => signal (tag r)) (signal w)) u T depth) :
    BudgetRunCut (duplicateRoots roots B)
      (duplicateRaw (fun r => signal (tag r)) (signal w)) u T depth := by
  have raw_eq : duplicateRaw (fun r => signal (tag r)) (signal w) =
      (fun r : Sum α Bool => signal (Sum.elim tag (fun _ => w) r)) := by
    funext r
    cases r <;> rfl
  rw [raw_eq] at blocked ⊢
  exact budgetRunCut_transport _ _ signal _ _
    (duplicate_counts_congr tag roots A B subA subB same w) u T depth blocked

lemma compress_budgetRunCut_congr (tag : α → β) (signal : β → Sig)
    (roots A B : Finset α) (subA : A ⊆ roots) (subB : B ⊆ roots)
    (same : ∀ j, count tag A j = count tag B j) (w : β) (u : Bool) (T : Sig) (depth : Nat)
    (blocked : BudgetRunCut (compressRoots roots A)
      (duplicateRaw (fun r => signal (tag r)) (signal w)) u T depth) :
    BudgetRunCut (compressRoots roots B)
      (duplicateRaw (fun r => signal (tag r)) (signal w)) u T depth := by
  have raw_eq : duplicateRaw (fun r => signal (tag r)) (signal w) =
      (fun r : Sum α Bool => signal (Sum.elim tag (fun _ => w) r)) := by
    funext r
    cases r <;> rfl
  rw [raw_eq] at blocked ⊢
  exact budgetRunCut_transport _ _ signal _ _
    (compress_counts_congr tag roots A B subA subB same w) u T depth blocked

end PEqualNP.Outside.L_meta_2373.CountVector
