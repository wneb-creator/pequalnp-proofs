import CountVectorCore
import PrunedInterface

namespace PEqualNP.Outside.L_meta_2373.CountVector

open Live1024

variable {α β Ω : Type} [DecidableEq α] [DecidableEq β]

lemma count_lift (tag : α → β) (w : β) (A : Finset α) (j : β) :
    count (Sum.elim tag (fun _ : Bool => w)) (liftLabels A) j = count tag A j :=
  count_image tag _ Sum.inl Sum.inl_injective (fun _ => rfl) A j

lemma count_copy_slots (tag : α → β) (w j : β) :
    count (Sum.elim tag (fun _ : Bool => w)) {Sum.inr false, Sum.inr true} j =
      if w = j then 2 else 0 := by
  have dis : Disjoint ({Sum.inr false} : Finset (Sum α Bool)) {Sum.inr true} := by simp
  have eq : ({Sum.inr false, Sum.inr true} : Finset (Sum α Bool)) =
      {Sum.inr false} ∪ {Sum.inr true} := by ext r; simp
  rw [eq, count_union _ _ _ dis, count_singleton, count_singleton]
  by_cases h : w = j <;> simp [h]

lemma count_duplicate (tag : α → β) (roots A : Finset α) (sub : A ⊆ roots) (w j : β) :
    count (Sum.elim tag (fun _ : Bool => w)) (duplicateRoots roots A) j =
      count tag roots j - count tag A j + if w = j then 2 else 0 := by
  have dis : Disjoint (liftLabels (roots \ A))
      ({Sum.inr false, Sum.inr true} : Finset (Sum α Bool)) := by
    apply Finset.disjoint_left.mpr
    intro r hr hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    simp at hn
  rw [duplicateRoots, count_union _ _ _ dis, count_lift, count_copy_slots, count_sdiff tag roots A sub]

lemma count_compress (tag : α → β) (roots A : Finset α) (sub : A ⊆ roots) (w j : β) :
    count (Sum.elim tag (fun _ : Bool => w)) (compressRoots roots A) j =
      count tag roots j - count tag A j + if w = j then 1 else 0 := by
  have dis : Disjoint (liftLabels (roots \ A))
      ({Sum.inr false} : Finset (Sum α Bool)) := by
    apply Finset.disjoint_left.mpr
    intro r hr hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    simp at hn
  rw [compressRoots, count_union _ _ _ dis, count_lift, count_singleton, count_sdiff tag roots A sub]
  rfl

lemma admissible_iff (tag : α → β) (signal : β → Sig) (roots A : Finset α)
    (sub : A ⊆ roots) (col : Sig → Set Ω) (need : Set Ω) (v : Sig) :
    ColumnAdmissible roots (fun r => signal (tag r)) col need A v ↔
      ∀ o ∈ need, (∀ j, count tag A j < count tag roots j → o ∉ col (signal j)) →
        o ∈ col v := by
  constructor
  · intro adm o ho outside
    exact adm o ho ((outside_absent_iff tag roots A sub (fun j => col (signal j)) o).mpr outside)
  · intro adm o ho outside
    exact adm o ho ((outside_absent_iff tag roots A sub (fun j => col (signal j)) o).mp outside)

def countCert (roots : Finset α) (tag : α → β)
    (table : (β → Nat) → Sig → Prop) (A : Finset α) (v : Sig) : Prop :=
  A ⊆ roots ∧ table (count tag A) v

lemma countCert_leaf (roots : Finset α) (tag : α → β) (signal : β → Sig)
    (table : (β → Nat) → Sig → Prop) (r : α) (mem : r ∈ roots)
    (entry : table (fun j => if tag r = j then 1 else 0) (signal (tag r))) :
    countCert roots tag table {r} (signal (tag r)) := by
  refine ⟨Finset.singleton_subset_iff.mpr mem, ?_⟩
  have eq : count tag {r} = (fun j => if tag r = j then 1 else 0) :=
    funext (count_singleton tag r)
  rw [eq]
  exact entry

lemma count_union_capacity (tag : α → β) (roots A B : Finset α)
    (subA : A ⊆ roots) (subB : B ⊆ roots) (dis : Disjoint A B) (j : β) :
    count tag A j + count tag B j ≤ count tag roots j := by
  rw [← count_union tag A B dis]
  exact count_mono tag (Finset.union_subset subA subB) j

lemma countCert_union (roots : Finset α) (tag : α → β)
    (table : (β → Nat) → Sig → Prop) (A B : Finset α) (a b v : Sig)
    (ca : countCert roots tag table A a) (cb : countCert roots tag table B b)
    (dis : Disjoint A B)
    (entry : table (fun j => count tag A j + count tag B j) v) :
    countCert roots tag table (A ∪ B) v := by
  refine ⟨Finset.union_subset ca.1 cb.1, ?_⟩
  have eq : count tag (A ∪ B) = (fun j => count tag A j + count tag B j) :=
    funext (count_union tag A B dis)
  rw [eq]
  exact entry

end PEqualNP.Outside.L_meta_2373.CountVector
