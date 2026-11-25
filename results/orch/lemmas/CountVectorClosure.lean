import CountVectorTransport

namespace PEqualNP.Outside.L_meta_2373.CountVector

open Live1024

variable {α β Ω : Type} [DecidableEq α] [DecidableEq β]

def CountAdmissible (total used : β → Nat) (signal : β → Sig)
    (col : Sig → Set Ω) (need : Set Ω) (v : Sig) : Prop :=
  ∀ o ∈ need, (∀ j, used j < total j → o ∉ col (signal j)) → o ∈ col v

def CountClosed (total : β → Nat) (signal : β → Sig) (col : Sig → Set Ω)
    (need : Set Ω) (table cut : (β → Nat) → Sig → Prop) (u : Bool) : Prop :=
  ∀ ca cb a b d, (∀ j, ca j + cb j ≤ total j) → allowed u d → a ≠ b →
    bin d a b ≠ a → bin d a b ≠ b → proper (bin d a b) →
    table ca a → table cb b →
    CountAdmissible total (fun j => ca j + cb j) signal col need (bin d a b) →
    table (fun j => ca j + cb j) (bin d a b) ∨ cut (fun j => ca j + cb j) (bin d a b)

lemma prunedGateClosed_of_count (roots : Finset α) (tag : α → β) (signal : β → Sig)
    (col : Sig → Set Ω) (need : Set Ω) (table cut : (β → Nat) → Sig → Prop)
    (u : Bool) (T : Sig) (depth : Nat)
    (closed : CountClosed (count tag roots) signal col need table cut u)
    (cutSound : ∀ A v, A ⊆ roots → cut (count tag A) v →
      BudgetRunCut (compressRoots roots A) (duplicateRaw (fun r => signal (tag r)) v) u T depth) :
    PrunedGateClosed roots (fun r => signal (tag r)) col need
      (countCert roots tag table) u T depth := by
  intro A B a b d dis hd hab hza hzb proper ca cb adm
  have sub : A ∪ B ⊆ roots := Finset.union_subset ca.1 cb.1
  have eq : count tag (A ∪ B) = (fun j => count tag A j + count tag B j) :=
    funext (count_union tag A B dis)
  have classes : CountAdmissible (count tag roots) (count tag (A ∪ B))
      signal col need (bin d a b) :=
    (admissible_iff tag signal roots (A ∪ B) sub col need _).mp adm
  rw [eq] at classes
  have result := closed (count tag A) (count tag B) a b d
    (count_union_capacity tag roots A B ca.1 cb.1 dis) hd hab hza hzb proper ca.2 cb.2 classes
  rw [← eq] at result
  rcases result with kept | cutEntry
  · exact Or.inl ⟨sub, kept⟩
  · exact Or.inr (cutSound (A ∪ B) _ sub cutEntry)

lemma count_positive_of_mem (tag : α → β) (roots : Finset α) (r : α) (mem : r ∈ roots) :
    0 < count tag roots (tag r) :=
  Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨mem, rfl⟩⟩

lemma prunedNode_zero_of_count (roots : Finset α) (tag : α → β) (signal : β → Sig)
    (col : Sig → Set Ω) (need : Set Ω) (table cut : (β → Nat) → Sig → Prop)
    (u : Bool) (T : Sig)
    (leaves : ∀ j, 0 < count tag roots j → table (fun k => if j = k then 1 else 0) (signal j))
    (closed : CountClosed (count tag roots) signal col need table cut u)
    (cutSound : ∀ A v, A ⊆ roots → cut (count tag A) v →
      BudgetRunCut (compressRoots roots A) (duplicateRaw (fun r => signal (tag r)) v) u T 0)
    (missing : ¬ table (count tag roots) T) :
    PrunedNode col need u T 0 α roots (fun r => signal (tag r)) (countCert roots tag table) := by
  refine ⟨?_, prunedGateClosed_of_count roots tag signal col need table cut u T 0 closed cutSound,
    ?_, trivial⟩
  · intro r hr
    exact countCert_leaf roots tag signal table r hr
      (leaves (tag r) (count_positive_of_mem tag roots r hr))
  · exact fun h => missing h.2

end PEqualNP.Outside.L_meta_2373.CountVector
