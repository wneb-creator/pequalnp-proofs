import CompressedWireCut

namespace PEqualNP.Outside.L_meta_2373.Live1024

def ColumnSupport {α Ω : Type} (raw : α → Sig) (col : Sig → Set Ω)
    (A : Finset α) (v : Sig) : Prop :=
  ∀ o ∈ col v, ∃ r ∈ A, o ∈ col (raw r)

def ColumnAdmissible {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (A : Finset α) (v : Sig) : Prop :=
  ∀ o ∈ need, (∀ r ∈ roots, r ∉ A → o ∉ col (raw r)) → o ∈ col v

abbrev BudgetRunCut {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat) : Prop :=
  ∀ n, n + 1 ≤ roots.card + depth →
    ¬ Run u (observe T) n (roots.toList.map (fun r => observe (raw r)))

abbrev PrunedGateClosed {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig) (depth : Nat) : Prop :=
  ∀ A B a b d, Disjoint A B → allowed u d → a ≠ b → bin d a b ≠ a →
    bin d a b ≠ b → proper (bin d a b) → Cert A a → Cert B b →
    ColumnAdmissible roots raw col need (A ∪ B) (bin d a b) →
    Cert (A ∪ B) (bin d a b) ∨
      BudgetRunCut (compressRoots roots (A ∪ B)) (duplicateRaw raw (bin d a b)) u T depth

abbrev PrunedBridge {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (Cert2 : Finset (Sum α Bool) → Sig → Prop)
    (u : Bool) (T : Sig) (depth : Nat) (A : Finset α) (w : Sig) : Prop :=
  ∀ B v, Cert B v → Disjoint A B →
    ColumnAdmissible (duplicateRoots roots A) (duplicateRaw raw w) col need
      (liftLabels B) v →
    Cert2 (liftLabels B) v ∨
      BudgetRunCut (compressRoots (duplicateRoots roots A) (liftLabels B))
        (duplicateRaw (duplicateRaw raw w) v) u T depth

def PrunedNode {Ω : Type} (col : Sig → Set Ω) (need : Set Ω) (u : Bool) (T : Sig)
    (depth : Nat) (α : Type) [DecidableEq α] (roots : Finset α) (raw : α → Sig)
    (Cert : Finset α → Sig → Prop) : Prop :=
  (∀ r ∈ roots, Cert {r} (raw r)) ∧
  PrunedGateClosed roots raw col need Cert u T depth ∧
  ¬ Cert roots T ∧
  match depth with
  | 0 => True
  | n + 1 =>
    ∀ A w, A ⊆ roots → proper w → Cert A w →
      BudgetRunCut (duplicateRoots roots A) (duplicateRaw raw w) u T n ∨
      ∃ Cert2 : Finset (Sum α Bool) → Sig → Prop,
        PrunedBridge roots raw col need Cert Cert2 u T n A w ∧
        PrunedNode col need u T n (Sum α Bool)
          (duplicateRoots roots A) (duplicateRaw raw w) Cert2

end PEqualNP.Outside.L_meta_2373.Live1024
