import CountDagCheck
import CountFixture1098

namespace PEqualNP.Outside.L_meta_2373.CountFixture1098
open Live1024 CountVector

def sources : List (Sum (Fin 12) (Nat × Nat × Nat)) :=
  (List.ofFn (fun j : Fin 12 => Sum.inl j)) ++ [Sum.inr (0, 3, 1)]

lemma checked_provenance : dagCheck false signal entries sources = true := by
  decide +kernel

theorem entry_provenance {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (tag : α → Fin 12) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (T : Sig) (depth : Nat)
    (initial : ∀ r ∈ roots, Cert {r} (signal (tag r)))
    (closed : PrunedGateClosed roots (fun r => signal (tag r)) col need Cert false T depth)
    (gateCol : ∀ d a b, allowed false d → col (bin d a b) ⊆ col a ∪ col b)
    (i : Nat) (hi : i < entries.length) (A : Finset α)
    (same : count tag A = (dagEntry entries i).1) (sub : A ⊆ roots) :
    ReadOnce (fun r => signal (tag r)) false A (dagEntry entries i).2 ∧
      ColumnSupport (fun r => signal (tag r)) col A (dagEntry entries i).2 ∧
      ProvenanceBridge roots (fun r => signal (tag r)) col need Cert false T depth
        A (dagEntry entries i).2 :=
  dagCheck_replay roots tag signal col need Cert false T depth initial closed gateCol
    entries sources checked_provenance i hi A same sub

end PEqualNP.Outside.L_meta_2373.CountFixture1098
