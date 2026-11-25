import CountNodeCompletion
import CountTableChecker

namespace PEqualNP.Outside.L_meta_2373.CountVector
open Live1024

theorem countNode_succ {m : Nat} {Ω : Type} (total : Fin m → Nat) (signal : Fin m → Sig)
    (col : Sig → Set Ω) (need : Set Ω) (u : Bool) (T : Sig) (depth : Nat)
    (table cut : (Fin m → Nat) → Sig → Prop)
    (leaves : ∀ j, 0 < total j → table (fun k => if j = k then 1 else 0) (signal j))
    (closed : CountClosed total signal col need table cut u)
    (missing : ¬ table total T)
    (cutSound : ∀ {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin m),
      count tag roots = total → ∀ A v, A ⊆ roots → cut (count tag A) v →
        BudgetRunCut (compressRoots roots A) (duplicateRaw (fun r => signal (tag r)) v)
          u T (depth + 1))
    (children : ∀ {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin m),
      count tag roots = total → ∀ A v, A ⊆ roots → proper v → table (count tag A) v →
        BudgetRunCut (duplicateRoots roots A) (duplicateRaw (fun r => signal (tag r)) v)
          u T depth ∨
        ∃ Cert2 : Finset (Sum α Bool) → Sig → Prop,
          PrunedBridge roots (fun r => signal (tag r)) col need (countCert roots tag table)
            Cert2 u T depth A v ∧
          PrunedNode col need u T depth (Sum α Bool) (duplicateRoots roots A)
            (duplicateRaw (fun r => signal (tag r)) v) Cert2) :
    CountNode total signal col need u T (depth + 1) table := by
  intro α inst roots tag same
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    apply countCert_leaf roots tag signal table r hr
    apply leaves
    rw [← same]
    exact count_positive_of_mem tag roots r hr
  · exact prunedGateClosed_of_count roots tag signal col need table cut u T (depth + 1)
      (by simpa only [same] using closed) (cutSound roots tag same)
  · intro member
    apply missing
    simpa only [same] using member.2
  · intro A v sub proper member
    exact children roots tag same A v sub proper member.2

end PEqualNP.Outside.L_meta_2373.CountVector
