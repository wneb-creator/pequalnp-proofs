import CountNodeCompletion
import PrunedRename

namespace PEqualNP.Outside.L_meta_2373.CountVector
open Live1024

theorem countNode_rename_regroup {m n : Nat}
    (f : Row → Row) (onto : Function.Surjective f) (u : Bool) (T : Sig)
    (targetFixed : rename f T = T) (depth : Nat)
    (total : Fin m → Nat) (signal : Fin m → Sig)
    (map : Fin m → Fin n) (priorTotal : Fin n → Nat) (priorSignal : Fin n → Sig)
    (priorTable : (Fin n → Nat) → Sig → Prop)
    (totals : regroup map total = priorTotal)
    (signals : ∀ j, 0 < total j → priorSignal (map j) = rename f (signal j))
    (prior : CountNode priorTotal priorSignal (pairColumn u) (pairColumn u T)
      u T depth priorTable) :
    CountNode total signal (pairColumn u) (pairColumn u T) u T depth
      (fun counts v => priorTable (regroup map counts) (rename f v)) := by
  intro α inst roots tag same
  let nextTag := fun r => map (tag r)
  have counts : count nextTag roots = priorTotal := by
    rw [count_regroup tag map roots, same]
    exact totals
  have agrees : ∀ r ∈ roots,
      priorSignal (nextTag r) = rename f (signal (tag r)) := by
    intro r hr
    apply signals (tag r)
    rw [← same]
    change 0 < (roots.filter (fun x => tag x = tag r)).card
    exact Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩⟩
  have moved := prunedNode_raw_congr (pairColumn u) (pairColumn u T) u T depth roots
    (fun r => priorSignal (nextTag r)) (fun r => rename f (signal (tag r)))
    (countCert roots nextTag priorTable) agrees (prior roots nextTag counts)
  have pulled := prunedNode_rename_pullback f onto u T targetFixed depth roots
    (fun r => signal (tag r)) (countCert roots nextTag priorTable) moved
  change PrunedNode (pairColumn u) (pairColumn u T) u T depth α roots
    (fun r => signal (tag r))
    (fun A v => A ⊆ roots ∧ priorTable (regroup map (count tag A)) (rename f v))
  simpa only [countCert, nextTag, count_regroup] using pulled

end PEqualNP.Outside.L_meta_2373.CountVector
