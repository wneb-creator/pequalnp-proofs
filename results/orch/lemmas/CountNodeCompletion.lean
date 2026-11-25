import CountVectorRegroup
import PrunedRawCongruence
import CountDagCopyBridge

namespace PEqualNP.Outside.L_meta_2373.CountVector
open Live1024

abbrev CountNode {m : Nat} {Ω : Type} (total : Fin m → Nat) (signal : Fin m → Sig)
    (col : Sig → Set Ω) (need : Set Ω) (u : Bool) (T : Sig) (depth : Nat)
    (table : (Fin m → Nat) → Sig → Prop) : Prop :=
  ∀ {α : Type} [DecidableEq α] (roots : Finset α) (tag : α → Fin m),
    count tag roots = total →
    PrunedNode col need u T depth α roots (fun r => signal (tag r)) (countCert roots tag table)

theorem copied_count_node {α Ω : Type} [DecidableEq α] {m n : Nat}
    (roots : Finset α) (tag : α → Fin m) (total : Fin m → Nat) (signal : Fin m → Sig)
    (same : count tag roots = total) (A : Finset α) (sub : A ⊆ roots)
    (used : Fin m → Nat) (selected : count tag A = used) (v : Sig)
    (map : Fin m → Fin n) (slot : Fin n) (nextTotal : Fin n → Nat) (nextSignal : Fin n → Sig)
    (nextTable : (Fin n → Nat) → Sig → Prop)
    (totals : ∀ j, regroup map total j - regroup map used j + (if slot = j then 2 else 0) = nextTotal j)
    (signals : ∀ j, used j < total j → nextSignal (map j) = signal j)
    (copied : nextSignal slot = v)
    (col : Sig → Set Ω) (need : Set Ω) (u : Bool) (T : Sig) (depth : Nat)
    (child : CountNode nextTotal nextSignal col need u T depth nextTable) :
    PrunedNode col need u T depth (Sum α Bool) (duplicateRoots roots A)
      (duplicateRaw (fun r => signal (tag r)) v)
      (countCert (duplicateRoots roots A)
        (Sum.elim (fun r => map (tag r)) (fun _ : Bool => slot)) nextTable) := by
  let nextTag := Sum.elim (fun r => map (tag r)) (fun _ : Bool => slot)
  have counts : count nextTag (duplicateRoots roots A) = nextTotal := by
    funext j
    rw [count_duplicate_regroup tag map roots A sub, same, selected]
    exact totals j
  have agrees := duplicateRaw_regroup tag map roots A sub signal nextSignal slot v
    (fun j h => signals j (by simpa only [same, selected] using h)) copied
  exact prunedNode_raw_congr col need u T depth _ _ _ _ agrees
    (child (duplicateRoots roots A) nextTag counts)

theorem copied_count_node_bridge {α Ω : Type} [DecidableEq α] {m n : Nat}
    (roots : Finset α) (tag : α → Fin m) (total : Fin m → Nat) (signal : Fin m → Sig)
    (same : count tag roots = total) (A : Finset α) (sub : A ⊆ roots)
    (used : Fin m → Nat) (selected : count tag A = used) (v : Sig)
    (map : Fin m → Fin n) (slot : Fin n) (nextTotal : Fin n → Nat) (nextSignal : Fin n → Sig)
    (nextTable : (Fin n → Nat) → Sig → Prop)
    (totals : ∀ j, regroup map total j - regroup map used j + (if slot = j then 2 else 0) = nextTotal j)
    (signals : ∀ j, used j < total j → nextSignal (map j) = signal j)
    (copied : nextSignal slot = v)
    (col : Sig → Set Ω) (need : Set Ω) (u : Bool) (T : Sig) (depth : Nat)
    (child : CountNode nextTotal nextSignal col need u T depth nextTable)
    (entries : List (DagEntry m)) (sources : List (Sum (Fin m) (Nat × Nat × Nat)))
    (checked : dagCheck u signal entries sources = true) (extra : Fin m)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b) :
    ∃ Cert2 : Finset (Sum α Bool) → Sig → Prop,
      PrunedBridge roots (fun r => signal (tag r)) col need
        (countCert roots tag (fun c w => (c, w) ∈ entries)) Cert2 u T depth A v ∧
      PrunedNode col need u T depth (Sum α Bool) (duplicateRoots roots A)
        (duplicateRaw (fun r => signal (tag r)) v) Cert2 := by
  have node := copied_count_node roots tag total signal same A sub used selected v
    map slot nextTotal nextSignal nextTable totals signals copied col need u T depth child
  cases depth <;> exact ⟨_, dagCheck_copy_bridge roots tag signal extra col need u T _ A v
    entries sources checked _ node.1 node.2.1 gateCol, node⟩

end PEqualNP.Outside.L_meta_2373.CountVector
