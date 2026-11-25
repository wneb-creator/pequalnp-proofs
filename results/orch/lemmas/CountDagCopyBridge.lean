import CountDagReplayOn
import CountVectorAdapters

namespace PEqualNP.Outside.L_meta_2373.CountVector
open Live1024

theorem dagCheck_copy_bridge {α Ω : Type} [DecidableEq α] {m : Nat}
    (roots : Finset α) (tag : α → Fin m) (signal : Fin m → Sig) (extra : Fin m)
    (col : Sig → Set Ω) (need : Set Ω) (u : Bool) (T : Sig) (depth : Nat)
    (A : Finset α) (w : Sig)
    (entries : List (DagEntry m)) (sources : List (Sum (Fin m) (Nat × Nat × Nat)))
    (checked : dagCheck u signal entries sources = true)
    (Cert2 : Finset (Sum α Bool) → Sig → Prop)
    (initial : ∀ r ∈ duplicateRoots roots A,
      Cert2 {r} (duplicateRaw (fun r => signal (tag r)) w r))
    (closed : PrunedGateClosed (duplicateRoots roots A)
      (duplicateRaw (fun r => signal (tag r)) w) col need Cert2 u T depth)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b) :
    PrunedBridge roots (fun r => signal (tag r)) col need
      (countCert roots tag (fun c v => (c, v) ∈ entries)) Cert2 u T depth A w := by
  intro B v entry disjoint admissible
  obtain ⟨subB, member⟩ := entry
  obtain ⟨i, hi, value⟩ := List.mem_iff_getElem.mp member
  have eq : dagEntry entries i = (count tag B, v) := by
    simpa only [dagEntry, List.getD_eq_getElem entries _ hi] using value
  let next : Sum α Bool → Fin m := Sum.elim tag (fun _ => extra)
  have agrees : ∀ r ∈ liftLabels roots,
      duplicateRaw (fun r => signal (tag r)) w r = signal (next r) := by
    intro r hr
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hr
    rfl
  have sub : liftLabels B ⊆ duplicateRoots roots A := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨s, Finset.mem_sdiff.mpr ⟨subB hs, ?_⟩, rfl⟩
    intro ha
    exact Finset.disjoint_left.mp disjoint ha hs
  have inside : liftLabels B ⊆ liftLabels roots := Finset.image_mono Sum.inl subB
  have counts : count next (liftLabels B) = (dagEntry entries i).1 := by
    funext j
    exact (count_image tag next Sum.inl Sum.inl_injective (fun _ => rfl) B j).trans
      (congrFun (congrArg Prod.fst eq) j).symm
  have replay := dagCheck_replay_on (duplicateRoots roots A) (liftLabels roots)
    (duplicateRaw (fun r => signal (tag r)) w) next signal agrees col need Cert2 u T depth
    initial closed gateCol entries sources checked i hi (liftLabels B) counts sub inside
  have bridge := replay.2.2
  rw [eq] at bridge
  exact bridge admissible

end PEqualNP.Outside.L_meta_2373.CountVector
