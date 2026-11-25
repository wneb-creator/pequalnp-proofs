import PrunedMerge
import SharingReadOnce

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem pruned_single_transfer {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (Cert2 : Finset (Sum α Bool) → Sig → Prop)
    (u : Bool) (T : Sig) (depth : Nat)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (U : Finset Sig) (a b : Sig) (d k : Nat) (label : Sig → Finset α)
    (hd : allowed u d) (pa : proper a) (pb : proper b) (hab : a ≠ b)
    (fresh : bin d a b ∉ insert a (insert b U)) (ha : a ∈ U) (hb : b ∉ U)
    (tail : Live u T k (insert (bin d a b) U))
    (cap : k + 1 ≤ (insert (bin d a b) U).card + depth)
    (part : LabelPartition roots (insert a (insert b U)) label)
    (entries : ∀ v ∈ insert a (insert b U), Cert (label v) v)
    (traces : ∀ v ∈ insert a (insert b U), ReadOnce raw u (label v) v)
    (supports : ∀ v ∈ insert a (insert b U), ColumnSupport raw col (label v) v)
    (bridge : PrunedBridge roots raw col need Cert Cert2 u T depth (label a) a)
    (initial : ∀ r ∈ duplicateRoots roots (label a), Cert2 {r} (duplicateRaw raw a r))
    (closed : PrunedGateClosed (duplicateRoots roots (label a)) (duplicateRaw raw a)
      col need Cert2 u T depth) :
    ∃ next : Sig → Finset (Sum α Bool),
      LabelPartition (duplicateRoots roots (label a)) (insert (bin d a b) U) next ∧
      (∀ v ∈ insert (bin d a b) U, Cert2 (next v) v) ∧
      (∀ v ∈ insert (bin d a b) U, ReadOnce (duplicateRaw raw a) u (next v) v) ∧
      (∀ v ∈ insert (bin d a b) U, ColumnSupport (duplicateRaw raw a) col (next v) v) := by
  let next := sharingLabels label a b (bin d a b)
  have pn := sharing_partition roots U a b (bin d a b) label hab fresh ha hb part
  have tn := sharing_readOnce raw u U a b d hd fresh label traces
  have sn := sharing_support raw col u gateCol U a b d hd fresh label supports
  have notU : bin d a b ∉ U := fun h => fresh (by simp [h])
  have oldEq : insert a (insert b U) = insert b U :=
    Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)
  have oldCap : k + 2 ≤ (insert a (insert b U)).card + (depth + 1) := by
    rw [oldEq, Finset.card_insert_of_notMem hb]
    rw [Finset.card_insert_of_notMem notU] at cap
    omega
  have lifted := pruned_bridge_live_copy roots raw col need Cert Cert2 u T depth rowCover
    U a b d k label hd pa pb hab fresh ha tail oldCap part entries traces supports bridge
  have leaf (t : Bool) : Cert2 {Sum.inr t} a := by
    simpa [duplicateRaw] using initial (Sum.inr t) (by cases t <;> simp [duplicateRoots])
  have disjoint : Disjoint ({Sum.inr true} : Finset (Sum α Bool)) (liftLabels (label b)) := by
    simp [liftLabels]
  have nz : next (bin d a b) = {Sum.inr true} ∪ liftLabels (label b) := by
    simp [next, sharingLabels, Finset.singleton_union]
  have za : bin d a b ≠ a := fun h => fresh (by simp [h])
  have zb : bin d a b ≠ b := fun h => fresh (by simp [h])
  have generated := pruned_closed_live
    (duplicateRoots roots (label a)) (duplicateRaw raw a) col need Cert2 u T depth
    rowCover closed tail cap next pn tn sn {Sum.inr true} (liftLabels (label b)) a b d
    disjoint hd hab za zb (leaf true) (lifted b (by simp) hab.symm) (by simp) nz
  refine ⟨next, pn, ?_, tn, sn⟩
  intro v hv
  rcases Finset.mem_insert.mp hv with vz | hv
  · subst v
    simpa only [nz] using generated
  · have vz : v ≠ bin d a b := by intro h; subst v; exact notU hv
    by_cases va : v = a
    · subst v
      simpa [next, sharingLabels, vz] using leaf false
    · simpa [next, sharingLabels, vz, va] using lifted v (by simp [hv]) va

end PEqualNP.Outside.L_meta_2373.Live1024
