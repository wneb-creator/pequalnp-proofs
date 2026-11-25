import IntermediateCopyCut

namespace PEqualNP.Outside.L_meta_2373.Live1024

def compressLabels {α : Type} [DecidableEq α] (label : Sig → Finset α)
    (z v : Sig) : Finset (Sum α Bool) :=
  if v = z then {Sum.inr false} else liftLabels (label v)

def compressRoots {α : Type} [DecidableEq α] (roots A : Finset α) :
    Finset (Sum α Bool) := liftLabels (roots \ A) ∪ {Sum.inr false}

theorem compress_partition {α : Type} [DecidableEq α]
    (roots : Finset α) (S : Finset Sig) (label : Sig → Finset α)
    (z : Sig) (part : LabelPartition roots S label) (hz : z ∈ S) :
    LabelPartition (compressRoots roots (label z)) S (compressLabels label z) := by
  classical
  let next := compressLabels label z
  have leftMem (v : Sig) (r : α) :
      Sum.inl r ∈ next v ↔ v ≠ z ∧ r ∈ label v := by
    by_cases vz : v = z <;> simp [next, compressLabels, liftLabels, vz]
  have falseMem (v : Sig) : Sum.inr false ∈ next v ↔ v = z := by
    by_cases vz : v = z <;> simp [next, compressLabels, liftLabels, vz]
  have trueNotMem (v : Sig) : Sum.inr true ∉ next v := by
    by_cases vz : v = z <;> simp [next, compressLabels, liftLabels, vz]
  change LabelPartition (compressRoots roots (label z)) S next
  refine ⟨?_, ?_, ?_⟩
  · intro v hv q hq
    cases q with
    | inl r =>
      obtain ⟨vz, hr⟩ := (leftMem v r).mp hq
      have rRoot := part.1 v hv hr
      have notZ : r ∉ label z := fun h =>
        Finset.disjoint_left.mp (part.2.1 v hv z hz vz) hr h
      simp [compressRoots, liftLabels, rRoot, notZ]
    | inr bit =>
      cases bit with
      | false => simp [compressRoots]
      | true => exact False.elim (trueNotMem v hq)
  · intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro q hqv hqw
    cases q with
    | inl r =>
      exact Finset.disjoint_left.mp (part.2.1 v hv w hw hne)
        ((leftMem v r).mp hqv).2 ((leftMem w r).mp hqw).2
    | inr bit =>
      cases bit with
      | false => exact hne (((falseMem v).mp hqv).trans ((falseMem w).mp hqw).symm)
      | true => exact trueNotMem v hqv
  · intro q hq
    cases q with
    | inl r =>
      have hr : r ∈ roots ∧ r ∉ label z := by
        simpa [compressRoots, liftLabels] using hq
      obtain ⟨v, hv, hrv⟩ := part.2.2 r hr.1
      have vz : v ≠ z := by rintro rfl; exact hr.2 hrv
      exact ⟨v, hv, (leftMem v r).mpr ⟨vz, hrv⟩⟩
    | inr bit =>
      cases bit with
      | false => exact ⟨z, hz, (falseMem z).mpr rfl⟩
      | true => simpa [compressRoots, liftLabels] using hq

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem compress_wire_readOnce {α : Type} [DecidableEq α]
    (raw : α → Sig) (u : Bool) (S : Finset Sig) (label : Sig → Finset α) (z : Sig)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) v) :
    ∀ v ∈ S, ReadOnce (duplicateRaw raw z) u (compressLabels label z v) v := by
  intro v hv
  by_cases hvz : v = z
  · subst v
    simpa [compressLabels, duplicateRaw] using
      ReadOnce.leaf (duplicateRaw raw z) u (Sum.inr false)
  · have mapped := ReadOnce.map raw (duplicateRaw raw z) u Sum.inl
      (by intro x y h; cases h; rfl) (by intro r; rfl) (entries v hv)
    simpa [compressLabels, hvz, liftLabels] using mapped

theorem compressed_wire_forest_exclusion {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    {k : Nat} {S : Finset Sig} (run : Live u T k S) (cap : k + 1 ≤ S.card + depth)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) v)
    (z : Sig) (hz : z ∈ S)
    (blocked : ∀ n, n + 1 ≤ (compressRoots roots (label z)).card + depth →
      ¬ Run u (observe T) n
        ((compressRoots roots (label z)).toList.map
          (fun r => observe (duplicateRaw raw z r)))) : False := by
  have part2 := compress_partition roots S label z part hz
  have entries2 := compress_wire_readOnce raw u S label z entries
  exact readOnce_forest_exclusion_state
    (compressRoots roots (label z)) (duplicateRaw raw z) u T depth blocked
    run cap (compressLabels label z) part2 entries2

end PEqualNP.Outside.L_meta_2373.Live1024
