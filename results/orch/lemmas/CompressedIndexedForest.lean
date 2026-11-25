import CompressedWireCut

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem compress_indexed_readOnce {α : Type} [DecidableEq α]
    (raw : α → Sig) (u : Bool) (S : Finset Sig)
    (value : Sig → Sig) (label : Sig → Finset α) (z : Sig)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) (value v)) :
    ∀ v ∈ S, ReadOnce (duplicateRaw raw (value z)) u
      (compressLabels label z v) (value v) := by
  intro v hv
  by_cases hvz : v = z
  · subst v
    simpa [compressLabels, duplicateRaw] using
      ReadOnce.leaf (duplicateRaw raw (value z)) u (Sum.inr false)
  · have mapped := ReadOnce.map raw (duplicateRaw raw (value z)) u Sum.inl
      (by intro x y h; cases h; rfl) (by intro r; rfl) (entries v hv)
    simpa [compressLabels, hvz, liftLabels] using mapped

theorem compressed_indexed_forest_exclusion {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    {k : Nat} {S : Finset Sig} (value : Sig → Sig)
    (run : Run u (observe T) k (S.toList.map (fun v => observe (value v))))
    (cap : k + 1 ≤ S.card + depth)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) (value v))
    (z : Sig) (hz : z ∈ S)
    (blocked : ∀ n, n + 1 ≤ (compressRoots roots (label z)).card + depth →
      ¬ Run u (observe T) n
        ((compressRoots roots (label z)).toList.map
          (fun r => observe (duplicateRaw raw (value z) r)))) : False := by
  have part2 := compress_partition roots S label z part hz
  have entries2 := compress_indexed_readOnce raw u S value label z entries
  exact readOnce_indexed_forest_exclusion_state
    (compressRoots roots (label z)) (duplicateRaw raw (value z)) u T depth blocked
    value run cap (compressLabels label z) part2 entries2

end PEqualNP.Outside.L_meta_2373.Live1024
