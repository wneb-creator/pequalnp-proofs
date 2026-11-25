import State4ReadOnceForest

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem Run.substitute_indexed {ι R : Type} {u : Bool} {target : Wire R}
    (xs : List ι) (value : ι → Wire R) (leaves : ι → List (Wire R)) (cost : ι → Nat)
    (traces : ∀ i ∈ xs, Run u (value i) (cost i) (leaves i))
    {rest : List (Wire R)} {k : Nat} (tail : Run u target k (xs.map value ++ rest)) :
    Run u target ((xs.map cost).sum + k) (xs.flatMap leaves ++ rest) := by
  induction xs generalizing rest k with
  | nil => simpa using tail
  | cons i xs ih =>
    have perm : ((i :: xs).map value ++ rest).Perm (xs.map value ++ value i :: rest) := by
      have small : ([value i] ++ xs.map value).Perm (xs.map value ++ [value i]) :=
        List.perm_append_comm
      simpa only [List.map_cons, List.cons_append, List.nil_append, List.append_assoc] using
        small.append_right rest
    have shifted := Run.perm perm tail
    have expanded := ih (fun j hj => traces j (List.mem_cons_of_mem i hj)) shifted
    have permBack : (xs.flatMap leaves ++ value i :: rest).Perm
        (value i :: (xs.flatMap leaves ++ rest)) := by
      have small : (xs.flatMap leaves ++ [value i]).Perm ([value i] ++ xs.flatMap leaves) :=
        List.perm_append_comm
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using
        small.append_right rest
    have atHead := Run.perm permBack expanded
    have result := Run.substitute (traces i (by simp)) atHead
    simpa only [List.map_cons, List.sum_cons, List.flatMap_cons, List.append_assoc,
      Nat.add_assoc] using result

theorem readOnce_indexed_forest_run {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig)
    {k : Nat} {S : Finset Sig} (value : Sig → Sig)
    (run : Run u (observe T) k (S.toList.map (fun v => observe (value v))))
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) (value v)) :
    Run u (observe T) (k + roots.card - S.card)
      (roots.toList.map (fun r => observe (raw r))) := by
  classical
  let leaves (v : Sig) := (label v).toList.map (fun r => observe (raw r))
  let cost (v : Sig) := (label v).card - 1
  have traces : ∀ v ∈ S.toList, Run u (observe (value v)) (cost v) (leaves v) := by
    intro v hv
    exact (entries v (Finset.mem_toList.mp hv)).2
  have expanded := Run.substitute_indexed S.toList (fun v => observe (value v)) leaves cost traces
    (rest := []) (by simpa only [List.append_nil] using run)
  have flat : S.toList.flatMap leaves =
      (S.toList.flatMap (fun v => (label v).toList)).map (fun r => observe (raw r)) := by
    simp only [leaves, List.map_flatMap]
  have expanded' : Run u (observe T)
      ((S.toList.map (fun v => (label v).card - 1)).sum + k)
      ((S.toList.flatMap (fun v => (label v).toList)).map (fun r => observe (raw r))) := by
    simpa only [List.append_nil, cost, flat] using expanded
  have moved := Run.perm
    ((partition_flatMap_perm roots S label part).map (fun r => observe (raw r))) expanded'
  have count := partition_cost_sum roots S label part (fun v hv => (entries v hv).1)
  have costEq : (S.toList.map (fun v => (label v).card - 1)).sum + k =
      k + roots.card - S.card := by omega
  simpa only [costEq] using moved

theorem readOnce_indexed_forest_exclusion_state {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    (blocked : ∀ n, n + 1 ≤ roots.card + depth →
      ¬ Run u (observe T) n (roots.toList.map (fun r => observe (raw r))))
    {k : Nat} {S : Finset Sig} (value : Sig → Sig)
    (run : Run u (observe T) k (S.toList.map (fun v => observe (value v))))
    (cap : k + 1 ≤ S.card + depth)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) (value v)) : False := by
  have count := partition_cost_sum roots S label part (fun v hv => (entries v hv).1)
  exact blocked (k + roots.card - S.card) (by omega)
    (readOnce_indexed_forest_run roots raw u T value run label part entries)

end PEqualNP.Outside.L_meta_2373.Live1024
