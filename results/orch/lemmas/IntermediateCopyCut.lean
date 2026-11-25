import IndexedForest

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem first_copy_run {u : Bool} {T a b : Sig} {k d : Nat} {U : Finset Sig}
    (tail : Live u T k (insert (bin d a b) U)) (hd : allowed u d)
    (hb : b ∈ U) (fresh : bin d a b ∉ U) :
    Run u (observe T) (k + 1)
      ((insert (bin d a b) U).toList.map
        (fun v => observe (if v = bin d a b then a else v))) := by
  classical
  let z := bin d a b
  let value : Sig → Sig := fun v => if v = z then a else v
  let rest := (U.erase b).toList
  let vs := z :: b :: rest
  have bz : b ≠ z := by
    intro h
    exact fresh (Eq.mp (congrArg (fun v : Sig => v ∈ U) h) hb)
  have zr : z ∉ rest := by
    simpa only [rest, Finset.mem_toList, Finset.mem_erase, not_and] using
      (fun _ h => fresh h)
  have br : b ∉ rest := by simp [rest]
  have restnd : rest.Nodup := Finset.nodup_toList _
  have nd : vs.Nodup := by simp [vs, Ne.symm bz, zr, br, restnd]
  have eqv : vs.toFinset = insert z U := by
    simp [vs, rest, Finset.insert_erase hb]
  have progress := list_run tail vs nd eqv
  have finish : Run u (observe T) (k + 1)
      (observe a :: observe b :: rest.map observe) :=
    Run.two d hd false true (by simpa [vs, kept, z, obs_bin] using progress)
  have untouched (v : Sig) (hv : v ∈ U) : value v = v := by
    have vz : v ≠ z := by
      intro h
      exact fresh (Eq.mp (congrArg (fun v : Sig => v ∈ U) h) hv)
    simp [value, vz]
  have mappedRest : rest.map (fun v => observe (value v)) = rest.map observe := by
    apply List.map_congr_left
    intro v hv
    rw [untouched v (Finset.mem_erase.mp (Finset.mem_toList.mp hv)).2]
  have source : Run u (observe T) (k + 1)
      (vs.map (fun v => observe (value v))) := by
    simpa only [vs, List.map_cons, show value z = a by simp [value],
      untouched b hb, mappedRest] using finish
  have perm : vs.Perm (insert z U).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq nd (Finset.nodup_toList _)
    simpa using eqv
  exact Run.perm (perm.map (fun v => observe (value v))) source

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

def copyInputLabels {α : Type} [DecidableEq α] (label : Sig → Finset α)
    (a z v : Sig) : Finset (Sum α Bool) :=
  if v = z then {Sum.inr true}
  else if v = a then {Sum.inr false} else liftLabels (label v)

theorem copy_input_partition {α : Type} [DecidableEq α]
    (roots : Finset α) (S : Finset Sig) (label : Sig → Finset α)
    (a z : Sig) (part : LabelPartition roots S label)
    (ha : a ∈ S) (fresh : z ∉ S) :
    LabelPartition (duplicateRoots roots (label a)) (insert z S)
      (copyInputLabels label a z) := by
  classical
  let next := copyInputLabels label a z
  have anz : a ≠ z := by rintro rfl; exact fresh ha
  have leftMem (v : Sig) (r : α) : Sum.inl r ∈ next v ↔
      v ≠ z ∧ v ≠ a ∧ r ∈ label v := by
    by_cases vz : v = z <;> by_cases va : v = a <;>
      simp [next, copyInputLabels, liftLabels, vz, va, anz]
  have falseMem (v : Sig) : Sum.inr false ∈ next v ↔ v ≠ z ∧ v = a := by
    by_cases vz : v = z <;> by_cases va : v = a <;>
      simp [next, copyInputLabels, liftLabels, vz, va, anz]
  have trueMem (v : Sig) : Sum.inr true ∈ next v ↔ v = z := by
    by_cases vz : v = z <;> by_cases va : v = a <;>
      simp [next, copyInputLabels, liftLabels, vz, va, anz]
  change LabelPartition (duplicateRoots roots (label a)) (insert z S) next
  refine ⟨?_, ?_, ?_⟩
  · intro v hv q hq
    cases q with
    | inl r =>
      obtain ⟨vz, va, hr⟩ := (leftMem v r).mp hq
      have hvS := (Finset.mem_insert.mp hv).resolve_left vz
      have rRoot := part.1 v hvS hr
      have notA : r ∉ label a := fun h =>
        Finset.disjoint_left.mp (part.2.1 v hvS a ha va) hr h
      simp [duplicateRoots, liftLabels, rRoot, notA]
    | inr bit => cases bit <;> simp [duplicateRoots]
  · intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro q hqv hqw
    cases q with
    | inl r =>
      obtain ⟨vz, _, hrv⟩ := (leftMem v r).mp hqv
      obtain ⟨wz, _, hrw⟩ := (leftMem w r).mp hqw
      exact Finset.disjoint_left.mp
        (part.2.1 v ((Finset.mem_insert.mp hv).resolve_left vz)
          w ((Finset.mem_insert.mp hw).resolve_left wz) hne) hrv hrw
    | inr bit =>
      cases bit with
      | false => exact hne (((falseMem v).mp hqv).2.trans ((falseMem w).mp hqw).2.symm)
      | true => exact hne (((trueMem v).mp hqv).trans ((trueMem w).mp hqw).symm)
  · intro q hq
    cases q with
    | inl r =>
      have hr : r ∈ roots ∧ r ∉ label a := by
        simpa [duplicateRoots, liftLabels] using hq
      obtain ⟨v, hv, hrv⟩ := part.2.2 r hr.1
      have vz : v ≠ z := by rintro rfl; exact fresh hv
      have va : v ≠ a := by rintro rfl; exact hr.2 hrv
      exact ⟨v, Finset.mem_insert_of_mem hv, (leftMem v r).mpr ⟨vz, va, hrv⟩⟩
    | inr bit =>
      cases bit with
      | false => exact ⟨a, Finset.mem_insert_of_mem ha, (falseMem a).mpr ⟨anz, rfl⟩⟩
      | true => exact ⟨z, Finset.mem_insert_self _ _, (trueMem z).mpr rfl⟩

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem copy_input_readOnce {α : Type} [DecidableEq α]
    (raw : α → Sig) (u : Bool) (S : Finset Sig) (label : Sig → Finset α) (a z : Sig)
    (fresh : z ∉ S) (entries : ∀ v ∈ S, ReadOnce raw u (label v) v) :
    ∀ v ∈ insert z S,
      ReadOnce (duplicateRaw raw a) u (copyInputLabels label a z v)
        (if v = z then a else v) := by
  intro v hv
  by_cases hvz : v = z
  · subst v
    simpa [copyInputLabels, duplicateRaw] using
      ReadOnce.leaf (duplicateRaw raw a) u (Sum.inr true)
  · have hvS : v ∈ S := (Finset.mem_insert.mp hv).resolve_left hvz
    by_cases hva : v = a
    · subst v
      simpa [copyInputLabels, hvz, duplicateRaw] using
        ReadOnce.leaf (duplicateRaw raw a) u (Sum.inr false)
    · have mapped := ReadOnce.map raw (duplicateRaw raw a) u Sum.inl
        (by intro x y h; cases h; rfl) (by intro r; rfl) (entries v hvS)
      simpa [copyInputLabels, hvz, hva, liftLabels] using mapped

theorem first_copy_forest_exclusion {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    {k d : Nat} {U : Finset Sig} {a b : Sig}
    (tail : Live u T k (insert (bin d a b) U)) (hd : allowed u d)
    (ha : a ∈ U) (hb : b ∈ U) (fresh : bin d a b ∉ U)
    (cap : k + 1 ≤ U.card + depth)
    (label : Sig → Finset α) (part : LabelPartition roots U label)
    (entries : ∀ v ∈ U, ReadOnce raw u (label v) v)
    (blocked : ∀ n, n + 1 ≤ (duplicateRoots roots (label a)).card + depth →
      ¬ Run u (observe T) n
        ((duplicateRoots roots (label a)).toList.map
          (fun r => observe (duplicateRaw raw a r)))) : False := by
  have part2 := copy_input_partition roots U label a (bin d a b) part ha fresh
  have entries2 := copy_input_readOnce raw u U label a (bin d a b) fresh entries
  have run := first_copy_run tail hd hb fresh
  apply readOnce_indexed_forest_exclusion_state
    (duplicateRoots roots (label a)) (duplicateRaw raw a) u T depth blocked
    (fun v => if v = bin d a b then a else v) run ?_
    (copyInputLabels label a (bin d a b)) part2 entries2
  rw [Finset.card_insert_of_notMem fresh]
  omega

end PEqualNP.Outside.L_meta_2373.Live1024
