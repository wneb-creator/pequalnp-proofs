import EntryGateChecker

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem budgetRunCut_of_list {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (labels : List α) (ws : List Sig)
    (nd : labels.Nodup) (basis : labels.toFinset = roots)
    (values : labels.map raw = ws) (u : Bool) (T : Sig) (depth cap : Nat)
    (size : roots.card + depth ≤ cap + 1)
    (blocked : ∀ k, k ≤ cap → ¬ Run u (observe T) k (ws.map observe)) :
    BudgetRunCut roots raw u T depth := by
  have perm : roots.toList.Perm labels := by
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList roots) nd
    simpa using basis.symm
  intro k bound run
  have transferred := Run.perm (perm.map (fun r => observe (raw r))) run
  have target : labels.map (fun r => observe (raw r)) = ws.map observe := by
    rw [← values, List.map_map]
    rfl
  rw [target] at transferred
  exact blocked k (by omega) transferred

def entryLeafCheck {α : Type} [DecidableEq α] (roots : List α) (raw : α → Sig)
    (entries : List (Entry α)) : Bool :=
  roots.all (fun r => decide (({r}, raw r) ∈ entries))

theorem entryLeafCheck_sound {α : Type} [DecidableEq α]
    {roots : List α} {raw : α → Sig} {entries : List (Entry α)}
    (check : entryLeafCheck roots raw entries = true) :
    ∀ r ∈ roots.toFinset, entryCert entries {r} (raw r) := by
  intro r hr
  change ({r}, raw r) ∈ entries
  exact of_decide_eq_true (List.all_eq_true.mp check r (List.mem_toFinset.mp hr))

def entryBridgeCheck {α : Type} [DecidableEq α]
    (u : Bool) (T : Sig) (roots : List (Sum α Bool)) (raw : Sum α Bool → Sig)
    (A : Finset α) (entries : List (Entry α))
    (nextEntries cuts : List (Entry (Sum α Bool))) (rows : List (Row × Row)) : Bool :=
  entries.all fun e => if Disjoint A e.1 then
    decide ((liftLabels e.1, e.2) ∈ nextEntries) ||
      decide ((liftLabels e.1, e.2) ∈ cuts) ||
      columnReject u T roots raw (liftLabels e.1) e.2 rows
    else true

theorem entryBridgeCheck_sound {α : Type} [DecidableEq α]
    {roots : Finset α} {raw : α → Sig} {u T depth} {A : Finset α} {w : Sig}
    {nextRoots : List (Sum α Bool)} {entries : List (Entry α)}
    {nextEntries cuts : List (Entry (Sum α Bool))} {rows}
    (basis : nextRoots.toFinset = duplicateRoots roots A)
    (cutSound : ∀ B v, (B, v) ∈ cuts →
      BudgetRunCut (compressRoots nextRoots.toFinset B) (duplicateRaw (duplicateRaw raw w) v)
        u T depth)
    (check : entryBridgeCheck u T nextRoots (duplicateRaw raw w) A entries
      nextEntries cuts rows = true) :
    PrunedBridge roots raw (pairColumn u) (pairColumn u T) (entryCert entries)
      (entryCert nextEntries) u T depth A w := by
  intro B v member disjoint adm
  have result := List.all_eq_true.mp check (B, v) member
  dsimp only at result
  rw [if_pos disjoint] at result
  rcases Bool.or_eq_true_iff.mp result with keptOrCut | rejected
  · rcases Bool.or_eq_true_iff.mp keptOrCut with kept | cut
    · apply Or.inl
      change (liftLabels B, v) ∈ nextEntries
      exact of_decide_eq_true kept
    · apply Or.inr
      simpa only [basis] using cutSound (liftLabels B) v (of_decide_eq_true cut)
  · apply False.elim
    apply columnReject_sound rejected
    simpa only [basis] using adm

theorem prunedNode_zero_of_checks {α : Type} [DecidableEq α]
    (roots : List α) (raw : α → Sig) (u : Bool) (T : Sig)
    (entries cuts : List (Entry α)) (rows : List (Row × Row))
    (cutSound : ∀ A v, (A, v) ∈ cuts →
      BudgetRunCut (compressRoots roots.toFinset A) (duplicateRaw raw v) u T 0)
    (leaves : entryLeafCheck roots raw entries = true)
    (closed : entryGateCheck u T roots raw entries cuts rows = true)
    (missing : (roots.toFinset, T) ∉ entries) :
    PrunedNode (pairColumn u) (pairColumn u T) u T 0 α roots.toFinset raw
      (entryCert entries) :=
  ⟨entryLeafCheck_sound leaves, entryGateCheck_sound cutSound closed, missing, trivial⟩

end PEqualNP.Outside.L_meta_2373.Live1024
