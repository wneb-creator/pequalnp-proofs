import PrunedRawCongruence
import EntryGateChecker

namespace PEqualNP.Outside.L_meta_2373.Live1024

lemma pairColumn_rename_mem (f : Row → Row) (u : Bool) (v : Sig) (p : Row × Row) :
    p ∈ pairColumn u (rename f v) ↔ (f p.1, f p.2) ∈ pairColumn u v := by
  simp [pairColumn, rowSeparates, bit_rename]

lemma rename_proper (f : Row → Row) (onto : Function.Surjective f) (v : Sig)
    (p : proper v) : proper (rename f v) := by
  have inj := rename_inj f onto
  obtain ⟨hz, ho⟩ := rename_constants f
  exact ⟨fun h => p.1 (inj (h.trans hz.symm)), fun h => p.2 (inj (h.trans ho.symm))⟩

lemma duplicateRaw_rename {α : Type} (f : Row → Row) (raw : α → Sig) (v : Sig) :
    duplicateRaw (fun r => rename f (raw r)) (rename f v) =
      (fun r => rename f (duplicateRaw raw v r)) := by
  funext r
  cases r <;> rfl

lemma budgetRunCut_rename_pullback {α : Type} [DecidableEq α]
    (f : Row → Row) (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    (fixed : rename f T = T)
    (cut : BudgetRunCut roots (fun r => rename f (raw r)) u T depth) :
    BudgetRunCut roots raw u T depth := by
  intro n cap run
  have moved := restrict_run f run
  have target : restrictRows f (observe T) = observe T := by rw [← observe_rename, fixed]
  rw [target] at moved
  apply cut n cap
  simpa only [List.map_map, Function.comp_def, ← observe_rename] using moved

lemma columnAdmissible_rename {α : Type} [DecidableEq α]
    (f : Row → Row) (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig)
    (fixed : rename f T = T) (A : Finset α) (v : Sig)
    (adm : ColumnAdmissible roots raw (pairColumn u) (pairColumn u T) A v) :
    ColumnAdmissible roots (fun r => rename f (raw r)) (pairColumn u) (pairColumn u T)
      A (rename f v) := by
  intro p hp outside
  have need : (f p.1, f p.2) ∈ pairColumn u T :=
    (pairColumn_rename_mem f u T p).mp (by simpa only [fixed] using hp)
  apply (pairColumn_rename_mem f u v p).mpr
  apply adm _ need
  intro r hr hn member
  exact outside r hr hn ((pairColumn_rename_mem f u (raw r) p).mpr member)

lemma prunedGateClosed_rename_pullback {α : Type} [DecidableEq α]
    (f : Row → Row) (onto : Function.Surjective f) (roots : Finset α) (raw : α → Sig)
    (u : Bool) (T : Sig) (depth : Nat) (fixed : rename f T = T)
    (Cert : Finset α → Sig → Prop)
    (closed : PrunedGateClosed roots (fun r => rename f (raw r))
      (pairColumn u) (pairColumn u T) Cert u T depth) :
    PrunedGateClosed roots raw (pairColumn u) (pairColumn u T)
      (fun A v => Cert A (rename f v)) u T depth := by
  intro A B a b d dis legal distinct freshA freshB good ca cb adm
  have inj := rename_inj f onto
  have old := columnAdmissible_rename f roots raw u T fixed (A ∪ B) (bin d a b) adm
  rw [rename_bin] at old
  have pa : bin d (rename f a) (rename f b) ≠ rename f a := by
    rw [← rename_bin]
    exact fun h => freshA (inj h)
  have pb : bin d (rename f a) (rename f b) ≠ rename f b := by
    rw [← rename_bin]
    exact fun h => freshB (inj h)
  have pg : proper (bin d (rename f a) (rename f b)) := by
    rw [← rename_bin]
    exact rename_proper f onto _ good
  have result := closed A B (rename f a) (rename f b) d dis legal
    (fun h => distinct (inj h)) pa pb pg ca cb old
  rw [← rename_bin] at result
  rcases result with kept | cut
  · exact Or.inl kept
  · rw [duplicateRaw_rename] at cut
    exact Or.inr (budgetRunCut_rename_pullback f _ _ u T depth fixed cut)

lemma prunedBridge_rename_pullback {α : Type} [DecidableEq α]
    (f : Row → Row) (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig)
    (depth : Nat) (fixed : rename f T = T)
    (Cert : Finset α → Sig → Prop) (Cert2 : Finset (Sum α Bool) → Sig → Prop)
    (A : Finset α) (v : Sig)
    (bridge : PrunedBridge roots (fun r => rename f (raw r))
      (pairColumn u) (pairColumn u T) Cert Cert2 u T depth A (rename f v)) :
    PrunedBridge roots raw (pairColumn u) (pairColumn u T)
      (fun B w => Cert B (rename f w)) (fun B w => Cert2 B (rename f w))
      u T depth A v := by
  intro B w member dis adm
  have old := columnAdmissible_rename f _ (duplicateRaw raw v) u T fixed (liftLabels B) w adm
  rw [← duplicateRaw_rename] at old
  rcases bridge B (rename f w) member dis old with kept | cut
  · exact Or.inl kept
  · simp only [duplicateRaw_rename] at cut
    exact Or.inr (budgetRunCut_rename_pullback f _ _ u T depth fixed cut)

theorem prunedNode_rename_pullback (f : Row → Row) (onto : Function.Surjective f)
    (u : Bool) (T : Sig) (targetFixed : rename f T = T) (depth : Nat) :
    ∀ {α : Type} [DecidableEq α] (roots : Finset α) (raw : α → Sig)
      (Cert : Finset α → Sig → Prop),
      PrunedNode (pairColumn u) (pairColumn u T) u T depth α roots
        (fun r => rename f (raw r)) Cert →
      PrunedNode (pairColumn u) (pairColumn u T) u T depth α roots raw
        (fun A v => Cert A (rename f v)) := by
  induction depth with
  | zero =>
    intro α inst roots raw Cert node
    refine ⟨node.1, prunedGateClosed_rename_pullback f onto roots raw u T 0 targetFixed
      Cert node.2.1, ?_, trivial⟩
    intro member
    rw [targetFixed] at member
    exact node.2.2.1 member
  | succ depth ih =>
    intro α inst roots raw Cert node
    refine ⟨node.1, prunedGateClosed_rename_pullback f onto roots raw u T (depth + 1)
      targetFixed Cert node.2.1, ?_, ?_⟩
    · intro member
      rw [targetFixed] at member
      exact node.2.2.1 member
    · intro A v sub good member
      rcases node.2.2.2 A (rename f v) sub (rename_proper f onto v good) member with cut | child
      · rw [duplicateRaw_rename] at cut
        exact Or.inl (budgetRunCut_rename_pullback f _ _ u T depth targetFixed cut)
      · obtain ⟨Cert2, bridge, child⟩ := child
        rw [duplicateRaw_rename] at child
        exact Or.inr ⟨(fun B w => Cert2 B (rename f w)),
          prunedBridge_rename_pullback f roots raw u T depth targetFixed Cert Cert2 A v bridge,
          ih _ _ _ child⟩

end PEqualNP.Outside.L_meta_2373.Live1024
