import PrunedInterface
import SuccessorChecker

namespace PEqualNP.Outside.L_meta_2373.Live1024

def pairColumn (u : Bool) (v : Sig) : Set (Row × Row) :=
  {p | rowSeparates u p.1 p.2 v = true}

def columnReject {α : Type} [DecidableEq α] (u : Bool) (T : Sig)
    (roots : List α) (raw : α → Sig) (A : Finset α) (v : Sig)
    (rows : List (Row × Row)) : Bool :=
  rows.any fun p => rowSeparates u p.1 p.2 T && !(rowSeparates u p.1 p.2 v) &&
    roots.all (fun r => decide (r ∈ A) || !(rowSeparates u p.1 p.2 (raw r)))

theorem columnReject_sound {α : Type} [DecidableEq α] {u T}
    {roots : List α} {raw : α → Sig} {A : Finset α} {v : Sig} {rows}
    (check : columnReject u T roots raw A v rows = true) :
    ¬ ColumnAdmissible roots.toFinset raw (pairColumn u) (pairColumn u T) A v := by
  obtain ⟨p, _, h⟩ := List.any_eq_true.mp check
  have both := Bool.and_eq_true_iff.mp h
  have bits := Bool.and_eq_true_iff.mp both.1
  intro adm
  have value := adm p bits.1 (by
    intro r hr hn
    have test := List.all_eq_true.mp both.2 r (List.mem_toFinset.mp hr)
    rcases Bool.or_eq_true_iff.mp test with inside | outside
    · exact False.elim (hn (of_decide_eq_true inside))
    · intro col
      simp only [pairColumn, Set.mem_ofPred_eq] at col
      simp [col] at outside)
  simp only [pairColumn, Set.mem_ofPred_eq] at value
  simp [value] at bits

abbrev Entry (α : Type) := Finset α × Sig

def entryCert {α : Type} (entries : List (Entry α)) (A : Finset α) (v : Sig) : Prop :=
  (A, v) ∈ entries

def entryGateCheck {α : Type} [DecidableEq α]
    (u : Bool) (T : Sig) (roots : List α) (raw : α → Sig)
    (entries cuts : List (Entry α)) (rows : List (Row × Row)) : Bool :=
  entries.all fun e => entries.all fun f => (successorOps u).all fun d =>
    let z := bin d e.2 f.2
    if Disjoint e.1 f.1 ∧ e.2 ≠ f.2 ∧ z ≠ e.2 ∧ z ≠ f.2 ∧ z ≠ zero ∧ z ≠ one then
      decide ((e.1 ∪ f.1, z) ∈ entries) || decide ((e.1 ∪ f.1, z) ∈ cuts) ||
        columnReject u T roots raw (e.1 ∪ f.1) z rows
    else true

theorem entryGateCheck_sound {α : Type} [DecidableEq α]
    {u T depth} {roots : List α} {raw : α → Sig}
    {entries cuts : List (Entry α)} {rows : List (Row × Row)}
    (cutSound : ∀ A v, (A, v) ∈ cuts →
      BudgetRunCut (compressRoots roots.toFinset A) (duplicateRaw raw v) u T depth)
    (check : entryGateCheck u T roots raw entries cuts rows = true) :
    PrunedGateClosed roots.toFinset raw (pairColumn u) (pairColumn u T)
      (entryCert entries) u T depth := by
  intro A B a b d disjoint legal distinct freshA freshB hp left right adm
  have outer := List.all_eq_true.mp check (A, a) left
  have inner := List.all_eq_true.mp outer (B, b) right
  have gate := List.all_eq_true.mp inner d (successorOps_complete legal)
  have guard : Disjoint A B ∧ a ≠ b ∧ bin d a b ≠ a ∧ bin d a b ≠ b ∧
      bin d a b ≠ zero ∧ bin d a b ≠ one := ⟨disjoint, distinct, freshA, freshB, hp⟩
  dsimp only at gate
  rw [if_pos guard] at gate
  rcases Bool.or_eq_true_iff.mp gate with keptOrCut | rejected
  · rcases Bool.or_eq_true_iff.mp keptOrCut with kept | cut
    · apply Or.inl
      change (A ∪ B, bin d a b) ∈ entries
      exact of_decide_eq_true kept
    · exact Or.inr (cutSound _ _ (of_decide_eq_true cut))
  · exact False.elim (columnReject_sound rejected adm)

end PEqualNP.Outside.L_meta_2373.Live1024
