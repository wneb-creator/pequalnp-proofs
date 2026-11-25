import CountVectorClosure
import EntryGateChecker

namespace PEqualNP.Outside.L_meta_2373.CountVector

open Live1024

abbrev CountEntry (m : Nat) := (Fin m → Nat) × Sig

def countColumnReject {m : Nat} (u : Bool) (T : Sig) (total used : Fin m → Nat)
    (signal : Fin m → Sig) (v : Sig) (rows : List (Row × Row)) : Bool :=
  rows.any fun p => rowSeparates u p.1 p.2 T && !(rowSeparates u p.1 p.2 v) &&
    (List.ofFn (fun j : Fin m => j)).all
      (fun j => decide (total j ≤ used j) || !(rowSeparates u p.1 p.2 (signal j)))

lemma countColumnReject_sound {m : Nat} {u T} {total used : Fin m → Nat}
    {signal : Fin m → Sig} {v : Sig} {rows}
    (check : countColumnReject u T total used signal v rows = true) :
    ¬ CountAdmissible total used signal (pairColumn u) (pairColumn u T) v := by
  obtain ⟨p, _, h⟩ := List.any_eq_true.mp check
  have both := Bool.and_eq_true_iff.mp h
  have bits := Bool.and_eq_true_iff.mp both.1
  intro adm
  have value := adm p bits.1 (by
    intro j hj
    have test := List.all_eq_true.mp both.2 j (List.mem_ofFn.mpr ⟨j, rfl⟩)
    rcases Bool.or_eq_true_iff.mp test with inside | outside
    · have le := of_decide_eq_true inside
      omega
    · intro col
      simp only [pairColumn, Set.mem_ofPred_eq] at col
      simp [col] at outside)
  simp only [pairColumn, Set.mem_ofPred_eq] at value
  simp [value] at bits

def countGateCheck {m : Nat} (u : Bool) (T : Sig) (total : Fin m → Nat)
    (signal : Fin m → Sig) (entries cuts : List (CountEntry m))
    (rows : List (Row × Row)) : Bool :=
  entries.all fun e => entries.all fun f => (successorOps u).all fun d =>
    let z := bin d e.2 f.2
    let used := fun j => e.1 j + f.1 j
    if (∀ j, used j ≤ total j) ∧ e.2 ≠ f.2 ∧ z ≠ e.2 ∧ z ≠ f.2 ∧ z ≠ zero ∧ z ≠ one then
      decide ((used, z) ∈ entries) || decide ((used, z) ∈ cuts) ||
        countColumnReject u T total used signal z rows
    else true

lemma countGateCheck_sound {m : Nat} {u T} {total : Fin m → Nat}
    {signal : Fin m → Sig} {entries cuts : List (CountEntry m)} {rows}
    (check : countGateCheck u T total signal entries cuts rows = true) :
    CountClosed total signal (pairColumn u) (pairColumn u T)
      (fun c v => (c, v) ∈ entries) (fun c v => (c, v) ∈ cuts) u := by
  intro ca cb a b d capacity legal distinct freshA freshB hp left right adm
  have outer := List.all_eq_true.mp check (ca, a) left
  have inner := List.all_eq_true.mp outer (cb, b) right
  have gate := List.all_eq_true.mp inner d (successorOps_complete legal)
  have guard : (∀ j, ca j + cb j ≤ total j) ∧ a ≠ b ∧ bin d a b ≠ a ∧ bin d a b ≠ b ∧
      bin d a b ≠ zero ∧ bin d a b ≠ one := ⟨capacity, distinct, freshA, freshB, hp⟩
  dsimp only at gate
  rw [ite_eq_left guard] at gate
  rcases Bool.or_eq_true_iff.mp gate with keptOrCut | rejected
  · rcases Bool.or_eq_true_iff.mp keptOrCut with kept | cut
    · exact Or.inl (of_decide_eq_true kept)
    · exact Or.inr (of_decide_eq_true cut)
  · exact False.elim (countColumnReject_sound rejected adm)

def countLeafCheck {m : Nat} (total : Fin m → Nat) (signal : Fin m → Sig)
    (entries : List (CountEntry m)) : Bool :=
  (List.ofFn (fun j : Fin m => j)).all fun j =>
    if 0 < total j then decide (((fun k => if j = k then 1 else 0), signal j) ∈ entries)
    else true

lemma countLeafCheck_sound {m : Nat} {total : Fin m → Nat} {signal : Fin m → Sig}
    {entries : List (CountEntry m)} (check : countLeafCheck total signal entries = true) :
    ∀ j, 0 < total j → ((fun k => if j = k then 1 else 0), signal j) ∈ entries := by
  intro j hj
  have test := List.all_eq_true.mp check j (List.mem_ofFn.mpr ⟨j, rfl⟩)
  rw [ite_eq_left hj] at test
  exact of_decide_eq_true test

end PEqualNP.Outside.L_meta_2373.CountVector
