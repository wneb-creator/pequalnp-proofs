import Mathlib
import PEqualNP.Library.Evasion.MTrans
import PEqualNP.MetaComplexity.Helpers.Machines.Zip

namespace AdjacentScan

open Turing PEqualNP.Library PEqualNP.Library.Evasion PEqualNP.Library.Machines
open PEqualNP.MetaComplexity.Helpers.Machines

abbrev Symbol := Bool ⊕ Bool
abbrev Row := List Bool × Bool
abbrev Zipped := Option Symbol × Option Symbol

def encodeRow (row : Row) : List Symbol := row.1.map Sum.inl ++ [Sum.inr row.2]
def encodeRows (rows : List Row) : List Symbol := rows.flatMap encodeRow

def dropFirst : List Symbol → List Symbol
  | [] => []
  | .inl _ :: rest => dropFirst rest
  | .inr _ :: rest => rest

lemma dropFirst_length (symbols : List Symbol) : (dropFirst symbols).length ≤ symbols.length := by
  induction symbols with
  | nil => simp [dropFirst]
  | cons symbol rest ih =>
    cases symbol with
    | inl bit => simp only [dropFirst, List.length_cons]; omega
    | inr bit => simp [dropFirst]

lemma dropFirst_row (row : Row) (rest : List Symbol) :
    dropFirst (encodeRow row ++ rest) = rest := by
  obtain ⟨bits, value⟩ := row
  induction bits with
  | nil => simp [encodeRow, dropFirst]
  | cons bit bits ih => simpa [encodeRow, dropFirst] using ih

lemma dropFirst_rows (rows : List Row) : dropFirst (encodeRows rows) = encodeRows rows.tail := by
  cases rows with
  | nil => rfl
  | cons row rows => simpa [encodeRows] using dropFirst_row row (encodeRows rows)

def shiftStep : Bool → Symbol ⊕ Symbol → Bool × Option (Symbol ⊕ Symbol) × Option (Symbol ⊕ Symbol)
  | state, .inl x => (state, some (.inl x), none)
  | false, .inr (.inl _) => (false, none, none)
  | false, .inr (.inr _) => (true, none, none)
  | true, .inr x => (true, some (.inr x), none)

lemma shift_right_true (symbols : List Symbol) :
    fstRun2 shiftStep (fun _ => none) true (symbols.map Sum.inr) = symbols.map Sum.inr := by
  induction symbols with
  | nil => rfl
  | cons symbol rest ih => simp [fstRun2, shiftStep, ih]

lemma shift_right_false (symbols : List Symbol) :
    fstRun2 shiftStep (fun _ => none) false (symbols.map Sum.inr) =
      (dropFirst symbols).map Sum.inr := by
  induction symbols with
  | nil => rfl
  | cons symbol rest ih => cases symbol <;> simp [fstRun2, shiftStep, dropFirst, ih, shift_right_true]

lemma shift_run (x y : List Symbol) :
    fstRun2 shiftStep (fun _ => none) false (Gen.gpair (x, y)) =
      Gen.gpair (x, dropFirst y) := by
  induction x with
  | nil => simpa [Gen.gpair] using shift_right_false y
  | cons symbol rest ih => simpa [Gen.gpair, fstRun2, shiftStep] using ih

lemma duplicate_time : ComputableInTime (fun x : List Symbol => x) Gen.gpair
    (fun x => (x, x)) (fun n => 4 * n + 4) := by
  apply tp_time _ _ _ (fun x => some (Sum.inl x)) (fun x => some (Sum.inr x)) (.inl (.inl false))
  intro x
  simp [Gen.gpair]

lemma shift_time : ComputableInTime Gen.gpair Gen.gpair
    (fun p : List Symbol × List Symbol => (p.1, dropFirst p.2)) (fun n => 3 * n + 3) := by
  exact time_mono (fst2_time _ _ _ shiftStep (fun _ => none) false (.inl (.inl false))
    (fun p => (shift_run p.1 p.2).symm)) (by intro n; omega)

lemma shifted_pair_time : ∃ C, ComputableInTime (fun x : List Symbol => x) Gen.gpair
    (fun x => (x, dropFirst x)) (fun n => C * n + C) := by
  apply lin_comp (D := 2) duplicate_time shift_time
  intro x
  simp [Gen.gpair]
  omega

lemma zip_time : ComputableInTime Gen.gpair (fun x : List Zipped => x)
    (fun p : List Symbol × List Symbol => List.zipWithAll Prod.mk p.1 p.2)
    (fun n => 5 * n + 5) := by
  refine ⟨{
    tm := Zip.zM Symbol Symbol
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun n => 4 * n + 5
    outputsFun := fun p => {
      steps := Classical.choose (Zip.zip_run p)
      evals_in_steps := ?_
      steps_le_m := (Classical.choose_spec (Zip.zip_run p)).1 }
  }, fun n => by change 4 * n + 5 ≤ 5 * n + 5; omega⟩
  have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l := fun γ l => by simp
  exact (congrArg (fun x => Zip.zStep^[Classical.choose (Zip.zip_run p)]
    (some (initList (Zip.zM Symbol Symbol) x))) (hm _ (Gen.gpair (p.1, p.2)))).trans
    ((Classical.choose_spec (Zip.zip_run p)).2.trans
      (congrArg (fun x => some (haltList (Zip.zM Symbol Symbol) x))
        (hm _ (List.zipWithAll Prod.mk p.1 p.2)).symm))

abbrev State := Bool × Bool

def scanStep (state : State) : Zipped → State
  | (some (.inl a), some (.inl b)) => (state.1 && decide (a = b), state.2)
  | (some (.inr a), some (.inr b)) => (true, state.2 && (!state.1 || decide (a = b)))
  | (some _, none) => state
  | _ => (false, false)

def scanFrom : State → List Zipped → Bool
  | state, [] => state.2
  | state, pair :: rest => scanFrom (scanStep state pair) rest

def scan (pairs : List Zipped) : Bool := scanFrom (true, true) pairs

lemma scan_run (pairs : List Zipped) (state : State) :
    fstRun2 (fun q a => (scanStep q a, none, none)) (fun q => some q.2) state pairs =
      [scanFrom state pairs] := by
  induction pairs generalizing state with
  | nil => rfl
  | cons pair rest ih => simp [fstRun2, scanFrom, ih]

lemma scan_time : ComputableInTime (fun x : List Zipped => x) Computability.encodeBool scan
    (fun n => 3 * n + 3) := by
  apply time_mono (fst2_time _ _ _ (fun q a => (scanStep q a, none, none))
    (fun q => some q.2) (true, true) false (fun p => (scan_run p (true, true)).symm))
  intro n
  omega

def consistent (symbols : List Symbol) : Bool :=
  scan (List.zipWithAll Prod.mk symbols (dropFirst symbols))

lemma consistent_time : ∃ C, ComputableInTime (fun x : List Symbol => x)
    Computability.encodeBool consistent (fun n => C * n + C) := by
  obtain ⟨C, hC⟩ := shifted_pair_time
  obtain ⟨D, hD⟩ := lin_comp (D := 2) hC zip_time (by
    intro x
    simp only [Gen.gpair_length]
    have h := dropFirst_length x
    omega)
  obtain ⟨E, hE⟩ := lin_comp (D := 1) hD scan_time (by
    intro x
    rw [Zip.zip_length]
    have h := dropFirst_length x
    change max x.length (dropFirst x).length ≤ 1 * x.length + 1
    omega)
  exact ⟨E, hE⟩

lemma scan_unpaired (symbols : List Symbol) (state : State) :
    scanFrom state (List.zipWithAll Prod.mk symbols []) = state.2 := by
  induction symbols with
  | nil => rfl
  | cons symbol rest ih => simpa [scanFrom, scanStep] using ih

lemma scan_row_pair (left right : Row) (hl : left.1.length = right.1.length)
    (xs ys : List Symbol) (eqFlag good : Bool) :
    scanFrom (eqFlag, good)
      (List.zipWithAll Prod.mk (encodeRow left ++ xs) (encodeRow right ++ ys)) =
    scanFrom (true, good && (!(eqFlag && decide (left.1 = right.1)) || decide (left.2 = right.2)))
      (List.zipWithAll Prod.mk xs ys) := by
  obtain ⟨a, av⟩ := left
  obtain ⟨b, bv⟩ := right
  induction a generalizing b eqFlag with
  | nil =>
    have hb : b = [] := List.length_eq_zero_iff.mp hl.symm
    subst b
    simp [encodeRow, scanFrom, scanStep]
  | cons bit bits ih =>
    cases b with
    | nil => simp at hl
    | cons bit' bits' =>
      have hlen : bits.length = bits'.length := by simpa using hl
      simp only [encodeRow, List.map_cons, List.cons_append, List.zipWithAll_cons_cons,
        scanFrom, scanStep]
      have h := ih (b := bits') (eqFlag := eqFlag && decide (bit = bit')) hlen
      simpa [encodeRow, Bool.and_assoc] using h

def allAdjacent : List Row → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (!decide (a.1 = b.1) || decide (a.2 = b.2)) && allAdjacent (b :: rest)

lemma scan_rows (rows : List Row) (width : ℕ) (hw : ∀ row ∈ rows, row.1.length = width)
    (good : Bool) :
    scanFrom (true, good) (List.zipWithAll Prod.mk (encodeRows rows) (encodeRows rows.tail)) =
      (good && allAdjacent rows) := by
  induction rows generalizing good with
  | nil => simp [encodeRows, scanFrom, allAdjacent]
  | cons a rows ih =>
    cases rows with
    | nil => simpa only [encodeRows, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.tail_cons, allAdjacent, Bool.and_true] using scan_unpaired (encodeRow a) (true, good)
    | cons b rest =>
      have hab : a.1.length = b.1.length := (hw a (by simp)).trans (hw b (by simp)).symm
      have hrest : ∀ row ∈ b :: rest, row.1.length = width := by
        intro row hr
        exact hw row (by simp [hr])
      have hrow := scan_row_pair a b hab (encodeRows (b :: rest)) (encodeRows rest) true good
      have h := ih hrest (good && (!decide (a.1 = b.1) || decide (a.2 = b.2)))
      simpa [encodeRows, allAdjacent, Bool.and_assoc] using
        hrow.trans (by simpa [encodeRows, Bool.and_assoc] using h)

def agree (a b : Row) : Prop := a.1 = b.1 → a.2 = b.2

lemma allAdjacent_iff (rows : List Row) : allAdjacent rows = true ↔ rows.IsChain agree := by
  induction rows with
  | nil => simp [allAdjacent]
  | cons a rows ih =>
    cases rows with
    | nil => simp [allAdjacent]
    | cons b rest => simp [allAdjacent, List.isChain_cons_cons, ← ih, agree, or_iff_not_imp_left]

theorem consistent_correct (rows : List Row) (width : ℕ)
    (hw : ∀ row ∈ rows, row.1.length = width) :
    consistent (encodeRows rows) = true ↔ rows.IsChain agree := by
  have h := scan_rows rows width hw true
  simp only [Bool.true_and] at h
  rw [consistent, scan, dropFirst_rows, h]
  exact allAdjacent_iff rows

end AdjacentScan
