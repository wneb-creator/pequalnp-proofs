import Mathlib
import PEqualNP.Library.Evasion.MTrans

namespace RadixPass

open PEqualNP.Library PEqualNP.Library.Evasion PEqualNP.Library.Machines

abbrev Symbol := Bool ⊕ Bool
abbrev Row := List Bool × Bool

def annotateStep : Option Bool → Symbol → Option Bool × Option (Bool × Symbol) × Option (Bool × Symbol)
  | none, .inl b => (some b, none, none)
  | some head, .inl b => (some head, some (head, .inl b), none)
  | some head, .inr value => (none, some (head, .inl head), some (head, .inr value))
  | none, .inr value => (none, some (false, .inr value), none)

def annotate (symbols : List Symbol) : List (Bool × Symbol) :=
  fstRun2 annotateStep (fun _ => none) none symbols

def chooseTag (wanted : Bool) (entry : Bool × Symbol) : Option Symbol :=
  if entry.1 = wanted then some entry.2 else none

def partitionTags (symbols : List (Bool × Symbol)) : List Symbol :=
  symbols.filterMap (chooseTag false) ++ symbols.filterMap (chooseTag true)

def radixPass (symbols : List Symbol) : List Symbol := partitionTags (annotate symbols)

lemma annotate_length_aux (symbols : List Symbol) (state : Option Bool) :
    (fstRun2 annotateStep (fun _ => none) state symbols).length ≤
      symbols.length + (if state.isSome then 1 else 0) := by
  induction symbols generalizing state with
  | nil => simp [fstRun2]
  | cons symbol symbols ih =>
    cases state with
    | none =>
      cases symbol with
      | inl b => simpa [fstRun2, annotateStep] using ih (some b)
      | inr value => simpa [fstRun2, annotateStep] using ih none
    | some head =>
      cases symbol with
      | inl b =>
        have h := ih (some head)
        simp at h
        simp [fstRun2, annotateStep]
        omega
      | inr value =>
        have h := ih none
        simp at h
        simp [fstRun2, annotateStep]
        omega

lemma annotate_length (symbols : List Symbol) : (annotate symbols).length ≤ symbols.length := by
  simpa [annotate] using annotate_length_aux symbols none

lemma partition_length (symbols : List (Bool × Symbol)) :
    (partitionTags symbols).length = symbols.length := by
  induction symbols with
  | nil => rfl
  | cons entry symbols ih =>
    obtain ⟨tag, symbol⟩ := entry
    cases tag <;> simp [partitionTags, chooseTag] at ih ⊢ <;> omega

lemma pass_length (symbols : List Symbol) : (radixPass symbols).length ≤ symbols.length := by
  rw [radixPass, partition_length]
  exact annotate_length symbols

lemma annotate_time : ComputableInTime (fun symbols : List Symbol => symbols)
    (fun symbols : List (Bool × Symbol) => symbols) annotate (fun n => 3 * n + 3) := by
  have h := fst2_time (fun symbols : List Symbol => symbols)
    (fun symbols : List (Bool × Symbol) => symbols) annotate
    annotateStep (fun _ => none) none (false, Sum.inl false) (fun _ => rfl)
  exact time_mono h (by intro n; omega)

lemma partition_time : ComputableInTime (fun symbols : List (Bool × Symbol) => symbols)
    (fun symbols : List Symbol => symbols) partitionTags (fun n => 4 * n + 4) :=
  tp_time _ _ _ (chooseTag false) (chooseTag true) (Sum.inl false) (fun _ => rfl)

lemma pass_time : ∃ C : ℕ, ComputableInTime (fun symbols : List Symbol => symbols)
    (fun symbols : List Symbol => symbols) radixPass (fun n => C * n + C) := by
  obtain ⟨C, hC⟩ := lin_comp (D := 1) annotate_time partition_time (by
    intro symbols
    simpa using (annotate_length symbols).trans (Nat.le_add_right _ 1))
  exact ⟨C, hC⟩

def encodeRow (row : Row) : List Symbol := row.1.map Sum.inl ++ [Sum.inr row.2]

def encodeRows (rows : List Row) : List Symbol := rows.flatMap encodeRow

def rotate (row : Row) : Row :=
  match row.1 with
  | [] => row
  | head :: rest => (rest ++ [head], row.2)

def bucket (row : Row) : Bool := row.1.headD false

lemma annotate_body (bits : List Bool) (head value : Bool) (suffix : List Symbol) :
    fstRun2 annotateStep (fun _ => none) (some head)
      (bits.map Sum.inl ++ Sum.inr value :: suffix) =
      ((bits ++ [head]).map (fun b => (head, Sum.inl b))) ++
        (head, Sum.inr value) :: annotate suffix := by
  induction bits with
  | nil => simp [fstRun2, annotateStep, annotate]
  | cons b bits ih => simp [fstRun2, annotateStep, ih]

lemma annotate_row (head value : Bool) (rest : List Bool) (suffix : List Symbol) :
    annotate (encodeRow (head :: rest, value) ++ suffix) =
      (encodeRow (rest ++ [head], value)).map (fun symbol => (head, symbol)) ++ annotate suffix := by
  simpa [annotate, encodeRow, fstRun2, annotateStep, List.append_assoc, Function.comp_def] using
    annotate_body rest head value suffix

lemma annotate_rows (rows : List Row) (hne : ∀ row ∈ rows, row.1 ≠ []) :
    annotate (encodeRows rows) = rows.flatMap
      (fun row => (encodeRow (rotate row)).map (fun symbol => (bucket row, symbol))) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨bits, value⟩ := row
    cases bits with
    | nil => exact False.elim (hne ([], value) (by simp) rfl)
    | cons head rest =>
      simpa [encodeRows, rotate, bucket, annotate_row] using
        congrArg ((encodeRow (rest ++ [head], value)).map (fun symbol => (head, symbol)) ++ ·)
          (ih (by intro row hr; exact hne row (by simp [hr])))

lemma filter_tagged (symbols : List Symbol) (tag wanted : Bool) :
    (symbols.map (fun symbol => (tag, symbol))).filterMap (chooseTag wanted) =
      if tag = wanted then symbols else [] := by
  by_cases h : tag = wanted <;>
    simp [List.filterMap_map, Function.comp_def, chooseTag, h]

lemma filter_tagged_rows (rows : List Row) (wanted : Bool) :
    (rows.flatMap (fun row =>
      (encodeRow (rotate row)).map (fun symbol => (bucket row, symbol)))).filterMap (chooseTag wanted) =
      encodeRows ((rows.filter (fun row => bucket row == wanted)).map rotate) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    by_cases h : bucket row = wanted <;>
      simp [List.filterMap_append, h, ih, encodeRows, chooseTag, Function.comp_def]

lemma pass_correct (rows : List Row) (hne : ∀ row ∈ rows, row.1 ≠ []) :
    radixPass (encodeRows rows) =
      encodeRows (((rows.filter (fun row => bucket row == false)).map rotate) ++
        ((rows.filter (fun row => bucket row == true)).map rotate)) := by
  simp only [radixPass, partitionTags, annotate_rows rows hne]
  rw [filter_tagged_rows, filter_tagged_rows]
  simp [encodeRows]

def symbolBits : Symbol → List Bool
  | .inl b => [false, b]
  | .inr b => [true, b]

def encodeSymbols (symbols : List Symbol) : List Bool := symbols.flatMap symbolBits

def encodeStep (_ : Unit) : Symbol → Unit × Option Bool × Option Bool
  | .inl b => ((), some false, some b)
  | .inr b => ((), some true, some b)

lemma encode_run (symbols : List Symbol) :
    encodeSymbols symbols = fstRun2 encodeStep (fun _ => none) () symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols ih =>
    simp only [encodeSymbols] at ih
    cases symbol <;> simp [encodeSymbols, symbolBits, fstRun2, encodeStep, ih]

lemma encode_length (symbols : List Symbol) : (encodeSymbols symbols).length = 2 * symbols.length := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols ih => cases symbol <;> simp [encodeSymbols, symbolBits] at ih ⊢ <;> omega

def decodeSymbols : List Bool → List Symbol
  | tag :: bit :: rest => (if tag then Sum.inr bit else Sum.inl bit) :: decodeSymbols rest
  | _ => []

def decodeStep : Option Bool → Bool → Option Bool × Option Symbol × Option Symbol
  | none, tag => (some tag, none, none)
  | some tag, bit => (none, some (if tag then Sum.inr bit else Sum.inl bit), none)

lemma decode_run : ∀ bits : List Bool,
    decodeSymbols bits = fstRun2 decodeStep (fun _ => none) none bits
  | [] => rfl
  | [_] => rfl
  | tag :: bit :: rest => by simp [decodeSymbols, fstRun2, decodeStep, decode_run rest]

lemma decode_length : ∀ bits : List Bool, 2 * (decodeSymbols bits).length ≤ bits.length
  | [] => by simp [decodeSymbols]
  | [_] => by simp [decodeSymbols]
  | tag :: bit :: rest => by
      have h := decode_length rest
      simp [decodeSymbols]
      omega

lemma decode_encode (symbols : List Symbol) : decodeSymbols (encodeSymbols symbols) = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols ih =>
    cases symbol with
    | inl b => simpa [encodeSymbols, symbolBits, decodeSymbols] using congrArg (List.cons (Sum.inl b)) ih
    | inr b => simpa [encodeSymbols, symbolBits, decodeSymbols] using congrArg (List.cons (Sum.inr b)) ih

lemma encode_time : ComputableInTime (fun symbols : List Symbol => symbols)
    (fun bits : List Bool => bits) encodeSymbols (fun n => 3 * n + 3) := by
  have h := fst2_time (fun symbols : List Symbol => symbols) (fun bits : List Bool => bits)
    encodeSymbols encodeStep (fun _ => none) () false encode_run
  exact time_mono h (by intro n; omega)

lemma decode_time : ComputableInTime (fun bits : List Bool => bits)
    (fun symbols : List Symbol => symbols) decodeSymbols (fun n => 3 * n + 3) := by
  have h := fst2_time (fun bits : List Bool => bits) (fun symbols : List Symbol => symbols)
    decodeSymbols decodeStep (fun _ => none) none (Sum.inl false) decode_run
  exact time_mono h (by intro n; omega)

def binaryPass (bits : List Bool) : List Bool := encodeSymbols (radixPass (decodeSymbols bits))

lemma binaryPass_length (bits : List Bool) : (binaryPass bits).length ≤ bits.length := by
  calc
    (binaryPass bits).length = 2 * (radixPass (decodeSymbols bits)).length := encode_length _
    _ ≤ 2 * (decodeSymbols bits).length := Nat.mul_le_mul_left _ (pass_length _)
    _ ≤ bits.length := decode_length bits

lemma binaryPass_time : ∃ C : ℕ, ComputableInTime (fun bits : List Bool => bits)
    (fun bits : List Bool => bits) binaryPass (fun n => C * n + C) := by
  obtain ⟨CP, hp⟩ := pass_time
  obtain ⟨CD, hd⟩ := lin_comp (D := 1) decode_time hp (by
    intro bits
    have h := decode_length bits
    omega)
  obtain ⟨C, hc⟩ := lin_comp (D := 1) hd encode_time (by
    intro bits
    have hdlen : (decodeSymbols bits).length ≤ bits.length := by
      have h := decode_length bits
      omega
    have h := (pass_length (decodeSymbols bits)).trans hdlen
    simpa using h.trans (Nat.le_add_right _ 1))
  exact ⟨C, hc⟩

lemma binaryPass_correct (symbols : List Symbol) :
    binaryPass (encodeSymbols symbols) = encodeSymbols (radixPass symbols) := by
  simp [binaryPass, decode_encode]

end RadixPass
