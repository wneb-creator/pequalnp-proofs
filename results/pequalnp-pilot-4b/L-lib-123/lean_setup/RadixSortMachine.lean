import Mathlib
import PEqualNP.Library.Evasion.MTrans
import PEqualNP.Library.Machines.IterMeasure

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

namespace IterationBound

open Turing PEqualNP.Library PEqualNP.Library.Machines

def pointBound (C data passes : ℕ) : ℕ :=
  passes * (C * data + C + 2 * data + 3) + 4 * data + passes + 5

def totalBound (C n : ℕ) : ℕ := n * (C * n + C + 2 * n + 3) + 5 * n + 5

lemma pointBound_le_totalBound (C data passes : ℕ) :
    pointBound C data passes ≤ totalBound C (data + passes) := by
  have hinner : C * data + C + 2 * data + 3 ≤
      C * (data + passes) + C + 2 * (data + passes) + 3 := by
    gcongr <;> omega
  have hmul := Nat.mul_le_mul (show passes ≤ data + passes by omega) hinner
  dsimp [pointBound, totalBound]
  omega

lemma iterate_length (g : List Bool → List Bool)
    (hg : ∀ x, (g x).length ≤ x.length) (x : List Bool) (n : ℕ) :
    (g^[n] x).length ≤ x.length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hg _).trans ih

lemma linear_iteration (g : List Bool → List Bool) (C : ℕ)
    (hg : ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) g
      (fun n => C * n + C))
    (hlen : ∀ x, (g x).length ≤ x.length) :
    ∃ c : TM2ComputableInTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1),
      ∀ y u, (c.outputsFun (y, u)).steps ≤ pointBound C y.length u.length := by
  obtain ⟨c, hc⟩ := hg
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let d₀ : c.tm.Γ c.tm.k₀ → Bool := c.inputAlphabet
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let p : Polynomial ℕ := Polynomial.C C * Polynomial.X + Polynomial.C C
  have hd : ∀ b, d₀ (e₀ b) = b := fun b => c.inputAlphabet.right_inv b
  have hrun : ∀ z : List Bool, ∃ (s : ℕ) (out : List (c.tm.Γ c.tm.k₁)),
      s ≤ p.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm out) ∧ out.map e₁ = g z := by
    intro z
    refine ⟨(c.outputsFun z).steps, (g z).map c.outputAlphabet.invFun, ?_,
      (c.outputsFun z).evals_in_steps, ?_⟩
    · simpa [p] using (c.outputsFun z).steps_le_m.trans (hc z.length)
    · simp only [List.map_map]
      conv_rhs => rw [← List.map_id (g z)]
      exact List.map_congr_left fun b _ => c.outputAlphabet.right_inv b
  have key : ∀ y u : List Bool, ∃ n, n ≤ pointBound C y.length u.length ∧
      (flip bind (TM2.step (Iter.iterProg c.tm e₀ d₀ e₁)))^[n]
        (some (initList (Iter.iterM c.tm e₀ d₀ e₁) (encodePair (y, u)))) =
        some (haltList (Iter.iterM c.tm e₀ d₀ e₁) (g^[u.length] y)) := by
    intro y u
    obtain ⟨n, hn, hr⟩ := Iter.iter_run_bdd e₀ d₀ e₁ g p hd hrun y u y.length
      (by intro j _; exact iterate_length g hlen y j)
    refine ⟨n, ?_, hr⟩
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at hn
    dsimp [pointBound]
    omega
  let result : TM2ComputableInTime encodePair (fun x : List Bool => x)
      (fun q : List Bool × List Bool => g^[q.2.length] q.1) := {
    tm := Iter.iterM c.tm e₀ d₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := totalBound C
    outputsFun := fun q => {
      steps := Classical.choose (key q.1 q.2)
      evals_in_steps := by
        have hm : ∀ (γ : Type) (xs : List γ), List.map (Equiv.refl γ).invFun xs = xs :=
          fun _ _ => by simp
        exact (congrArg (fun xs =>
          (flip bind (TM2.step (Iter.iterProg c.tm e₀ d₀ e₁)))^[Classical.choose (key q.1 q.2)]
            (some (initList (Iter.iterM c.tm e₀ d₀ e₁) xs))) (hm _ (encodePair q))).trans
          ((Classical.choose_spec (key q.1 q.2)).2.trans
            (congrArg (fun xs => some (haltList (Iter.iterM c.tm e₀ d₀ e₁) xs))
              (hm _ (g^[q.2.length] q.1))).symm)
      steps_le_m := (Classical.choose_spec (key q.1 q.2)).1.trans (by
        simpa [encodePair] using pointBound_le_totalBound C q.1.length q.2.length)
    }
  }
  exact ⟨result, fun y u => (Classical.choose_spec (key y u)).1⟩

end IterationBound

namespace RadixOrder

def bitPass {α : Type} (bit : α → Bool) (rows : List α) : List α :=
  rows.filter (fun row => !(bit row)) ++ rows.filter bit

def lowValue {α : Type} (bits : α → ℕ → Bool) (row : α) : ℕ → ℕ
  | 0 => 0
  | k + 1 => lowValue bits row k + if bits row k then 2 ^ k else 0

lemma lowValue_lt {α : Type} (bits : α → ℕ → Bool) (row : α) (k : ℕ) :
    lowValue bits row k < 2 ^ k := by
  induction k with
  | zero => simp [lowValue]
  | succ k ih =>
    cases h : bits row k <;> simp [lowValue, h, pow_succ] <;> omega

lemma bitPass_perm {α : Type} (bit : α → Bool) (rows : List α) :
    (bitPass bit rows).Perm rows := by
  simpa [bitPass] using List.filter_append_perm (fun row => !(bit row)) rows

lemma bitPass_sorted {α : Type} (bits : α → ℕ → Bool) (k : ℕ) (rows : List α)
    (h : rows.Pairwise (fun a b => lowValue bits a k ≤ lowValue bits b k)) :
    (bitPass (fun row => bits row k) rows).Pairwise
      (fun a b => lowValue bits a (k + 1) ≤ lowValue bits b (k + 1)) := by
  rw [bitPass, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_filter.mpr
    apply h.imp
    intro a b hab ha hb
    have ha' : bits a k = false := by simpa using ha
    have hb' : bits b k = false := by simpa using hb
    simpa [lowValue, ha', hb'] using hab
  · apply List.pairwise_filter.mpr
    apply h.imp
    intro a b hab ha hb
    simpa [lowValue, ha, hb] using Nat.add_le_add_right hab (2 ^ k)
  · intro a ha b hb
    have ha' : bits a k = false := by simpa using (List.mem_filter.mp ha).2
    have hb' : bits b k = true := (List.mem_filter.mp hb).2
    simp only [lowValue, ha', hb', Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    have bound := lowValue_lt bits a k
    omega

def radix {α : Type} (bits : α → ℕ → Bool) : ℕ → List α → List α
  | 0, rows => rows
  | k + 1, rows => bitPass (fun row => bits row k) (radix bits k rows)

lemma radix_perm {α : Type} (bits : α → ℕ → Bool) (k : ℕ) (rows : List α) :
    (radix bits k rows).Perm rows := by
  induction k with
  | zero => exact List.Perm.refl _
  | succ k ih => exact (bitPass_perm _ _).trans ih

lemma radix_sorted {α : Type} (bits : α → ℕ → Bool) (k : ℕ) (rows : List α) :
    (radix bits k rows).Pairwise (fun a b => lowValue bits a k ≤ lowValue bits b k) := by
  induction k with
  | zero => exact List.pairwise_of_forall (by intro a b; simp [lowValue])
  | succ k ih => exact bitPass_sorted bits k _ ih

abbrev Row := List Bool × Bool

def rowBit (row : Row) (i : ℕ) : Bool := row.1.getD i false

def rotateRow (i : ℕ) (row : Row) : Row := (row.1.rotate i, row.2)

def rowPass (rows : List Row) : List Row :=
  (bitPass (fun row => rowBit row 0) rows).map (rotateRow 1)

lemma rotateRow_zero (row : Row) : rotateRow 0 row = row := by
  simp [rotateRow]

lemma rotateRow_add (i j : ℕ) (row : Row) :
    rotateRow j (rotateRow i row) = rotateRow (i + j) row := by
  simp [rotateRow]

lemma rowBit_rotate (row : Row) (i : ℕ) (h : i < row.1.length) :
    rowBit (rotateRow i row) 0 = rowBit row i := by
  simp only [rowBit, rotateRow, List.getD_eq_getElem?_getD]
  rw [← List.head?_eq_getElem?, List.head?_rotate h]

lemma filter_map_eq {α β : Type} (f : α → β) (p : β → Bool) (q : α → Bool) (rows : List α)
    (h : ∀ row ∈ rows, p (f row) = q row) :
    (rows.map f).filter p = (rows.filter q).map f := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have he := h row (by simp)
    have ht := ih (by intro r hr; exact h r (by simp [hr]))
    cases hb : q row <;> simp [he, hb, ht]

lemma bitPass_map {α β : Type} (f : α → β) (p : β → Bool) (q : α → Bool) (rows : List α)
    (h : ∀ row ∈ rows, p (f row) = q row) :
    bitPass p (rows.map f) = (bitPass q rows).map f := by
  rw [bitPass, bitPass, List.map_append,
    filter_map_eq f (fun row => !(p row)) (fun row => !(q row)) rows
      (by intro row hr; rw [h row hr]), filter_map_eq f p q rows h]

lemma rowPass_rotated (rows : List Row) (i : ℕ)
    (h : ∀ row ∈ rows, i < row.1.length) :
    rowPass (rows.map (rotateRow i)) =
      (bitPass (fun row => rowBit row i) rows).map (rotateRow (i + 1)) := by
  rw [rowPass, bitPass_map (rotateRow i) (fun row => rowBit row 0)
    (fun row => rowBit row i) rows (by intro row hr; exact rowBit_rotate row i (h row hr))]
  simp [List.map_map, Function.comp_def, rotateRow_add]

lemma iterated_pass (width i : ℕ) (rows : List Row)
    (hw : ∀ row ∈ rows, row.1.length = width) (hi : i ≤ width) :
    rowPass^[i] rows = (radix rowBit i rows).map (rotateRow i) := by
  induction i with
  | zero =>
    have he : rotateRow 0 = id := funext rotateRow_zero
    simp [radix, he]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    rw [rowPass_rotated]
    · rfl
    · intro row hr
      have hm := (radix_perm rowBit i rows).mem_iff.mp hr
      rw [hw row hm]
      omega

lemma full_passes_eq (width : ℕ) (rows : List Row)
    (hw : ∀ row ∈ rows, row.1.length = width) :
    rowPass^[width] rows = radix rowBit width rows := by
  rw [iterated_pass width width rows hw (le_refl _)]
  calc
    (radix rowBit width rows).map (rotateRow width) = (radix rowBit width rows).map id := by
      apply List.map_congr_left
      intro row hr
      have hm := (radix_perm rowBit width rows).mem_iff.mp hr
      have hlen := hw row hm
      simp [rotateRow, ← hlen]
    _ = radix rowBit width rows := List.map_id _

lemma full_passes_correct (width : ℕ) (rows : List Row)
    (hw : ∀ row ∈ rows, row.1.length = width) :
    (rowPass^[width] rows).Perm rows ∧
    (rowPass^[width] rows).Pairwise
      (fun a b => lowValue rowBit a width ≤ lowValue rowBit b width) := by
  rw [full_passes_eq width rows hw]
  exact ⟨radix_perm _ _ _, radix_sorted _ _ _⟩

def moveHead (row : Row) : Row :=
  match row.1 with
  | [] => row
  | head :: rest => (rest ++ [head], row.2)

def concretePass (rows : List Row) : List Row :=
  ((rows.filter (fun row => row.1.headD false == false)).map moveHead) ++
    ((rows.filter (fun row => row.1.headD false == true)).map moveHead)

lemma moveHead_eq (row : Row) : moveHead row = rotateRow 1 row := by
  obtain ⟨bits, value⟩ := row
  cases bits <;> simp [moveHead, rotateRow]

lemma head_eq (row : Row) : row.1.headD false = rowBit row 0 := by
  obtain ⟨bits, value⟩ := row
  cases bits <;> rfl

lemma concretePass_eq (rows : List Row) : concretePass rows = rowPass rows := by
  have hm : moveHead = rotateRow 1 := funext moveHead_eq
  have hfalse : (fun row : Row => row.1.headD false == false) =
      (fun row : Row => !(rowBit row 0)) := by
    funext row
    rw [head_eq]
    cases rowBit row 0 <;> rfl
  have htrue : (fun row : Row => row.1.headD false == true) =
      (fun row : Row => rowBit row 0) := by
    funext row
    rw [head_eq]
    cases rowBit row 0 <;> rfl
  simp only [concretePass, rowPass, bitPass, hfalse, htrue, hm, List.map_append]

lemma concrete_full_passes_correct (width : ℕ) (rows : List Row)
    (hw : ∀ row ∈ rows, row.1.length = width) :
    (concretePass^[width] rows).Perm rows ∧
    (concretePass^[width] rows).Pairwise
      (fun a b => lowValue rowBit a width ≤ lowValue rowBit b width) := by
  have he : concretePass = rowPass := funext concretePass_eq
  rw [he]
  exact full_passes_correct width rows hw

lemma encoded_length (width : ℕ) (rows : List Row)
    (hw : ∀ row ∈ rows, row.1.length = width) :
    (rows.flatMap (fun row => row.1.map (Sum.inl : Bool → Bool ⊕ Bool) ++ [Sum.inr row.2])).length =
      (width + 1) * rows.length := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hrow := hw row (by simp)
    have hrows := ih (by intro r hr; exact hw r (by simp [hr]))
    simp only [List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, List.length_nil, Nat.mul_succ]
    rw [hrow, hrows]
    omega

end RadixOrder

namespace RadixSortMachine

open PEqualNP.Library

def encode (rows : List RadixPass.Row) : List Bool :=
  RadixPass.encodeSymbols (RadixPass.encodeRows rows)

lemma pass_compat (rows : List RadixPass.Row) (hne : ∀ row ∈ rows, row.1 ≠ []) :
    RadixPass.binaryPass (encode rows) = encode (RadixOrder.concretePass rows) := by
  rw [encode, RadixPass.binaryPass_correct, RadixPass.pass_correct rows hne]
  rfl

lemma width_preserved (width : ℕ) (rows : List RadixPass.Row)
    (hw : ∀ row ∈ rows, row.1.length = width) :
    ∀ row ∈ RadixOrder.concretePass rows, row.1.length = width := by
  intro row hr
  rw [RadixOrder.concretePass_eq, RadixOrder.rowPass] at hr
  obtain ⟨before, hbefore, rfl⟩ := List.mem_map.mp hr
  have hm := (RadixOrder.bitPass_perm (fun row => RadixOrder.rowBit row 0) rows).mem_iff.mp hbefore
  simpa [RadixOrder.rotateRow] using hw before hm

lemma iterated_width (width steps : ℕ) (rows : List RadixPass.Row)
    (hw : ∀ row ∈ rows, row.1.length = width) :
    ∀ row ∈ RadixOrder.concretePass^[steps] rows, row.1.length = width := by
  induction steps with
  | zero => exact hw
  | succ steps ih =>
    rw [Function.iterate_succ_apply']
    exact width_preserved width _ ih

lemma iterated_compat (width steps : ℕ) (rows : List RadixPass.Row)
    (hw : ∀ row ∈ rows, row.1.length = width) (hwidth : 1 ≤ width) :
    RadixPass.binaryPass^[steps] (encode rows) = encode (RadixOrder.concretePass^[steps] rows) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    simp only [Function.iterate_succ_apply', ih]
    apply pass_compat
    intro row hr he
    have hw := iterated_width width steps rows hw row hr
    simp [he] at hw
    omega

lemma encode_length (width : ℕ) (rows : List RadixPass.Row)
    (hw : ∀ row ∈ rows, row.1.length = width) :
    (encode rows).length = 2 * ((width + 1) * rows.length) := by
  rw [encode, RadixPass.encode_length]
  congr 1
  exact RadixOrder.encoded_length width rows hw

lemma pointBound_quasilinear (C width count : ℕ) :
    IterationBound.pointBound C (2 * ((width + 1) * count)) width ≤
      (2 * C + 20) * (count + 1) * (width + 1) ^ 2 := by
  dsimp [IterationBound.pointBound]
  ring_nf
  omega

lemma sorting_machine : ∃ K : ℕ,
    ∃ c : Turing.TM2ComputableInTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => RadixPass.binaryPass^[p.2.length] p.1),
      ∀ (width : ℕ) (rows : List RadixPass.Row), 1 ≤ width →
        (∀ row ∈ rows, row.1.length = width) →
        ∃ sorted : List RadixPass.Row,
          sorted.Perm rows ∧
          sorted.Pairwise (fun a b =>
            RadixOrder.lowValue RadixOrder.rowBit a width ≤
              RadixOrder.lowValue RadixOrder.rowBit b width) ∧
          RadixPass.binaryPass^[width] (encode rows) = encode sorted ∧
          (c.outputsFun (encode rows, List.replicate width true)).steps ≤
            K * (rows.length + 1) * (width + 1) ^ 2 := by
  obtain ⟨C, hC⟩ := RadixPass.binaryPass_time
  obtain ⟨c, hc⟩ := IterationBound.linear_iteration RadixPass.binaryPass C hC RadixPass.binaryPass_length
  refine ⟨2 * C + 20, c, ?_⟩
  intro width rows hwidth hw
  have hs := RadixOrder.concrete_full_passes_correct width rows hw
  refine ⟨RadixOrder.concretePass^[width] rows, hs.1, hs.2,
    iterated_compat width width rows hw hwidth, ?_⟩
  have hb := hc (encode rows) (List.replicate width true)
  conv at hb =>
    rhs
    rw [encode_length width rows hw, List.length_replicate]
  exact hb.trans (pointBound_quasilinear C width rows.length)

end RadixSortMachine
