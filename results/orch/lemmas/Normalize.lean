import Mathlib.Data.List.GetD
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_5112_aux

def gateStep (xs : List Nat) (g : Bool × Nat × Nat) : List Nat :=
  xs ++ [if g.1 = true then xs.getD g.2.1 0 ||| xs.getD g.2.2 0
    else xs.getD g.2.1 0 &&& xs.getD g.2.2 0]

def clipGate (n : Nat) (g : Bool × Nat × Nat) : Bool × Nat × Nat :=
  (g.1, min g.2.1 n, min g.2.2 n)

def clipProgram (n : Nat) : List (Bool × Nat × Nat) → List (Bool × Nat × Nat)
  | [] => []
  | g :: gs => clipGate n g :: clipProgram (n + 1) gs

theorem getD_default (xs : List Nat) (i : Nat) (h : xs.length ≤ i) : xs.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_clip (xs : List Nat) (i : Nat) :
    xs.getD (min i xs.length) 0 = xs.getD i 0 := by
  by_cases h : i ≤ xs.length
  · rw [Nat.min_eq_left h]
  · have h' : xs.length ≤ i := by omega
    rw [Nat.min_eq_right h', getD_default _ _ (by omega),
      getD_default _ _ h']

theorem gateStep_clip (xs : List Nat) (g : Bool × Nat × Nat) :
    gateStep xs (clipGate xs.length g) = gateStep xs g := by
  simp only [gateStep, clipGate, getD_clip]

theorem clipProgram_length (n : Nat) (gs : List (Bool × Nat × Nat)) :
    (clipProgram n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [clipProgram, ih]

theorem gateStep_length (xs : List Nat) (g : Bool × Nat × Nat) :
    (gateStep xs g).length = xs.length + 1 := by
  simp [gateStep]

theorem eval_clipProgram (xs : List Nat) (gs : List (Bool × Nat × Nat)) :
    (clipProgram xs.length gs).foldl gateStep xs = gs.foldl gateStep xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [clipProgram, List.foldl_cons, gateStep_clip]
    rw [← gateStep_length xs g]
    exact ih _

theorem clipProgram_sources (n : Nat) (gs : List (Bool × Nat × Nat)) :
    ∀ g ∈ clipProgram n gs, g.2.1 < n + gs.length + 1 ∧
      g.2.2 < n + gs.length + 1 := by
  induction gs generalizing n with
  | nil => simp [clipProgram]
  | cons g gs ih =>
    intro a ha
    simp only [clipProgram, List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp only [clipGate, List.length_cons]
      constructor
      · exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)
      · exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)
    · have h := ih (n + 1) a ha
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem gateStep_repeat (xs : List Nat) (i : Nat) :
    gateStep xs (true, i, i) = xs ++ [xs.getD i 0] := by
  simp [gateStep]

theorem eval_length (xs : List Nat) (gs : List (Bool × Nat × Nat)) :
    (gs.foldl gateStep xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, gateStep_length, List.length_cons]
    omega

theorem foldl_replicate_repeat (xs : List Nat) (i k : Nat) (hi : i < xs.length) :
    (List.replicate k (true, i, i)).foldl gateStep xs =
      xs ++ List.replicate k (xs.getD i 0) := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons, gateStep_repeat,
      ih (xs ++ [xs.getD i 0]) (by simpa using Nat.lt_succ_of_lt hi)]
    rw [List.getD_append xs [xs.getD i 0] 0 i hi]
    simp [List.replicate_succ, List.append_assoc]

theorem getD_extend_last (xs : List Nat) (k : Nat) (hx : 0 < xs.length) :
    (xs ++ List.replicate k (xs.getD (xs.length - 1) 0)).getD
      (xs.length + k - 1) 0 = xs.getD (xs.length - 1) 0 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [List.getD_append_right xs _ 0 _ (by omega)]
    exact List.getD_replicate (x := xs.getD (xs.length - 1) 0) (by omega)

theorem padded_output (xs : List Nat) (gs : List (Bool × Nat × Nat)) (k : Nat)
    (h : 0 < xs.length + gs.length) :
    let ys := gs.foldl gateStep xs
    let more := List.replicate k (true, xs.length + gs.length - 1,
      xs.length + gs.length - 1)
    ((gs ++ more).foldl gateStep xs).getD
      (xs.length + (gs ++ more).length - 1) 0 =
        ys.getD (xs.length + gs.length - 1) 0 := by
  dsimp only
  rw [List.foldl_append, List.length_append, List.length_replicate]
  rw [foldl_replicate_repeat _ _ _ (by rw [eval_length]; omega)]
  have he : (gs.foldl gateStep xs).length = xs.length + gs.length := eval_length xs gs
  have ht := getD_extend_last (gs.foldl gateStep xs) k (by rw [he]; exact h)
  simpa only [he, Nat.add_assoc] using ht

theorem bounded_pad (xs : List Nat) (gs : List (Bool × Nat × Nat)) (s : Nat)
    (hpos : 0 < xs.length + gs.length) (hlen : gs.length ≤ s) :
    ∃ hs : List (Bool × Nat × Nat), hs.length = s ∧
      (∀ g ∈ hs, g.2.1 < xs.length + s + 1 ∧ g.2.2 < xs.length + s + 1) ∧
      (hs.foldl gateStep xs).getD (xs.length + s - 1) 0 =
        (gs.foldl gateStep xs).getD (xs.length + gs.length - 1) 0 := by
  let more := List.replicate (s - gs.length)
    (true, xs.length + gs.length - 1, xs.length + gs.length - 1)
  let raw := gs ++ more
  have hraw : raw.length = s := by
    simp only [raw, more, List.length_append, List.length_replicate]
    omega
  refine ⟨clipProgram xs.length raw, ?_, ?_, ?_⟩
  · rw [clipProgram_length, hraw]
  · simpa only [hraw] using clipProgram_sources xs.length raw
  · rw [eval_clipProgram]
    have ho := padded_output xs gs (s - gs.length) hpos
    change (raw.foldl gateStep xs).getD (xs.length + raw.length - 1) 0 = _ at ho
    simpa only [hraw] using ho

theorem eval_extends (xs : List Nat) (gs : List (Bool × Nat × Nat)) :
    ∃ zs : List Nat, gs.foldl gateStep xs = xs ++ zs := by
  induction gs generalizing xs with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨zs, hz⟩ := ih (gateStep xs g)
    refine ⟨[if g.1 = true then xs.getD g.2.1 0 ||| xs.getD g.2.2 0
      else xs.getD g.2.1 0 &&& xs.getD g.2.2 0] ++ zs, ?_⟩
    rw [List.foldl_cons, hz]
    simp only [gateStep, List.append_assoc]

theorem eval_preserves (xs : List Nat) (gs : List (Bool × Nat × Nat)) (i : Nat)
    (hi : i < xs.length) :
    (gs.foldl gateStep xs).getD i 0 = xs.getD i 0 := by
  obtain ⟨zs, hz⟩ := eval_extends xs gs
  rw [hz, List.getD_append xs zs 0 i hi]

theorem take_eval_length (xs : List Nat) (gs : List (Bool × Nat × Nat)) (j : Nat)
    (hj : j ≤ gs.length) :
    ((gs.take j).foldl gateStep xs).length = xs.length + j := by
  rw [eval_length, List.length_take, Nat.min_eq_left hj]

theorem take_eval_preserves (xs : List Nat) (gs : List (Bool × Nat × Nat)) (j k : Nat)
    (hj : j ≤ gs.length) (hk : k < xs.length + j) :
    (gs.foldl gateStep xs).getD k 0 = ((gs.take j).foldl gateStep xs).getD k 0 := by
  have hh : k < ((gs.take j).foldl gateStep xs).length := by
    rw [take_eval_length xs gs j hj]
    exact hk
  simpa only [← List.foldl_append, List.take_append_drop] using
    eval_preserves ((gs.take j).foldl gateStep xs) (gs.drop j) k hh

theorem take_eval_source (xs : List Nat) (gs : List (Bool × Nat × Nat)) (j k : Nat)
    (hj : j ≤ gs.length) :
    ((gs.take j).foldl gateStep xs).getD k 0 =
      if k < xs.length + j then (gs.foldl gateStep xs).getD k 0 else 0 := by
  split
  · exact (take_eval_preserves xs gs j k hj ‹_›).symm
  · exact getD_default _ _ (by rw [take_eval_length xs gs j hj]; omega)

theorem gate_eq (xs : List Nat) (gs : List (Bool × Nat × Nat)) (j : Nat)
    (hj : j < gs.length) :
    (gs.foldl gateStep xs).getD (xs.length + j) 0 =
      let front := (gs.take j).foldl gateStep xs
      let g := gs[j]
      if g.1 = true then front.getD g.2.1 0 ||| front.getD g.2.2 0
        else front.getD g.2.1 0 &&& front.getD g.2.2 0 := by
  rw [take_eval_preserves xs gs (j + 1) (xs.length + j) (by omega) (by omega)]
  rw [List.take_succ_eq_append_getElem hj, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, gateStep]
  rw [List.getD_append_right _ _ 0 _ (by rw [take_eval_length xs gs j (by omega)])]
  rw [take_eval_length xs gs j (by omega), Nat.sub_self]
  rfl

end PEqualNP.Outside.L_meta_5112_aux
