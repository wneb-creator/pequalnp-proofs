import Mathlib.Tactic.Tauto
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3787

def slots : List (Fin 26) := [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def front : List Gate := [
  ⟨GateOp.or, [13, 14]⟩,
  ⟨GateOp.or, [26, 16]⟩,
  ⟨GateOp.or, [27, 22]⟩,
  ⟨GateOp.and, [0, 28]⟩,
  ⟨GateOp.or, [13, 15]⟩,
  ⟨GateOp.or, [30, 21]⟩,
  ⟨GateOp.or, [31, 25]⟩,
  ⟨GateOp.and, [1, 32]⟩,
  ⟨GateOp.or, [13, 19]⟩,
  ⟨GateOp.or, [34, 23]⟩,
  ⟨GateOp.or, [35, 24]⟩,
  ⟨GateOp.and, [3, 36]⟩,
  ⟨GateOp.or, [13, 17]⟩,
  ⟨GateOp.or, [38, 18]⟩,
  ⟨GateOp.or, [39, 20]⟩,
  ⟨GateOp.and, [9, 40]⟩,
  ⟨GateOp.or, [29, 33]⟩,
  ⟨GateOp.or, [42, 37]⟩,
  ⟨GateOp.or, [43, 41]⟩]

def rename (i : Nat) : Nat :=
  if h : i < slots.length then (slots[i]).val else 45 + (i - slots.length)

def renamed (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩

lemma runLen (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons a gs ih => simp [ih, step]; omega

lemma readLeft (xs ys : List Bool) {i : Nat} (h : i < xs.length) :
    (xs ++ ys).getD i false = xs.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma readRight (xs ys : List Bool) (i : Nat) :
    (xs ++ ys).getD (xs.length + i) false = ys.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right xs.length i)]

lemma read (f : Fin 26 → Bool) (pre tail : List Bool)
    (hp : pre.length = 45) (hf : ∀ j : Fin 26, pre.getD j.val false = f j) (i : Nat) :
    (pre ++ tail).getD (rename i) false = (slots.map f ++ tail).getD i false := by
  unfold rename
  split
  next h =>
    rw [readLeft _ _ (by have := slots[i].isLt; omega),
      readLeft _ _ (by simpa using h), hf]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h : i < (slots.map f).length)]
  next h =>
    have hi : i = (slots.map f).length + (i - slots.length) := by simp; omega
    rw [← hp, readRight]
    exact ((readRight (slots.map f) tail (i - slots.length)).symm.trans (congrArg (fun k => (slots.map f ++ tail).getD k false) hi.symm))

lemma run (f : Fin 26 → Bool) (pre : List Bool) (hp : pre.length = 45)
    (hf : ∀ j : Fin 26, pre.getD j.val false = f j)
    (gs : List Gate) (t : List Bool) :
    ∃ u : List Bool, (gs.map renamed).foldl step (pre ++ t) = pre ++ u ∧
      gs.foldl step (slots.map f ++ t) = slots.map f ++ u := by
  induction gs generalizing t with
  | nil => exact ⟨t, rfl, rfl⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => (slots.map f ++ t).getD i false)
    have hv : (g.inputs.map rename).map (fun i => (pre ++ t).getD i false) =
        g.inputs.map (fun i => (slots.map f ++ t).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact read f pre t hp hf i
    simpa only [List.map_cons, List.foldl_cons, step, renamed, hv, List.append_assoc, b]
      using ih (t ++ [b])

def combo (C : Circuit) : Circuit :=
  ⟨front ++ C.gates.map renamed ++ [⟨GateOp.or, [rename C.output, 44]⟩],
   45 + C.size⟩

def vec (s t : Finset (Fin 13)) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)

abbrev near (p l : Fin 13) : Prop := (p.val + l.val) % 13 ∈ ([0,1,3,9] : List Nat)

def special (s t : Finset (Fin 13)) : Prop :=
  ∃ p ∈ s, p.val ∈ ([0,1,3,9] : List Nat) ∧ ∃ l ∈ t, near p l

lemma frontRaw (f : Fin 26 → Bool) :
    (front.foldl step (List.ofFn f)).getD 44 false = ((((f 0 && ((((f 13 || (f 14 || false)) || (f 16 || false)) || (f 22 || false)) && true)) || ((f 1 && ((((f 13 || (f 15 || false)) || (f 21 || false)) || (f 25 || false)) && true)) || false)) || ((f 3 && ((((f 13 || (f 19 || false)) || (f 23 || false)) || (f 24 || false)) && true)) || false)) || ((f 9 && ((((f 13 || (f 17 || false)) || (f 18 || false)) || (f 20 || false)) && true)) || false)) := by cbv

lemma frontEval (s t : Finset (Fin 13)) :
    (front.foldl step (List.ofFn (vec s t))).getD 44 false = true ↔ special s t := by
  have points : ∀ p : Fin 13, p.val ∈ ([0,1,3,9] : List Nat) ↔
      p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9 := by decide
  have row0 : ∀ l : Fin 13, near 0 l ↔ l = 0 ∨ l = 1 ∨ l = 3 ∨ l = 9 := by decide
  have row1 : ∀ l : Fin 13, near 1 l ↔ l = 0 ∨ l = 2 ∨ l = 8 ∨ l = 12 := by decide
  have row3 : ∀ l : Fin 13, near 3 l ↔ l = 0 ∨ l = 6 ∨ l = 10 ∨ l = 11 := by decide
  have row9 : ∀ l : Fin 13, near 9 l ↔ l = 0 ∨ l = 4 ∨ l = 5 ∨ l = 7 := by decide
  rw [frontRaw]
  change ((((decide ((0 : Fin 13) ∈ s) && ((((decide ((0 : Fin 13) ∈ t) || (decide ((1 : Fin 13) ∈ t) || false)) || (decide ((3 : Fin 13) ∈ t) || false)) || (decide ((9 : Fin 13) ∈ t) || false)) && true)) || ((decide ((1 : Fin 13) ∈ s) && ((((decide ((0 : Fin 13) ∈ t) || (decide ((2 : Fin 13) ∈ t) || false)) || (decide ((8 : Fin 13) ∈ t) || false)) || (decide ((12 : Fin 13) ∈ t) || false)) && true)) || false)) || ((decide ((3 : Fin 13) ∈ s) && ((((decide ((0 : Fin 13) ∈ t) || (decide ((6 : Fin 13) ∈ t) || false)) || (decide ((10 : Fin 13) ∈ t) || false)) || (decide ((11 : Fin 13) ∈ t) || false)) && true)) || false)) || ((decide ((9 : Fin 13) ∈ s) && ((((decide ((0 : Fin 13) ∈ t) || (decide ((4 : Fin 13) ∈ t) || false)) || (decide ((5 : Fin 13) ∈ t) || false)) || (decide ((7 : Fin 13) ∈ t) || false)) && true)) || false)) = true ↔ _
  simp only [Bool.or_false, Bool.and_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  unfold special
  constructor
  · intro h
    rcases h with ((h | h) | h) | h
    · refine ⟨0, h.1, by decide, ?_⟩
      rcases h.2 with ((hl | hl) | hl) | hl
      · exact ⟨0, hl, by decide⟩
      · exact ⟨1, hl, by decide⟩
      · exact ⟨3, hl, by decide⟩
      · exact ⟨9, hl, by decide⟩
    · refine ⟨1, h.1, by decide, ?_⟩
      rcases h.2 with ((hl | hl) | hl) | hl
      · exact ⟨0, hl, by decide⟩
      · exact ⟨2, hl, by decide⟩
      · exact ⟨8, hl, by decide⟩
      · exact ⟨12, hl, by decide⟩
    · refine ⟨3, h.1, by decide, ?_⟩
      rcases h.2 with ((hl | hl) | hl) | hl
      · exact ⟨0, hl, by decide⟩
      · exact ⟨6, hl, by decide⟩
      · exact ⟨10, hl, by decide⟩
      · exact ⟨11, hl, by decide⟩
    · refine ⟨9, h.1, by decide, ?_⟩
      rcases h.2 with ((hl | hl) | hl) | hl
      · exact ⟨0, hl, by decide⟩
      · exact ⟨4, hl, by decide⟩
      · exact ⟨5, hl, by decide⟩
      · exact ⟨7, hl, by decide⟩
  · rintro ⟨p, hp, hs, l, hl, hn⟩
    rcases (points p).1 hs with rfl | rfl | rfl | rfl
    · rcases (row0 l).1 hn with rfl | rfl | rfl | rfl <;> tauto
    · rcases (row1 l).1 hn with rfl | rfl | rfl | rfl <;> tauto
    · rcases (row3 l).1 hn with rfl | rfl | rfl | rfl <;> tauto
    · rcases (row9 l).1 hn with rfl | rfl | rfl | rfl <;> tauto

lemma keep (gs : List Gate) (w : List Bool) {i : Nat} (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact readLeft _ _ hi

lemma endOR (w : List Bool) (a b : Nat) :
    (step w ⟨GateOp.or, [a,b]⟩).getD w.length false =
      (w.getD a false || w.getD b false) := by
  simp [step, GateOp.eval]

lemma comboEval (C : Circuit) (s t : Finset (Fin 13)) :
    (combo C).eval (List.ofFn (vec s t)) = true ↔
      C.eval (slots.map (vec s t)) = true ∨ special s t := by
  let f := vec s t
  let pre := front.foldl step (List.ofFn f)
  have hp : pre.length = 45 := by
    change (front.foldl step (List.ofFn f)).length = 45
    rw [runLen, List.length_ofFn]
    decide
  have hf (j : Fin 26) : pre.getD j.val false = f j := by
    rw [show pre = front.foldl step (List.ofFn f) from rfl,
      keep _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  obtain ⟨u, hu, hv⟩ := run f pre hp hf C.gates []
  simp only [List.append_nil] at hu hv
  have hlen : (pre ++ u).length = 45 + C.size := by
    rw [← hu, runLen, List.length_map, hp]; rfl
  have hr : (pre ++ u).getD (rename C.output) false = C.eval (slots.map f) := by
    rw [read f pre u hp hf, ← hv]; rfl
  have hs := frontEval s t
  change pre.getD 44 false = true ↔ special s t at hs
  change ((front ++ C.gates.map renamed ++ [(⟨GateOp.or, [rename C.output, 44]⟩ : Gate)]).foldl step (List.ofFn f)).getD
    (45 + C.size) false = true ↔ _
  rw [List.foldl_append, List.foldl_append]
  change (step ((C.gates.map renamed).foldl step pre) ⟨GateOp.or, [rename C.output, 44]⟩).getD (45 + C.size) false = true ↔ _
  rw [hu, ← hlen]
  rw [endOR, hr, readLeft pre u (show 44 < pre.length by omega), Bool.or_eq_true, hs]

end PEqualNP.Outside.L_meta_3787

open PEqualNP.Outside.L_meta_3787

theorem PEqualNP.Outside.L_meta_3787 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.output < (21 : ℕ) + x1.size →       ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x4 ∧           x4.size ≤ x1.size + (20 : ℕ) ∧             have x5 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))];             have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);             have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x7 x8 : Fin (13 : ℕ)) => (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             ∀ (x8 x9 : Finset (Fin (13 : ℕ))), x4.eval (List.ofFn (x6 x8 x9)) = Bool.true ↔ x1.eval (List.map (x6 x8 x9) x5) = Bool.true ∨ ∃ x10 ∈ x8, ↑x10 ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ∃ x11 ∈ x9, x7 x10 x11 := by
  intro C hm _
  refine ⟨combo C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [combo, List.mem_append, List.mem_singleton, List.mem_map] at hg
    rcases hg with (hg | ⟨g, h, rfl⟩) | rfl
    · have good : ∀ g ∈ front, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          g.inputs.length ≤ 2 := by
        intro a ha
        simp only [front, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      exact good g hg
    · simpa [renamed] using hm g h
    · simp
  · simp [combo, Circuit.size, front] <;> omega
  · exact fun s t => comboEval C s t
