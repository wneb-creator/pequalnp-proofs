import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27759

open PEqualNP.CircuitLowerBounds



abbrev h7Atom := Fin 6

def h7Dual (a : h7Atom) : h7Atom := ![5, 1, 2, 4, 3, 0] a

def h7Infimum (a b : h7Atom) : h7Atom :=
  if a = 0 ∨ b = 0 then 0
  else if a = 5 then b
  else if b = 5 then a
  else if a = 3 ∨ b = 3 then 3
  else if a = 4 then b
  else if b = 4 then a
  else if a = b then a
  else 3

def h7Op (s : Bool) (a b : h7Atom) : h7Atom :=
  if s then h7Dual (h7Infimum (h7Dual a) (h7Dual b)) else h7Infimum a b

abbrev h7Col := h7Atom × h7Atom
def h7Dead : h7Col := (0, 0)
def h7GoalCol : h7Col := (3, 4)
abbrev h7Good (w : h7Col) : Prop := w ≠ h7GoalCol ∧ w ≠ (4, 3)
def h7Blend (s : Bool) (u v : h7Col) : h7Col := (h7Op s u.1 v.1, h7Op s u.2 v.2)

def h7Uses (axis : Bool) (a : h7Atom) : Bool :=
  if a = 0 ∨ a = 5 then false
  else if a = 1 then !axis
  else if a = 2 then axis
  else true

def h7Cost (axis : Bool) (w : h7Col) := (h7Uses axis w.1 || h7Uses axis w.2).toNat

lemma h7Blend_good : ∀ (s : Bool) (u v : h7Col), h7Good u → h7Good v →
    (∀ t : Bool, h7Cost t u + h7Cost t v ≤ 1) → h7Good (h7Blend s u v) := by decide +kernel

lemma h7Blend_cost : ∀ (s t : Bool) (u v : h7Col),
    h7Cost t (h7Blend s u v) ≤ h7Cost t u + h7Cost t v := by decide +kernel

def h7Observe (p q : Bool) (a : h7Atom) : Bool :=
  if a = 0 then false
  else if a = 1 then p
  else if a = 2 then q
  else if a = 3 then p && q
  else if a = 4 then p || q
  else true

def h7View (s p q : Bool) (w : h7Col) : Bool := h7Observe p q (if s then w.2 else w.1)

lemma h7Blend_view : ∀ (b s p q : Bool) (u v : h7Col),
    h7View s p q (h7Blend b u v) =
      if b then h7View s p q u || h7View s p q v else h7View s p q u && h7View s p q v := by decide +kernel

lemma h7Distinguish : ∀ w : h7Col, (∀ s p q, h7View s p q w = h7View s p q h7GoalCol) → w = h7GoalCol := by
  decide +kernel

def h7Bin (h7Op : Bool) (a b : Nat) : Gate := ⟨if h7Op then .or else .and, [a,b]⟩

def h7Reads (gs : List Gate) (o : Nat) := gs.flatMap Gate.inputs ++ [o]

def h7Need (t : Bool) (w : List h7Col) (rs : List Nat) : Nat :=
  (rs.map fun j => h7Cost t (w.getD j h7Dead)).sum

lemma h7Need_cons (t : Bool) (w : List h7Col) (a : Nat) (rs : List Nat) :
    h7Need t w (a::rs) = h7Cost t (w.getD a h7Dead) + h7Need t w rs := rfl

lemma h7Snoc_eq (w : List h7Col) (v : h7Col) : (w ++ [v]).getD w.length h7Dead = v := by
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

lemma h7Snoc_ne (w : List h7Col) (v : h7Col) (j : Nat) (hn : j ≠ w.length) :
    (w ++ [v]).getD j h7Dead = w.getD j h7Dead := by
  by_cases h : j < w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma h7Need_snoc (t : Bool) (w : List h7Col) (v : h7Col) (rs : List Nat) :
    h7Need t (w ++ [v]) rs ≤ h7Need t w rs + rs.count w.length * h7Cost t v := by
  induction rs with
  | nil => simp [h7Need]
  | cons j rs ih =>
    rw [h7Need_cons, h7Need_cons, List.count_cons]
    by_cases h : j = w.length
    · subst j
      rw [h7Snoc_eq]
      simp only [beq_self_eq_true, ite_true, Nat.add_mul, Nat.one_mul]
      omega
    · rw [h7Snoc_ne _ _ _ h]
      simp [h]
      omega

def h7GateCol (g : Gate) (w : List h7Col) : h7Col :=
  let s := match g.op with | .or => true | _ => false
  h7Blend s (w.getD (g.inputs.getD 0 0) h7Dead) (w.getD (g.inputs.getD 1 0) h7Dead)

lemma h7Gate_bin (s : Bool) (a b : Nat) (w : List h7Col) :
    h7GateCol (h7Bin s a b) w = h7Blend s (w.getD a h7Dead) (w.getD b h7Dead) := by cases s <;> rfl

def h7Run : List Gate → List h7Col → List h7Col
  | [], w => w
  | g :: gs, w => h7Run gs (w ++ [h7GateCol g w])

lemma h7Flow (gs : List Gate) (o : Nat) (w : List h7Col)
    (binary : ∀ g ∈ gs, ∃ s a b, g = h7Bin s a b)
    (ok : ∀ i, h7Good (w.getD i h7Dead))
    (budget : ∀ t, h7Need t w (h7Reads gs o) ≤ 1)
    (single : ∀ j, w.length ≤ j → (h7Reads gs o).count j ≤ 1) :
    h7Good ((h7Run gs w).getD o h7Dead) := by
  induction gs generalizing w with
  | nil => exact ok o
  | cons g gs ih =>
    obtain ⟨s, a, b, rfl⟩ := binary g List.mem_cons_self
    let z := h7Blend s (w.getD a h7Dead) (w.getD b h7Dead)
    have reads_eq : h7Reads (h7Bin s a b :: gs) o = a :: b :: h7Reads gs o := by
      simp [h7Reads, h7Bin]
    have bounded (t : Bool) : h7Cost t (w.getD a h7Dead) + h7Cost t (w.getD b h7Dead) +
        h7Need t w (h7Reads gs o) ≤ 1 := by simpa only [reads_eq, h7Need_cons, Nat.add_assoc] using budget t
    have gz : h7Good z := h7Blend_good s _ _ (ok a) (ok b) (fun t => by have := bounded t; omega)
    have rest_count (j : Nat) (hj : w.length ≤ j) : (h7Reads gs o).count j ≤ 1 := by
      have h := single j hj
      rw [reads_eq, List.count_cons, List.count_cons] at h
      omega
    rw [h7Run, h7Gate_bin]
    apply ih (w := w ++ [z]) (fun g hg => binary g (List.mem_cons_of_mem _ hg))
    · intro i
      by_cases hi : i = w.length
      · subst i; rwa [h7Snoc_eq]
      · rw [h7Snoc_ne _ _ _ hi]; exact ok i
    · intro t
      have h := h7Need_snoc t w z (h7Reads gs o)
      have hc := Nat.mul_le_mul_right (h7Cost t z) (rest_count w.length le_rfl)
      simp only [Nat.one_mul] at hc
      have hcost : h7Cost t z ≤ h7Cost t (w.getD a h7Dead) + h7Cost t (w.getD b h7Dead) := h7Blend_cost s t _ _
      have hb := bounded t
      omega
    · intro j hj
      exact rest_count j (by simp at hj; omega)

lemma h7Read_view (w : List h7Col) (s p q : Bool) (j : Nat) :
    (w.map (h7View s p q)).getD j false = h7View s p q (w.getD j h7Dead) := by
  cases h : w[j]? <;> simp [List.getD, h, h7View, h7Dead, h7Observe]

def h7StepBool (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma h7One_view (w : List h7Col) (s p q b : Bool) (a d : Nat) :
    (w ++ [h7GateCol (h7Bin b a d) w]).map (h7View s p q) =
      h7StepBool (w.map (h7View s p q)) (h7Bin b a d) := by
  simp only [List.map_append, List.map_cons, List.map_nil, h7Gate_bin, h7Blend_view]
  rw [← h7Read_view, ← h7Read_view]
  cases b <;> simp [h7StepBool, h7Bin, GateOp.eval]

lemma h7Run_view (gs : List Gate) (w : List h7Col) (s p q : Bool)
    (hb : ∀ g ∈ gs, ∃ t a b, g = h7Bin t a b) :
    (h7Run gs w).map (h7View s p q) = gs.foldl h7StepBool (w.map (h7View s p q)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨t,a,b,rfl⟩ := hb g List.mem_cons_self
    rw [h7Run, List.foldl_cons, ih _ (fun g hg => hb g (List.mem_cons_of_mem _ hg)), h7One_view]

def h7Start : List h7Col :=
  [(5,5), (0,5), (0,5), (0,5), (1,1), h7Dead, (0,5), h7Dead, (2,2)]

def h7Assign (s p q : Bool) (i : Fin 9) := h7View s p q (h7Start.getD i.val h7Dead)

def h7Matching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

lemma h7Start_view : ∀ s p q, h7Start.map (h7View s p q) = List.ofFn (h7Assign s p q) := by decide

lemma h7Target : ∀ s p q, h7Matching (h7Assign s p q) = h7View s p q h7GoalCol := by decide

lemma h7Start_valid (i : Nat) : h7Good (h7Start.getD i h7Dead) := by
  by_cases h : i < 9
  · exact (by decide : ∀ i : Fin 9, h7Good (h7Start.getD i.val h7Dead)) ⟨i,h⟩
  · rw [List.getD_eq_default _ _ (by change 9 ≤ i; omega)]; decide

def h7Index (t : Bool) : Nat := if t then 8 else 4

lemma h7Start_cost (t : Bool) (j : Nat) : h7Cost t (h7Start.getD j h7Dead) = if j = h7Index t then 1 else 0 := by
  by_cases h : j < 9
  · exact (by decide : ∀ t (j : Fin 9), h7Cost t (h7Start.getD j.val h7Dead) =
      if j.val = h7Index t then 1 else 0) t ⟨j,h⟩
  · rw [List.getD_eq_default _ _ (by change 9 ≤ j; omega)]
    cases t <;> simp [h7Index, h7Cost, h7Dead, h7Uses] <;> omega

lemma h7Start_need (t : Bool) (rs : List Nat) : h7Need t h7Start rs = rs.count (h7Index t) := by
  induction rs with
  | nil => rfl
  | cons j rs ih =>
    rw [h7Need_cons, h7Start_cost, ih, List.count_cons]
    by_cases h : j = h7Index t <;> simp [h, Nat.add_comm]

lemma h7Impossible (C : Circuit)
    (hc : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = h7Matching x)
    (hb : ∀ g ∈ C.gates, ∃ t a b, g = h7Bin t a b)
    (h5 : (h7Reads C.gates C.output).count 4 ≤ 1) (h6 : (h7Reads C.gates C.output).count 8 ≤ 1)
    (hs : ∀ j, 9 ≤ j → (h7Reads C.gates C.output).count j ≤ 1) : False := by
  have hg := h7Flow C.gates C.output h7Start hb h7Start_valid (fun t => by
    rw [h7Start_need]; cases t <;> first | exact h5 | exact h6) hs
  apply hg.1
  apply h7Distinguish
  intro s p q
  rw [← h7Read_view, h7Run_view _ _ _ _ _ hb, h7Start_view]
  change C.eval (List.ofFn (h7Assign s p q)) = _
  rw [hc, h7Target]


open PEqualNP.CircuitLowerBounds

def h7OccTarget (x : Fin 9 → Bool) : Bool :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))

def h7OccFirst : Gate := ⟨.or, [0, 1]⟩

def h7OccSecond : Gate := ⟨.or, [3, 6]⟩

def h7OccProbe (m : ℕ) (i : Fin 9) : Bool := m.testBit i.val

lemma h7OccWitness (i : Fin 9) : ∃ x y : Fin 9 → Bool,
    h7OccTarget x ≠ h7OccTarget y ∧ (x 0 || x 1) = (y 0 || y 1) ∧
    (x 3 || x 6) = (y 3 || y 6) ∧ (∀ j, j ≠ i → x j = y j) := by
  refine ⟨h7OccProbe (![162, 97, 80, 196, 68, 66, 28, 12, 10] i),
    h7OccProbe (![163, 99, 84, 204, 84, 98, 92, 140, 266] i), ?_⟩
  fin_cases i <;> decide

def h7OccStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def h7OccAgree (a b : List Bool) (i : ℕ) : Prop :=
  a.length = b.length ∧ ∀ j, j ≠ i → a.getD j false = b.getD j false

lemma h7OccAppend {a b : List Bool} {i : ℕ} (h : h7OccAgree a b i) (z : Bool) :
    h7OccAgree (a ++ [z]) (b ++ [z]) i := by
  refine ⟨by simp [h.1], ?_⟩
  intro j hj
  by_cases hjl : j < a.length
  · rw [List.getD_append _ _ _ _ hjl, List.getD_append _ _ _ _ (h.1 ▸ hjl)]
    exact h.2 j hj
  · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by have := h.1; omega), h.1]

lemma h7OccFold (gs : List Gate) {i : ℕ} (hn : i ∉ gs.flatMap Gate.inputs)
    {a b : List Bool} (h : h7OccAgree a b i) :
    h7OccAgree (gs.foldl h7OccStep a) (gs.foldl h7OccStep b) i := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have hp : i ∉ g.inputs ∧ i ∉ gs.flatMap Gate.inputs := by simpa using hn
    have he : g.inputs.map (fun k => a.getD k false) = g.inputs.map (fun k => b.getD k false) := by
      apply List.map_congr_left
      intro k hk
      exact h.2 k (fun he => hp.1 (he ▸ hk))
    apply ih hp.2
    unfold h7OccStep
    rw [he]
    exact h7OccAppend h _

lemma h7OccInitial (x : Fin 9 → Bool) (j : ℕ) (hj : j < 9) :
    (List.ofFn x).getD j false = x ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_ofFn]

lemma h7OccPrefix (x : Fin 9 → Bool) :
    h7OccStep (h7OccStep (List.ofFn x) h7OccFirst) h7OccSecond =
      (List.ofFn x ++ [x 0 || x 1]) ++ [x 3 || x 6] := by
  simp [h7OccStep, h7OccFirst, h7OccSecond, GateOp.eval]

lemma h7OccTailInput (C : Circuit) (gs : List Gate) (hg : C.gates = h7OccFirst :: h7OccSecond :: gs)
    (hcomp : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = h7OccTarget x)
    (hout : C.output + 1 = 9 + C.size) (i : Fin 9) :
    i.val ∈ gs.flatMap Gate.inputs := by
  by_contra hn
  obtain ⟨x, y, hxy, h01, h38, hsame⟩ := h7OccWitness i
  have hbase : h7OccAgree (List.ofFn x) (List.ofFn y) i.val := by
    refine ⟨by simp, ?_⟩
    intro j hji
    by_cases hj : j < 9
    · rw [h7OccInitial x j hj, h7OccInitial y j hj]
      exact hsame _ (fun h => hji (congrArg Fin.val h))
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hpre : h7OccAgree (h7OccStep (h7OccStep (List.ofFn x) h7OccFirst) h7OccSecond)
      (h7OccStep (h7OccStep (List.ofFn y) h7OccFirst) h7OccSecond) i.val := by
    rw [h7OccPrefix, h7OccPrefix, h01, h38]
    exact h7OccAppend (h7OccAppend hbase _) _
  have ho : C.output ≠ i.val := by
    have hz : C.size = gs.length + 2 := by simp [Circuit.size, hg]
    have hi := i.isLt
    omega
  apply hxy
  rw [← hcomp, ← hcomp]
  change (C.gates.foldl h7OccStep (List.ofFn x)).getD C.output false =
    (C.gates.foldl h7OccStep (List.ofFn y)).getD C.output false
  rw [hg]
  exact (h7OccFold gs hn hpre).2 _ ho

lemma h7OccCap (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hh := hf g (by simp)
    have ht := ih (fun a ha => hf a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

lemma h7OccTight (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (he : (gs.flatMap Gate.inputs).length = 2 * gs.length) :
    ∀ g ∈ gs, g.inputs.length = 2 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hh := hf g (by simp)
    have ht : ∀ a ∈ gs, a.inputs.length ≤ 2 := fun a ha => hf a (by simp [ha])
    have hc := h7OccCap gs ht
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at he
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · exact ih ht (by omega) a ha

lemma h7OccSplit (C : Circuit) (h0 : C.gates.head? = some h7OccFirst)
    (h1 : C.gates.tail.head? = some h7OccSecond) :
    ∃ gs, C.gates = h7OccFirst :: h7OccSecond :: gs := by
  cases hg : C.gates with
  | nil => simp [hg] at h0
  | cons a t =>
    cases ht : t with
    | nil => simp [hg, ht] at h1
    | cons b gs =>
      have ha : a = h7OccFirst := by simpa [hg] using h0
      have hb : b = h7OccSecond := by simpa [hg, ht] using h1
      exact ⟨gs, by simp [ha, hb]⟩

lemma h7OccRigidTail (C : Circuit) (gs : List Gate) (hg : C.gates = h7OccFirst :: h7OccSecond :: gs)
    (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 12)
    (hout : C.output + 1 = 9 + C.size)
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (hinputs : ∀ i : Fin 9, i.val ∈ gs.flatMap Gate.inputs) :
    C.size = 12 ∧ (∀ g ∈ C.gates, g.inputs.length = 2) ∧
      (gs.flatMap Gate.inputs ++ [C.output]).Nodup := by
  let r := gs.flatMap Gate.inputs ++ [C.output]
  have hlen : C.size = gs.length + 2 := by simp [Circuit.size, hg]
  have hgs : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g hm => (hf g (by simp [hg, hm])).2
  have hsub : Finset.range (9 + C.size) ⊆ r.toFinset := by
    intro j hj
    have hb := Finset.mem_range.mp hj
    apply List.mem_toFinset.mpr
    by_cases hsmall : j < 9
    · exact List.mem_append_left _ (hinputs ⟨j, hsmall⟩)
    by_cases hlast : j = C.output
    · simp [r, hlast]
    have hidx : j - 9 < C.gates.length := by change j - 9 < C.size; omega
    let k : Fin C.gates.length := ⟨j - 9, hidx⟩
    have hjk : 9 + k.val = j := by dsimp [k]; omega
    have hnlast : k.val + 1 < C.gates.length := by change j - 9 + 1 < C.size; omega
    obtain ⟨n, _, hn⟩ := hlive k hnlast
    have hall : j ∈ C.gates.flatMap Gate.inputs :=
      List.mem_flatMap.mpr ⟨C.gates.get n, List.get_mem _ _, hjk ▸ hn⟩
    simp only [hg, List.flatMap_cons, h7OccFirst, h7OccSecond, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hall
    apply List.mem_append_left
    rcases hall with (h | h) | (h | h) | ha <;> omega
  have hcard : 9 + C.size ≤ r.toFinset.card := by
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hcl := List.toFinset_card_le r
  have hrl : r.length = (gs.flatMap Gate.inputs).length + 1 := by simp [r]
  have hc := h7OccCap gs hgs
  refine ⟨by omega, ?_, ?_⟩
  · intro g hm
    rw [hg] at hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rfl
    rcases List.mem_cons.mp hm with rfl | hm
    · rfl
    exact h7OccTight gs hgs (by omega) g hm
  · exact (Multiset.toFinset_card_eq_card_iff_nodup (m := (r : Multiset ℕ))).mp
      (show r.toFinset.card = r.length by omega)

lemma h7OccRigid (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 12)
    (hcomp : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = h7OccTarget x)
    (hout : C.output + 1 = 9 + C.size)
    (hnorm : ∀ j : Fin C.gates.length,
      ((C.gates.get j).op = GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b]))
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (h0 : C.gates.head? = some h7OccFirst) (h1 : C.gates.tail.head? = some h7OccSecond) :
    C.size = 12 ∧ (∀ g ∈ C.gates, ∃ a b : ℕ,
        g = ⟨GateOp.and, [a,b]⟩ ∨ g = ⟨GateOp.or, [a,b]⟩) ∧
      (C.gates.flatMap Gate.inputs ++ [C.output]).count 4 ≤ 1 ∧
      (C.gates.flatMap Gate.inputs ++ [C.output]).count 8 ≤ 1 ∧
      ∀ j : ℕ, 9 ≤ j → (C.gates.flatMap Gate.inputs ++ [C.output]).count j ≤ 1 := by
  obtain ⟨gs, hg⟩ := h7OccSplit C h0 h1
  obtain ⟨hsize, hlen, hnd⟩ := h7OccRigidTail C gs hg hf hs hout hlive
    (h7OccTailInput C gs hg hcomp hout)
  have he : C.gates.flatMap Gate.inputs ++ [C.output] =
      0 :: 1 :: 3 :: 6 :: (gs.flatMap Gate.inputs ++ [C.output]) := by
    simp [hg, h7OccFirst, h7OccSecond]
  have hu (j : ℕ) (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hj3 : j ≠ 3) (hj8 : j ≠ 6) :
      (C.gates.flatMap Gate.inputs ++ [C.output]).count j ≤ 1 := by
    rw [he]
    simpa [List.count_cons, Ne.symm hj0, Ne.symm hj1, Ne.symm hj3, Ne.symm hj8] using
      List.nodup_iff_count_le_one.mp hnd j
  refine ⟨hsize, ?_, hu 4 (by decide) (by decide) (by decide) (by decide),
    hu 8 (by decide) (by decide) (by decide) (by decide),
    fun j hj => hu j (by omega) (by omega) (by omega) (by omega)⟩
  intro g hm
  obtain ⟨n, hn⟩ := List.get_of_mem hm
  have hnrm := hnorm n
  rw [hn] at hnrm
  rcases hnrm with ⟨_, a, _, ha⟩ | ⟨hop, a, b, _, _, hp⟩
  · have hl := hlen g hm
    simp [ha] at hl
  · refine ⟨a, b, ?_⟩
    have heq : g = ⟨g.op, g.inputs⟩ := rfl
    rcases hop with hop | hop
    · left
      exact heq.trans (by rw [hop, hp])
    · right
      exact heq.trans (by rw [hop, hp])



end PEqualNP.Outside.L_meta_27759

open PEqualNP.Outside.L_meta_27759 in
theorem PEqualNP.Outside.L_meta_27759 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩) := by
  rintro ⟨C, hf, hs, hc, hout, hnorm, _, hlive, h0, h1⟩
  obtain ⟨_, hg, h4, h8, hi⟩ := h7OccRigid C hf hs hc hout hnorm hlive h0 h1
  apply h7Impossible C hc ?_ h4 h8 hi
  intro g hm
  obtain ⟨a, b, h | h⟩ := hg g hm
  · exact ⟨false, a, b, h⟩
  · exact ⟨true, a, b, h⟩
