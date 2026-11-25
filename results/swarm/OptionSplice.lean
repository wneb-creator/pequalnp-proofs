import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fin.Tuple.Sort

namespace PEqualNP.Outside.L_meta_5012

namespace CriticalEdge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
lemma dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

lemma ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

lemma ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (hs : s < n + gs.length) (ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

end CriticalEdge

namespace OptionSplice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open CriticalEdge


open Classical in
lemma dc_snoc_eq (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) = dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

open Classical in
lemma operation_build (n : ℕ) (F : (Fin n → Bool) → Bool)
    (gs : List Gate) (hok : Ok n gs) (A : Bool) (a b : Option ℕ)
    (ha : ∀ w, a = some w → w < n + gs.length)
    (hb : ∀ w, b = some w → w < n + gs.length)
    (f : (Fin n → Bool) → Bool)
    (hfun : ∀ x, f x = if A then ov gs (List.ofFn x) a && ov gs (List.ofFn x) b
      else ov gs (List.ofFn x) a || ov gs (List.ofFn x) b) :
    ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ 1 ∧
      (∀ w, o = some w → w < n + (gs ++ hs).length) ∧
      (∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o = f x) ∧
      dc n F (gs ++ hs) = dc n F gs + if A = true ∧
        ∃ x, f x = true ∧ F x = false then 1 else 0 := by
  cases a with
  | none =>
    cases A with
    | false =>
      refine ⟨[], b, by simpa using hok, by simp, by simpa using hb, ?_, by simp⟩
      intro x
      simpa [ov] using (hfun x).symm
    | true =>
      have hf : ∀ x, f x = false := by intro x; simpa [ov] using hfun x
      exact ⟨[], none, by simpa using hok, by simp, by simp,
        by intro x; simp [ov, hf], by simp [hf]⟩
  | some a =>
    cases b with
    | none =>
      cases A with
      | false =>
        refine ⟨[], some a, by simpa using hok, by simp, by simpa using ha, ?_, by simp⟩
        intro x
        simpa [ov] using (hfun x).symm
      | true =>
        have hf : ∀ x, f x = false := by intro x; simpa [ov] using hfun x
        exact ⟨[], none, by simpa using hok, by simp, by simp,
          by intro x; simp [ov, hf], by simp [hf]⟩
    | some b =>
      let op : GateOp := if A then GateOp.and else GateOp.or
      have hop : op = GateOp.and ∨ op = GateOp.or := by cases A <;> simp [op]
      have ha' := ha a rfl
      have hb' := hb b rfl
      have hv : ∀ x : Fin n → Bool,
          ov (gs ++ [⟨op, [a, b]⟩]) (List.ofFn x) (some (n + gs.length)) = f x := by
        intro x
        rw [ov_new gs n _ (by simp) op a b ha' hb', hfun x]
        cases A <;> simp [op, ov, GateOp.eval]
      refine ⟨[⟨op, [a, b]⟩], some (n + gs.length), ok_snoc hok hop ha' hb',
        by simp, by intro w hw; cases hw; simp, hv, ?_⟩
      rw [dc_snoc_eq]
      have he : (op = GateOp.and ∧ ∃ x : Fin n → Bool,
          (run (gs ++ [⟨op, [a, b]⟩]) (List.ofFn x)).getD (n + gs.length) false = true ∧
            F x = false) ↔ (A = true ∧ ∃ x, f x = true ∧ F x = false) := by
        have hv' : ∀ x : Fin n → Bool,
            (run (gs ++ [⟨op, [a, b]⟩]) (List.ofFn x)).getD (n + gs.length) false = f x := hv
        simp only [hv']
        cases A <;> simp [op]
      rw [if_congr he rfl rfl]

def Maps (n p : ℕ) (Del : Finset ℕ) (gs : List Gate) (m : ℕ → Option ℕ)
    (V : (Fin n → Bool) → ℕ → Bool) : Prop :=
  ∀ w < n + p, (w < n ∨ w - n ∉ Del) →
    (∀ z, m w = some z → z < n + gs.length) ∧
      ∀ x, ov gs (List.ofFn x) (m w) = V x w

open Classical in
lemma build_with_overrides (n N : ℕ) (F : (Fin n → Bool) → Bool)
    (A : ℕ → Bool) (a b : ℕ → ℕ) (S Del : Finset ℕ) (hDel : Del ⊆ S)
    (cost extra : ℕ → ℕ) (V : (Fin n → Bool) → ℕ → Bool)
    (P : List Gate) (hP : Ok n P)
    (hin : ∀ x w, w < n → V x w = (List.ofFn x).getD w false)
    (hback : ∀ j < N, a j < n + j ∧ b j < n + j)
    (havoid : ∀ j < N, j ∉ S →
      (a j < n ∨ a j - n ∉ Del) ∧ (b j < n ∨ b j - n ∉ Del))
    (hval : ∀ j < N, j ∉ S → ∀ x,
      V x (n + j) = if A j then V x (a j) && V x (b j) else V x (a j) || V x (b j))
    (block : ∀ j < N, j ∈ S → ∀ (gs : List Gate) (m : ℕ → Option ℕ),
      Ok n gs → (∃ tail, gs = P ++ tail) → Maps n j Del gs m V →
      ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
        (∀ w, o = some w → w < n + (gs ++ hs).length) ∧
        (j ∉ Del → ∀ x, ov (gs ++ hs) (List.ofFn x) o = V x (n + j)) ∧
        hs.length ≤ cost j ∧ dc n F (gs ++ hs) = dc n F gs + extra j) :
    ∀ p, p ≤ N → ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∃ tail, gs = P ++ tail) ∧ Maps n p Del gs m V ∧
      gs.length + ((Finset.range p).filter (· ∈ S)).card ≤
        P.length + p + (∑ j ∈ Finset.range p, if j ∈ S then cost j else 0) ∧
      dc n F gs = dc n F P + (∑ j ∈ Finset.range p, if j ∈ S then extra j else 0) +
        ((Finset.range p).filter fun j =>
        j ∉ S ∧ A j = true ∧ ∃ x, V x (n + j) = true ∧ F x = false).card := by
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨P, some, hP, ⟨[], by simp⟩, ?_, by simp, by simp⟩
    intro w hw _
    refine ⟨by intro z hz; cases hz; omega, fun x => ?_⟩
    rw [hin x w (by omega)]
    exact run_input P (List.ofFn x) w (by simpa using hw)
  | succ p ih =>
    intro hpN
    obtain ⟨gs, m, hok, hprefix, hm, hsize, hdirty⟩ := ih (by omega)
    have hp : p < N := by omega
    suffices hh : ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
        (∀ w, o = some w → w < n + (gs ++ hs).length) ∧
        (p ∉ Del → ∀ x, ov (gs ++ hs) (List.ofFn x) o = V x (n + p)) ∧
        hs.length + (if p ∈ S then 1 else 0) ≤ 1 + (if p ∈ S then cost p else 0) ∧
        dc n F (gs ++ hs) = dc n F gs + (if p ∈ S then extra p else 0) +
          if p ∉ S ∧ A p = true ∧ ∃ x, V x (n + p) = true ∧ F x = false
            then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · obtain ⟨tail, rfl⟩ := hprefix
        exact ⟨tail ++ hs, by simp only [List.append_assoc]⟩
      · intro w hw hvalid
        by_cases hwp : w = n + p
        · subst w
          rw [Function.update_self]
          have hpD : p ∉ Del := by simpa using hvalid
          exact ⟨h2, h3 hpD⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨hb, hv⟩ := hm w (by omega) hvalid
          refine ⟨fun z hz => by have := hb z hz; simp only [List.length_append]; omega,
            fun x => ?_⟩
          rw [ov_ext gs hs _ _ (by simpa using hb), hv x]
      · rw [Finset.range_add_one, Finset.filter_insert, Finset.sum_insert (by simp),
          List.length_append]
        by_cases hpS : p ∈ S
        · rw [ite_eq_left hpS, Finset.card_insert_of_notMem (by simp)]
          simp only [hpS, ↓reduceIte] at h4 ⊢
          omega
        · simp only [hpS, ↓reduceIte] at h4 ⊢
          omega
      · rw [Finset.range_add_one, Finset.filter_insert, Finset.sum_insert (by simp), h5, hdirty]
        split_ifs with h h2 <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;> omega
    by_cases hpS : p ∈ S
    · obtain ⟨hs, o, h1, h2, h3, h4, h5⟩ := block p hp hpS gs m hok hprefix hm
      refine ⟨hs, o, h1, h2, h3, ?_, ?_⟩
      · simp only [hpS, ↓reduceIte]; omega
      · simpa [hpS] using h5
    have hpD : p ∉ Del := fun h => hpS (hDel h)
    obtain ⟨hab, hbb⟩ := hback p hp
    obtain ⟨haValid, hbValid⟩ := havoid p hp hpS
    obtain ⟨haBound, haValue⟩ := hm (a p) hab haValid
    obtain ⟨hbBound, hbValue⟩ := hm (b p) hbb hbValid
    obtain ⟨hs, o, h1, h2, h3, h4, h5⟩ := operation_build n F gs hok (A p)
      (m (a p)) (m (b p)) haBound hbBound (fun x => V x (n + p)) (by
        intro x
        rw [hval p hp hpS x, haValue x, hbValue x])
    exact ⟨hs, o, h1, h3, fun _ => h4, by simpa [hpS] using h2,
      by simpa [hpS] using h5⟩

lemma or_list_build (n : ℕ) (gs : List Gate) (hgs : Ok n gs) :
    ∀ l : List ℕ, (∀ w ∈ l, w < n + gs.length) →
    ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
      hs.length = l.length - 1 ∧ (∀ g ∈ hs, g.op = GateOp.or) ∧
      (o = none ↔ l = []) ∧ (∀ w, o = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : List Bool, x.length = n →
        ov (gs ++ hs) x o = l.any (fun w => (run gs x).getD w false) := by
  intro l
  induction l with
  | nil =>
    intro _
    exact ⟨[], none, by simpa using hgs, by simp, by simp, by simp, by simp,
      fun x hx => by simp [ov]⟩
  | cons a l ih =>
    intro hl
    have ha : a < n + gs.length := hl a (by simp)
    obtain ⟨hs, o, hok, hlen, hops, hnone, ho, hval⟩ := ih (fun w hw => hl w (by simp [hw]))
    cases o with
    | none =>
      have hl0 : l = [] := hnone.mp rfl
      subst l
      refine ⟨[], some a, by simpa using hgs, by simp, by simp, by simp,
        by intro w hw; cases hw; simpa using ha, ?_⟩
      intro x hx
      simp [ov]
    | some b =>
      have hb := ho b rfl
      have hlne : l ≠ [] := by intro h; have hh := hnone.mpr h; cases hh
      have hlpos : 0 < l.length := List.length_pos_iff.mpr hlne
      let g : Gate := ⟨GateOp.or, [a, b]⟩
      have hok' : Ok n ((gs ++ hs) ++ [g]) :=
        ok_snoc hok (Or.inr rfl) (by simp only [List.length_append]; omega) hb
      refine ⟨hs ++ [g], some (n + (gs ++ hs).length), by simpa only [List.append_assoc] using hok',
        by simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]; omega,
        ?_, by simp, ?_, ?_⟩
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hops q hq
        · have hqg : q = g := by simpa using hq
          subst q
          rfl
      · intro w hw
        cases hw
        simp only [List.length_append, List.length_singleton]
        omega
      · intro x hx
        have hkeep : (run (gs ++ hs) x).getD a false = (run gs x).getD a false :=
          run_prefix gs hs x a (by simpa only [hx] using ha)
        have ht := hval x hx
        simp only [ov] at ht
        rw [← List.append_assoc, ov_new (gs ++ hs) n x hx GateOp.or a b
          (by simp only [List.length_append]; omega) hb, hkeep, ht]
        simp [g, GateOp.eval]

lemma dc_append_or (n : ℕ) (F : (Fin n → Bool) → Bool) (gs hs : List Gate)
    (hOR : ∀ g ∈ hs, g.op = GateOp.or) : dc n F (gs ++ hs) = dc n F gs := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, dc_snoc_eq]
    have hg : g.op = GateOp.or := hOR g (by simp)
    have hi := ih (fun k hk => hOR k (by simp [hk]))
    simp [hg, hi]

lemma or_mapped_build (n : ℕ) (F : (Fin n → Bool) → Bool)
    (gs : List Gate) (hok : Ok n gs) (l : List ℕ) (m : ℕ → Option ℕ)
    (V : (Fin n → Bool) → ℕ → Bool)
    (hm : ∀ w ∈ l, (∀ z, m w = some z → z < n + gs.length) ∧
      ∀ x, ov gs (List.ofFn x) (m w) = V x w) :
    ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ l.length - 1 ∧
      (∀ w, o = some w → w < n + (gs ++ hs).length) ∧
      (∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o =
        decide (∃ w ∈ l, V x w = true)) ∧ dc n F (gs ++ hs) = dc n F gs := by
  classical
  have hb : ∀ z ∈ l.filterMap m, z < n + gs.length := by
    intro z hz
    obtain ⟨w, hw, heq⟩ := List.mem_filterMap.mp hz
    exact (hm w hw).1 z heq
  obtain ⟨hs, o, h1, h2, h3, _, h4, h5⟩ := or_list_build n gs hok (l.filterMap m) hb
  have hlenmap : ∀ q : List ℕ, (q.filterMap m).length ≤ q.length := by
    intro q
    induction q with
    | nil => simp
    | cons a q ih =>
      cases hm' : m a with
      | none => simpa [List.filterMap_cons, hm'] using (Nat.le_succ_of_le ih)
      | some z => simpa [List.filterMap_cons, hm'] using (Nat.succ_le_succ ih)
  have hlen := hlenmap l
  refine ⟨hs, o, h1, by omega, h4, ?_, dc_append_or n F gs hs h3⟩
  intro x
  rw [h5 (List.ofFn x) (by simp)]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨z, hz, hv⟩
    obtain ⟨w, hw, heq⟩ := List.mem_filterMap.mp hz
    refine ⟨w, hw, ?_⟩
    rw [← (hm w hw).2 x, heq]
    exact hv
  · rintro ⟨w, hw, hv⟩
    have hmval := (hm w hw).2 x
    cases heq : m w with
    | none =>
      rw [heq] at hmval
      simp only [ov] at hmval
      rw [hv] at hmval
      cases hmval
    | some z =>
      refine ⟨z, List.mem_filterMap.mpr ⟨w, hw, heq⟩, ?_⟩
      rw [heq] at hmval
      exact hmval.trans hv

open Classical in
lemma and_mapped_or_build (n : ℕ) (F : (Fin n → Bool) → Bool)
    (gs : List Gate) (hok : Ok n gs) (l : List ℕ) (m : ℕ → Option ℕ)
    (V : (Fin n → Bool) → ℕ → Bool) (b : ℕ) (f : (Fin n → Bool) → Bool)
    (hm : ∀ w ∈ l, (∀ z, m w = some z → z < n + gs.length) ∧
      ∀ x, ov gs (List.ofFn x) (m w) = V x w)
    (hb : (∀ z, m b = some z → z < n + gs.length) ∧
      ∀ x, ov gs (List.ofFn x) (m b) = V x b)
    (hfun : ∀ x, f x = (decide (∃ w ∈ l, V x w = true) && V x b)) :
    ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ (l.length - 1) + 1 ∧
      (∀ w, o = some w → w < n + (gs ++ hs).length) ∧
      (∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o = f x) ∧
      dc n F (gs ++ hs) = dc n F gs + if ∃ x, f x = true ∧ F x = false then 1 else 0 := by
  obtain ⟨hs, o, h1, h2, h3, h4, h5⟩ := or_mapped_build n F gs hok l m V hm
  have hb' : ∀ z, m b = some z → z < n + (gs ++ hs).length := by
    intro z hz
    have := hb.1 z hz
    simp only [List.length_append]
    omega
  obtain ⟨ts, q, t1, t2, t3, t4, t5⟩ := operation_build n F (gs ++ hs) h1 true o
    (m b) h3 hb' f (by
      intro x
      simp only [↓reduceIte]
      rw [hfun x, h4 x, ov_ext gs hs _ _ (by simpa using hb.1), hb.2 x])
  refine ⟨hs ++ ts, q, by simpa only [List.append_assoc] using t1,
    by simp only [List.length_append]; omega, ?_, ?_, ?_⟩
  · simpa only [List.append_assoc] using t3
  · simpa only [List.append_assoc] using t4
  · rw [← List.append_assoc, t5, h5]
    simp

lemma small_raw_option (n : ℕ) (P : List Gate) (S : Finset (Fin n))
    (hS : S.card ≤ 1) :
    ∃ o : Option ℕ, (∀ w, o = some w → w < n + P.length) ∧
      ∀ x : Fin n → Bool, ov P (List.ofFn x) o = decide (∃ u ∈ S, x u = true) := by
  classical
  by_cases he : S = ∅
  · exact ⟨none, by simp, by intro x; simp [ov, he]⟩
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hsingle : S = {a} := by
    apply Finset.ext
    intro b
    constructor
    · intro hb
      have hba : b = a := Finset.card_le_one.mp hS b hb a ha
      simp [hba]
    · intro hb
      have hba : b = a := by simpa using hb
      simpa [hba] using ha
  refine ⟨some a.val, by intro w hw; cases hw; have := a.isLt; omega, ?_⟩
  intro x
  rw [ov, run_input P (List.ofFn x) a.val (by simpa using a.isLt)]
  simp [hsingle, List.getD_eq_getElem?_getD]

lemma center_prefix (n : ℕ) (F : (Fin n → Bool) → Bool)
    (Z : Finset (Fin n)) (hZ : Z.card ≤ 2) :
    ∃ P : List Gate, Ok n P ∧ P.length = Z.card - 1 ∧ dc n F P = 0 ∧
      ∀ S : Finset (Fin n), S ⊆ Z → ∃ o : Option ℕ,
        (∀ w, o = some w → w < n + P.length) ∧
        ∀ x : Fin n → Bool, ov P (List.ofFn x) o = decide (∃ u ∈ S, x u = true) := by
  classical
  let l := Z.toList.map Fin.val
  have hl : ∀ w ∈ l, w < n + ([] : List Gate).length := by
    intro w hw
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hw
    exact u.isLt
  obtain ⟨P, o, hp, hlen, hOR, _, ho, hov⟩ := or_list_build n [] (by intro j hj; simp at hj) l hl
  have hP : Ok n P := by simpa using hp
  have heval : ∀ x : Fin n → Bool, ov P (List.ofFn x) o = decide (∃ u ∈ Z, x u = true) := by
    intro x
    have hh := hov (List.ofFn x) (by simp)
    simp only [List.nil_append] at hh
    rw [hh]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨w, hw, hv⟩
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      refine ⟨u, by simpa using hu, ?_⟩
      simpa [run, List.getD_eq_getElem?_getD] using hv
    · rintro ⟨u, hu, hv⟩
      refine ⟨u.val, List.mem_map.mpr ⟨u, by simpa using hu, rfl⟩, ?_⟩
      simpa [run, List.getD_eq_getElem?_getD] using hv
  refine ⟨P, hP, by simpa [l] using hlen, ?_, ?_⟩
  · have hd := dc_append_or n F [] P hOR
    simpa [dc] using hd
  · intro S hsub
    by_cases hEq : S = Z
    · subst S
      exact ⟨o, by simpa using ho, heval⟩
    · have hS : S.card ≤ 1 := by
        by_contra hn
        have hcard : Z.card ≤ S.card := by omega
        exact hEq (Finset.eq_of_subset_of_card_le hsub hcard)
      exact small_raw_option n P S hS

open Classical in
lemma compile_center_cut (n N : ℕ) (F : (Fin n → Bool) → Bool)
    (A : ℕ → Bool) (a b : ℕ → ℕ) (J Del : Finset ℕ) (hDel : Del ⊆ J)
    (h : ℕ) (hh : h < N) (hhJ : h ∉ J) (hJ : ∀ j ∈ J, j < N)
    (Z : Finset (Fin n)) (hZ : Z.card ≤ 2) (proj : ℕ → Finset (Fin n))
    (hproj : ∀ j ∈ J, proj j ⊆ Z)
    (good : List ℕ) (other : ℕ) (V : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ x w, w < n → V x w = (List.ofFn x).getD w false)
    (hback : ∀ j < N, a j < n + j ∧ b j < n + j)
    (havoid : ∀ j < N, j ∉ insert h J →
      (a j < n ∨ a j - n ∉ Del) ∧ (b j < n ∨ b j - n ∉ Del))
    (hval : ∀ j < N, j ∉ insert h J → ∀ x,
      V x (n + j) = if A j then V x (a j) && V x (b j) else V x (a j) || V x (b j))
    (hcut : ∀ j ∈ J, j ∉ Del → ∀ x,
      V x (n + j) = decide (∃ u ∈ proj j, x u = true))
    (hgood : ∀ w ∈ good, w < n + h ∧ (w < n ∨ w - n ∉ Del))
    (hother : other < n + h ∧ (other < n ∨ other - n ∉ Del))
    (hhval : ∀ x, V x (n + h) = (decide (∃ w ∈ good, V x w = true) && V x other)) :
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧ Maps n N Del gs m V ∧
      gs.length + J.card ≤ N + (Z.card - 1) + (good.length - 1) ∧
      dc n F gs = (if ∃ x, V x (n + h) = true ∧ F x = false then 1 else 0) +
        ((Finset.range N).filter fun j => j ∉ insert h J ∧ A j = true ∧
          ∃ x, V x (n + j) = true ∧ F x = false).card := by
  let cost : ℕ → ℕ := fun j => if j = h then (good.length - 1) + 1 else 0
  let extra : ℕ → ℕ := fun j => if j = h then
    (if ∃ x, V x (n + h) = true ∧ F x = false then 1 else 0) else 0
  obtain ⟨P, hP, hPlen, hPdirty, hPproxy⟩ := center_prefix n F Z hZ
  have hDel' : Del ⊆ insert h J := fun j hj => Finset.mem_insert_of_mem (hDel hj)
  have block : ∀ j < N, j ∈ insert h J → ∀ (gs : List Gate) (m : ℕ → Option ℕ),
      Ok n gs → (∃ tail, gs = P ++ tail) → Maps n j Del gs m V →
      ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
        (∀ w, o = some w → w < n + (gs ++ hs).length) ∧
        (j ∉ Del → ∀ x, ov (gs ++ hs) (List.ofFn x) o = V x (n + j)) ∧
        hs.length ≤ cost j ∧ dc n F (gs ++ hs) = dc n F gs + extra j := by
    intro j hj hjS gs m hok hprefix hm
    by_cases hjh : j = h
    · subst j
      have hmGood : ∀ w ∈ good, (∀ z, m w = some z → z < n + gs.length) ∧
          ∀ x, ov gs (List.ofFn x) (m w) = V x w := by
        intro w hw
        exact hm w (hgood w hw).1 (hgood w hw).2
      obtain ⟨hs, o, h1, h2, h3, h4, h5⟩ := and_mapped_or_build n F gs hok good m V other
        (fun x => V x (n + h)) hmGood (hm other hother.1 hother.2) hhval
      exact ⟨hs, o, h1, h3, fun _ => h4, by simpa [cost] using h2,
        by simpa [extra] using h5⟩
    · have hjJ : j ∈ J := (Finset.mem_insert.mp hjS).resolve_left hjh
      by_cases hjD : j ∈ Del
      · exact ⟨[], none, by simpa using hok, by simp,
          fun hn => False.elim (hn hjD), by simp [cost, hjh], by simp [extra, hjh]⟩
      · obtain ⟨o, ho, hov⟩ := hPproxy (proj j) (hproj j hjJ)
        obtain ⟨tail, hgs⟩ := hprefix
        refine ⟨[], o, by simpa using hok, ?_, ?_, by simp [cost, hjh], by simp [extra, hjh]⟩
        · intro w hw
          have := ho w hw
          simp only [List.length_append, List.length_nil, Nat.add_zero]
          rw [hgs, List.length_append]
          omega
        · intro _ x
          simp only [List.append_nil]
          rw [hgs, ov_ext P tail _ _ (by simpa using ho), hov x, hcut j hjJ hjD x]
  obtain ⟨gs, m, hok, _, hm, hsize, hdirty⟩ := build_with_overrides n N F A a b
    (insert h J) Del hDel' cost extra V P hP hin hback havoid hval block N le_rfl
  have hfilter : (Finset.range N).filter (· ∈ insert h J) = insert h J := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact And.right
    · intro hj
      refine ⟨?_, hj⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hh
      · exact hJ j hj
  have hsum (f : ℕ → ℕ) (hf : ∀ j, j ≠ h → f j = 0) :
      (∑ j ∈ Finset.range N, if j ∈ insert h J then f j else 0) = f h := by
    rw [Finset.sum_eq_single h]
    · simp
    · intro j _ hj
      simp [hf j hj]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr hh))
  have hcost := hsum cost (by intro j hj; simp [cost, hj])
  have hextra := hsum extra (by intro j hj; simp [extra, hj])
  rw [hfilter, Finset.card_insert_of_notMem hhJ, hcost, hPlen] at hsize
  rw [hPdirty, hextra] at hdirty
  refine ⟨gs, m, hok, hm, ?_, ?_⟩
  · simp only [cost, ↓reduceIte] at hsize
    omega
  · simpa [extra] using hdirty

lemma ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; exact h2
  · intro j hj i hi
    obtain ⟨o', s', t', h1, h2, h3, h4⟩ := hok j hj
    have e1 : gateAt ⟨gs, w⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e1, h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; rfl

def outputWire (n : ℕ) (gs : List Gate) (o : Option ℕ) : ℕ :=
  o.getD (n + gs.length)

lemma outputWire_eval (n : ℕ) (gs : List Gate) (o : Option ℕ) (x : List Bool)
    (hx : x.length = n) :
    (⟨gs, outputWire n gs o⟩ : Circuit).eval x = ov gs x o := by
  cases o with
  | none =>
    change (run gs x).getD (n + gs.length) false = false
    exact List.getD_eq_default _ _ (by rw [run_length, hx])
  | some w => rfl

lemma dc_eq_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (out : ℕ) :
    dc n (graphFun G ∅) gs = (TopForm.junk G (⟨gs, out⟩ : Circuit)).card := by
  classical
  unfold dc TopForm.junk TopForm.gatesWhere
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' : j < gs.length := Finset.mem_range.mp hj
  simp only [PEqualNP.CleanedNonEdge.IsDirtyAnd, PEqualNP.CleanedNonEdge.IsDirty,
    gateAt, PEqualNP.EdgeOwnership.gateVal, Circuit.wires, run, hj', true_and]

lemma realize_mapped_circuit (n N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Del : Finset ℕ) (gs : List Gate) (m : ℕ → Option ℕ)
    (V : (Fin n → Bool) → ℕ → Bool) (hok : Ok n gs) (hm : Maps n N Del gs m V)
    (out : ℕ) (hout : out < n + N) (hvalid : out < n ∨ out - n ∉ Del) :
    ∃ D : Circuit, TopForm.IsAO2 n D ∧ D.size = gs.length ∧
      circuitFun n D = (fun x => V x out) ∧ (TopForm.junk G D).card = dc n (graphFun G ∅) gs := by
  let D : Circuit := ⟨gs, outputWire n gs (m out)⟩
  refine ⟨D, ok_ao hok, rfl, ?_, (dc_eq_junk G gs _).symm⟩
  funext x
  change D.eval (List.ofFn x) = V x out
  rw [outputWire_eval n gs (m out) (List.ofFn x) (by simp)]
  exact (hm out hout hvalid).2 x

end OptionSplice
end PEqualNP.Outside.L_meta_5012
