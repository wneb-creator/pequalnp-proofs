import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5187

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def evalOpt (w : List Bool) : Option (Option ℕ) → Bool
  | none => false
  | some none => true
  | some (some i) => w.getD i false

def extractWires : List (Option (Option ℕ)) → List ℕ
  | [] => []
  | some (some a) :: t => a :: extractWires t
  | _ :: t => extractWires t

def zeroStep (n : ℕ) (st : List (Option (Option ℕ)) × List Gate) (g : Gate) :
    List (Option (Option ℕ)) × List Gate :=
  let wmap := st.1
  let ng := st.2
  let ins := g.inputs.map fun i => wmap.getD i none
  match g.op with
  | GateOp.and =>
    if ins.any (fun o => o.isNone) then
      (wmap ++ [none], ng)
    else
      match extractWires ins with
      | [] => (wmap ++ [some none], ng)
      | [a] => (wmap ++ [some (some a)], ng)
      | a :: b :: _ => (wmap ++ [some (some (n + ng.length))], ng ++ [⟨GateOp.and, [a, b]⟩])
  | GateOp.or =>
    if ins.any (fun o => match o with | some none => true | _ => false) then
      (wmap ++ [some none], ng)
    else
      match extractWires ins with
      | [] => (wmap ++ [none], ng)
      | [a] => (wmap ++ [some (some a)], ng)
      | a :: b :: _ => (wmap ++ [some (some (n + ng.length))], ng ++ [⟨GateOp.or, [a, b]⟩])
  | _ => (wmap ++ [none], ng)

lemma extractWires_len_le : ∀ l : List (Option (Option ℕ)),
    (extractWires l).length ≤ l.length
  | [] => by simp [extractWires]
  | none :: t => by simp only [extractWires, List.length_cons]; have := extractWires_len_le t; omega
  | some none :: t => by simp only [extractWires, List.length_cons]; have := extractWires_len_le t; omega
  | some (some a) :: t => by simp only [extractWires, List.length_cons]; have := extractWires_len_le t; omega

lemma extractWires_len_lt_of_none : ∀ l : List (Option (Option ℕ)),
    none ∈ l → (extractWires l).length + 1 ≤ l.length
  | [], h => by simp at h
  | none :: t, _ => by simp only [extractWires, List.length_cons]; have := extractWires_len_le t; omega
  | some none :: t, h => by
    simp only [List.mem_cons, reduceCtorEq, false_or] at h
    simp only [extractWires, List.length_cons]; have := extractWires_len_lt_of_none t h; omega
  | some (some a) :: t, h => by
    simp only [List.mem_cons, reduceCtorEq, false_or] at h
    simp only [extractWires, List.length_cons]; have := extractWires_len_lt_of_none t h; omega

lemma evalOpt_and_step (w : List Bool) (ins : List (Option (Option ℕ))) (hl : ins.length ≤ 2) :
    (ins.map (evalOpt w)).all id =
      if ins.any (fun o => o.isNone) then false
      else match extractWires ins with
        | [] => true
        | [a] => w.getD a false
        | a :: b :: _ => w.getD a false && w.getD b false := by
  cases ins with
  | nil => simp [extractWires]
  | cons o1 t1 =>
    cases t1 with
    | nil =>
      rcases o1 with _ | (_ | a) <;> simp [evalOpt, extractWires]
    | cons o2 t2 =>
      cases t2 with
      | nil =>
        rcases o1 with _ | (_ | a) <;> rcases o2 with _ | (_ | b) <;> simp [evalOpt, extractWires]
      | cons o3 t3 =>
        simp at hl

lemma evalOpt_or_step (w : List Bool) (ins : List (Option (Option ℕ))) (hl : ins.length ≤ 2) :
    (ins.map (evalOpt w)).any id =
      if ins.any (fun o => match o with | some none => true | _ => false) then true
      else match extractWires ins with
        | [] => false
        | [a] => w.getD a false
        | a :: b :: _ => w.getD a false || w.getD b false := by
  cases ins with
  | nil => simp [extractWires]
  | cons o1 t1 =>
    cases t1 with
    | nil =>
      rcases o1 with _ | (_ | a) <;> simp [evalOpt, extractWires]
    | cons o2 t2 =>
      cases t2 with
      | nil =>
        rcases o1 with _ | (_ | a) <;> rcases o2 with _ | (_ | b) <;> simp [evalOpt, extractWires]
      | cons o3 t3 =>
        simp at hl

lemma mem_extractWires_of_mem : ∀ {a : ℕ} {l : List (Option (Option ℕ))},
    a ∈ extractWires l → some (some a) ∈ l
  | _, [], h => by simp [extractWires] at h
  | a, none :: t, h => List.mem_cons_of_mem _ (mem_extractWires_of_mem h)
  | a, some none :: t, h => List.mem_cons_of_mem _ (mem_extractWires_of_mem h)
  | a, some (some b) :: t, h => by
    simp only [extractWires, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (mem_extractWires_of_mem h)

lemma zeroStep_inv (n : ℕ) (st : List (Option (Option ℕ)) × List Gate) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hm : ∀ g' ∈ st.2, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2)
    (hbd : ∀ a, some (some a) ∈ st.1 → a < n + st.2.length) :
    let st' := zeroStep n st g
    st'.1.length = st.1.length + 1 ∧
    st'.2.length ≤ st.2.length + 1 ∧
    (∀ k, k < st.1.length → st.1.getD k none = none → st'.1.getD k none = none ∧ (k ∈ g.inputs → st'.2.length = st.2.length)) ∧
    (∀ g' ∈ st'.2, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2) ∧
    (∀ a, some (some a) ∈ st'.1 → a < n + st'.2.length) ∧
    (∀ (x : Fin n → Bool) (oldW : List Bool),
      oldW.length = st.1.length →
      (∀ i, evalOpt (wiresFrom st.2 (List.ofFn x)) (st.1.getD i none) = oldW.getD i false) →
      ∀ i, evalOpt (wiresFrom st'.2 (List.ofFn x)) (st'.1.getD i none) =
        (oldW ++ [g.op.eval (g.inputs.map fun j => oldW.getD j false)]).getD i false) := by
  have hins_mem : ∀ a, a ∈ extractWires (g.inputs.map fun i => st.1.getD i none) →
      a < n + st.2.length := by
    intro a ha
    have hm1 := mem_extractWires_of_mem ha
    rw [List.mem_map] at hm1
    obtain ⟨i, _, hi⟩ := hm1
    have hlt : i < st.1.length := by
      by_contra hge
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hge)] at hi
      cases hi
    rw [List.getD_eq_getElem _ _ hlt] at hi
    exact hbd a (hi ▸ List.getElem_mem hlt)
  have hk_none : ∀ k, st.1.getD k none = none → k ∈ g.inputs →
      none ∈ g.inputs.map (fun i => st.1.getD i none) := by
    intro k hgk hk
    exact List.mem_map.2 ⟨k, hk, hgk⟩
  have hkeep_all : ∀ (x : Fin n → Bool) (oldW : List Bool) (v : Option (Option ℕ)) (add : List Gate),
      oldW.length = st.1.length →
      (∀ i, evalOpt (wiresFrom st.2 (List.ofFn x)) (st.1.getD i none) = oldW.getD i false) →
      evalOpt (wiresFrom (st.2 ++ add) (List.ofFn x)) v =
        g.op.eval (g.inputs.map fun j => oldW.getD j false) →
      ∀ i, evalOpt (wiresFrom (st.2 ++ add) (List.ofFn x)) ((st.1 ++ [v]).getD i none) =
        (oldW ++ [g.op.eval (g.inputs.map fun j => oldW.getD j false)]).getD i false := by
    intro x oldW v add hol hev hv i
    by_cases hi : i < st.1.length
    · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hol.symm ▸ hi)]
      have hpre : evalOpt (wiresFrom (st.2 ++ add) (List.ofFn x)) (st.1.getD i none) =
          evalOpt (wiresFrom st.2 (List.ofFn x)) (st.1.getD i none) := by
        cases ho : st.1.getD i none with
        | none => rfl
        | some o =>
          cases o with
          | none => rfl
          | some a =>
            have ha : a < n + st.2.length := by
              rw [List.getD_eq_getElem _ _ hi] at ho
              exact hbd a (ho ▸ List.getElem_mem hi)
            simp only [evalOpt, wiresFrom_append]
            exact prefix_val add _ a (by rw [wiresFrom_length, List.length_ofFn]; exact ha)
      rw [hpre, hev i]
    · by_cases heq : i = st.1.length
      · subst heq
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right le_rfl]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        rw [← hol, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right le_rfl]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        exact hv
      · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
        rfl
  have hk_keep : ∀ k v, k < st.1.length → st.1.getD k none = none → (st.1 ++ [v]).getD k none = none := by
    intro k v hk hgk
    rw [List.getD_append _ _ _ _ hk, hgk]
  rcases hg with ⟨hop, hgl⟩
  rcases hop with hop | hop
  · rw [hop] at hkeep_all
    simp only [zeroStep, hop]
    by_cases hnone : (g.inputs.map fun i => st.1.getD i none).any (fun o => o.isNone) = true
    · simp only [hnone, ↓reduceIte]
      refine ⟨by simp, by omega, fun k hk hgk => ⟨hk_keep k _ hk hgk, fun _ => trivial⟩, hm, ?_, ?_⟩
      · intro a ha
        simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at ha
        exact hbd a ha
      · intro x oldW hol hev i
        have hstep := hkeep_all x oldW none [] hol hev
        simp only [List.append_nil] at hstep
        refine hstep ?_ i
        simp only [evalOpt, GateOp.eval]
        have heq_map : g.inputs.map (fun j => oldW.getD j false) =
            (g.inputs.map fun i => st.1.getD i none).map (evalOpt (wiresFrom st.2 (List.ofFn x))) := by
          rw [List.map_map]; apply List.map_congr_left; intro j _; exact (hev j).symm
        rw [heq_map, evalOpt_and_step _ _ (by simp [hgl]), hnone]
        simp
    · simp only [hnone, Bool.false_eq_true, ↓reduceIte]
      have hno_k : ∀ k, st.1.getD k none = none → k ∉ g.inputs := by
        intro k hgk hk
        apply hnone
        exact List.any_eq_true.2 ⟨none, hk_none k hgk hk, rfl⟩
      cases hfm : extractWires (g.inputs.map fun i => st.1.getD i none) with
      | nil =>
        dsimp only
        refine ⟨by simp, by omega, fun k hk hgk => ⟨hk_keep k _ hk hgk, fun hk' => (hno_k k hgk hk').elim⟩, hm, ?_, ?_⟩
        · intro a ha
          simp only [List.mem_append, List.mem_singleton, Option.some.injEq, reduceCtorEq, or_false] at ha
          exact hbd a ha
        · intro x oldW hol hev i
          have hstep := hkeep_all x oldW (some none) [] hol hev
          simp only [List.append_nil] at hstep
          refine hstep ?_ i
          simp only [evalOpt, GateOp.eval]
          have heq_map : g.inputs.map (fun j => oldW.getD j false) =
              (g.inputs.map fun i => st.1.getD i none).map (evalOpt (wiresFrom st.2 (List.ofFn x))) := by
            rw [List.map_map]; apply List.map_congr_left; intro j _; exact (hev j).symm
          rw [heq_map, evalOpt_and_step _ _ (by simp [hgl]), Bool.eq_false_iff.2 hnone, hfm]
          rfl
      | cons a tl =>
        cases tl with
        | nil =>
          dsimp only
          have ha_bd := hins_mem a (by rw [hfm]; simp)
          refine ⟨by simp, by omega, fun k hk hgk => ⟨hk_keep k _ hk hgk, fun hk' => (hno_k k hgk hk').elim⟩, hm, ?_, ?_⟩
          · intro c hc
            simp only [List.mem_append, List.mem_singleton, Option.some.injEq] at hc
            rcases hc with hc | rfl
            · exact hbd c hc
            · exact ha_bd
          · intro x oldW hol hev i
            have hstep := hkeep_all x oldW (some (some a)) [] hol hev
            simp only [List.append_nil] at hstep
            refine hstep ?_ i
            simp only [evalOpt, GateOp.eval]
            have heq_map : g.inputs.map (fun j => oldW.getD j false) =
                (g.inputs.map fun i => st.1.getD i none).map (evalOpt (wiresFrom st.2 (List.ofFn x))) := by
              rw [List.map_map]; apply List.map_congr_left; intro j _; exact (hev j).symm
            rw [heq_map, evalOpt_and_step _ _ (by simp [hgl]), Bool.eq_false_iff.2 hnone, hfm]
            rfl
        | cons b tl2 =>
          dsimp only
          refine ⟨by simp, by simp, fun k hk hgk => ⟨hk_keep k _ hk hgk, fun hk' => (hno_k k hgk hk').elim⟩, ?_, ?_, ?_⟩
          · intro g' hg'
            simp only [List.mem_append, List.mem_singleton] at hg'
            rcases hg' with hg' | rfl
            · exact hm g' hg'
            · exact ⟨Or.inl rfl, by simp⟩
          · intro c hc
            simp only [List.mem_append, List.mem_singleton, Option.some.injEq, List.length_append,
              List.length_singleton] at hc ⊢
            rcases hc with hc | rfl
            · have := hbd c hc; omega
            · omega
          · intro x oldW hol hev i
            refine hkeep_all x oldW (some (some (n + st.2.length))) [⟨GateOp.and, [a, b]⟩] hol hev ?_ i
            simp only [evalOpt, wiresFrom_append]
            have hwl : (wiresFrom st.2 (List.ofFn x)).length = n + st.2.length := by
              rw [wiresFrom_length, List.length_ofFn]
            change (wiresFrom st.2 (List.ofFn x) ++
              [GateOp.and.eval ([a, b].map fun j => (wiresFrom st.2 (List.ofFn x)).getD j false)]).getD
              (n + st.2.length) false = _
            rw [← hwl, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right le_rfl]
            simp only [Nat.sub_self, List.getElem_cons_zero, GateOp.eval, List.map_cons,
              List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            have heq_map : g.inputs.map (fun j => oldW.getD j false) =
                (g.inputs.map fun i => st.1.getD i none).map (evalOpt (wiresFrom st.2 (List.ofFn x))) := by
              rw [List.map_map]; apply List.map_congr_left; intro j _; exact (hev j).symm
            rw [heq_map, evalOpt_and_step _ _ (by simp [hgl]), Bool.eq_false_iff.2 hnone, hfm]
            rfl
  · rw [hop] at hkeep_all
    simp only [zeroStep, hop]
    by_cases htrue : (g.inputs.map fun i => st.1.getD i none).any
        (fun o => match o with | some none => true | _ => false) = true
    · simp only [htrue, ↓reduceIte]
      refine ⟨by simp, by omega, fun k hk hgk => ⟨hk_keep k _ hk hgk, fun _ => trivial⟩, hm, ?_, ?_⟩
      · intro a ha
        simp only [List.mem_append, List.mem_singleton, Option.some.injEq, reduceCtorEq, or_false] at ha
        exact hbd a ha
      · intro x oldW hol hev i
        have hstep := hkeep_all x oldW (some none) [] hol hev
        simp only [List.append_nil] at hstep
        refine hstep ?_ i
        simp only [evalOpt, GateOp.eval]
        have heq_map : g.inputs.map (fun j => oldW.getD j false) =
            (g.inputs.map fun i => st.1.getD i none).map (evalOpt (wiresFrom st.2 (List.ofFn x))) := by
          rw [List.map_map]; apply List.map_congr_left; intro j _; exact (hev j).symm
        rw [heq_map, evalOpt_or_step _ _ (by simp [hgl]), htrue]
        simp
    · simp only [htrue, Bool.false_eq_true, ↓reduceIte]
      cases hfm : extractWires (g.inputs.map fun i => st.1.getD i none) with
      | nil =>
        dsimp only
        refine ⟨by simp, by omega, fun k hk hgk => ⟨hk_keep k _ hk hgk, fun _ => rfl⟩, hm, ?_, ?_⟩
        · intro a ha
          simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at ha
          exact hbd a ha
        · intro x oldW hol hev i
          have hstep := hkeep_all x oldW none [] hol hev
          simp only [List.append_nil] at hstep
          refine hstep ?_ i
          simp only [evalOpt, GateOp.eval]
          have heq_map : g.inputs.map (fun j => oldW.getD j false) =
              (g.inputs.map fun i => st.1.getD i none).map (evalOpt (wiresFrom st.2 (List.ofFn x))) := by
            rw [List.map_map]; apply List.map_congr_left; intro j _; exact (hev j).symm
          rw [heq_map, evalOpt_or_step _ _ (by simp [hgl]), Bool.eq_false_iff.2 htrue, hfm]
          rfl
      | cons a tl =>
        cases tl with
        | nil =>
          dsimp only
          have ha_bd := hins_mem a (by rw [hfm]; simp)
          refine ⟨by simp, by omega, fun k hk hgk => ⟨hk_keep k _ hk hgk, fun _ => rfl⟩, hm, ?_, ?_⟩
          · intro c hc
            simp only [List.mem_append, List.mem_singleton, Option.some.injEq] at hc
            rcases hc with hc | rfl
            · exact hbd c hc
            · exact ha_bd
          · intro x oldW hol hev i
            have hstep := hkeep_all x oldW (some (some a)) [] hol hev
            simp only [List.append_nil] at hstep
            refine hstep ?_ i
            simp only [evalOpt, GateOp.eval]
            have heq_map : g.inputs.map (fun j => oldW.getD j false) =
                (g.inputs.map fun i => st.1.getD i none).map (evalOpt (wiresFrom st.2 (List.ofFn x))) := by
              rw [List.map_map]; apply List.map_congr_left; intro j _; exact (hev j).symm
            rw [heq_map, evalOpt_or_step _ _ (by simp [hgl]), Bool.eq_false_iff.2 htrue, hfm]
            rfl
        | cons b tl2 =>
          dsimp only
          have hno_k : ∀ k, st.1.getD k none = none → k ∉ g.inputs := by
            intro k hgk hk
            have hlt := extractWires_len_lt_of_none _ (hk_none k hgk hk)
            rw [hfm] at hlt
            simp only [List.length_cons, List.length_map] at hlt
            omega
          refine ⟨by simp, by simp, fun k hk hgk => ⟨hk_keep k _ hk hgk, fun hk' => (hno_k k hgk hk').elim⟩, ?_, ?_, ?_⟩
          · intro g' hg'
            simp only [List.mem_append, List.mem_singleton] at hg'
            rcases hg' with hg' | rfl
            · exact hm g' hg'
            · exact ⟨Or.inr rfl, by simp⟩
          · intro c hc
            simp only [List.mem_append, List.mem_singleton, Option.some.injEq, List.length_append,
              List.length_singleton] at hc ⊢
            rcases hc with hc | rfl
            · have := hbd c hc; omega
            · omega
          · intro x oldW hol hev i
            refine hkeep_all x oldW (some (some (n + st.2.length))) [⟨GateOp.or, [a, b]⟩] hol hev ?_ i
            simp only [evalOpt, wiresFrom_append]
            have hwl : (wiresFrom st.2 (List.ofFn x)).length = n + st.2.length := by
              rw [wiresFrom_length, List.length_ofFn]
            change (wiresFrom st.2 (List.ofFn x) ++
              [GateOp.or.eval ([a, b].map fun j => (wiresFrom st.2 (List.ofFn x)).getD j false)]).getD
              (n + st.2.length) false = _
            rw [← hwl, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right le_rfl]
            simp only [Nat.sub_self, List.getElem_cons_zero, GateOp.eval, List.map_cons,
              List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            have heq_map : g.inputs.map (fun j => oldW.getD j false) =
                (g.inputs.map fun i => st.1.getD i none).map (evalOpt (wiresFrom st.2 (List.ofFn x))) := by
              rw [List.map_map]; apply List.map_congr_left; intro j _; exact (hev j).symm
            rw [heq_map, evalOpt_or_step _ _ (by simp [hgl]), Bool.eq_false_iff.2 htrue, hfm]
            rfl

lemma zeroFold_inv (n : ℕ) : ∀ (gs : List Gate) (st : List (Option (Option ℕ)) × List Gate),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ g ∈ st.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ a, some (some a) ∈ st.1 → a < n + st.2.length) →
    let res := gs.foldl (zeroStep n) st
    res.1.length = st.1.length + gs.length ∧
    res.2.length ≤ st.2.length + gs.length ∧
    (∀ k, k < st.1.length → st.1.getD k none = none → (∃ g ∈ gs, k ∈ g.inputs) → res.2.length + 1 ≤ st.2.length + gs.length) ∧
    (∀ g ∈ res.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ (x : Fin n → Bool) (oldW : List Bool),
      oldW.length = st.1.length →
      (∀ i, evalOpt (wiresFrom st.2 (List.ofFn x)) (st.1.getD i none) = oldW.getD i false) →
      ∀ i, evalOpt (wiresFrom res.2 (List.ofFn x)) (res.1.getD i none) =
        (wiresFrom gs oldW).getD i false)
  | [], st, _, hm, _ => by
    refine ⟨by simp, by simp, ?_, hm, ?_⟩
    · intro k _ _ ⟨g, hg, _⟩; simp at hg
    · intro x oldW _ hev i; exact hev i
  | g :: gs, st, hgs, hm, hbd => by
    have hg := hgs g List.mem_cons_self
    have hgs' := fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    obtain ⟨hl1, hl2, hk1, hm1, hbd1, hev1⟩ := zeroStep_inv n st g hg hm hbd
    obtain ⟨il1, il2, ik1, im1, iev1⟩ := zeroFold_inv n gs (zeroStep n st g) hgs' hm1 hbd1
    dsimp only [List.foldl_cons]
    refine ⟨by simp only [List.length_cons]; omega, by simp only [List.length_cons]; omega, ?_, im1, ?_⟩
    · intro k hk hgk ⟨g0, hg0, hkg0⟩
      simp only [List.mem_cons] at hg0
      rcases hg0 with rfl | hg0
      · have h0 := (hk1 k hk hgk).2 hkg0
        simp only [List.length_cons]
        omega
      · have h0 := ik1 k (by omega) (hk1 k hk hgk).1 ⟨g0, hg0, hkg0⟩
        simp only [List.length_cons]
        omega
    · intro x oldW hol hev i
      exact iev1 x (oldW ++ [g.op.eval (g.inputs.map fun j => oldW.getD j false)])
        (by simp [hol, hl1]) (hev1 x oldW hol hev) i

lemma no_read_indep_fold (k : ℕ) : ∀ (gs : List Gate) (w1 w2 : List Bool),
    w1.length = w2.length →
    (∀ i, i ≠ k → w1.getD i false = w2.getD i false) →
    (∀ g ∈ gs, k ∉ g.inputs) →
    ∀ i, i ≠ k → (wiresFrom gs w1).getD i false = (wiresFrom gs w2).getD i false
  | [], w1, w2, _, heq, _, i, hi => heq i hi
  | g :: gs, w1, w2, hlen, heq, hnr, i, hi => by
    have hng : k ∉ g.inputs := hnr g List.mem_cons_self
    have hmap : g.inputs.map (fun j => w1.getD j false) = g.inputs.map (fun j => w2.getD j false) := by
      apply List.map_congr_left
      intro j hj
      exact heq j (fun e => hng (e ▸ hj))
    apply no_read_indep_fold k gs _ _ (by simp [hlen]) _ (fun g' hg' => hnr g' (List.mem_cons_of_mem g hg')) i hi
    intro j hj
    by_cases hlt : j < w1.length
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hlen ▸ hlt)]
      exact heq j hj
    · by_cases he : j = w1.length
      · subst he
        have h1 : (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)]).getD w1.length false =
            g.op.eval (g.inputs.map fun i => w1.getD i false) := by simp
        have h2 : (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]).getD w1.length false =
            g.op.eval (g.inputs.map fun i => w2.getD i false) := by rw [hlen]; simp
        change (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)]).getD w1.length false =
            (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]).getD w1.length false
        rw [h1, h2, hmap]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma essential_zero {n : ℕ} (C : Circuit) (hM : Monotone2 C) (k : Fin n)
    (x0 x1 xe : Fin n → Bool)
    (h0 : C.eval (List.ofFn (Function.update x0 k false)) = false)
    (h1 : C.eval (List.ofFn (Function.update x1 k false)) = true)
    (he : C.eval (List.ofFn (Function.update xe k false)) ≠ C.eval (List.ofFn (Function.update xe k true)))
    (hs : C.eval (List.ofFn (fun i : Fin n => decide (i = k))) = false) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size + 1 ≤ C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x k false)) := by
  have hout_ne : C.output ≠ k.val := by
    intro h
    have hv : C.eval (List.ofFn (fun i : Fin n => decide (i = k))) = true := by
      change (wiresFrom C.gates (List.ofFn (fun i : Fin n => decide (i = k)))).getD C.output false = true
      rw [h, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      simp
    rw [hv] at hs
    exact Bool.noConfusion hs
  have hread : ∃ g ∈ C.gates, k.val ∈ g.inputs := by
    by_contra hnr
    push Not at hnr
    apply he
    apply no_read_indep_fold k.val C.gates _ _ (by simp) _ hnr C.output hout_ne
    intro i hi
    by_cases hlt : i < n
    · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt]),
          List.getElem_ofFn, List.getElem_ofFn]
      have hne : (⟨i, hlt⟩ : Fin n) ≠ k := fun e => hi (congrArg Fin.val e)
      simp [Function.update, hne]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  let wmap0 : List (Option (Option ℕ)) :=
    (List.range n).map fun i => if i = k.val then none else some (some i)
  have hw0_len : wmap0.length = n := by simp [wmap0]
  have hw0_bd : ∀ a, some (some a) ∈ wmap0 → a < n + ([] : List Gate).length := by
    intro a ha
    simp only [wmap0, List.mem_map, List.mem_range] at ha
    obtain ⟨i, hi, hia⟩ := ha
    by_cases hik : i = k.val
    · simp [hik] at hia
    · simp only [hik, ↓reduceIte, Option.some.injEq] at hia
      subst hia; simp [hi]
  have hw0_k : wmap0.getD k.val none = none := by
    rw [List.getD_eq_getElem _ _ (by simp [wmap0, k.isLt])]
    simp [wmap0]
  have hw0_ev : ∀ x : Fin n → Bool, ∀ i,
      evalOpt (wiresFrom [] (List.ofFn x)) (wmap0.getD i none) =
        (List.ofFn (Function.update x k false)).getD i false := by
    intro x i
    by_cases hi : i < n
    · rw [List.getD_eq_getElem wmap0 none (by simp [wmap0, hi])]
      rw [List.getD_eq_getElem (List.ofFn _) false (by simp [hi]), List.getElem_ofFn]
      simp only [wmap0, List.getElem_map, List.getElem_range]
      by_cases hik : i = k.val
      · subst hik
        simp [evalOpt]
      · simp only [hik, ↓reduceIte, evalOpt, wiresFrom, List.foldl_nil]
        rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]
        have hne : (⟨i, hi⟩ : Fin n) ≠ k := fun e => hik (congrArg Fin.val e)
        simp [Function.update, hne]
    · rw [List.getD_eq_default wmap0 none (by simp [wmap0]; omega)]
      rw [List.getD_eq_default (List.ofFn _) false (by simp; omega)]
      rfl
  have hgs : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have hm := hM g hg
    exact ⟨by simpa using hm.1, hm.2⟩
  obtain ⟨_, _, hsz, hmon, hev⟩ := zeroFold_inv n C.gates (wmap0, []) hgs (by simp) hw0_bd
  have hsz' : (C.gates.foldl (zeroStep n) (wmap0, [])).2.length + 1 ≤ C.gates.length := by
    have := hsz k.val (by rw [hw0_len]; exact k.isLt) hw0_k hread
    simpa using this
  let res := C.gates.foldl (zeroStep n) (wmap0, [])
  have hres_ev : ∀ x : Fin n → Bool,
      evalOpt (wiresFrom res.2 (List.ofFn x)) (res.1.getD C.output none) =
        C.eval (List.ofFn (Function.update x k false)) := by
    intro x
    exact hev x (List.ofFn (Function.update x k false)) (by simp [hw0_len]) (hw0_ev x) C.output
  cases ho : res.1.getD C.output none with
  | none =>
    have := hres_ev x1
    rw [ho, h1] at this
    exact Bool.noConfusion this
  | some o =>
    cases o with
    | none =>
      have := hres_ev x0
      rw [ho, h0] at this
      exact Bool.noConfusion this
    | some out =>
      refine ⟨⟨res.2, out⟩, ?_, ?_, ?_⟩
      · intro g hg
        have hm := hmon g hg
        exact ⟨by simpa using hm.1, hm.2⟩
      · exact hsz'
      · intro x
        have := hres_ev x
        rw [ho] at this
        exact this

def ext17 (x : Fin 11 → Bool) (i : Fin 17) : Bool :=
  if h1 : i.val < 10 then x ⟨i.val, by omega⟩
  else if i.val = 16 then x ⟨10, by omega⟩
  else false

lemma project17to11 (C : Circuit) (hM : Monotone2 C)
    (x0 x1 : Fin 11 → Bool)
    (h0 : C.eval (List.ofFn (ext17 x0)) = false)
    (h1 : C.eval (List.ofFn (ext17 x1)) = true) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧
      ∀ x : Fin 11 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn (ext17 x)) := by
  let wmap0 : List (Option (Option ℕ)) :=
    (List.range 17).map fun i => if i < 10 then some (some i) else if i = 16 then some (some 10) else none
  have hw0_len : wmap0.length = 17 := by simp [wmap0]
  have hw0_bd : ∀ a, some (some a) ∈ wmap0 → a < 11 + ([] : List Gate).length := by
    intro a ha
    simp only [wmap0, List.mem_map, List.mem_range] at ha
    obtain ⟨i, hi, hia⟩ := ha
    split_ifs at hia with hlt heq
    · cases hia; simp; omega
    · cases hia; simp
  have hw0_ev : ∀ x : Fin 11 → Bool, ∀ i,
      evalOpt (wiresFrom [] (List.ofFn x)) (wmap0.getD i none) = (List.ofFn (ext17 x)).getD i false := by
    intro x i
    by_cases hi : i < 17
    · rw [List.getD_eq_getElem wmap0 none (by simp [wmap0, hi])]
      rw [List.getD_eq_getElem (List.ofFn _) false (by simp [hi]), List.getElem_ofFn]
      simp only [wmap0, List.getElem_map, List.getElem_range, ext17]
      by_cases h10 : i < 10
      · simp only [h10, ↓reduceIte, ↓reduceDIte, evalOpt, wiresFrom, List.foldl_nil]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      · simp only [h10, ↓reduceIte, ↓reduceDIte]
        by_cases h16 : i = 16
        · simp only [h16, ↓reduceIte, evalOpt, wiresFrom, List.foldl_nil]
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        · simp [h16, evalOpt]
    · rw [List.getD_eq_default wmap0 none (by simp [wmap0]; omega)]
      rw [List.getD_eq_default (List.ofFn _) false (by simp; omega)]
      rfl
  have hgs : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have hm := hM g hg
    exact ⟨by simpa using hm.1, hm.2⟩
  obtain ⟨_, hsz, _, hmon, hev⟩ := zeroFold_inv 11 C.gates (wmap0, []) hgs (by simp) hw0_bd
  let res := C.gates.foldl (zeroStep 11) (wmap0, [])
  have hres_ev : ∀ x : Fin 11 → Bool,
      evalOpt (wiresFrom res.2 (List.ofFn x)) (res.1.getD C.output none) = C.eval (List.ofFn (ext17 x)) := by
    intro x
    exact hev x (List.ofFn (ext17 x)) (by simp [hw0_len]) (hw0_ev x) C.output
  cases ho : res.1.getD C.output none with
  | none =>
    have := hres_ev x1
    rw [ho, h1] at this
    exact Bool.noConfusion this
  | some o =>
    cases o with
    | none =>
      have := hres_ev x0
      rw [ho, h0] at this
      exact Bool.noConfusion this
    | some out =>
      refine ⟨⟨res.2, out⟩, ?_, ?_, ?_⟩
      · intro g hg
        have hm := hmon g hg
        exact ⟨by simpa using hm.1, hm.2⟩
      · simpa [Circuit.size] using hsz
      · intro x
        have := hres_ev x
        rw [ho] at this
        exact this

def core5Edges : List (ℕ × ℕ) :=
  [(0, 5), (1, 5), (3, 5), (1, 6), (2, 6), (4, 6), (2, 7), (3, 7),
   (3, 8), (4, 8), (0, 9), (4, 9), (0, 10), (2, 10)]

def core5AdjB (u v : Fin 11) : Bool :=
  core5Edges.any fun e => (e.1 == u.val && e.2 == v.val) || (e.1 == v.val && e.2 == u.val)

lemma core5AdjB_symm : ∀ u v : Fin 11, core5AdjB u v = core5AdjB v u := by decide +kernel
lemma core5AdjB_irrefl : ∀ u : Fin 11, core5AdjB u u = false := by decide +kernel

def core5 : SimpleGraph (Fin 11) where
  Adj u v := core5AdjB u v = true
  symm := ⟨fun u v h => by rwa [core5AdjB_symm]⟩
  loopless := ⟨fun u h => by rw [core5AdjB_irrefl] at h; exact Bool.noConfusion h⟩

def enc : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (enc bs)

lemma enc_testBit : ∀ (l : List Bool) (k : ℕ), (enc l).testBit k = l.getD k false
  | [], k => by simp [enc]
  | b :: bs, 0 => by simp [enc]
  | b :: bs, k + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit bs k]

lemma enc_lt : ∀ (l : List Bool), enc l < 2 ^ l.length
  | [] => by simp [enc]
  | b :: bs => by
    have ih := enc_lt bs
    simp only [enc, List.length_cons, pow_succ]
    cases b <;> simp [Nat.bit] <;> omega

def isVcB (m : ℕ) : Bool :=
  core5Edges.all fun e => m.testBit e.1 || m.testBit e.2

def pop11 (m : ℕ) : ℕ :=
  ((List.range 11).filter fun i => m.testBit i).length

def reqB (m v : ℕ) : ℕ :=
  let ucnt := ((List.range 11).filter fun u => !m.testBit u &&
    core5AdjB (Fin.ofNat 11 v) (Fin.ofNat 11 u)).length
  let hasInt := (List.range 11).any fun u => m.testBit u &&
    core5AdjB (Fin.ofNat 11 v) (Fin.ofNat 11 u)
  max 1 (ucnt + (if hasInt then 1 else 0) - 1)

def checkAllVC : Bool :=
  (List.range 2048).all fun m =>
    !isVcB m || (
      decide (5 ≤ pop11 m) &&
      (if pop11 m == 5 then m == 31 else true) &&
      (if pop11 m ≤ 7 then
        decide (8 ≤ (((List.range 11).filter fun v => m.testBit v).map (reqB m)).sum)
      else true) &&
      (if pop11 m == 6 then
        (List.range 11).any fun v1 =>
          m.testBit v1 && decide (2 ≤ reqB m v1) &&
          (List.range 11).any fun v2 =>
            m.testBit v2 && decide (v1 < v2) && decide (2 ≤ reqB m v2) &&
            let inter := ((List.range 11).filter fun u => !m.testBit u &&
              core5AdjB (Fin.ofNat 11 v1) (Fin.ofNat 11 u) &&
              core5AdjB (Fin.ofNat 11 v2) (Fin.ofNat 11 u)).length
            let h1 := (List.range 11).any fun w => m.testBit w &&
              core5AdjB (Fin.ofNat 11 v1) (Fin.ofNat 11 w)
            let h2 := (List.range 11).any fun w => m.testBit w &&
              core5AdjB (Fin.ofNat 11 v2) (Fin.ofNat 11 w)
            decide (inter + (if h1 && h2 then 1 else 0) ≤ 1)
      else true))

lemma checkAllVC_true : checkAllVC = true := by decide +kernel

lemma core5_deg_ge_1 : ∀ v : Fin 11, ∃ u : Fin 11, core5.Adj v u := by
  change ∀ v : Fin 11, ∃ u : Fin 11, core5AdjB v u = true
  decide +kernel

lemma core5_no_twin : ∀ v w : Fin 11, v ≠ w → ¬ core5.Adj v w →
    ∃ q : Fin 11, core5.Adj v q ∧ ¬ core5.Adj w q := by
  change ∀ v w : Fin 11, v ≠ w → core5AdjB v w ≠ true →
    ∃ q : Fin 11, core5AdjB v q = true ∧ core5AdjB w q ≠ true
  decide +kernel

lemma core5_covers_edge_hyp : ∀ v w : Fin 11, core5.Adj v w →
    ∃ a b : Fin 11, core5.Adj v a ∧ a ≠ w ∧ core5.Adj w b ∧ b ≠ v ∧ ¬ core5.Adj a b := by
  change ∀ v w : Fin 11, core5AdjB v w = true →
    ∃ a b : Fin 11, core5AdjB v a = true ∧ a ≠ w ∧ core5AdjB w b = true ∧ b ≠ v ∧ core5AdjB a b ≠ true
  decide +kernel

def P4 : Finset (Fin 11) := {0, 2, 3, 4}
def L6 : Finset (Fin 11) := {5, 6, 7, 8, 9, 10}
def P5 : Finset (Fin 11) := {0, 1, 2, 3, 4}

lemma core5_p4_deg3 : open Classical in ∀ p ∈ P4, (Finset.univ.filter fun l : Fin 11 => core5.Adj p l).card = 3 := by
  classical
  have h : ∀ p ∈ P4, (Finset.univ.filter fun l : Fin 11 => core5AdjB p l = true).card = 3 := by decide +kernel
  intro p hp
  have heq : (Finset.univ.filter fun l : Fin 11 => core5.Adj p l) =
      (Finset.univ.filter fun l : Fin 11 => core5AdjB p l = true) := by
    ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  rw [heq]; exact h p hp

lemma core5_p4_nbr_L6 : ∀ p ∈ P4, ∀ l : Fin 11, core5.Adj p l → l ∈ L6 := by
  change ∀ p ∈ P4, ∀ l : Fin 11, core5AdjB p l = true → l ∈ L6
  decide +kernel

lemma core5_p4_inter1 : open Classical in ∀ p1 ∈ P4, ∀ p2 ∈ P4, p1 ≠ p2 →
    (Finset.univ.filter fun l : Fin 11 => core5.Adj p1 l ∧ core5.Adj p2 l).card = 1 := by
  classical
  have h : ∀ p1 ∈ P4, ∀ p2 ∈ P4, p1 ≠ p2 →
      (Finset.univ.filter fun l : Fin 11 => core5AdjB p1 l = true ∧ core5AdjB p2 l = true).card = 1 := by
    decide +kernel
  intro p1 hp1 p2 hp2 hne
  have heq : (Finset.univ.filter fun l : Fin 11 => core5.Adj p1 l ∧ core5.Adj p2 l) =
      (Finset.univ.filter fun l : Fin 11 => core5AdjB p1 l = true ∧ core5AdjB p2 l = true) := by
    ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  rw [heq]; exact h p1 hp1 p2 hp2 hne

lemma core5_l6_deg2_p4 : open Classical in ∀ l ∈ L6, (P4.filter fun p : Fin 11 => core5.Adj p l).card = 2 := by
  classical
  have h : ∀ l ∈ L6, (P4.filter fun p : Fin 11 => core5AdjB p l = true).card = 2 := by decide +kernel
  intro l hl
  have heq : (P4.filter fun p : Fin 11 => core5.Adj p l) =
      (P4.filter fun p : Fin 11 => core5AdjB p l = true) := by
    ext p; simp only [Finset.mem_filter]; rfl
  rw [heq]; exact h l hl

lemma core5_p5_indep : ∀ p ∈ P5, ∀ l : Fin 11, core5.Adj p l → l ∉ P5 := by
  change ∀ p ∈ P5, ∀ l : Fin 11, core5AdjB p l = true → l ∉ P5
  decide +kernel

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n + p) = g.op.eval (g.inputs.map (operand C x (n + p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p + 1) := by
    conv_lhs => rw [← List.take_append_drop (p + 1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n + p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n + p) i := by
    by_cases hi : i < n + p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n + p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p + 1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n + p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n + p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

theorem next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ} (h : Trace n C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

theorem live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

theorem trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

theorem align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
    (p : Trace n C P v b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j = j') :
    ∀ d, Trace n C Q v d → (d < b ∧ P d) ∨ Trace n C Q b d := by
  induction p using ReflTransGen.head_induction_on with
  | refl => intro d q; exact Or.inr q
  | head hp pt ih =>
    intro d q
    have hlt := hp.2.1.1.trans_le (trace_le pt)
    rcases q.cases_head with rfl | ⟨j, hq, qt⟩
    · exact Or.inl ⟨hlt, hp.1⟩
    · have e := unique _ _ _ hlt hp.1 hp.2 hq.2
      subst j
      exact ih _ qt

theorem difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
    ∀ j, Live n C j → val C x j ≠ val C y j →
      ∃ i : Fin n, x i ≠ y i ∧ Trace n C (fun a => val C x a ≠ val C y a) i.val j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hd
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n + C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n + p := ⟨j - n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n + p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n + p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n + p) := ⟨hlt, p, g, hg, rfl, ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha', hs, hj⟩⟩

theorem acts_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj; contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n + p := ⟨j - n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n + p) a = true → operand C y (n + p) a = true := by
      by_cases ha : a < n + p
      · simp only [operand, ite_eq_left ha]; exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

def point {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

theorem point_mono {n : ℕ} {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

theorem point_insert {n : ℕ} {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

def Carries {n : ℕ} (C : Circuit) (v : Fin n) (a : ℕ) : Prop :=
  val C (point {v}) a ≠ val C (point (∅ : Finset (Fin n))) a

theorem carries_iff {n : ℕ} {C : Circuit} (hC : Monotone2 C) {v : Fin n} {a : ℕ} :
    Carries C v a ↔
      val C (point {v}) a = true ∧ val C (point (∅ : Finset (Fin n))) a = false := by
  have hm := acts_mono hC (point_mono (Finset.empty_subset {v})) a
  unfold Carries
  cases ha : val C (point {v}) a <;>
    cases hb : val C (point (∅ : Finset (Fin n))) a <;> simp_all

theorem singleton_path {n : ℕ} {C : Circuit} {v : Fin n} {a : ℕ}
    (ha : Live n C a) (hd : Carries C v a) :
    Trace n C (Carries C v) v.val a := by
  obtain ⟨i, hi, hpath⟩ := difference C (point {v}) (point ∅) a ha hd
  have e : i = v := by by_contra h; exact hi (by simp [point, h])
  exact e ▸ hpath

theorem influence {n : ℕ} {C : Circuit} {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b ≤ j ∧ val C x b ≠ val C y b) := by
  obtain ⟨i, hi, trace⟩ := difference C x y j hj hd
  have e : i = v := by by_contra h; exact hi (agrees i h)
  subst i
  rcases align path unique j trace with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨trace_le hb, trace_start hb hd⟩

noncomputable def readers (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (n + C.gates.length)).filter (fun b => LNext n C a b)

theorem next_in_range {n : ℕ} {C : Circuit} {a b : ℕ} (h : Next n C a b) : b < n + C.gates.length := by
  obtain ⟨_, p, g, hg, rfl, _⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

theorem mem_readers {n : ℕ} {C : Circuit} {a b : ℕ} : b ∈ readers n C a ↔ LNext n C a b := by
  classical
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨next_in_range h.1, h⟩⟩

def Branch (n : ℕ) (C : Circuit) (a : ℕ) : Prop := 2 ≤ (readers n C a).card

theorem nonbranch_unique {n : ℕ} {C : Circuit} {a j j' : ℕ} (h : ¬ Branch n C a)
    (hj : LNext n C a j) (hj' : LNext n C a j') : j = j' := by
  apply Finset.card_le_one_iff.1 (show (readers n C a).card ≤ 1 from by unfold Branch at h; omega)
    (mem_readers.2 hj) (mem_readers.2 hj')

def Eligible {n : ℕ} (C : Circuit) (v : Fin n) : Prop :=
  ∃ b, Live n C b ∧ Carries C v b ∧ Branch n C b

noncomputable def firstBranch {n : ℕ} (C : Circuit) (v : Fin n) (h : Eligible C v) : ℕ := by
  classical exact Nat.find h

theorem firstBranch_spec {n : ℕ} {C : Circuit} (v : Fin n) (h : Eligible C v) :
    Live n C (firstBranch C v h) ∧ Carries C v (firstBranch C v h) ∧ Branch n C (firstBranch C v h) := by
  classical exact Nat.find_spec h

theorem firstBranch_le {n : ℕ} {C : Circuit} (v : Fin n) (h : Eligible C v) {w : ℕ}
    (hw : Live n C w ∧ Carries C v w ∧ Branch n C w) : firstBranch C v h ≤ w := by
  classical exact Nat.find_min' h hw

theorem firstBranch_unique {n : ℕ} {C : Circuit} (v : Fin n) (h : Eligible C v) :
    ∀ a j j', a < firstBranch C v h → Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  classical
  intro a j j' hl hc hj hj'
  apply nonbranch_unique _ hj hj'
  intro hb
  exact (Nat.not_le_of_gt hl) (Nat.find_min' h ⟨live_before hj.1 hj.2, hc, hb⟩)

theorem no_eligible_unique {n : ℕ} {C : Circuit} {v : Fin n} (h : ¬ Eligible C v) :
    ∀ a j j', Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  intro a j j' hc hj hj'
  exact nonbranch_unique (fun hb => h ⟨a, live_before hj.1 hj.2, hc, hb⟩) hj hj'

def GraphEval {n : ℕ} (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v : Fin n, val C (point {u, v}) C.output = true ↔ G.Adj u v

theorem point_pair {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} (he : GraphEval C G)
    (v w : Fin n) :
    val C (point {v, w}) C.output = true ↔ G.Adj v w := he v w

theorem point_pair_quiet {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} (he : GraphEval C G)
    {v w : Fin n} (hn : ¬ G.Adj v w) : val C (point {v, w}) C.output = false := by
  rw [← Bool.not_eq_true, point_pair he]; exact hn

theorem point_single_quiet {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} (he : GraphEval C G)
    (v : Fin n) : val C (point {v}) C.output = false := by
  have h := point_pair_quiet he (G.irrefl (v := v))
  rwa [show ({v, v} : Finset (Fin n)) = {v} from by simp] at h

theorem point_true_of_edge {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    (hC : Monotone2 C) (he : GraphEval C G) {S : Finset (Fin n)} {u v : Fin n}
    (hu : u ∈ S) (hv : v ∈ S) (huv : G.Adj u v) : val C (point S) C.output = true := by
  have hsub : ({u, v} : Finset (Fin n)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  exact acts_mono hC (point_mono hsub) C.output ((point_pair he u v).2 huv)

theorem edge_at_output {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} (he : GraphEval C G)
    {v w : Fin n} (hvw : G.Adj v w) : n ≤ C.output ∧ C.output < n + C.gates.length := by
  have hp := (point_pair he v w).2 hvw
  constructor
  · by_contra! hl
    let i : Fin n := ⟨C.output, hl⟩
    have hv := point_single_quiet he i
    rw [show C.output = i.val from rfl, val_input] at hv
    simp [point] at hv
  · by_contra! hgt
    rw [val_beyond C _ hgt] at hp; contradiction

theorem two_inputs {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hl : l.length ≤ 2) : ∀ i ∈ l, i = a ∨ i = b := by
  have hsub : ({a, b} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb
  have hcard : l.toFinset.card ≤ ({a, b} : Finset ℕ).card := by
    simpa [hne] using l.toFinset_card_le.trans hl
  have hEq := Finset.eq_of_subset_of_card_le hsub hcard
  intro i hi
  have hm : i ∈ ({a, b} : Finset ℕ) := hEq.symm ▸ (List.mem_toFinset.mpr hi)
  simpa using hm

theorem carries_separate {n : ℕ} {C : Circuit} (hC : Monotone2 C) {v w : Fin n} {a : ℕ}
    (h1 : val C (point {v}) a = true) (h0 : val C (point {w}) a = false) :
    Carries C v a ∧ ¬ Carries C w a := by
  have hb : val C (point (∅ : Finset (Fin n))) a = false := by
    rw [← Bool.not_eq_true]
    intro hc
    have hh := acts_mono hC (point_mono (Finset.empty_subset {w})) a hc
    rw [h0] at hh; contradiction
  rw [carries_iff hC, carries_iff hC]
  simp [h1, h0, hb]

theorem meeting_gate {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    (hC : Monotone2 C) (he : GraphEval C G) {v w : Fin n} (hvw : G.Adj v w) :
    ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ Live n C (n + p) ∧
      LNext n C a (n + p) ∧ LNext n C b (n + p) ∧ a ≠ b ∧
      val C (point {v}) (n + p) = false ∧ val C (point {w}) (n + p) = false ∧
      Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
      (∀ i ∈ g.inputs, i = a ∨ i = b) := by
  classical
  let P (i : ℕ) := Live n C i ∧ val C (point {v, w}) i = true ∧
    val C (point {v}) i = false ∧ val C (point {w}) i = false
  have hex : ∃ i, P i :=
    ⟨C.output, .refl, (point_pair he v w).2 hvw, point_single_quiet he v, point_single_quiet he w⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have earlier (i : ℕ) (hlt : i < j) (hl : Live n C i) (htrue : val C (point {v, w}) i = true) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    by_contra! h
    have h' : P i := ⟨hl, htrue, by simpa using h.1, by simpa using h.2⟩
    exact (Nat.not_le_of_gt hlt) (Nat.find_min' hex h')
  have hge : n ≤ j := by
    by_contra! hh
    let i : Fin n := ⟨j, hh⟩
    obtain ⟨_, ht, hv, hw⟩ := hj
    rw [show j = i.val from rfl, val_input] at ht hv hw
    simp only [point, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with h | h
    · simp [point, h] at hv
    · simp [point, h] at hw
  have hlt : j < n + C.gates.length := by
    by_contra! hh
    have ht := hj.2.1
    rw [val_beyond C _ hh] at ht; contradiction
  let p := j - n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have ep : n + p = j := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
  have hl := hC g (List.mem_of_getElem? hg)
  have hh : Live n C (n + p) := ep ▸ hj.1
  have hs1 : val C (point {v, w}) (n + p) = true := ep ▸ hj.2.1
  have hs2 : val C (point {v}) (n + p) = false := ep ▸ hj.2.2.1
  have hs3 : val C (point {w}) (n + p) = false := ep ▸ hj.2.2.2
  have reads (i : ℕ) (hi : i < n + p) (hm : i ∈ g.inputs) : LNext n C i (n + p) :=
    ⟨⟨hi, p, g, hg, rfl, hm⟩, hh⟩
  have hAnd : g.op = GateOp.and := by
    rcases hl.1 with h | h
    · exact h
    have hop : g.op = GateOp.or := h
    simp only [val_gate C _ hg, hop, GateOp.eval, List.any_map, Function.comp_apply, id,
      List.any_eq_true] at hs1
    obtain ⟨i, hi, ht⟩ := hs1
    have hi' : i < n + p := by by_contra hh'; simp [operand, hh'] at ht
    have ht' : val C (point {v, w}) i = true := by simpa [operand, hi'] using ht
    rcases earlier i (ep ▸ hi') (live_before (reads i hi' hi).1 hh) ht' with hV | hW
    · have hs := hs2
      rw [← Bool.not_eq_true, val_gate C _ hg, hop, GateOp.eval, List.any_map, List.any_eq_true] at hs
      exact (hs ⟨i, hi, by simpa [operand, hi'] using hV⟩).elim
    · have hs := hs3
      rw [← Bool.not_eq_true, val_gate C _ hg, hop, GateOp.eval, List.any_map, List.any_eq_true] at hs
      exact (hs ⟨i, hi, by simpa [operand, hi'] using hW⟩).elim
  have hAll : ∀ i ∈ g.inputs, operand C (point {v, w}) (n + p) i = true := by
    simpa [val_gate C _ hg, hAnd, GateOp.eval, List.all_eq_true] using hs1
  have hFalse (x : Fin n → Bool) (hX : val C x (n + p) = false) :
      ∃ i ∈ g.inputs, operand C x (n + p) i = false := by
    by_contra! h
    have ht : val C x (n + p) = true := by
      rw [val_gate C _ hg, hAnd, GateOp.eval, List.all_map, List.all_eq_true]
      intro i hi; simpa using h i hi
    rw [hX] at ht; contradiction
  obtain ⟨a, ha, hwa⟩ := hFalse _ hs3
  obtain ⟨b, hb, hvb⟩ := hFalse _ hs2
  have before (i : ℕ) (h : i ∈ g.inputs) : i < n + p := by
    by_contra hi; have hX := hAll i h; simp [operand, hi] at hX
  have ha' := before a ha
  have hb' := before b hb
  rw [operand, ite_eq_left ha'] at hwa
  rw [operand, ite_eq_left hb'] at hvb
  have near (i : ℕ) (h : i ∈ g.inputs) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    have hi := before i h
    apply earlier i (ep ▸ hi) (live_before (reads i hi h).1 hh)
    simpa [operand, hi] using hAll i h
  have hva := (near a ha).resolve_right (by rw [hwa]; decide)
  have hwb := (near b hb).resolve_left (by rw [hvb]; decide)
  have hne : a ≠ b := fun e => Bool.noConfusion (hva.symm.trans (e ▸ hvb))
  exact ⟨p, g, a, b, hg, hAnd, hh, reads a ha' ha, reads b hb' hb, hne, hs2, hs3,
    (carries_separate hC hva hwa).1, (carries_separate hC hva hwa).2,
    (carries_separate hC hwb hvb).1, (carries_separate hC hwb hvb).2,
    two_inputs ha hb hne hl.2⟩

theorem covers_edge {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    (hC : Monotone2 C) (he : GraphEval C G) {v w a₀ b₀ : Fin n}
    (hvw : G.Adj v w) (ha₀ : G.Adj v a₀) (hb₀ : G.Adj w b₀) (hind : a₀ = b₀ ∨ ¬ G.Adj a₀ b₀) :
    Eligible C v ∨ Eligible C w := by
  by_contra! bad
  obtain ⟨p, g, a, b, hg, hAnd, hj, ha, hb, _, _, _, hva, hwa, hwb, hvb, hs⟩ := meeting_gate hC he hvw
  have pathV : Trace n C (Carries C v) v.val (n + p) :=
    (singleton_path (live_before ha.1 ha.2) hva).tail ⟨hva, ha⟩
  have pathW : Trace n C (Carries C w) w.val (n + p) :=
    (singleton_path (live_before hb.1 hb.2) hwb).tail ⟨hwb, hb⟩
  have uniqueV : ∀ k j j', k < n + p → Carries C v k → LNext n C k j → LNext n C k j' → j = j' :=
    fun k j j' _ => no_eligible_unique bad.1 k j j'
  have uniqueW : ∀ k j j', k < n + p → Carries C w k → LNext n C k j → LNext n C k j' → j = j' :=
    fun k j j' _ => no_eligible_unique bad.2 k j j'
  let S : Finset (Fin n) := {a₀, b₀}
  let x := point S
  let y := point (insert v S)
  let z := point (insert w S)
  have hzero : val C x C.output = false :=
    point_pair_quiet he (hind.elim (fun e => e ▸ G.irrefl (v := a₀)) id)
  have hY : val C y C.output = true :=
    point_true_of_edge hC he (u := v) (v := a₀) (by simp) (by simp [S]) ha₀
  have hZ : val C z C.output = true :=
    point_true_of_edge hC he (u := w) (v := b₀) (by simp) (by simp [S]) hb₀
  have jout := next_le hj
  have hvj := influence pathV uniqueV (fun _ hi => (point_insert hi).symm) ReflTransGen.refl
    (show val C x C.output ≠ val C y C.output from by rw [hzero, hY]; decide)
  have hwj := influence pathW uniqueW (fun _ hi => (point_insert hi).symm) ReflTransGen.refl
    (show val C x C.output ≠ val C z C.output from by rw [hzero, hZ]; decide)
  have hdiffV := (hvj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hdiffW := (hwj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hX : val C x (n + p) = false := by
    rw [← Bool.not_eq_true]
    intro htrue
    exact hdiffV (htrue.trans (acts_mono hC (point_mono (Finset.subset_insert _ _)) _ htrue).symm)
  have hyj : val C y (n + p) = true := by rw [hX] at hdiffV; simpa using hdiffV.symm
  have hzj : val C z (n + p) = true := by rw [hX] at hdiffW; simpa using hdiffW.symm
  have hAX : val C x a = val C z a := by
    by_contra h
    rcases influence pathW uniqueW (fun _ hi => (point_insert hi).symm) (live_before ha.1 ha.2) h with h' | h'
    · exact hwa h'.2
    · exact (Nat.not_le_of_gt ha.1.1) h'.1
  have hBX : val C x b = val C y b := by
    by_contra h
    rcases influence pathV uniqueV (fun _ hi => (point_insert hi).symm) (live_before hb.1 hb.2) h with h' | h'
    · exact hvb h'.2
    · exact (Nat.not_le_of_gt hb.1.1) h'.1
  have hYall : ∀ i ∈ g.inputs, operand C y (n + p) i = true := by
    simpa [val_gate C _ hg, hAnd, GateOp.eval, List.all_eq_true] using hyj
  have hZall : ∀ i ∈ g.inputs, operand C z (n + p) i = true := by
    simpa [val_gate C _ hg, hAnd, GateOp.eval, List.all_eq_true] using hzj
  have hin (i : ℕ) : LNext n C i (n + p) → i ∈ g.inputs := by
    rintro ⟨⟨_, k, g', he', hk, hmem⟩, _⟩
    have e : k = p := by omega
    subst k; rw [hg] at he'; cases he'; exact hmem
  have hxA := hZall a (hin a ha)
  have hxB := hYall b (hin b hb)
  rw [operand, ite_eq_left ha.1.1, ← hAX] at hxA
  rw [operand, ite_eq_left hb.1.1, ← hBX] at hxB
  have hs' : val C x (n + p) = true := by
    rw [val_gate C _ hg, hAnd, GateOp.eval, List.all_map, List.all_eq_true]
    intro i hi
    rcases hs i hi with rfl | rfl
    · simpa [Function.comp_apply, operand, ha.1.1] using hxA
    · simpa [Function.comp_apply, operand, hb.1.1] using hxB
  rw [hX] at hs'; contradiction

theorem value_at_branch {n : ℕ} {C : Circuit} {v : Fin n} {x y : Fin n → Bool} (hv : Eligible C v)
    (agrees : ∀ i, i ≠ v → x i = y i)
    (hb : val C x (firstBranch C v hv) = val C y (firstBranch C v hv)) :
    val C x C.output = val C y C.output := by
  by_contra h
  have spec := firstBranch_spec v hv
  have path := singleton_path spec.1 spec.2.1
  rcases influence path (firstBranch_unique v hv) agrees ReflTransGen.refl h with bad | bad
  · exact (Nat.not_lt_of_ge (next_le spec.1)) bad.1
  · exact bad.2 hb

theorem value_at_carries {n : ℕ} {C : Circuit} {u : Fin n} {c : ℕ} {x y : Fin n → Bool}
    (hu : ¬ Eligible C u) (hl : Live n C c) (hc : Carries C u c)
    (agrees : ∀ i, i ≠ u → x i = y i) (heq : val C x c = val C y c) :
    val C x C.output = val C y C.output := by
  by_contra h
  have path := singleton_path hl hc
  rcases influence path (fun a j j' _ => no_eligible_unique hu a j j') agrees ReflTransGen.refl h with bad | bad
  · exact (Nat.not_lt_of_ge (next_le hl)) bad.1
  · exact bad.2 heq

theorem pure_bottleneck {C : Circuit} (hC : Monotone2 C) (he : GraphEval C core5)
    {u z : Fin 11} {c : ℕ} (hne : z ≠ u)
    (hb : ∀ x y : Fin 11 → Bool, (∀ i, i ≠ u → x i = y i) → val C x c = val C y c →
      val C x C.output = val C y C.output) :
    val C (point {z}) c = false := by
  by_contra ht
  have hz : val C (point {z}) c = true := by cases h : val C (point {z}) c <;> simp_all
  by_cases hadj : core5.Adj u z
  · have hbig : val C (point (insert u ({z} : Finset (Fin 11)))) c = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) c hz
    have eq := hb (point {z}) (point (insert u {z})) (fun _ hi => (point_insert hi).symm) (hz.trans hbig.symm)
    have hy : val C (point (insert u ({z} : Finset (Fin 11)))) C.output = true :=
      (point_pair he u z).2 hadj
    rw [point_single_quiet he z, hy] at eq
    exact Bool.noConfusion eq
  · obtain ⟨q, huq, hzq⟩ := core5_no_twin u z hne.symm hadj
    have hx : val C (point {z, q}) c = true :=
      acts_mono hC (point_mono (by simp)) c hz
    have hbig : val C (point (insert u ({z, q} : Finset (Fin 11)))) c = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) c hx
    have eq := hb (point {z, q}) (point (insert u {z, q})) (fun _ hi => (point_insert hi).symm)
      (hx.trans hbig.symm)
    have h0 : val C (point {z, q}) C.output = false := point_pair_quiet he hzq
    have h1 : val C (point (insert u ({z, q} : Finset (Fin 11)))) C.output = true :=
      point_true_of_edge hC he (u := u) (v := q) (by simp) (by simp) huq
    rw [h0, h1] at eq
    exact Bool.noConfusion eq

theorem non_eligible_pure {C : Circuit} (hC : Monotone2 C) (he : GraphEval C core5)
    {u z : Fin 11} (hu : ¬ Eligible C u) (hne : z ≠ u) {c : ℕ}
    (hl : Live 11 C c) (hc : Carries C u c) :
    val C (point {z}) c = false :=
  pure_bottleneck hC he hne (fun _ _ => value_at_carries hu hl hc)

theorem branch_disjoint {C : Circuit} (hC : Monotone2 C) (he : GraphEval C core5)
    {w v : Fin 11} (hw : Eligible C w) (hne : v ≠ w) :
    val C (point {v}) (firstBranch C w hw) = false :=
  pure_bottleneck hC he hne (fun _ _ => value_at_branch hw)

theorem branch_injective_core5 {C : Circuit} (hC : Monotone2 C) (he : GraphEval C core5)
    {v w : Fin 11} (hv : Eligible C v) (hw : Eligible C w)
    (h : firstBranch C v hv = firstBranch C w hw) : v = w := by
  by_contra hne
  have h1 := ((carries_iff hC).1 (firstBranch_spec v hv).2.1).1
  rw [h, branch_disjoint hC he hw hne] at h1
  exact Bool.noConfusion h1

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n + C.gates.length)).filter (Live n C)

theorem mem_living {n : ℕ} {C : Circuit} {w : ℕ} :
    w ∈ living n C ↔ w < n + C.gates.length ∧ Live n C w := by
  classical simp [living]

theorem input_live {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} (he : GraphEval C G)
    {v u : Fin n} (hvu : G.Adj v u) : Live n C v.val := by
  have hx : val C (point {u}) C.output = false := point_single_quiet he u
  have hy : val C (point {v, u}) C.output = true := (point_pair he v u).2 hvu
  obtain ⟨i, hi, trace⟩ := difference C (point {u}) (point {v, u}) C.output ReflTransGen.refl
    (by rw [hx, hy]; decide)
  have ei : i = v := by by_contra h; exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b, hb, _⟩
  · rw [h]; exact .refl
  · exact live_before hb.2.1 hb.2.2

theorem live_readers_nonempty {n : ℕ} {C : Circuit} {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    (readers n C a).Nonempty := by
  rcases ha.cases_head with h | ⟨b, hb, hpath⟩
  · exact (hneq h).elim
  · exact ⟨b, mem_readers.2 ⟨hb, hpath⟩⟩

theorem readers_filter (n : ℕ) (C : Circuit) (a : ℕ) :
    open Classical in readers n C a = (living n C).filter (fun b => LNext n C a b) := by
  classical
  ext b
  simp only [mem_readers, Finset.mem_filter, mem_living]
  exact ⟨fun h => ⟨⟨next_in_range h.1, h.2⟩, h⟩, And.right⟩

theorem incoming_bound {n : ℕ} {C : Circuit} (hC : Monotone2 C) {j : ℕ} (hj : j ∈ living n C) :
    open Classical in ((living n C).filter fun i => LNext n C i j).card ≤ if j < n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_, ⟨_, p, g, hg, hp, _⟩, _⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j - n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j = n + p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_, ⟨_, q, g', hg', hq, hm⟩, _⟩ := Finset.mem_filter.1 ha
    have ep : p = q := by omega
    subst q; rw [hg] at hg'; cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)

theorem excess_fanout {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    (hC : Monotone2 C) (he : GraphEval C G)
    (hdegree : ∀ v : Fin n, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in
    n + ∑ a ∈ (living n C).filter (Branch n C), ((readers n C a).card - 1) ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have hSub : Finset.range n ⊆ W := by
    intro a ha
    have hi := Finset.mem_range.1 ha
    obtain ⟨u, hu⟩ := hdegree ⟨a, hi⟩
    exact mem_living.2 ⟨by omega, input_live he hu⟩
  have hW : W.card = n + S.card := by
    have h := Finset.card_sdiff_add_card_eq_card hSub
    have e : W \ Finset.range n = S := by ext a; simp [S]
    rw [e, Finset.card_range] at h
    omega
  have hR : R.card + 1 = W.card := Finset.card_erase_add_one ho
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a - n)
    · intro a ha
      have h : a < n + C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2; change a - n < C.gates.length; omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a - n = b - n at hab; omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card + ∑ a ∈ B, ((readers n C a).card - 1) ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a = C.output then 0 else 1 : ℕ)) = R.card := by
      calc _ = ∑ a ∈ W, (if a ≠ C.output then 1 else 0 : ℕ) := by
            apply Finset.sum_congr rfl; intro a _; by_cases h : a = C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R, Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then (readers n C a).card - 1 else 0)) =
        ∑ a ∈ B, ((readers n C a).card - 1) := by
      rw [← Finset.sum_filter]
    rw [← eR, ← eB, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a = C.output
    · subst a; simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simp only [heq, ↓reduceIte, hb]; omega
      · have h1 := Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
        simp only [heq, ↓reduceIte, hb]; omega
  have hcomm : (∑ a ∈ W, (readers n C a).card) =
      ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2 * S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j < n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j < n then 0 else 2 : ℕ)) = 2 * S.card := by
      simp [S, Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change n + ∑ a ∈ B, ((readers n C a).card - 1) ≤ C.gates.length + 1
  omega

noncomputable def Kv (C : Circuit) (v : Fin 11) : Finset ℕ :=
  open Classical in (living 11 C).filter (Carries C v)

lemma mem_Kv {C : Circuit} {v : Fin 11} {w : ℕ} :
    w ∈ Kv C v ↔ w < 11 + C.gates.length ∧ Live 11 C w ∧ Carries C v w := by
  classical simp [Kv, mem_living, and_assoc]

lemma Kv_sub_living {C : Circuit} {v : Fin 11} : Kv C v ⊆ living 11 C := by
  classical exact Finset.filter_subset _ _

lemma v_mem_Kv {C : Circuit} (hC : Monotone2 C) (he : GraphEval C core5) (v : Fin 11) :
    v.val ∈ Kv C v := by
  obtain ⟨u, hu⟩ := core5_deg_ge_1 v
  rw [mem_Kv]
  refine ⟨by have := v.isLt; omega, input_live he hu, ?_⟩
  rw [carries_iff hC, val_input, val_input]
  simp [point]

lemma out_notMem_Kv {C : Circuit} (hC : Monotone2 C) (he : GraphEval C core5) (v : Fin 11) :
    C.output ∉ Kv C v := by
  intro h
  rw [mem_Kv] at h
  have h1 := ((carries_iff hC).1 h.2.2).1
  rw [point_single_quiet he v] at h1
  exact Bool.noConfusion h1

lemma Kv_indeg_pos {C : Circuit} (hC : Monotone2 C) (v : Fin 11) {y : ℕ}
    (hy : y ∈ (Kv C v).erase v.val) :
    open Classical in 1 ≤ ((Kv C v).filter fun x => LNext 11 C x y).card := by
  classical
  have hne : y ≠ v.val := (Finset.mem_erase.1 hy).1
  have hyk := mem_Kv.1 (Finset.mem_erase.1 hy).2
  have h1 := ((carries_iff hC).1 hyk.2.2).1
  have h0 := ((carries_iff hC).1 hyk.2.2).2
  have hge : 11 ≤ y := by
    by_contra! hlt
    let u : Fin 11 := ⟨y, hlt⟩
    have huv : u ≠ v := fun e => hne (congrArg Fin.val e)
    rw [show y = u.val from rfl, val_input] at h1
    simp [point, huv] at h1
  obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ y = 11 + p := ⟨y - 11, by omega, by omega⟩
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
  have hm := (hC g (List.mem_of_getElem? hg)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  suffices ∃ a ∈ Kv C v, LNext 11 C a (11 + p) by
    obtain ⟨a, ha, hln⟩ := this
    exact Finset.card_pos.2 ⟨a, Finset.mem_filter.2 ⟨ha, hln⟩⟩
  rcases hm with hop | hop
  · rw [val_gate C _ hg, hop] at h1 h0
    have hall : ∀ a ∈ g.inputs, operand C (point {v}) (11 + p) a = true := by
      simpa [GateOp.eval, List.all_map, List.all_eq_true] using h1
    have hex : ∃ a ∈ g.inputs, operand C (point (∅ : Finset (Fin 11))) (11 + p) a = false := by
      by_contra! h
      have : GateOp.and.eval (g.inputs.map (operand C (point (∅ : Finset (Fin 11))) (11 + p))) = true := by
        simp only [GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true]
        intro a ha; exact Bool.eq_true_of_not_eq_false (h a ha)
      rw [h0] at this; exact Bool.noConfusion this
    obtain ⟨a, ha, ha0⟩ := hex
    have ha1 := hall a ha
    have halt : a < 11 + p := by by_contra hge'; simp [operand, hge'] at ha1
    rw [operand, ite_eq_left halt] at ha1 ha0
    have hln : LNext 11 C a (11 + p) := ⟨⟨halt, p, g, hg, rfl, ha⟩, hyk.2.1⟩
    exact ⟨a, mem_Kv.2 ⟨by omega, live_before hln.1 hln.2, (carries_iff hC).2 ⟨ha1, ha0⟩⟩, hln⟩
  · rw [val_gate C _ hg, hop] at h1 h0
    simp only [GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at h1
    obtain ⟨a, ha, ha1⟩ := h1
    have halt : a < 11 + p := by by_contra hge'; simp [operand, hge'] at ha1
    have ha0 : val C (point (∅ : Finset (Fin 11))) a = false := by
      by_contra h
      have ht : val C (point (∅ : Finset (Fin 11))) a = true := by
        cases hv : val C (point (∅ : Finset (Fin 11))) a <;> simp_all
      have : GateOp.or.eval (g.inputs.map (operand C (point (∅ : Finset (Fin 11))) (11 + p))) = true := by
        simp only [GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true]
        exact ⟨a, ha, by simp [operand, halt, ht]⟩
      rw [h0] at this; exact Bool.noConfusion this
    rw [operand, ite_eq_left halt] at ha1
    have hln : LNext 11 C a (11 + p) := ⟨⟨halt, p, g, hg, rfl, ha⟩, hyk.2.1⟩
    exact ⟨a, mem_Kv.2 ⟨by omega, live_before hln.1 hln.2, (carries_iff hC).2 ⟨ha1, ha0⟩⟩, hln⟩

theorem dag_sum_Kv {C : Circuit} (hC : Monotone2 C) (he : GraphEval C core5) (v : Fin 11) :
    open Classical in
    (∑ w ∈ (Kv C v).filter (Branch 11 C), ((readers 11 C w).card - 1)) + 1 =
      (∑ y ∈ (Kv C v).erase v.val, (((Kv C v).filter fun x => LNext 11 C x y).card - 1)) +
      (∑ m ∈ (living 11 C) \ Kv C v, ((Kv C v).filter fun x => LNext 11 C x m).card) := by
  classical
  let K := Kv C v
  let W := living 11 C
  have hsub : K ⊆ W := Kv_sub_living
  have hvK : v.val ∈ K := v_mem_Kv hC he v
  have hsum_lhs : ∑ w ∈ K, ((readers 11 C w).card - 1) =
      ∑ w ∈ K.filter (Branch 11 C), ((readers 11 C w).card - 1) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hb : Branch 11 C w
    · simp [hb]
    · simp only [hb, ↓reduceIte]
      have : (readers 11 C w).card ≤ 1 := by unfold Branch at hb; omega
      omega
  have hreaders_ge1 : ∀ w ∈ K, 1 ≤ (readers 11 C w).card := by
    intro w hw
    have hne : w ≠ C.output := fun e => out_notMem_Kv hC he v (e ▸ hw)
    exact Finset.card_pos.2 (live_readers_nonempty (mem_Kv.1 hw).2.1 hne)
  have hsplit_out : ∀ w ∈ K, (readers 11 C w).card =
      (K.filter fun y => LNext 11 C w y).card + ((W \ K).filter fun m => LNext 11 C w m).card := by
    intro w _
    rw [readers_filter]
    have hdisj : Disjoint (K.filter fun y => LNext 11 C w y) ((W \ K).filter fun m => LNext 11 C w m) := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 hy2).1).2 (Finset.mem_filter.1 hy1).1
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hyW, hln⟩
      by_cases hyK : y ∈ K
      · exact Or.inl ⟨hyK, hln⟩
      · exact Or.inr ⟨⟨hyW, hyK⟩, hln⟩
    · rintro (⟨hyK, hln⟩ | ⟨⟨hyW, _⟩, hln⟩)
      · exact ⟨hsub hyK, hln⟩
      · exact ⟨hyW, hln⟩
  have hcomm1 : (∑ w ∈ K, (K.filter fun y => LNext 11 C w y).card) =
      ∑ y ∈ K, (K.filter fun x => LNext 11 C x y).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hcomm2 : (∑ w ∈ K, ((W \ K).filter fun m => LNext 11 C w m).card) =
      ∑ m ∈ W \ K, (K.filter fun x => LNext 11 C x m).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hv_in0 : (K.filter fun x => LNext 11 C x v.val).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨_, ⟨_, p, g, _, hp, _⟩, _⟩ := Finset.mem_filter.1 hx
    have := v.isLt; omega
  have htot1 : (∑ w ∈ K, (readers 11 C w).card) =
      (∑ w ∈ K, ((readers 11 C w).card - 1)) + K.card := by
    rw [show K.card = ∑ _w ∈ K, 1 by simp, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw; have := hreaders_ge1 w hw; omega
  have htot2 : (∑ y ∈ K, (K.filter fun x => LNext 11 C x y).card) =
      (∑ y ∈ K.erase v.val, ((K.filter fun x => LNext 11 C x y).card - 1)) + (K.erase v.val).card := by
    rw [← Finset.add_sum_erase _ _ hvK, hv_in0, zero_add]
    rw [show (K.erase v.val).card = ∑ _y ∈ K.erase v.val, 1 by simp, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy; have : 1 ≤ (K.filter fun x => LNext 11 C x y).card := Kv_indeg_pos hC v hy; omega
  have her : (K.erase v.val).card + 1 = K.card := Finset.card_erase_add_one hvK
  have hsum_eq : (∑ w ∈ K, (readers 11 C w).card) =
      (∑ y ∈ K, (K.filter fun x => LNext 11 C x y).card) +
      (∑ m ∈ W \ K, (K.filter fun x => LNext 11 C x m).card) := by
    rw [← hcomm1, ← hcomm2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hsplit_out
  change (∑ w ∈ K.filter (Branch 11 C), ((readers 11 C w).card - 1)) + 1 =
    (∑ y ∈ K.erase v.val, ((K.filter fun x => LNext 11 C x y).card - 1)) +
    (∑ m ∈ W \ K, (K.filter fun x => LNext 11 C x m).card)
  rw [← hsum_lhs]
  omega

lemma meeting_gate_in_Kv_indeg2 {C : Circuit} (hC : Monotone2 C) (_he : GraphEval C core5)
    {u w v : Fin 11} (_huw : core5.Adj u w) {m : ℕ}
    (hm : ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ m = 11 + p ∧
      LNext 11 C a m ∧ LNext 11 C b m ∧ a ≠ b ∧ Carries C u a ∧ Carries C w b)
    (hmk : m ∈ Kv C v) :
    open Classical in 2 ≤ ((Kv C v).filter fun x => LNext 11 C x m).card := by
  classical
  obtain ⟨p, g, a, b, hg, hop, rfl, ha, hb, hne, hca, hcb⟩ := hm
  have hp : p < C.gates.length := (List.getElem?_eq_some_iff.1 hg).1
  have halt : a < 11 + p := ha.1.1
  have hblt : b < 11 + p := hb.1.1
  have hmv := mem_Kv.1 hmk
  have hm1 := ((carries_iff hC).1 hmv.2.2).1
  rw [val_gate C _ hg, hop] at hm1
  have hall : ∀ i ∈ g.inputs, operand C (point {v}) (11 + p) i = true := by
    simpa [GateOp.eval, List.all_map, List.all_eq_true] using hm1
  have hin : ∀ x, LNext 11 C x (11 + p) → x ∈ g.inputs := by
    rintro x ⟨⟨_, q, g', hg', hq, hmem⟩, _⟩
    have e : q = p := by omega
    subst q; rw [hg] at hg'; cases hg'; exact hmem
  have ha1 : val C (point {v}) a = true := by
    have := hall a (hin a ha); rwa [operand, ite_eq_left halt] at this
  have hb1 : val C (point {v}) b = true := by
    have := hall b (hin b hb); rwa [operand, ite_eq_left hblt] at this
  have ha0 := ((carries_iff hC).1 hca).2
  have hb0 := ((carries_iff hC).1 hcb).2
  have haK : a ∈ (Kv C v).filter fun x => LNext 11 C x (11 + p) :=
    Finset.mem_filter.2 ⟨mem_Kv.2 ⟨by omega, live_before ha.1 ha.2, (carries_iff hC).2 ⟨ha1, ha0⟩⟩, ha⟩
  have hbK : b ∈ (Kv C v).filter fun x => LNext 11 C x (11 + p) :=
    Finset.mem_filter.2 ⟨mem_Kv.2 ⟨by omega, live_before hb.1 hb.2, (carries_iff hC).2 ⟨hb1, hb0⟩⟩, hb⟩
  have hsub : ({a, b} : Finset ℕ) ⊆ (Kv C v).filter fun x => LNext 11 C x (11 + p) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard := Finset.card_le_card hsub
  simpa [hne] using hcard

noncomputable def nextWire (C : Circuit) (x : ℕ) : ℕ :=
  open Classical in if h : (readers 11 C x).Nonempty then h.choose else x

lemma nextWire_eq {C : Circuit} {x y : ℕ} (hnb : ¬ Branch 11 C x) (hln : LNext 11 C x y) :
    (readers 11 C x).card = 1 ∧ nextWire C x = y := by
  classical
  have hmem : y ∈ readers 11 C x := mem_readers.2 hln
  have hne : (readers 11 C x).Nonempty := ⟨y, hmem⟩
  have hle : (readers 11 C x).card ≤ 1 := by unfold Branch at hnb; omega
  have hge : 1 ≤ (readers 11 C x).card := Finset.card_pos.2 hne
  refine ⟨by omega, ?_⟩
  unfold nextWire
  rw [dite_eq_left hne]
  exact nonbranch_unique hnb (mem_readers.1 hne.choose_spec) hln

noncomputable def chase (C : Circuit) (stop : Finset ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | fuel + 1, x =>
    open Classical in
    if x ∈ stop ∨ Branch 11 C x ∨ (readers 11 C x).card ≠ 1 then x
    else chase C stop fuel (nextWire C x)

lemma chase_stop (C : Circuit) (stop : Finset ℕ) (fuel x : ℕ)
    (hx : x ∈ stop ∨ Branch 11 C x) : chase C stop fuel x = x := by
  cases fuel with
  | zero => rfl
  | succ f =>
    classical
    simp only [chase]
    split_ifs with h
    · rfl
    · exfalso; apply h; rcases hx with h1 | h2; exact Or.inl h1; exact Or.inr (Or.inl h2)

lemma chase_step (C : Circuit) (stop : Finset ℕ) (fuel x y : ℕ)
    (hns : x ∉ stop) (hnb : ¬ Branch 11 C x) (hln : LNext 11 C x y) :
    chase C stop (fuel + 1) x = chase C stop fuel y := by
  classical
  obtain ⟨hc1, hnw⟩ := nextWire_eq hnb hln
  simp only [chase, hns, hnb, hc1, ne_eq, not_true_eq_false, or_self, ↓reduceIte, hnw]

lemma chase_of_trace {C : Circuit} {stop : Finset ℕ} {P : ℕ → Prop} {x t : ℕ}
    (htr : Trace 11 C P x t)
    (hmid : ∀ z, x ≤ z → z < t → P z → z ∉ stop ∧ ¬ Branch 11 C z)
    (hend : t ∈ stop ∨ Branch 11 C t) :
    ∀ fuel, t - x ≤ fuel → chase C stop fuel x = t := by
  induction htr using ReflTransGen.head_induction_on with
  | refl =>
    intro fuel _
    exact chase_stop C stop fuel t hend
  | head hp hrest ih =>
    intro fuel hfuel
    rename_i a b
    have hab : a < b := hp.2.1.1
    have hbt : b ≤ t := trace_le hrest
    have hat : a < t := lt_of_lt_of_le hab hbt
    have hmid_a := hmid a le_rfl hat hp.1
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [chase_step C stop f a b hmid_a.1 hmid_a.2 hp.2]
    exact ih (fun z hbz hzt hPz => hmid z (le_trans hab.le hbz) hzt hPz) f (by omega)

lemma walk_back_in_Kv {C : Circuit} (hC : Monotone2 C) (v : Fin 11) (a : ℕ) :
    open Classical in
    ∀ y, y ∈ Kv C v → ¬ Branch 11 C y →
      Trace 11 C (fun z => z ∈ Kv C v ∧ ¬ Branch 11 C z) y a →
      (∃ b ∈ (Kv C v).filter (Branch 11 C), ∃ r ∈ readers 11 C b,
        Trace 11 C (fun z => z ∈ Kv C v ∧ ¬ Branch 11 C z) r a) ∨
      Trace 11 C (fun z => z ∈ Kv C v ∧ ¬ Branch 11 C z) v.val a := by
  classical
  intro y
  induction y using Nat.strong_induction_on with
  | ind y ih =>
    intro hyK hynb htr
    by_cases hyv : y = v.val
    · subst hyv; exact Or.inr htr
    · have hyer : y ∈ (Kv C v).erase v.val := Finset.mem_erase.2 ⟨hyv, hyK⟩
      have hpos := Kv_indeg_pos hC v hyer
      obtain ⟨x, hx⟩ := Finset.card_pos.1 hpos
      rw [Finset.mem_filter] at hx
      obtain ⟨hxK, hxln⟩ := hx
      by_cases hxb : Branch 11 C x
      · exact Or.inl ⟨x, Finset.mem_filter.2 ⟨hxK, hxb⟩, y, mem_readers.2 hxln, htr⟩
      · exact ih x hxln.1.1 hxK hxb (ReflTransGen.head ⟨⟨hxK, hxb⟩, hxln⟩ htr)

lemma backtrack_to_branch {C : Circuit} (hC : Monotone2 C) {v : Fin 11} (hv : Eligible C v)
    {a m : ℕ} (ha : a ∈ Kv C v) (hm_not : m ∉ Kv C v) (hln : LNext 11 C a m)
    {stop : Finset ℕ} (hm_stop : m ∈ stop) (hstop_K : ∀ z ∈ Kv C v, z ∈ stop → Branch 11 C z) :
    open Classical in
    ∃ b ∈ (Kv C v).filter (Branch 11 C), ∃ r ∈ readers 11 C b,
      chase C stop (11 + C.gates.length) r = m := by
  classical
  have hm_lt : m < 11 + C.gates.length := next_in_range hln.1
  by_cases hab : Branch 11 C a
  · refine ⟨a, Finset.mem_filter.2 ⟨ha, hab⟩, m, mem_readers.2 hln, ?_⟩
    exact chase_stop C stop _ m (Or.inl hm_stop)
  · rcases walk_back_in_Kv hC v a a ha hab .refl with ⟨b, hb, r, hr, htr⟩ | htr
    · refine ⟨b, hb, r, hr, ?_⟩
      have htrm : Trace 11 C (fun z => z ∈ Kv C v ∧ ¬ Branch 11 C z) r m :=
        htr.tail ⟨⟨ha, hab⟩, hln⟩
      refine chase_of_trace htrm ?_ (Or.inl hm_stop) _ (by omega)
      intro z _ _ hPz
      exact ⟨fun hs => hPz.2 (hstop_K z hPz.1 hs), hPz.2⟩
    · exfalso
      have htrm : Trace 11 C (fun z => z ∈ Kv C v ∧ ¬ Branch 11 C z) v.val m :=
        htr.tail ⟨⟨ha, hab⟩, hln⟩
      have hspec := firstBranch_spec v hv
      have hpath := singleton_path hspec.1 hspec.2.1
      rcases align hpath (firstBranch_unique v hv) m htrm with ⟨_, hcm⟩ | hbm
      · exact hm_not (mem_Kv.2 ⟨hm_lt, hln.2, hcm⟩)
      · rcases hbm.cases_head with heq | ⟨_, hstep, _⟩
        · rw [← heq] at hm_not hm_lt
          exact hm_not (mem_Kv.2 ⟨hm_lt, hspec.1, hspec.2.1⟩)
        · exact hstep.1.2 hspec.2.2

lemma first_branch_split {C : Circuit} {v : Fin 11} :
    open Classical in
    ∀ {r w : ℕ}, Trace 11 C (Carries C v) r w → w ∈ (Kv C v).filter (Branch 11 C) →
      ∃ t ∈ (Kv C v).filter (Branch 11 C), r ≤ t ∧ t ≤ w ∧
        Trace 11 C (fun z => z ∈ Kv C v ∧ ¬ Branch 11 C z) r t ∧
        Trace 11 C (Carries C v) t w := by
  classical
  intro r w htr
  induction htr using ReflTransGen.head_induction_on with
  | refl =>
    intro hw
    exact ⟨w, hw, le_rfl, le_rfl, .refl, .refl⟩
  | head hp hrest ih =>
    intro hw
    rename_i a b
    have hla : Live 11 C a := live_before hp.2.1 hp.2.2
    have ha_lt : a < 11 + C.gates.length := lt_trans hp.2.1.1 (next_in_range hp.2.1)
    have haK : a ∈ Kv C v := mem_Kv.2 ⟨ha_lt, hla, hp.1⟩
    by_cases hab : Branch 11 C a
    · exact ⟨a, Finset.mem_filter.2 ⟨haK, hab⟩, le_rfl, trace_le (ReflTransGen.head hp hrest),
        .refl, ReflTransGen.head hp hrest⟩
    · obtain ⟨t, ht, hbt, htw, htr1, htr2⟩ := ih hw
      exact ⟨t, ht, le_trans hp.2.1.1.le hbt, htw, ReflTransGen.head ⟨⟨haK, hab⟩, hp.2⟩ htr1, htr2⟩

lemma branch_reaches_via_chase {C : Circuit} {v : Fin 11} (hv : Eligible C v)
    {w : ℕ} (hw : open Classical in w ∈ (Kv C v).filter (Branch 11 C)) (hne : w ≠ firstBranch C v hv)
    {stop : Finset ℕ} (hstop_K : ∀ z ∈ Kv C v, z ∈ stop → Branch 11 C z) :
    open Classical in
    ∃ r ∈ readers 11 C (firstBranch C v hv),
      ∃ t ∈ ((Kv C v).filter (Branch 11 C)).erase (firstBranch C v hv),
        t ≤ w ∧ chase C stop (11 + C.gates.length) r = t ∧
        Trace 11 C (Carries C v) t w := by
  classical
  let bv := firstBranch C v hv
  have hspec := firstBranch_spec v hv
  have hwK := mem_Kv.1 (Finset.mem_filter.1 hw).1
  have hwb := (Finset.mem_filter.1 hw).2
  have hle : bv ≤ w := firstBranch_le v hv ⟨hwK.2.1, hwK.2.2, hwb⟩
  have hlt : bv < w := lt_of_le_of_ne hle hne.symm
  have hpw := singleton_path hwK.2.1 hwK.2.2
  have hpb := singleton_path hspec.1 hspec.2.1
  rcases align hpb (firstBranch_unique v hv) w hpw with ⟨hlt', _⟩ | hbw
  · omega
  · rcases hbw.cases_head with heq | ⟨r, hstep, hrest⟩
    · exact (hne heq.symm).elim
    · obtain ⟨t, ht, hrt, htw, htr1, htr2⟩ := first_branch_split hrest hw
      have ht_ne : t ≠ bv := by have := hstep.2.1.1; omega
      have ht_lt : t < 11 + C.gates.length := (mem_Kv.1 (Finset.mem_filter.1 ht).1).1
      have hch : chase C stop (11 + C.gates.length) r = t := by
        refine chase_of_trace htr1 ?_ (Or.inr (Finset.mem_filter.1 ht).2) _ (by omega)
        intro z _ _ hPz
        exact ⟨fun hs => hPz.2 (hstop_K z hPz.1 hs), hPz.2⟩
      exact ⟨r, mem_readers.2 hstep.2, t, Finset.mem_erase.2 ⟨ht_ne, ht⟩, htw, hch, htr2⟩

lemma vc_bridge (S : Finset (Fin 11))
    (hvc : ∀ u v : Fin 11, core5.Adj u v → u ∈ S ∨ v ∈ S) :
    open Classical in
    5 ≤ S.card ∧
    (S.card = 5 → S = P5) ∧
    (S.card ≤ 7 → 8 ≤ ∑ v ∈ S,
      max 1 ((Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v u).card +
        (if ∃ w ∈ S, core5.Adj v w then 1 else 0) - 1)) ∧
    (S.card = 6 → ∃ v1 ∈ S, ∃ v2 ∈ S, v1 ≠ v2 ∧
      2 ≤ max 1 ((Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v1 u).card +
        (if ∃ w ∈ S, core5.Adj v1 w then 1 else 0) - 1) ∧
      2 ≤ max 1 ((Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v2 u).card +
        (if ∃ w ∈ S, core5.Adj v2 w then 1 else 0) - 1) ∧
      (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v1 u ∧ core5.Adj v2 u).card +
        (if (∃ w ∈ S, core5.Adj v1 w) ∧ (∃ w ∈ S, core5.Adj v2 w) then 1 else 0) ≤ 1) := by
  classical
  let f : Fin 11 → Bool := fun i => decide (i ∈ S)
  let l := (List.finRange 11).map f
  let m := enc l
  have hm_lt : m < 2048 := by
    have h1 := enc_lt l; have h2 : l.length = 11 := by simp [l]
    rw [h2] at h1; exact h1
  have hm_bit : ∀ i : Fin 11, m.testBit i.val = decide (i ∈ S) := by
    intro i; simp [m, enc_testBit, l, f]
  have hm_bit_nat : ∀ i (hi : i < 11), m.testBit i = true ↔ (⟨i, hi⟩ : Fin 11) ∈ S := by
    intro i hi
    rw [show m.testBit i = decide ((⟨i, hi⟩ : Fin 11) ∈ S) from hm_bit ⟨i, hi⟩, decide_eq_true_eq]
  have hpop : pop11 m = S.card := by
    unfold pop11
    have hnd : ((List.range 11).filter fun i => m.testBit i).Nodup :=
      (List.nodup_range).filter _
    rw [← List.toFinset_card_of_nodup hnd]
    apply Finset.card_bij (fun i hi => ⟨i, by
      have := List.mem_toFinset.1 hi; rw [List.mem_filter, List.mem_range] at this; exact this.1⟩)
    · intro i hi
      have h1 := List.mem_toFinset.1 hi
      rw [List.mem_filter, List.mem_range] at h1
      exact (hm_bit_nat i h1.1).1 h1.2
    · intro a _ b _ h; exact congrArg Fin.val h
    · intro v hv
      refine ⟨v.val, List.mem_toFinset.2 (List.mem_filter.2 ⟨List.mem_range.2 v.isLt, ?_⟩), Fin.ext rfl⟩
      exact (hm_bit_nat v.val v.isLt).2 hv
  have hisvc : isVcB m = true := by
    simp only [isVcB, List.all_eq_true, Bool.or_eq_true]
    intro e he
    have he1 : e.1 < 11 ∧ e.2 < 11 := by
      simp only [core5Edges, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hadj : core5.Adj ⟨e.1, he1.1⟩ ⟨e.2, he1.2⟩ := by
      change core5AdjB _ _ = true
      simp only [core5AdjB, List.any_eq_true]
      exact ⟨e, he, by simp⟩
    rcases hvc _ _ hadj with h1 | h2
    · exact Or.inl ((hm_bit_nat e.1 he1.1).2 h1)
    · exact Or.inr ((hm_bit_nat e.2 he1.2).2 h2)
  have hreq : ∀ v : Fin 11, reqB m v.val =
      max 1 ((Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v u).card +
        (if ∃ w ∈ S, core5.Adj v w then 1 else 0) - 1) := by
    intro v
    have hfv : Fin.ofNat 11 v.val = v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
    have huc : ((List.range 11).filter fun u => !m.testBit u &&
        core5AdjB (Fin.ofNat 11 v.val) (Fin.ofNat 11 u)).length =
        (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v u).card := by
      rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
      apply Finset.card_bij (fun i hi => ⟨i, by
        have := List.mem_toFinset.1 hi; rw [List.mem_filter, List.mem_range] at this; exact this.1⟩)
      · intro i hi
        have h1 := List.mem_toFinset.1 hi
        rw [List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true'] at h1
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun hmem => by
          have := (hm_bit_nat i h1.1).2 hmem; rw [h1.2.1] at this; exact Bool.noConfusion this, ?_⟩
        have hfi : Fin.ofNat 11 i = ⟨i, h1.1⟩ := Fin.ext (Nat.mod_eq_of_lt h1.1)
        have h2 := h1.2.2
        rw [hfv, hfi] at h2
        exact h2
      · intro a _ b _ h; exact congrArg Fin.val h
      · intro u hu
        rw [Finset.mem_filter] at hu
        refine ⟨u.val, List.mem_toFinset.2 (List.mem_filter.2 ⟨List.mem_range.2 u.isLt, ?_⟩), Fin.ext rfl⟩
        rw [Bool.and_eq_true, Bool.not_eq_true']
        have hfu : Fin.ofNat 11 u.val = u := Fin.ext (Nat.mod_eq_of_lt u.isLt)
        refine ⟨?_, by rw [hfv, hfu]; exact hu.2.2⟩
        cases hb : m.testBit u.val
        · rfl
        · exact (hu.2.1 ((hm_bit_nat u.val u.isLt).1 hb)).elim
    have hint : ((List.range 11).any fun u => m.testBit u &&
        core5AdjB (Fin.ofNat 11 v.val) (Fin.ofNat 11 u)) = true ↔ ∃ w ∈ S, core5.Adj v w := by
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
      constructor
      · rintro ⟨u, hu, hb, hadj⟩
        have hfu : Fin.ofNat 11 u = ⟨u, hu⟩ := Fin.ext (Nat.mod_eq_of_lt hu)
        refine ⟨⟨u, hu⟩, (hm_bit_nat u hu).1 hb, ?_⟩
        change core5AdjB v ⟨u, hu⟩ = true
        rw [← hfv, ← hfu]; exact hadj
      · rintro ⟨w, hw, hadj⟩
        have hfw : Fin.ofNat 11 w.val = w := Fin.ext (Nat.mod_eq_of_lt w.isLt)
        exact ⟨w.val, w.isLt, (hm_bit_nat w.val w.isLt).2 hw, by rw [hfv, hfw]; exact hadj⟩
    unfold reqB
    dsimp only
    rw [huc]
    by_cases h : ∃ w ∈ S, core5.Adj v w
    · rw [ite_eq_left h, hint.2 h]; simp
    · have hf : ((List.range 11).any fun u => m.testBit u &&
          core5AdjB (Fin.ofNat 11 v.val) (Fin.ofNat 11 u)) = false := by
        cases hc : (List.range 11).any fun u => m.testBit u &&
            core5AdjB (Fin.ofNat 11 v.val) (Fin.ofNat 11 u)
        · rfl
        · exact (h (hint.1 hc)).elim
      rw [ite_eq_right h, hf]; simp
  have hchk := checkAllVC_true
  simp only [checkAllVC, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hchk
  rcases hchk m hm_lt with hf | hok
  · rw [hisvc] at hf; exact Bool.noConfusion hf
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hc5, heq5⟩, hlb8⟩, hvc6⟩ := hok
    rw [hpop] at hc5 heq5 hlb8 hvc6
    refine ⟨hc5, ?_, ?_, ?_⟩
    · intro h5
      simp only [h5, beq_self_eq_true, ↓reduceIte, beq_iff_eq] at heq5
      ext i
      have h1 := hm_bit i
      rw [heq5] at h1
      have h31 : (31 : ℕ).testBit i.val = decide (i ∈ P5) := by
        fin_cases i <;> decide
      rw [h31] at h1
      simpa using h1.symm
    · intro h7
      simp only [h7, ↓reduceIte, decide_eq_true_eq] at hlb8
      have hsum : (((List.range 11).filter fun v => m.testBit v).map (reqB m)).sum =
          ∑ v ∈ S, reqB m v.val := by
        have hnd : ((List.range 11).filter fun v => m.testBit v).Nodup :=
          (List.nodup_range).filter _
        rw [← List.sum_toFinset _ hnd]
        apply Finset.sum_bij (fun i hi => ⟨i, by
          have := List.mem_toFinset.1 hi; rw [List.mem_filter, List.mem_range] at this; exact this.1⟩)
        · intro i hi
          have h1 := List.mem_toFinset.1 hi; rw [List.mem_filter, List.mem_range] at h1
          exact (hm_bit_nat i h1.1).1 h1.2
        · intro a _ b _ h; exact congrArg Fin.val h
        · intro v hv
          exact ⟨v.val, List.mem_toFinset.2 (List.mem_filter.2 ⟨List.mem_range.2 v.isLt,
            (hm_bit_nat v.val v.isLt).2 hv⟩), Fin.ext rfl⟩
        · intro i _; rfl
      rw [hsum] at hlb8
      simpa only [hreq] using hlb8
    · intro h6
      simp only [h6, beq_self_eq_true, ↓reduceIte, List.any_eq_true, List.mem_range,
        Bool.and_eq_true, decide_eq_true_eq] at hvc6
      obtain ⟨v1n, hv1lt, ⟨hv1m, hv1r⟩, v2n, hv2lt, ⟨⟨⟨hv2m, hlt12⟩, hv2r⟩, hinter⟩⟩ := hvc6
      let v1 : Fin 11 := ⟨v1n, hv1lt⟩
      let v2 : Fin 11 := ⟨v2n, hv2lt⟩
      have hv1S : v1 ∈ S := (hm_bit_nat v1n hv1lt).1 hv1m
      have hv2S : v2 ∈ S := (hm_bit_nat v2n hv2lt).1 hv2m
      have hfv1 : Fin.ofNat 11 v1n = v1 := Fin.ext (Nat.mod_eq_of_lt hv1lt)
      have hfv2 : Fin.ofNat 11 v2n = v2 := Fin.ext (Nat.mod_eq_of_lt hv2lt)
      refine ⟨v1, hv1S, v2, hv2S, fun e => by have := congrArg Fin.val e; dsimp [v1, v2] at this; omega, ?_, ?_, ?_⟩
      · rw [← hreq v1]; exact hv1r
      · rw [← hreq v2]; exact hv2r
      · have hic : ((List.range 11).filter fun u => !m.testBit u &&
            core5AdjB (Fin.ofNat 11 v1n) (Fin.ofNat 11 u) &&
            core5AdjB (Fin.ofNat 11 v2n) (Fin.ofNat 11 u)).length =
            (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v1 u ∧ core5.Adj v2 u).card := by
          rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
          apply Finset.card_bij (fun i hi => ⟨i, by
            have := List.mem_toFinset.1 hi; rw [List.mem_filter, List.mem_range] at this; exact this.1⟩)
          · intro i hi
            have h1 := List.mem_toFinset.1 hi
            rw [List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h1
            have hfi : Fin.ofNat 11 i = ⟨i, h1.1⟩ := Fin.ext (Nat.mod_eq_of_lt h1.1)
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, fun hmem => by
              have := (hm_bit_nat i h1.1).2 hmem; rw [h1.2.1.1] at this; exact Bool.noConfusion this,
              by change core5AdjB v1 ⟨i, h1.1⟩ = true; rw [← hfv1, ← hfi]; exact h1.2.1.2,
              by change core5AdjB v2 ⟨i, h1.1⟩ = true; rw [← hfv2, ← hfi]; exact h1.2.2⟩
          · intro a _ b _ h; exact congrArg Fin.val h
          · intro u hu
            rw [Finset.mem_filter] at hu
            have hfu : Fin.ofNat 11 u.val = u := Fin.ext (Nat.mod_eq_of_lt u.isLt)
            refine ⟨u.val, List.mem_toFinset.2 (List.mem_filter.2 ⟨List.mem_range.2 u.isLt, ?_⟩), Fin.ext rfl⟩
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true']
            refine ⟨⟨?_, by rw [hfv1, hfu]; exact hu.2.2.1⟩,
              by rw [hfv2, hfu]; exact hu.2.2.2⟩
            cases hb : m.testBit u.val
            · rfl
            · exact (hu.2.1 ((hm_bit_nat u.val u.isLt).1 hb)).elim
        have hh1 : ((List.range 11).any fun w => m.testBit w &&
            core5AdjB (Fin.ofNat 11 v1n) (Fin.ofNat 11 w)) = true ↔ ∃ w ∈ S, core5.Adj v1 w := by
          simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
          constructor
          · rintro ⟨w, hw, hb, ha⟩
            have hfw : Fin.ofNat 11 w = ⟨w, hw⟩ := Fin.ext (Nat.mod_eq_of_lt hw)
            refine ⟨⟨w, hw⟩, (hm_bit_nat w hw).1 hb, ?_⟩
            change core5AdjB v1 ⟨w, hw⟩ = true; rw [← hfv1, ← hfw]; exact ha
          · rintro ⟨w, hw, ha⟩
            have hfw : Fin.ofNat 11 w.val = w := Fin.ext (Nat.mod_eq_of_lt w.isLt)
            exact ⟨w.val, w.isLt, (hm_bit_nat w.val w.isLt).2 hw, by rw [hfv1, hfw]; exact ha⟩
        have hh2 : ((List.range 11).any fun w => m.testBit w &&
            core5AdjB (Fin.ofNat 11 v2n) (Fin.ofNat 11 w)) = true ↔ ∃ w ∈ S, core5.Adj v2 w := by
          simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
          constructor
          · rintro ⟨w, hw, hb, ha⟩
            have hfw : Fin.ofNat 11 w = ⟨w, hw⟩ := Fin.ext (Nat.mod_eq_of_lt hw)
            refine ⟨⟨w, hw⟩, (hm_bit_nat w hw).1 hb, ?_⟩
            change core5AdjB v2 ⟨w, hw⟩ = true; rw [← hfv2, ← hfw]; exact ha
          · rintro ⟨w, hw, ha⟩
            have hfw : Fin.ofNat 11 w.val = w := Fin.ext (Nat.mod_eq_of_lt w.isLt)
            exact ⟨w.val, w.isLt, (hm_bit_nat w.val w.isLt).2 hw, by rw [hfv2, hfw]; exact ha⟩
        rw [hic] at hinter
        by_cases h12 : (∃ w ∈ S, core5.Adj v1 w) ∧ (∃ w ∈ S, core5.Adj v2 w)
        · rw [ite_eq_left h12]
          have e1 : ∃ x < 11, m.testBit x = true ∧
              core5AdjB (Fin.ofNat 11 v1n) (Fin.ofNat 11 x) = true := by
            have := hh1.2 h12.1
            simpa [List.any_eq_true, List.mem_range, Bool.and_eq_true] using this
          have e2 : ∃ x < 11, m.testBit x = true ∧
              core5AdjB (Fin.ofNat 11 v2n) (Fin.ofNat 11 x) = true := by
            have := hh2.2 h12.2
            simpa [List.any_eq_true, List.mem_range, Bool.and_eq_true] using this
          rw [ite_eq_left ⟨e1, e2⟩] at hinter
          exact hinter
        · rw [ite_eq_right h12, add_zero]
          exact le_trans (Nat.le_add_right _ _) hinter

set_option maxHeartbeats 800000 in
theorem core5_lb (C : Circuit) (hC : Monotone2 C) (he : GraphEval C core5) : 18 ≤ C.size := by
  classical
  by_contra! hsmall
  have h17 : C.size ≤ 17 := by omega
  have ho_range := edge_at_output he (show core5.Adj 0 5 by change core5AdjB 0 5 = true; decide)
  have ho_live : C.output ∈ living 11 C := mem_living.2 ⟨ho_range.2, .refl⟩
  have hexc_tot := excess_fanout hC he core5_deg_ge_1 ho_live
  let W := living 11 C
  let B := W.filter (Branch 11 C)
  let S : Finset (Fin 11) := Finset.univ.filter (Eligible C)
  have hS_vc : ∀ u v : Fin 11, core5.Adj u v → u ∈ S ∨ v ∈ S := by
    intro u v huv
    obtain ⟨a, b, hua, _, hvb, _, hab⟩ := core5_covers_edge_hyp u v huv
    rcases covers_edge hC he huv hua hvb (Or.inr hab) with h | h
    · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    · exact Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  let fb : Fin 11 → ℕ := fun v => if h : Eligible C v then firstBranch C v h else 0
  have hfb_eq : ∀ (v : Fin 11) (hv : Eligible C v), fb v = firstBranch C v hv := fun v hv => dite_eq_left hv
  have hfb_in_B : ∀ v ∈ S, fb v ∈ B := by
    intro v hv
    have hel : Eligible C v := (Finset.mem_filter.1 hv).2
    rw [hfb_eq v hel]
    have hsp := firstBranch_spec v hel
    have hne : (readers 11 C (firstBranch C v hel)).Nonempty :=
      Finset.card_pos.1 (by have := hsp.2.2; unfold Branch at this; omega)
    obtain ⟨y, hy⟩ := hne
    have hlt := lt_trans (mem_readers.1 hy).1.1 (next_in_range (mem_readers.1 hy).1)
    exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hlt, hsp.1⟩, hsp.2.2⟩
  have hfb_inj : Set.InjOn fb (S : Set (Fin 11)) := by
    intro v hv w hw hvw
    have hv' := (Finset.mem_filter.1 hv).2
    have hw' := (Finset.mem_filter.1 hw).2
    rw [hfb_eq v hv', hfb_eq w hw'] at hvw
    exact branch_injective_core5 hC he hv' hw' hvw
  let B1 := S.image fb
  let B2 := B \ B1
  have hB1_sub : B1 ⊆ B := by
    intro w hw; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw; exact hfb_in_B v hv
  have hB1_card : B1.card = S.card := Finset.card_image_of_injOn hfb_inj
  have hB_split : (∑ w ∈ B, ((readers 11 C w).card - 1)) =
      (∑ w ∈ B1, ((readers 11 C w).card - 1)) + (∑ w ∈ B2, ((readers 11 C w).card - 1)) := by
    have hdisj : Disjoint B1 B2 := Finset.disjoint_sdiff
    rw [← Finset.sum_union hdisj, Finset.union_sdiff_of_subset hB1_sub]
  have hB_le7 : (∑ w ∈ B1, ((readers 11 C w).card - 1)) + (∑ w ∈ B2, ((readers 11 C w).card - 1)) ≤ 7 := by
    change 11 + ∑ w ∈ B, ((readers 11 C w).card - 1) ≤ C.size + 1 at hexc_tot
    rw [← hB_split]; omega
  have hB1_sum : (∑ w ∈ B1, ((readers 11 C w).card - 1)) = ∑ v ∈ S, ((readers 11 C (fb v)).card - 1) :=
    Finset.sum_image (fun a ha b hb h => hfb_inj ha hb h)
  have hB1_ge_S : S.card ≤ ∑ w ∈ B1, ((readers 11 C w).card - 1) := by
    rw [hB1_sum, show S.card = ∑ _v ∈ S, 1 by simp]
    apply Finset.sum_le_sum
    intro v hv
    have hb : Branch 11 C (fb v) := (Finset.mem_filter.1 (hfb_in_B v hv)).2
    unfold Branch at hb; omega
  have hB2_card_le : B2.card ≤ ∑ w ∈ B2, ((readers 11 C w).card - 1) := by
    rw [show B2.card = ∑ _w ∈ B2, 1 by simp]
    apply Finset.sum_le_sum
    intro w hw
    have hb : Branch 11 C w := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hw).1).2
    unfold Branch at hb; omega
  obtain ⟨hS_ge5, hS_eq5, hS_lb8, hS_vc6⟩ := vc_bridge S hS_vc
  have hS_le7 : S.card ≤ 7 := by omega
  have hKvB_sub : ∀ v ∈ S, (Kv C v).filter (Branch 11 C) ⊆ insert (fb v) B2 := by
    intro v hv w hw
    have hwK := (Finset.mem_filter.1 hw).1
    have hwb := (Finset.mem_filter.1 hw).2
    have hwB : w ∈ B := Finset.mem_filter.2 ⟨Kv_sub_living hwK, hwb⟩
    by_cases h1 : w ∈ B1
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h1
      have huv : u = v := by
        by_contra hne
        have hel := (Finset.mem_filter.1 hu).2
        have h0 := branch_disjoint hC he hel (Ne.symm hne)
        rw [← hfb_eq u hel] at h0
        have h1' := ((carries_iff hC).1 (mem_Kv.1 hwK).2.2).1
        rw [h0] at h1'; exact Bool.noConfusion h1'
      subst huv; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.2 ⟨hwB, h1⟩)
  have hfb_mem_KvB : ∀ v ∈ S, fb v ∈ (Kv C v).filter (Branch 11 C) := by
    intro v hv
    have hel := (Finset.mem_filter.1 hv).2
    rw [hfb_eq v hel]
    have hsp := firstBranch_spec v hel
    have hB := hfb_in_B v hv
    rw [hfb_eq v hel] at hB
    exact Finset.mem_filter.2 ⟨mem_Kv.2 ⟨(mem_living.1 (Finset.mem_filter.1 hB).1).1, hsp.1, hsp.2.1⟩, hsp.2.2⟩
  have hfb_not_B2 : ∀ v ∈ S, fb v ∉ B2 := fun v hv h =>
    (Finset.mem_sdiff.1 h).2 (Finset.mem_image.2 ⟨v, hv, rfl⟩)
  have hmg_pick : ∀ u v : Fin 11, core5.Adj u v →
      ∃ m, (∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ m = 11 + p ∧
        Live 11 C m ∧ LNext 11 C a m ∧ LNext 11 C b m ∧ a ≠ b ∧
        val C (point {u}) m = false ∧ val C (point {v}) m = false ∧
        Carries C u a ∧ ¬ Carries C v a ∧ Carries C v b ∧ ¬ Carries C u b ∧
        (∀ i ∈ g.inputs, i = a ∨ i = b)) := by
    intro u v huv
    obtain ⟨p, g, a, b, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := meeting_gate hC he huv
    exact ⟨11 + p, p, g, a, b, h1, h2, rfl, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  let mg (u v : Fin 11) (h : core5.Adj u v) : ℕ := (hmg_pick u v h).choose
  have mg_spec : ∀ (u v : Fin 11) (h : core5.Adj u v),
      ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ mg u v h = 11 + p ∧
        Live 11 C (mg u v h) ∧ LNext 11 C a (mg u v h) ∧ LNext 11 C b (mg u v h) ∧ a ≠ b ∧
        val C (point {u}) (mg u v h) = false ∧ val C (point {v}) (mg u v h) = false ∧
        Carries C u a ∧ ¬ Carries C v a ∧ Carries C v b ∧ ¬ Carries C u b ∧
        (∀ i ∈ g.inputs, i = a ∨ i = b) := fun u v h => (hmg_pick u v h).choose_spec
  have mg_exit : ∀ (u v : Fin 11) (h : core5.Adj u v),
      mg u v h ∈ W \ Kv C u ∧ ∃ a ∈ Kv C u, LNext 11 C a (mg u v h) := by
    intro u v h
    obtain ⟨p, g, a, b, hg, _, hme, hl, hna, _, _, hvu, _, hca, _, _, _, _⟩ := mg_spec u v h
    have hlt : mg u v h < 11 + C.gates.length := next_in_range hna.1
    have hnot : mg u v h ∉ Kv C u := by
      intro hm; have := ((carries_iff hC).1 (mem_Kv.1 hm).2.2).1; rw [hvu] at this; exact Bool.noConfusion this
    exact ⟨Finset.mem_sdiff.2 ⟨mem_living.2 ⟨hlt, hl⟩, hnot⟩,
      a, mem_Kv.2 ⟨lt_trans hna.1.1 hlt, live_before hna.1 hna.2, hca⟩, hna⟩
  have mg_ext_not_Kv : ∀ (v u z : Fin 11) (h : core5.Adj v u), u ∉ S → mg v u h ∉ Kv C z := by
    intro v u z h huS hmk
    have hu_nel : ¬ Eligible C u := fun hel => huS (Finset.mem_filter.2 ⟨Finset.mem_univ _, hel⟩)
    obtain ⟨p, g, a, b, hg, hop, hme, hl, _, hnb, _, _, hvu, _, _, hcb, _, _⟩ := mg_spec v u h
    by_cases hzu : z = u
    · subst hzu
      have h1 := ((carries_iff hC).1 (mem_Kv.1 hmk).2.2).1
      rw [hvu] at h1; exact Bool.noConfusion h1
    · have h1 := ((carries_iff hC).1 (mem_Kv.1 hmk).2.2).1
      rw [hme, val_gate C _ hg, hop] at h1
      have hall : ∀ i ∈ g.inputs, operand C (point {z}) (11 + p) i = true := by
        simpa [GateOp.eval, List.all_map, List.all_eq_true] using h1
      have hbin : b ∈ g.inputs := by
        obtain ⟨⟨_, q, g', hg', hq, hmem⟩, _⟩ := hnb
        have e : q = p := by omega
        subst q; rw [hg] at hg'; cases hg'; exact hmem
      have hb1 := hall b hbin
      have hblt : b < 11 + p := by rw [← hme]; exact hnb.1.1
      rw [operand, ite_eq_left hblt] at hb1
      have hb0 := non_eligible_pure hC he hu_nel hzu (live_before hnb.1 hnb.2) hcb
      rw [hb0] at hb1; exact Bool.noConfusion hb1
  have mg_ext_tag : ∀ (v1 u1 v2 u2 : Fin 11) (h1 : core5.Adj v1 u1) (h2 : core5.Adj v2 u2),
      u1 ∉ S → v2 ∈ S → (u2 ∉ S → u1 ≠ u2) → mg v1 u1 h1 ≠ mg v2 u2 h2 := by
    intro v1 u1 v2 u2 h1 h2 hu1 hv2 hne heq
    have hu1_nel : ¬ Eligible C u1 := fun hel => hu1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hel⟩)
    obtain ⟨p1, g1, a1, b1, hg1, _, hm1, _, _, hnb1, _, _, _, _, _, hcb1, _, _⟩ := mg_spec v1 u1 h1
    obtain ⟨p2, g2, a2, b2, hg2, _, hm2, _, hna2, hnb2, _, _, _, hca2, _, hcb2, _, hin2⟩ := mg_spec v2 u2 h2
    have ep : p1 = p2 := by omega
    subst ep
    rw [hg1] at hg2; cases hg2
    have hb1_in : b1 ∈ g1.inputs := by
      obtain ⟨⟨_, q, g', hg', hq, hmem⟩, _⟩ := hnb1
      have e : q = p1 := by omega
      subst q; rw [hg1] at hg'; cases hg'; exact hmem
    rcases hin2 b1 hb1_in with rfl | rfl
    · have hv2_ne : v2 ≠ u1 := fun e => hu1 (e ▸ hv2)
      have h0 := non_eligible_pure hC he hu1_nel hv2_ne (live_before hnb1.1 hnb1.2) hcb1
      have h1' := ((carries_iff hC).1 hca2).1
      rw [h0] at h1'; exact Bool.noConfusion h1'
    · have hu2_ne : u2 ≠ u1 := by
        by_cases hu2S : u2 ∈ S
        · exact fun e => hu1 (e ▸ hu2S)
        · exact (hne hu2S).symm
      have h0 := non_eligible_pure hC he hu1_nel hu2_ne (live_before hnb1.1 hnb1.2) hcb1
      have h1' := ((carries_iff hC).1 hcb2).1
      rw [h0] at h1'; exact Bool.noConfusion h1'
  let extM (v : Fin 11) : Finset ℕ :=
    (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v u).attach.image
      fun u => mg v u.1 (Finset.mem_filter.1 u.2).2.2
  let intM (v : Fin 11) : Finset ℕ :=
    if h : ∃ w ∈ S, core5.Adj v w then {mg v h.choose h.choose_spec.2} else ∅
  let chosenM (v : Fin 11) : Finset ℕ := extM v ∪ intM v
  have hchosenM_card : ∀ v ∈ S, (chosenM v).card =
      (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v u).card +
      (if ∃ w ∈ S, core5.Adj v w then 1 else 0) := by
    intro v hv
    have hext_card : (extM v).card = (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v u).card := by
      rw [← Finset.card_attach (s := Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v u)]
      apply Finset.card_image_of_injective
      intro a b hab
      apply Subtype.ext
      by_contra hne
      have ha := (Finset.mem_filter.1 a.2).2
      have hb := (Finset.mem_filter.1 b.2).2
      exact mg_ext_tag v a.1 v b.1 ha.2 hb.2 ha.1 hv (fun _ => hne) hab
    have hdisj : Disjoint (extM v) (intM v) := by
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hm1
      have ha := (Finset.mem_filter.1 a.2).2
      unfold intM at hm2
      split_ifs at hm2 with hint
      · rw [Finset.mem_singleton] at hm2
        exact mg_ext_tag v a.1 v hint.choose ha.2 hint.choose_spec.2 ha.1 hv
          (fun hn => (hn hint.choose_spec.1).elim) hm2
      · simp at hm2
    rw [Finset.card_union_of_disjoint hdisj, hext_card]
    unfold intM
    split_ifs <;> simp
  have hchosenM_exit : ∀ v ∈ S, ∀ m ∈ chosenM v, m ∈ W \ Kv C v ∧ ∃ a ∈ Kv C v, LNext 11 C a m := by
    intro v _ m hm
    rcases Finset.mem_union.1 hm with h1 | h2
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 h1
      exact mg_exit v a.1 (Finset.mem_filter.1 a.2).2.2
    · unfold intM at h2
      split_ifs at h2 with hint
      · rw [Finset.mem_singleton] at h2; subst h2
        exact mg_exit v hint.choose hint.choose_spec.2
      · simp at h2
  have hchosenM_le_Eout : ∀ v ∈ S,
      (chosenM v).card ≤ ∑ m ∈ W \ Kv C v, ((Kv C v).filter fun x => LNext 11 C x m).card := by
    intro v hv
    calc (chosenM v).card = ∑ _m ∈ chosenM v, 1 := by simp
      _ ≤ ∑ m ∈ chosenM v, ((Kv C v).filter fun x => LNext 11 C x m).card := by
          apply Finset.sum_le_sum
          intro m hm
          obtain ⟨_, a, ha, hln⟩ := hchosenM_exit v hv m hm
          exact Finset.card_pos.2 ⟨a, Finset.mem_filter.2 ⟨ha, hln⟩⟩
      _ ≤ ∑ m ∈ W \ Kv C v, ((Kv C v).filter fun x => LNext 11 C x m).card := by
          apply Finset.sum_le_sum_of_subset
          intro m hm; exact (hchosenM_exit v hv m hm).1
  have hKv_exc_ge : ∀ v ∈ S,
      max 1 ((chosenM v).card - 1) ≤ ∑ w ∈ (Kv C v).filter (Branch 11 C), ((readers 11 C w).card - 1) := by
    intro v hv
    have hd := dag_sum_Kv hC he v
    have he1 := hchosenM_le_Eout v hv
    have hfb1 : 1 ≤ ∑ w ∈ (Kv C v).filter (Branch 11 C), ((readers 11 C w).card - 1) := by
      have hm := hfb_mem_KvB v hv
      have hb : Branch 11 C (fb v) := (Finset.mem_filter.1 hm).2
      have hle := Finset.single_le_sum (f := fun w => (readers 11 C w).card - 1)
        (fun _ _ => Nat.zero_le _) hm
      unfold Branch at hb; omega
    dsimp only [W] at he1
    omega
  have hKv_exc_le : ∀ v ∈ S,
      (∑ w ∈ (Kv C v).filter (Branch 11 C), ((readers 11 C w).card - 1)) ≤
        ((readers 11 C (fb v)).card - 1) + ∑ w ∈ B2, ((readers 11 C w).card - 1) := by
    intro v hv
    calc (∑ w ∈ (Kv C v).filter (Branch 11 C), ((readers 11 C w).card - 1))
        ≤ ∑ w ∈ insert (fb v) B2, ((readers 11 C w).card - 1) :=
          Finset.sum_le_sum_of_subset (hKvB_sub v hv)
      _ = ((readers 11 C (fb v)).card - 1) + ∑ w ∈ B2, ((readers 11 C w).card - 1) :=
          Finset.sum_insert (hfb_not_B2 v hv)
  have hchosenM_inter : ∀ v1 ∈ S, ∀ v2 ∈ S,
      (chosenM v1 ∩ chosenM v2).card ≤
        (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v1 u ∧ core5.Adj v2 u).card +
        (if (∃ w ∈ S, core5.Adj v1 w) ∧ (∃ w ∈ S, core5.Adj v2 w) then 1 else 0) := by
    intro v1 hv1 v2 hv2
    let extI := (chosenM v1 ∩ chosenM v2).filter (· ∈ extM v1)
    let intI := (chosenM v1 ∩ chosenM v2).filter (· ∉ extM v1)
    have hsplit : (chosenM v1 ∩ chosenM v2).card = extI.card + intI.card := by
      have hdisj : Disjoint extI intI := Finset.disjoint_left.2 fun m hm1 hm2 =>
        (Finset.mem_filter.1 hm2).2 (Finset.mem_filter.1 hm1).2
      rw [← Finset.card_union_of_disjoint hdisj]
      congr 1; ext m; simp only [extI, intI, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro h; by_cases hm : m ∈ extM v1
        · exact Or.inl ⟨h, hm⟩
        · exact Or.inr ⟨h, hm⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    rw [hsplit]
    apply Nat.add_le_add
    · let U12 := Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v1 u ∧ core5.Adj v2 u
      have hsub : extI ⊆ U12.attach.image fun u => mg v1 u.1 (Finset.mem_filter.1 u.2).2.2.1 := by
        intro m hm
        have hm12 := (Finset.mem_filter.1 hm).1
        have hm_e1 := (Finset.mem_filter.1 hm).2
        have hm_c2 := (Finset.mem_inter.1 hm12).2
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hm_e1
        have ha := (Finset.mem_filter.1 a.2).2
        have ha2 : core5.Adj v2 a.1 := by
          rcases Finset.mem_union.1 hm_c2 with h2e | h2i
          · obtain ⟨b, _, hmb⟩ := Finset.mem_image.1 h2e
            have hb := (Finset.mem_filter.1 b.2).2
            have hab : a.1 = b.1 := by
              by_contra hne
              exact mg_ext_tag v1 a.1 v2 b.1 ha.2 hb.2 ha.1 hv2 (fun _ => hne) hmb.symm
            exact hab ▸ hb.2
          · unfold intM at h2i
            split_ifs at h2i with hint
            · rw [Finset.mem_singleton] at h2i
              exact (mg_ext_tag v1 a.1 v2 hint.choose ha.2 hint.choose_spec.2 ha.1 hv2
                (fun hn => (hn hint.choose_spec.1).elim) h2i).elim
            · simp at h2i
        exact Finset.mem_image.2 ⟨⟨a.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha.1, ha.2, ha2⟩⟩,
          Finset.mem_attach _ _, rfl⟩
      exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp [U12]))
    · by_cases h12 : (∃ w ∈ S, core5.Adj v1 w) ∧ (∃ w ∈ S, core5.Adj v2 w)
      · rw [ite_eq_left h12]
        have hsub : intI ⊆ intM v1 := by
          intro m hm
          have h1 := (Finset.mem_inter.1 (Finset.mem_filter.1 hm).1).1
          have h2 := (Finset.mem_filter.1 hm).2
          exact (Finset.mem_union.1 h1).resolve_left h2
        refine (Finset.card_le_card hsub).trans ?_
        unfold intM; rw [dite_eq_left h12.1]; simp
      · rw [ite_eq_right h12]
        have hemp : intI = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro m hm
          have h12m := (Finset.mem_filter.1 hm).1
          have hne1 := (Finset.mem_filter.1 hm).2
          have hi1 : m ∈ intM v1 := (Finset.mem_union.1 (Finset.mem_inter.1 h12m).1).resolve_left hne1
          unfold intM at hi1
          split_ifs at hi1 with h1
          · rw [Finset.mem_singleton] at hi1; subst hi1
            have h2 : ¬ ∃ w ∈ S, core5.Adj v2 w := fun h2 => h12 ⟨h1, h2⟩
            have hc2 := (Finset.mem_inter.1 h12m).2
            have he2 : mg v1 h1.choose h1.choose_spec.2 ∈ extM v2 := by
              rcases Finset.mem_union.1 hc2 with he2 | hi2
              · exact he2
              · unfold intM at hi2; rw [dite_eq_right h2] at hi2; simp at hi2
            obtain ⟨b, _, hmb⟩ := Finset.mem_image.1 he2
            have hb := (Finset.mem_filter.1 b.2).2
            exact mg_ext_tag v2 b.1 v1 h1.choose hb.2 h1.choose_spec.2 hb.1 hv1
              (fun hn => (hn h1.choose_spec.1).elim) hmb
          · simp at hi1
        simp [hemp]
  have hB2_le2 : ∑ w ∈ B2, ((readers 11 C w).card - 1) ≤ 2 := by omega
  have hcase_e2_1 : ∀ (wstar : ℕ), B2 = {wstar} → (readers 11 C wstar).card = 2 →
      ∀ v1 ∈ S, ∀ v2 ∈ S,
        (readers 11 C (fb v1)).card = 2 → (readers 11 C (fb v2)).card = 2 →
        3 ≤ (chosenM v1).card → 3 ≤ (chosenM v2).card →
        (chosenM v1 ∩ chosenM v2).card ≤ 1 → False := by
    intro wstar hB2eq hw2 v1 hv1 v2 hv2 hfb1 hfb2 hc1 hc2 hinter
    have hno_mg_in_Kv : ∀ v ∈ S, (readers 11 C (fb v)).card = 2 → 3 ≤ (chosenM v).card →
        ∀ m ∈ chosenM v1 ∪ chosenM v2, m ∉ Kv C v := by
      intro v hv hfbv hcv m hm hmk
      have hd := dag_sum_Kv hC he v
      have hle := hKv_exc_le v hv
      rw [hB2eq, Finset.sum_singleton, hw2, hfbv] at hle
      have heout := hchosenM_le_Eout v hv
      have hmg_in : 2 ≤ ((Kv C v).filter fun x => LNext 11 C x m).card := by
        have hspec_m : ∃ (u w : Fin 11) (huw : core5.Adj u w), m = mg u w huw := by
          rcases Finset.mem_union.1 hm with hm1 | hm2
          · rcases Finset.mem_union.1 hm1 with h1 | h2
            · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 h1
              exact ⟨v1, a.1, (Finset.mem_filter.1 a.2).2.2, rfl⟩
            · unfold intM at h2; split_ifs at h2 with hi
              · rw [Finset.mem_singleton] at h2; exact ⟨v1, hi.choose, hi.choose_spec.2, h2⟩
              · simp at h2
          · rcases Finset.mem_union.1 hm2 with h1 | h2
            · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 h1
              exact ⟨v2, a.1, (Finset.mem_filter.1 a.2).2.2, rfl⟩
            · unfold intM at h2; split_ifs at h2 with hi
              · rw [Finset.mem_singleton] at h2; exact ⟨v2, hi.choose, hi.choose_spec.2, h2⟩
              · simp at h2
        obtain ⟨u, w, huw, rfl⟩ := hspec_m
        obtain ⟨p, g, a, b, hg, hop, hme, _, hna, hnb, hne, _, _, hca, _, hcb, _, _⟩ := mg_spec u w huw
        exact meeting_gate_in_Kv_indeg2 hC he huw ⟨p, g, a, b, hg, hop, hme, hna, hnb, hne, hca, hcb⟩ hmk
      have hm_ne_v : m ≠ v.val := by
        have hlt : 11 ≤ m := by
          rcases Finset.mem_union.1 hm with hm1 | hm2
          · rcases Finset.mem_union.1 hm1 with h1 | h2
            · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 h1
              obtain ⟨p, _, _, _, _, _, hme, _⟩ := mg_spec v1 a.1 (Finset.mem_filter.1 a.2).2.2; omega
            · unfold intM at h2; split_ifs at h2 with hi
              · rw [Finset.mem_singleton] at h2; subst h2
                obtain ⟨p, _, _, _, _, _, hme, _⟩ := mg_spec v1 hi.choose hi.choose_spec.2; omega
              · simp at h2
          · rcases Finset.mem_union.1 hm2 with h1 | h2
            · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 h1
              obtain ⟨p, _, _, _, _, _, hme, _⟩ := mg_spec v2 a.1 (Finset.mem_filter.1 a.2).2.2; omega
            · unfold intM at h2; split_ifs at h2 with hi
              · rw [Finset.mem_singleton] at h2; subst h2
                obtain ⟨p, _, _, _, _, _, hme, _⟩ := mg_spec v2 hi.choose hi.choose_spec.2; omega
              · simp at h2
        have := v.isLt; omega
      have hmer : m ∈ (Kv C v).erase v.val := Finset.mem_erase.2 ⟨hm_ne_v, hmk⟩
      have h1_indeg := Finset.single_le_sum
        (f := fun y => ((Kv C v).filter fun x => LNext 11 C x y).card - 1)
        (fun _ _ => Nat.zero_le _) hmer
      dsimp only [W] at heout
      omega
    let stop := chosenM v1 ∪ chosenM v2
    let fuel := 11 + C.gates.length
    let Wimgs := (readers 11 C wstar).image (chase C stop fuel)
    have hWimgs_le : Wimgs.card ≤ 2 := Finset.card_image_le.trans (by omega)
    have hhits2 : ∀ v ∈ S, (readers 11 C (fb v)).card = 2 → 3 ≤ (chosenM v).card →
        chosenM v ⊆ stop → 2 ≤ (chosenM v ∩ Wimgs).card := by
      intro v hv hfbv hcv hsub_st
      have hel := (Finset.mem_filter.1 hv).2
      have hstop_K : ∀ z ∈ Kv C v, z ∈ stop → Branch 11 C z := fun z hz hst =>
        (hno_mg_in_Kv v hv hfbv hcv z hst hz).elim
      have hw_in_Kv : wstar ∈ (Kv C v).filter (Branch 11 C) := by
        by_contra hnot
        have hsub1 : (Kv C v).filter (Branch 11 C) ⊆ {fb v} := by
          intro x hx
          have := hKvB_sub v hv hx
          rw [hB2eq, Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | rfl
          · exact Finset.mem_singleton_self _
          · exact (hnot hx).elim
        have hle := Finset.sum_le_sum_of_subset (f := fun w => (readers 11 C w).card - 1) hsub1
        rw [Finset.sum_singleton, hfbv] at hle
        have hge := hKv_exc_ge v hv
        omega
      have hw_ne : wstar ≠ firstBranch C v hel := by
        rw [← hfb_eq v hel]
        exact fun e => hfb_not_B2 v hv (by rw [hB2eq, e]; exact Finset.mem_singleton_self _)
      obtain ⟨r0, hr0, t0, ht0, _, hch0, _⟩ := branch_reaches_via_chase hel hw_in_Kv hw_ne hstop_K
      have ht0_eq : t0 = wstar := by
        have h1 := hKvB_sub v hv (Finset.mem_erase.1 ht0).2
        rw [hB2eq, Finset.mem_insert, Finset.mem_singleton] at h1
        rcases h1 with h1 | h1
        · exact ((Finset.mem_erase.1 ht0).1 (h1.trans (hfb_eq v hel))).elim
        · exact h1
      subst ht0_eq
      have hr0_mem : r0 ∈ readers 11 C (fb v) := by rwa [hfb_eq v hel]
      have hother_card : ((readers 11 C (fb v)).erase r0).card = 1 := by
        have := Finset.card_erase_add_one hr0_mem; omega
      let Fimgs := ((readers 11 C (fb v)).erase r0).image (chase C stop fuel)
      have hFimgs_le : Fimgs.card ≤ 1 := Finset.card_image_le.trans (by omega)
      have hcov_ch : chosenM v ⊆ Fimgs ∪ Wimgs := by
        intro m hm
        obtain ⟨_, a, ha, hln⟩ := hchosenM_exit v hv m hm
        have hm_not : m ∉ Kv C v := (hchosenM_exit v hv m hm).1 |> fun h => (Finset.mem_sdiff.1 h).2
        obtain ⟨b, hb, r, hr, hchr⟩ := backtrack_to_branch hC hel ha hm_not hln (hsub_st hm) hstop_K
        have hb_mem := hKvB_sub v hv hb
        rw [hB2eq, Finset.mem_insert, Finset.mem_singleton] at hb_mem
        rcases hb_mem with rfl | rfl
        · by_cases hrr0 : r = r0
          · subst hrr0
            rw [hch0] at hchr
            exfalso
            exact hno_mg_in_Kv v hv hfbv hcv m (hsub_st hm) (hchr ▸ (Finset.mem_filter.1 hw_in_Kv).1)
          · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨r, Finset.mem_erase.2 ⟨hrr0, hr⟩, hchr⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨r, hr, hchr⟩)
      have h1 : (chosenM v).card ≤ (chosenM v ∩ Fimgs).card + (chosenM v ∩ Wimgs).card := by
        calc (chosenM v).card ≤ ((chosenM v ∩ Fimgs) ∪ (chosenM v ∩ Wimgs)).card := by
              apply Finset.card_le_card; intro m hm
              rcases Finset.mem_union.1 (hcov_ch hm) with h | h
              · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hm, h⟩)
              · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hm, h⟩)
          _ ≤ (chosenM v ∩ Fimgs).card + (chosenM v ∩ Wimgs).card := Finset.card_union_le _ _
      have h2 : (chosenM v ∩ Fimgs).card ≤ 1 :=
        (Finset.card_le_card Finset.inter_subset_right).trans hFimgs_le
      omega
    have h1 := hhits2 v1 hv1 hfb1 hc1 Finset.subset_union_left
    have h2 := hhits2 v2 hv2 hfb2 hc2 Finset.subset_union_right
    have he1 : Wimgs = chosenM v1 ∩ Wimgs :=
      (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)).symm
    have hsub1 : Wimgs ⊆ chosenM v1 := by
      intro x hx; rw [he1] at hx; exact (Finset.mem_inter.1 hx).1
    have hsub2 : chosenM v2 ∩ Wimgs ⊆ chosenM v1 ∩ chosenM v2 := by
      intro x hx
      rw [Finset.mem_inter] at hx ⊢
      exact ⟨hsub1 hx.2, hx.1⟩
    have := Finset.card_le_card hsub2
    omega
  interval_cases hE2 : ∑ w ∈ B2, ((readers 11 C w).card - 1)
  · have hB2_emp : B2 = ∅ := Finset.card_eq_zero.1 (by omega)
    have hsum_le : ∑ v ∈ S,
        max 1 ((Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj v u).card +
          (if ∃ w ∈ S, core5.Adj v w then 1 else 0) - 1) ≤ 7 := by
      calc _ = ∑ v ∈ S, max 1 ((chosenM v).card - 1) := by
              apply Finset.sum_congr rfl; intro v hv; rw [hchosenM_card v hv]
        _ ≤ ∑ v ∈ S, ∑ w ∈ (Kv C v).filter (Branch 11 C), ((readers 11 C w).card - 1) :=
              Finset.sum_le_sum (fun v hv => hKv_exc_ge v hv)
        _ ≤ ∑ v ∈ S, ((readers 11 C (fb v)).card - 1) := by
              apply Finset.sum_le_sum; intro v hv
              have := hKv_exc_le v hv; omega
        _ = ∑ w ∈ B1, ((readers 11 C w).card - 1) := hB1_sum.symm
        _ ≤ 7 := by omega
    have h8 := hS_lb8 hS_le7
    omega
  · have hB2_c1 : B2.card = 1 := by
      have hpos : 0 < B2.card := by
        by_contra h0
        have he0 : B2 = ∅ := Finset.card_eq_zero.1 (by omega)
        rw [he0, Finset.sum_empty] at hE2; omega
      omega
    obtain ⟨wstar, hB2eq⟩ := Finset.card_eq_one.1 hB2_c1
    have hw2 : (readers 11 C wstar).card = 2 := by
      rw [hB2eq, Finset.sum_singleton] at hE2
      have hb : Branch 11 C wstar := (Finset.mem_filter.1 (Finset.mem_sdiff.1 (hB2eq ▸ Finset.mem_singleton_self wstar)).1).2
      unfold Branch at hb; omega
    have hS_le6 : S.card ≤ 6 := by omega
    interval_cases hSc : S.card
    · have hSP5 : S = P5 := hS_eq5 rfl
      have hB1_le6 : ∑ v ∈ S, ((readers 11 C (fb v)).card - 1) ≤ 6 := by rw [← hB1_sum]; omega
      let Big := P4.filter fun p => 3 ≤ (readers 11 C (fb p)).card
      have hBig_le1 : Big.card ≤ 1 := by
        have hP4S : P4 ⊆ S := by rw [hSP5]; decide
        have h1 : S.card + Big.card ≤ ∑ v ∈ S, ((readers 11 C (fb v)).card - 1) := by
          have e1 : S.card = ∑ _v ∈ S, 1 := by simp
          have e2 : Big.card = ∑ v ∈ S, (if v ∈ Big then 1 else 0) := by
            rw [← Finset.sum_filter]
            have : S.filter (· ∈ Big) = Big := by
              ext x; simp only [Finset.mem_filter, and_iff_right_iff_imp]
              intro hx; exact hP4S (Finset.mem_filter.1 hx).1
            rw [this]; simp
          rw [e1, e2, ← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro v hv
          have hb : Branch 11 C (fb v) := (Finset.mem_filter.1 (hfb_in_B v hv)).2
          unfold Branch at hb
          by_cases hvb : v ∈ Big
          · have h3 := (Finset.mem_filter.1 hvb).2; simp [hvb]; omega
          · simp [hvb]; omega
        omega
      let Small := P4 \ Big
      have hSmall_ge3 : 3 ≤ Small.card := by
        have hP4c : P4.card = 4 := by decide
        have hsub : Big ⊆ P4 := Finset.filter_subset _ _
        have := Finset.card_sdiff_add_card_eq_card hsub
        dsimp only [Small]
        omega
      obtain ⟨p1, hp1, p2, hp2, hne12⟩ := Finset.one_lt_card.1 (by omega : 1 < Small.card)
      have hp1P4 : p1 ∈ P4 := (Finset.mem_sdiff.1 hp1).1
      have hp2P4 : p2 ∈ P4 := (Finset.mem_sdiff.1 hp2).1
      have hP4S : P4 ⊆ S := by rw [hSP5]; decide
      have hp1S := hP4S hp1P4
      have hp2S := hP4S hp2P4
      have hfb1 : (readers 11 C (fb p1)).card = 2 := by
        have hnb : p1 ∉ Big := (Finset.mem_sdiff.1 hp1).2
        have hb : Branch 11 C (fb p1) := (Finset.mem_filter.1 (hfb_in_B p1 hp1S)).2
        unfold Branch at hb
        simp only [Big, Finset.mem_filter, hp1P4, true_and, not_le] at hnb
        omega
      have hfb2 : (readers 11 C (fb p2)).card = 2 := by
        have hnb : p2 ∉ Big := (Finset.mem_sdiff.1 hp2).2
        have hb : Branch 11 C (fb p2) := (Finset.mem_filter.1 (hfb_in_B p2 hp2S)).2
        unfold Branch at hb
        simp only [Big, Finset.mem_filter, hp2P4, true_and, not_le] at hnb
        omega
      have hc1 : 3 ≤ (chosenM p1).card := by
        rw [hchosenM_card p1 hp1S]
        have hfilt : (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj p1 u) =
            (Finset.univ.filter fun u : Fin 11 => core5.Adj p1 u) := by
          ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
          intro hadj; rw [hSP5]; exact core5_p5_indep p1 (hSP5 ▸ hp1S) u hadj
        rw [hfilt, core5_p4_deg3 p1 hp1P4]; omega
      have hc2 : 3 ≤ (chosenM p2).card := by
        rw [hchosenM_card p2 hp2S]
        have hfilt : (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj p2 u) =
            (Finset.univ.filter fun u : Fin 11 => core5.Adj p2 u) := by
          ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
          intro hadj; rw [hSP5]; exact core5_p5_indep p2 (hSP5 ▸ hp2S) u hadj
        rw [hfilt, core5_p4_deg3 p2 hp2P4]; omega
      have hint12 : (chosenM p1 ∩ chosenM p2).card ≤ 1 := by
        refine (hchosenM_inter p1 hp1S p2 hp2S).trans ?_
        have hni : ¬ ((∃ w ∈ S, core5.Adj p1 w) ∧ (∃ w ∈ S, core5.Adj p2 w)) := by
          rintro ⟨⟨w, hw, hadj⟩, _⟩
          exact core5_p5_indep p1 (hSP5 ▸ hp1S) w hadj (hSP5 ▸ hw)
        rw [ite_eq_right hni, add_zero]
        have hsub : (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj p1 u ∧ core5.Adj p2 u) ⊆
            (Finset.univ.filter fun u : Fin 11 => core5.Adj p1 u ∧ core5.Adj p2 u) := by
          intro u hu; rw [Finset.mem_filter] at hu ⊢; exact ⟨Finset.mem_univ _, hu.2.2⟩
        exact (Finset.card_le_card hsub).trans (by rw [core5_p4_inter1 p1 hp1P4 p2 hp2P4 hne12])
      exact hcase_e2_1 wstar hB2eq hw2 p1 hp1S p2 hp2S hfb1 hfb2 hc1 hc2 hint12
    · have hB1_eq6 : ∑ v ∈ S, ((readers 11 C (fb v)).card - 1) = 6 := by rw [← hB1_sum]; omega
      have hfb_all2 : ∀ v ∈ S, (readers 11 C (fb v)).card = 2 := by
        intro v hv
        have hb : Branch 11 C (fb v) := (Finset.mem_filter.1 (hfb_in_B v hv)).2
        unfold Branch at hb
        by_contra hne2
        have hge3 : 3 ≤ (readers 11 C (fb v)).card := by omega
        have hsum_ge7 : 7 ≤ ∑ u ∈ S, ((readers 11 C (fb u)).card - 1) := by
          rw [← Finset.add_sum_erase _ _ hv]
          have hrest : (S.erase v).card ≤ ∑ u ∈ S.erase v, ((readers 11 C (fb u)).card - 1) := by
            rw [show (S.erase v).card = ∑ _u ∈ S.erase v, 1 by simp]
            apply Finset.sum_le_sum; intro u hu
            have hbu : Branch 11 C (fb u) := (Finset.mem_filter.1 (hfb_in_B u (Finset.mem_erase.1 hu).2)).2
            unfold Branch at hbu; omega
          have her := Finset.card_erase_add_one hv
          omega
        omega
      obtain ⟨v1, hv1, v2, hv2, _, hr1, hr2, hinter⟩ := hS_vc6 rfl
      have hc1 : 3 ≤ (chosenM v1).card := by rw [hchosenM_card v1 hv1]; omega
      have hc2 : 3 ≤ (chosenM v2).card := by rw [hchosenM_card v2 hv2]; omega
      exact hcase_e2_1 wstar hB2eq hw2 v1 hv1 v2 hv2 (hfb_all2 v1 hv1) (hfb_all2 v2 hv2)
        hc1 hc2 ((hchosenM_inter v1 hv1 v2 hv2).trans hinter)
  · have hSc5 : S.card = 5 := by omega
    have hSP5 : S = P5 := hS_eq5 hSc5
    have hP4S : P4 ⊆ S := by rw [hSP5]; decide
    have hB1_eq5 : ∑ v ∈ S, ((readers 11 C (fb v)).card - 1) = 5 := by rw [← hB1_sum]; omega
    have hfb_all2 : ∀ v ∈ S, (readers 11 C (fb v)).card = 2 := by
      intro v hv
      have hb : Branch 11 C (fb v) := (Finset.mem_filter.1 (hfb_in_B v hv)).2
      unfold Branch at hb
      by_contra hne2
      have hge3 : 3 ≤ (readers 11 C (fb v)).card := by omega
      have hsum_ge6 : 6 ≤ ∑ u ∈ S, ((readers 11 C (fb u)).card - 1) := by
        rw [← Finset.add_sum_erase _ _ hv]
        have hrest : (S.erase v).card ≤ ∑ u ∈ S.erase v, ((readers 11 C (fb u)).card - 1) := by
          rw [show (S.erase v).card = ∑ _u ∈ S.erase v, 1 by simp]
          apply Finset.sum_le_sum; intro u hu
          have hbu : Branch 11 C (fb u) := (Finset.mem_filter.1 (hfb_in_B u (Finset.mem_erase.1 hu).2)).2
          unfold Branch at hbu; omega
        have her := Finset.card_erase_add_one hv
        omega
      omega
    let MI : Finset ℕ := P4.biUnion chosenM
    have hMI_not_Kv : ∀ m ∈ MI, ∀ z : Fin 11, m ∉ Kv C z := by
      intro m hm z
      obtain ⟨p, hp, hmp⟩ := Finset.mem_biUnion.1 hm
      have hpS := hP4S hp
      rcases Finset.mem_union.1 hmp with he1 | hi1
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 he1
        exact mg_ext_not_Kv p a.1 z (Finset.mem_filter.1 a.2).2.2 (Finset.mem_filter.1 a.2).2.1
      · unfold intM at hi1
        split_ifs at hi1 with hint
        · obtain ⟨w, hw, hadj⟩ := hint
          exact (core5_p5_indep p (hSP5 ▸ hpS) w hadj (hSP5 ▸ hw)).elim
        · simp at hi1
    have hMI_tag_ex : ∀ m ∈ MI, ∃ l ∈ L6, ∃ p ∈ P4, ∃ h : core5.Adj p l, m = mg p l h := by
      intro m hm
      obtain ⟨p, hp, hmp⟩ := Finset.mem_biUnion.1 hm
      have hpS := hP4S hp
      rcases Finset.mem_union.1 hmp with he1 | hi1
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 he1
        have ha := (Finset.mem_filter.1 a.2).2
        exact ⟨a.1, core5_p4_nbr_L6 p hp a.1 ha.2, p, hp, ha.2, rfl⟩
      · unfold intM at hi1
        split_ifs at hi1 with hint
        · obtain ⟨w, hw, hadj⟩ := hint
          exact (core5_p5_indep p (hSP5 ▸ hpS) w hadj (hSP5 ▸ hw)).elim
        · simp at hi1
    let tag (m : ℕ) : Fin 11 := if h : m ∈ MI then (hMI_tag_ex m h).choose else 0
    have htag_eq : ∀ (p : Fin 11) (hp : p ∈ P4) (l : Fin 11) (hpl : core5.Adj p l),
        mg p l hpl ∈ MI ∧ tag (mg p l hpl) = l := by
      intro p hp l hpl
      have hl_notS : l ∉ S := by rw [hSP5]; exact core5_p5_indep p (hSP5 ▸ hP4S hp) l hpl
      have hmem_ext : mg p l hpl ∈ extM p :=
        Finset.mem_image.2 ⟨⟨l, Finset.mem_filter.2 ⟨Finset.mem_univ _, hl_notS, hpl⟩⟩,
          Finset.mem_attach _ _, rfl⟩
      have hmem : mg p l hpl ∈ MI :=
        Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_union_left _ hmem_ext⟩
      refine ⟨hmem, ?_⟩
      unfold tag
      rw [dite_eq_left hmem]
      let l' := (hMI_tag_ex _ hmem).choose
      obtain ⟨_, p', hp', hpl', heq⟩ := (hMI_tag_ex _ hmem).choose_spec
      change l' = l
      by_contra hne
      exact mg_ext_tag p l p' l' hpl hpl' hl_notS (hP4S hp') (fun _ => Ne.symm hne) heq
    have hstop_K_MI : ∀ v : Fin 11, ∀ z ∈ Kv C v, z ∈ MI → Branch 11 C z :=
      fun v z hz hm => (hMI_not_Kv z hm v hz).elim
    let fuel := 11 + C.gates.length
    have hdouble_count : ∀ L : Finset (Fin 11), L ⊆ L6 →
        (∑ p ∈ P4, (L.filter fun l => core5.Adj p l).card) = 2 * L.card := by
      intro L hL
      calc (∑ p ∈ P4, (L.filter fun l => core5.Adj p l).card)
          = ∑ l ∈ L, (P4.filter fun p => core5.Adj p l).card := by
              simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
              exact Finset.sum_comm
        _ = ∑ _l ∈ L, 2 := Finset.sum_congr rfl fun l hl => core5_l6_deg2_p4 l (hL hl)
        _ = 2 * L.card := by simp [Nat.mul_comm]
    have hB2_card_pos : 0 < B2.card := by
      by_contra h0; have he0 : B2 = ∅ := Finset.card_eq_zero.1 (by omega)
      rw [he0, Finset.sum_empty] at hE2; omega
    have hB2_card_le2 : B2.card ≤ 2 := by omega
    have hL_from_ch : ∀ (Rs : Finset ℕ),
        let L := ((Rs.image (chase C MI fuel)).filter (· ∈ MI)).image tag
        L ⊆ L6 ∧ L.card ≤ Rs.card ∧
        ∀ (p : Fin 11), p ∈ P4 → ∀ (l : Fin 11) (hpl : core5.Adj p l),
          mg p l hpl ∈ Rs.image (chase C MI fuel) → l ∈ L := by
      intro Rs
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · intro l hl
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hl
        have hmMI := (Finset.mem_filter.1 hm).2
        unfold tag; rw [dite_eq_left hmMI]
        exact (hMI_tag_ex m hmMI).choose_spec.1
      · exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans Finset.card_image_le)
      · intro p hp l hpl hm
        obtain ⟨hmMI, hteq⟩ := htag_eq p hp l hpl
        exact Finset.mem_image.2 ⟨mg p l hpl, Finset.mem_filter.2 ⟨hm, hmMI⟩, hteq⟩
    have hp_needs_B2 : ∀ p ∈ P4,
        ∃ w ∈ (Kv C p).filter (Branch 11 C), w ∈ B2 := by
      intro p hp
      by_contra hnone
      push Not at hnone
      have hsub : (Kv C p).filter (Branch 11 C) ⊆ {fb p} := by
        intro x hx
        have := hKvB_sub p (hP4S hp) hx
        rcases Finset.mem_insert.1 this with rfl | hb2
        · exact Finset.mem_singleton_self _
        · exact (hnone x hx hb2).elim
      have hle := Finset.sum_le_sum_of_subset (f := fun w => (readers 11 C w).card - 1) hsub
      rw [Finset.sum_singleton, hfb_all2 p (hP4S hp)] at hle
      have hge := hKv_exc_ge p (hP4S hp)
      have hc3 : (chosenM p).card = 3 := by
        rw [hchosenM_card p (hP4S hp)]
        have hni : ¬ ∃ w ∈ S, core5.Adj p w := by
          rintro ⟨w, hw, hadj⟩; exact core5_p5_indep p (hSP5 ▸ hP4S hp) w hadj (hSP5 ▸ hw)
        have hfilt : (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj p u) =
            (Finset.univ.filter fun u : Fin 11 => core5.Adj p u) := by
          ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
          intro hadj; rw [hSP5]; exact core5_p5_indep p (hSP5 ▸ hP4S hp) u hadj
        rw [ite_eq_right hni, add_zero, hfilt, core5_p4_deg3 p hp]
      omega
    have hp_hits_2_of_B2 : ∀ p ∈ P4,
        let Rs := B2.biUnion (readers 11 C)
        let L := ((Rs.image (chase C MI fuel)).filter (· ∈ MI)).image tag
        2 ≤ (L.filter fun l => core5.Adj p l).card := by
      intro p hp
      dsimp only
      have hpS := hP4S hp
      have hel := (Finset.mem_filter.1 hpS).2
      obtain ⟨w0, hw0Kv, hw0B2⟩ := hp_needs_B2 p hp
      have hw0_ne : w0 ≠ firstBranch C p hel := by
        rw [← hfb_eq p hel]
        exact fun e => hfb_not_B2 p hpS (e ▸ hw0B2)
      obtain ⟨r0, hr0, t0, ht0, _, hch0, _⟩ := branch_reaches_via_chase hel hw0Kv hw0_ne (hstop_K_MI p)
      have hr0_mem : r0 ∈ readers 11 C (fb p) := by rwa [hfb_eq p hel]
      have hfb2 := hfb_all2 p hpS
      have hother_card : ((readers 11 C (fb p)).erase r0).card = 1 := by
        have := Finset.card_erase_add_one hr0_mem; omega
      let Fimgs := ((readers 11 C (fb p)).erase r0).image (chase C MI fuel)
      have hFimgs_le : Fimgs.card ≤ 1 := Finset.card_image_le.trans (by omega)
      let Rs := B2.biUnion (readers 11 C)
      let Wimgs := Rs.image (chase C MI fuel)
      let L := (Wimgs.filter (· ∈ MI)).image tag
      have hcov_p : chosenM p ⊆ Fimgs ∪ Wimgs := by
        intro m hm
        have hmMI : m ∈ MI := Finset.mem_biUnion.2 ⟨p, hp, hm⟩
        obtain ⟨_, a, ha, hln⟩ := hchosenM_exit p hpS m hm
        have hm_not : m ∉ Kv C p := hMI_not_Kv m hmMI p
        obtain ⟨b, hb, r, hr, hchr⟩ := backtrack_to_branch hC hel ha hm_not hln hmMI (hstop_K_MI p)
        rcases Finset.mem_insert.1 (hKvB_sub p hpS hb) with rfl | hb2
        · by_cases hrr0 : r = r0
          · subst hrr0
            rw [hch0] at hchr
            exact (hMI_not_Kv m hmMI p (hchr ▸ (Finset.mem_filter.1 (Finset.mem_erase.1 ht0).2).1)).elim
          · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨r, Finset.mem_erase.2 ⟨hrr0, hr⟩, hchr⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨r, Finset.mem_biUnion.2 ⟨b, hb2, hr⟩, hchr⟩)
      have hc3 : (chosenM p).card = 3 := by
        rw [hchosenM_card p hpS]
        have hni : ¬ ∃ w ∈ S, core5.Adj p w := by
          rintro ⟨w, hw, hadj⟩; exact core5_p5_indep p (hSP5 ▸ hpS) w hadj (hSP5 ▸ hw)
        have hfilt : (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj p u) =
            (Finset.univ.filter fun u : Fin 11 => core5.Adj p u) := by
          ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
          intro hadj; rw [hSP5]; exact core5_p5_indep p (hSP5 ▸ hpS) u hadj
        rw [ite_eq_right hni, add_zero, hfilt, core5_p4_deg3 p hp]
      have h2m : 2 ≤ (chosenM p ∩ Wimgs).card := by
        have h1 : (chosenM p).card ≤ (chosenM p ∩ Fimgs).card + (chosenM p ∩ Wimgs).card := by
          calc (chosenM p).card ≤ ((chosenM p ∩ Fimgs) ∪ (chosenM p ∩ Wimgs)).card := by
                apply Finset.card_le_card; intro m hm
                rcases Finset.mem_union.1 (hcov_p hm) with h | h
                · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hm, h⟩)
                · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hm, h⟩)
            _ ≤ (chosenM p ∩ Fimgs).card + (chosenM p ∩ Wimgs).card := Finset.card_union_le _ _
        have h2 : (chosenM p ∩ Fimgs).card ≤ 1 :=
          (Finset.card_le_card Finset.inter_subset_right).trans hFimgs_le
        omega
      have hinj : Set.InjOn tag ((chosenM p ∩ Wimgs : Finset ℕ) : Set ℕ) := by
        intro m1 hm1 m2 hm2 heq
        have h1 : m1 ∈ extM p := by
          rcases Finset.mem_union.1 (Finset.mem_inter.1 hm1).1 with h | h
          · exact h
          · unfold intM at h; split_ifs at h with hi
            · exact (core5_p5_indep p (hSP5 ▸ hpS) hi.choose hi.choose_spec.2 (hSP5 ▸ hi.choose_spec.1)).elim
            · simp at h
        have h2 : m2 ∈ extM p := by
          rcases Finset.mem_union.1 (Finset.mem_inter.1 hm2).1 with h | h
          · exact h
          · unfold intM at h; split_ifs at h with hi
            · exact (core5_p5_indep p (hSP5 ▸ hpS) hi.choose hi.choose_spec.2 (hSP5 ▸ hi.choose_spec.1)).elim
            · simp at h
        obtain ⟨a1, _, rfl⟩ := Finset.mem_image.1 h1
        obtain ⟨a2, _, rfl⟩ := Finset.mem_image.1 h2
        have ha1 := (Finset.mem_filter.1 a1.2).2
        have ha2 := (Finset.mem_filter.1 a2.2).2
        rw [(htag_eq p hp a1.1 ha1.2).2, (htag_eq p hp a2.1 ha2.2).2] at heq
        have : a1 = a2 := Subtype.ext heq
        subst this; rfl
      have hsub_L : (chosenM p ∩ Wimgs).image tag ⊆ L.filter fun l => core5.Adj p l := by
        intro l hl
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hl
        have hm1 : m ∈ extM p := by
          rcases Finset.mem_union.1 (Finset.mem_inter.1 hm).1 with h | h
          · exact h
          · unfold intM at h; split_ifs at h with hi
            · exact (core5_p5_indep p (hSP5 ▸ hpS) hi.choose hi.choose_spec.2 (hSP5 ▸ hi.choose_spec.1)).elim
            · simp at h
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hm1
        have ha := (Finset.mem_filter.1 a.2).2
        obtain ⟨hmMI, hteq⟩ := htag_eq p hp a.1 ha.2
        rw [hteq]
        exact Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨mg p a.1 ha.2,
          Finset.mem_filter.2 ⟨(Finset.mem_inter.1 hm).2, hmMI⟩, hteq⟩, ha.2⟩
      have hcard_img := Finset.card_image_of_injOn hinj
      exact (h2m.trans_eq hcard_img.symm).trans (Finset.card_le_card hsub_L)
    interval_cases hB2c : B2.card
    · obtain ⟨wstar, hB2eq⟩ := Finset.card_eq_one.1 hB2c
      have hw3 : (readers 11 C wstar).card = 3 := by
        rw [hB2eq, Finset.sum_singleton] at hE2
        have hb : Branch 11 C wstar := (Finset.mem_filter.1 (Finset.mem_sdiff.1 (hB2eq ▸ Finset.mem_singleton_self wstar)).1).2
        unfold Branch at hb; omega
      let Rs := B2.biUnion (readers 11 C)
      have hRs_card : Rs.card = 3 := by simp [Rs, hB2eq, hw3]
      let L := ((Rs.image (chase C MI fuel)).filter (· ∈ MI)).image tag
      obtain ⟨hLL6, hLle, _⟩ := hL_from_ch Rs
      change L.card ≤ Rs.card at hLle
      have hsum_ge8 : 8 ≤ ∑ p ∈ P4, (L.filter fun l => core5.Adj p l).card := by
        calc 8 = ∑ _p ∈ P4, 2 := by decide
          _ ≤ ∑ p ∈ P4, (L.filter fun l => core5.Adj p l).card :=
              Finset.sum_le_sum fun p hp => hp_hits_2_of_B2 p hp
      rw [hdouble_count L hLL6] at hsum_ge8
      omega
    · obtain ⟨w1, w2, hne12, hB2eq⟩ := Finset.card_eq_two.1 hB2c
      have hw_ord : ∃ u1 u2, u1 < u2 ∧ B2 = {u1, u2} := by
        rcases lt_or_gt_of_ne hne12 with h | h
        · exact ⟨w1, w2, h, hB2eq⟩
        · exact ⟨w2, w1, h, by rw [Finset.pair_comm]; exact hB2eq⟩
      obtain ⟨u1, u2, hlt12, hB2pair⟩ := hw_ord
      have hne_u : u1 ≠ u2 := ne_of_lt hlt12
      have hu1_b : Branch 11 C u1 := (Finset.mem_filter.1 (Finset.mem_sdiff.1 (hB2pair ▸ Finset.mem_insert_self u1 {u2})).1).2
      have hu2_b : Branch 11 C u2 := (Finset.mem_filter.1 (Finset.mem_sdiff.1 (hB2pair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self u2))).1).2
      unfold Branch at hu1_b hu2_b
      rw [hB2pair, Finset.sum_pair hne_u] at hE2
      have hu1_2 : (readers 11 C u1).card = 2 := by omega
      have hu2_2 : (readers 11 C u2).card = 2 := by omega
      by_cases hreach12 : ∃ r ∈ readers 11 C u1, chase C MI fuel r = u2
      · obtain ⟨r12, hr12, hch12⟩ := hreach12
        let Rs := B2.biUnion (readers 11 C)
        let Wimgs := (Rs.image (chase C MI fuel)).filter (· ∈ MI)
        let L := Wimgs.image tag
        have hWimgs_le3 : Wimgs.card ≤ 3 := by
          have hsub : Wimgs ⊆ ((readers 11 C u1).erase r12 ∪ readers 11 C u2).image (chase C MI fuel) := by
            intro m hm
            have hmMI := (Finset.mem_filter.1 hm).2
            obtain ⟨r, hr, hchr⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hm).1
            obtain ⟨b, hb, hrb⟩ := Finset.mem_biUnion.1 hr
            rw [hB2pair, Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with hbu1 | hbu2
            · subst b
              by_cases hreq : r = r12
              · subst hreq; rw [hch12] at hchr
                have hu2_in : u2 ∈ MI := hchr ▸ hmMI
                have hu2_live : u2 ∈ W := (Finset.mem_filter.1 (Finset.mem_sdiff.1 (hB2pair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self u2))).1).1
                exfalso
                obtain ⟨l, _, p, hp, hpl, heq⟩ := hMI_tag_ex u2 hu2_in
                have := hMI_not_Kv u2 hu2_in p
                obtain ⟨p', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := mg_spec p l hpl
                have : ∃ q ∈ P4, u2 ∈ Kv C q := by
                  by_contra hnone; push Not at hnone
                  have hu2_unused : ∀ p ∈ P4, u2 ∉ (Kv C p).filter (Branch 11 C) :=
                    fun p hp h => hnone p hp (Finset.mem_filter.1 h).1
                  have hbad : ∀ p ∈ P4, 2 ≤ (((readers 11 C u1).image (chase C MI fuel)).filter (· ∈ MI) |>.image tag |>.filter fun l => core5.Adj p l).card := by
                    intro p hp
                    have hpS := hP4S hp
                    have hel := (Finset.mem_filter.1 hpS).2
                    obtain ⟨w0, hw0Kv, hw0B2⟩ := hp_needs_B2 p hp
                    have hw0eq : w0 = u1 := by
                      rw [hB2pair, Finset.mem_insert, Finset.mem_singleton] at hw0B2
                      rcases hw0B2 with hwu1 | hwu2
                      · exact hwu1
                      · subst w0; exact (hu2_unused p hp hw0Kv).elim
                    subst w0
                    have hw0_ne : u1 ≠ firstBranch C p hel := by
                      rw [← hfb_eq p hel]
                      exact fun e => hfb_not_B2 p hpS (e ▸ hw0B2)
                    obtain ⟨r0, hr0, t0, ht0, _, hch0, _⟩ := branch_reaches_via_chase hel hw0Kv hw0_ne (hstop_K_MI p)
                    have ht0_eq : t0 = u1 := by
                      have h1 := hKvB_sub p hpS (Finset.mem_erase.1 ht0).2
                      simp only [hB2pair, Finset.mem_insert, Finset.mem_singleton] at h1
                      rcases h1 with h1 | h1 | h1
                      · exact ((Finset.mem_erase.1 ht0).1 (h1.trans (hfb_eq p hel))).elim
                      · exact h1
                      · exact (hu2_unused p hp (h1 ▸ (Finset.mem_erase.1 ht0).2)).elim
                    rw [ht0_eq] at hch0
                    have hr0_mem : r0 ∈ readers 11 C (fb p) := by rwa [hfb_eq p hel]
                    have hfb2 := hfb_all2 p hpS
                    have hother_card : ((readers 11 C (fb p)).erase r0).card = 1 := by
                      have := Finset.card_erase_add_one hr0_mem; omega
                    let Fimgs := ((readers 11 C (fb p)).erase r0).image (chase C MI fuel)
                    let U1imgs := (readers 11 C u1).image (chase C MI fuel)
                    have hcov : chosenM p ⊆ Fimgs ∪ U1imgs := by
                      intro m0 hm0
                      have hm0MI : m0 ∈ MI := Finset.mem_biUnion.2 ⟨p, hp, hm0⟩
                      obtain ⟨_, a0, ha0, hln0⟩ := hchosenM_exit p hpS m0 hm0
                      obtain ⟨b0, hb0, r0', hr0', hchr0⟩ := backtrack_to_branch hC hel ha0 (hMI_not_Kv m0 hm0MI p) hln0 hm0MI (hstop_K_MI p)
                      have hbm := hKvB_sub p hpS hb0
                      simp only [hB2pair, Finset.mem_insert, Finset.mem_singleton] at hbm
                      rcases hbm with hbm | hbm | hbm
                      · subst b0
                        by_cases heqr : r0' = r0
                        · subst heqr; rw [hch0] at hchr0
                          exact (hMI_not_Kv m0 hm0MI p (hchr0 ▸ (Finset.mem_filter.1 hw0Kv).1)).elim
                        · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨r0', Finset.mem_erase.2 ⟨heqr, hr0'⟩, hchr0⟩)
                      · subst b0; exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨r0', hr0', hchr0⟩)
                      · subst b0; exact (hu2_unused p hp hb0).elim
                    have hc3 : (chosenM p).card = 3 := by
                      rw [hchosenM_card p hpS]
                      have hni : ¬ ∃ w ∈ S, core5.Adj p w := by
                        rintro ⟨w, hw, hadj⟩; exact core5_p5_indep p (hSP5 ▸ hpS) w hadj (hSP5 ▸ hw)
                      have hfilt : (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj p u) =
                          (Finset.univ.filter fun u : Fin 11 => core5.Adj p u) := by
                        ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
                        intro hadj; rw [hSP5]; exact core5_p5_indep p (hSP5 ▸ hpS) u hadj
                      rw [ite_eq_right hni, add_zero, hfilt, core5_p4_deg3 p hp]
                    have h2m : 2 ≤ (chosenM p ∩ U1imgs).card := by
                      have h1 : (chosenM p).card ≤ (chosenM p ∩ Fimgs).card + (chosenM p ∩ U1imgs).card := by
                        calc (chosenM p).card ≤ ((chosenM p ∩ Fimgs) ∪ (chosenM p ∩ U1imgs)).card := by
                              apply Finset.card_le_card; intro m0 hm0
                              rcases Finset.mem_union.1 (hcov hm0) with h | h
                              · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hm0, h⟩)
                              · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hm0, h⟩)
                          _ ≤ (chosenM p ∩ Fimgs).card + (chosenM p ∩ U1imgs).card := Finset.card_union_le _ _
                      have h2 : (chosenM p ∩ Fimgs).card ≤ 1 :=
                        (Finset.card_le_card Finset.inter_subset_right).trans (Finset.card_image_le.trans (by omega))
                      omega
                    have hinj : Set.InjOn tag ((chosenM p ∩ U1imgs : Finset ℕ) : Set ℕ) := by
                      intro m1 hm1 m2 hm2 heqt
                      have h1 : m1 ∈ extM p := by
                        rcases Finset.mem_union.1 (Finset.mem_inter.1 hm1).1 with h | h
                        · exact h
                        · unfold intM at h; split_ifs at h with hi
                          · exact (core5_p5_indep p (hSP5 ▸ hpS) hi.choose hi.choose_spec.2 (hSP5 ▸ hi.choose_spec.1)).elim
                          · simp at h
                      have h2 : m2 ∈ extM p := by
                        rcases Finset.mem_union.1 (Finset.mem_inter.1 hm2).1 with h | h
                        · exact h
                        · unfold intM at h; split_ifs at h with hi
                          · exact (core5_p5_indep p (hSP5 ▸ hpS) hi.choose hi.choose_spec.2 (hSP5 ▸ hi.choose_spec.1)).elim
                          · simp at h
                      obtain ⟨a1, _, rfl⟩ := Finset.mem_image.1 h1
                      obtain ⟨a2, _, rfl⟩ := Finset.mem_image.1 h2
                      have ha1 := (Finset.mem_filter.1 a1.2).2
                      have ha2 := (Finset.mem_filter.1 a2.2).2
                      rw [(htag_eq p hp a1.1 ha1.2).2, (htag_eq p hp a2.1 ha2.2).2] at heqt
                      have : a1 = a2 := Subtype.ext heqt
                      subst this; rfl
                    have hsubL : (chosenM p ∩ U1imgs).image tag ⊆
                        ((U1imgs.filter (· ∈ MI)).image tag).filter fun l => core5.Adj p l := by
                      intro l0 hl0
                      obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.1 hl0
                      have hm1 : m0 ∈ extM p := by
                        rcases Finset.mem_union.1 (Finset.mem_inter.1 hm0).1 with h | h
                        · exact h
                        · unfold intM at h; split_ifs at h with hi
                          · exact (core5_p5_indep p (hSP5 ▸ hpS) hi.choose hi.choose_spec.2 (hSP5 ▸ hi.choose_spec.1)).elim
                          · simp at h
                      obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hm1
                      have ha := (Finset.mem_filter.1 a.2).2
                      obtain ⟨hmMI, hteq⟩ := htag_eq p hp a.1 ha.2
                      rw [hteq]
                      exact Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨mg p a.1 ha.2,
                        Finset.mem_filter.2 ⟨(Finset.mem_inter.1 hm0).2, hmMI⟩, hteq⟩, ha.2⟩
                    exact (h2m.trans_eq (Finset.card_image_of_injOn hinj).symm).trans (Finset.card_le_card hsubL)
                  obtain ⟨hL1sub, hL1le, _⟩ := hL_from_ch (readers 11 C u1)
                  let L1 := (((readers 11 C u1).image (chase C MI fuel)).filter (· ∈ MI)).image tag
                  change L1.card ≤ (readers 11 C u1).card at hL1le
                  have hsum8 : 8 ≤ ∑ p ∈ P4, (L1.filter fun l => core5.Adj p l).card := by
                    calc 8 = ∑ _p ∈ P4, 2 := by decide
                      _ ≤ ∑ p ∈ P4, (L1.filter fun l => core5.Adj p l).card :=
                          Finset.sum_le_sum fun p hp => hbad p hp
                  rw [hdouble_count L1 hL1sub] at hsum8
                  omega
                obtain ⟨q, _, hqu2⟩ := this
                exact hMI_not_Kv u2 hu2_in q hqu2
              · exact Finset.mem_image.2 ⟨r, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hreq, hrb⟩), hchr⟩
            · subst b; exact Finset.mem_image.2 ⟨r, Finset.mem_union_right _ hrb, hchr⟩
          refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
          have h1 := Finset.card_union_le ((readers 11 C u1).erase r12) (readers 11 C u2)
          have h2 := Finset.card_erase_add_one hr12
          omega
        have hL_le3 : L.card ≤ 3 := Finset.card_image_le.trans hWimgs_le3
        have hLL6 : L ⊆ L6 := (hL_from_ch Rs).1
        have hsum_ge8 : 8 ≤ ∑ p ∈ P4, (L.filter fun l => core5.Adj p l).card := by
          calc 8 = ∑ _p ∈ P4, 2 := by decide
            _ ≤ ∑ p ∈ P4, (L.filter fun l => core5.Adj p l).card :=
                Finset.sum_le_sum fun p hp => hp_hits_2_of_B2 p hp
        rw [hdouble_count L hLL6] at hsum_ge8
        omega
      · push Not at hreach12
        let L1 := (((readers 11 C u1).image (chase C MI fuel)).filter (· ∈ MI)).image tag
        let L2 := (((readers 11 C u2).image (chase C MI fuel)).filter (· ∈ MI)).image tag
        let L12 := L1 ∪ L2
        obtain ⟨hL1sub, hL1le, _⟩ := hL_from_ch (readers 11 C u1)
        obtain ⟨hL2sub, hL2le, _⟩ := hL_from_ch (readers 11 C u2)
        change L1.card ≤ (readers 11 C u1).card at hL1le
        change L2.card ≤ (readers 11 C u2).card at hL2le
        have hL12sub : L12 ⊆ L6 := Finset.union_subset hL1sub hL2sub
        have hL12le : L12.card ≤ 4 := (Finset.card_union_le L1 L2).trans (by omega)
        have hp_ext_only : ∀ p ∈ P4, ∀ m ∈ chosenM p, m ∈ extM p := by
          intro p hp m hm
          rcases Finset.mem_union.1 hm with h | h
          · exact h
          · unfold intM at h; split_ifs at h with hi
            · exact (core5_p5_indep p (hSP5 ▸ hP4S hp) hi.choose hi.choose_spec.2 (hSP5 ▸ hi.choose_spec.1)).elim
            · simp at h
        have hp_card3 : ∀ p ∈ P4, (chosenM p).card = 3 := by
          intro p hp
          rw [hchosenM_card p (hP4S hp)]
          have hni : ¬ ∃ w ∈ S, core5.Adj p w := by
            rintro ⟨w, hw, hadj⟩; exact core5_p5_indep p (hSP5 ▸ hP4S hp) w hadj (hSP5 ▸ hw)
          have hfilt : (Finset.univ.filter fun u : Fin 11 => u ∉ S ∧ core5.Adj p u) =
              (Finset.univ.filter fun u : Fin 11 => core5.Adj p u) := by
            ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
            intro hadj; rw [hSP5]; exact core5_p5_indep p (hSP5 ▸ hP4S hp) u hadj
          rw [ite_eq_right hni, add_zero, hfilt, core5_p4_deg3 p hp]
        have htags_inj : ∀ p ∈ P4, Set.InjOn tag (chosenM p : Set ℕ) := by
          intro p hp m1 hm1 m2 hm2 heqt
          obtain ⟨a1, _, rfl⟩ := Finset.mem_image.1 (hp_ext_only p hp m1 hm1)
          obtain ⟨a2, _, rfl⟩ := Finset.mem_image.1 (hp_ext_only p hp m2 hm2)
          have ha1 := (Finset.mem_filter.1 a1.2).2
          have ha2 := (Finset.mem_filter.1 a2.2).2
          rw [(htag_eq p hp a1.1 ha1.2).2, (htag_eq p hp a2.1 ha2.2).2] at heqt
          have : a1 = a2 := Subtype.ext heqt
          subst this; rfl
        have honly_one : ∀ (u : ℕ) (Lu : Finset (Fin 11)) (hu : u ∈ B2)
            (hLu : Lu = (((readers 11 C u).image (chase C MI fuel)).filter (· ∈ MI)).image tag),
            ∀ p ∈ P4, u ∈ Kv C p → (∀ u' ∈ B2, u' ≠ u → u' ∉ Kv C p) →
              2 ≤ (Lu.filter fun l => core5.Adj p l).card := by
          intro u Lu hu hLu p hp huKp hother
          have hpS := hP4S hp
          have hel := (Finset.mem_filter.1 hpS).2
          have huB : u ∈ (Kv C p).filter (Branch 11 C) :=
            Finset.mem_filter.2 ⟨huKp, (Finset.mem_filter.1 (Finset.mem_sdiff.1 hu).1).2⟩
          have hu_ne : u ≠ firstBranch C p hel := by
            rw [← hfb_eq p hel]; exact fun e => hfb_not_B2 p hpS (e ▸ hu)
          obtain ⟨r0, hr0, t0, ht0, _, hch0, _⟩ := branch_reaches_via_chase hel huB hu_ne (hstop_K_MI p)
          have ht0_eq : t0 = u := by
            have h1 := hKvB_sub p hpS (Finset.mem_erase.1 ht0).2
            rcases Finset.mem_insert.1 h1 with h1 | h1
            · exact ((Finset.mem_erase.1 ht0).1 (h1.trans (hfb_eq p hel))).elim
            · by_contra hne
              exact hother t0 h1 hne (Finset.mem_filter.1 (Finset.mem_erase.1 ht0).2).1
          rw [ht0_eq] at hch0
          have hr0_mem : r0 ∈ readers 11 C (fb p) := by rwa [hfb_eq p hel]
          have hfb2 := hfb_all2 p hpS
          have hother_card : ((readers 11 C (fb p)).erase r0).card = 1 := by
            have := Finset.card_erase_add_one hr0_mem; omega
          let Fimgs := ((readers 11 C (fb p)).erase r0).image (chase C MI fuel)
          let Uimgs := (readers 11 C u).image (chase C MI fuel)
          have hcov : chosenM p ⊆ Fimgs ∪ Uimgs := by
            intro m hm
            have hmMI : m ∈ MI := Finset.mem_biUnion.2 ⟨p, hp, hm⟩
            obtain ⟨_, a, ha, hln⟩ := hchosenM_exit p hpS m hm
            obtain ⟨b, hb, r, hr, hchr⟩ := backtrack_to_branch hC hel ha (hMI_not_Kv m hmMI p) hln hmMI (hstop_K_MI p)
            rcases Finset.mem_insert.1 (hKvB_sub p hpS hb) with hbf | hb2
            · subst b
              by_cases hrr0 : r = r0
              · subst hrr0; rw [hch0] at hchr
                exact (hMI_not_Kv m hmMI p (hchr ▸ huKp)).elim
              · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨r, Finset.mem_erase.2 ⟨hrr0, hr⟩, hchr⟩)
            · by_cases hbu : b = u
              · subst b; exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨r, hr, hchr⟩)
              · exact (hother b hb2 hbu (Finset.mem_filter.1 hb).1).elim
          have h2m : 2 ≤ (chosenM p ∩ Uimgs).card := by
            have hc3 := hp_card3 p hp
            have h1 : (chosenM p).card ≤ (chosenM p ∩ Fimgs).card + (chosenM p ∩ Uimgs).card := by
              calc (chosenM p).card ≤ ((chosenM p ∩ Fimgs) ∪ (chosenM p ∩ Uimgs)).card := by
                    apply Finset.card_le_card; intro m hm
                    rcases Finset.mem_union.1 (hcov hm) with h | h
                    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hm, h⟩)
                    · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hm, h⟩)
                _ ≤ (chosenM p ∩ Fimgs).card + (chosenM p ∩ Uimgs).card := Finset.card_union_le _ _
            have h2 : (chosenM p ∩ Fimgs).card ≤ 1 :=
              (Finset.card_le_card Finset.inter_subset_right).trans (Finset.card_image_le.trans (by omega))
            omega
          have hinj : Set.InjOn tag ((chosenM p ∩ Uimgs : Finset ℕ) : Set ℕ) :=
            (htags_inj p hp).mono (Finset.coe_subset.2 Finset.inter_subset_left)
          have hsubL : (chosenM p ∩ Uimgs).image tag ⊆ Lu.filter fun l => core5.Adj p l := by
            intro l hl
            obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hl
            obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 (hp_ext_only p hp m (Finset.mem_inter.1 hm).1)
            have ha := (Finset.mem_filter.1 a.2).2
            obtain ⟨hmMI, hteq⟩ := htag_eq p hp a.1 ha.2
            rw [hteq, hLu]
            exact Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨mg p a.1 ha.2,
              Finset.mem_filter.2 ⟨(Finset.mem_inter.1 hm).2, hmMI⟩, hteq⟩, ha.2⟩
          exact (h2m.trans_eq (Finset.card_image_of_injOn hinj).symm).trans (Finset.card_le_card hsubL)
        have hboth_3 : ∀ p ∈ P4, u1 ∈ Kv C p → u2 ∈ Kv C p →
            3 ≤ (L12.filter fun l => core5.Adj p l).card := by
          intro p hp hu1p hu2p
          have hpS := hP4S hp
          have hel := (Finset.mem_filter.1 hpS).2
          have hu1B : u1 ∈ (Kv C p).filter (Branch 11 C) :=
            Finset.mem_filter.2 ⟨hu1p, by unfold Branch; omega⟩
          have hu2B : u2 ∈ (Kv C p).filter (Branch 11 C) :=
            Finset.mem_filter.2 ⟨hu2p, by unfold Branch; omega⟩
          have hu1_ne : u1 ≠ firstBranch C p hel := by
            rw [← hfb_eq p hel]; exact fun e => hfb_not_B2 p hpS (by rw [hB2pair, e]; simp)
          have hu2_ne : u2 ≠ firstBranch C p hel := by
            rw [← hfb_eq p hel]; exact fun e => hfb_not_B2 p hpS (by rw [hB2pair, e]; simp)
          obtain ⟨r1, hr1, t1, ht1, ht1le, hch1, _⟩ := branch_reaches_via_chase hel hu1B hu1_ne (hstop_K_MI p)
          have ht1_eq : t1 = u1 := by
            have h1 := hKvB_sub p hpS (Finset.mem_erase.1 ht1).2
            simp only [hB2pair, Finset.mem_insert, Finset.mem_singleton] at h1
            rcases h1 with h1 | h1 | h1
            · exact ((Finset.mem_erase.1 ht1).1 (h1.trans (hfb_eq p hel))).elim
            · exact h1
            · omega
          rw [ht1_eq] at hch1
          obtain ⟨r2, hr2, t2, ht2, ht2le, hch2, htr2⟩ := branch_reaches_via_chase hel hu2B hu2_ne (hstop_K_MI p)
          have ht2_eq : t2 = u2 := by
            have h1 := hKvB_sub p hpS (Finset.mem_erase.1 ht2).2
            simp only [hB2pair, Finset.mem_insert, Finset.mem_singleton] at h1
            rcases h1 with h1 | h1 | h1
            · exact ((Finset.mem_erase.1 ht2).1 (h1.trans (hfb_eq p hel))).elim
            · rw [h1] at htr2
              rcases htr2.cases_head with heq | ⟨q, hstep, hrest⟩
              · omega
              · obtain ⟨t', ht', hqt', ht'le, htr1', _⟩ := first_branch_split hrest hu2B
                have ht'_eq : t' = u2 := by
                  have h2 := hKvB_sub p hpS ht'
                  simp only [hB2pair, Finset.mem_insert, Finset.mem_singleton] at h2
                  rcases h2 with h2 | h2 | h2
                  · have hle := firstBranch_le p hel ⟨(mem_Kv.1 hu1p).2.1, (mem_Kv.1 hu1p).2.2, by unfold Branch; omega⟩
                    rw [← hfb_eq p hel] at hle
                    have := hstep.2.1.1; omega
                  · have := hstep.2.1.1; omega
                  · exact h2
                subst t'
                have hchq : chase C MI fuel q = u2 := by
                  have hu2lt : u2 < fuel := (mem_Kv.1 hu2p).1
                  refine chase_of_trace htr1' ?_ (Or.inr (by unfold Branch; omega)) fuel (by omega)
                  intro z _ _ hPz
                  exact ⟨fun hs => hPz.2 (hstop_K_MI p z hPz.1 hs), hPz.2⟩
                exact (hreach12 q (mem_readers.2 hstep.2) hchq).elim
            · exact h1
          rw [ht2_eq] at hch2
          have hr1_mem : r1 ∈ readers 11 C (fb p) := by rwa [hfb_eq p hel]
          have hr2_mem : r2 ∈ readers 11 C (fb p) := by rwa [hfb_eq p hel]
          have hr12_ne : r1 ≠ r2 := fun e => hne_u (by rw [← hch1, e, hch2])
          have hfb_pair : readers 11 C (fb p) = {r1, r2} := by
            refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption
            · rw [Finset.card_pair hr12_ne, hfb_all2 p hpS]
          let Uimgs := (readers 11 C u1 ∪ readers 11 C u2).image (chase C MI fuel)
          have hcov : chosenM p ⊆ Uimgs := by
            intro m hm
            have hmMI : m ∈ MI := Finset.mem_biUnion.2 ⟨p, hp, hm⟩
            obtain ⟨_, a, ha, hln⟩ := hchosenM_exit p hpS m hm
            obtain ⟨b, hb, r, hr, hchr⟩ := backtrack_to_branch hC hel ha (hMI_not_Kv m hmMI p) hln hmMI (hstop_K_MI p)
            have hbm := hKvB_sub p hpS hb
            simp only [hB2pair, Finset.mem_insert, Finset.mem_singleton] at hbm
            rcases hbm with hbm | hbm | hbm
            · subst b
              rw [hfb_pair, Finset.mem_insert, Finset.mem_singleton] at hr
              rcases hr with rfl | rfl
              · rw [hch1] at hchr; exact (hMI_not_Kv m hmMI p (hchr ▸ hu1p)).elim
              · rw [hch2] at hchr; exact (hMI_not_Kv m hmMI p (hchr ▸ hu2p)).elim
            · subst b; exact Finset.mem_image.2 ⟨r, Finset.mem_union_left _ hr, hchr⟩
            · subst b; exact Finset.mem_image.2 ⟨r, Finset.mem_union_right _ hr, hchr⟩
          have hsubL : (chosenM p).image tag ⊆ L12.filter fun l => core5.Adj p l := by
            intro l hl
            obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hl
            obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 (hp_ext_only p hp m hm)
            have ha := (Finset.mem_filter.1 a.2).2
            obtain ⟨hmMI, hteq⟩ := htag_eq p hp a.1 ha.2
            rw [hteq]
            refine Finset.mem_filter.2 ⟨?_, ha.2⟩
            obtain ⟨r, hr, hchr⟩ := Finset.mem_image.1 (hcov hm)
            rcases Finset.mem_union.1 hr with hr1' | hr2'
            · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨mg p a.1 ha.2,
                Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨r, hr1', hchr⟩, hmMI⟩, hteq⟩)
            · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨mg p a.1 ha.2,
                Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨r, hr2', hchr⟩, hmMI⟩, hteq⟩)
          have hc3 := hp_card3 p hp
          have hci := Finset.card_image_of_injOn (htags_inj p hp)
          have hle := Finset.card_le_card hsubL
          omega
        let C1 := P4.filter fun p => u1 ∈ Kv C p ∧ u2 ∉ Kv C p
        let C2 := P4.filter fun p => u2 ∈ Kv C p ∧ u1 ∉ Kv C p
        let C12 := P4.filter fun p => u1 ∈ Kv C p ∧ u2 ∈ Kv C p
        have hC1_le1 : C1.card ≤ 1 := by
          apply Finset.card_le_one.2
          intro p1 hp1 p2 hp2
          by_contra hne
          have h1 := honly_one u1 L1 (hB2pair ▸ Finset.mem_insert_self u1 {u2}) rfl p1
            (Finset.mem_filter.1 hp1).1 (Finset.mem_filter.1 hp1).2.1 (fun u' hu' hneu => by
              rw [hB2pair, Finset.mem_insert, Finset.mem_singleton] at hu'
              rcases hu' with rfl | rfl
              · exact (hneu rfl).elim
              · exact (Finset.mem_filter.1 hp1).2.2)
          have h2 := honly_one u1 L1 (hB2pair ▸ Finset.mem_insert_self u1 {u2}) rfl p2
            (Finset.mem_filter.1 hp2).1 (Finset.mem_filter.1 hp2).2.1 (fun u' hu' hneu => by
              rw [hB2pair, Finset.mem_insert, Finset.mem_singleton] at hu'
              rcases hu' with rfl | rfl
              · exact (hneu rfl).elim
              · exact (Finset.mem_filter.1 hp2).2.2)
          have he1 : L1.filter (fun l => core5.Adj p1 l) = L1 :=
            Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
          have he2 : L1.filter (fun l => core5.Adj p2 l) = L1 :=
            Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
          have hsub : L1 ⊆ Finset.univ.filter fun l : Fin 11 => core5.Adj p1 l ∧ core5.Adj p2 l := by
            intro l hl
            have hl1 : l ∈ L1.filter (fun l => core5.Adj p1 l) := he1.symm ▸ hl
            have hl2 : l ∈ L1.filter (fun l => core5.Adj p2 l) := he2.symm ▸ hl
            exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hl1).2, (Finset.mem_filter.1 hl2).2⟩
          have hci := Finset.card_le_card hsub
          rw [core5_p4_inter1 p1 (Finset.mem_filter.1 hp1).1 p2 (Finset.mem_filter.1 hp2).1 hne] at hci
          rw [he1] at h1
          omega
        have hC2_le1 : C2.card ≤ 1 := by
          apply Finset.card_le_one.2
          intro p1 hp1 p2 hp2
          by_contra hne
          have h1 := honly_one u2 L2 (hB2pair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self u2)) rfl p1
            (Finset.mem_filter.1 hp1).1 (Finset.mem_filter.1 hp1).2.1 (fun u' hu' hneu => by
              rw [hB2pair, Finset.mem_insert, Finset.mem_singleton] at hu'
              rcases hu' with rfl | rfl
              · exact (Finset.mem_filter.1 hp1).2.2
              · exact (hneu rfl).elim)
          have h2 := honly_one u2 L2 (hB2pair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self u2)) rfl p2
            (Finset.mem_filter.1 hp2).1 (Finset.mem_filter.1 hp2).2.1 (fun u' hu' hneu => by
              rw [hB2pair, Finset.mem_insert, Finset.mem_singleton] at hu'
              rcases hu' with rfl | rfl
              · exact (Finset.mem_filter.1 hp2).2.2
              · exact (hneu rfl).elim)
          have he1 : L2.filter (fun l => core5.Adj p1 l) = L2 :=
            Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
          have he2 : L2.filter (fun l => core5.Adj p2 l) = L2 :=
            Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
          have hsub : L2 ⊆ Finset.univ.filter fun l : Fin 11 => core5.Adj p1 l ∧ core5.Adj p2 l := by
            intro l hl
            have hl1 : l ∈ L2.filter (fun l => core5.Adj p1 l) := he1.symm ▸ hl
            have hl2 : l ∈ L2.filter (fun l => core5.Adj p2 l) := he2.symm ▸ hl
            exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hl1).2, (Finset.mem_filter.1 hl2).2⟩
          have hci := Finset.card_le_card hsub
          rw [core5_p4_inter1 p1 (Finset.mem_filter.1 hp1).1 p2 (Finset.mem_filter.1 hp2).1 hne] at hci
          rw [he1] at h1
          omega
        have hP4_part : P4 ⊆ C1 ∪ C2 ∪ C12 := by
          intro p hp
          obtain ⟨w, hwKv, hwB2⟩ := hp_needs_B2 p hp
          have hwK := (Finset.mem_filter.1 hwKv).1
          rw [hB2pair, Finset.mem_insert, Finset.mem_singleton] at hwB2
          by_cases h1 : u1 ∈ Kv C p
          · by_cases h2 : u2 ∈ Kv C p
            · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hp, h1, h2⟩)
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hp, h1, h2⟩))
          · by_cases h2 : u2 ∈ Kv C p
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hp, h2, h1⟩))
            · rcases hwB2 with rfl | rfl
              · exact (h1 hwK).elim
              · exact (h2 hwK).elim
        have hC12_ge2 : 2 ≤ C12.card := by
          have hP4c : P4.card = 4 := by decide
          have h1 := Finset.card_le_card hP4_part
          have h2 := Finset.card_union_le (C1 ∪ C2) C12
          have h3 := Finset.card_union_le C1 C2
          omega
        have hsum_ge10 : 10 ≤ ∑ p ∈ P4, (L12.filter fun l => core5.Adj p l).card := by
          have hge_each : ∀ p ∈ P4, (if p ∈ C12 then 3 else 2) ≤ (L12.filter fun l => core5.Adj p l).card := by
            intro p hp
            by_cases h12 : p ∈ C12
            · rw [ite_eq_left h12]
              exact hboth_3 p hp (Finset.mem_filter.1 h12).2.1 (Finset.mem_filter.1 h12).2.2
            · rw [ite_eq_right h12]
              have h12e : L12 = ((((B2.biUnion (readers 11 C)).image (chase C MI fuel)).filter (· ∈ MI)).image tag) := by
                ext l
                simp only [L12, L1, L2, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
                  Finset.mem_biUnion, hB2pair, Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro (⟨m, ⟨⟨r, hr, hch⟩, hm⟩, rfl⟩ | ⟨m, ⟨⟨r, hr, hch⟩, hm⟩, rfl⟩)
                  · exact ⟨m, ⟨⟨r, ⟨u1, Or.inl rfl, hr⟩, hch⟩, hm⟩, rfl⟩
                  · exact ⟨m, ⟨⟨r, ⟨u2, Or.inr rfl, hr⟩, hch⟩, hm⟩, rfl⟩
                · rintro ⟨m, ⟨⟨r, ⟨b, rfl | rfl, hr⟩, hch⟩, hm⟩, rfl⟩
                  · exact Or.inl ⟨m, ⟨⟨r, hr, hch⟩, hm⟩, rfl⟩
                  · exact Or.inr ⟨m, ⟨⟨r, hr, hch⟩, hm⟩, rfl⟩
              rw [h12e]
              exact hp_hits_2_of_B2 p hp
          have hsum_ite : (∑ p ∈ P4, if p ∈ C12 then 3 else 2) = 8 + C12.card := by
            have h1 : ∀ p ∈ P4, (if p ∈ C12 then 3 else 2) = 2 + (if p ∈ C12 then 1 else 0) := by
              intro p _; split_ifs <;> omega
            rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
            have h2 : (∑ _p ∈ P4, 2) = 8 := by decide
            have h3 : (∑ p ∈ P4, if p ∈ C12 then 1 else 0) = C12.card := by
              rw [← Finset.sum_filter]
              have : P4.filter (· ∈ C12) = C12 := by
                ext x; simp only [Finset.mem_filter, and_iff_right_iff_imp]; intro hx; exact (Finset.mem_filter.1 hx).1
              rw [this]; simp
            rw [h2, h3]
          calc 10 ≤ 8 + C12.card := by omega
            _ = ∑ p ∈ P4, if p ∈ C12 then 3 else 2 := hsum_ite.symm
            _ ≤ ∑ p ∈ P4, (L12.filter fun l => core5.Adj p l).card := Finset.sum_le_sum hge_each
        rw [hdouble_count L12 hL12sub] at hsum_ge10
        omega


def embList : List ℕ := [13, 16, 14, 15, 17, 3, 4, 2, 5, 0, 6, 10, 11, 7, 9, 12, 1]

def idxList : List ℕ := [9, 16, 7, 5, 6, 8, 10, 13, 17, 14, 11, 12, 15, 0, 2, 3, 1, 4,
  17, 17, 17, 17, 17, 17, 17, 17]

def emb17 (i : Fin 17) : Fin 26 :=
  Fin.ofNat 26 (embList.getD i.val 0)

def idx26 (i : ℕ) : ℕ := idxList.getD i 17

def ren (m i : ℕ) : ℕ :=
  if i < 26 then (if idx26 i < 17 then idx26 i else 17 + m) else i - 9

def shrink (C : Circuit) : Circuit :=
  ⟨C.gates.map fun g => ⟨g.op, g.inputs.map (ren C.gates.length)⟩, ren C.gates.length C.output⟩

def pull (x : Fin 17 → Bool) (i : Fin 26) : Bool :=
  (List.ofFn x).getD (idx26 i.val) false

def edges17 : List (ℕ × ℕ) :=
  [(0, 5), (0, 16), (0, 14), (0, 9), (1, 6), (1, 5), (1, 15), (1, 10), (2, 7), (2, 6),
   (2, 16), (2, 11), (3, 8), (3, 7), (3, 5), (3, 12), (4, 9), (4, 8), (4, 6), (4, 13)]

def adj17 (u v : Fin 17) : Bool :=
  edges17.any fun e => (e.1 == u.val && e.2 == v.val) || (e.1 == v.val && e.2 == u.val)

def ptsOf (u v : Fin 17) : Finset (Fin 13) :=
  Finset.univ.filter fun p => emb17 u = Fin.castAdd 13 p ∨ emb17 v = Fin.castAdd 13 p

def linesOf (u v : Fin 17) : Finset (Fin 13) :=
  Finset.univ.filter fun l => emb17 u = Fin.natAdd 13 l ∨ emb17 v = Fin.natAdd 13 l

def phi (i : Fin 11) : Fin 17 :=
  Fin.ofNat 17 (if i.val < 10 then i.val else 16)

lemma idx26_bound (i : Fin 26) : idx26 i.val ≤ 17 := by decide +kernel +revert

lemma ren_eq_idx (m j : ℕ) (hj : j < 26) (h : idx26 j < 17) : ren m j = idx26 j := by
  simp [ren, hj, h]

lemma ren_eq_sentinel (m j : ℕ) (hj : j < 26) (h : ¬ idx26 j < 17) : ren m j = 17 + m := by
  have h17 : idx26 j = 17 := by
    have hb := idx26_bound (⟨j, hj⟩ : Fin 26)
    change idx26 j ≤ 17 at hb
    omega
  simp [ren, hj, h17]

lemma ren_eq_shift (m j : ℕ) (hj : 26 ≤ j) : ren m j = j - 9 := by
  simp [ren, Nat.not_lt.2 hj]

lemma adj17_loop (k : Fin 17) : adj17 k k = false := by decide +kernel +revert

lemma pos_mask (P L : Fin 13) (hL : L.val < 5)
    (hPL : P - L ∈ ({0, 1, 3, 9} : Finset (Fin 13))) :
    pull (fun k => decide (emb17 k = Fin.castAdd 13 P ∨ emb17 k = Fin.natAdd 13 L)) =
      fun i => decide (i = Fin.castAdd 13 P ∨ i = Fin.natAdd 13 L) := by
  decide +kernel +revert

lemma neg_ok : ∀ u v : Fin 17, adj17 u v = false →
    (∀ p ∈ ptsOf u v, ∀ l ∈ linesOf u v, p - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))) ∧
    (∀ l : Fin 13, {p ∈ ptsOf u v | p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))}.card ≤ 2) ∧
    (∀ p : Fin 13, {l ∈ linesOf u v | p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))}.card ≤ 2) ∧
    pull (fun k => decide (k = u ∨ k = v)) =
      fun i => decide ((∃ p ∈ ptsOf u v, i = Fin.castAdd 13 p) ∨
                       (∃ l ∈ linesOf u v, i = Fin.natAdd 13 l)) := by
  decide +kernel +revert

lemma pos_ex (u v : Fin 17) (huv : adj17 u v = true) :
    ∃ P L : Fin 13, L.val < 5 ∧ P - L ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      ∀ k : Fin 17,
        decide (emb17 k = Fin.castAdd 13 P ∨ emb17 k = Fin.natAdd 13 L) = true → k = u ∨ k = v := by
  decide +kernel +revert

lemma ext17_pair (u v : Fin 11) :
    ext17 (fun k => decide (k = u ∨ k = v)) =
      fun i : Fin 17 => decide (i = phi u ∨ i = phi v) := by
  decide +kernel +revert

lemma core5_edge_adj17 : ∀ u v : Fin 11, core5AdjB u v = true → adj17 (phi u) (phi v) = true := by
  decide +kernel +revert

lemma core5_nonedge_adj17 : ∀ u v : Fin 11, core5AdjB u v = false → adj17 (phi u) (phi v) = false := by
  decide +kernel +revert

lemma gate_step (m p : ℕ) (g : Gate) (v w : List Bool)
    (hv : v.length = 17 + p) (hw : w.length = 26 + p)
    (hinv : ∀ j, j < 26 + p → w.getD j false = v.getD (ren m j) false) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => v.getD (ren m i) false) := by
  have hmap : (g.inputs.map fun i => w.getD i false) =
      (g.inputs.map fun i => v.getD (ren m i) false) := by
    apply List.map_congr_left
    intro i _
    by_cases h1 : i < 26 + p
    · exact hinv i h1
    · by_cases h2 : i = 26 + p
      · subst h2
        have hren : ren m (26 + p) = 17 + p := by
          have h : ¬ 26 + p < 26 := by omega
          simp [ren, h]
          omega
        rw [hren]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · have hgt : 26 + p < i := by omega
        have hge : 26 ≤ i := by omega
        rw [ren_eq_shift m i hge]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  rw [hmap]

lemma wiresFrom_sim (m : ℕ) (gs : List Gate) (v w : List Bool) (p : ℕ)
    (hpm : p + gs.length ≤ m) (hv : v.length = 17 + p) (hw : w.length = 26 + p)
    (hinv : ∀ j, j < 26 + p → w.getD j false = v.getD (ren m j) false) :
    (wiresFrom (gs.map fun g => ⟨g.op, g.inputs.map (ren m)⟩) v).length = 17 + p + gs.length ∧
    (wiresFrom gs w).length = 26 + p + gs.length ∧
    ∀ j, j < 26 + p + gs.length →
      (wiresFrom gs w).getD j false =
        (wiresFrom (gs.map fun g => ⟨g.op, g.inputs.map (ren m)⟩) v).getD (ren m j) false := by
  induction gs generalizing v w p with
  | nil =>
    refine ⟨by simpa [wiresFrom] using hv, by simpa [wiresFrom] using hw, ?_⟩
    intro j hj
    simpa [wiresFrom] using hinv j (by simpa using hj)
  | cons g gs ih =>
    simp only [List.length_cons] at hpm
    let a := g.op.eval (g.inputs.map fun i => v.getD (ren m i) false)
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    have hstep : b = a := gate_step m p g v w hv hw hinv
    have hpm' : (p + 1) + gs.length ≤ m := by omega
    have hv' : (v ++ [a]).length = 17 + (p + 1) := by simp [hv]; omega
    have hw' : (w ++ [b]).length = 26 + (p + 1) := by simp [hw]; omega
    have hinv' : ∀ j, j < 26 + (p + 1) →
        (w ++ [b]).getD j false = (v ++ [a]).getD (ren m j) false := by
      intro j hj
      by_cases hlt : j < 26 + p
      · by_cases hrend : ren m j < 17 + p
        · have hltw : j < w.length := by omega
          have hrendv : ren m j < v.length := by omega
          rw [List.getD_append w [b] false j hltw,
              List.getD_append v [a] false (ren m j) hrendv]
          exact hinv j hlt
        · have hj26 : j < 26 := by
            by_contra h
            have hge : 26 ≤ j := by omega
            rw [ren_eq_shift m j hge] at hrend
            omega
          have hbig : 17 + p < ren m j := by
            by_cases hidx : idx26 j < 17
            · rw [ren_eq_idx m j hj26 hidx] at hrend
              omega
            · rw [ren_eq_sentinel m j hj26 hidx]
              omega
          have hltw : j < w.length := by omega
          rw [List.getD_append w [b] false j hltw,
              hinv j hlt,
              List.getD_eq_default (v ++ [a]) false (by simp; omega),
              List.getD_eq_default v false (by omega)]
      · have hj' : j = 26 + p := by omega
        subst hj'
        have hren : ren m (26 + p) = 17 + p := by
          have h : ¬ 26 + p < 26 := by omega
          simp [ren, h]
          omega
        rw [hren,
            List.getD_append_right w [b] false (26 + p) (by omega),
            List.getD_append_right v [a] false (17 + p) (by omega)]
        simp only [hw, hv, Nat.sub_self, List.getD_cons_zero]
        exact hstep
    have hV : wiresFrom ((g :: gs).map fun g => ⟨g.op, g.inputs.map (ren m)⟩) v =
        wiresFrom (gs.map fun g => ⟨g.op, g.inputs.map (ren m)⟩) (v ++ [a]) := by
      simp [wiresFrom, a, Function.comp_def]
    have hW : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [b]) := by
      simp [wiresFrom, b]
    rw [hV, hW]
    obtain ⟨i1, i2, i3⟩ := ih (v ++ [a]) (w ++ [b]) (p + 1) hpm' hv' hw' hinv'
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
    · intro j hj
      simp only [List.length_cons] at hj
      exact i3 j (by omega)

lemma shrink_mono (C : Circuit) (hM : Monotone2 C) : Monotone2 (shrink C) := by
  intro g hg
  simp only [shrink, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  simpa using hM g' hg'

lemma sim (C : Circuit) (x : Fin 17 → Bool) :
    circuitFun 17 (shrink C) x = circuitFun 26 C (pull x) := by
  unfold circuitFun
  change (wiresFrom (shrink C).gates (List.ofFn x)).getD (shrink C).output false =
    (wiresFrom C.gates (List.ofFn (pull x))).getD C.output false
  simp only [shrink]
  have hinv0 : ∀ j, j < 26 + 0 →
      (List.ofFn (pull x)).getD j false = (List.ofFn x).getD (ren C.gates.length j) false := by
    intro j hj
    rw [Nat.add_zero] at hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
    simp only [pull]
    by_cases hidx : idx26 j < 17
    · rw [ren_eq_idx _ j hj hidx]
    · have h17 : idx26 j = 17 := by
        have h := idx26_bound (⟨j, hj⟩ : Fin 26)
        change idx26 j ≤ 17 at h
        omega
      rw [ren_eq_sentinel _ j hj hidx, h17]
      rw [List.getD_eq_default _ _ (by simp)]
      rw [List.getD_eq_default _ _ (by simp)]
  obtain ⟨hVlen, hWlen, hinv⟩ := wiresFrom_sim C.gates.length C.gates
    (List.ofFn x) (List.ofFn (pull x)) 0 (by omega) (by simp) (by simp) hinv0
  by_cases hout : C.output < 26 + C.gates.length
  · exact (hinv C.output hout).symm
  · have hren : 17 + C.gates.length ≤ ren C.gates.length C.output := by
      have h26 : 26 ≤ C.output := by omega
      rw [ren_eq_shift C.gates.length C.output h26]
      omega
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma main_proof (C : Circuit) (hM : Monotone2 C) (hsz : C.size ≤ 23)
    (hpos : ∀ (P L : Fin 13), L.val < 5 →
      P - L ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      circuitFun 17 C (fun k : Fin 17 => decide (emb17 k = Fin.castAdd 13 P ∨ emb17 k = Fin.natAdd 13 L)) = true)
    (hneg : ∀ u v : Fin 17, adj17 u v = false →
      circuitFun 17 C (fun k : Fin 17 => decide (k = u ∨ k = v)) = false) : False := by
  have hmono_eval : ∀ (D : Circuit), Monotone2 D → ∀ (x y : Fin 17 → Bool),
      (∀ k, x k = true → y k = true) → D.eval (List.ofFn x) = true → D.eval (List.ofFn y) = true :=
    fun D hD x y hxy hx => acts_mono hD hxy D.output hx
  have hpos_pair : ∀ (u v : Fin 17), adj17 u v = true →
      circuitFun 17 C (fun k : Fin 17 => decide (k = u ∨ k = v)) = true := by
    intro u v huv
    obtain ⟨P, L, hL, hPL, hcov⟩ := pos_ex u v huv
    have hp : C.eval (List.ofFn (fun k : Fin 17 => decide (emb17 k = Fin.castAdd 13 P ∨ emb17 k = Fin.natAdd 13 L))) = true := by
      simpa [circuitFun] using hpos P L hL hPL
    have hm : ∀ k : Fin 17,
        (fun k : Fin 17 => decide (emb17 k = Fin.castAdd 13 P ∨ emb17 k = Fin.natAdd 13 L)) k = true →
        (fun k : Fin 17 => decide (k = u ∨ k = v)) k = true := by
      intro k hk
      have h := hcov k hk
      simp [h]
    have h := hmono_eval C hM _ _ hm hp
    simpa [circuitFun] using h
  have hsingle : ∀ k : Fin 17, C.eval (List.ofFn (fun i : Fin 17 => decide (i = k))) = false := by
    intro k
    have h := hneg k k (adj17_loop k)
    simpa [circuitFun] using h
  have hff : C.eval (List.ofFn (fun _ : Fin 17 => false)) = false := by
    rw [Bool.eq_false_iff]
    intro htrue
    have h2 := hmono_eval C hM (fun _ : Fin 17 => false) (fun i : Fin 17 => decide (i = 0))
      (fun k hk => by simp at hk) htrue
    rw [hsingle 0] at h2
    exact Bool.noConfusion h2
  have he05 : ∀ x : Fin 17 → Bool, x 0 = true → x 5 = true → C.eval (List.ofFn x) = true := by
    intro x h0 h5
    have hp : C.eval (List.ofFn (fun k : Fin 17 => decide (k = 0 ∨ k = 5))) = true := by
      simpa [circuitFun] using hpos_pair 0 5 (by decide)
    exact hmono_eval C hM _ x (fun k hk => by
      simp only [decide_eq_true_eq] at hk
      rcases hk with rfl | rfl
      · exact h0
      · exact h5) hp
  have he10 : C.eval (List.ofFn (fun i : Fin 17 => decide (i = 1 ∨ i = 10))) = true := by
    simpa [circuitFun] using hpos_pair 1 10 (by decide)
  have he11 : C.eval (List.ofFn (fun i : Fin 17 => decide (i = 2 ∨ i = 11))) = true := by
    simpa [circuitFun] using hpos_pair 2 11 (by decide)
  have he12 : C.eval (List.ofFn (fun i : Fin 17 => decide (i = 3 ∨ i = 12))) = true := by
    simpa [circuitFun] using hpos_pair 3 12 (by decide)
  have he13 : C.eval (List.ofFn (fun i : Fin 17 => decide (i = 4 ∨ i = 13))) = true := by
    simpa [circuitFun] using hpos_pair 4 13 (by decide)
  have he14 : C.eval (List.ofFn (fun i : Fin 17 => decide (i = 0 ∨ i = 14))) = true := by
    simpa [circuitFun] using hpos_pair 0 14 (by decide)
  have he15 : C.eval (List.ofFn (fun i : Fin 17 => decide (i = 1 ∨ i = 15))) = true := by
    simpa [circuitFun] using hpos_pair 1 15 (by decide)
  have peel : ∀ (D : Circuit) (k : Fin 17) (z : Fin 17 → Bool)
      (hD : Monotone2 D)
      (hev : ∀ x : Fin 17 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn fun i => if z i then false else x i))
      (hz0 : z 0 = false) (hz5 : z 5 = false) (hzk : z k = false) (hk5 : 5 < k.val)
      (pi : Fin 17) (hpi5 : pi.val < 5) (hzpi : z pi = false)
      (htrue : C.eval (List.ofFn (fun i : Fin 17 => decide (i = pi ∨ i = k))) = true),
      ∃ D' : Circuit, Monotone2 D' ∧ D'.size + 1 ≤ D.size ∧
        ∀ x : Fin 17 → Bool, D'.eval (List.ofFn x) =
          C.eval (List.ofFn fun i => if (z i || decide (i = k)) then false else x i) := by
    intro D k z hD hev hz0 hz5 hzk hk5 pi hpi5 hzpi htrue
    let x0 : Fin 17 → Bool := fun _ => false
    let x1 : Fin 17 → Bool := fun i => decide (i = 0 ∨ i = 5)
    let xe : Fin 17 → Bool := fun i => decide (i = pi)
    have hkpi : k ≠ pi := fun e => by have := congrArg Fin.val e; omega
    have h0 : D.eval (List.ofFn (Function.update x0 k false)) = false := by
      rw [hev]
      have e : (fun i : Fin 17 => if z i then false else Function.update x0 k false i) =
          fun _ : Fin 17 => false := by
        funext i
        by_cases hzi : z i = true <;> simp [x0, Function.update, hzi]
      rw [e]; exact hff
    have h1 : D.eval (List.ofFn (Function.update x1 k false)) = true := by
      rw [hev]
      apply he05
      · have h0ne : (0 : Fin 17) ≠ k := fun e => by have := congrArg Fin.val e; dsimp at this; omega
        simp [hz0, Function.update, h0ne, x1]
      · have h5ne : (5 : Fin 17) ≠ k := fun e => by have := congrArg Fin.val e; dsimp at this; omega
        simp [hz5, Function.update, h5ne, x1]
    have hne : D.eval (List.ofFn (Function.update xe k false)) ≠
        D.eval (List.ofFn (Function.update xe k true)) := by
      rw [hev, hev]
      have hf : C.eval (List.ofFn fun i => if z i then false else Function.update xe k false i) = false := by
        have e : (fun i : Fin 17 => if z i then false else Function.update xe k false i) =
            fun i : Fin 17 => decide (i = pi) := by
          funext i
          by_cases hzi : z i = true
          · have hip : i ≠ pi := fun e => by
              rw [e] at hzi
              rw [hzpi] at hzi
              exact Bool.noConfusion hzi
            simp [hzi, hip]
          · by_cases hik : i = k
            · subst hik
              simp [hzi, hkpi, Function.update]
            · by_cases hip : i = pi
              · subst hip
                simp [hzi, hik, Function.update, xe]
              · simp [hzi, hik, hip, Function.update, xe]
        rw [e]; exact hsingle pi
      have ht : C.eval (List.ofFn fun i => if z i then false else Function.update xe k true i) = true := by
        have heq : (fun i : Fin 17 => if z i then false else Function.update xe k true i) =
            (fun i : Fin 17 => decide (i = pi ∨ i = k)) := by
          funext i
          by_cases hik : i = k
          · subst hik; simp [hzk]
          · by_cases hip : i = pi
            · subst hip; simp [hzpi, Function.update, hik, xe]
            · cases hzi : z i <;> simp [Function.update, hik, hip, xe]
        rw [heq]; exact htrue
      rw [hf, ht]; decide
    have hs : D.eval (List.ofFn (fun i : Fin 17 => decide (i = k))) = false := by
      rw [hev]
      have e : (fun i : Fin 17 => if z i then false else decide (i = k)) =
          fun i : Fin 17 => decide (i = k) := by
        funext i
        by_cases hzi : z i = true
        · have hik : i ≠ k := fun e => by
            rw [e] at hzi
            rw [hzk] at hzi
            exact Bool.noConfusion hzi
          simp [hzi, hik]
        · simp [hzi]
      rw [e]; exact hsingle k
    obtain ⟨D', hDM, hDsz, hDev⟩ := essential_zero D hD k x0 x1 xe h0 h1 hne hs
    refine ⟨D', hDM, hDsz, fun x => ?_⟩
    rw [hDev, hev]
    congr 2
    funext i
    by_cases hik : i = k
    · subst hik; simp
    · simp [Function.update, hik]
  obtain ⟨C1, hM1, hsz1, hev1⟩ := peel C 10 (fun _ => false) hM
    (fun x => by simp) rfl rfl rfl (by decide) 1 (by decide) rfl he10
  obtain ⟨C2, hM2, hsz2, hev2⟩ := peel C1 11 _ hM1 hev1
    (by decide) (by decide) (by decide) (by decide) 2 (by decide) (by decide) he11
  obtain ⟨C3, hM3, hsz3, hev3⟩ := peel C2 12 _ hM2 hev2
    (by decide) (by decide) (by decide) (by decide) 3 (by decide) (by decide) he12
  obtain ⟨C4, hM4, hsz4, hev4⟩ := peel C3 13 _ hM3 hev3
    (by decide) (by decide) (by decide) (by decide) 4 (by decide) (by decide) he13
  obtain ⟨C5, hM5, hsz5, hev5⟩ := peel C4 14 _ hM4 hev4
    (by decide) (by decide) (by decide) (by decide) 0 (by decide) (by decide) he14
  obtain ⟨C6, hM6, hsz6, hev6⟩ := peel C5 15 _ hM5 hev5
    (by decide) (by decide) (by decide) (by decide) 1 (by decide) (by decide) he15
  have hC6_ext : ∀ x : Fin 11 → Bool, C6.eval (List.ofFn (ext17 x)) = C.eval (List.ofFn (ext17 x)) := by
    intro x
    rw [hev6]
    congr 2
    funext i
    fin_cases i <;> rfl
  have hC6_0 : C6.eval (List.ofFn (ext17 (fun _ => false))) = false := by
    rw [hC6_ext]
    have e : ext17 (fun _ : Fin 11 => false) = fun _ : Fin 17 => false := by
      funext i; simp [ext17]
    rw [e]; exact hff
  have hC6_1 : C6.eval (List.ofFn (ext17 (fun i : Fin 11 => decide (i = 0 ∨ i = 5)))) = true := by
    rw [hC6_ext]
    exact he05 _ (by decide) (by decide)
  obtain ⟨C11, hM11, hsz11, hev11⟩ := project17to11 C6 hM6 _ _ hC6_0 hC6_1
  have hG : GraphEval C11 core5 := by
    intro u v
    have hev : val C11 (point {u, v}) C11.output =
        C.eval (List.ofFn (ext17 (fun k : Fin 11 => decide (k = u ∨ k = v)))) := by
      have h1 : val C11 (point {u, v}) C11.output = C11.eval (List.ofFn (point {u, v})) := rfl
      have hfun : point {u, v} = fun k : Fin 11 => decide (k = u ∨ k = v) := by
        funext k
        simp [point]
      rw [h1, hev11, hC6_ext, hfun]
    constructor
    · intro ht
      by_contra hna
      have hnb : core5AdjB u v = false := by
        cases h : core5AdjB u v
        · rfl
        · exact (hna (by simpa [core5] using h)).elim
      have hnon := core5_nonedge_adj17 u v hnb
      have hfalse : C.eval (List.ofFn (ext17 (fun k : Fin 11 => decide (k = u ∨ k = v)))) = false := by
        rw [ext17_pair u v]
        have h := hneg (phi u) (phi v) hnon
        simpa [circuitFun] using h
      rw [hev, hfalse] at ht
      exact Bool.noConfusion ht
    · intro hadj
      have htrue : C.eval (List.ofFn (ext17 (fun k : Fin 11 => decide (k = u ∨ k = v)))) = true := by
        rw [ext17_pair u v]
        have h := hpos_pair (phi u) (phi v) (core5_edge_adj17 u v (show core5AdjB u v = true from hadj))
        simpa [circuitFun] using h
      rw [hev]
      exact htrue
  have h18 := core5_lb C11 hM11 hG
  omega

end PEqualNP.Outside.L_meta_5187

theorem PEqualNP.Outside.L_meta_5187 : ¬ (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (23 : ℕ) ∧ x2.output < (26 : ℕ) + x2.size ∧ (∀ (x3 x4 : Fin (13 : ℕ)), ↑x4 < (5 : ℕ) → x3 - x4 ∈ x1 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = Fin.castAdd (13 : ℕ) x3 ∨ x7 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∈ x3, ∀ x7 ∈ x4, x5 - x7 ∉ x1) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x7 - x6 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 - x8 ∈ x1}.card ≤ (2 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x3, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ x9 ∈ x4, x8 = Fin.natAdd (13 : ℕ) x9)) = Bool.false) := by
  rintro ⟨C, hM, hsz, -, hpos, hneg⟩
  refine PEqualNP.Outside.L_meta_5187.main_proof (PEqualNP.Outside.L_meta_5187.shrink C)
    (PEqualNP.Outside.L_meta_5187.shrink_mono C hM)
    (by simpa [PEqualNP.Outside.L_meta_5187.shrink, PEqualNP.CircuitLowerBounds.Circuit.size] using hsz) ?_ ?_
  · intro P L hL hPL
    rw [PEqualNP.Outside.L_meta_5187.sim, PEqualNP.Outside.L_meta_5187.pos_mask P L hL hPL]
    exact hpos P L hL hPL
  · intro u v huv
    obtain ⟨h1, h2, h3, h4⟩ := PEqualNP.Outside.L_meta_5187.neg_ok u v huv
    rw [PEqualNP.Outside.L_meta_5187.sim, h4]
    exact hneg (PEqualNP.Outside.L_meta_5187.ptsOf u v)
      (PEqualNP.Outside.L_meta_5187.linesOf u v) h1 h2 h3
