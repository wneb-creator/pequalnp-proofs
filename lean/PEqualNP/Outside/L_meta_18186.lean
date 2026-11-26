import Mathlib.Data.Tree.Basic
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18186

namespace GraphTools

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi
          exact absurd hi (by decide)

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl b => b
  | Sum.inr k => w.getD k false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < m

lemma statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hk => lt_of_lt_of_le hk h

lemma statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s → statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr k, hk => getD_append_left_lt w t k hk

def simpMono (op : GateOp) (m : ℕ) (ins : List Stat) : Stat × Option Gate :=
  match op with
  | GateOp.and =>
    match ins with
    | [] => (Sum.inl true, none)
    | [s] => (s, none)
    | [s1, s2] =>
      match s1, s2 with
      | Sum.inl false, _ => (Sum.inl false, none)
      | _, Sum.inl false => (Sum.inl false, none)
      | Sum.inl true, s => (s, none)
      | s, Sum.inl true => (s, none)
      | Sum.inr a, Sum.inr b => (Sum.inr m, some ⟨GateOp.and, [a, b]⟩)
    | _ => (Sum.inl false, none)
  | GateOp.or =>
    match ins with
    | [] => (Sum.inl false, none)
    | [s] => (s, none)
    | [s1, s2] =>
      match s1, s2 with
      | Sum.inl true, _ => (Sum.inl true, none)
      | _, Sum.inl true => (Sum.inl true, none)
      | Sum.inl false, s => (s, none)
      | s, Sum.inl false => (s, none)
      | Sum.inr a, Sum.inr b => (Sum.inr m, some ⟨GateOp.or, [a, b]⟩)
    | _ => (Sum.inl false, none)
  | _ => (Sum.inl false, none)

lemma simpMono_ok (op : GateOp) (m : ℕ) (ins : List Stat)
    (hins : ∀ s ∈ ins, statValid m s) :
    let res := simpMono op m ins
    statValid (m + res.2.toList.length) res.1 ∧
    ∀ g, res.2 = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  cases op with
  | and =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statValid]
    · refine ⟨by simpa [simpMono] using hins s1 (by simp), fun _ h => by simp [simpMono] at h⟩
    · cases s1 with
      | inl b1 =>
        cases b1
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr _ => simp [simpMono, statValid]
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr b => refine ⟨by simpa [simpMono] using hins (Sum.inr b) (by simp), fun _ h => by simp [simpMono] at h⟩
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2
          · simp [simpMono, statValid]
          · refine ⟨by simpa [simpMono] using hins (Sum.inr a) (by simp), fun _ h => by simp [simpMono] at h⟩
        | inr b =>
          simp [simpMono, statValid]
    · simp [simpMono, statValid]
  | or =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statValid]
    · refine ⟨by simpa [simpMono] using hins s1 (by simp), fun _ h => by simp [simpMono] at h⟩
    · cases s1 with
      | inl b1 =>
        cases b1
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr b => refine ⟨by simpa [simpMono] using hins (Sum.inr b) (by simp), fun _ h => by simp [simpMono] at h⟩
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr _ => simp [simpMono, statValid]
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2
          · refine ⟨by simpa [simpMono] using hins (Sum.inr a) (by simp), fun _ h => by simp [simpMono] at h⟩
          · simp [simpMono, statValid]
        | inr b =>
          simp [simpMono, statValid]
    · simp [simpMono, statValid]
  | not => simp [simpMono, statValid]
  | mod _ => simp [simpMono, statValid]
  | maj => simp [simpMono, statValid]

lemma simpMono_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2) :
    let res := simpMono op w.length ins
    statVal (res.2.toList.foldl step w) res.1 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statVal, GateOp.eval]
    · simp [simpMono, statVal, GateOp.eval]
    · cases s1 with
      | inl b1 =>
        cases b1 <;> cases s2 with | inl b2 => cases b2 <;> simp [simpMono, statVal, GateOp.eval] | inr _ => simp [simpMono, statVal, GateOp.eval]
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2 <;> simp [simpMono, statVal, GateOp.eval]
        | inr b =>
          simp only [simpMono, Option.toList_some, List.foldl_cons, List.foldl_nil, step, statVal, getD_append_self, GateOp.eval, List.map_cons, List.map_nil]
    · simp at hlen
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statVal, GateOp.eval]
    · simp [simpMono, statVal, GateOp.eval]
    · cases s1 with
      | inl b1 =>
        cases b1 <;> cases s2 with | inl b2 => cases b2 <;> simp [simpMono, statVal, GateOp.eval] | inr _ => simp [simpMono, statVal, GateOp.eval]
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2 <;> simp [simpMono, statVal, GateOp.eval]
        | inr b =>
          simp only [simpMono, Option.toList_some, List.foldl_cons, List.foldl_nil, step, statVal, getD_append_self, GateOp.eval, List.map_cons, List.map_nil]
    · simp at hlen

def elimPass (n j0 : ℕ) (repl : List Stat → Stat) (gs : List Gate) : List Stat × List Gate :=
  (gs.zipIdx).foldl (fun acc p =>
    let tbl := acc.1
    let outG := acc.2
    if p.2 = j0 then
      (tbl ++ [repl tbl], outG)
    else
      let ins := p.1.inputs.map (fun i => if i < n + p.2 then tbl.getD i (Sum.inl false) else Sum.inl false)
      let res := simpMono p.1.op (n + outG.length) ins
      (tbl ++ [res.1], outG ++ res.2.toList))
    (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat)), [])

lemma elim_step_core (n j0 : ℕ) (repl : List Stat → Stat)
    (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C) (hj0 : j0 < C.gates.length)
    (skip : Bool)
    (hrepl_valid : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (tbl.getD i (Sum.inl false))) →
      statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (repl tbl))
    (hrepl_val : skip = false → ∀ (x : Fin n → Bool) (tbl : List Stat) (w' : List Bool),
      tbl.length = n + j0 →
      (∀ i < n + j0, statVal w' (tbl.getD i (Sum.inl false)) = (C.wires (List.ofFn x)).getD i false) →
      statVal w' (repl tbl) = (C.wires (List.ofFn x)).getD (n + j0) false)
    (hunused : skip = true → ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → j ≠ j0 → n + j0 ∉ g.inputs) :
    let res := elimPass n j0 repl C.gates
    res.1.length = n + C.gates.length ∧
    res.2.length < C.gates.length ∧
    (∀ g ∈ res.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ i < n + C.gates.length, statValid (n + res.2.length) (res.1.getD i (Sum.inl false))) ∧
    (∀ (x : Fin n → Bool) (i : ℕ), i < n + C.gates.length → (skip = true → i ≠ n + j0) →
      statVal (res.2.foldl step (List.ofFn x)) (res.1.getD i (Sum.inl false)) = (C.wires (List.ofFn x)).getD i false) := by
  have hpref : ∀ k ≤ C.gates.length,
      let res := elimPass n j0 repl (C.gates.take k)
      res.1.length = n + k ∧
      res.2.length ≤ (if j0 < k then k - 1 else k) ∧
      (∀ g ∈ res.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ i < n + k, statValid (n + res.2.length) (res.1.getD i (Sum.inl false))) ∧
      (∀ (x : Fin n → Bool) (i : ℕ), i < n + k → (skip = true → i ≠ n + j0) →
        statVal (res.2.foldl step (List.ofFn x)) (res.1.getD i (Sum.inl false)) = (C.wires (List.ofFn x)).getD i false) := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.take_zero, elimPass, List.zipIdx_nil, List.foldl_nil, List.length_ofFn, add_zero, List.length_nil, Nat.not_lt_zero, ↓reduceIte, le_refl, List.not_mem_nil, IsEmpty.forall_iff, imp_true_iff, true_and]
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, ↓reduceDIte, Option.getD_some, statValid, hi]
      · intro x i hi _
        have hget : (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat))).getD i (Sum.inl false) = Sum.inr i := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
        rw [hget]
        simp only [statVal, wires_input C x i hi, ofFn_getD_lt x i hi]
    | succ k ih =>
      obtain ⟨hlen, hsz, hgm, hval, hsnd⟩ := ih (by omega)
      have hklt : k < C.gates.length := by omega
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]'hklt] := List.take_succ_eq_append_getElem hklt
      have hzip : (C.gates.take (k + 1)).zipIdx = (C.gates.take k).zipIdx ++ [(C.gates[k]'hklt, k)] := by
        rw [htake, List.zipIdx_append]
        simp [List.length_take, Nat.min_eq_left (by omega : k ≤ C.gates.length)]
      set prev := elimPass n j0 repl (C.gates.take k)
      have hstep : elimPass n j0 repl (C.gates.take (k + 1)) =
          if k = j0 then
            (prev.1 ++ [repl prev.1], prev.2)
          else
            let ins := (C.gates[k]'hklt).inputs.map (fun i => if i < n + k then prev.1.getD i (Sum.inl false) else Sum.inl false)
            let res := simpMono (C.gates[k]'hklt).op (n + prev.2.length) ins
            (prev.1 ++ [res.1], prev.2 ++ res.2.toList) := by
        show ((C.gates.take (k + 1)).zipIdx).foldl _ _ = _
        rw [hzip, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      rw [hstep]
      by_cases hkj : k = j0
      · subst hkj
        simp only [↓reduceIte, lt_irrefl, Nat.lt_succ_self] at hsz ⊢
        refine ⟨by simp [hlen]; omega, by omega, hgm, ?_, ?_⟩
        · intro i hi
          by_cases hik : i < n + k
          · rw [getD_append_left_lt_stat]
            · exact hval i hik
            · omega
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [repl prev.1]).getD (n + k) (Sum.inl false) = repl prev.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            exact hrepl_valid prev.1 hlen hval
        · intro x i hi hsk
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [repl prev.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]
            exact hsnd x i hik hsk
          · have heq : i = n + k := by omega
            subst heq
            have hskf : skip = false := by
              cases h : skip
              · rfl
              · exact absurd rfl (hsk h)
            have hget : (prev.1 ++ [repl prev.1]).getD (n + k) (Sum.inl false) = repl prev.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            exact hrepl_val hskf x prev.1 (prev.2.foldl step (List.ofFn x)) hlen (fun i hi => hsnd x i hi (by intro h; rw [hskf] at h; cases h))
      · simp only [hkj, ↓reduceIte]
        set g := C.gates[k]'hklt
        set ins := g.inputs.map (fun i => if i < n + k then prev.1.getD i (Sum.inl false) else Sum.inl false)
        set sm := simpMono g.op (n + prev.2.length) ins
        have hsm_ok := simpMono_ok g.op (n + prev.2.length) ins (fun s hs => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
          by_cases hi : i < n + k
          · simp only [hi, ↓reduceIte]; exact hval i hi
          · simp only [hi, ↓reduceIte, statValid])
        have htolen : sm.2.toList.length ≤ 1 := by cases sm.2 <;> simp
        refine ⟨by simp [hlen]; omega, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append]
          split_ifs at hsz ⊢ <;> omega
        · intro g' hg'
          rcases List.mem_append.mp hg' with hm | hm
          · exact hgm g' hm
          · cases h2 : sm.2 with
            | none => rw [h2] at hm; simp at hm
            | some g0 =>
              rw [h2] at hm
              simp only [Option.toList_some, List.mem_singleton] at hm
              subst hm
              exact hsm_ok.2 g' h2
        · intro i hi
          simp only [List.length_append]
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [sm.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]
            exact statValid_mono (by omega) _ (hval i hik)
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [sm.1]).getD (n + k) (Sum.inl false) = sm.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            rw [← Nat.add_assoc]
            exact hsm_ok.1
        · intro x i hi hsk
          rw [List.foldl_append]
          have hprevlen : (prev.2.foldl step (List.ofFn x)).length = n + prev.2.length := by
            rw [foldl_step_len, List.length_ofFn]
          by_cases hik : i < n + k
          · have hget : (prev.1 ++ [sm.1]).getD i (Sum.inl false) = prev.1.getD i (Sum.inl false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < prev.1.length)]
            rw [hget]
            have hkeep : statVal (sm.2.toList.foldl step (prev.2.foldl step (List.ofFn x))) (prev.1.getD i (Sum.inl false)) =
                statVal (prev.2.foldl step (List.ofFn x)) (prev.1.getD i (Sum.inl false)) := by
              have hvi := hval i hik
              cases hs : prev.1.getD i (Sum.inl false) with
              | inl b => rfl
              | inr m =>
                rw [hs] at hvi
                exact foldl_step_getD_lt sm.2.toList _ m (by rw [hprevlen]; exact hvi)
            rw [hkeep]
            exact hsnd x i hik hsk
          · have heq : i = n + k := by omega
            subst heq
            have hget : (prev.1 ++ [sm.1]).getD (n + k) (Sum.inl false) = sm.1 := by
              rw [← hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            rw [hget]
            have hgmem : g ∈ C.gates := List.getElem_mem hklt
            have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hmono g hgmem).1
            have hglen : ins.length ≤ 2 := by simp only [ins, List.length_map]; exact (hmono g hgmem).2
            have hsms := simpMono_sound g.op hgop (prev.2.foldl step (List.ofFn x)) ins hglen
            rw [hprevlen] at hsms
            change statVal (sm.2.toList.foldl step (prev.2.foldl step (List.ofFn x))) sm.1 = _
            rw [hsms]
            have hgetk : C.gates[k]? = some g := List.getElem?_eq_getElem hklt
            rw [wires_gate_ofFn C x k g hgetk]
            congr 1
            simp only [ins, List.map_map]
            apply List.map_congr_left
            intro u hu
            simp only [Function.comp_apply]
            by_cases hu_lt : u < n + k
            · simp only [hu_lt, ↓reduceIte]
              apply hsnd x u hu_lt
              intro hskt hequ
              subst hequ
              exact hunused hskt k g hgetk hkj hu
            · simp only [hu_lt, ↓reduceIte, statVal]
  have hfull := hpref C.gates.length (le_refl _)
  rw [List.take_length] at hfull
  simp only [hj0, ↓reduceIte] at hfull
  exact ⟨hfull.1, by omega, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2⟩
where
  getD_append_left_lt_stat (w t : List Stat) (i : ℕ) (hi : i < w.length) :
      (w ++ t).getD i (Sum.inl false) = w.getD i (Sum.inl false) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def orEndAux (n s : ℕ) (C : Circuit) (outdeg nextOf : ℕ → ℕ)
    (hnext : ∀ w, w < n + s - 1 → outdeg w = 1 → w < n + nextOf w) (w : ℕ) : ℕ :=
  if _h : w < n + s - 1 ∧ outdeg w = 1 then
    if hlt : nextOf w < C.gates.length then
      match (C.gates[nextOf w]'hlt).op with
      | GateOp.or => orEndAux n s C outdeg nextOf hnext (n + nextOf w)
      | _ => w
    else w
  else w
termination_by n + s - w
decreasing_by
  have := hnext w _h.1 _h.2
  omega

def orChainAux (n s : ℕ) (C : Circuit) (outdeg nextOf : ℕ → ℕ)
    (hnext : ∀ w, w < n + s - 1 → outdeg w = 1 → w < n + nextOf w) (w : ℕ) : Finset ℕ :=
  if _h : w < n + s - 1 ∧ outdeg w = 1 then
    if hlt : nextOf w < C.gates.length then
      match (C.gates[nextOf w]'hlt).op with
      | GateOp.or => insert w (orChainAux n s C outdeg nextOf hnext (n + nextOf w))
      | _ => ∅
    else ∅
  else ∅
termination_by n + s - w
decreasing_by
  have := hnext w _h.1 _h.2
  omega

end GraphTools

namespace Sparse2008

open PEqualNP.CircuitLowerBounds GraphTools

def Tiny {n : ℕ} (x : Fin n → Bool) := ∃ a b : Fin n, ∀ i, x i = true → i=a ∨ i=b

def SparseTruth {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :=
  (∀ x : Fin n → Bool, Tiny x → C.eval (List.ofFn x)=true →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ∧
  (∀ x : Fin n → Bool, (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      C.eval (List.ofFn x)=true)

theorem tinyOne {n : ℕ} (v : Fin n) : Tiny (fun i => decide (i=v)) :=
  ⟨v,v,fun _ h => Or.inl (of_decide_eq_true h)⟩

theorem tinyTwo {n : ℕ} (v w : Fin n) : Tiny (fun i => decide (i=v ∨ i=w)) :=
  ⟨v,w,fun _ h => of_decide_eq_true h⟩

theorem elimSparse {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hfun : SparseTruth G C)
    (hedge : ∃ u v : Fin n, G.Adj u v)
    (j0 : ℕ) (hj0 : j0 < C.gates.length)
    (repl : List Stat → Stat) (skip : Bool)
    (hrepl_valid : ∀ tbl : List Stat, tbl.length = n + j0 →
      (∀ i < n + j0, statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (tbl.getD i (Sum.inl false))) →
      statValid (n + (elimPass n j0 repl (C.gates.take j0)).2.length) (repl tbl))
    (hrepl_val : skip = false → ∀ (x : Fin n → Bool) (tbl : List Stat) (w' : List Bool),
      tbl.length = n + j0 →
      (∀ i < n + j0, statVal w' (tbl.getD i (Sum.inl false)) = (C.wires (List.ofFn x)).getD i false) →
      statVal w' (repl tbl) = (C.wires (List.ofFn x)).getD (n + j0) false)
    (hunused : skip = true → (C.output ≠ n + j0 ∧ ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → j ≠ j0 → n + j0 ∉ g.inputs)) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size < C.size ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hcore := elim_step_core n j0 repl C hmono hj0 skip hrepl_valid hrepl_val (fun h => (hunused h).2)
  set res := elimPass n j0 repl C.gates
  obtain ⟨u0, v0, huv0⟩ := hedge
  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    have ht : C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true :=
      hfun.2 _ ⟨u0, v0, huv0, by simp, by simp⟩
    unfold Circuit.eval at ht
    rw [wires_oob C _ C.output (by omega)] at ht
    exact absurd ht (by decide)
  have hzero : C.eval (List.ofFn (fun _ : Fin n => false)) = false := by
    cases h : C.eval (List.ofFn (fun _ : Fin n => false)) with
    | false => rfl
    | true =>
      obtain ⟨_, _, _, hu, _⟩ := hfun.1 _ ⟨u0,u0,by simp⟩ h
      exact absurd hu (by decide)
  have hout_ne : skip = true → C.output ≠ n + j0 := fun h => (hunused h).1
  cases hout : res.1.getD C.output (Sum.inl false) with
  | inl b =>
    cases b
    · have ht := hcore.2.2.2.2 (fun t : Fin n => decide (t = u0 ∨ t = v0)) C.output hout_lt hout_ne
      rw [hout] at ht
      change false = C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) at ht
      have ht2 : C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true :=
        hfun.2 _ ⟨u0, v0, huv0, by simp, by simp⟩
      rw [ht2] at ht; exact absurd ht (by decide)
    · have ht := hcore.2.2.2.2 (fun _ : Fin n => false) C.output hout_lt hout_ne
      rw [hout] at ht
      change true = C.eval (List.ofFn (fun _ : Fin n => false)) at ht
      rw [hzero] at ht; exact absurd ht (by decide)
  | inr wout =>
    refine ⟨⟨res.2, wout⟩, ?_, hcore.2.1, ?_⟩
    · intro g hg
      have := hcore.2.2.1 g hg
      exact ⟨by simpa using this.1, this.2⟩
    · intro x
      have hx := hcore.2.2.2.2 x C.output hout_lt hout_ne
      rw [hout] at hx
      exact hx

end Sparse2008

namespace WireFacts

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

end WireFacts

namespace RepReads

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity WireFacts
open PEqualNP.Represents

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

theorem inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

end RepReads

namespace RepInduced

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity WireFacts
open PEqualNP.Represents RepReads

open scoped Classical

section kill
variable (N : ℕ) (Z : Finset ℕ) (gs : List Gate)

def gat (j : ℕ) : Gate := gs.getD j ⟨.and, []⟩

noncomputable def st : ℕ → List Gate × (ℕ → Option ℕ)
  | 0 => ([], fun w => if w < N ∧ w ∉ Z then some w else none)
  | j + 1 =>
    let p := st j
    let g := gat gs j
    if ∃ i ∈ g.inputs, p.2 i = none then
      (p.1, Function.update p.2 (N + j)
        (if g.op = GateOp.and then none else (g.inputs.filterMap p.2).head?))
    else (p.1 ++ [⟨g.op, g.inputs.map fun i => (p.2 i).getD 0⟩],
      Function.update p.2 (N + j) (some (N + p.1.length)))

def Dead (j : ℕ) : Prop := ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i = none

theorem st_dead {j : ℕ} (h : Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1, Function.update (st N Z gs j).2 (N + j)
      (if (gat gs j).op = GateOp.and then none
        else ((gat gs j).inputs.filterMap (st N Z gs j).2).head?)) := by
  rw [st]; exact if_pos h

theorem st_keep {j : ℕ} (h : ¬ Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1 ++ [⟨(gat gs j).op, (gat gs j).inputs.map fun i =>
      ((st N Z gs j).2 i).getD 0⟩],
      Function.update (st N Z gs j).2 (N + j) (some (N + (st N Z gs j).1.length))) := by
  rw [st]; exact if_neg h

theorem st_ne {j w : ℕ} (h : w ≠ N + j) : (st N Z gs (j + 1)).2 w = (st N Z gs j).2 w := by
  by_cases hd : Dead N Z gs j
  · rw [st_dead N Z gs hd]; exact Function.update_of_ne h _ _
  · rw [st_keep N Z gs hd]; exact Function.update_of_ne h _ _

theorem st_late (j : ℕ) : ∀ w, N + j ≤ w → (st N Z gs j).2 w = none := by
  induction j with
  | zero => intro w h; simp [st, show ¬ w < N by omega]
  | succ j ih => intro w h; rw [st_ne N Z gs (by omega)]; exact ih w (by omega)

theorem st_final {j k w : ℕ} (hjk : j ≤ k) (h : w < N + j) :
    (st N Z gs k).2 w = (st N Z gs j).2 w := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [st_ne N Z gs (by omega)]; exact ih

theorem st_off {j k w : ℕ} (hjk : j ≤ k) (h : (st N Z gs k).2 w = none) :
    (st N Z gs j).2 w = none := by
  by_cases hw : w < N + j
  · rw [← st_final N Z gs hjk hw]; exact h
  · exact st_late N Z gs j w (by omega)

theorem st_len (j : ℕ) : (st N Z gs j).1.length +
    ((Finset.range j).filter fun i => Dead N Z gs i).card = j := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hd : Dead N Z gs j
    · rw [if_pos hd, Finset.card_insert_of_notMem (by simp), st_dead N Z gs hd]
      show (st N Z gs j).1.length + _ = _
      omega
    · rw [if_neg hd, st_keep N Z gs hd]
      simp only [List.length_append, List.length_singleton]
      omega

theorem st_lt (j : ℕ) : ∀ w a, (st N Z gs j).2 w = some a → a < N + (st N Z gs j).1.length := by
  induction j with
  | zero =>
    intro w a h
    simp only [st] at h
    split_ifs at h with hw
    · simp only [Option.some.injEq] at h
      simp [st]; omega
  | succ j ih =>
    intro w a h
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd] at h ⊢
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self] at h
        split_ifs at h
        have hm := List.mem_of_mem_head? (Option.mem_def.2 h)
        obtain ⟨i, _, hi⟩ := List.mem_filterMap.1 hm
        exact ih i a hi
      · simp only [Function.update_of_ne hw] at h
        exact ih w a h
    · rw [st_keep N Z gs hd] at h ⊢
      simp only [List.length_append, List.length_singleton]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, Option.some.injEq] at h
        omega
      · simp only [Function.update_of_ne hw] at h
        have := ih w a h
        omega

variable (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)

include hgs in
theorem gat_ok (j : ℕ) : ((gat gs j).op = GateOp.and ∨ (gat gs j).op = GateOp.or) ∧
    (gat gs j).inputs.length ≤ 2 := by
  by_cases h : j < gs.length
  · have := hgs (gat gs j) (by rw [gat, List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
    simpa using this
  · rw [gat, List.getD_eq_default _ _ (by omega)]; simp

include hgs in
theorem st_ok (j : ℕ) : ∀ g ∈ (st N Z gs j).1,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]; exact ih
    · rw [st_keep N Z gs hd]
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ih g hg
      · rw [List.mem_singleton.1 hg]
        have := gat_ok gs hgs j
        simpa using this

theorem take_succ (j : ℕ) (hj : j < gs.length) : gs.take (j + 1) = gs.take j ++ [gat gs j] := by
  rw [List.take_succ_eq_append_getElem hj, gat, List.getD_eq_getElem _ _ hj]

include hgs in

theorem st_val (P : Finset ℕ) (j : ℕ) (hj : j ≤ gs.length) : ∀ w,
    ((st N Z gs j).2 w = none → (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false = false) ∧
    ∀ a, (st N Z gs j).2 w = some a → (wiresFrom (st N Z gs j).1 (inp N P)).getD a false =
      (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false := by
  induction j with
  | zero =>
    intro w
    simp only [st, List.take_zero, wiresFrom, List.foldl_nil, inp_getD, Finset.mem_sdiff]
    constructor
    · intro h
      split_ifs at h with hw
      simp only [decide_eq_false_iff_not]; tauto
    · intro a h
      split_ifs at h with hw
      simp only [Option.some.injEq] at h
      subst h
      rw [decide_eq_decide]; tauto
  | succ j ih =>
    have H := ih (by omega)
    have hl1 : (wiresFrom (gs.take j) (inp N (P \ Z))).length = N + j := by
      rw [length_wiresFrom, List.length_take]; simp [inp]; omega
    have hl2 : (wiresFrom (st N Z gs j).1 (inp N P)).length = N + (st N Z gs j).1.length := by
      rw [length_wiresFrom]; simp [inp]
    have hok := gat_ok gs hgs j
    rw [take_succ gs j (by omega), wiresFrom_snoc]
    set V := wiresFrom (gs.take j) (inp N (P \ Z)) with hV
    intro w
    rw [getD_snoc, hl1]
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        obtain ⟨i, hi, hoff⟩ := hd
        have hi0 := (H i).1 hoff
        rcases hok.1 with hop | hop
        · simp only [hop, if_true]
          refine ⟨fun _ => ?_, fun a h => by simp at h⟩
          rw [← Bool.not_eq_true, GateOp.eval, List.all_eq_true]
          intro h
          have := h _ (List.mem_map.2 ⟨i, hi, rfl⟩)
          rw [hi0] at this; simp at this
        · simp only [hop, reduceCtorEq, if_false]

          have hlen := hok.2
          constructor
          · intro h
            rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at h
            rw [← Bool.not_eq_true, GateOp.eval, List.any_eq_true]
            rintro ⟨b, hb, hb1⟩
            obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hb
            have := (H i').1 (h i' hi')
            rw [this] at hb1; simp at hb1
          · intro a h
            obtain ⟨i', hi', hia⟩ := List.mem_filterMap.1 (List.mem_of_mem_head? (Option.mem_def.2 h))
            rw [(H i').2 a hia, GateOp.eval]
            have hne : i ≠ i' := by rintro rfl; rw [hoff] at hia; simp at hia

            have hall : ∀ b ∈ (gat gs j).inputs, b = i ∨ b = i' := by
              intro b hb
              by_contra hn
              push Not at hn
              have h3 : ({i, i', b} : Finset ℕ) ⊆ (gat gs j).inputs.toFinset := by
                intro c hc
                simp only [Finset.mem_insert, Finset.mem_singleton] at hc
                rcases hc with rfl | rfl | rfl <;> simpa
              have := Finset.card_le_card h3
              rw [Finset.card_eq_three.2 ⟨i, i', b, hne, fun e => hn.1 e.symm, fun e => hn.2 e.symm,
                rfl⟩] at this
              have := List.toFinset_card_le (gat gs j).inputs
              omega
            apply Bool.eq_iff_iff.2
            rw [List.any_eq_true]
            constructor
            · intro hv; exact ⟨_, List.mem_map.2 ⟨i', hi', rfl⟩, hv⟩
            · rintro ⟨b, hb, hb1⟩
              obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
              rcases hall c hc with rfl | rfl
              · rw [hi0] at hb1; simp at hb1
              · exact hb1
      · simp only [Function.update_of_ne hw, if_neg hw]
        exact H w
    · rw [st_keep N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        refine ⟨fun h => by simp at h, fun a h => ?_⟩
        simp only [Option.some.injEq] at h
        subst h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_pos rfl]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        obtain ⟨b, hb⟩ : ∃ b, (st N Z gs j).2 i = some b := by
          cases h : (st N Z gs j).2 i with
          | none => exact absurd ⟨i, hi, h⟩ hd
          | some b => exact ⟨b, rfl⟩
        simp only [Function.comp_apply, hb, Option.getD_some]
        exact (H i).2 b hb
      · simp only [Function.update_of_ne hw, if_neg hw]
        refine ⟨(H w).1, fun a h => ?_⟩
        have hlt := st_lt N Z gs j w a h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_neg (by omega)]
        exact (H w).2 a h

def Live (o : ℕ) : ℕ → Prop :=
  Relation.ReflTransGen (fun g w => ∃ j < gs.length, g = N + j ∧ w ∈ (gat gs j).inputs) o

theorem live_dep (o : ℕ) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (h : ∀ i, Live N gs o i → x.getD i false = y.getD i false) (j : ℕ) (hj : j ≤ gs.length) :
    ∀ w, Live N gs o w →
      (wiresFrom (gs.take j) x).getD w false = (wiresFrom (gs.take j) y).getD w false := by
  induction j with
  | zero => intro w hw; simpa [wiresFrom] using h w hw
  | succ j ih =>
    intro w hw
    have H := ih (by omega)
    rw [take_succ gs j (by omega), wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc,
      length_wiresFrom, length_wiresFrom, hx, hy, List.length_take, Nat.min_eq_left (by omega)]
    split_ifs with hwj
    · congr 1
      apply List.map_congr_left
      intro a ha
      exact H a (hw.tail ⟨j, by omega, hwj, ha⟩)
    · exact H w hw

include hgs in

theorem kill_count (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (ho : (st N Z gs gs.length).2 o ≠ none) :
    Z0.card ≤ ((Finset.range gs.length).filter fun i => Dead N Z gs i).card := by
  set k := gs.length with hk
  let K := (Finset.range k).filter fun j => Dead N Z gs j ∧ Live N gs o (N + j)
  let Y := (Finset.range k).filter fun j => (st N Z gs k).2 (N + j) = none ∧ Live N gs o (N + j)
  let Q : Finset (Σ _ : ℕ, ℕ) := K.sigma fun j =>
    (gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none
  let W := Z0 ∪ Y.image fun j => N + j
  have hYK : Y ⊆ K := by
    intro j hj
    obtain ⟨hjk, hz, hl⟩ := Finset.mem_filter.1 hj
    refine Finset.mem_filter.2 ⟨hjk, ?_, hl⟩
    by_contra hd
    have hjk' := Finset.mem_range.1 hjk
    rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_keep N Z gs hd] at hz
    simp at hz
  have hW : W ⊆ Q.image fun q => q.2 := by
    intro w hw
    have hw2 : (st N Z gs k).2 w = none ∧ Live N gs o w := by
      rcases Finset.mem_union.1 hw with h | h
      · obtain ⟨h1, h2, h3⟩ := hZ0 w h
        refine ⟨?_, h3⟩
        rw [st_final N Z gs (Nat.zero_le k) (by omega)]
        simp [st, h2]
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
        exact (Finset.mem_filter.1 hj).2
    have hne : w ≠ o := fun e => ho (e ▸ hw2.1)
    rcases Relation.ReflTransGen.cases_tail hw2.2 with e | ⟨g, hg, j, hj, rfl, hi⟩
    · exact absurd e hne
    · have hoff := st_off N Z gs (show j ≤ k by omega) hw2.1
      refine Finset.mem_image.2 ⟨⟨j, w⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, rfl⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ⟨w, hi, hoff⟩, hg⟩
      · exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 hi, hoff⟩
  have hWc : W.card = Z0.card + Y.card := by
    have : Disjoint Z0 (Y.image fun j => N + j) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 h2
      have := (hZ0 _ h1).1
      omega
    show (Z0 ∪ Y.image fun j => N + j).card = _
    rw [Finset.card_union_of_disjoint this,
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  have hQ : Q.card ≤ K.card + Y.card := by
    show (K.sigma _).card ≤ _
    rw [Finset.card_sigma]
    calc ∑ j ∈ K, ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card
        ≤ ∑ j ∈ K, (1 + if j ∈ Y then 1 else 0) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hjk, hd, hl⟩ := Finset.mem_filter.1 hj
          have hjk' := Finset.mem_range.1 hjk
          have hok := gat_ok gs hgs j
          have hc := List.toFinset_card_le (gat gs j).inputs
          have hf := Finset.card_filter_le (gat gs j).inputs.toFinset
            fun i => (st N Z gs j).2 i = none
          split_ifs with hY
          · omega
          ·
            have hsome : (st N Z gs k).2 (N + j) ≠ none := fun e =>
              hY (Finset.mem_filter.2 ⟨hjk, e, hl⟩)
            rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_dead N Z gs hd] at hsome
            simp only [Function.update_self] at hsome
            obtain ⟨i, hi, hia⟩ : ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i ≠ none := by
              by_contra hn
              push Not at hn
              apply hsome
              split_ifs
              · rfl
              · rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff]; exact hn
            have hlt : ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card <
                (gat gs j).inputs.toFinset.card :=
              Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, List.mem_toFinset.2 hi, hia⟩)
            omega
      _ = K.card + Y.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_ite_mem,
            Finset.inter_eq_right.2 hYK, Finset.sum_const, smul_eq_mul, mul_one]
  have h1 := Finset.card_le_card hW
  have h2 := Finset.card_image_le (s := Q) (f := fun q => q.2)
  have h3 : K.card ≤ ((Finset.range k).filter fun i => Dead N Z gs i).card :=
    Finset.card_le_card fun j hj => by
      obtain ⟨a, b, _⟩ := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨a, b⟩
  omega

include hgs in

theorem kill (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (P0 : Finset ℕ) (hP0 : Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + Z0.card ≤ gs.length ∧
      ∀ P, D.eval (inp N P) = Circuit.eval ⟨gs, o⟩ (inp N (P \ Z)) := by
  have hv : ∀ P, _ := fun P => st_val N Z gs hgs P gs.length le_rfl o
  simp only [List.take_length] at hv
  have ho : (st N Z gs gs.length).2 o ≠ none := by
    intro e
    have := (hv P0).1 e
    rw [show Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) =
      (wiresFrom gs (inp N (P0 \ Z))).getD o false from rfl, this] at hP0
    exact Bool.noConfusion hP0
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 ho
  refine ⟨⟨(st N Z gs gs.length).1, a⟩, st_ok N Z gs hgs _, ?_, fun P => (hv P).2 a ha⟩
  have h1 := kill_count N Z gs hgs o Z0 hZ0 ho
  have h2 := st_len N Z gs gs.length
  show (st N Z gs gs.length).1.length + Z0.card ≤ gs.length
  omega

end kill
end RepInduced

namespace PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

end PermInputs

namespace CrownCharge9304
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity GraphTools

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) := (C.wires (List.ofFn x)).getD i false

theorem firstMeet {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (shape : ∀ j : Fin C.gates.length, ∃ a b, C.gates[j.val].inputs=[a,b] ∧ a<n+j.val ∧ b<n+j.val)
    (x y : Fin n → Bool) (o : ℕ) (limit : o<n+C.gates.length)
    (hx : val C x o=false) (hy : val C y o=false)
    (hxy : val C (fun i => x i || y i) o=true) :
    ∃ j : Fin C.gates.length, val C x (n+j.val)=false ∧
      (∃ i ∈ C.gates[j.val].inputs, i<n+j.val ∧ val C x i=true) ∧
      (∀ i ∈ C.gates[j.val].inputs, val C x i=true ∨ val C y i=true) := by
  classical
  let z (i : Fin n) := x i || y i
  let fresh (t : ℕ) := val C z t=true ∧ val C x t=false ∧ val C y t=false
  have ex : ∃ t, fresh t := ⟨o,hxy,hx,hy⟩
  let k := Nat.find ex
  obtain ⟨kz,kx,ky⟩ := Nat.find_spec ex
  change val C z k=true at kz
  change val C x k=false at kx
  change val C y k=false at ky
  have ko : k ≤ o := Nat.find_min' ex ⟨hxy,hx,hy⟩
  have earlier {a : ℕ} (ha : a<k) (on : val C z a=true) : val C x a=true ∨ val C y a=true := by
    by_contra! neg
    exact Nat.find_min ex ha ⟨on,by simpa using neg.1,by simpa using neg.2⟩
  have raw : n ≤ k := by
    by_contra! small
    simp only [val,wires_input C _ k small] at kz kx ky
    change (x ⟨k,small⟩ || y ⟨k,small⟩)=true at kz
    rw [kx,ky] at kz
    contradiction
  let j : Fin C.gates.length := ⟨k-n,by omega⟩
  have kj : k=n+j.val := by dsimp [j]; omega
  obtain ⟨a,b,hg,ha,hb⟩ := shape j
  have lookup : C.gates[j.val]?=some (C.gates[j.val]) := List.getElem?_eq_getElem j.isLt
  have op := (mono _ (List.getElem_mem j.isLt)).1
  have ka : a<k := by omega
  have kb : b<k := by omega
  rcases op with op|op
  · have E (w : Fin n → Bool) : val C w k=(val C w a && val C w b) := by
      unfold val
      rw [kj,wires_gate_ofFn C w _ _ lookup,op,hg]
      simp [ha,hb,GateOp.eval]
    rw [E] at kz kx ky
    obtain ⟨za,zb⟩ := Bool.and_eq_true_iff.mp kz
    have ea := earlier ka za
    have eb := earlier kb zb
    have ax : val C x a=true ∨ val C x b=true := by
      by_contra! no
      rw [ea.resolve_left no.1,eb.resolve_left no.2] at ky
      contradiction
    refine ⟨j,by rw [←kj,E]; exact kx,?_,?_⟩
    · rcases ax with aa|bb
      · exact ⟨a,by simp [hg],ha,aa⟩
      · exact ⟨b,by simp [hg],hb,bb⟩
    · intro u hu
      simp only [hg,List.mem_cons,List.not_mem_nil,or_false] at hu
      exact hu.elim (fun h => h ▸ ea) (fun h => h ▸ eb)
  · have E (w : Fin n → Bool) : val C w k=(val C w a || val C w b) := by
      unfold val
      rw [kj,wires_gate_ofFn C w _ _ lookup,op,hg]
      simp [ha,hb,GateOp.eval]
    rw [E] at kz kx ky
    obtain ⟨xa,xb⟩ := Bool.or_eq_false_iff.mp kx
    obtain ⟨ya,yb⟩ := Bool.or_eq_false_iff.mp ky
    rcases Bool.or_eq_true_iff.mp kz with aa|bb
    · have diff := earlier ka aa
      simp [xa,ya] at diff
    · have diff := earlier kb bb
      simp [xb,yb] at diff

end CrownCharge9304

namespace CrownCharge9304
open Sparse2008 PEqualNP.CircuitLowerBounds GraphTools

set_option maxHeartbeats 2400000 in
theorem saturationBound (n target : ℕ) (hnpos : 0<n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ v : Fin n, 3 ≤ G.degree v)
    (hdistinct_nbrs : ∀ v w : Fin n, v ≠ w → ∃ u : Fin n, G.Adj v u ∧ ¬ G.Adj w u)
    (cut : ∀ (s extra : ℕ) (T : Finset (Fin n)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T →
      n+T.card+extra=s+1 → s < target →
      (∀ v∈T, (G.neighborFinset v ∩ (Finset.univ \ T)).card ≤ 2+extra) →
      ∃ v∈T, ∃ w∈T, G.Adj v w ∧ 2+extra≤(G.neighborFinset v ∩ (Finset.univ \ T)).card) :
    ∀ s : ℕ, ∀ C : Circuit, C.size=s → PEqualNP.MetaComplexity.Monotone2 C → SparseTruth G C → target ≤ s := by
  classical
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro C hCsize hmono hfun
    have hCglen : C.gates.length = s := hCsize
    have hn1 : 1 ≤ n := by omega
    have hedge : ∃ u v : Fin n, G.Adj u v := by
      let v0 : Fin n := ⟨0, hn1⟩
      have hpos : 0 < (G.neighborFinset v0).card := by have h : 3 ≤ (G.neighborFinset v0).card := hdeg v0; omega
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      exact ⟨v0, u, (SimpleGraph.mem_neighborFinset G v0 u).mp hu⟩
    have hmin : ∀ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' → C'.size < s →
        (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) → target ≤ s := by
      intro C' hC'm hC'sz hC'eq
      have hC'fun : SparseTruth G C' := by
        constructor
        · intro x small yes; exact hfun.1 x small ((hC'eq x) ▸ yes)
        · intro x edge; rw [hC'eq x]; exact hfun.2 x edge
      have := ih C'.size hC'sz C' rfl hC'm hC'fun
      omega
    by_contra hlt_goal
    have hnot_smaller : ∀ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' → C'.size < s →
        (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) → False :=
      fun C' hm hsz heq => hlt_goal (hmin C' hm hsz heq)
    have hno_const_or_copy : ∀ (j0 : ℕ), j0 < s →
        (¬ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j0) false = false) ∧
        (¬ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j0) false = true) ∧
        (∀ w0 < n + j0, ¬ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j0) false = (C.wires (List.ofFn x)).getD w0 false) := by
      intro j0 hj0
      have hj0len : j0 < C.gates.length := by omega
      refine ⟨?_, ?_, ?_⟩
      · intro hf
        obtain ⟨C', hm', hsz', heq'⟩ := elimSparse G C hmono hfun hedge j0 hj0len (fun _ => Sum.inl false) false
          (fun _ _ _ => trivial) (fun _ x _ _ _ _ => (hf x).symm) (by intro h; cases h)
        exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
      · intro ht
        obtain ⟨C', hm', hsz', heq'⟩ := elimSparse G C hmono hfun hedge j0 hj0len (fun _ => Sum.inl true) false
          (fun _ _ _ => trivial) (fun _ x _ _ _ _ => (ht x).symm) (by intro h; cases h)
        exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
      · intro w0 hw0 heqw
        obtain ⟨C', hm', hsz', heq'⟩ := elimSparse G C hmono hfun hedge j0 hj0len (fun tbl => tbl.getD w0 (Sum.inl false)) false
          (fun tbl _ hv => hv w0 hw0)
          (fun _ x tbl w' _ hvals => (hvals w0 hw0).trans (heqw x).symm)
          (by intro h; cases h)
        exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
    have hgate_shape : ∀ (j : ℕ) (hj : j < C.gates.length),
        ∃ p q : ℕ, (C.gates[j]'hj).inputs = [p, q] ∧ p < n + j ∧ q < n + j ∧ p ≠ q := by
      intro j hj
      have hj_s : j < s := by omega
      have hg : C.gates[j]? = some (C.gates[j]'hj) := List.getElem?_eq_getElem hj
      have hgop : (C.gates[j]'hj).op = GateOp.and ∨ (C.gates[j]'hj).op = GateOp.or := by
        simpa using (hmono _ (List.getElem_mem hj)).1
      have hglen : (C.gates[j]'hj).inputs.length ≤ 2 := (hmono _ (List.getElem_mem hj)).2
      obtain ⟨hnc0, hnc1, hncw⟩ := hno_const_or_copy j hj_s
      rcases hinp : (C.gates[j]'hj).inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
      · rcases hgop with hand | hor
        · exfalso; apply hnc1; intro x; rw [wires_gate_ofFn C x j _ hg, hand, hinp]; rfl
        · exfalso; apply hnc0; intro x; rw [wires_gate_ofFn C x j _ hg, hor, hinp]; rfl
      · by_cases hp : p < n + j
        · exfalso; apply hncw p hp; intro x
          rw [wires_gate_ofFn C x j _ hg, hinp]
          rcases hgop with hand | hor
          · simp [hand, GateOp.eval, hp]
          · simp [hor, GateOp.eval, hp]
        · exfalso; apply hnc0; intro x
          rw [wires_gate_ofFn C x j _ hg, hinp]
          rcases hgop with hand | hor
          · simp [hand, GateOp.eval, hp]
          · simp [hor, GateOp.eval, hp]
      · by_cases hp : p < n + j
        · by_cases hq : q < n + j
          · by_cases hpq : p = q
            · subst hpq
              exfalso; apply hncw p hp; intro x
              rw [wires_gate_ofFn C x j _ hg, hinp]
              rcases hgop with hand | hor
              · simp [hand, GateOp.eval, hp]
              · simp [hor, GateOp.eval, hp]
            · exact ⟨p, q, rfl, hp, hq, hpq⟩
          · rcases hgop with hand | hor
            · exfalso; apply hnc0; intro x; rw [wires_gate_ofFn C x j _ hg, hand, hinp]; simp [GateOp.eval, hq]
            · exfalso; apply hncw p hp; intro x; rw [wires_gate_ofFn C x j _ hg, hor, hinp]; simp [GateOp.eval, hp, hq]
        · rcases hgop with hand | hor
          · exfalso; apply hnc0; intro x; rw [wires_gate_ofFn C x j _ hg, hand, hinp]; simp [GateOp.eval, hp]
          · by_cases hq : q < n + j
            · exfalso; apply hncw q hq; intro x; rw [wires_gate_ofFn C x j _ hg, hor, hinp]; simp [GateOp.eval, hp, hq]
            · exfalso; apply hnc0; intro x; rw [wires_gate_ofFn C x j _ hg, hor, hinp]; simp [GateOp.eval, hp, hq]
      · rw [hinp] at hglen; simp at hglen
    have hout_bounds : n ≤ C.output ∧ C.output < n + s := by
      refine ⟨?_, ?_⟩
      · by_contra hlt
        have hw : C.output < n := by omega
        let v : Fin n := ⟨C.output, hw⟩
        have hfv : C.eval (List.ofFn (fun t : Fin n => decide (t = v))) = false := by
          cases h : C.eval (List.ofFn (fun t : Fin n => decide (t = v))) with
          | false => rfl
          | true =>
            obtain ⟨a, b, hab, ha, hb⟩ := hfun.1 _ (tinyOne v) h
            simp only [decide_eq_true_eq] at ha hb
            subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
        unfold Circuit.eval at hfv
        rw [wires_input C _ C.output hw] at hfv
        simp [v] at hfv
      · by_contra hge
        obtain ⟨u0, v0, huv0⟩ := hedge
        have ht : C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true :=
          hfun.2 _ ⟨u0, v0, huv0, by simp, by simp⟩
        unfold Circuit.eval at ht
        rw [wires_oob C _ C.output (by omega)] at ht
        exact absurd ht (by decide)
    have hs_pos : 1 ≤ s := by omega
    have hgate_used : ∀ j < s, n + j ≠ C.output → ∃ j' : Fin C.gates.length, n + j ∈ (C.gates[j'.val]).inputs := by
      intro j hjs hne
      by_contra hnone
      have hjlen : j < C.gates.length := by omega
      obtain ⟨C', hm', hsz', heq'⟩ := elimSparse G C hmono hfun hedge j hjlen (fun _ => Sum.inl false) true
        (fun _ _ _ => trivial) (by intro h; cases h)
        (fun _ => ⟨hne.symm, fun j' g' hg' _ hmem => by
          have hj'lt : j' < C.gates.length := by
            by_contra hge; rw [List.getElem?_eq_none (by omega)] at hg'; cases hg'
          rw [List.getElem?_eq_getElem hj'lt, Option.some.injEq] at hg'
          subst hg'
          exact hnone ⟨⟨j', hj'lt⟩, hmem⟩⟩)
      exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
    have hout_last : C.output = n + s - 1 := by
      by_contra hne
      have hlast_ne : n + (s - 1) ≠ C.output := by omega
      obtain ⟨j', hj'mem⟩ := hgate_used (s - 1) (by omega) hlast_ne
      obtain ⟨p, q, hpq, hp, hq, _⟩ := hgate_shape j'.val j'.isLt
      rw [hpq] at hj'mem
      have hj's : j'.val < s := by have := j'.isLt; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'mem
      rcases hj'mem with h | h <;> omega
    let outdeg : ℕ → ℕ := fun w => ∑ j : Fin C.gates.length, (C.gates[j.val]).inputs.count w
    have hcount_mem : ∀ (j : Fin C.gates.length) (w : ℕ),
        (C.gates[j.val]).inputs.count w = if w ∈ (C.gates[j.val]).inputs then 1 else 0 := by
      intro j w
      obtain ⟨p, q, hpq, _, _, hne⟩ := hgate_shape j.val j.isLt
      rw [hpq]
      by_cases hwp : w = p
      · subst hwp; simp [hne]
      · by_cases hwq : w = q
        · subst hwq; simp [hwp, Ne.symm hwp]
        · simp [hwp, Ne.symm hwp, hwq, Ne.symm hwq]
    have houtdeg_card : ∀ w : ℕ, outdeg w = (Finset.univ.filter (fun j : Fin C.gates.length => w ∈ (C.gates[j.val]).inputs)).card := by
      intro w
      simp only [outdeg, hcount_mem, Finset.sum_boole, Nat.cast_id]
    have hinput_used : ∀ v : Fin n, 1 ≤ outdeg v.val := by
      intro v
      by_contra h0
      have hzero : outdeg v.val = 0 := by omega
      rw [houtdeg_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hzero
      have hno_read : ∀ j : Fin C.gates.length, v.val ∉ (C.gates[j.val]).inputs := fun j hj =>
        hzero j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      have hpos : 0 < (G.neighborFinset v).card := by have h : 3 ≤ (G.neighborFinset v).card := hdeg v; omega
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      have hvu : G.Adj v u := (SimpleGraph.mem_neighborFinset G v u).mp hu
      have hvu_ne : v ≠ u := G.ne_of_adj hvu
      let x : Fin n → Bool := fun t => decide (t = u)
      let x' : Fin n → Bool := Function.update x v true
      have hind : ∀ w : ℕ, w ≠ v.val → (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn x')).getD w false := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ihw =>
          intro hwv
          by_cases hw1 : w < n
          · rw [wires_input C x w hw1, wires_input C x' w hw1]
            have hne : (⟨w, hw1⟩ : Fin n) ≠ v := fun h => hwv (congrArg Fin.val h)
            exact (Function.update_of_ne hne true x).symm
          · by_cases hw2 : n + C.gates.length ≤ w
            · rw [wires_oob C x w hw2, wires_oob C x' w hw2]
            · have hjlt : w - n < C.gates.length := by omega
              set j := w - n
              have hwj : w = n + j := by omega
              have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
              rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C x' j _ hg]
              congr 1
              apply List.map_congr_left
              intro k hk
              have hkv : k ≠ v.val := fun h => hno_read ⟨j, hjlt⟩ (h ▸ hk)
              by_cases hklt : k < n + j
              · simp only [hklt, ↓reduceIte]; exact ihw k (by omega) hkv
              · simp only [hklt, ↓reduceIte]
      have heq := hind C.output (by omega)
      change C.eval (List.ofFn x) = C.eval (List.ofFn x') at heq
      have hf1 : C.eval (List.ofFn x) = false := by
        cases h : C.eval (List.ofFn x) with
        | false => rfl
        | true =>
          obtain ⟨a, b, hab, ha, hb⟩ := hfun.1 x (tinyOne u) h
          simp only [x, decide_eq_true_eq] at ha hb
          subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
      have hf2 : C.eval (List.ofFn x') = true := by
        apply hfun.2
        exact ⟨v, u, hvu, by simp [x'], by simp [x', x, hvu_ne.symm]⟩
      rw [hf1, hf2] at heq; exact absurd heq (by decide)
    have houtdeg_ge1 : ∀ w < n + s - 1, 1 ≤ outdeg w := by
      intro w hw
      by_cases hwn : w < n
      · exact hinput_used ⟨w, hwn⟩
      · have hj : w - n < s := by omega
        have hwj : w = n + (w - n) := by omega
        obtain ⟨j', hj'm⟩ := hgate_used (w - n) hj (by omega)
        rw [houtdeg_card]
        exact Finset.card_pos.mpr ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ j', hwj ▸ hj'm⟩⟩
    have houtdeg_sum : ∑ w ∈ Finset.range (n + s - 1), outdeg w = 2 * s := by
      have hswap : ∑ w ∈ Finset.range (n + s - 1), outdeg w =
          ∑ j : Fin C.gates.length, ∑ w ∈ Finset.range (n + s - 1), (C.gates[j.val]).inputs.count w :=
        Finset.sum_comm
      rw [hswap]
      have heach : ∀ j : Fin C.gates.length, ∑ w ∈ Finset.range (n + s - 1), (C.gates[j.val]).inputs.count w = 2 := by
        intro j
        obtain ⟨p, q, hpq, hp, hq, hne⟩ := hgate_shape j.val j.isLt
        have hj_s : j.val < s := by have := j.isLt; omega
        have hp_mem : p ∈ Finset.range (n + s - 1) := Finset.mem_range.mpr (by omega)
        have hq_mem : q ∈ Finset.range (n + s - 1) := Finset.mem_range.mpr (by omega)
        have hsub : ({p, q} : Finset ℕ) ⊆ Finset.range (n + s - 1) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        rw [← Finset.sum_subset hsub]
        · rw [Finset.sum_pair hne, hpq]
          simp [hne, Ne.symm hne]
        · intro w _ hw
          rw [hpq]
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
          simp [Ne.symm hw.1, Ne.symm hw.2]
      simp only [heach, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have hlen : C.gates.length = s := hCsize
      omega
    have hsurplus_sum : (∑ w ∈ Finset.range (n + s - 1), (outdeg w - 1)) + n = s + 1 := by
      have hadd : ∑ w ∈ Finset.range (n + s - 1), (outdeg w - 1) + ∑ _w ∈ Finset.range (n + s - 1), 1 =
          ∑ w ∈ Finset.range (n + s - 1), outdeg w := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w hw
        have := houtdeg_ge1 w (Finset.mem_range.mp hw)
        omega
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, houtdeg_sum] at hadd
      omega
    have hnext_uniq : ∀ w < n + s - 1, outdeg w = 1 →
        ∃! j : Fin C.gates.length, w ∈ (C.gates[j.val]).inputs := by
      intro w _ h1
      rw [houtdeg_card, Finset.card_eq_one] at h1
      obtain ⟨j, hj⟩ := h1
      have hjmem : j ∈ Finset.univ.filter (fun j : Fin C.gates.length => w ∈ (C.gates[j.val]).inputs) :=
        hj ▸ Finset.mem_singleton_self j
      refine ⟨j, (Finset.mem_filter.mp hjmem).2, ?_⟩
      intro j' hj'
      have hj'mem : j' ∈ ({j} : Finset (Fin C.gates.length)) :=
        hj ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j', hj'⟩
      exact Finset.mem_singleton.mp hj'mem
    let nextOf : (w : ℕ) → ℕ := fun w =>
      if h : w < n + s - 1 ∧ outdeg w = 1 then
        (hnext_uniq w h.1 h.2).choose.val
      else
        0
    have hnextOf_spec : ∀ w, w < n + s - 1 → outdeg w = 1 →
        ∃ hlt : nextOf w < C.gates.length, w ∈ (C.gates[nextOf w]'hlt).inputs ∧
          ∀ j : Fin C.gates.length, w ∈ (C.gates[j.val]).inputs → j.val = nextOf w := by
      intro w hw h1
      have hdef : nextOf w = (hnext_uniq w hw h1).choose.val := by simp [nextOf, hw, h1]
      have hsp := (hnext_uniq w hw h1).choose_spec
      refine ⟨by rw [hdef]; exact (hnext_uniq w hw h1).choose.isLt, ?_, ?_⟩
      · simpa [hdef] using hsp.1
      · intro j hj; rw [hdef]; exact congrArg Fin.val (hsp.2 j hj)
    have hnextOf_gt : ∀ w, w < n + s - 1 → outdeg w = 1 → w < n + nextOf w := by
      intro w hw h1
      obtain ⟨hlt, hmem, _⟩ := hnextOf_spec w hw h1
      obtain ⟨p, q, hpq, hp, hq, _⟩ := hgate_shape (nextOf w) hlt
      rw [hpq] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl <;> assumption
    let orEnd : ℕ → ℕ := orEndAux n s C outdeg nextOf hnextOf_gt
    let orChain : ℕ → Finset ℕ := orChainAux n s C outdeg nextOf hnextOf_gt
    have horEnd_ge : ∀ w, w ≤ orEnd w := by
      intro w
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orEnd]; rw [orEndAux]
        split_ifs with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            have hgt := hnextOf_gt w h.1 h.2
            have hrec := ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) rfl
            change w ≤ orEnd (n + nextOf w)
            omega
          | and => exact le_refl w
          | not => exact le_refl w
          | mod _ => exact le_refl w
          | maj => exact le_refl w
        · exact le_refl w
        · exact le_refl w
    have horEnd_lt : ∀ w, w < n + s → orEnd w < n + s := by
      intro w hw
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orEnd]; rw [orEndAux]
        split_ifs with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            have hgt := hnextOf_gt w h.1 h.2
            have hns : nextOf w < s := by omega
            exact ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) (by omega) rfl
          | and => exact hw
          | not => exact hw
          | mod _ => exact hw
          | maj => exact hw
        · exact hw
        · exact hw
    have horEnd_true : ∀ (w : ℕ) (x : Fin n → Bool), w < n + s → (C.wires (List.ofFn x)).getD w false = true →
        (C.wires (List.ofFn x)).getD (orEnd w) false = true := by
      intro w x hw hwt
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orEnd]; rw [orEndAux]
        split_ifs with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            have hgt := hnextOf_gt w h.1 h.2
            have hns : nextOf w < s := by omega
            obtain ⟨hlt', hmem, _⟩ := hnextOf_spec w h.1 h.2
            have hg : C.gates[nextOf w]? = some (C.gates[nextOf w]'hlt) := List.getElem?_eq_getElem hlt
            have hnext_t : (C.wires (List.ofFn x)).getD (n + nextOf w) false = true := by
              rw [wires_gate_ofFn C x (nextOf w) _ hg, hop]
              change ((C.gates[nextOf w]'hlt).inputs.map fun i => if i < n + nextOf w then (C.wires (List.ofFn x)).getD i false else false).any id = true
              rw [List.any_eq_true]
              exact ⟨_, List.mem_map_of_mem hmem, by simp only [id_eq, hgt, ↓reduceIte, hwt]⟩
            exact ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) (by omega) hnext_t rfl
          | and => exact hwt
          | not => exact hwt
          | mod _ => exact hwt
          | maj => exact hwt
        · exact hwt
        · exact hwt
    have horEnd_stop : ∀ w, w < n + s - 1 →
        (orEnd w = n + s - 1) ∨
        (orEnd w < n + s - 1 ∧ 2 ≤ outdeg (orEnd w)) ∨
        (orEnd w < n + s - 1 ∧ outdeg (orEnd w) = 1 ∧
          ∃ hlt : nextOf (orEnd w) < C.gates.length, (C.gates[nextOf (orEnd w)]'hlt).op = GateOp.and) := by
      intro w hw
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orEnd]; rw [orEndAux]
        by_cases h1 : w < n + s - 1 ∧ outdeg w = 1
        · obtain ⟨hlt, _, _⟩ := hnextOf_spec w h1.1 h1.2
          simp only [h1, ↓reduceDIte, hlt]
          have hgop : (C.gates[nextOf w]'hlt).op = GateOp.and ∨ (C.gates[nextOf w]'hlt).op = GateOp.or := by
            simpa using (hmono _ (List.getElem_mem hlt)).1
          rcases hgop with hand | hor
          · simp only [hand]
            exact Or.inr (Or.inr ⟨hw, h1.2, hlt, hand⟩)
          · simp only [hor]
            have hgt := hnextOf_gt w h1.1 h1.2
            have hns : nextOf w < s := by omega
            by_cases hlast : n + nextOf w = n + s - 1
            · left
              rw [hlast]
              rw [orEndAux]
              simp
            · exact ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) (by omega) rfl
        · simp only [h1, ↓reduceDIte]
          have hge1 := houtdeg_ge1 w hw
          have hne1 : outdeg w ≠ 1 := fun h => h1 ⟨hw, h⟩
          exact Or.inr (Or.inl ⟨hw, by omega⟩)
    have horChain_props : ∀ w, w < n + s →
        (w ∉ orChain w → w = orEnd w) ∧
        (∀ u ∈ orChain w, u < orEnd w ∧ u < n + s - 1 ∧ outdeg u = 1 ∧
          (n + nextOf u ∈ orChain w ∨ n + nextOf u = orEnd w)) := by
      intro w hw
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orChain, orEnd]; rw [orChainAux, orEndAux]
        split_ifs with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            have hgt := hnextOf_gt w h.1 h.2
            have hns : nextOf w < s := by omega
            obtain ⟨hrec1, hrec2⟩ := ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) (by omega) rfl
            refine ⟨fun hnot => absurd (Finset.mem_insert_self w _) hnot, ?_⟩
            intro u hu
            rcases Finset.mem_insert.mp hu with huw | hu'
            · subst huw
              have hge := horEnd_ge (n + nextOf u)
              refine ⟨by change u < orEnd (n + nextOf u); omega, h.1, h.2, ?_⟩
              by_cases hmem : n + nextOf u ∈ orChain (n + nextOf u)
              · exact Or.inl (Finset.mem_insert_of_mem hmem)
              · exact Or.inr (hrec1 hmem)
            · obtain ⟨h1, h2, h3, h4⟩ := hrec2 u hu'
              exact ⟨h1, h2, h3, h4.imp Finset.mem_insert_of_mem id⟩
          | and => simp
          | not => simp
          | mod _ => simp
          | maj => simp
        · simp
        · simp
    have horChain_in : ∀ w u, u ∈ orChain w → w ≤ u := by
      intro w u hu
      induction hrem : n + s - w using Nat.strong_induction_on generalizing w with
      | ind rem ihr =>
        dsimp only [orChain] at hu; rw [orChainAux] at hu
        split_ifs at hu with h hlt
        · cases hop : (C.gates[nextOf w]'hlt).op with
          | or =>
            rw [hop] at hu
            rcases Finset.mem_insert.mp hu with rfl | hu'
            · exact le_refl u
            · have hgt := hnextOf_gt w h.1 h.2
              have hrec := ihr (n + s - (n + nextOf w)) (by omega) (n + nextOf w) hu' rfl
              omega
          | and => rw [hop] at hu; simp at hu
          | not => rw [hop] at hu; simp at hu
          | mod _ => rw [hop] at hu; simp at hu
          | maj => rw [hop] at hu; simp at hu
        · simp at hu
        · simp at hu
    have horChain_self_or : ∀ w, w < n + s → w ∈ orChain w ∨ w = orEnd w := by
      intro w hw
      by_cases h : w ∈ orChain w
      · exact Or.inl h
      · exact Or.inr ((horChain_props w hw).1 h)
    have horEnd_sole_exit : ∀ (v : Fin n) (x y : Fin n → Bool),
        (∀ t : Fin n, t ≠ v → x t = y t) →
        (C.wires (List.ofFn x)).getD (orEnd v.val) false = (C.wires (List.ofFn y)).getD (orEnd v.val) false →
        ∀ u : ℕ, u < n + s → u ∉ orChain v.val →
          (C.wires (List.ofFn x)).getD u false = (C.wires (List.ofFn y)).getD u false := by
      intro v x y hxy hseq u hu
      induction u using Nat.strong_induction_on with
      | ind u ihu =>
        intro hunot
        by_cases hueq : u = orEnd v.val
        · rw [hueq]; exact hseq
        · by_cases hu1 : u < n
          · rw [wires_input C x u hu1, wires_input C y u hu1]
            have hne : (⟨u, hu1⟩ : Fin n) ≠ v := by
              intro h
              have huv : u = v.val := congrArg Fin.val h
              subst huv
              rcases horChain_self_or v.val (by omega) with hm | he
              · exact hunot hm
              · exact hueq he
            exact hxy ⟨u, hu1⟩ hne
          · have hjlt : u - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
            set j := u - n
            have huj : u = n + j := by omega
            have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
            rw [huj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
            congr 1
            apply List.map_congr_left
            intro k hk
            by_cases hklt : k < n + j
            · simp only [hklt, ↓reduceIte]
              apply ihu k (by omega) (by omega)
              intro hkch
              obtain ⟨_, hklt1, hk1, hknxt⟩ := (horChain_props v.val (by omega)).2 k hkch
              obtain ⟨_, _, huniq⟩ := hnextOf_spec k hklt1 hk1
              have hjeq : j = nextOf k := huniq ⟨j, hjlt⟩ hk
              rw [hjeq] at huj
              rcases hknxt with h1 | h2
              · exact hunot (huj ▸ h1)
              · exact hueq (huj ▸ h2)
            · simp only [hklt, ↓reduceIte]
    have hs_ne_out : ∀ v : Fin n, orEnd v.val < n + s - 1 := by
      intro v
      have hlt := horEnd_lt v.val (by omega)
      by_contra hge
      have heq : orEnd v.val = C.output := by omega
      have h1 : (C.wires (List.ofFn (fun t : Fin n => decide (t = v)))).getD (orEnd v.val) false = true := by
        apply horEnd_true v.val _ (by omega)
        rw [wires_input C _ v.val v.isLt]; simp
      rw [heq] at h1
      change C.eval (List.ofFn (fun t : Fin n => decide (t = v))) = true at h1
      obtain ⟨a, b, hab, ha, hb⟩ := hfun.1 _ (tinyOne v) h1
      simp only [decide_eq_true_eq] at ha hb
      subst ha; subst hb; exact G.loopless.irrefl _ hab
    have hs_zero_other : ∀ v q : Fin n, q ≠ v →
        (C.wires (List.ofFn (fun t : Fin n => decide (t = q)))).getD (orEnd v.val) false = false := by
      intro v q hqv
      by_contra hne
      have htrue : (C.wires (List.ofFn (fun t : Fin n => decide (t = q)))).getD (orEnd v.val) false = true := by
        cases h : (C.wires (List.ofFn (fun t : Fin n => decide (t = q)))).getD (orEnd v.val) false
        · exact absurd h hne
        · rfl
      have hout_not_ch : C.output ∉ orChain v.val := by
        intro hmem
        have := (horChain_props v.val (by omega)).2 C.output hmem
        omega
      by_cases hadj : G.Adj v q
      · let x : Fin n → Bool := fun t => decide (t = q)
        let y : Fin n → Bool := Function.update x v true
        have hy_true : (C.wires (List.ofFn y)).getD (orEnd v.val) false = true := by
          apply horEnd_true v.val y (by omega)
          rw [wires_input C y v.val v.isLt]
          have : (⟨v.val, v.isLt⟩ : Fin n) = v := Fin.ext rfl
          rw [this]; simp [y]
        have heq := horEnd_sole_exit v x y (fun t ht => (Function.update_of_ne ht true x).symm)
          (htrue.trans hy_true.symm) C.output (by omega) hout_not_ch
        change C.eval (List.ofFn x) = C.eval (List.ofFn y) at heq
        have hf0 : C.eval (List.ofFn x) = false := by
          cases h : C.eval (List.ofFn x) with
          | false => rfl
          | true =>
            obtain ⟨a, b, hab, ha, hb⟩ := hfun.1 x (tinyOne q) h
            simp only [x, decide_eq_true_eq] at ha hb
            subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
        have hf1 : C.eval (List.ofFn y) = true := by
          apply hfun.2
          exact ⟨v, q, hadj, by simp [y], by simp [y, x, hqv]⟩
        rw [hf0, hf1] at heq; exact absurd heq (by decide)
      · obtain ⟨u, hvu, hnw⟩ := hdistinct_nbrs v q hqv.symm
        have huv : u ≠ v := (G.ne_of_adj hvu).symm
        let x : Fin n → Bool := fun t => decide (t = q ∨ t = u)
        let y : Fin n → Bool := Function.update x v true
        have hx_true : (C.wires (List.ofFn x)).getD (orEnd v.val) false = true :=
          wires_mono C hmono (fun t => decide (t = q)) x (fun t ht => by simp only [x, decide_eq_true_eq] at ht ⊢; exact Or.inl ht) (orEnd v.val) htrue
        have hy_true : (C.wires (List.ofFn y)).getD (orEnd v.val) false = true := by
          apply horEnd_true v.val y (by omega)
          rw [wires_input C y v.val v.isLt]
          have : (⟨v.val, v.isLt⟩ : Fin n) = v := Fin.ext rfl
          rw [this]; simp [y]
        have heq := horEnd_sole_exit v x y (fun t ht => (Function.update_of_ne ht true x).symm)
          (hx_true.trans hy_true.symm) C.output (by omega) hout_not_ch
        change C.eval (List.ofFn x) = C.eval (List.ofFn y) at heq
        have hf0 : C.eval (List.ofFn x) = false := by
          cases h : C.eval (List.ofFn x) with
          | false => rfl
          | true =>
            obtain ⟨a, b, hab, ha, hb⟩ := hfun.1 x (tinyTwo q u) h
            simp only [x, decide_eq_true_eq] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact absurd hab (G.loopless.irrefl _)
            · exact absurd hab hnw
            · exact absurd hab.symm hnw
            · exact absurd hab (G.loopless.irrefl _)
        have hf1 : C.eval (List.ofFn y) = true := by
          apply hfun.2
          exact ⟨v, u, hvu, by simp [y], by simp [y, x, huv]⟩
        rw [hf0, hf1] at heq; exact absurd heq (by decide)
    have hs_inj : Function.Injective (fun v : Fin n => orEnd v.val) := by
      intro v w hvw
      by_contra hne
      have h1 : (C.wires (List.ofFn (fun t : Fin n => decide (t = v)))).getD (orEnd v.val) false = true := by
        apply horEnd_true v.val _ (by omega)
        rw [wires_input C _ v.val v.isLt]; simp
      have h2 := hs_zero_other w v hne
      dsimp only at hvw
      rw [hvw, h2] at h1
      exact absurd h1 (by decide)
    set Tbranch : Finset (Fin n) := Finset.univ.filter (fun v : Fin n => 2 ≤ outdeg (orEnd v.val))
    have hand_exit : ∀ v : Fin n, v ∉ Tbranch →
        outdeg (orEnd v.val) = 1 ∧
        ∃ hlt : nextOf (orEnd v.val) < C.gates.length, (C.gates[nextOf (orEnd v.val)]'hlt).op = GateOp.and := by
      intro v hv
      have hnot2 : ¬ 2 ≤ outdeg (orEnd v.val) := fun h => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
      have hlt := hs_ne_out v
      rcases horEnd_stop v.val (by omega) with h1 | h2 | h3
      · omega
      · omega
      · exact ⟨h3.2.1, h3.2.2⟩
    have hand_sole_exit : ∀ (v : Fin n) (hv : v ∉ Tbranch) (x y : Fin n → Bool),
        (∀ t : Fin n, t ≠ v → x t = y t) →
        (C.wires (List.ofFn x)).getD (n + nextOf (orEnd v.val)) false =
        (C.wires (List.ofFn y)).getD (n + nextOf (orEnd v.val)) false →
        ∀ u : ℕ, u < n + s → u ∉ orChain v.val → u ≠ orEnd v.val →
          (C.wires (List.ofFn x)).getD u false = (C.wires (List.ofFn y)).getD u false := by
      intro v hv x y hxy haeq u hu
      obtain ⟨h1, hlt_a, _⟩ := hand_exit v hv
      have hlt_s := hs_ne_out v
      induction u using Nat.strong_induction_on with
      | ind u ihu =>
        intro hunot hune
        by_cases hueq : u = n + nextOf (orEnd v.val)
        · rw [hueq]; exact haeq
        · by_cases hu1 : u < n
          · rw [wires_input C x u hu1, wires_input C y u hu1]
            have hne : (⟨u, hu1⟩ : Fin n) ≠ v := by
              intro h
              have huv : u = v.val := congrArg Fin.val h
              subst huv
              rcases horChain_self_or v.val (by omega) with hm | he
              · exact hunot hm
              · exact hune he
            exact hxy ⟨u, hu1⟩ hne
          · have hjlt : u - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
            set j := u - n
            have huj : u = n + j := by omega
            have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
            rw [huj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
            congr 1
            apply List.map_congr_left
            intro k hk
            by_cases hklt : k < n + j
            · simp only [hklt, ↓reduceIte]
              apply ihu k (by omega) (by omega)
              · intro hkch
                obtain ⟨_, hklt1, hk1, hknxt⟩ := (horChain_props v.val (by omega)).2 k hkch
                obtain ⟨_, _, huniq⟩ := hnextOf_spec k hklt1 hk1
                have hjeq : j = nextOf k := huniq ⟨j, hjlt⟩ hk
                rw [hjeq] at huj
                rcases hknxt with h1' | h2'
                · exact hunot (huj ▸ h1')
                · exact hune (huj ▸ h2')
              · intro hks
                subst hks
                obtain ⟨_, _, huniq⟩ := hnextOf_spec (orEnd v.val) hlt_s h1
                have hjeq : j = nextOf (orEnd v.val) := huniq ⟨j, hjlt⟩ hk
                exact hueq (by rw [huj, hjeq])
            · simp only [hklt, ↓reduceIte]
    have hother_input_and : ∀ (v : Fin n) (hv : v ∉ Tbranch),
        let j := nextOf (orEnd v.val)
        ∃ (hlt : j < C.gates.length) (z : ℕ),
          ((C.gates[j]'hlt).inputs = [orEnd v.val, z] ∨ (C.gates[j]'hlt).inputs = [z, orEnd v.val]) ∧
          z < n + j ∧ z ≠ orEnd v.val ∧ z ∉ orChain v.val := by
      intro v hv
      obtain ⟨h1, hlt, hand⟩ := hand_exit v hv
      obtain ⟨_, hmem, _⟩ := hnextOf_spec (orEnd v.val) (hs_ne_out v) h1
      obtain ⟨p, q, hpq, hp, hq, hne⟩ := hgate_shape (nextOf (orEnd v.val)) hlt
      rw [hpq] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      have hnot_ch : ∀ z, z ∈ (C.gates[nextOf (orEnd v.val)]'hlt).inputs → z ∉ orChain v.val := by
        intro z hz hch
        obtain ⟨_, zlt1, z1, _⟩ := (horChain_props v.val (by omega)).2 z hch
        obtain ⟨_, _, huniq⟩ := hnextOf_spec z zlt1 z1
        have hjeq : nextOf (orEnd v.val) = nextOf z := huniq ⟨nextOf (orEnd v.val), hlt⟩ hz

        have : (C.gates[nextOf z]'(hjeq ▸ hlt)).op = GateOp.or := by
          have hzprops : ∀ w0, w0 < n + s → ∀ u ∈ orChain w0,
              ∃ hlt' : nextOf u < C.gates.length, (C.gates[nextOf u]'hlt').op = GateOp.or := by
            intro w0 hw0
            induction hrem : n + s - w0 using Nat.strong_induction_on generalizing w0 with
            | ind rem ihr =>
              intro u hu
              dsimp only [orChain] at hu; rw [orChainAux] at hu
              split_ifs at hu with h' hlt'
              · cases hop' : (C.gates[nextOf w0]'hlt').op with
                | or =>
                  rw [hop'] at hu
                  rcases Finset.mem_insert.mp hu with rfl | hu'
                  · exact ⟨hlt', hop'⟩
                  · have hgt := hnextOf_gt w0 h'.1 h'.2
                    have hns : nextOf w0 < s := by omega
                    exact ihr (n + s - (n + nextOf w0)) (by omega) (n + nextOf w0) (by omega) rfl u hu'
                | and => rw [hop'] at hu; simp at hu
                | not => rw [hop'] at hu; simp at hu
                | mod _ => rw [hop'] at hu; simp at hu
                | maj => rw [hop'] at hu; simp at hu
              · simp at hu
              · simp at hu
          obtain ⟨hlt', hor'⟩ := hzprops v.val (by omega) z hch
          exact hor'
        have hbad : (C.gates[nextOf (orEnd v.val)]'hlt).op = GateOp.or := by
          simpa [hjeq] using this
        rw [hand] at hbad; cases hbad
      rcases hmem with rfl | rfl
      · exact ⟨hlt, q, Or.inl hpq, hq, hne.symm, hnot_ch q (by rw [hpq]; simp)⟩
      · exact ⟨hlt, p, Or.inr hpq, hp, hne, hnot_ch p (by rw [hpq]; simp)⟩
    have hand_z_true : ∀ (v : Fin n) (hv : v ∉ Tbranch) (u : Fin n), G.Adj v u →
        ∀ (hlt : nextOf (orEnd v.val) < C.gates.length) (z : ℕ),
          ((C.gates[nextOf (orEnd v.val)]'hlt).inputs = [orEnd v.val, z] ∨
           (C.gates[nextOf (orEnd v.val)]'hlt).inputs = [z, orEnd v.val]) →
          z < n + nextOf (orEnd v.val) → z ≠ orEnd v.val → z ∉ orChain v.val →
          (C.wires (List.ofFn (fun t : Fin n => decide (t = u)))).getD z false = true := by
      intro v hv u hvu hlt z hord hzlt hzne hzch
      obtain ⟨h1, _, hand⟩ := hand_exit v hv
      have hvu_ne : v ≠ u := G.ne_of_adj hvu
      let x : Fin n → Bool := fun t => decide (t = u)
      let y : Fin n → Bool := Function.update x v true
      have hzeq : (C.wires (List.ofFn x)).getD z false = (C.wires (List.ofFn y)).getD z false := by
        have hrec : ∀ w < n + nextOf (orEnd v.val), w ∉ orChain v.val → w ≠ orEnd v.val →
            (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ihw =>
            intro hwlt hwch hwne
            by_cases hw1 : w < n
            · rw [wires_input C x w hw1, wires_input C y w hw1]
              have hne : (⟨w, hw1⟩ : Fin n) ≠ v := by
                intro h
                have hwv : w = v.val := congrArg Fin.val h
                subst hwv
                rcases horChain_self_or v.val (by omega) with hm | he
                · exact hwch hm
                · exact hwne he
              exact (Function.update_of_ne hne true x).symm
            · have hjlt : w - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
              set j := w - n
              have hwj : w = n + j := by omega
              have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
              rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
              congr 1
              apply List.map_congr_left
              intro k hk
              by_cases hklt : k < n + j
              · simp only [hklt, ↓reduceIte]
                apply ihw k (by omega) (by omega)
                · intro hkch
                  obtain ⟨_, hklt1, hk1, hknxt⟩ := (horChain_props v.val (by omega)).2 k hkch
                  obtain ⟨_, _, huniq⟩ := hnextOf_spec k hklt1 hk1
                  have hjeq : j = nextOf k := huniq ⟨j, hjlt⟩ hk
                  rw [hjeq] at hwj
                  rcases hknxt with h1' | h2'
                  · exact hwch (hwj ▸ h1')
                  · exact hwne (hwj ▸ h2')
                · intro hks
                  subst hks
                  obtain ⟨_, _, huniq⟩ := hnextOf_spec (orEnd v.val) (hs_ne_out v) h1
                  have hjeq : j = nextOf (orEnd v.val) := huniq ⟨j, hjlt⟩ hk
                  omega
              · simp only [hklt, ↓reduceIte]
        exact hrec z hzlt hzch hzne
      by_contra hzf
      have hz0 : (C.wires (List.ofFn x)).getD z false = false := by
        cases h : (C.wires (List.ofFn x)).getD z false
        · rfl
        · exact absurd h hzf
      have hz0' : (C.wires (List.ofFn y)).getD z false = false := hzeq.symm.trans hz0
      have hg : C.gates[nextOf (orEnd v.val)]? = some (C.gates[nextOf (orEnd v.val)]'hlt) := List.getElem?_eq_getElem hlt
      have ha0 : (C.wires (List.ofFn x)).getD (n + nextOf (orEnd v.val)) false = false := by
        rw [wires_gate_ofFn C x _ _ hg, hand]
        rcases hord with h | h <;> rw [h] <;> simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hzlt, ↓reduceIte, hz0, Bool.false_and, Bool.and_false]
      have ha0' : (C.wires (List.ofFn y)).getD (n + nextOf (orEnd v.val)) false = false := by
        rw [wires_gate_ofFn C y _ _ hg, hand]
        rcases hord with h | h <;> rw [h] <;> simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hzlt, ↓reduceIte, hz0', Bool.false_and, Bool.and_false]
      have hout_ch : C.output ∉ orChain v.val := fun hm => by
        have := (horChain_props v.val (by omega)).2 C.output hm; omega
      have hout_ne : C.output ≠ orEnd v.val := by have := hs_ne_out v; omega
      have heval := hand_sole_exit v hv x y (fun t ht => (Function.update_of_ne ht true x).symm)
        (ha0.trans ha0'.symm) C.output (by omega) hout_ch hout_ne
      change C.eval (List.ofFn x) = C.eval (List.ofFn y) at heval
      have hf0 : C.eval (List.ofFn x) = false := by
        cases h : C.eval (List.ofFn x) with
        | false => rfl
        | true =>
          obtain ⟨a, b, hab, ha, hb⟩ := hfun.1 x (tinyOne u) h
          simp only [x, decide_eq_true_eq] at ha hb
          subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
      have hf1 : C.eval (List.ofFn y) = true := by
        apply hfun.2
        exact ⟨v, u, hvu, by simp [y], by simp [y, x, hvu_ne.symm]⟩
      rw [hf0, hf1] at heval; exact absurd heval (by decide)
    have hvc : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G Tbranch := by
      intro v w hvw
      by_contra hneither
      have hv : v ∉ Tbranch := fun h => hneither (Or.inl h)
      have hw : w ∉ Tbranch := fun h => hneither (Or.inr h)
      have hvw_ne : v ≠ w := G.ne_of_adj hvw
      have hstep_le : ∀ (a b : Fin n) (ha : a ∉ Tbranch) (hb : b ∉ Tbranch),
          G.Adj a b → nextOf (orEnd a.val) ≤ nextOf (orEnd b.val) → False := by
        intro a b ha hb hab hle
        have hab_ne : a ≠ b := G.ne_of_adj hab
        obtain ⟨hlta, za, horda, hzalt, hzane, hzach⟩ := hother_input_and a ha
        obtain ⟨h1a, _, handa⟩ := hand_exit a ha
        obtain ⟨h1b, hltb, handb⟩ := hand_exit b hb
        by_cases heq_gate : nextOf (orEnd a.val) = nextOf (orEnd b.val)
        · obtain ⟨hltb', hmemb, _⟩ := hnextOf_spec (orEnd b.val) (hs_ne_out b) h1b
          have hmemb' : orEnd b.val ∈ (C.gates[nextOf (orEnd a.val)]'hlta).inputs := by
            simpa only [heq_gate] using hmemb
          have hza_eq : za = orEnd b.val := by
            rcases horda with h | h <;> rw [h] at hmemb' <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hmemb'
            · rcases hmemb' with h' | h'
              · exact absurd (hs_inj h'.symm) hab_ne
              · exact h'.symm
            · rcases hmemb' with h' | h'
              · exact h'.symm
              · exact absurd (hs_inj h'.symm) hab_ne
          have hpos : 1 < (G.neighborFinset a).card := by have h : 3 ≤ (G.neighborFinset a).card := hdeg a; omega
          obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp hpos
          obtain ⟨u, hua, hub⟩ : ∃ u : Fin n, G.Adj a u ∧ u ≠ b := by
            by_cases h1 : u1 = b
            · exact ⟨u2, (SimpleGraph.mem_neighborFinset G a u2).mp hu2, fun h => hu12 (h1.trans h.symm)⟩
            · exact ⟨u1, (SimpleGraph.mem_neighborFinset G a u1).mp hu1, h1⟩
          have hzt := hand_z_true a ha u hua hlta za horda hzalt hzane hzach
          rw [hza_eq] at hzt
          have hz0 := hs_zero_other b u hub
          rw [hz0] at hzt; exact absurd hzt (by decide)
        · have hlt_ab : nextOf (orEnd a.val) < nextOf (orEnd b.val) := by omega
          have hzt := hand_z_true a ha b hab hlta za horda hzalt hzane hzach
          have hza_not_sb : za ≠ orEnd b.val := by
            intro h
            subst h
            obtain ⟨_, _, huniq⟩ := hnextOf_spec (orEnd b.val) (hs_ne_out b) h1b
            have hmemza : orEnd b.val ∈ (C.gates[nextOf (orEnd a.val)]'hlta).inputs := by
              rcases horda with h1 | h1 <;> rw [h1] <;> simp
            exact heq_gate (huniq ⟨nextOf (orEnd a.val), hlta⟩ hmemza)
          have hza_not_chb : za ∉ orChain b.val := by
            intro hch
            obtain ⟨_, zlt1, z1, hznxt⟩ := (horChain_props b.val (by omega)).2 za hch
            obtain ⟨_, _, huniq⟩ := hnextOf_spec za zlt1 z1
            have hmemza : za ∈ (C.gates[nextOf (orEnd a.val)]'hlta).inputs := by
              rcases horda with h1 | h1 <;> rw [h1] <;> simp
            have heq : nextOf (orEnd a.val) = nextOf za := huniq ⟨nextOf (orEnd a.val), hlta⟩ hmemza
            have hgt_b := horChain_props b.val (by omega)
            have hlt_sb : n + nextOf za ≤ orEnd b.val := by
              rcases hznxt with h1' | h2'
              · exact le_of_lt (hgt_b.2 _ h1').1
              · exact le_of_eq h2'
            have hlt_a' : orEnd a.val < n + nextOf (orEnd a.val) := hnextOf_gt _ (hs_ne_out a) h1a
            have hlt_b' : orEnd b.val < n + nextOf (orEnd b.val) := hnextOf_gt _ (hs_ne_out b) h1b
            have hba_lt : nextOf (orEnd a.val) < C.gates.length := hlta
            have hnot_and : (C.gates[nextOf za]'(heq ▸ hlta)).op = GateOp.or := by
              have hzprops : ∀ w0, w0 < n + s → ∀ u ∈ orChain w0,
                  ∃ hlt' : nextOf u < C.gates.length, (C.gates[nextOf u]'hlt').op = GateOp.or := by
                intro w0 hw0
                induction hrem : n + s - w0 using Nat.strong_induction_on generalizing w0 with
                | ind rem ihr =>
                  intro u hu
                  dsimp only [orChain] at hu; rw [orChainAux] at hu
                  split_ifs at hu with h' hlt'
                  · cases hop' : (C.gates[nextOf w0]'hlt').op with
                    | or =>
                      rw [hop'] at hu
                      rcases Finset.mem_insert.mp hu with rfl | hu'
                      · exact ⟨hlt', hop'⟩
                      · have hgt := hnextOf_gt w0 h'.1 h'.2
                        have hns : nextOf w0 < s := by omega
                        exact ihr (n + s - (n + nextOf w0)) (by omega) (n + nextOf w0) (by omega) rfl u hu'
                    | and => rw [hop'] at hu; simp at hu
                    | not => rw [hop'] at hu; simp at hu
                    | mod _ => rw [hop'] at hu; simp at hu
                    | maj => rw [hop'] at hu; simp at hu
                  · simp at hu
                  · simp at hu
              obtain ⟨_, hor'⟩ := hzprops b.val (by omega) za hch
              exact hor'
            have : (C.gates[nextOf (orEnd a.val)]'hlta).op = GateOp.or := by simpa [heq] using hnot_and
            rw [handa] at this; cases this
          have hza_indep_b : ∀ u < n + nextOf (orEnd b.val), u ∉ orChain b.val → u ≠ orEnd b.val →
              (C.wires (List.ofFn (fun _ : Fin n => false))).getD u false =
              (C.wires (List.ofFn (fun t : Fin n => decide (t = b)))).getD u false := by
            intro u
            induction u using Nat.strong_induction_on with
            | ind u ihu =>
              intro hult huch hune
              by_cases hu1 : u < n
              · rw [wires_input C _ u hu1, wires_input C _ u hu1]
                have hne : (⟨u, hu1⟩ : Fin n) ≠ b := by
                  intro h
                  have hub : u = b.val := congrArg Fin.val h
                  subst hub
                  rcases horChain_self_or b.val (by omega) with hm | he
                  · exact huch hm
                  · exact hune he
                simp [hne]
              · have hjlt : u - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
                set j := u - n
                have huj : u = n + j := by omega
                have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
                rw [huj, wires_gate_ofFn C _ j _ hg, wires_gate_ofFn C _ j _ hg]
                congr 1
                apply List.map_congr_left
                intro k hk
                by_cases hklt : k < n + j
                · simp only [hklt, ↓reduceIte]
                  apply ihu k (by omega) (by omega)
                  · intro hkch
                    obtain ⟨_, hklt1, hk1, hknxt⟩ := (horChain_props b.val (by omega)).2 k hkch
                    obtain ⟨_, _, huniq⟩ := hnextOf_spec k hklt1 hk1
                    have hjeq : j = nextOf k := huniq ⟨j, hjlt⟩ hk
                    rw [hjeq] at huj
                    rcases hknxt with h1' | h2'
                    · exact huch (huj ▸ h1')
                    · exact hune (huj ▸ h2')
                  · intro hks
                    subst hks
                    obtain ⟨_, _, huniq⟩ := hnextOf_spec (orEnd b.val) (hs_ne_out b) h1b
                    have hjeq : j = nextOf (orEnd b.val) := huniq ⟨j, hjlt⟩ hk
                    omega
                · simp only [hklt, ↓reduceIte]
          have hza0 : (C.wires (List.ofFn (fun _ : Fin n => false))).getD za false = true :=
            (hza_indep_b za (by omega) hza_not_chb hza_not_sb).trans hzt
          have hza_all : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD za false = true := fun x =>
            wires_mono C hmono (fun _ => false) x (fun _ h => absurd h (by decide)) za hza0
          have ha_copy : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + nextOf (orEnd a.val)) false =
              (C.wires (List.ofFn x)).getD (orEnd a.val) false := by
            intro x
            have hg : C.gates[nextOf (orEnd a.val)]? = some (C.gates[nextOf (orEnd a.val)]'hlta) := List.getElem?_eq_getElem hlta
            have hs_lt : orEnd a.val < n + nextOf (orEnd a.val) := hnextOf_gt _ (hs_ne_out a) h1a
            rw [wires_gate_ofFn C x _ _ hg, handa]
            rcases horda with h1 | h1 <;> rw [h1] <;> simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hs_lt, hzalt, ↓reduceIte, hza_all x, Bool.true_and, Bool.and_true]
          have hja_s : nextOf (orEnd a.val) < s := by omega
          exact (hno_const_or_copy (nextOf (orEnd a.val)) hja_s).2.2 (orEnd a.val) (hnextOf_gt _ (hs_ne_out a) h1a) ha_copy
      rcases le_total (nextOf (orEnd v.val)) (nextOf (orEnd w.val)) with hle | hle
      · exact hstep_le v w hv hw hvw hle
      · exact hstep_le w v hw hv hvw.symm hle
    set Simg : Finset ℕ := Tbranch.image (fun v : Fin n => orEnd v.val)
    have hSimg_sub : Simg ⊆ Finset.range (n + s - 1) := by
      intro w hw
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_range.mpr (hs_ne_out v)
    have hSimg_card : Simg.card = Tbranch.card := Finset.card_image_of_injective Tbranch hs_inj
    have hsum_ge_T : Tbranch.card ≤ ∑ w ∈ Simg, (outdeg w - 1) := by
      have hle1 : ∀ w ∈ Simg, 1 ≤ outdeg w - 1 := by
        intro w hw
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        have := (Finset.mem_filter.mp hv).2
        omega
      have := Finset.sum_le_sum hle1
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hSimg_card] at this
      exact this
    have hsum_le_all : ∑ w ∈ Simg, (outdeg w - 1) ≤ ∑ w ∈ Finset.range (n + s - 1), (outdeg w - 1) :=
      Finset.sum_le_sum_of_subset hSimg_sub
    let extra := s+1-(n+Tbranch.card)
    have paid : n+Tbranch.card+extra=s+1 := by dsimp [extra]; omega
    set I : Finset (Fin n) := Finset.univ \ Tbranch
    have hI_card : I.card = n - Tbranch.card := by
      have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Tbranch)
      change I.card + Tbranch.card = (Finset.univ : Finset (Fin n)).card at this
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    let fee (w : ℕ) := if w∈Simg then 1 else 0
    let spare (w : ℕ) := outdeg w-1-fee w
    have parts (w : ℕ) : outdeg w-1=fee w+spare w := by
      unfold spare fee
      by_cases h : w∈Simg
      · obtain ⟨u,hu,e⟩ := Finset.mem_image.mp h
        have ge := (Finset.mem_filter.mp hu).2
        rw [e] at ge
        simp only [h,ite_true]
        omega
      · simp [h]
    have fees : (∑ w ∈ Finset.range (n+s-1), fee w) = Tbranch.card := by
      rw [←Finset.sum_subset hSimg_sub (fun w _ h => by simp [fee,h])]
      calc
        _ = ∑ _w ∈ Simg,1 := Finset.sum_congr rfl (fun w h => by simp [fee,h])
        _ = _ := by simp [hSimg_card]
    have fullSpare : (∑ w ∈ Finset.range (n+s-1),spare w)=extra := by
      have h := hsurplus_sum
      simp only [parts,Finset.sum_add_distrib,fees] at h
      omega
    let posW (v : Fin n) := (Finset.range (n+s)).filter
      (fun w => (C.wires (List.ofFn (fun x : Fin n => decide (x=v)))).getD w false = true)
    let bound (v : Fin n) := Finset.univ.filter (fun j : Fin C.gates.length =>
      n+j.val ∉ posW v ∧ ∃ i ∈ (C.gates[j.val]).inputs, i∈posW v)
    let follow (u : Fin n) := nextOf (orEnd u.val)
    have details : ∀ v∈Tbranch,
        (G.neighborFinset v ∩ I).card ≤ (bound v).card ∧
        (bound v).card ≤ (∑ w ∈ posW v, spare w)+2 ∧
        (posW v ⊆ Finset.range (n+s-1)) ∧
        ((G.neighborFinset v ∩ I).image follow ⊆ (bound v).image Fin.val) ∧
        (∀ u∈G.neighborFinset v ∩ I, ∀ u'∈I, follow u=follow u' → u=u') := by
      intro v hv
      let ev : Fin n → Bool := fun t => decide (t = v)
      set Tv : Finset ℕ := (Finset.range (n + s)).filter (fun w => (C.wires (List.ofFn ev)).getD w false = true)
      have hv_in_Tv : v.val ∈ Tv := by
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        rw [wires_input C ev v.val v.isLt]; simp [ev]
      have hsv_in_Tv : orEnd v.val ∈ Tv := by
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨by have := hs_ne_out v; omega, ?_⟩
        apply horEnd_true v.val ev (by omega)
        rw [wires_input C ev v.val v.isLt]; simp [ev]
      have hout_not_Tv : n + s - 1 ∉ Tv := by
        intro hm
        have ht := (Finset.mem_filter.mp hm).2
        rw [← hout_last] at ht
        change C.eval (List.ofFn ev) = true at ht
        obtain ⟨a, b, hab, ha, hb⟩ := hfun.1 ev (tinyOne v) ht
        simp only [ev, decide_eq_true_eq] at ha hb
        subst ha; subst hb; exact G.loopless.irrefl _ hab
      have hTv_lt : ∀ w ∈ Tv, w < n + s - 1 := by
        intro w hw
        have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
        have hne : w ≠ n + s - 1 := fun h => hout_not_Tv (h ▸ hw)
        omega
      let other := Simg.erase (orEnd v.val)
      have member : orEnd v.val ∈ Simg := Finset.mem_image.mpr ⟨v,hv,rfl⟩
      have cardOther : other.card+1=Tbranch.card :=
        (Finset.card_erase_add_one member).trans hSimg_card
      have disjoint : Disjoint Tv other := by
        apply Finset.disjoint_left.mpr
        intro w hw hw'
        obtain ⟨ne,ins⟩ := Finset.mem_erase.mp hw'
        obtain ⟨v',_,eq⟩ := Finset.mem_image.mp ins
        have diff : v' ≠ v := fun h => ne (eq.symm.trans (congrArg (fun x : Fin n => orEnd x.val) h))
        have zero := hs_zero_other v' v diff.symm
        have ht := (Finset.mem_filter.mp hw).2
        rw [←eq,zero] at ht
        contradiction
      have allin : Tv ∪ other ⊆ Finset.range (n+s-1) := by
        intro w hw
        rcases Finset.mem_union.mp hw with hvv|ho
        · exact Finset.mem_range.mpr (hTv_lt w hvv)
        · exact hSimg_sub (Finset.mem_of_mem_erase ho)
      have otherPay : other.card ≤ ∑ w ∈ other, (outdeg w-1) := by
        have h (w : ℕ) (hw : w ∈ other) : 1 ≤ outdeg w-1 := by
          obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hw)
          have := (Finset.mem_filter.mp hu).2
          omega
        simpa using Finset.sum_le_sum h
      have joined := Finset.sum_le_sum_of_subset (f:=fun w => outdeg w-1) allin
      rw [Finset.sum_union disjoint] at joined
      have totalTv : (∑ w ∈ Tv, (outdeg w-1))+Tv.card = ∑ w ∈ Tv,outdeg w := by
        calc
          _ = (∑ w ∈ Tv,(outdeg w-1))+∑ _w ∈ Tv,1 := by simp
          _ = _ := by
            rw [←Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro w hw
            have := houtdeg_ge1 w (hTv_lt w hw)
            omega
      have feeTv : (∑ w ∈ Tv,fee w)=1 := by
        rw [Finset.sum_eq_single (orEnd v.val)]
        · simp [fee,member]
        · intro w hw ne
          have nS : w∉Simg := by
            intro hin
            exact Finset.disjoint_left.mp disjoint hw (Finset.mem_erase.mpr ⟨ne,hin⟩)
          simp [fee,nS]
        · exact fun no => (no hsv_in_Tv).elim
      have hsum_Tv_outdeg : (∑ w ∈ Tv, outdeg w) = Tv.card+1+(∑ w ∈ Tv, spare w) := by
        simp only [parts,Finset.sum_add_distrib,feeTv] at totalTv
        omega
      let Ev : Finset (Fin C.gates.length) :=
        Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∉ Tv ∧ ∃ i ∈ (C.gates[j.val]).inputs, i ∈ Tv)
      have hmem_Ev : ∀ j : Fin C.gates.length, j ∈ Ev ↔ n + j.val ∉ Tv ∧ ∃ i ∈ (C.gates[j.val]'j.isLt).inputs, i ∈ Tv := fun j => by
        simp only [Ev, Finset.mem_filter, Finset.mem_univ, true_and]
      have hEv_le2 : Ev.card ≤ (∑ w ∈ Tv,spare w)+2 := by
        let din : ℕ → ℕ := fun w => (Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv ∧ w ∈ (C.gates[j.val]).inputs)).card
        let dout : ℕ → ℕ := fun w => (Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∉ Tv ∧ w ∈ (C.gates[j.val]).inputs)).card
        have hsplit : ∀ w, din w + dout w = outdeg w := by
          intro w
          rw [houtdeg_card]
          have := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun j : Fin C.gates.length => w ∈ (C.gates[j.val]).inputs))
            (p := fun j : Fin C.gates.length => n + j.val ∈ Tv)
          simpa only [din, dout, Finset.filter_filter, and_comm] using this
        have hdin_sum : Tv.card - 1 ≤ ∑ w ∈ Tv, din w := by
          have hswap : ∑ w ∈ Tv, din w =
              ∑ j ∈ Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv),
                (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card := by
            simp only [din, Finset.card_eq_sum_ones]
            have h1 : ∀ j : Fin C.gates.length,
                (∑ w ∈ Tv, if n + j.val ∈ Tv ∧ w ∈ (C.gates[j.val]).inputs then 1 else 0) =
                if n + j.val ∈ Tv then (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card else 0 := by
              intro j
              by_cases hj : n + j.val ∈ Tv
              · simp [hj, Finset.sum_boole]
              · simp [hj]
            trans ∑ j : Fin C.gates.length, ∑ w ∈ Tv, if n + j.val ∈ Tv ∧ w ∈ (C.gates[j.val]).inputs then 1 else 0
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro w _; simp only [Finset.sum_filter]
            · trans ∑ j : Fin C.gates.length, if n + j.val ∈ Tv then (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card else 0
              · exact Finset.sum_congr rfl (fun j _ => h1 j)
              · rw [← Finset.sum_filter]; simp only [Finset.card_eq_sum_ones]
          rw [hswap]
          have hge1 : ∀ j ∈ Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv),
              1 ≤ (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card := by
            intro j hj
            have hjTv : n + j.val ∈ Tv := (Finset.mem_filter.mp hj).2
            have hjt : (C.wires (List.ofFn ev)).getD (n + j.val) false = true := (Finset.mem_filter.mp hjTv).2
            have hg : C.gates[j.val]? = some (C.gates[j.val]'j.isLt) := List.getElem?_eq_getElem j.isLt
            obtain ⟨p, q, hpq, hp, hq, _⟩ := hgate_shape j.val j.isLt
            have hgop : (C.gates[j.val]'j.isLt).op = GateOp.and ∨ (C.gates[j.val]'j.isLt).op = GateOp.or := by
              simpa using (hmono _ (List.getElem_mem j.isLt)).1
            rw [wires_gate_ofFn C ev j.val _ hg, hpq] at hjt
            have hex : (C.wires (List.ofFn ev)).getD p false = true ∨ (C.wires (List.ofFn ev)).getD q false = true := by
              rcases hgop with hand | hor
              · rw [hand] at hjt; simp [GateOp.eval, hp, hq] at hjt; exact Or.inl hjt.1
              · rw [hor] at hjt; simp [GateOp.eval, hp, hq] at hjt; exact hjt
            have hjs : j.val < s := by have := j.isLt; omega
            rcases hex with hpt | hqt
            · exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpt⟩, by rw [hpq]; simp⟩⟩
            · exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hqt⟩, by rw [hpq]; simp⟩⟩
          have hsum_j := Finset.sum_le_sum hge1
          simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum_j
          have hcard_j : Tv.card - 1 ≤ (Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv)).card := by
            have hsub_inj : (Tv.erase v.val).card ≤ (Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∈ Tv)).card := by
              refine Finset.card_le_card_of_injOn
                (fun w => if h : w - n < C.gates.length then ⟨w - n, h⟩ else ⟨0, by omega⟩) ?_ ?_
              · intro w hw
                have hwTv := Finset.mem_of_mem_erase hw
                have hne_v := (Finset.mem_erase.mp hw).1
                have hw_lt := hTv_lt w hwTv
                have hge_n : n ≤ w := by
                  by_contra hlt
                  have hwt := (Finset.mem_filter.mp hwTv).2
                  rw [wires_input C ev w (by omega)] at hwt
                  simp only [ev, decide_eq_true_eq] at hwt
                  exact hne_v (congrArg Fin.val hwt)
                have hsub_lt : w - n < C.gates.length := by omega
                simp only [hsub_lt, ↓reduceDIte, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
                rwa [show n + (w - n) = w by omega]
              · intro w1 hw1 w2 hw2 heq
                have h1Tv := Finset.mem_of_mem_erase hw1
                have h2Tv := Finset.mem_of_mem_erase hw2
                have hw1_lt := hTv_lt w1 h1Tv
                have hw2_lt := hTv_lt w2 h2Tv
                have hge1 : n ≤ w1 := by
                  by_contra hlt
                  have hwt := (Finset.mem_filter.mp h1Tv).2
                  rw [wires_input C ev w1 (by omega)] at hwt
                  simp only [ev, decide_eq_true_eq] at hwt
                  exact (Finset.mem_erase.mp hw1).1 (congrArg Fin.val hwt)
                have hge2 : n ≤ w2 := by
                  by_contra hlt
                  have hwt := (Finset.mem_filter.mp h2Tv).2
                  rw [wires_input C ev w2 (by omega)] at hwt
                  simp only [ev, decide_eq_true_eq] at hwt
                  exact (Finset.mem_erase.mp hw2).1 (congrArg Fin.val hwt)
                have hlt1 : w1 - n < C.gates.length := by omega
                have hlt2 : w2 - n < C.gates.length := by omega
                simp only [hlt1, hlt2, ↓reduceDIte] at heq
                have hv_eq : w1 - n = w2 - n := congrArg Fin.val heq
                omega
            have := Finset.card_erase_add_one hv_in_Tv
            omega
          omega
        have hdout_ge : Ev.card ≤ ∑ w ∈ Tv, dout w := by
          have hswap : ∑ w ∈ Tv, dout w =
              ∑ j ∈ Ev, (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card := by
            trans ∑ j : Fin C.gates.length, ∑ w ∈ Tv, if n + j.val ∉ Tv ∧ w ∈ (C.gates[j.val]).inputs then 1 else 0
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro w _; simp [dout]
            · rw [← Finset.sum_subset (Finset.subset_univ Ev)]
              · apply Finset.sum_congr rfl
                intro j hj
                have hjnot : n + j.val ∉ Tv := ((hmem_Ev j).mp hj).1
                simp [hjnot, Finset.sum_boole]
              · intro j _ hjnot
                simp only [Ev, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_exists] at hjnot
                by_cases hntv : n + j.val ∉ Tv
                · apply Finset.sum_eq_zero
                  intro w hw
                  have : w ∉ (C.gates[j.val]).inputs := fun hm => hjnot hntv w hm hw
                  simp [hntv, this]
                · simp [hntv]
          rw [hswap]
          have hge1 : ∀ j ∈ Ev, 1 ≤ (Tv.filter (fun w => w ∈ (C.gates[j.val]).inputs)).card := by
            intro j hj
            obtain ⟨i, hi_mem, hi_Tv⟩ := ((hmem_Ev j).mp hj).2
            exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi_Tv, hi_mem⟩⟩
          have := Finset.sum_le_sum hge1
          simpa using this
        have htot : (∑ w ∈ Tv, din w) + (∑ w ∈ Tv, dout w) = ∑ w ∈ Tv, outdeg w := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun w _ => hsplit w)
        have hTv_pos : 1 ≤ Tv.card := Finset.card_pos.mpr ⟨v.val, hv_in_Tv⟩
        omega
      have hu_maps_Ev : ∀ u ∈ G.neighborFinset v ∩ I,
          ∃ hlt : nextOf (orEnd u.val) < C.gates.length, (⟨nextOf (orEnd u.val), hlt⟩ : Fin C.gates.length) ∈ Ev := by
        intro u hu
        have hvu : G.Adj v u := (SimpleGraph.mem_neighborFinset G v u).mp (Finset.mem_inter.mp hu).1
        have huNotT : u ∉ Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu).2).2
        obtain ⟨hlt, z, hord, hzlt, hzne, hzch⟩ := hother_input_and u huNotT
        obtain ⟨_, _, handu⟩ := hand_exit u huNotT
        have hzt : (C.wires (List.ofFn ev)).getD z false = true :=
          hand_z_true u huNotT v hvu.symm hlt z hord hzlt hzne hzch
        have hsu0 : (C.wires (List.ofFn ev)).getD (orEnd u.val) false = false :=
          hs_zero_other u v (G.ne_of_adj hvu)
        have ha0 : (C.wires (List.ofFn ev)).getD (n + nextOf (orEnd u.val)) false = false := by
          have hg : C.gates[nextOf (orEnd u.val)]? = some (C.gates[nextOf (orEnd u.val)]'hlt) := List.getElem?_eq_getElem hlt
          have h1u := (hand_exit u huNotT).1
          have hsult : orEnd u.val < n + nextOf (orEnd u.val) := hnextOf_gt _ (hs_ne_out u) h1u
          rw [wires_gate_ofFn C ev _ _ hg, handu]
          rcases hord with h | h <;> rw [h] <;>
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hsult, ↓reduceIte, hsu0, Bool.false_and, Bool.and_false]
        refine ⟨hlt, (hmem_Ev ⟨nextOf (orEnd u.val), hlt⟩).mpr ⟨?_, z, ?_, ?_⟩⟩
        · intro hm
          have h1 := (Finset.mem_filter.mp hm).2
          rw [ha0] at h1; exact absurd h1 (by decide)
        · rcases hord with h | h <;> rw [h] <;> simp
        · have hj_s : nextOf (orEnd u.val) < s := by omega
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hzt⟩
      have hu_inj : ∀ u1 ∈ G.neighborFinset v ∩ I, ∀ u2 ∈ I,
          nextOf (orEnd u1.val) = nextOf (orEnd u2.val) → u1 = u2 := by
        intro u1 hu1 u2 hu2 heq
        have hvu1 : G.Adj v u1 := (SimpleGraph.mem_neighborFinset G v u1).mp (Finset.mem_inter.mp hu1).1
        have diff : v ≠ u2 := fun e => (Finset.mem_sdiff.mp hu2).2 (e ▸ hv)
        have hu1NotT : u1 ∉ Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu1).2).2
        have hu2NotT : u2 ∉ Tbranch := (Finset.mem_sdiff.mp hu2).2
        obtain ⟨hlt1, z1, hord1, hz1lt, hz1ne, hz1ch⟩ := hother_input_and u1 hu1NotT
        have hz1t : (C.wires (List.ofFn ev)).getD z1 false = true :=
          hand_z_true u1 hu1NotT v hvu1.symm hlt1 z1 hord1 hz1lt hz1ne hz1ch
        have hsu20 : (C.wires (List.ofFn ev)).getD (orEnd u2.val) false = false :=
          hs_zero_other u2 v diff
        have h1u2 := (hand_exit u2 hu2NotT).1
        obtain ⟨_, hm2, _⟩ := hnextOf_spec (orEnd u2.val) (hs_ne_out u2) h1u2
        have hm2' : orEnd u2.val ∈ (C.gates[nextOf (orEnd u1.val)]'hlt1).inputs := by
          simpa only [heq] using hm2
        rcases hord1 with h | h <;> rw [h] at hm2' <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2'
        · rcases hm2' with h' | h'
          · exact hs_inj h'.symm
          · rw [h', hz1t] at hsu20; exact absurd hsu20 (by decide)
        · rcases hm2' with h' | h'
          · rw [h', hz1t] at hsu20; exact absurd hsu20 (by decide)
          · exact hs_inj h'.symm
      have hcard_le2 : (G.neighborFinset v ∩ I).card ≤ Ev.card := by
        have hle := Finset.card_le_card_of_injOn
          (s := G.neighborFinset v ∩ I) (t := Ev)
          (fun u => if h : nextOf (orEnd u.val) < C.gates.length then ⟨nextOf (orEnd u.val), h⟩ else ⟨0, by omega⟩)
          (fun u hu => by
            obtain ⟨hlt, hmem⟩ := hu_maps_Ev u hu
            simp only [hlt, ↓reduceDIte, Finset.mem_coe]
            exact hmem)
          (fun u1 hu1 u2 hu2 heq => by
            have hlt1 := (hu_maps_Ev u1 hu1).1
            have hlt2 := (hu_maps_Ev u2 hu2).1
            simp only [hlt1, hlt2, ↓reduceDIte] at heq
            exact hu_inj u1 hu1 u2 (Finset.mem_inter.mp hu2).2 (congrArg Fin.val heq))
        omega
      refine ⟨hcard_le2,hEv_le2,fun w h => Finset.mem_range.mpr (hTv_lt w h),?_,hu_inj⟩
      intro w hw
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hlt,hm⟩ := hu_maps_Ev u hu
      exact Finset.mem_image.mpr ⟨⟨_,hlt⟩,hm,rfl⟩
    have neighborCap (v : Fin n) (hv : v∈Tbranch) : (G.neighborFinset v ∩ I).card ≤ 2+extra := by
      obtain ⟨a,b,c,-,-⟩ := details v hv
      have z := Finset.sum_le_sum_of_subset (f:=spare) c
      rw [fullSpare] at z
      omega
    obtain ⟨v,hv,w,hw,adj,ge⟩ := cut s extra Tbranch hvc paid (by omega) neighborCap
    change 2+extra ≤ (G.neighborFinset v ∩ I).card at ge
    obtain ⟨a,b,sub,images,inj⟩ := details v hv
    have upper := Finset.sum_le_sum_of_subset (f:=spare) sub
    rw [fullSpare] at upper
    have cardSrc : ((G.neighborFinset v ∩ I).image follow).card=(G.neighborFinset v ∩ I).card :=
      Finset.card_image_of_injOn (fun u hu z hz h => inj u hu z (Finset.mem_inter.mp hz).2 h)
    have cardDst : ((bound v).image Fin.val).card=(bound v).card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have imageEq := Finset.eq_of_subset_of_card_le images (by omega)
    let ev (z i : Fin n) := decide (i=z)
    have off (z : Fin n) : val C (ev z) C.output=false := by
      cases h : val C (ev z) C.output
      · rfl
      · obtain ⟨p,q,edge,hp,hq⟩ := hfun.1 _ (tinyOne z) h
        simp only [decide_eq_true_eq] at hp hq
        subst hp; subst hq
        exact False.elim (G.loopless.irrefl _ edge)
    have on : val C (fun i => ev v i || ev w i) C.output=true :=
      hfun.2 _ ⟨v,w,adj,by simp [ev],by simp [ev]⟩
    obtain ⟨j,stop,⟨q,hq,beforeQ,onQ⟩,live⟩ := firstMeet C hmono (by
      intro j
      obtain ⟨p,q,shape,hp,hq,-⟩ := hgate_shape j.val j.isLt
      exact ⟨p,q,shape,hp,hq⟩) (ev v) (ev w) C.output (by omega) (off v) (off w) on
    have jlt : j.val < s := by have := j.isLt; omega
    have jb : j∈bound v := by
      simp only [bound,Finset.mem_filter,Finset.mem_univ,true_and]
      refine ⟨?_,q,hq,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),onQ⟩⟩
      intro hit
      exact Bool.noConfusion (stop.symm.trans (Finset.mem_filter.mp hit).2)
    obtain ⟨u,hu,uj⟩ := Finset.mem_image.mp (imageEq.symm ▸ Finset.mem_image.mpr ⟨j,jb,rfl⟩)
    have un : u∉Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu).2).2
    obtain ⟨_,hm,_⟩ := hnextOf_spec (orEnd u.val) (hs_ne_out u) (hand_exit u un).1
    have uj' : nextOf (orEnd u.val)=j.val := uj
    have gm : orEnd u.val ∈ (C.gates[j.val]).inputs := by simpa only [uj'] using hm
    rcases live _ gm with lv|lw
    · exact Bool.noConfusion ((hs_zero_other u v (fun h => un (h ▸ hv))).symm.trans lv)
    · exact Bool.noConfusion ((hs_zero_other u w (fun h => un (h ▸ hw))).symm.trans lw)

end CrownCharge9304

namespace Crown9304
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open GraphTools Finset
abbrev V := Fin 12
def A (u v : Fin 6) := decide (u ≠ v)
def side (v : V) := decide (v.val<6)
def mate : V → V := ![6,7,8,9,10,11,0,1,2,3,4,5]
def cross (u v : V) := side u≠side v ∧ v≠mate u
instance (u v : V) : Decidable (cross u v) := by unfold cross; infer_instance
def pair (a b : V) (i : V) := decide (i=a ∨ i=b)
def value (C : Circuit) (x : V → Bool) := C.eval (List.ofFn x)
theorem pairSwap (a b : V) : pair a b=pair b a := by funext i; simp [pair,or_comm]
def graph (C : Circuit) : SimpleGraph V where
  Adj u v := u≠v ∧ value C (pair u v)=true
  symm := ⟨fun _ _ h => ⟨h.1.symm,(pairSwap ..) ▸ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
instance (C : Circuit) : DecidableRel (graph C).Adj := fun u v => inferInstanceAs
  (Decidable (u≠v ∧ value C (pair u v)=true))

theorem matched (C : Circuit) (h : Represents A C) (v : V) : value C (pair v (mate v))=false := by
  have samples : ∀ v : V, ∃ p l : Fin 6, A p l=false ∧ List.ofFn (pair v (mate v))=oneEach p l := by
    decide
  obtain ⟨p,l,bad,eq⟩ := samples v
  unfold value
  rw [eq,h,bad]

theorem crossEdge {C : Circuit} (h : Represents A C) {u v} (c : cross u v) : (graph C).Adj u v := by
  have samples : ∀ u v : V, cross u v → ∃ p l : Fin 6, A p l=true ∧ List.ofFn (pair u v)=oneEach p l := by
    decide
  obtain ⟨p,l,yes,eq⟩ := samples u v c
  refine ⟨fun same => c.1 (congrArg side same),?_⟩
  unfold value
  rw [eq,h,yes]

theorem valueMono {C : Circuit} (hm : Monotone2 C) {x y : V → Bool}
    (hxy : ∀ i, x i=true → y i=true) : value C x=true → value C y=true :=
  wires_mono C hm x y hxy C.output

theorem sparse {C : Circuit} (hm : Monotone2 C) (hr : Represents A C) :
    Sparse2008.SparseTruth (graph C) C := by
  constructor
  · rintro x ⟨a,b,support⟩ yes
    have many (v : V) (only : ∀ i, x i=true → i=v) : False := by
      have top := valueMono hm (y := pair v (mate v)) (fun i hi => by simp [pair,only i hi]) yes
      rw [matched C hr v] at top
      contradiction
    have aa : x a=true := by
      by_contra off
      exact many b (fun i hi => (support i hi).resolve_left (fun e => off (e ▸ hi)))
    have bb : x b=true := by
      by_contra off
      exact many a (fun i hi => (support i hi).resolve_right (fun e => off (e ▸ hi)))
    have ne : a≠b := fun same => many a (fun i hi => (support i hi).elim id (fun e => e.trans same.symm))
    have eq : x=pair a b := by
      funext i; rw [Bool.eq_iff_iff]
      simp only [pair,decide_eq_true_eq]
      exact ⟨support i,fun h => h.elim (fun e => e ▸ aa) (fun e => e ▸ bb)⟩
    exact ⟨a,b,⟨ne,eq ▸ yes⟩,aa,bb⟩
  · rintro x ⟨u,v,adj,hu,hv⟩
    apply valueMono hm (x := pair u v) _ adj.2
    intro i hi
    rcases of_decide_eq_true hi with rfl|rfl <;> assumption

def row (p : Fin 6) : V := Fin.castAdd 6 p
end Crown9304

namespace Crown9304
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def label : V → Fin 6 := ![0,1,2,3,4,5,0,1,2,3,4,5]
def mergeInput (z : Fin 6 → Bool) (i : V) := z (label i)
def two (z : Fin 6 → Bool) := ∃ i j : Fin 6, i≠j ∧ z i=true ∧ z j=true
instance (z : Fin 6 → Bool) : Decidable (two z) := by unfold two; infer_instance

theorem mergeForced {C : Circuit} (hm : Monotone2 C) (hr : Represents A C) (z : Fin 6 → Bool) :
    value C (mergeInput z) = decide (two z) := by
  have pos : ∀ z : Fin 6 → Bool, two z → ∃ a b : V, cross a b ∧
    ∀ i, pair a b i=true → mergeInput z i=true := by decide
  have neg : ∀ z : Fin 6 → Bool, ¬two z → ∃ v : V, ∀ i, mergeInput z i=true → pair v (mate v) i=true := by decide
  by_cases h : two z
  · obtain ⟨a,b,yes,bound⟩ := pos z h
    simpa [h] using valueMono hm bound (crossEdge hr yes).2
  · simp only [h,decide_false]
    obtain ⟨v,bound⟩ := neg z h
    cases e : value C (mergeInput z)
    · rfl
    · have bad := valueMono hm bound e
      rw [matched C hr v] at bad
      contradiction

end Crown9304

namespace Crown9304
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open RepReads RepInduced Finset
open PermInputs

theorem allLive {C : Circuit} (hm : Monotone2 C) (hr : Represents A C) (v : V) :
    Live 12 C.gates C.output v.val := by
  have existsNeighbor : ∀ v : V, ∃ a, cross v a := by decide
  obtain ⟨a,yes⟩ := existsNeighbor v
  have truePair := (crossEdge hr yes).2
  have sf : value C (pair a a)=false := by
    cases e : value C (pair a a)
    · rfl
    · have up := valueMono hm (y := pair a (mate a)) (fun i hi => by
        simp [pair] at hi; simp [pair,hi]) e
      rw [matched C hr a] at up; contradiction
  by_contra outside
  have eq := live_dep 12 C.gates C.output (List.ofFn (pair v a)) (List.ofFn (pair a a))
    (by simp) (by simp) (fun i hi => by
      by_cases h : i<12
      · have ne : (⟨i,h⟩ : V) ≠ v := fun e => outside ((congrArg Fin.val e) ▸ hi)
        rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by simpa using h)]
        simp only [List.getElem_ofFn]
        simp [pair,ne]
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)])
    C.gates.length le_rfl C.output Relation.ReflTransGen.refl
  rw [List.take_length] at eq
  change value C (pair v a)=value C (pair a a) at eq
  rw [truePair,sf] at eq
  contradiction

def bitsSet {n : ℕ} (x : Fin n → Bool) : Finset ℕ :=
  (univ.filter (fun i : Fin n => x i=true)).image Fin.val

theorem inBits {n : ℕ} (x : Fin n → Bool) (i : Fin n) : i.val∈bitsSet x ↔ x i=true := by
  simp only [bitsSet,mem_image,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨v,h,e⟩; exact (Fin.ext e : v=i) ▸ h
  · intro h; exact ⟨i,h,rfl⟩

theorem inpBits {n : ℕ} (x : Fin n → Bool) : inp n (bitsSet x)=List.ofFn x := by
  unfold inp
  apply congrArg List.ofFn
  funext i
  simp [inBits]

theorem renameMono {n m : ℕ} (f : Fin n → Fin m) (C : Circuit) (hc : Monotone2 C) :
    Monotone2 (relabel n m f C) := by
  intro g hg
  obtain ⟨g',h,rfl⟩ := List.mem_map.mp hg
  exact ⟨(hc g' h).1,by simpa [relGate] using (hc g' h).2⟩

theorem renameEval {n m : ℕ} (f : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    (relabel n m f C).eval (List.ofFn x)=C.eval (List.ofFn (x ∘ f)) :=
  (rel_fold n m f C.gates _ _ (rel_init n m f x)).2.2 C.output

theorem restrictInputs {C : Circuit} (hm : Monotone2 C) (hr : Represents A C) (E : Finset V)
    (P : Finset ℕ) (hp : C.eval (inp 12 (P \ E.image Fin.val))=true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+E.card≤C.size ∧
       ∀ x : V → Bool, value D x=value C (fun i => x i && decide (i∉E)) := by
  let Z := E.image Fin.val
  obtain ⟨D,md,sz,ev⟩ := kill 12 Z C.gates hm C.output Z (fun i hi => by
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
    exact ⟨v.isLt,mem_image.mpr ⟨v,hv,rfl⟩,allLive hm hr v⟩) P hp
  have card : Z.card=E.card := card_image_of_injective _ Fin.val_injective
  refine ⟨D,md,by simpa only [card,Circuit.size] using sz,?_⟩
  intro x
  change D.eval (List.ofFn x)=C.eval (List.ofFn _)
  rw [← inpBits x,ev]
  congr 1
  apply congrArg List.ofFn
  funext i
  have killEq : i.val∈Z ↔ i∈E := by
    constructor
    · intro h; obtain ⟨v,hv,e⟩ := mem_image.mp h; exact (Fin.ext e : v=i) ▸ hv
    · intro h; exact mem_image.mpr ⟨i,h,rfl⟩
  apply Bool.eq_iff_iff.mpr
  simp [mem_sdiff,killEq,inBits]

end Crown9304

namespace Crown9304
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PermInputs RepReads Finset

set_option maxHeartbeats 1200000 in
theorem cliqueTransfer {C : Circuit} (hm : Monotone2 C) (hr : Represents A C)
    (pick : Fin 6 → V) (sectionLabel : ∀ j, label (pick j)=j)
    (clique : ∀ j k, j≠k → (graph C).Adj (pick j) (pick k)) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+6≤C.size ∧
        ∀ x : Fin 6 → Bool, D.eval (List.ofFn x)=decide (two x) := by
  let K := (univ : Finset (Fin 6)).image pick
  let E := (univ : Finset V) \ K
  have kept (i : Fin 6) : pick i∈K := mem_image.mpr ⟨i,mem_univ _,rfl⟩
  have outside (i : Fin 6) : pick i∉E := fun e => (mem_sdiff.mp e).2 (kept i)
  have inj : Function.Injective pick := fun a b e => (sectionLabel a).symm.trans ((congrArg label e).trans (sectionLabel b))
  have szK : K.card=6 := by simp [K,card_image_of_injective _ inj]
  have szE : E.card=6 := by have h := card_sdiff_add_card_eq_card (subset_univ K); change E.card+K.card=12 at h; omega
  let pair0 := pair (pick 0) (pick 1)
  have unchanged : bitsSet pair0 \ E.image Fin.val=bitsSet pair0 := by
    ext a
    simp only [mem_sdiff,and_iff_left_iff_imp]
    intro ha he
    obtain ⟨i,ei,rfl⟩ := mem_image.mp he
    have : pair0 i=true := (inBits _ _).mp ha
    rcases of_decide_eq_true this with rfl|rfl
    · exact outside 0 ei
    · exact outside 1 ei
  have hp : C.eval (inp 12 (bitsSet pair0 \ E.image Fin.val))=true := by
    rw [unchanged,inpBits]; exact (clique 0 1 (by decide)).2
  obtain ⟨D,dm,sz,ev⟩ := restrictInputs hm hr E (bitsSet pair0) hp
  refine ⟨relabel 12 6 label D,renameMono label D dm,by simpa [relabel,Circuit.size,szE] using sz,?_⟩
  intro x
  rw [renameEval]
  change value D (mergeInput x)=_
  rw [ev]
  by_cases yes : two x
  · simp only [yes,decide_true]
    obtain ⟨j,k,diff,hj,hk⟩ := yes
    apply valueMono hm (x := pair (pick j) (pick k)) _ (clique j k diff).2
    intro i hi
    rcases of_decide_eq_true hi with rfl|rfl
    · simp [mergeInput,sectionLabel,hj,outside]
    · simp [mergeInput,sectionLabel,hk,outside]
  · simp only [yes,decide_false]
    cases e : value C (fun i => mergeInput x i && decide (i∉E))
    · rfl
    · have bad : value C (mergeInput x)=true := valueMono hm (x := fun i => mergeInput x i && decide (i∉E)) (y := mergeInput x) (fun i hi => (Bool.and_eq_true_iff.mp hi).1) e
      have off : value C (mergeInput x)=false := (mergeForced hm hr x).trans (by simp only [yes,decide_false])
      exact False.elim (Bool.noConfusion (off.symm.trans bad))

end Crown9304

namespace Crown9304
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PermInputs RepReads Finset

def induced {m : ℕ} (C : Circuit) (f : Fin m ↪ V) : SimpleGraph (Fin m) :=
  (graph C).comap f

instance {m : ℕ} (C : Circuit) (f : Fin m ↪ V) : DecidableRel (induced C f).Adj :=
  fun a b => inferInstanceAs (Decidable ((graph C).Adj (f a) (f b)))

theorem extractInduced {m : ℕ} {C : Circuit} (hm : Monotone2 C) (hr : Represents A C)
    (f : Fin m ↪ V) (hedge : ∃ a b, (induced C f).Adj a b) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+(12-m) ≤ C.size ∧ Sparse2008.SparseTruth (induced C f) D := by
  classical
  obtain ⟨a,b,hab⟩ := hedge
  letI : Nonempty (Fin m) := ⟨a⟩
  let K := (univ : Finset (Fin m)).image f
  let E := (univ : Finset V) \ K
  let r : V → Fin m := Function.invFun f
  have left (j : Fin m) : r (f j) = j := Function.leftInverse_invFun f.injective j
  have kept (j : Fin m) : f j ∈ K := mem_image.mpr ⟨j,mem_univ _,rfl⟩
  have outside (j : Fin m) : f j ∉ E := fun h => (mem_sdiff.mp h).2 (kept j)
  have survive {i : V} (hi : i ∉ E) : ∃ j, f j=i := by
    have hiK : i ∈ K := by
      by_contra no
      exact hi (mem_sdiff.mpr ⟨mem_univ _,no⟩)
    obtain ⟨j,_,hj⟩ := mem_image.mp hiK
    exact ⟨j,hj⟩
  have szK : K.card=m := by simp [K,card_image_of_injective _ f.injective]
  have szE : E.card=12-m := by
    have h := card_sdiff_add_card_eq_card (subset_univ K)
    change E.card+K.card=12 at h
    omega
  let p := pair (f a) (f b)
  have stable : bitsSet p \ E.image Fin.val = bitsSet p := by
    ext j
    simp only [mem_sdiff,and_iff_left_iff_imp]
    intro hj h
    obtain ⟨w,hw,rfl⟩ := mem_image.mp h
    have hw' : p w = true := (inBits p w).mp hj
    rcases of_decide_eq_true hw' with rfl|rfl
    · exact outside a hw
    · exact outside b hw
  have hp : C.eval (inp 12 (bitsSet p \ E.image Fin.val)) = true := by
    rw [stable,inpBits]
    exact hab.2
  obtain ⟨D,hd,sz,ev⟩ := restrictInputs hm hr E (bitsSet p) hp
  let lift (x : Fin m → Bool) (i : V) := x (r i) && decide (i ∉ E)
  have selected (x : Fin m → Bool) (j) : lift x (f j) = x j := by simp [lift,left,outside]
  have equal (x : Fin m → Bool) : (relabel 12 m r D).eval (List.ofFn x) = value C (lift x) := by
    rw [renameEval]
    exact ev _
  refine ⟨relabel 12 m r D,renameMono r D hd,by simpa [relabel,Circuit.size,szE] using sz,?_,?_⟩
  · intro x small yes
    obtain ⟨u,v,hs⟩ := small
    have tiny : Sparse2008.Tiny (lift x) := by
      refine ⟨f u,f v,?_⟩
      intro i hi
      have notE : i ∉ E := of_decide_eq_true (Bool.and_eq_true_iff.mp hi).2
      obtain ⟨j,rfl⟩ := survive notE
      exact (hs j ((selected x j) ▸ hi)).imp (congrArg f) (congrArg f)
    obtain ⟨i,j,hadj,hi,hj⟩ := (sparse hm hr).1 (lift x) tiny ((equal x).symm.trans yes)
    obtain ⟨u',rfl⟩ := survive (of_decide_eq_true (Bool.and_eq_true_iff.mp hi).2)
    obtain ⟨v',rfl⟩ := survive (of_decide_eq_true (Bool.and_eq_true_iff.mp hj).2)
    exact ⟨u',v',hadj,(selected x u') ▸ hi,(selected x v') ▸ hj⟩
  · rintro x ⟨u,v,hadj,hu,hv⟩
    rw [equal]
    exact (sparse hm hr).2 _ ⟨f u,f v,hadj,(selected x u).trans hu,(selected x v).trans hv⟩

theorem tenVertices {m : ℕ} {C : Circuit} (hm : Monotone2 C) (hr : Represents A C)
    (f : Fin m ↪ V) (large : 10 ≤ m) (hedge : ∃ a b, (induced C f).Adj a b)
    (degree : ∀ i, 5 ≤ (induced C f).degree i)
    (apart : ∀ i j, i ≠ j → ∃ z, (induced C f).Adj i z ∧ ¬(induced C f).Adj j z)
    (hcov : ∀ S, CoverPromise.IsVertexCover (induced C f) S → 6 ≤ S.card) : 19 ≤ C.size := by
  obtain ⟨D,mono,sz,rep⟩ := extractInduced hm hr f hedge
  have lower := CrownCharge9304.saturationBound m (m+7) (by omega) (induced C f)
    (fun i => (by decide : 3≤5).trans (degree i)) apart (by
      intro s extra Tbranch hvc paid small hT_nbr_I
      exfalso
      let G := induced C f
      let I := (Finset.univ : Finset (Fin m)) \ Tbranch
      have num : I.card+Tbranch.card=m := by simpa [I] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Tbranch)
      have minCover := hcov Tbranch hvc
      change ∀ v∈Tbranch, (G.neighborFinset v ∩ I).card ≤ 2+extra at hT_nbr_I
      have hdouble_count : 5 * I.card ≤ Tbranch.card*(2+extra) := by
        have h1 : ∑ u ∈ I, (G.neighborFinset u ∩ Tbranch).card = ∑ v ∈ Tbranch, (G.neighborFinset v ∩ I).card := by
          have hLHS : ∑ u ∈ I, (G.neighborFinset u ∩ Tbranch).card =
              ∑ u ∈ I, ∑ v ∈ Tbranch, if G.Adj u v then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro u _
            rw [Finset.sum_boole]
            congr 1
            ext v
            simp [SimpleGraph.mem_neighborFinset, and_comm]
          have hRHS : ∑ v ∈ Tbranch, (G.neighborFinset v ∩ I).card =
              ∑ v ∈ Tbranch, ∑ u ∈ I, if G.Adj u v then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro v _
            rw [Finset.sum_boole]
            congr 1
            ext u
            simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm, and_comm]
          rw [hLHS, hRHS, Finset.sum_comm]
        have hLHS_ge : 5 * I.card ≤ ∑ u ∈ I, (G.neighborFinset u ∩ Tbranch).card := by
          calc
            5 * I.card = ∑ _u ∈ I, 5 := by simp [mul_comm]
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro u hu
              have hsub : G.neighborFinset u ⊆ Tbranch := by
                intro v hv
                have huv : G.Adj u v := (SimpleGraph.mem_neighborFinset G u v).mp hv
                rcases hvc u v huv with huT | hvT
                · exact absurd huT (Finset.mem_sdiff.mp hu).2
                · exact hvT
              rw [Finset.inter_eq_left.mpr hsub]
              exact degree u
        have hRHS_le : ∑ v ∈ Tbranch, (G.neighborFinset v ∩ I).card ≤ Tbranch.card*(2+extra) := by
          have := Finset.sum_le_sum hT_nbr_I
          simpa using this
        omega
      have b7 : Tbranch.card≤7 := by omega
      let b := Tbranch.card
      have options : b=6 ∨ b=7 := by dsimp [b]; omega
      change 5*I.card ≤ b*(2+extra) at hdouble_count
      change m+b+extra=s+1 at paid
      change I.card+b=m at num
      rcases options with h|h <;> rw [h] at hdouble_count paid num <;> omega) D.size D rfl mono rep
  omega

end Crown9304

namespace Crown9304
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents Finset

theorem mateMate : ∀ v : V, mate (mate v) = v := by decide
theorem mateNot : ∀ v : V, mate v ≠ v := by decide
theorem sidesMate : ∀ v : V, side (mate v) ≠ side v := by decide
theorem sameLabel : ∀ v w : V, label v = label w ↔ w=v ∨ w=mate v := by decide
theorem labelMate : ∀ v : V, label (mate v)=label v := by decide

def Retains (P : Finset V) := ∀ v : V, v ∈ P ∨ mate v ∈ P
def AllAdjacent (C : Circuit) (P : Finset V) (u : V) :=
  ∀ z ∈ P, z ≠ u → (graph C).Adj u z
def UnpairedUniversal (C : Circuit) (P : Finset V) :=
  ∀ u ∈ P, mate u ∉ P → AllAdjacent C P u
def Terminal (C : Circuit) (P : Finset V) :=
  ∀ u ∈ P, mate u ∈ P → ∃ z ∈ P, side z=side u ∧ z≠u ∧ ¬(graph C).Adj u z

theorem peel {C : Circuit} (hr : Represents A C) (P : Finset V) (keep : Retains P)
    (univP : UnpairedUniversal C P) :
    ∃ Q : Finset V, Q ⊆ P ∧ Retains Q ∧ UnpairedUniversal C Q ∧ Terminal C Q := by
  classical
  induction hsize : P.card using Nat.strong_induction_on generalizing P with
  | ind n ih =>
    by_cases done : Terminal C P
    · exact ⟨P,Subset.rfl,keep,univP,done⟩
    unfold Terminal at done
    push Not at done
    obtain ⟨u,hu,hmu,univSide⟩ := done
    let P' := P.erase (mate u)
    have inc : P' ⊆ P := erase_subset _ _
    have retained : Retains P' := by
      intro v
      by_cases e : v=mate u
      · subst v
        right
        rw [mateMate]
        exact mem_erase.mpr ⟨(mateNot u).symm,hu⟩
      obtain hv | hv := keep v
      · exact Or.inl (mem_erase.mpr ⟨e,hv⟩)
      · by_cases m : mate v = mate u
        · have eq : v=u := by simpa only [mateMate] using congrArg mate m
          exact Or.inl (mem_erase.mpr ⟨e,eq ▸ hu⟩)
        · exact Or.inr (mem_erase.mpr ⟨m,hv⟩)
    have universals : UnpairedUniversal C P' := by
      intro a ha lost z hz hza
      by_cases hm : mate a ∈ P
      · have same : mate a = mate u := by
          by_contra different
          exact lost (mem_erase.mpr ⟨different,hm⟩)
        have eq : a = u := by simpa only [mateMate] using congrArg mate same
        subst a
        by_cases sideEq : side z=side u
        · exact univSide z (inc hz) sideEq hza
        · exact crossEdge hr ⟨Ne.symm sideEq,(mem_erase.mp hz).1⟩
      · exact univP a (inc ha) hm z (inc hz) hza
    have smaller : P'.card < n := by
      have card := Finset.card_erase_add_one hmu
      change (P.erase (mate u)).card < n
      omega
    obtain ⟨Q,hQ,kQ,uQ,tQ⟩ := ih _ smaller P' retained universals rfl
    exact ⟨Q,hQ.trans inc,kQ,uQ,tQ⟩

theorem terminalExists {C : Circuit} (hr : Represents A C) :
    ∃ Q, Retains Q ∧ UnpairedUniversal C Q ∧ Terminal C Q := by
  obtain ⟨Q,_,h⟩ := peel hr univ (fun _ => Or.inl (mem_univ _)) (by simp [UnpairedUniversal])
  exact ⟨Q,h⟩

theorem terminalSep {C : Circuit} (hr : Represents A C) {P : Finset V}
    (singles : UnpairedUniversal C P) (terminal : Terminal C P)
    {u v : V} (hu : u∈P) (hv : v∈P) (ne : u≠v) :
    ∃ z ∈ P, (graph C).Adj u z ∧ ¬(graph C).Adj v z := by
  by_cases adj : (graph C).Adj u v
  · exact ⟨v,hv,adj,(graph C).loopless.irrefl v⟩
  have vm : mate v∈P := by
    by_contra lost
    exact adj ((singles v hv lost u hu ne).symm)
  by_cases sideEq : side u=side v
  · have c : ∀ a b : V, a≠b → side a=side b → cross a (mate b) := by decide
    exact ⟨mate v,vm,crossEdge hr (c u v ne sideEq),
        fun bad => Bool.false_ne_true ((matched C hr v).symm.trans bad.2)⟩
  · have paired : v=mate u := by by_contra e; exact adj (crossEdge hr ⟨sideEq,e⟩)
    obtain ⟨z,hz,sideZ,hne,off⟩ := terminal v hv vm
    exact ⟨z,hz,crossEdge hr ⟨fun e => sideEq (e.trans sideZ),fun e => hne (e.trans paired.symm)⟩,off⟩

def slot (i : Fin 6) (s : Bool) : V := if s then row i else mate (row i)

theorem slotLabel : ∀ i s, label (slot i s) = i := by decide
theorem slotSide : ∀ i s, side (slot i s)=s := by decide
theorem slotMate : ∀ i s, mate (slot i s)=slot i (!s) := by decide
theorem slotRecover : ∀ v : V, slot (label v) (side v)=v := by decide

theorem otherLabelNeighbor {C : Circuit} (hr : Represents A C) {P : Finset V}
    (keep : Retains P) (singles : UnpairedUniversal C P) {v : V} (hv : v∈P)
    (j : Fin 6) (diff : j≠label v) : ∃ w∈P, (graph C).Adj v w ∧ label w=j := by
  let w := slot j (!side v)
  have lab : label w=j := slotLabel _ _
  have wside : side v≠side w := by rw [show side w = !side v from slotSide _ _]; cases side v <;> decide
  by_cases present : w∈P
  · exact ⟨w,present,crossEdge hr ⟨wside,fun same => diff (lab.symm.trans ((congrArg label same).trans (labelMate v)))⟩,lab⟩
  · have rem := (keep w).resolve_left present
    have vne : v ≠ mate w := fun e => diff (lab.symm.trans ((labelMate w).symm.trans (congrArg label e).symm))
    have only : mate (mate w) ∉ P := by rwa [mateMate]
    exact ⟨mate w,rem,(singles _ rem only v hv vne).symm,(labelMate w).trans lab⟩

end Crown9304

namespace Crown9304
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents Finset

theorem terminalCover {C : Circuit} (hr : Represents A C) {P : Finset V} (size : 8 ≤ P.card)
    (keep : Retains P) (singles : UnpairedUniversal C P)
    (S : Finset V) (cover : ∀ u∈P, ∀ v∈P, (graph C).Adj u v → u∈S ∨ v∈S) : 6 ≤ S.card := by
  classical
  let D := P \ S
  have hs : P ⊆ S ∪ D := by
    intro x hx
    by_cases h : x∈S
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hx,h⟩)
  have tot := (card_le_card hs).trans (card_union_le S D)
  by_cases tiny : D.card ≤ 2
  · omega
  have ind {u v : V} (hu : u∈D) (hv : v∈D) : ¬ (graph C).Adj u v := by
    obtain ⟨up,us⟩ := mem_sdiff.mp hu
    obtain ⟨vp,vs⟩ := mem_sdiff.mp hv
    exact fun e => (cover u up v vp e).elim us vs
  have paired (v : V) (vd : v∈D) : mate v ∈ P := by
    by_contra lost
    have universal := singles v (mem_sdiff.mp vd).1 lost
    have few : D ⊆ {v} := by
      intro w hw
      apply mem_singleton.mpr
      by_contra ne
      exact ind vd hw (universal w (mem_sdiff.mp hw).1 ne)
    have h := card_le_card few
    simp only [card_singleton] at h
    omega
  have separate (v : V) (vd : v∈D) : mate v ∉ D := by
    intro md
    have diff : ∀ a z : V, z≠a → z≠mate a → cross a z ∨ cross (mate a) z := by decide
    have few : D ⊆ {v,mate v} := by
      intro w hw
      by_contra ne
      simp only [mem_insert,mem_singleton,not_or] at ne
      rcases diff v w ne.1 ne.2 with left|right
      · exact ind vd hw (crossEdge hr left)
      · exact ind md hw (crossEdge hr right)
    exact tiny ((card_le_card few).trans (card_le_two (a:=v) (b:=mate v)))
  have covered : (univ : Finset (Fin 6)) ⊆ S.image label := by
    intro j _
    let v := slot j true
    have lj : label v = j := slotLabel _ _
    have use (i : V) (il : label i=j) (ip : i∈P) : j∈S.image label := by
      by_cases inside : i∈S
      · exact mem_image.mpr ⟨i,inside,il⟩
      · have idD : i∈D := mem_sdiff.mpr ⟨ip,inside⟩
        have mi : mate i∈S := by
          by_contra no
          exact separate i idD (mem_sdiff.mpr ⟨paired i idD,no⟩)
        exact mem_image.mpr ⟨mate i,mi,(labelMate i).trans il⟩
    rcases keep v with vp|mp
    · exact use v lj vp
    · exact use (mate v) ((labelMate v).trans lj) mp
  exact (show 6 ≤ (S.image label).card from by simpa using card_le_card covered).trans card_image_le

noncomputable def indexEquiv (P : Finset V) : Fin P.card ≃ ↥P :=
  (Fintype.equivFinOfCardEq (α := ↥P) (by simp)).symm

theorem terminalCost {C : Circuit} (hm : Monotone2 C) (hr : Represents A C) {P : Finset V}
    (size : 10 ≤ P.card) (keep : Retains P) (singles : UnpairedUniversal C P)
    (termP : Terminal C P) : 19 ≤ C.size := by
  classical
  let e := indexEquiv P
  let f := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ P))
  have memP (i) : f i ∈ P := (e i).property
  have onto (x : V) (h : x∈P) : ∃ j, f j=x := by
    refine ⟨e.symm ⟨x,h⟩,?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x,h⟩)
  have degree (i : Fin P.card) : 5 ≤ (induced C f).degree i := by
    let L := (univ : Finset (Fin 6)).erase (label (f i))
    have sub : L ⊆ ((induced C f).neighborFinset i).image (fun u => label (f u)) := by
      intro j hj
      obtain ⟨w,hw,adj,lab⟩ := otherLabelNeighbor hr keep singles (memP i) j (mem_erase.mp hj).1
      obtain ⟨k,rfl⟩ := onto w hw
      exact mem_image.mpr ⟨k,((induced C f).mem_neighborFinset i k).mpr adj,lab⟩
    have bound := (card_le_card sub).trans card_image_le
    have num : L.card=5 := by simp [L]
    rwa [num,SimpleGraph.card_neighborFinset_eq_degree] at bound
  have nonempty : ∃ a b, (induced C f).Adj a b := by
    let i : Fin P.card := ⟨0,by omega⟩
    have pos : 0 < ((induced C f).neighborFinset i).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; have := degree i; omega
    obtain ⟨v,hv⟩ := card_pos.mp pos
    exact ⟨i,v,((induced C f).mem_neighborFinset i v).mp hv⟩
  apply tenVertices hm hr f size nonempty degree
  · intro u v ne
    obtain ⟨z,hz,adj,off⟩ := terminalSep hr singles termP (memP u) (memP v)
      (fun h => ne (f.injective h))
    obtain ⟨k,rfl⟩ := onto z hz
    exact ⟨k,adj,off⟩
  · intro S hc
    have h := terminalCover hr (by omega : 8≤P.card) keep singles (S.image f) (by
      intro u hu v hv uv
      obtain ⟨a,rfl⟩ := onto u hu
      obtain ⟨b,rfl⟩ := onto v hv
      exact (hc a b uv).imp (fun h => mem_image.mpr ⟨a,h,rfl⟩) (fun h => mem_image.mpr ⟨b,h,rfl⟩))
    simpa [card_image_of_injective _ f.injective] using h

theorem smallCore {C : Circuit} (hm : Monotone2 C) (hr : Represents A C) (small : C.size ≤ 18) :
    ∃ P : Finset V, Retains P ∧ UnpairedUniversal C P ∧ Terminal C P ∧ P.card ≤ 9 := by
  obtain ⟨P,keep,single,t⟩ := terminalExists hr
  refine ⟨P,keep,single,t,?_⟩
  by_contra! large
  have := terminalCost hm hr large keep single t
  omega

end Crown9304

namespace Crown9304
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents Finset

def both (P : Finset V) : Finset (Fin 6) :=
  univ.filter fun j => slot j true ∈ P ∧ slot j false ∈ P

def basePick (P : Finset V) (j : Fin 6) : V :=
  if slot j true ∈ P then slot j true else slot j false

theorem baseLabel (P : Finset V) (j : Fin 6) : label (basePick P j)=j := by
  unfold basePick
  split <;> exact slotLabel _ _

theorem baseMem {P : Finset V} (k : Retains P) (j : Fin 6) : basePick P j ∈ P := by
  unfold basePick
  split
  · assumption
  · rename_i h
    have other := (k (slot j true)).resolve_left h
    simpa only [slotMate,Bool.not_true] using other

theorem baseOnly (P : Finset V) (j : Fin 6) (h : j ∉ both P) : mate (basePick P j) ∉ P := by
  simp only [both,mem_filter,mem_univ,true_and,not_and] at h
  unfold basePick
  split <;> simp_all [slotMate]

theorem pairMem {P : Finset V} {j : Fin 6} (h : j ∈ both P) (b : Bool) : slot j b ∈ P := by
  obtain ⟨_,up,lo⟩ := mem_filter.mp h
  cases b <;> assumption

def hasClique (C : Circuit) := ∃ f : Fin 6 → V, (∀ j, label (f j)=j) ∧
  ∀ i j, i≠j → (graph C).Adj (f i) (f j)

theorem colorClique {C : Circuit} (hr : Represents A C) {P : Finset V} (k : Retains P)
    (single : UnpairedUniversal C P) (color : Fin 6 → Bool)
    (compatible : ∀ i ∈ both P, ∀ j ∈ both P, i≠j → color i=color j →
      (graph C).Adj (slot i (color i)) (slot j (color j))) : hasClique C := by
  classical
  let f (j : Fin 6) := if j ∈ both P then slot j (color j) else basePick P j
  have lab (j) : label (f j)=j := by
    dsimp only [f]
    split
    · exact slotLabel _ _
    · exact baseLabel _ _
  have live (j) : f j ∈ P := by
    dsimp only [f]
    split
    · exact pairMem (by assumption) _
    · exact baseMem k _
  refine ⟨f,lab,?_⟩
  intro i j ne
  have dif : f i ≠ f j := fun eq => ne ((lab i).symm.trans ((congrArg label eq).trans (lab j)))
  by_cases hi : i ∈ both P
  swap
  · exact single (f i) (live i) (by simpa [f,hi] using baseOnly P i hi) (f j) (live j) dif.symm
  by_cases hj : j ∈ both P
  swap
  · exact (single (f j) (live j) (by simpa [f,hj] using baseOnly P j hj) (f i) (live i) dif).symm
  simp only [f,hi,hj,ite_true]
  by_cases eq : color i=color j
  · exact compatible i hi j hj ne eq
  · exact crossEdge hr ⟨by simpa only [slotSide] using eq,fun e => ne <| by
      have h := congrArg label e
      rw [slotLabel,labelMate,slotLabel] at h
      exact h.symm⟩

theorem cliqueSmall {C : Circuit} (hr : Represents A C) {P : Finset V} (k : Retains P)
    (single : UnpairedUniversal C P) (sz : (both P).card ≤ 2) : hasClique C := by
  have colorable : ∀ M : Finset (Fin 6), M.card≤2 → ∃ F : Finset (Fin 6),
      ∀ i ∈ M, ∀ j ∈ M, i≠j → decide (i∈F)≠decide (j∈F) := by decide
  obtain ⟨F,c⟩ := colorable _ sz
  exact colorClique hr k single (fun i => decide (i∈F))
    (fun i hi j hj ne e => False.elim (c i hi j hj ne e))

end Crown9304

namespace Crown9304
open PEqualNP.CircuitLowerBounds Finset

theorem countByPairs (P : Finset V) (k : Retains P) : (both P).card+6=P.card := by
  classical
  let first := basePick P
  let extra (j : Fin 6) := mate (first j)
  let B := (univ : Finset (Fin 6)).image first
  let E := (both P).image extra
  have baseLab (j : Fin 6) : label (first j)=j := baseLabel P j
  have extraLab (j : Fin 6) : label (extra j)=j := (labelMate _).trans (baseLab j)
  have injB : Function.Injective first := fun a b h => (baseLab a).symm.trans ((congrArg label h).trans (baseLab b))
  have injE : Function.Injective extra := fun a b h => (extraLab a).symm.trans ((congrArg label h).trans (extraLab b))
  have dis : Disjoint B E := by
    apply disjoint_left.mpr
    intro v vb ve
    obtain ⟨i,_,iv⟩ := mem_image.mp vb
    obtain ⟨j,_,jv⟩ := mem_image.mp ve
    have h := (baseLab i).symm.trans ((congrArg label (iv.trans jv.symm)).trans (extraLab j))
    subst j
    exact mateNot (first i) (jv.trans iv.symm)
  have eq : E ∪ B=P := by
    ext v
    constructor
    · intro h
      rcases mem_union.mp h with he|hb
      · obtain ⟨j,hj,rfl⟩ := mem_image.mp he
        change mate (basePick P j)∈P
        by_cases h : slot j true∈P
        · simpa [basePick,h,slotMate] using pairMem hj false
        · simpa [basePick,h,slotMate] using pairMem hj true
      · obtain ⟨j,_,rfl⟩ := mem_image.mp hb
        exact baseMem k j
    · intro hv
      let j := label v
      have pair := (sameLabel (first j) v).mp (baseLab j)
      rcases pair with h|h
      · apply mem_union_right
        exact mem_image.mpr ⟨j,mem_univ _,h.symm⟩
      · by_cases bothIn : j∈both P
        · apply mem_union_left
          exact mem_image.mpr ⟨j,bothIn,h.symm⟩
        · exact False.elim ((baseOnly P j bothIn) (h ▸ hv))
  calc
    _ = E.card+B.card := by simp [E,B,card_image_of_injective _ injE,card_image_of_injective _ injB]
    _ = (E ∪ B).card := (card_union_of_disjoint dis.symm).symm
    _ = P.card := congrArg Finset.card eq

end Crown9304

namespace Crown9304
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents Finset

theorem nineVertices {m : ℕ} {C : Circuit} (hm : Monotone2 C) (hr : Represents A C)
    (f : Fin m ↪ V) (size : m=9) (hedge : ∃ a b, (induced C f).Adj a b)
    (degree : ∀ i, 5 ≤ (induced C f).degree i)
    (universal : ∃ a, ∀ b, b ≠ a → (induced C f).Adj a b)
    (apart : ∀ i j, i ≠ j → ∃ z, (induced C f).Adj i z ∧ ¬(induced C f).Adj j z)
    (hcov : ∀ S, CoverPromise.IsVertexCover (induced C f) S → 6 ≤ S.card) : 19 ≤ C.size := by
  classical
  let G := induced C f
  obtain ⟨D,mono,sz,rep⟩ := extractInduced hm hr f hedge
  obtain ⟨a,allAdj⟩ := universal
  have lower := CrownCharge9304.saturationBound m 16 (by omega) G (fun i => (by decide : 3≤5).trans (degree i)) apart (by
    intro s extra T cover paid small _
    let I := (univ : Finset (Fin m)) \ T
    have covered := hcov T cover
    have total : I.card + T.card=m := by simpa [I] using card_sdiff_add_card_eq_card (subset_univ T)
    have inT : a∈T := by
      by_contra outside
      have sub : I ⊆ {a} := by
        intro i hi
        apply mem_singleton.mpr
        by_contra ne
        exact (mem_sdiff.mp hi).2 ((cover a i (allAdj i ne)).resolve_left outside)
      have few := card_le_card sub
      simp only [card_singleton] at few
      omega
    obtain ⟨b,hb,diff⟩ : ∃ b∈T, b≠a := by
      by_contra! only
      have sub : T ⊆ {a} := fun i hi => mem_singleton.mpr (only i hi)
      have few := card_le_card sub
      simp only [card_singleton] at few
      omega
    refine ⟨a,inT,b,hb,allAdj b diff,?_⟩
    have sub : I ⊆ G.neighborFinset a := by
      intro i hi
      apply (G.mem_neighborFinset a i).mpr
      apply allAdj
      rintro rfl
      exact (mem_sdiff.mp hi).2 inT
    change 2+extra ≤ (G.neighborFinset a ∩ I).card
    rw [inter_eq_right.mpr sub]
    omega) D.size D rfl mono rep
  omega

theorem nineTerminal {C : Circuit} (hm : Monotone2 C) (hr : Represents A C) {P : Finset V}
    (size : P.card=9) (keep : Retains P) (singles : UnpairedUniversal C P)
    (termP : Terminal C P) : 19 ≤ C.size := by
  classical
  let e := indexEquiv P
  let f := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ P))
  have memP (i) : f i ∈ P := (e i).property
  have onto (x : V) (h : x∈P) : ∃ j, f j=x := by
    refine ⟨e.symm ⟨x,h⟩,?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x,h⟩)
  have degree (i : Fin P.card) : 5 ≤ (induced C f).degree i := by
    let L := (univ : Finset (Fin 6)).erase (label (f i))
    have sub : L ⊆ ((induced C f).neighborFinset i).image (fun u => label (f u)) := by
      intro j hj
      obtain ⟨w,hw,adj,lab⟩ := otherLabelNeighbor hr keep singles (memP i) j (mem_erase.mp hj).1
      obtain ⟨k,rfl⟩ := onto w hw
      exact mem_image.mpr ⟨k,((induced C f).mem_neighborFinset i k).mpr adj,lab⟩
    have bound := (card_le_card sub).trans card_image_le
    have num : L.card=5 := by simp [L]
    rwa [num,SimpleGraph.card_neighborFinset_eq_degree] at bound
  have nonempty : ∃ a b, (induced C f).Adj a b := by
    let i : Fin P.card := ⟨0,by omega⟩
    have pos : 0 < ((induced C f).neighborFinset i).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; have := degree i; omega
    obtain ⟨v,hv⟩ := card_pos.mp pos
    exact ⟨i,v,((induced C f).mem_neighborFinset i v).mp hv⟩
  have lost : ∃ z : V, z∉P := by
    by_contra! all
    have eq : P=univ := eq_univ_of_forall all
    simp [eq] at size
  obtain ⟨z,hz⟩ := lost
  have mateIn := (keep z).resolve_left hz
  have every := singles (mate z) mateIn (by simpa only [mateMate] using hz)
  obtain ⟨a,ha⟩ := onto _ mateIn
  apply nineVertices hm hr f size nonempty degree
  · refine ⟨a,?_⟩
    intro b ne
    change (graph C).Adj (f a) (f b)
    rw [ha]
    exact every _ (memP b) (fun h => ne (f.injective (h.trans ha.symm)))
  · intro u v ne
    obtain ⟨z,hz,adj,off⟩ := terminalSep hr singles termP (memP u) (memP v)
      (fun h => ne (f.injective h))
    obtain ⟨k,rfl⟩ := onto z hz
    exact ⟨k,adj,off⟩
  · intro S hc
    have h := terminalCover hr (by omega : 8≤P.card) keep singles (S.image f) (by
      intro u hu v hv uv
      obtain ⟨a,rfl⟩ := onto u hu
      obtain ⟨b,rfl⟩ := onto v hv
      exact (hc a b uv).imp (fun h => mem_image.mpr ⟨a,h,rfl⟩) (fun h => mem_image.mpr ⟨b,h,rfl⟩))
    simpa [card_image_of_injective _ f.injective] using h
theorem cliqueNeeded {C : Circuit} (hm : Monotone2 C) (hr : Represents A C) (small : C.size≤18) :
    hasClique C := by
  obtain ⟨P,k,u,t,h⟩ := smallCore hm hr small
  have eight : P.card≤8 := by
    by_contra! large
    have := nineTerminal hm hr (by omega : P.card=9) k u t
    omega
  have count := countByPairs P k
  apply cliqueSmall hr k u
  omega

theorem shortThreshold {C : Circuit} (hm : Monotone2 C) (hr : Represents A C) (small : C.size≤18) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+6≤C.size ∧
      ∀ x : Fin 6 → Bool, D.eval (List.ofFn x)=decide (two x) := by
  obtain ⟨f,lab,cl⟩ := cliqueNeeded hm hr small
  exact cliqueTransfer hm hr f lab cl

end Crown9304

namespace ThresholdFive

def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

theorem zeroGate_canalizes :
    ∀ k : Fin 4,
      (∃ b c : Bool, ∀ a : Bool, zeroGate k a b = c) ∧
      (∃ a c : Bool, ∀ b : Bool, zeroGate k a b = c) := by
  decide

abbrev Formula (n : Nat) := BinaryTree (Sum (Fin n) Bool)

def formEval {n : Nat} : Formula n → (Fin n → Bool) → Bool
  | .nil, _ => false
  | .node (.inl i) _ _, x => x i
  | .node (.inr false) l r, x => formEval l x || formEval r x
  | .node (.inr true) l r, x => formEval l x && formEval r x

def singleInput {n : Nat} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)

def pairInput {n : Nat} (i j : Fin n) : Fin n → Bool :=
  fun k => decide (k = i ∨ k = j)

def formOcc {n : Nat} : Formula n → Fin n → Nat
  | .nil, _ => 0
  | .node (.inl j) _ _, i => if j = i then 1 else 0
  | .node (.inr _) l r, i => formOcc l i + formOcc r i

def formCut {n : Nat} (l r : Formula n) (i : Fin n) : Option Bool :=
  match formEval l (singleInput i), formEval r (singleInput i) with
  | true, false => some false
  | false, true => some true
  | _, _ => none

def formCuts {n : Nat} : Formula n → List (Fin n → Option Bool)
  | .nil => []
  | .node (.inl _) _ _ => []
  | .node (.inr false) l r => formCuts l ++ formCuts r
  | .node (.inr true) l r => formCut l r :: (formCuts l ++ formCuts r)

def formDegree {n : Nat} (t : Formula n) (i : Fin n) : Nat :=
  (formCuts t).countP fun c => (c i).isSome

theorem form_charge {n : Nat} (t : Formula n) (i : Fin n) :
    formDegree t i + (formEval t (singleInput i)).toNat ≤ formOcc t i := by
  induction t with
  | nil => simp [formDegree, formCuts, formEval, formOcc]
  | node a l r hl hr =>
    cases a with
    | inl j =>
      by_cases h : j = i <;>
        simp [formDegree, formCuts, formEval, formOcc, singleInput, h]
    | inr op =>
      cases op <;>
        cases el : formEval l (singleInput i) <;>
        cases er : formEval r (singleInput i) <;>
        simp [formDegree, formCuts, formEval, formOcc, formCut, el, er,
          List.countP_append] at * <;> omega

theorem form_pair_separator {n : Nat} (t : Formula n) (i j : Fin n)
    (hp : formEval t (pairInput i j) = true)
    (hi : formEval t (singleInput i) = false)
    (hj : formEval t (singleInput j) = false) :
    ∃ c ∈ formCuts t,
      (c i = some false ∧ c j = some true) ∨
      (c i = some true ∧ c j = some false) := by
  induction t with
  | nil => simp [formEval] at hp
  | node a l r hl hr =>
    cases a with
    | inl k =>
      simp [formEval, pairInput] at hp
      simp [formEval, singleInput] at hi hj
      rcases hp with hp | hp
      · exact (hi hp).elim
      · exact (hj hp).elim
    | inr op =>
      cases op with
      | false =>
        simp only [formEval, Bool.or_eq_true] at hp
        simp only [formEval, Bool.or_eq_false_iff] at hi hj
        rcases hp with hp | hp
        · obtain ⟨c, hc, hs⟩ := hl hp hi.1 hj.1
          exact ⟨c, by simp [formCuts, hc], hs⟩
        · obtain ⟨c, hc, hs⟩ := hr hp hi.2 hj.2
          exact ⟨c, by simp [formCuts, hc], hs⟩
      | true =>
        simp only [formEval, Bool.and_eq_true] at hp
        have liftL (hli : formEval l (singleInput i) = false)
            (hlj : formEval l (singleInput j) = false) :
            ∃ c ∈ formCuts (.node (.inr true) l r),
              (c i = some false ∧ c j = some true) ∨
              (c i = some true ∧ c j = some false) := by
          obtain ⟨c, hc, hs⟩ := hl hp.1 hli hlj
          exact ⟨c, by simp [formCuts, hc], hs⟩
        have liftR (hri : formEval r (singleInput i) = false)
            (hrj : formEval r (singleInput j) = false) :
            ∃ c ∈ formCuts (.node (.inr true) l r),
              (c i = some false ∧ c j = some true) ∨
              (c i = some true ∧ c j = some false) := by
          obtain ⟨c, hc, hs⟩ := hr hp.2 hri hrj
          exact ⟨c, by simp [formCuts, hc], hs⟩
        cases eli : formEval l (singleInput i) with
        | false =>
          cases elj : formEval l (singleInput j) with
          | false => exact liftL eli elj
          | true =>
            have erj : formEval r (singleInput j) = false := by
              simpa [formEval, elj] using hj
            cases eri : formEval r (singleInput i) with
            | false => exact liftR eri erj
            | true =>
              refine ⟨formCut l r, by simp [formCuts], Or.inr ?_⟩
              simp [formCut, eli, elj, eri, erj]
        | true =>
          have eri : formEval r (singleInput i) = false := by
            simpa [formEval, eli] using hi
          cases erj : formEval r (singleInput j) with
          | false => exact liftR eri erj
          | true =>
            have elj : formEval l (singleInput j) = false := by
              simpa [formEval, erj] using hj
            refine ⟨formCut l r, by simp [formCuts], Or.inl ?_⟩
            simp [formCut, eli, elj, eri, erj]

open scoped BigOperators

def cCube {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) : Finset (α → Bool) :=
  Fintype.piFinset fun a => if a ∈ s then {b a} else Finset.univ

theorem cCubeMember {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b f : α → Bool) :
    f ∈ cCube s b ↔ ∀ a ∈ s, f a = b a := by
  simp only [cCube, Fintype.mem_piFinset]
  constructor
  · intro h a ha
    simpa only [ite_eq_left ha, Finset.mem_singleton] using h a
  · intro h a
    by_cases ha : a ∈ s
    · simpa only [ite_eq_left ha, Finset.mem_singleton] using h a ha
    · simp only [ite_eq_right ha, Finset.mem_univ]

theorem cCubeCard {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) :
    (cCube s b).card = ∏ a : α, if a ∈ s then 1 else 2 := by
  rw [cCube, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro a ha
  by_cases hs : a ∈ s <;> simp [hs]

theorem cCubeVolume {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) :
    (cCube s b).card * 2 ^ s.card = 2 ^ Fintype.card α := by
  rw [cCubeCard]
  have hs : (∏ a : α, if a ∈ s then 2 else 1) = 2 ^ s.card := by simp
  rw [← hs, ← Finset.prod_mul_distrib]
  have he : (∏ a : α, (if a ∈ s then 1 else 2) * (if a ∈ s then 2 else 1)) =
      ∏ _a : α, 2 := by
    apply Finset.prod_congr rfl
    intro a ha
    by_cases h : a ∈ s <;> simp [h]
  rw [he]
  simp

theorem cCubeQuarter {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) (hs : s.card ≤ 2) :
    2 ^ Fintype.card α ≤ (cCube s b).card * 4 := by
  have hpow : 2 ^ s.card ≤ 4 := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hs
  calc
    2 ^ Fintype.card α = (cCube s b).card * 2 ^ s.card := (cCubeVolume s b).symm
    _ ≤ (cCube s b).card * 4 := Nat.mul_le_mul_left _ hpow

theorem cFiveSeparatedImpossible {α : Type*} [Fintype α] [DecidableEq α]
    (s : Fin 5 → Finset α) (b : Fin 5 → α → Bool)
    (small : ∀ i, (s i).card ≤ 2)
    (separates : ∀ i j, i ≠ j → ∃ a, a ∈ s i ∧ a ∈ s j ∧ b i a ≠ b j a) :
    False := by
  classical
  have hd : ((Finset.univ : Finset (Fin 5)) : Set (Fin 5)).PairwiseDisjoint
      (fun i => cCube (s i) (b i)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro f hfi hfj
    obtain ⟨a, hai, haj, hab⟩ := separates i j hij
    have hia := (cCubeMember (s i) (b i) f).mp hfi a hai
    have hja := (cCubeMember (s j) (b j) f).mp hfj a haj
    exact hab (hia.symm.trans hja)
  have upper : (∑ i : Fin 5, (cCube (s i) (b i)).card) ≤ 2 ^ Fintype.card α := by
    rw [← Finset.card_biUnion hd]
    have h := Finset.card_le_univ
      ((Finset.univ : Finset (Fin 5)).biUnion fun i => cCube (s i) (b i))
    simpa using h
  have lower : 5 * 2 ^ Fintype.card α ≤
      (∑ i : Fin 5, (cCube (s i) (b i)).card) * 4 := by
    calc
      5 * 2 ^ Fintype.card α = ∑ _i : Fin 5, 2 ^ Fintype.card α := by simp
      _ ≤ ∑ i : Fin 5, (cCube (s i) (b i)).card * 4 := by
        apply Finset.sum_le_sum
        intro i hi
        exact cCubeQuarter (s i) (b i) (small i)
      _ = (∑ i : Fin 5, (cCube (s i) (b i)).card) * 4 :=
        (Finset.sum_mul _ _ _).symm
  have hp : 0 < 2 ^ Fintype.card α := Nat.pow_pos (by decide)
  omega

theorem no_readtwice_five (t : Formula 5)
    (hocc : ∀ i, formOcc t i ≤ 2)
    (hs : ∀ i, formEval t (singleInput i) = false)
    (hp : ∀ i j, i ≠ j → formEval t (pairInput i j) = true) : False := by
  let L := formCuts t
  let s : Fin 5 → Finset (Fin L.length) := fun i =>
    Finset.univ.filter fun k => ((L.get k) i).isSome
  let b : Fin 5 → Fin L.length → Bool := fun i k => ((L.get k) i).getD false
  apply cFiveSeparatedImpossible s b
  · intro i
    have hcard : (s i).card = formDegree t i := by
      simpa [s, formDegree, L, List.ofFn_get] using
        (List.countP_ofFn (List.get L) (fun c => (c i).isSome)).symm
    rw [hcard]
    have hc := form_charge t i
    have ho := hocc i
    omega
  · intro i j hij
    obtain ⟨c, hc, hsep⟩ := form_pair_separator t i j (hp i j hij) (hs i) (hs j)
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hc
    change (formCuts t)[k.val] = c at hk
    rcases hsep with ⟨hci, hcj⟩ | ⟨hci, hcj⟩
    · refine ⟨k, ?_, ?_, ?_⟩ <;> simp [s, b, L, hk, hci, hcj]
    · refine ⟨k, ?_, ?_, ?_⟩ <;> simp [s, b, L, hk, hci, hcj]

section Generic
variable {α : Type} {β : Type}

def UC (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) : ℕ → (α → Prop) → α → Prop
  | 0, S, f => S f
  | t + 1, S, f => UC G A t S f ∨
      ∃ k a b, A k ∧ S a ∧ S b ∧ UC G A t (fun w => w = G k a b ∨ S w) f

theorem UC_monoS (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS G A t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS G A t _ _ f (fun w hw => hw.imp id (h w)) hu⟩

theorem UC_le {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t t' : ℕ} {S : α → Prop} {f : α}
    (h : t ≤ t') (hu : UC G A t S f) : UC G A t' S f := by
  induction h with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

theorem UC_gate {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t : ℕ} {S : α → Prop} {f : α}
    (k : Fin 4) (a b : α) (hk : A k) (ha : S a) (hb : S b)
    (hu : UC G A t (fun w => w = G k a b ∨ S w) f) : UC G A (t + 1) S f :=
  Or.inr ⟨k, a, b, hk, ha, hb, hu⟩

theorem UC_map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {A : Fin 4 → Prop} (e : α → β)
    (he : ∀ k a b, e (G k a b) = G' k (e a) (e b)) :
    ∀ (t : ℕ) (S : α → Prop) (S' : β → Prop) (f : α), (∀ w, S w → S' (e w)) →
      UC G A t S f → UC G' A t S' (e f)
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_map e he t S S' f h hu)
    · refine Or.inr ⟨k, e a, e b, hk, h a ha, h b hb, UC_map e he t _ _ f ?_ hu⟩
      intro w hw
      rcases hw with rfl | hw
      · exact Or.inl (he k a b)
      · exact Or.inr (h w hw)

def TR (G : Fin 4 → α → α → α) (C : Fin 4 → α → α → Prop) (ys : List α) (t : ℕ)
    (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 ys →
    (∀ s xs zs, List.Perm xs zs → P s xs → P s zs) →
    (∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) →
    P t ws

section Run
variable {G : Fin 4 → α → α → α} {C : Fin 4 → α → α → Prop} {ys : List α}

theorem TR.done : TR G C ys 0 ys := fun _ d _ _ => d

theorem TR.perm {s : ℕ} {xs zs : List α} (p : List.Perm xs zs) (h : TR G C ys s xs) :
    TR G C ys s zs := fun P d q st => q s xs zs p (h P d q st)

theorem TR.step {s : ℕ} {a b : α} {r : List α} (k : Fin 4) (u : ℕ) (hc : C k a b)
    (h : TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) :
    TR G C ys (s + 1) (a :: b :: r) := fun P d q st => st s a b r k u hc (h P d q st)

theorem TR.ind {P : ℕ → List α → Prop} {t : ℕ} {ws : List α} (h : TR G C ys t ws)
    (d : P 0 ys)
    (p : ∀ s xs zs, List.Perm xs zs → TR G C ys s xs → P s xs → P s zs)
    (st : ∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      TR G C ys s (List.replicate (u + 1) (G k a b) ++ r) →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) : P t ws :=
  (h (fun s xs => TR G C ys s xs ∧ P s xs) ⟨TR.done, d⟩
    (fun s xs zs hp hx => ⟨TR.perm hp hx.1, p s xs zs hp hx.1 hx.2⟩)
    (fun s a b r k u hc hx => ⟨TR.step k u hc hx.1, st s a b r k u hc hx.1 hx.2⟩)).2

theorem TR.inv {t : ℕ} {ws : List α} (h : TR G C ys t ws) :
    (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) := by
  refine TR.ind (P := fun t ws => (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r))) h
    ⟨fun _ => List.Perm.refl _, fun s hs => by omega⟩ ?_ ?_
  · intro s xs zs hp _ ih
    refine ⟨fun h0 => hp.symm.trans (ih.1 h0), fun s' hs => ?_⟩
    obtain ⟨k, u, a, b, r, hc, hq, hr⟩ := ih.2 s' hs
    exact ⟨k, u, a, b, r, hc, hp.symm.trans hq, hr⟩
  · intro s a b r k u hc hr _
    refine ⟨fun h0 => by omega, fun s' hs => ?_⟩
    have : s = s' := by omega
    subst this
    exact ⟨k, u, a, b, r, hc, List.Perm.refl _, hr⟩

theorem TR.len {t : ℕ} {ws : List α} (h : TR G C ys t ws) : ws.length ≤ t + ys.length := by
  refine TR.ind (P := fun t ws => ws.length ≤ t + ys.length) h (by simp) ?_ ?_
  · intro s xs zs hp _ ih
    rw [← hp.length_eq]; exact ih
  · intro s a b r k u _ _ ih
    simp only [List.length_append, List.length_replicate, List.length_cons] at ih ⊢
    omega

theorem TR.monoC {C' : Fin 4 → α → α → Prop} (hC : ∀ k a b, C k a b → C' k a b) {t : ℕ}
    {ws : List α} (h : TR G C ys t ws) : TR G C' ys t ws :=
  TR.ind (P := fun t ws => TR G C' ys t ws) h TR.done (fun _ _ _ hp _ ih => TR.perm hp ih)
    (fun _ _ _ _ k u hc _ ih => TR.step k u (hC _ _ _ hc) ih)

end Run

def strictC (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop) (I : α → Prop) :
    Fin 4 → α → α → Prop :=
  fun k a b => A k ∧ I a ∧ I b ∧ a ≠ b ∧ G k a b ≠ a ∧ G k a b ≠ b ∧ G k a b ≠ z

theorem normalize [DecidableEq α] (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop)
    (I : α → Prop) (hI : ∀ k a b, I a → I b → I (G k a b))
    (hz1 : ∀ k b, G k z b = z ∨ G k z b = b) (hz2 : ∀ k a, G k a z = z ∨ G k a z = a)
    (hd : ∀ k a, G k a a = z ∨ G k a a = a) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), (∀ w, S w → I w) → f ≠ z → UC G A t S f →
      ∃ t', t' ≤ t ∧ ∃ ws : List α, (∀ w ∈ ws, S w ∧ w ≠ z) ∧
        TR G (strictC G z A I) [f] t' ws
  | 0, S, f, _, hf, hu => ⟨0, le_rfl, [f], by simpa using ⟨hu, hf⟩, TR.done⟩
  | t + 1, S, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t S f hS hf hu
      exact ⟨t', by omega, ws, hws, hr⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t _ f (by
        rintro w (rfl | hw)
        · exact hI k a b (hS a ha) (hS b hb)
        · exact hS w hw) hf hu
      by_cases hg : S (G k a b)
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact hg
        · exact h
      by_cases hc : G k a b ∈ ws
      · have hgz : G k a b ≠ z := (hws _ hc).2
        have hga : G k a b ≠ a := fun h => hg (by rw [h]; exact ha)
        have hgb : G k a b ≠ b := fun h => hg (by rw [h]; exact hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hd k a with h | h
          · exact hgz h
          · exact hga h
        have haz : a ≠ z := by
          rintro rfl
          rcases hz1 k b with h | h
          · exact hgz h
          · exact hgb h
        have hbz : b ≠ z := by
          rintro rfl
          rcases hz2 k a with h | h
          · exact hgz h
          · exact hga h
        obtain ⟨u, hu1⟩ : ∃ u, List.count (G k a b) ws = u + 1 :=
          ⟨List.count (G k a b) ws - 1, by have := List.count_pos_iff.2 hc; omega⟩
        have hperm : ws.Perm (List.replicate (u + 1) (G k a b) ++ ws.filter (· ≠ G k a b)) := by
          rw [← hu1, ← List.filter_eq]
          have := List.filter_append_perm (fun x => decide (x = G k a b)) ws
          refine this.symm.trans ?_
          simp
        refine ⟨t' + 1, by omega, a :: b :: ws.filter (· ≠ G k a b), ?_,
          TR.step k u ⟨hk, hS a ha, hS b hb, hab, hga, hgb, hgz⟩ (TR.perm hperm hr)⟩
        intro w hw
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl | ⟨hw, hne⟩
        · exact ⟨ha, haz⟩
        · exact ⟨hb, hbz⟩
        · rcases (hws w hw).1 with h | h
          · exact absurd h hne
          · exact ⟨h, (hws w hw).2⟩
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact absurd hw hc
        · exact h

theorem TR.map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {C : Fin 4 → α → α → Prop}
    {C' : Fin 4 → β → β → Prop} (e : α → β) (he : ∀ k a b, e (G k a b) = G' k (e a) (e b))
    (hC : ∀ k a b, C k a b → C' k (e a) (e b)) {ys : List α} {t : ℕ} {ws : List α}
    (h : TR G C ys t ws) : TR G' C' (ys.map e) t (ws.map e) := by
  refine TR.ind (P := fun t ws => TR G' C' (ys.map e) t (ws.map e)) h TR.done
    (fun _ _ _ hp _ ih => TR.perm (hp.map e) ih) ?_
  intro s a b r k u hc _ ih
  rw [List.map_append, List.map_replicate, he] at ih
  exact TR.step k u (hC _ _ _ hc) ih

theorem TR.rel {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} (R : α → α → Prop)
    (hR : ∀ k a a' b b', R a a' → R b b' → R (G k a b) (G k a' b')) {ys : List α} {t : ℕ}
    {ws : List α} (h : TR G (fun k _ _ => A k) ys t ws) :
    ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws' := by
  refine TR.ind (P := fun t ws => ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws') h
    (fun ws' hw => ⟨ws', hw, TR.done⟩) ?_ ?_
  · intro s xs zs hp _ ih zs' hz
    obtain ⟨xs', hx, hp'⟩ := List.perm_comp_forall₂ hp hz
    obtain ⟨ys', hy, hr⟩ := ih xs' hx
    exact ⟨ys', hy, TR.perm hp' hr⟩
  · intro s a b r k u hc _ ih ws' hw
    obtain ⟨a', t1, ha, ht1, rfl⟩ := List.forall₂_cons_left_iff.1 hw
    obtain ⟨b', r', hb, hr', rfl⟩ := List.forall₂_cons_left_iff.1 ht1
    have h1 : List.Forall₂ R (List.replicate (u + 1) (G k a b) ++ r)
        (List.replicate (u + 1) (G k a' b') ++ r') := by
      refine List.rel_append ?_ hr'
      generalize u + 1 = n
      induction n with
      | zero => exact List.Forall₂.nil
      | succ n ih => exact List.Forall₂.cons (hR k a a' b b' ha hb) ih
    obtain ⟨ys', hy, hrun⟩ := ih _ h1
    exact ⟨ys', hy, TR.step k u hc hrun⟩

end Generic

abbrev BF := (Fin 5 → Bool) → Bool

def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)

def var (i : Fin 5) : BF := fun x => x i

def gM (k a b : ℕ) : ℕ :=
  match k with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)

def gN (k : Fin 4) (a b : ℕ) : ℕ := gM k.val a b

theorem gN_testBit (k : Fin 4) (a b i : ℕ) :
    (gN k a b).testBit i = zeroGate k (a.testBit i) (b.testBit i) := by
  fin_cases k <;>
    simp [gN, gM, zeroGate, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl

theorem gN_zero_left (k : Fin 4) (b : ℕ) : gN k 0 b = 0 ∨ gN k 0 b = b := by
  fin_cases k <;> simp [gN, gM]

theorem gN_zero_right (k : Fin 4) (a : ℕ) : gN k a 0 = 0 ∨ gN k a 0 = a := by
  fin_cases k <;> simp [gN, gM]

theorem gN_self (k : Fin 4) (a : ℕ) : gN k a a = 0 ∨ gN k a a = a := by
  fin_cases k <;> simp [gN, gM]

theorem gN_lt (k : Fin 4) (a b : ℕ) (ha : a < 1024) (hb : b < 1024) : gN k a b < 1024 := by
  apply Nat.lt_pow_two_of_testBit (n := 10)
  intro i hi
  have hp : (1024 : ℕ) ≤ 2 ^ i :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (show 0 < 2 by norm_num) hi)
  rw [gN_testBit, Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp)]
  fin_cases k <;> rfl

def enc {ρ : Type} (w : ρ → Bool) : List ρ → ℕ
  | [] => 0
  | p :: t => Nat.bit (w p) (enc w t)

theorem enc_testBit {ρ : Type} (w : ρ → Bool) : ∀ (l : List ρ) (j : ℕ),
    (enc w l).testBit j = (l.map w).getD j false
  | [], j => by simp [enc]
  | p :: t, 0 => by simp [enc]
  | p :: t, j + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit w t j]

theorem enc_gate {ρ : Type} (k : Fin 4) (a b : ρ → Bool) (l : List ρ) :
    enc (fun r => zeroGate k (a r) (b r)) l = gN k (enc a l) (enc b l) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [gN_testBit, enc_testBit, enc_testBit, enc_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    fin_cases k <;> rfl

theorem enc_gF (k : Fin 4) (a b : BF) (l : List (Fin 5 → Bool)) :
    enc (gF k a b) l = gN k (enc a l) (enc b l) := enc_gate k a b l

theorem enc_lt {ρ : Type} (w : ρ → Bool) (l : List ρ) : enc w l < 2 ^ l.length := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [enc_testBit, List.getD_eq_default _ _ (by simp; omega)]

theorem TRN_det {C : Fin 4 → ℕ → ℕ → Prop} {y : ℕ} {s : ℕ} {ws : List ℕ}
    (h : TR gN C [y] s ws) (i j : ℕ) :
    (∀ t ∈ ws, t.testBit i = t.testBit j) → y.testBit i = y.testBit j := by
  refine TR.ind (P := fun _ ws => (∀ t ∈ ws, t.testBit i = t.testBit j) →
    y.testBit i = y.testBit j) h (fun h => h y (by simp)) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht, gN_testBit, gN_testBit, hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

theorem TRN_zp {C : Fin 4 → ℕ → ℕ → Prop} {y : ℕ} {s : ℕ} {ws : List ℕ}
    (h : TR gN C [y] s ws) (i : ℕ) :
    (∀ t ∈ ws, t.testBit i = false) → y.testBit i = false := by
  refine TR.ind (P := fun _ ws => (∀ t ∈ ws, t.testBit i = false) →
    y.testBit i = false) h (fun h => h y (by simp)) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht, gN_testBit, hz a (by simp), hz b (by simp)]
      fin_cases k <;> rfl
    · exact hz t (by simp [ht])

def sg (p t : ℕ) : ℕ := if t.testBit p then t ^^^ 1023 else t

def covB (f : ℕ → ℕ) (ws : List ℕ) : Bool :=
  ws.foldl (fun acc t => acc ||| f t) 0 &&& 1008 == 1008

def cov (ws : List ℕ) : Bool :=
  covB id ws && covB (sg 0) ws && covB (sg 1) ws && covB (sg 2) ws && covB (sg 3) ws

theorem fold_bit (f : ℕ → ℕ) (i : ℕ) : ∀ (ws : List ℕ) (a : ℕ),
    (ws.foldl (fun acc t => acc ||| f t) a).testBit i =
      (a.testBit i || ws.any fun t => (f t).testBit i)
  | [], a => by simp
  | t :: ws, a => by
    rw [List.foldl_cons, fold_bit f i ws, Nat.testBit_or, List.any_cons, Bool.or_assoc]

theorem covB_iff (f : ℕ → ℕ) (ws : List ℕ) :
    covB f ws = true ↔
      ∀ i, (1008 : ℕ).testBit i = true → ∃ t ∈ ws, (f t).testBit i = true := by
  unfold covB
  rw [beq_iff_eq]
  constructor
  · intro h i hi
    have h1 := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.and_true, fold_bit, Nat.zero_testBit, Bool.false_or,
      List.any_eq_true] at h1
    exact h1
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : (1008 : ℕ).testBit i
    · simp
    · rw [Bool.and_true, fold_bit, Nat.zero_testBit, Bool.false_or, List.any_eq_true]
      exact h i hi

theorem sg_bit (p t i : ℕ) (hi : (1008 : ℕ).testBit i = true) :
    (sg p t).testBit i = (t.testBit i != t.testBit p) := by
  have h1023 : (1023 : ℕ).testBit i = true := by
    have hlt : i < 10 := by
      by_contra hc
      have h2 : (1008 : ℕ) < 2 ^ i :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hc))
      rw [Nat.testBit_lt_two_pow h2] at hi
      exact Bool.noConfusion hi
    interval_cases i <;> rfl
  have e : (sg p t).testBit i =
      if t.testBit p = true then (t.testBit i ^^ true) else t.testBit i := by
    unfold sg
    split_ifs with h
    · rw [Nat.testBit_xor, h1023]
    · rfl
  rw [e]
  cases t.testBit i <;> cases t.testBit p <;> rfl

theorem TRN_cov {C : Fin 4 → ℕ → ℕ → Prop} {s : ℕ} {ws : List ℕ}
    (h : TR gN C [1008] s ws) : cov ws = true := by
  have hd := TRN_det h
  have hz := TRN_zp h
  have k1 : ∀ i, (1008 : ℕ).testBit i = true → ∃ t ∈ ws, (id t).testBit i = true := by
    intro i hi
    by_contra hc
    have h1 : ∀ t ∈ ws, t.testBit i = false := by
      intro t ht
      by_contra h2
      exact hc ⟨t, ht, by simpa using h2⟩
    rw [hz i h1] at hi
    exact Bool.noConfusion hi
  have k2 : ∀ p, (1008 : ℕ).testBit p = false → ∀ i, (1008 : ℕ).testBit i = true →
      ∃ t ∈ ws, (sg p t).testBit i = true := by
    intro p hp i hi
    by_contra hc
    have h1 : ∀ t ∈ ws, t.testBit i = t.testBit p := by
      intro t ht
      by_contra h2
      refine hc ⟨t, ht, ?_⟩
      rw [sg_bit p t i hi]
      simpa using h2
    rw [hd i p h1, hp] at hi
    exact Bool.noConfusion hi
  simp only [cov, Bool.and_eq_true, covB_iff]
  exact ⟨⟨⟨⟨k1, k2 0 (by decide)⟩, k2 1 (by decide)⟩, k2 2 (by decide)⟩, k2 3 (by decide)⟩

def tryG (g a b : ℕ) (f : ℕ → Bool) : Bool :=
  match g with
  | 0 => false
  | g' + 1 => g' + 1 != a && g' + 1 != b && f (g' + 1)

theorem tryG_iff (g a b : ℕ) (f : ℕ → Bool) :
    tryG g a b f = true ↔ g ≠ 0 ∧ g ≠ a ∧ g ≠ b ∧ f g = true := by
  cases g <;> simp [tryG, and_assoc]

def search : ℕ → List ℕ → Bool
  | 0, ws => decide (ws = [1008])
  | s + 1, ws =>
    decide (ws.length ≤ s + 2) && cov ws &&
      ws.dedup.any fun a => ws.dedup.any fun b => decide (a < b) &&
        [0, 1, 2, 3].any fun k =>
          tryG (gM k a b) a b fun g =>
            (List.range (s + 3 - ws.length)).any fun u =>
              search s (List.replicate (u + 1) g ++ (ws.erase a).erase b)

theorem search_succ (s : ℕ) (ws : List ℕ) :
    search (s + 1) ws = true ↔ ws.length ≤ s + 2 ∧ cov ws = true ∧
      ∃ a ∈ ws, ∃ b ∈ ws, a < b ∧ ∃ k, k < 4 ∧ gM k a b ≠ 0 ∧ gM k a b ≠ a ∧ gM k a b ≠ b ∧
        ∃ u, u < s + 3 - ws.length ∧
          search s (List.replicate (u + 1) (gM k a b) ++ (ws.erase a).erase b) = true := by
  simp only [search, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_dedup,
    tryG_iff, List.mem_range, and_assoc]
  constructor
  · rintro ⟨h1, h2, a, ha, b, hb, hab, k, hk, h3⟩
    refine ⟨h1, h2, a, ha, b, hb, hab, k, ?_, h3⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  · rintro ⟨h1, h2, a, ha, b, hb, hab, k, hk, h3⟩
    refine ⟨h1, h2, a, ha, b, hb, hab, k, ?_, h3⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

theorem cov_perm {xs zs : List ℕ} (hp : xs.Perm zs) (h : cov xs = true) : cov zs = true := by
  simp only [cov, Bool.and_eq_true, covB_iff] at h ⊢
  have key : ∀ f : ℕ → ℕ,
      (∀ i, (1008 : ℕ).testBit i = true → ∃ t ∈ xs, (f t).testBit i = true) →
      ∀ i, (1008 : ℕ).testBit i = true → ∃ t ∈ zs, (f t).testBit i = true :=
    fun f hf i hi => let ⟨t, ht, h3⟩ := hf i hi; ⟨t, hp.mem_iff.1 ht, h3⟩
  exact ⟨⟨⟨⟨key _ h.1.1.1.1, key _ h.1.1.1.2⟩, key _ h.1.1.2⟩, key _ h.1.2⟩, key _ h.2⟩

theorem search_perm : ∀ (s : ℕ) (xs zs : List ℕ), xs.Perm zs → search s xs = true →
    search s zs = true
  | 0, xs, zs, hp, h => by
    simp only [search, decide_eq_true_eq] at h ⊢
    subst h
    exact List.perm_singleton.1 hp.symm
  | s + 1, xs, zs, hp, h => by
    rw [search_succ] at h ⊢
    obtain ⟨h1, h2, a, ha, b, hb, hab, k, hk, h3, h4, h5, u, hu, h6⟩ := h
    refine ⟨hp.length_eq ▸ h1, cov_perm hp h2, a, hp.mem_iff.1 ha, b, hp.mem_iff.1 hb, hab, k,
      hk, h3, h4, h5, u, hp.length_eq ▸ hu, ?_⟩
    exact search_perm s _ _ (List.Perm.append_left _ ((hp.erase a).erase b)) h6

theorem gM_swap (k a b : ℕ) (hk : k < 4) :
    ∃ k', k' < 4 ∧ gM k' b a = gM k a b := by
  interval_cases k
  · exact ⟨0, by omega, by simp [gM, Nat.and_comm]⟩
  · exact ⟨1, by omega, by simp [gM, Nat.or_comm]⟩
  · exact ⟨3, by omega, by simp [gM, Nat.and_comm]⟩
  · exact ⟨2, by omega, by simp [gM, Nat.and_comm]⟩

abbrev NR (s : ℕ) (ws : List ℕ) : Prop :=
  TR gN (strictC gN 0 (fun _ => True) fun t => t < 1024) [1008] s ws

theorem run_search {s : ℕ} {ws : List ℕ} (h : NR s ws) : search s ws = true := by
  refine TR.ind (P := fun s ws => search s ws = true) h (by simp [search]) ?_ ?_
  · intro s xs zs hp _ ih
    exact search_perm s xs zs hp ih
  · intro s a b r k u hc hr ih
    have hrun := TR.step k u hc hr
    obtain ⟨-, -, -, hab, hga, hgb, hgz⟩ := hc
    have hlen := TR.len hr
    simp only [List.length_append, List.length_replicate, List.length_singleton] at hlen
    rw [search_succ]
    refine ⟨by have := TR.len hrun; simpa using this, TRN_cov hrun, ?_⟩
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · refine ⟨a, by simp, b, by simp, hlt, k.val, k.isLt, hgz, hga, hgb, u, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · have : ((a :: b :: r).erase a).erase b = r := by simp
        rw [this]
        exact ih
    · obtain ⟨k', hk', he⟩ := gM_swap k.val a b k.isLt
      have he' : gM k' b a = gN k a b := he
      refine ⟨b, by simp, a, by simp, hlt, k', hk', by rw [he']; exact hgz, by rw [he']; exact hgb,
        by rw [he']; exact hga, u, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · rw [he']
        have : ((a :: b :: r).erase b).erase a = r := by
          rw [List.erase_cons_tail (by simpa using hab), List.erase_cons_head,
            List.erase_cons_head]
        rw [this]
        exact ih

def bperm (rho : List ℕ) (t : ℕ) : ℕ := enc (fun i => t.testBit i) rho

theorem bperm_gN (rho : List ℕ) (k : Fin 4) (a b : ℕ) :
    bperm rho (gN k a b) = gN k (bperm rho a) (bperm rho b) := by
  unfold bperm
  rw [← enc_gate]
  congr 1
  funext i
  exact gN_testBit k a b i

theorem NR_perm (rho : List ℕ) (hlen : rho.length = 10)
    (hinv : ∀ t, t < 1024 → bperm rho (bperm rho t) = t) (h0 : bperm rho 0 = 0)
    (h1008 : bperm rho 1008 = 1008) {s : ℕ} {ws : List ℕ} (h : NR s ws) :
    NR s (ws.map (bperm rho)) := by
  have hlt : ∀ t, bperm rho t < 1024 := fun t => by
    have := enc_lt (fun i => t.testBit i) rho
    rw [hlen] at this
    exact this
  have hinj : ∀ a b, a < 1024 → b < 1024 → bperm rho a = bperm rho b → a = b := by
    intro a b ha hb he
    rw [← hinv a ha, ← hinv b hb, he]
  have h1 := TR.map (C' := strictC gN 0 (fun _ => True) fun t => t < 1024) (bperm rho)
    (bperm_gN rho) (by
      rintro k a b ⟨hk, ha, hb, hab, hga, hgb, hgz⟩
      have hg := gN_lt k a b ha hb
      refine ⟨hk, hlt a, hlt b, fun e => hab (hinj a b ha hb e), ?_, ?_, ?_⟩
      · rw [← bperm_gN]; exact fun e => hga (hinj _ _ hg ha e)
      · rw [← bperm_gN]; exact fun e => hgb (hinj _ _ hg hb e)
      · rw [← bperm_gN, ← h0]; exact fun e => hgz (hinj _ _ hg (by norm_num) e)) h
  simp only [List.map_cons, List.map_nil, h1008] at h1
  exact h1

def mk (m0 m1 m2 m3 : ℕ) : List ℕ :=
  List.replicate m0 113 ++ List.replicate m1 402 ++ List.replicate m2 676 ++ List.replicate m3 840

theorem mk_perm (ws : List ℕ) (h : ∀ w ∈ ws, w = 113 ∨ w = 402 ∨ w = 676 ∨ w = 840) :
    ws.Perm (mk (ws.count 113) (ws.count 402) (ws.count 676) (ws.count 840)) := by
  rw [List.perm_iff_count]
  intro a
  simp only [mk, List.count_append, List.count_replicate]
  by_cases h0 : a = 113
  · subst h0; simp
  by_cases h1 : a = 402
  · subst h1; simp
  by_cases h2 : a = 676
  · subst h2; simp
  by_cases h3 : a = 840
  · subst h3; simp
  have : a ∉ ws := fun hm => by rcases h a hm with h | h | h | h <;> contradiction
  simp [List.count_eq_zero_of_not_mem this, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3]

def Good (s m0 m1 m2 m3 : ℕ) : Prop := ∃ ws : List ℕ, ws.Perm (mk m0 m1 m2 m3) ∧ NR s ws

def rho01 : List ℕ := [1, 0, 2, 3, 4, 7, 8, 5, 6, 9]

def rho12 : List ℕ := [0, 2, 1, 3, 5, 4, 6, 7, 9, 8]

def rho23 : List ℕ := [0, 1, 3, 2, 4, 6, 5, 8, 7, 9]

theorem inv01 : ∀ t, t < 1024 → bperm rho01 (bperm rho01 t) = t := by decide +kernel

theorem inv12 : ∀ t, t < 1024 → bperm rho12 (bperm rho12 t) = t := by decide +kernel

theorem inv23 : ∀ t, t < 1024 → bperm rho23 (bperm rho23 t) = t := by decide +kernel

theorem good01 {s m0 m1 m2 m3 : ℕ} (h : Good s m0 m1 m2 m3) : Good s m1 m0 m2 m3 := by
  obtain ⟨ws, hp, hr⟩ := h
  refine ⟨ws.map (bperm rho01), (hp.map _).trans ?_,
    NR_perm rho01 rfl inv01 (by decide) (by decide) hr⟩
  have e1 : bperm rho01 113 = 402 := by decide
  have e2 : bperm rho01 402 = 113 := by decide
  have e3 : bperm rho01 676 = 676 := by decide
  have e4 : bperm rho01 840 = 840 := by decide
  simp only [mk, List.map_append, List.map_replicate, e1, e2, e3, e4]
  rw [List.perm_iff_count]
  intro a
  simp only [List.count_append, List.count_replicate]
  omega

theorem good12 {s m0 m1 m2 m3 : ℕ} (h : Good s m0 m1 m2 m3) : Good s m0 m2 m1 m3 := by
  obtain ⟨ws, hp, hr⟩ := h
  refine ⟨ws.map (bperm rho12), (hp.map _).trans ?_,
    NR_perm rho12 rfl inv12 (by decide) (by decide) hr⟩
  have e1 : bperm rho12 113 = 113 := by decide
  have e2 : bperm rho12 402 = 676 := by decide
  have e3 : bperm rho12 676 = 402 := by decide
  have e4 : bperm rho12 840 = 840 := by decide
  simp only [mk, List.map_append, List.map_replicate, e1, e2, e3, e4]
  rw [List.perm_iff_count]
  intro a
  simp only [List.count_append, List.count_replicate]
  omega

theorem good23 {s m0 m1 m2 m3 : ℕ} (h : Good s m0 m1 m2 m3) : Good s m0 m1 m3 m2 := by
  obtain ⟨ws, hp, hr⟩ := h
  refine ⟨ws.map (bperm rho23), (hp.map _).trans ?_,
    NR_perm rho23 rfl inv23 (by decide) (by decide) hr⟩
  have e1 : bperm rho23 113 = 113 := by decide
  have e2 : bperm rho23 402 = 402 := by decide
  have e3 : bperm rho23 676 = 840 := by decide
  have e4 : bperm rho23 840 = 676 := by decide
  simp only [mk, List.map_append, List.map_replicate, e1, e2, e3, e4]
  rw [List.perm_iff_count]
  intro a
  simp only [List.count_append, List.count_replicate]
  omega

theorem good_sorted (s : ℕ) : ∀ (n m0 m1 m2 m3 : ℕ), m1 + 2 * m2 + 3 * m3 ≤ n →
    Good s m0 m1 m2 m3 →
    ∃ a b c d, d ≤ c ∧ c ≤ b ∧ b ≤ a ∧ a + b + c + d = m0 + m1 + m2 + m3 ∧ Good s a b c d
  | 0, m0, m1, m2, m3, hn, h => ⟨m0, m1, m2, m3, by omega, by omega, by omega, rfl, h⟩
  | n + 1, m0, m1, m2, m3, hn, h => by
    by_cases h1 : m1 ≤ m0
    · by_cases h2 : m2 ≤ m1
      · by_cases h3 : m3 ≤ m2
        · exact ⟨m0, m1, m2, m3, h3, h2, h1, rfl, h⟩
        · obtain ⟨a, b, c, d, q1, q2, q3, q4, q5⟩ :=
            good_sorted s n m0 m1 m3 m2 (by omega) (good23 h)
          exact ⟨a, b, c, d, q1, q2, q3, by omega, q5⟩
      · obtain ⟨a, b, c, d, q1, q2, q3, q4, q5⟩ :=
          good_sorted s n m0 m2 m1 m3 (by omega) (good12 h)
        exact ⟨a, b, c, d, q1, q2, q3, by omega, q5⟩
    · obtain ⟨a, b, c, d, q1, q2, q3, q4, q5⟩ :=
        good_sorted s n m1 m0 m2 m3 (by omega) (good01 h)
      exact ⟨a, b, c, d, q1, q2, q3, by omega, q5⟩

def searchS (s : ℕ) : Bool :=
  (List.range (s + 2)).any fun m0 => (List.range (m0 + 1)).any fun m1 =>
    (List.range (m1 + 1)).any fun m2 => (List.range (m2 + 1)).any fun m3 =>
      search s (mk m0 m1 m2 m3)

theorem run_searchS {s : ℕ} {ws : List ℕ} (h : NR s ws)
    (hw : ∀ w ∈ ws, w = 113 ∨ w = 402 ∨ w = 676 ∨ w = 840) : searchS s = true := by
  have hp := mk_perm ws hw
  have hl := TR.len h
  rw [hp.length_eq] at hl
  simp only [mk, List.length_append, List.length_replicate, List.length_singleton] at hl
  obtain ⟨a, b, c, d, q1, q2, q3, q4, ws', hp', hr'⟩ :=
    good_sorted s _ _ _ _ _ le_rfl ⟨ws, hp, h⟩
  have hs := search_perm s _ _ hp' (run_search hr')
  simp only [searchS, List.any_eq_true, List.mem_range]
  exact ⟨a, by omega, b, by omega, c, by omega, d, by omega, hs⟩

set_option maxRecDepth 100000 in
theorem searchS_false : (List.range 7).all (fun s => !searchS s) = true := by
  decide +kernel

theorem U4 (ι : Fin 4 → Fin 5) (hι : Function.Injective ι) (F : BF)
    (hs : ∀ j, F (singleInput (ι j)) = false)
    (hp : ∀ j j', j ≠ j' → F (pairInput (ι j) (ι j')) = true) :
    ¬ UC gF (fun _ => True) 6 (fun w => ∃ j, w = var (ι j)) F := by
  intro hu
  let rows : List (Fin 5 → Bool) := [singleInput (ι 0), singleInput (ι 1), singleInput (ι 2),
    singleInput (ι 3), pairInput (ι 0) (ι 1), pairInput (ι 0) (ι 2), pairInput (ι 0) (ι 3),
    pairInput (ι 1) (ι 2), pairInput (ι 1) (ι 3), pairInput (ι 2) (ι 3)]
  have hF : enc F rows = 1008 := by
    simp only [rows, enc, hs, hp 0 1 (by decide), hp 0 2 (by decide), hp 0 3 (by decide),
      hp 1 2 (by decide), hp 1 3 (by decide), hp 2 3 (by decide)]
    rfl
  have hv : ∀ j, enc (var (ι j)) rows = 113 ∨ enc (var (ι j)) rows = 402 ∨
      enc (var (ι j)) rows = 676 ∨ enc (var (ι j)) rows = 840 := by
    intro j
    fin_cases j <;>
      simp [rows, enc, var, singleInput, pairInput, hι.eq_iff, Nat.bit]
  have hu2 : UC gN (fun _ => True) 6
      (fun w => w = 113 ∨ w = 402 ∨ w = 676 ∨ w = 840) (enc F rows) :=
    UC_map (fun w => enc w rows) (fun k a b => enc_gF k a b rows) 6 _ _ F
      (by rintro w ⟨j, rfl⟩; exact hv j) hu
  rw [hF] at hu2
  obtain ⟨t', ht, ws, hws, hr⟩ := normalize gN 0 (fun _ => True) (fun t => t < 1024) gN_lt
    gN_zero_left gN_zero_right gN_self 6 _ 1008
    (by rintro w (rfl | rfl | rfl | rfl) <;> norm_num) (by decide) hu2
  have h1 := run_searchS hr fun w hw => (hws w hw).1
  have h2 := searchS_false
  rw [List.all_eq_true] at h2
  have h3 := h2 t' (List.mem_range.2 (by omega))
  rw [h1] at h3
  exact Bool.noConfusion h3

def zF : BF := fun _ => false

def rst (p : Fin 5) (a : BF) : BF := fun x => a (Function.update x p false)

def ThrL (V : Fin 5 → Prop) (F : BF) : Prop :=
  (∀ i, V i → F (singleInput i) = false) ∧
    ∀ i j, V i → V j → i ≠ j → F (pairInput i j) = true

theorem gF_zero_left (k : Fin 4) (b : BF) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_right (k : Fin 4) (a : BF) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_self (k : Fin 4) (a : BF) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_zero (k : Fin 4) : gF k zF zF = zF := by
  fin_cases k <;> exact funext fun x => by simp [gF, zF, zeroGate]

theorem upd_single {i p : Fin 5} (h : i ≠ p) :
    Function.update (singleInput i) p false = singleInput i := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [singleInput, Ne.symm h]
  · simp [Function.update_of_ne hm]

theorem upd_pair {i j p : Fin 5} (hi : i ≠ p) (hj : j ≠ p) :
    Function.update (pairInput i j) p false = pairInput i j := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [pairInput, Ne.symm hi, Ne.symm hj]
  · simp [Function.update_of_ne hm]

theorem rst_var_self (p : Fin 5) : rst p (var p) = zF :=
  funext fun x => by simp [rst, var, zF]

theorem rst_var_ne {i p : Fin 5} (h : i ≠ p) : rst p (var i) = var i :=
  funext fun x => by simp [rst, var, Function.update_of_ne h]

theorem var_inj {i j : Fin 5} (h : var i = var j) : i = j := by
  have := congrFun h (singleInput i)
  exact (by simpa [var, singleInput] using this : j = i).symm

theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 5 → Bool) :
    (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x' := by
  refine TR.ind (P := fun _ ws => (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x') h
    (fun h => h) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]
      show zeroGate k (a x) (b x) = zeroGate k (a x') (b x')
      rw [hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

def dcount (p : Fin 5) (ws : List BF) : ℕ := ws.countP fun w => decide (rst p w = zF)

theorem dcount_cons (p : Fin 5) (a : BF) (l : List BF) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]

theorem dcount_rep (p : Fin 5) (n : ℕ) (g : BF) (r : List BF) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

theorem pot_dead {A : Fin 4 → Prop} (p : Fin 5) {F : BF} (hF : rst p F ≠ zF) {s : ℕ}
    {ws : List BF} (h : TR gF (fun k _ _ => A k) [F] s ws) :
    dcount p ws ≤ s ∧ ∀ S : BF → Prop, (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) →
      UC gF A (s - dcount p ws) S (rst p F) := by
  refine TR.ind (P := fun s ws => dcount p ws ≤ s ∧ ∀ S : BF → Prop,
    (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) → UC gF A (s - dcount p ws) S (rst p F)) h ?_ ?_ ?_
  · refine ⟨by simp [dcount, hF], fun S hS => ?_⟩
    have : dcount p [F] = 0 := by simp [dcount, hF]
    rw [this]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dcount p zs = dcount p xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u hk _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : rst p (gF k a b) = gF k (rst p a) (rst p b) := rfl
    rw [dcount_rep] at ih1 ih2
    rw [dcount_cons, dcount_cons]
    have hmem : ∀ (S : BF → Prop), (∀ w ∈ a :: b :: r, rst p w ≠ zF → S (rst p w)) →
        ∀ w ∈ r, rst p w ≠ zF → S (rst p w) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : rst p a = zF <;> by_cases hb : rst p b = zF
    · have hgz : rst p (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : rst p (gF k a b) = rst p b := by
          rcases gF_zero_left k (rst p b) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : rst p (gF k a b) = rst p a := by
          rcases gF_zero_right k (rst p a) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gF k (rst p a) (rst p b) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (rst p a) (rst p b) hk (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2

theorem ex_third : ∀ p q : Fin 5, ∃ r, r ≠ p ∧ r ≠ q := by decide

theorem thr_rst {F : BF} (hF : ThrL (fun _ => True) F) (p : Fin 5) :
    (∀ j, rst p F (singleInput (p.succAbove j)) = false) ∧
    (∀ j j', j ≠ j' → rst p F (pairInput (p.succAbove j) (p.succAbove j')) = true) := by
  refine ⟨fun j => ?_, fun j j' hj => ?_⟩
  · show F (Function.update (singleInput (p.succAbove j)) p false) = false
    rw [upd_single (Fin.succAbove_ne p j)]
    exact hF.1 _ trivial
  · show F (Function.update (pairInput (p.succAbove j) (p.succAbove j')) p false) = true
    rw [upd_pair (Fin.succAbove_ne p j) (Fin.succAbove_ne p j')]
    exact hF.2 _ _ trivial trivial fun h => hj (Fin.succAbove_right_injective h)

theorem thr_rst_ne {F : BF} (hF : ThrL (fun _ => True) F) (p : Fin 5) : rst p F ≠ zF := by
  intro h
  have := (thr_rst hF p).2 0 1 (by decide)
  rw [h] at this
  exact Bool.noConfusion this

theorem U5T {F : BF} (hF : ThrL (fun _ => True) F) {s : ℕ} {ws : List BF}
    (h : TR gF (fun _ _ _ => True) [F] s ws) (hw : ∀ w ∈ ws, ∃ i, w = var i) : 9 ≤ s := by
  rcases s with _ | s
  · have hp := (TR.inv h).1 rfl
    obtain ⟨i, hi⟩ := hw F (hp.mem_iff.2 (by simp))
    have := hF.1 i trivial
    rw [hi] at this
    simp [var, singleInput] at this
  · obtain ⟨k, u, a, b, r, -, hp, hr⟩ := (TR.inv h).2 s rfl
    obtain ⟨p, rfl⟩ := hw a (hp.mem_iff.2 (by simp))
    obtain ⟨q, rfl⟩ := hw b (hp.mem_iff.2 (by simp))
    have hcnt : dcount p ws = dcount p (var p :: var q :: r) := hp.countP_eq _
    have key : 2 ≤ dcount p ws := by
      rw [hcnt, dcount_cons, dcount_cons]
      by_cases hpq : p = q
      · subst hpq; simp [rst_var_self]
      by_cases hmem : var p ∈ r
      · have : 1 ≤ dcount p r := by
          unfold dcount
          exact List.countP_pos_iff.2 ⟨var p, hmem, by simp [rst_var_self]⟩
        simp only [rst_var_self, ite_true]
        omega
      exfalso
      have hrv : ∀ w ∈ r, ∃ i, i ≠ p ∧ w = var i := by
        intro w hw'
        obtain ⟨i, hi⟩ := hw w (hp.mem_iff.2 (by simp [hw']))
        refine ⟨i, ?_, hi⟩
        rintro rfl
        exact hmem (hi ▸ hw')
      obtain ⟨β, c, hβ⟩ := (zeroGate_canalizes k).1
      cases β
      · obtain ⟨r₀, hr1, hr2⟩ := ex_third p q
        have hd := TRF_det hr (pairInput p r₀) (singleInput r₀) (by
          intro w hw'
          rcases List.mem_append.1 hw' with hw' | hw'
          · rw [List.eq_of_mem_replicate hw']
            have e1 : var q (pairInput p r₀) = false := by
              simp [var, pairInput, Ne.symm hpq, Ne.symm hr2]
            have e2 : var q (singleInput r₀) = false := by simp [var, singleInput, Ne.symm hr2]
            show zeroGate k (var p _) (var q _) = zeroGate k (var p _) (var q _)
            rw [e1, e2, hβ, hβ]
          · obtain ⟨i, hi, rfl⟩ := hrv w hw'
            simp [var, pairInput, singleInput, hi]) F (by simp)
        rw [hF.1 r₀ trivial, hF.2 p r₀ trivial trivial (Ne.symm hr1)] at hd
        exact Bool.noConfusion hd
      · have hd := TRF_det hr (pairInput p q) (singleInput q) (by
          intro w hw'
          rcases List.mem_append.1 hw' with hw' | hw'
          · rw [List.eq_of_mem_replicate hw']
            have e1 : var q (pairInput p q) = true := by simp [var, pairInput]
            have e2 : var q (singleInput q) = true := by simp [var, singleInput]
            show zeroGate k (var p _) (var q _) = zeroGate k (var p _) (var q _)
            rw [e1, e2, hβ, hβ]
          · obtain ⟨i, hi, rfl⟩ := hrv w hw'
            simp [var, pairInput, singleInput, hi]) F (by simp)
        rw [hF.1 q trivial, hF.2 p q trivial trivial hpq] at hd
        exact Bool.noConfusion hd
    obtain ⟨h1, h2⟩ := pot_dead p (thr_rst_ne hF p) h
    have h3 := h2 (fun w => ∃ j, w = var (p.succAbove j)) (by
      intro w hw' hwz
      obtain ⟨i, rfl⟩ := hw w hw'
      by_cases hi : i = p
      · subst hi; exact absurd (rst_var_self i) hwz
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
        exact ⟨j, by rw [rst_var_ne hi, hj]⟩)
    by_contra hlt
    exact U4 p.succAbove Fin.succAbove_right_injective (rst p F) (thr_rst hF p).1
      (thr_rst hF p).2 (UC_le (by omega) h3)

theorem thr_ne_zero {F : BF} (hF : ThrL (fun _ => True) F) : F ≠ zF := by
  intro h
  have := hF.2 0 1 trivial trivial (by decide)
  rw [h] at this
  exact Bool.noConfusion this

theorem to_run {A : Fin 4 → Prop} {F : BF} (hF : ThrL (fun _ => True) F) {t : ℕ}
    (hu : UC gF A t (fun w => ∃ i, w = var i) F) :
    ∃ t', t' ≤ t ∧ ∃ ws : List BF, (∀ w ∈ ws, ∃ i, w = var i) ∧
      TR gF (fun k _ _ => A k) [F] t' ws := by
  obtain ⟨t', ht, ws, hws, hr⟩ := normalize gF zF A (fun _ => True) (fun _ _ _ _ _ => trivial)
    gF_zero_left gF_zero_right gF_self t _ F (fun _ _ => trivial) (thr_ne_zero hF) hu
  exact ⟨t', ht, ws, fun w hw => (hws w hw).1, TR.monoC (fun _ _ _ h => h.1) hr⟩

theorem U5 {F : BF} (hF : ThrL (fun _ => True) F) {t : ℕ}
    (hu : UC gF (fun _ => True) t (fun w => ∃ i, w = var i) F) : 9 ≤ t := by
  obtain ⟨t', ht, ws, hws, hr⟩ := to_run hF hu
  have := U5T hF hr hws
  omega

def MonoA : Fin 4 → Prop := fun k => k.val < 2

abbrev MR (ys : List BF) (s : ℕ) (ws : List BF) : Prop := TR gF (fun k _ _ => MonoA k) ys s ws

def outF (ys : List BF) : BF := fun x => ys.any fun y => y x

def otop (x : Fin 5) : BF := fun p => decide (∃ i, i ≠ x ∧ p i = true)

theorem mono_cases (k : Fin 4) (hk : MonoA k) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all [MonoA]

theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl

theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl

theorem UC_monoA {α : Type} {G : Fin 4 → α → α → α} {A A' : Fin 4 → Prop}
    (hA : ∀ k, A k → A' k) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), UC G A t S f → UC G A' t S f
  | 0, _, _, hu => hu
  | t + 1, S, f, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoA hA t S f hu)
    · exact Or.inr ⟨k, a, b, hA k hk, ha, hb, UC_monoA hA t _ f hu⟩

theorem top_elim (O : BF) :
    ∀ (m : ℕ) (S : BF → Prop) (F : BF), (∀ w, S w → ∀ p, w p = true → O p = true) → F ≠ O →
      UC gF MonoA m (fun w => w = O ∨ S w) F → UC gF MonoA m S F
  | 0, S, F, _, hF, hu => by
    rcases hu with h | h
    · exact absurd h hF
    · exact h
  | m + 1, S, F, hS, hF, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (top_elim O m S F hS hF hu)
    · have hle : ∀ w, (w = O ∨ S w) → ∀ p, w p = true → O p = true := by
        rintro w (rfl | hw) p hp
        · exact hp
        · exact hS w hw p hp
      have free : (gF k a b = O ∨ S (gF k a b)) → UC gF MonoA (m + 1) S F := by
        intro hg
        refine Or.inl (top_elim O m S F hS hF (UC_monoS gF MonoA m _ _ F ?_ hu))
        rintro w (rfl | hw)
        · exact hg
        · exact hw
      by_cases hao : a = O
      · subst hao
        apply free
        rcases mono_cases k hk with rfl | rfl
        · have : gF 0 a b = b := by
            rw [gF_and]
            funext p
            cases hbp : b p
            · simp
            · simp [hle b hb p hbp]
          rw [this]; exact hb
        · have : gF 1 a b = a := by
            rw [gF_or]
            funext p
            cases hbp : b p
            · simp
            · simp [hle b hb p hbp]
          rw [this]; exact Or.inl rfl
      by_cases hbo : b = O
      · subst hbo
        apply free
        rcases mono_cases k hk with rfl | rfl
        · have : gF 0 a b = a := by
            rw [gF_and]
            funext p
            cases hap : a p
            · simp
            · simp [hle a ha p hap]
          rw [this]; exact ha
        · have : gF 1 a b = b := by
            rw [gF_or]
            funext p
            cases hap : a p
            · simp
            · simp [hle a ha p hap]
          rw [this]; exact Or.inl rfl
      have ha' : S a := ha.resolve_left hao
      have hb' : S b := hb.resolve_left hbo
      refine UC_gate k a b hk ha' hb' (top_elim O m _ F ?_ hF (UC_monoS gF MonoA m _ _ F ?_ hu))
      · rintro w (rfl | hw) p hp
        · rcases mono_cases k hk with rfl | rfl
          · rw [gF_and] at hp
            simp only [Bool.and_eq_true] at hp
            exact hS a ha' p hp.1
          · rw [gF_or] at hp
            simp only [Bool.or_eq_true] at hp
            rcases hp with hp | hp
            · exact hS a ha' p hp
            · exact hS b hb' p hp
        · exact hS w hw p hp
      · rintro w (rfl | rfl | hw)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hw)

theorem outF_true (ys : List BF) (p : Fin 5 → Bool) :
    outF ys p = true ↔ ∃ y ∈ ys, y p = true := by
  simp [outF]

theorem outF_congr (ys : List BF) (p p' : Fin 5 → Bool) (h : ∀ y ∈ ys, y p = y p') :
    outF ys p = outF ys p' := by
  rw [Bool.eq_iff_iff, outF_true, outF_true]
  constructor
  · rintro ⟨y, hy, hp⟩; exact ⟨y, hy, by rw [← h y hy]; exact hp⟩
  · rintro ⟨y, hy, hp⟩; exact ⟨y, hy, by rw [h y hy]; exact hp⟩

theorem or_chain : ∀ (ys : List BF) (y : BF), MR [outF (y :: ys)] ys.length (y :: ys)
  | [], y => by
    have : outF [y] = y := funext fun x => by simp [outF]
    rw [this]
    exact TR.done
  | y2 :: rest, y => by
    have h := or_chain rest (gF 1 y y2)
    have e : outF (gF 1 y y2 :: rest) = outF (y :: y2 :: rest) :=
      funext fun x => by simp [outF, gF_or, Bool.or_assoc]
    rw [e] at h
    exact TR.step (r := rest) 1 0 (by simp [MonoA]) h

theorem complete_run (y0 : BF) (yt : List BF) {s : ℕ} {ws : List BF} (h : MR (y0 :: yt) s ws) :
    MR [outF (y0 :: yt)] (s + yt.length) ws := by
  refine TR.ind (P := fun s ws => MR [outF (y0 :: yt)] (s + yt.length) ws) h ?_ ?_ ?_
  · rw [Nat.zero_add]; exact or_chain yt y0
  · intro s xs zs hp _ ih; exact TR.perm hp ih
  · intro s a b r k u hc _ ih
    have e : s + 1 + yt.length = s + yt.length + 1 := by omega
    rw [e]
    exact TR.step k u hc ih

theorem frame (h0 : BF) {ys : List BF} {s : ℕ} {ws : List BF} (h : MR ys s ws) :
    MR (h0 :: ys) s (h0 :: ws) := by
  refine TR.ind (P := fun s ws => MR (h0 :: ys) s (h0 :: ws)) h TR.done ?_ ?_
  · intro s xs zs hp _ ih; exact TR.perm (hp.cons h0) ih
  · intro s a b r k u hc _ ih
    have p1 : (a :: b :: h0 :: r).Perm (h0 :: a :: b :: r) :=
      List.perm_middle (l₁ := [a, b])
    have p2 : (h0 :: (List.replicate (u + 1) (gF k a b) ++ r)).Perm
        (List.replicate (u + 1) (gF k a b) ++ h0 :: r) := List.perm_middle.symm
    exact TR.perm p1 (TR.step k u hc (TR.perm p2 ih))

def XI (x : Fin 5) (w : BF) : Prop := ∀ p b, w (Function.update p x b) = w p

def MonoF (w : BF) : Prop :=
  ∀ p q : Fin 5 → Bool, (∀ i, p i = true → q i = true) → w p = true → w q = true

def InvX (x : Fin 5) (w : BF) : Prop := XI x w ∧ MonoF w ∧ w (fun _ => false) = false

theorem InvX_gate {x : Fin 5} {k : Fin 4} (hk : MonoA k) {a b : BF} (ha : InvX x a)
    (hb : InvX x b) : InvX x (gF k a b) := by
  rcases mono_cases k hk with rfl | rfl
  · refine ⟨fun p v => ?_, fun p q hpq h => ?_, ?_⟩
    · show (a _ && b _) = (a _ && b _)
      rw [ha.1 p v, hb.1 p v]
    · rw [gF_and] at h ⊢
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨ha.2.1 p q hpq h.1, hb.2.1 p q hpq h.2⟩
    · show (a _ && b _) = false
      rw [ha.2.2]; rfl
  · refine ⟨fun p v => ?_, fun p q hpq h => ?_, ?_⟩
    · show (a _ || b _) = (a _ || b _)
      rw [ha.1 p v, hb.1 p v]
    · rw [gF_or] at h ⊢
      simp only [Bool.or_eq_true] at h ⊢
      exact h.imp (ha.2.1 p q hpq) (hb.2.1 p q hpq)
    · show (a _ || b _) = false
      rw [ha.2.2, hb.2.2]; rfl

theorem InvX_var {x m : Fin 5} (h : m ≠ x) : InvX x (var m) :=
  ⟨fun p v => by simp [var, Function.update_of_ne h], fun p q hpq hp => hpq m hp, rfl⟩

theorem mono_comm {k : Fin 4} (hk : MonoA k) (a b : BF) : gF k a b = gF k b a := by
  rcases mono_cases k hk with rfl | rfl
  · rw [gF_and, gF_and]; funext p; exact Bool.and_comm _ _
  · rw [gF_or, gF_or]; funext p; exact Bool.or_comm _ _

theorem upd_single_true (i x : Fin 5) :
    Function.update (singleInput i) x true = pairInput i x := by
  funext m
  by_cases hm : m = x
  · subst hm; simp [pairInput]
  · simp [singleInput, pairInput, hm]

theorem single_eq_upd (x : Fin 5) :
    singleInput x = Function.update (fun _ => false) x true := by
  funext m
  by_cases hm : m = x
  · subst hm; simp [singleInput]
  · simp [singleInput, hm]

theorem outF_rel (b' : BF) (p : Fin 5 → Bool) (hb : b' p = false) :
    ∀ (ys ys' : List BF), List.Forall₂ (fun w w' => ∀ q, b' q = false → w q = w' q) ys ys' →
      outF ys p = outF ys' p
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h t => by
    have ih := outF_rel b' p hb _ _ t
    simp only [outF, List.any_cons] at ih ⊢
    rw [h p hb, ih]

def SUc (x : Fin 5) (y0 : BF) (yt : List BF) (s : ℕ) (r : List BF) : Prop :=
  ((if otop x ∈ r then 2 else 3) ≤ s + yt.length ∧
    ∀ S : BF → Prop, (∀ w ∈ r, S w) → S (otop x) →
      UC gF MonoA (s + yt.length - (if otop x ∈ r then 2 else 3)) S
        (rst x (outF (y0 :: yt)))) ∨
  ∃ (c : ℕ) (h0 : BF) (ys' : List BF) (s' : ℕ), s = s' + 1 ∧ ys'.length = yt.length + 1 ∧
    ThrL (fun _ => True) (outF (h0 :: ys')) ∧
    MR (h0 :: ys') s' (List.replicate (c + 1) (var x) ++ r)

theorem SU (x : Fin 5) (y0 : BF) (yt : List BF)
    (hF : ThrL (fun _ => True) (outF (y0 :: yt))) :
    ∀ (s : ℕ) (r : List BF), MR (y0 :: yt) s (var x :: r) → (∀ w ∈ r, InvX x w) →
      SUc x y0 yt s r := by
  intro s
  induction s with
  | zero =>
    intro r h _
    exfalso
    have hp := (TR.inv h).1 rfl
    have hm : var x ∈ y0 :: yt := hp.mem_iff.1 (by simp)
    have h1 : outF (y0 :: yt) (singleInput x) = true :=
      (outF_true _ _).2 ⟨var x, hm, by simp [var, singleInput]⟩
    rw [hF.1 x trivial] at h1
    exact Bool.noConfusion h1
  | succ s ih =>
    intro r h hinv
    obtain ⟨k, u, a, b, r₁, hk, hp, hr⟩ := (TR.inv h).2 s rfl
    have consume : ∀ b' : BF, r.Perm (b' :: r₁) → gF k a b = gF k (var x) b' →
        SUc x y0 yt (s + 1) r := by
      intro b' hrp hg
      unfold SUc
      rw [hg] at hr
      have hb' : InvX x b' := hinv b' (hrp.mem_iff.2 (by simp))
      have hr1 : ∀ w ∈ r₁, InvX x w := fun w hw => hinv w (hrp.mem_iff.2 (by simp [hw]))
      have sens : ∀ i, i ≠ x → gF k (var x) b' (pairInput i x) =
          gF k (var x) b' (singleInput i) → False := by
        intro i hi hgg
        have hd := TRF_det hr (pairInput i x) (singleInput i) (by
          intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · rw [List.eq_of_mem_replicate hw]; exact hgg
          · rw [← upd_single_true]
            exact (hr1 w hw).1 _ _)
        have h2 := outF_congr _ _ _ hd
        rw [hF.1 i trivial, hF.2 i x trivial trivial hi] at h2
        exact Bool.noConfusion h2
      have hbx : ∀ i, i ≠ x → b' (pairInput i x) = b' (singleInput i) := fun i _ => by
        rw [← upd_single_true]; exact hb'.1 _ _
      have hv1 : ∀ i, var x (pairInput i x) = true := fun i => by simp [var, pairInput]
      have hv2 : ∀ i, i ≠ x → var x (singleInput i) = false := fun i hi => by
        simp [var, singleInput, Ne.symm hi]
      rcases mono_cases k hk with rfl | rfl
      · left
        have hone : ∀ i, i ≠ x → b' (singleInput i) = true := by
          intro i hi
          by_contra hc
          have hc' : b' (singleInput i) = false := by simpa using hc
          apply sens i hi
          rw [gF_and]
          show (var x _ && b' _) = (var x _ && b' _)
          rw [hbx i hi, hc', hv2 i hi]; simp
        have hbo : b' = otop x := by
          funext p
          rw [← hb'.1 p false]
          by_cases hex : ∃ i, i ≠ x ∧ p i = true
          · obtain ⟨i, hi, hpi⟩ := hex
            have : otop x p = true := by simp only [otop, decide_eq_true_eq]; exact ⟨i, hi, hpi⟩
            rw [this]
            refine hb'.2.1 (singleInput i) _ ?_ (hone i hi)
            intro m hm
            have : m = i := by simpa [singleInput] using hm
            subst this
            rw [Function.update_of_ne hi]; exact hpi
          · have : otop x p = false := by simp only [otop, decide_eq_false_iff_not]; exact hex
            rw [this]
            have hz : Function.update p x false = fun _ => false := by
              funext m
              by_cases hm : m = x
              · subst hm; simp
              · rw [Function.update_of_ne hm]
                by_contra hc
                exact hex ⟨m, hm, by simpa using hc⟩
            rw [hz]; exact hb'.2.2
        have hmem : otop x ∈ r := hrp.mem_iff.2 (by simp [hbo])
        have hdead : rst x (gF 0 (var x) b') = zF := by
          funext p
          show (var x _ && b' _) = false
          simp [var]
        have hc := complete_run y0 yt hr
        obtain ⟨hd1, hd2⟩ := pot_dead x (thr_rst_ne hF x) hc
        rw [dcount_rep] at hd1 hd2
        simp only [hdead, ite_true] at hd1 hd2
        simp only [hmem, ite_true]
        refine ⟨by omega, fun S hS _ => UC_le (by omega) (hd2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hdead) hwz
        · have : rst x w = w := funext fun p => (hr1 w hw).1 p false
          rw [this]
          exact hS w (hrp.mem_iff.2 (by simp [hw]))
      · right
        have hzero : ∀ i, b' (singleInput i) = false := by
          intro i
          by_cases hi : i = x
          · subst hi
            rw [single_eq_upd, hb'.1]; exact hb'.2.2
          · by_contra hc
            have hc' : b' (singleInput i) = true := by simpa using hc
            apply sens i hi
            rw [gF_or]
            show (var x _ || b' _) = (var x _ || b' _)
            rw [hbx i hi, hc', hv1 i]; simp
        have hrel : List.Forall₂ (fun w w' => ∀ q, b' q = false → w q = w' q)
            (List.replicate (u + 1) (gF 1 (var x) b') ++ r₁)
            (List.replicate (u + 1) (var x) ++ r₁) := by
          refine List.rel_append ?_ (List.forall₂_same.2 fun _ _ _ _ => rfl)
          generalize u + 1 = n
          induction n with
          | zero => exact List.Forall₂.nil
          | succ n ihn =>
            refine List.Forall₂.cons (fun q hq => ?_) ihn
            show (var x q || b' q) = var x q
            rw [hq]; simp
        obtain ⟨ys', hy, hrun⟩ := TR.rel (A := MonoA)
          (fun w w' => ∀ q, b' q = false → w q = w' q)
          (fun k a a' b b' ha hb q hq => by
            show zeroGate k (a q) (b q) = zeroGate k (a' q) (b' q)
            rw [ha q hq, hb q hq]) hr _ hrel
        refine ⟨u, b', ys', s, rfl, ?_, ⟨fun i _ => ?_, fun i j _ _ hij => ?_⟩, ?_⟩
        · have := hy.length_eq
          simpa using this.symm
        · have e := outF_rel b' (singleInput i) (hzero i) _ _ hy
          have h3 : outF (b' :: ys') (singleInput i) =
              (b' (singleInput i) || outF ys' (singleInput i)) := by simp [outF]
          rw [h3, hzero i, ← e, hF.1 i trivial]; rfl
        · have h3 : outF (b' :: ys') (pairInput i j) =
              (b' (pairInput i j) || outF ys' (pairInput i j)) := by simp [outF]
          rw [h3]
          cases hbp : b' (pairInput i j)
          · have e := outF_rel b' (pairInput i j) hbp _ _ hy
            rw [← e, hF.2 i j trivial trivial hij]; rfl
          · rfl
        · have p1 : (b' :: (List.replicate (u + 1) (var x) ++ r₁)).Perm
              (List.replicate (u + 1) (var x) ++ r) :=
            List.perm_middle.symm.trans (List.Perm.append_left _ hrp.symm)
          exact TR.perm p1 (frame b' hrun)
    by_cases hax : a = var x
    · subst hax
      exact consume b hp.cons_inv rfl
    by_cases hbx : b = var x
    · subst hbx
      have hp' : (var x :: r).Perm (var x :: a :: r₁) := hp.trans (List.Perm.swap _ _ _)
      exact consume a hp'.cons_inv (mono_comm hk a (var x))
    have hx1 : var x ∈ r₁ := by
      have : var x ∈ a :: b :: r₁ := hp.mem_iff.1 (by simp)
      simp only [List.mem_cons] at this
      rcases this with h1 | h1 | h1
      · exact absurd h1.symm hax
      · exact absurd h1.symm hbx
      · exact h1
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx1
    have hr2 : r.Perm (a :: b :: (l₁ ++ l₂)) := by
      have p1 : (a :: b :: (l₁ ++ var x :: l₂)).Perm (var x :: a :: b :: (l₁ ++ l₂)) :=
        List.perm_middle (l₁ := a :: b :: l₁)
      exact (hp.trans p1).cons_inv
    have ha : InvX x a := hinv a (hr2.mem_iff.2 (by simp))
    have hb : InvX x b := hinv b (hr2.mem_iff.2 (by simp))
    have hsub : ∀ w ∈ l₁ ++ l₂, w ∈ r := fun w hw => hr2.mem_iff.2 (by simp [List.mem_append.1 hw])
    have p2 : (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ var x :: l₂)).Perm
        (var x :: (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂))) := by
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_middle
    have hinv2 : ∀ w ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂), InvX x w := by
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · rw [List.eq_of_mem_replicate hw]; exact InvX_gate hk ha hb
      · exact hinv w (hsub w hw)
    have hih := ih _ (TR.perm p2 hr) hinv2
    unfold SUc at hih ⊢
    rcases hih with ⟨hA1, hA2⟩ | ⟨c, h0, ys', s', hs', hl, hthr, hrun⟩
    · left
      by_cases hgo : gF k a b = otop x
      · have hm : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) := by
          rw [hgo]; simp
        simp only [hm, ite_true] at hA1 hA2
        refine ⟨by split_ifs <;> omega, fun S hS hSo => ?_⟩
        refine UC_le (by split_ifs <;> omega) (hA2 S ?_ hSo)
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgo]; exact hSo
        · exact hS w (hsub w hw)
      · have hiff : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) → otop x ∈ r := by
          intro hm
          rcases List.mem_append.1 hm with hm | hm
          · exact absurd (List.eq_of_mem_replicate hm).symm hgo
          · exact hsub _ hm
        have hcc : (if otop x ∈ r then 2 else 3) ≤
            (if otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) then 2 else 3) := by
          by_cases h1 : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂)
          · simp [h1, hiff h1]
          · simp only [h1, ite_false]; split_ifs <;> omega
        refine ⟨by omega, fun S hS hSo => ?_⟩
        have h1 := hA2 (fun w => w = gF k a b ∨ S w) (by
          intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (List.eq_of_mem_replicate hw)
          · exact Or.inr (hS w (hsub w hw))) (Or.inr hSo)
        have h2 := UC_gate k a b hk (hS a (hr2.mem_iff.2 (by simp)))
          (hS b (hr2.mem_iff.2 (by simp))) h1
        exact UC_le (by omega) h2
    · right
      refine ⟨c, h0, ys', s' + 1, by omega, hl, hthr, ?_⟩
      have p3 : (List.replicate (c + 1) (var x) ++ r).Perm
          (a :: b :: (List.replicate (c + 1) (var x) ++ (l₁ ++ l₂))) := by
        refine (List.Perm.append_left _ hr2).trans ?_
        exact List.perm_middle.trans (List.Perm.cons a List.perm_middle)
      have p4 : (List.replicate (c + 1) (var x) ++
          (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂))).Perm
          (List.replicate (u + 1) (gF k a b) ++
            (List.replicate (c + 1) (var x) ++ (l₁ ++ l₂))) :=
        List.perm_append_comm_assoc _ _ _
      subst hs'
      exact TR.perm p3.symm (TR.step k u hk (TR.perm p4 hrun))

theorem map_perm_cons {β γ : Type} (f : β → γ) {l : List β} {a : γ} {r : List γ}
    (h : (l.map f).Perm (a :: r)) :
    ∃ x l', l.Perm (x :: l') ∧ f x = a ∧ (l'.map f).Perm r := by
  have ha : a ∈ l.map f := h.mem_iff.2 (by simp)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
  refine ⟨x, l₁ ++ l₂, List.perm_middle, rfl, ?_⟩
  have h1 := (List.perm_middle (a := x) (l₁ := l₁) (l₂ := l₂)).map f
  exact (h1.symm.trans h).cons_inv

def occSum (ts : List (Formula 5)) (i : Fin 5) : ℕ := (ts.map fun t => formOcc t i).sum

theorem occSum_perm {ts ts' : List (Formula 5)} (h : ts.Perm ts') (i : Fin 5) :
    occSum ts i = occSum ts' i := (h.map _).sum_eq

theorem forest {ys : List BF} {s : ℕ} {ws : List BF} (h : MR ys s ws) :
    ∀ ts : List (Formula 5), (ts.map formEval).Perm ws → ws.length = s + ys.length →
      ∃ ts' : List (Formula 5), (ts'.map formEval).Perm ys ∧
        ∀ i, occSum ts' i = occSum ts i := by
  refine TR.ind (P := fun s ws => ∀ ts : List (Formula 5), (ts.map formEval).Perm ws →
    ws.length = s + ys.length → ∃ ts' : List (Formula 5), (ts'.map formEval).Perm ys ∧
      ∀ i, occSum ts' i = occSum ts i) h ?_ ?_ ?_
  · intro ts hts _
    exact ⟨ts, hts, fun _ => rfl⟩
  · intro s xs zs hp _ ih ts hts hlen
    exact ih ts (hts.trans hp.symm) (by rw [hp.length_eq]; exact hlen)
  · intro s a b r k u hk hr ih ts hts hlen
    have hl := TR.len hr
    simp only [List.length_append, List.length_replicate, List.length_cons] at hl hlen
    obtain rfl : u = 0 := by omega
    obtain ⟨ta, ts₁, hp1, rfl, h1⟩ := map_perm_cons formEval hts
    obtain ⟨tb, ts₂, hp2, rfl, h2⟩ := map_perm_cons formEval h1
    have hev : formEval (BinaryTree.node (Sum.inr (decide (k = 0))) ta tb : Formula 5) =
        gF k (formEval ta) (formEval tb) := by
      rcases mono_cases k hk with rfl | rfl
      · funext x; simp [formEval, gF_and]
      · funext x; simp [formEval, gF_or]
    obtain ⟨ts', hy, hocc⟩ := ih (BinaryTree.node (Sum.inr (decide (k = 0))) ta tb :: ts₂)
      (by
        rw [List.map_cons, hev]
        exact h2.cons _)
      (by simp only [List.length_append, List.length_replicate]; omega)
    refine ⟨ts', hy, fun i => ?_⟩
    rw [hocc i, occSum_perm hp1 i]
    have e2 := occSum_perm hp2 i
    simp only [occSum, List.map_cons, List.sum_cons, formOcc] at e2 ⊢
    omega

def orAll : List (Formula 5) → Formula 5
  | [] => BinaryTree.nil
  | t :: l => BinaryTree.node (Sum.inr false) t (orAll l)

theorem orAll_eval : ∀ (l : List (Formula 5)) (p : Fin 5 → Bool),
    formEval (orAll l) p = outF (l.map formEval) p
  | [], p => by simp [orAll, formEval, outF]
  | t :: l, p => by
    have ih := orAll_eval l p
    simp only [orAll, formEval, outF, List.map_cons, List.any_cons] at ih ⊢
    rw [ih]

theorem orAll_occ : ∀ (l : List (Formula 5)) (i : Fin 5), formOcc (orAll l) i = occSum l i
  | [], i => by simp [orAll, formOcc, occSum]
  | t :: l, i => by
    have ih := orAll_occ l i
    simp only [orAll, formOcc, occSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

def leafF (i : Fin 5) : Formula 5 := BinaryTree.node (Sum.inl i) BinaryTree.nil BinaryTree.nil

theorem leaf_eval (idx : List (Fin 5)) : (idx.map leafF).map formEval = idx.map var := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  funext x
  simp [leafF, formEval, var]

theorem leaf_occ : ∀ (idx : List (Fin 5)) (i : Fin 5), occSum (idx.map leafF) i = idx.count i
  | [], i => by simp [occSum]
  | j :: idx, i => by
    have ih := leaf_occ idx i
    simp only [occSum, List.map_cons, List.sum_cons, leafF, formOcc, List.count_cons] at ih ⊢
    rw [ih]
    by_cases h : j = i
    · simp [h]; omega
    · simp [h]

theorem vars_list : ∀ (ws : List BF), (∀ w ∈ ws, ∃ i, w = var i) →
    ∃ idx : List (Fin 5), ws = idx.map var
  | [], _ => ⟨[], rfl⟩
  | w :: ws, h => by
    obtain ⟨i, rfl⟩ := h w (by simp)
    obtain ⟨idx, rfl⟩ := vars_list ws fun w hw => h w (by simp [hw])
    exact ⟨i :: idx, rfl⟩

theorem len_counts : ∀ (idx : List (Fin 5)),
    idx.length = idx.count 0 + idx.count 1 + idx.count 2 + idx.count 3 + idx.count 4
  | [] => rfl
  | j :: idx => by
    have ih := len_counts idx
    fin_cases j <;> simp <;> omega

theorem outF_perm {ys ys' : List BF} (h : ys.Perm ys') (p : Fin 5 → Bool) :
    outF ys p = outF ys' p := h.any_eq

theorem GS : ∀ (s : ℕ) (y0 : BF) (yt : List BF) (ws : List BF), MR (y0 :: yt) s ws →
    (∀ w ∈ ws, ∃ i, w = var i) → s + yt.length = 9 →
    ThrL (fun _ => True) (outF (y0 :: yt)) → False := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro y0 yt ws h hw hs hF
    have hlen := TR.len h
    obtain ⟨idx, rfl⟩ := vars_list ws hw
    have hpres : ∀ i, i ∈ idx := by
      intro i
      by_contra hi
      obtain ⟨j, hj, -⟩ := ex_third i i
      have hd := TRF_det h (pairInput i j) (singleInput j) (by
        intro w hw'
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
        have : m ≠ i := fun e => hi (e ▸ hm)
        simp [var, pairInput, singleInput, this])
      have h2 := outF_congr _ _ _ hd
      rw [hF.1 j trivial, hF.2 i j trivial trivial (Ne.symm hj)] at h2
      exact Bool.noConfusion h2
    simp only [List.length_map, List.length_cons] at hlen
    by_cases hall : ∀ i, 2 ≤ idx.count i
    · have hc := len_counts idx
      have h0 := hall 0
      have h1 := hall 1
      have h2 := hall 2
      have h3 := hall 3
      have h4 := hall 4
      have hle : ∀ i, idx.count i ≤ 2 := by
        intro i
        fin_cases i
        · show idx.count 0 ≤ 2; omega
        · show idx.count 1 ≤ 2; omega
        · show idx.count 2 ≤ 2; omega
        · show idx.count 3 ≤ 2; omega
        · show idx.count 4 ≤ 2; omega
      obtain ⟨ts', hy, hocc⟩ := forest h (idx.map leafF) (by rw [leaf_eval])
        (by simp only [List.length_map, List.length_cons]; omega)
      refine no_readtwice_five (orAll ts') ?_ ?_ ?_
      · intro i; rw [orAll_occ, hocc, leaf_occ]; exact hle i
      · intro i; rw [orAll_eval, outF_perm hy]; exact hF.1 i trivial
      · intro i j hij; rw [orAll_eval, outF_perm hy]; exact hF.2 i j trivial trivial hij
    · obtain ⟨x, hx⟩ := not_forall.1 hall
      have hx1 : idx.count x = 1 := by
        have := List.count_pos_iff.2 (hpres x)
        omega
      have hp : (idx.map var).Perm (var x :: (idx.erase x).map var) :=
        (List.perm_cons_erase (hpres x)).map var
      have hnx : x ∉ idx.erase x := by
        intro hm
        have := List.count_pos_iff.2 hm
        rw [List.count_erase_self] at this
        omega
      have hinv : ∀ w ∈ (idx.erase x).map var, InvX x w := by
        intro w hw'
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
        exact InvX_var fun e => hnx (e ▸ hm)
      have hsu := SU x y0 yt hF s _ (TR.perm hp h) hinv
      unfold SUc at hsu
      rcases hsu with ⟨hA1, hA2⟩ | ⟨c, h0, ys', s', hs', hl, hthr, hrun⟩
      · have hno : otop x ∉ (idx.erase x).map var := by
          intro hm
          obtain ⟨m, -, he⟩ := List.mem_map.1 hm
          obtain ⟨j, hj1, hj2⟩ := ex_third m x
          have h5 := congrFun he (singleInput j)
          have h6 : var m (singleInput j) = false := by simp [var, singleInput, Ne.symm hj1]
          have h7 : otop x (singleInput j) = true := by
            simp only [otop, decide_eq_true_eq]
            exact ⟨j, hj2, by simp [singleInput]⟩
          rw [h6, h7] at h5
          exact Bool.noConfusion h5
        simp only [hno, ite_false] at hA1 hA2
        have h6 := hA2 (fun w => w = otop x ∨ ∃ j, w = var (x.succAbove j)) (by
          intro w hw'
          obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
          have hmx : m ≠ x := fun e => hnx (e ▸ hm)
          obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hmx
          exact Or.inr ⟨j, by rw [hj]⟩) (Or.inl rfl)
        have h7 := top_elim (otop x) _ (fun w => ∃ j, w = var (x.succAbove j)) _ (by
          rintro w ⟨j, rfl⟩ p hp'
          simp only [otop, decide_eq_true_eq]
          exact ⟨x.succAbove j, Fin.succAbove_ne x j, hp'⟩) (by
          intro he
          have h8 := (thr_rst hF x).1 0
          rw [he] at h8
          have h9 : otop x (singleInput (x.succAbove 0)) = true := by
            simp only [otop, decide_eq_true_eq]
            exact ⟨x.succAbove 0, Fin.succAbove_ne x 0, by simp [singleInput]⟩
          rw [h9] at h8
          exact Bool.noConfusion h8) h6
        have h8 := UC_monoA (A' := fun _ => True) (fun _ _ => trivial) _ _ _ h7
        exact U4 x.succAbove Fin.succAbove_right_injective _ (thr_rst hF x).1 (thr_rst hF x).2
          (UC_le (by omega) h8)
      · refine ih s' (by omega) h0 ys' _ hrun ?_ (by omega) hthr
        intro w hw'
        rcases List.mem_append.1 hw' with hw' | hw'
        · exact ⟨x, List.eq_of_mem_replicate hw'⟩
        · obtain ⟨m, -, rfl⟩ := List.mem_map.1 hw'
          exact ⟨m, rfl⟩

theorem M5 {F : BF} (hF : ThrL (fun _ => True) F) :
    ¬ UC gF MonoA 9 (fun w => ∃ i, w = var i) F := by
  intro hu
  obtain ⟨t', ht, ws, hws, hr⟩ := to_run hF hu
  have h9 := U5T hF (TR.monoC (fun _ _ _ _ => trivial) hr) hws
  have ht9 : t' = 9 := by omega
  subst ht9
  have e : outF [F] = F := funext fun x => by simp [outF]
  exact GS 9 F [] ws hr hws rfl (by rw [e]; exact hF)

end ThresholdFive

namespace ThresholdSix
open ThresholdFive (zeroGate UC UC_gate UC_le UC_monoS UC_map TR normalize singleInput pairInput)
open ThresholdFive.TR (ind inv len perm step done)
abbrev BF := (Fin 6 → Bool) → Bool

def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)

def var (i : Fin 6) : BF := fun x => x i

def zF : BF := fun _ => false

def rst (p : Fin 6) (a : BF) : BF := fun x => a (Function.update x p false)

def ThrL (V : Fin 6 → Prop) (F : BF) : Prop :=
  (∀ i, V i → F (singleInput i) = false) ∧
    ∀ i j, V i → V j → i ≠ j → F (pairInput i j) = true

theorem gF_zero_left (k : Fin 4) (b : BF) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_right (k : Fin 4) (a : BF) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_self (k : Fin 4) (a : BF) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_zero (k : Fin 4) : gF k zF zF = zF := by
  fin_cases k <;> exact funext fun x => by simp [gF, zF, zeroGate]

theorem upd_single {i p : Fin 6} (h : i ≠ p) :
    Function.update (singleInput i) p false = singleInput i := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [singleInput, Ne.symm h]
  · simp [Function.update_of_ne hm]

theorem upd_pair {i j p : Fin 6} (hi : i ≠ p) (hj : j ≠ p) :
    Function.update (pairInput i j) p false = pairInput i j := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [pairInput, Ne.symm hi, Ne.symm hj]
  · simp [Function.update_of_ne hm]

theorem rst_var_self (p : Fin 6) : rst p (var p) = zF :=
  funext fun x => by simp [rst, var, zF]

theorem rst_var_ne {i p : Fin 6} (h : i ≠ p) : rst p (var i) = var i :=
  funext fun x => by simp [rst, var, Function.update_of_ne h]

theorem var_inj {i j : Fin 6} (h : var i = var j) : i = j := by
  have := congrFun h (singleInput i)
  exact (by simpa [var, singleInput] using this : j = i).symm

theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 6 → Bool) :
    (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x' := by
  refine TR.ind (P := fun _ ws => (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x') h
    (fun h => h) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]
      show zeroGate k (a x) (b x) = zeroGate k (a x') (b x')
      rw [hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

def dcount (p : Fin 6) (ws : List BF) : ℕ := ws.countP fun w => decide (rst p w = zF)

theorem dcount_cons (p : Fin 6) (a : BF) (l : List BF) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]

theorem dcount_rep (p : Fin 6) (n : ℕ) (g : BF) (r : List BF) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

theorem pot_dead {A : Fin 4 → Prop} (p : Fin 6) {F : BF} (hF : rst p F ≠ zF) {s : ℕ}
    {ws : List BF} (h : TR gF (fun k _ _ => A k) [F] s ws) :
    dcount p ws ≤ s ∧ ∀ S : BF → Prop, (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) →
      UC gF A (s - dcount p ws) S (rst p F) := by
  refine TR.ind (P := fun s ws => dcount p ws ≤ s ∧ ∀ S : BF → Prop,
    (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) → UC gF A (s - dcount p ws) S (rst p F)) h ?_ ?_ ?_
  · refine ⟨by simp [dcount, hF], fun S hS => ?_⟩
    have : dcount p [F] = 0 := by simp [dcount, hF]
    rw [this]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dcount p zs = dcount p xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u hk _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : rst p (gF k a b) = gF k (rst p a) (rst p b) := rfl
    rw [dcount_rep] at ih1 ih2
    rw [dcount_cons, dcount_cons]
    have hmem : ∀ (S : BF → Prop), (∀ w ∈ a :: b :: r, rst p w ≠ zF → S (rst p w)) →
        ∀ w ∈ r, rst p w ≠ zF → S (rst p w) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : rst p a = zF <;> by_cases hb : rst p b = zF
    · have hgz : rst p (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : rst p (gF k a b) = rst p b := by
          rcases gF_zero_left k (rst p b) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : rst p (gF k a b) = rst p a := by
          rcases gF_zero_right k (rst p a) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gF k (rst p a) (rst p b) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (rst p a) (rst p b) hk (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2

theorem ex_third : ∀ p q : Fin 6, ∃ r, r ≠ p ∧ r ≠ q := by decide

theorem thr_rst {F : BF} (hF : ThrL (fun _ => True) F) (p : Fin 6) :
    (∀ j, rst p F (singleInput (p.succAbove j)) = false) ∧
    (∀ j j', j ≠ j' → rst p F (pairInput (p.succAbove j) (p.succAbove j')) = true) := by
  refine ⟨fun j => ?_, fun j j' hj => ?_⟩
  · show F (Function.update (singleInput (p.succAbove j)) p false) = false
    rw [upd_single (Fin.succAbove_ne p j)]
    exact hF.1 _ trivial
  · show F (Function.update (pairInput (p.succAbove j) (p.succAbove j')) p false) = true
    rw [upd_pair (Fin.succAbove_ne p j) (Fin.succAbove_ne p j')]
    exact hF.2 _ _ trivial trivial fun h => hj (Fin.succAbove_right_injective h)

theorem thr_rst_ne {F : BF} (hF : ThrL (fun _ => True) F) (p : Fin 6) : rst p F ≠ zF := by
  intro h
  have := (thr_rst hF p).2 0 1 (by decide)
  rw [h] at this
  exact Bool.noConfusion this

theorem thr_ne_zero {F : BF} (hF : ThrL (fun _ => True) F) : F ≠ zF := by
  intro h
  have := hF.2 0 1 trivial trivial (by decide)
  rw [h] at this
  exact Bool.noConfusion this

theorem to_run {A : Fin 4 → Prop} {F : BF} (hF : ThrL (fun _ => True) F) {t : ℕ}
    (hu : UC gF A t (fun w => ∃ i, w = var i) F) :
    ∃ t', t' ≤ t ∧ ∃ ws : List BF, (∀ w ∈ ws, ∃ i, w = var i) ∧
      TR gF (fun k _ _ => A k) [F] t' ws := by
  obtain ⟨t', ht, ws, hws, hr⟩ := normalize gF zF A (fun _ => True) (fun _ _ _ _ _ => trivial)
    gF_zero_left gF_zero_right gF_self t _ F (fun _ _ => trivial) (thr_ne_zero hF) hu
  exact ⟨t', ht, ws, fun w hw => (hws w hw).1, TR.monoC (fun _ _ _ h => h.1) hr⟩

def MonoA : Fin 4 → Prop := fun k => k.val < 2

abbrev MR (ys : List BF) (s : ℕ) (ws : List BF) : Prop := TR gF (fun k _ _ => MonoA k) ys s ws

def outF (ys : List BF) : BF := fun x => ys.any fun y => y x

def otop (x : Fin 6) : BF := fun p => decide (∃ i, i ≠ x ∧ p i = true)

theorem mono_cases (k : Fin 4) (hk : MonoA k) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all [MonoA]

theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl

theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl

theorem UC_monoA {α : Type} {G : Fin 4 → α → α → α} {A A' : Fin 4 → Prop}
    (hA : ∀ k, A k → A' k) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), UC G A t S f → UC G A' t S f
  | 0, _, _, hu => hu
  | t + 1, S, f, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoA hA t S f hu)
    · exact Or.inr ⟨k, a, b, hA k hk, ha, hb, UC_monoA hA t _ f hu⟩

theorem top_elim (O : BF) :
    ∀ (m : ℕ) (S : BF → Prop) (F : BF), (∀ w, S w → ∀ p, w p = true → O p = true) → F ≠ O →
      UC gF MonoA m (fun w => w = O ∨ S w) F → UC gF MonoA m S F
  | 0, S, F, _, hF, hu => by
    rcases hu with h | h
    · exact absurd h hF
    · exact h
  | m + 1, S, F, hS, hF, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (top_elim O m S F hS hF hu)
    · have hle : ∀ w, (w = O ∨ S w) → ∀ p, w p = true → O p = true := by
        rintro w (rfl | hw) p hp
        · exact hp
        · exact hS w hw p hp
      have free : (gF k a b = O ∨ S (gF k a b)) → UC gF MonoA (m + 1) S F := by
        intro hg
        refine Or.inl (top_elim O m S F hS hF (UC_monoS gF MonoA m _ _ F ?_ hu))
        rintro w (rfl | hw)
        · exact hg
        · exact hw
      by_cases hao : a = O
      · subst hao
        apply free
        rcases mono_cases k hk with rfl | rfl
        · have : gF 0 a b = b := by
            rw [gF_and]
            funext p
            cases hbp : b p
            · simp
            · simp [hle b hb p hbp]
          rw [this]; exact hb
        · have : gF 1 a b = a := by
            rw [gF_or]
            funext p
            cases hbp : b p
            · simp
            · simp [hle b hb p hbp]
          rw [this]; exact Or.inl rfl
      by_cases hbo : b = O
      · subst hbo
        apply free
        rcases mono_cases k hk with rfl | rfl
        · have : gF 0 a b = a := by
            rw [gF_and]
            funext p
            cases hap : a p
            · simp
            · simp [hle a ha p hap]
          rw [this]; exact ha
        · have : gF 1 a b = b := by
            rw [gF_or]
            funext p
            cases hap : a p
            · simp
            · simp [hle a ha p hap]
          rw [this]; exact Or.inl rfl
      have ha' : S a := ha.resolve_left hao
      have hb' : S b := hb.resolve_left hbo
      refine UC_gate k a b hk ha' hb' (top_elim O m _ F ?_ hF (UC_monoS gF MonoA m _ _ F ?_ hu))
      · rintro w (rfl | hw) p hp
        · rcases mono_cases k hk with rfl | rfl
          · rw [gF_and] at hp
            simp only [Bool.and_eq_true] at hp
            exact hS a ha' p hp.1
          · rw [gF_or] at hp
            simp only [Bool.or_eq_true] at hp
            rcases hp with hp | hp
            · exact hS a ha' p hp
            · exact hS b hb' p hp
        · exact hS w hw p hp
      · rintro w (rfl | rfl | hw)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hw)

theorem outF_true (ys : List BF) (p : Fin 6 → Bool) :
    outF ys p = true ↔ ∃ y ∈ ys, y p = true := by
  simp [outF]

theorem outF_congr (ys : List BF) (p p' : Fin 6 → Bool) (h : ∀ y ∈ ys, y p = y p') :
    outF ys p = outF ys p' := by
  rw [Bool.eq_iff_iff, outF_true, outF_true]
  constructor
  · rintro ⟨y, hy, hp⟩; exact ⟨y, hy, by rw [← h y hy]; exact hp⟩
  · rintro ⟨y, hy, hp⟩; exact ⟨y, hy, by rw [h y hy]; exact hp⟩

theorem or_chain : ∀ (ys : List BF) (y : BF), MR [outF (y :: ys)] ys.length (y :: ys)
  | [], y => by
    have : outF [y] = y := funext fun x => by simp [outF]
    rw [this]
    exact TR.done
  | y2 :: rest, y => by
    have h := or_chain rest (gF 1 y y2)
    have e : outF (gF 1 y y2 :: rest) = outF (y :: y2 :: rest) :=
      funext fun x => by simp [outF, gF_or, Bool.or_assoc]
    rw [e] at h
    exact TR.step (r := rest) 1 0 (by simp [MonoA]) h

theorem complete_run (y0 : BF) (yt : List BF) {s : ℕ} {ws : List BF} (h : MR (y0 :: yt) s ws) :
    MR [outF (y0 :: yt)] (s + yt.length) ws := by
  refine TR.ind (P := fun s ws => MR [outF (y0 :: yt)] (s + yt.length) ws) h ?_ ?_ ?_
  · rw [Nat.zero_add]; exact or_chain yt y0
  · intro s xs zs hp _ ih; exact TR.perm hp ih
  · intro s a b r k u hc _ ih
    have e : s + 1 + yt.length = s + yt.length + 1 := by omega
    rw [e]
    exact TR.step k u hc ih

theorem frame (h0 : BF) {ys : List BF} {s : ℕ} {ws : List BF} (h : MR ys s ws) :
    MR (h0 :: ys) s (h0 :: ws) := by
  refine TR.ind (P := fun s ws => MR (h0 :: ys) s (h0 :: ws)) h TR.done ?_ ?_
  · intro s xs zs hp _ ih; exact TR.perm (hp.cons h0) ih
  · intro s a b r k u hc _ ih
    have p1 : (a :: b :: h0 :: r).Perm (h0 :: a :: b :: r) :=
      List.perm_middle (l₁ := [a, b])
    have p2 : (h0 :: (List.replicate (u + 1) (gF k a b) ++ r)).Perm
        (List.replicate (u + 1) (gF k a b) ++ h0 :: r) := List.perm_middle.symm
    exact TR.perm p1 (TR.step k u hc (TR.perm p2 ih))

def XI (x : Fin 6) (w : BF) : Prop := ∀ p b, w (Function.update p x b) = w p

def MonoF (w : BF) : Prop :=
  ∀ p q : Fin 6 → Bool, (∀ i, p i = true → q i = true) → w p = true → w q = true

def InvX (x : Fin 6) (w : BF) : Prop := XI x w ∧ MonoF w ∧ w (fun _ => false) = false

theorem InvX_gate {x : Fin 6} {k : Fin 4} (hk : MonoA k) {a b : BF} (ha : InvX x a)
    (hb : InvX x b) : InvX x (gF k a b) := by
  rcases mono_cases k hk with rfl | rfl
  · refine ⟨fun p v => ?_, fun p q hpq h => ?_, ?_⟩
    · show (a _ && b _) = (a _ && b _)
      rw [ha.1 p v, hb.1 p v]
    · rw [gF_and] at h ⊢
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨ha.2.1 p q hpq h.1, hb.2.1 p q hpq h.2⟩
    · show (a _ && b _) = false
      rw [ha.2.2]; rfl
  · refine ⟨fun p v => ?_, fun p q hpq h => ?_, ?_⟩
    · show (a _ || b _) = (a _ || b _)
      rw [ha.1 p v, hb.1 p v]
    · rw [gF_or] at h ⊢
      simp only [Bool.or_eq_true] at h ⊢
      exact h.imp (ha.2.1 p q hpq) (hb.2.1 p q hpq)
    · show (a _ || b _) = false
      rw [ha.2.2, hb.2.2]; rfl

theorem InvX_var {x m : Fin 6} (h : m ≠ x) : InvX x (var m) :=
  ⟨fun p v => by simp [var, Function.update_of_ne h], fun p q hpq hp => hpq m hp, rfl⟩

theorem mono_comm {k : Fin 4} (hk : MonoA k) (a b : BF) : gF k a b = gF k b a := by
  rcases mono_cases k hk with rfl | rfl
  · rw [gF_and, gF_and]; funext p; exact Bool.and_comm _ _
  · rw [gF_or, gF_or]; funext p; exact Bool.or_comm _ _

theorem upd_single_true (i x : Fin 6) :
    Function.update (singleInput i) x true = pairInput i x := by
  funext m
  by_cases hm : m = x
  · subst hm; simp [pairInput]
  · simp [singleInput, pairInput, hm]

theorem single_eq_upd (x : Fin 6) :
    singleInput x = Function.update (fun _ => false) x true := by
  funext m
  by_cases hm : m = x
  · subst hm; simp [singleInput]
  · simp [singleInput, hm]

theorem outF_rel (b' : BF) (p : Fin 6 → Bool) (hb : b' p = false) :
    ∀ (ys ys' : List BF), List.Forall₂ (fun w w' => ∀ q, b' q = false → w q = w' q) ys ys' →
      outF ys p = outF ys' p
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h t => by
    have ih := outF_rel b' p hb _ _ t
    simp only [outF, List.any_cons] at ih ⊢
    rw [h p hb, ih]

def SUc (x : Fin 6) (y0 : BF) (yt : List BF) (s : ℕ) (r : List BF) : Prop :=
  ((if otop x ∈ r then 2 else 3) ≤ s + yt.length ∧
    ∀ S : BF → Prop, (∀ w ∈ r, S w) → S (otop x) →
      UC gF MonoA (s + yt.length - (if otop x ∈ r then 2 else 3)) S
        (rst x (outF (y0 :: yt)))) ∨
  ∃ (c : ℕ) (h0 : BF) (ys' : List BF) (s' : ℕ), s = s' + 1 ∧ ys'.length = yt.length + 1 ∧
    ThrL (fun _ => True) (outF (h0 :: ys')) ∧
    MR (h0 :: ys') s' (List.replicate (c + 1) (var x) ++ r)

theorem SU (x : Fin 6) (y0 : BF) (yt : List BF)
    (hF : ThrL (fun _ => True) (outF (y0 :: yt))) :
    ∀ (s : ℕ) (r : List BF), MR (y0 :: yt) s (var x :: r) → (∀ w ∈ r, InvX x w) →
      SUc x y0 yt s r := by
  intro s
  induction s with
  | zero =>
    intro r h _
    exfalso
    have hp := (TR.inv h).1 rfl
    have hm : var x ∈ y0 :: yt := hp.mem_iff.1 (by simp)
    have h1 : outF (y0 :: yt) (singleInput x) = true :=
      (outF_true _ _).2 ⟨var x, hm, by simp [var, singleInput]⟩
    rw [hF.1 x trivial] at h1
    exact Bool.noConfusion h1
  | succ s ih =>
    intro r h hinv
    obtain ⟨k, u, a, b, r₁, hk, hp, hr⟩ := (TR.inv h).2 s rfl
    have consume : ∀ b' : BF, r.Perm (b' :: r₁) → gF k a b = gF k (var x) b' →
        SUc x y0 yt (s + 1) r := by
      intro b' hrp hg
      unfold SUc
      rw [hg] at hr
      have hb' : InvX x b' := hinv b' (hrp.mem_iff.2 (by simp))
      have hr1 : ∀ w ∈ r₁, InvX x w := fun w hw => hinv w (hrp.mem_iff.2 (by simp [hw]))
      have sens : ∀ i, i ≠ x → gF k (var x) b' (pairInput i x) =
          gF k (var x) b' (singleInput i) → False := by
        intro i hi hgg
        have hd := TRF_det hr (pairInput i x) (singleInput i) (by
          intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · rw [List.eq_of_mem_replicate hw]; exact hgg
          · rw [← upd_single_true]
            exact (hr1 w hw).1 _ _)
        have h2 := outF_congr _ _ _ hd
        rw [hF.1 i trivial, hF.2 i x trivial trivial hi] at h2
        exact Bool.noConfusion h2
      have hbx : ∀ i, i ≠ x → b' (pairInput i x) = b' (singleInput i) := fun i _ => by
        rw [← upd_single_true]; exact hb'.1 _ _
      have hv1 : ∀ i, var x (pairInput i x) = true := fun i => by simp [var, pairInput]
      have hv2 : ∀ i, i ≠ x → var x (singleInput i) = false := fun i hi => by
        simp [var, singleInput, Ne.symm hi]
      rcases mono_cases k hk with rfl | rfl
      · left
        have hone : ∀ i, i ≠ x → b' (singleInput i) = true := by
          intro i hi
          by_contra hc
          have hc' : b' (singleInput i) = false := by simpa using hc
          apply sens i hi
          rw [gF_and]
          show (var x _ && b' _) = (var x _ && b' _)
          rw [hbx i hi, hc', hv2 i hi]; simp
        have hbo : b' = otop x := by
          funext p
          rw [← hb'.1 p false]
          by_cases hex : ∃ i, i ≠ x ∧ p i = true
          · obtain ⟨i, hi, hpi⟩ := hex
            have : otop x p = true := by simp only [otop, decide_eq_true_eq]; exact ⟨i, hi, hpi⟩
            rw [this]
            refine hb'.2.1 (singleInput i) _ ?_ (hone i hi)
            intro m hm
            have : m = i := by simpa [singleInput] using hm
            subst this
            rw [Function.update_of_ne hi]; exact hpi
          · have : otop x p = false := by simp only [otop, decide_eq_false_iff_not]; exact hex
            rw [this]
            have hz : Function.update p x false = fun _ => false := by
              funext m
              by_cases hm : m = x
              · subst hm; simp
              · rw [Function.update_of_ne hm]
                by_contra hc
                exact hex ⟨m, hm, by simpa using hc⟩
            rw [hz]; exact hb'.2.2
        have hmem : otop x ∈ r := hrp.mem_iff.2 (by simp [hbo])
        have hdead : rst x (gF 0 (var x) b') = zF := by
          funext p
          show (var x _ && b' _) = false
          simp [var]
        have hc := complete_run y0 yt hr
        obtain ⟨hd1, hd2⟩ := pot_dead x (thr_rst_ne hF x) hc
        rw [dcount_rep] at hd1 hd2
        simp only [hdead, ite_true] at hd1 hd2
        simp only [hmem, ite_true]
        refine ⟨by omega, fun S hS _ => UC_le (by omega) (hd2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hdead) hwz
        · have : rst x w = w := funext fun p => (hr1 w hw).1 p false
          rw [this]
          exact hS w (hrp.mem_iff.2 (by simp [hw]))
      · right
        have hzero : ∀ i, b' (singleInput i) = false := by
          intro i
          by_cases hi : i = x
          · subst hi
            rw [single_eq_upd, hb'.1]; exact hb'.2.2
          · by_contra hc
            have hc' : b' (singleInput i) = true := by simpa using hc
            apply sens i hi
            rw [gF_or]
            show (var x _ || b' _) = (var x _ || b' _)
            rw [hbx i hi, hc', hv1 i]; simp
        have hrel : List.Forall₂ (fun w w' => ∀ q, b' q = false → w q = w' q)
            (List.replicate (u + 1) (gF 1 (var x) b') ++ r₁)
            (List.replicate (u + 1) (var x) ++ r₁) := by
          refine List.rel_append ?_ (List.forall₂_same.2 fun _ _ _ _ => rfl)
          generalize u + 1 = n
          induction n with
          | zero => exact List.Forall₂.nil
          | succ n ihn =>
            refine List.Forall₂.cons (fun q hq => ?_) ihn
            show (var x q || b' q) = var x q
            rw [hq]; simp
        obtain ⟨ys', hy, hrun⟩ := TR.rel (A := MonoA)
          (fun w w' => ∀ q, b' q = false → w q = w' q)
          (fun k a a' b b' ha hb q hq => by
            show zeroGate k (a q) (b q) = zeroGate k (a' q) (b' q)
            rw [ha q hq, hb q hq]) hr _ hrel
        refine ⟨u, b', ys', s, rfl, ?_, ⟨fun i _ => ?_, fun i j _ _ hij => ?_⟩, ?_⟩
        · have := hy.length_eq
          simpa using this.symm
        · have e := outF_rel b' (singleInput i) (hzero i) _ _ hy
          have h3 : outF (b' :: ys') (singleInput i) =
              (b' (singleInput i) || outF ys' (singleInput i)) := by simp [outF]
          rw [h3, hzero i, ← e, hF.1 i trivial]; rfl
        · have h3 : outF (b' :: ys') (pairInput i j) =
              (b' (pairInput i j) || outF ys' (pairInput i j)) := by simp [outF]
          rw [h3]
          cases hbp : b' (pairInput i j)
          · have e := outF_rel b' (pairInput i j) hbp _ _ hy
            rw [← e, hF.2 i j trivial trivial hij]; rfl
          · rfl
        · have p1 : (b' :: (List.replicate (u + 1) (var x) ++ r₁)).Perm
              (List.replicate (u + 1) (var x) ++ r) :=
            List.perm_middle.symm.trans (List.Perm.append_left _ hrp.symm)
          exact TR.perm p1 (frame b' hrun)
    by_cases hax : a = var x
    · subst hax
      exact consume b hp.cons_inv rfl
    by_cases hbx : b = var x
    · subst hbx
      have hp' : (var x :: r).Perm (var x :: a :: r₁) := hp.trans (List.Perm.swap _ _ _)
      exact consume a hp'.cons_inv (mono_comm hk a (var x))
    have hx1 : var x ∈ r₁ := by
      have : var x ∈ a :: b :: r₁ := hp.mem_iff.1 (by simp)
      simp only [List.mem_cons] at this
      rcases this with h1 | h1 | h1
      · exact absurd h1.symm hax
      · exact absurd h1.symm hbx
      · exact h1
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx1
    have hr2 : r.Perm (a :: b :: (l₁ ++ l₂)) := by
      have p1 : (a :: b :: (l₁ ++ var x :: l₂)).Perm (var x :: a :: b :: (l₁ ++ l₂)) :=
        List.perm_middle (l₁ := a :: b :: l₁)
      exact (hp.trans p1).cons_inv
    have ha : InvX x a := hinv a (hr2.mem_iff.2 (by simp))
    have hb : InvX x b := hinv b (hr2.mem_iff.2 (by simp))
    have hsub : ∀ w ∈ l₁ ++ l₂, w ∈ r := fun w hw => hr2.mem_iff.2 (by simp [List.mem_append.1 hw])
    have p2 : (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ var x :: l₂)).Perm
        (var x :: (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂))) := by
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_middle
    have hinv2 : ∀ w ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂), InvX x w := by
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · rw [List.eq_of_mem_replicate hw]; exact InvX_gate hk ha hb
      · exact hinv w (hsub w hw)
    have hih := ih _ (TR.perm p2 hr) hinv2
    unfold SUc at hih ⊢
    rcases hih with ⟨hA1, hA2⟩ | ⟨c, h0, ys', s', hs', hl, hthr, hrun⟩
    · left
      by_cases hgo : gF k a b = otop x
      · have hm : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) := by
          rw [hgo]; simp
        simp only [hm, ite_true] at hA1 hA2
        refine ⟨by split_ifs <;> omega, fun S hS hSo => ?_⟩
        refine UC_le (by split_ifs <;> omega) (hA2 S ?_ hSo)
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgo]; exact hSo
        · exact hS w (hsub w hw)
      · have hiff : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) → otop x ∈ r := by
          intro hm
          rcases List.mem_append.1 hm with hm | hm
          · exact absurd (List.eq_of_mem_replicate hm).symm hgo
          · exact hsub _ hm
        have hcc : (if otop x ∈ r then 2 else 3) ≤
            (if otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) then 2 else 3) := by
          by_cases h1 : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂)
          · simp [h1, hiff h1]
          · simp only [h1, ite_false]; split_ifs <;> omega
        refine ⟨by omega, fun S hS hSo => ?_⟩
        have h1 := hA2 (fun w => w = gF k a b ∨ S w) (by
          intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (List.eq_of_mem_replicate hw)
          · exact Or.inr (hS w (hsub w hw))) (Or.inr hSo)
        have h2 := UC_gate k a b hk (hS a (hr2.mem_iff.2 (by simp)))
          (hS b (hr2.mem_iff.2 (by simp))) h1
        exact UC_le (by omega) h2
    · right
      refine ⟨c, h0, ys', s' + 1, by omega, hl, hthr, ?_⟩
      have p3 : (List.replicate (c + 1) (var x) ++ r).Perm
          (a :: b :: (List.replicate (c + 1) (var x) ++ (l₁ ++ l₂))) := by
        refine (List.Perm.append_left _ hr2).trans ?_
        exact List.perm_middle.trans (List.Perm.cons a List.perm_middle)
      have p4 : (List.replicate (c + 1) (var x) ++
          (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂))).Perm
          (List.replicate (u + 1) (gF k a b) ++
            (List.replicate (c + 1) (var x) ++ (l₁ ++ l₂))) :=
        List.perm_append_comm_assoc _ _ _
      subst hs'
      exact TR.perm p3.symm (TR.step k u hk (TR.perm p4 hrun))

theorem vars_list : ∀ (ws : List BF), (∀ w ∈ ws, ∃ i, w = var i) →
    ∃ idx : List (Fin 6), ws = idx.map var
  | [], _ => ⟨[], rfl⟩
  | w :: ws, h => by
    obtain ⟨i, rfl⟩ := h w (by simp)
    obtain ⟨idx, rfl⟩ := vars_list ws fun w hw => h w (by simp [hw])
    exact ⟨i :: idx, rfl⟩

theorem len_counts : ∀ (idx : List (Fin 6)),
    idx.length = idx.count 0 + idx.count 1 + idx.count 2 + idx.count 3 + idx.count 4 + idx.count 5
  | [] => rfl
  | j :: idx => by
    have ih := len_counts idx
    fin_cases j <;> simp <;> omega

theorem outF_perm {ys ys' : List BF} (h : ys.Perm ys') (p : Fin 6 → Bool) :
    outF ys p = outF ys' p := h.any_eq

theorem fiveRestriction (ι : Fin 5 → Fin 6) (inj : Function.Injective ι) (F : BF)
    (hs : ∀ j, F (singleInput (ι j))=false)
    (hp : ∀ j k, j≠k → F (pairInput (ι j) (ι k))=true)
    (h : UC gF MonoA 9 (fun w => ∃ j, w=var (ι j)) F) : False := by
  classical
  let embed (x : Fin 5 → Bool) (i : Fin 6) := if hh : ∃ j, ι j=i then x (Classical.choose hh) else false
  have atI (x : Fin 5 → Bool) (j : Fin 5) : embed x (ι j)=x j := by
    have hh : ∃ k, ι k=ι j := ⟨j,rfl⟩
    simp only [embed,dif_pos hh,inj (Classical.choose_spec hh)]
  have atOne (j : Fin 5) : embed (singleInput j)=singleInput (ι j) := by
    funext i
    by_cases e : ∃ k, ι k=i
    · obtain ⟨k,rfl⟩ := e
      simp [atI,singleInput,inj.eq_iff]
    · simp only [embed,dif_neg e,singleInput,Bool.false_eq,decide_eq_false_iff_not]
      exact (fun q => e ⟨j,q.symm⟩)
  have atTwo (j k : Fin 5) : embed (pairInput j k)=pairInput (ι j) (ι k) := by
    funext i
    by_cases e : ∃ r, ι r=i
    · obtain ⟨r,rfl⟩ := e
      simp [atI,pairInput,inj.eq_iff]
    · simp only [embed,dif_neg e,pairInput,Bool.false_eq,decide_eq_false_iff_not]
      rintro (q|q)
      · exact e ⟨j,q.symm⟩
      · exact e ⟨k,q.symm⟩
  let rel (w : BF) : ThresholdFive.BF := fun x => w (embed x)
  have smaller := UC_map (G' := ThresholdFive.gF) rel
    (fun _ _ _ => rfl) 9 _ (fun w => ∃ j, w=ThresholdFive.var j) F (by
      rintro w ⟨j,rfl⟩
      exact ⟨j,funext fun x => atI x j⟩) h
  apply ThresholdFive.M5 (F:=rel F) _ smaller
  exact ⟨fun j _ => by change F _ = false; rw [atOne,hs], fun j k _ _ ne => by
    change F _ = true; rw [atTwo,hp j k ne]⟩

end ThresholdSix

namespace ChargeTree9304
open Finset
open ThresholdFive (cCube cCubeMember cCubeVolume)

inductive Tree (α : Type) where
  | leaf (a : α)
  | node (isAnd : Bool) (l r : Tree α)

def gate (b x y : Bool) := if b then x && y else x || y

def eval {α : Type} (w : α → Bool) : Tree α → Bool
  | .leaf a => w a
  | .node b l r => gate b (eval w l) (eval w r)

def mass {α : Type} (w : α → ℕ) : Tree α → ℕ
  | .leaf a => w a
  | .node _ l r => mass w l + mass w r

def occ {α : Type} [DecidableEq α] (a : α) := mass (fun b => if b=a then 1 else 0)

def cut (x y : Bool) : Option Bool :=
  match x,y with
  | true,false => some false
  | false,true => some true
  | _,_ => none

def cuts {α I : Type} (w : I → α → Bool) : Tree α → List (I → Option Bool)
  | .leaf _ => []
  | .node b l r =>
    if b then (fun i => cut (eval (w i) l) (eval (w i) r)) :: (cuts w l ++ cuts w r)
    else cuts w l ++ cuts w r

def degree {I : Type} (ls : List (I → Option Bool)) (i : I) :=
  ls.countP fun c => (c i).isSome

def sides {I : Type} (c : I → Option Bool) (i j : I) :=
  (c i = some false ∧ c j = some true) ∨ (c i = some true ∧ c j = some false)

def separates {I : Type} (ls : List (I → Option Bool)) (i j : I) :=
  ∃ c ∈ ls, sides c i j

theorem charge {α I : Type} (w : I → α → Bool) (i : I) (t : Tree α) :
    degree (cuts w t) i + (eval (w i) t).toNat ≤ mass (fun a => (w i a).toNat) t := by
  induction t with
  | leaf a => simp [degree,cuts,eval,mass]
  | node b l r il ir =>
    cases b <;> cases el : eval (w i) l <;> cases er : eval (w i) r <;>
      simp [cuts,eval,gate,mass,degree,cut,el,er,List.countP_append] at * <;> omega

theorem separate {α I : Type} (w : I → α → Bool) (i j : I) (z : α → Bool) (R : Prop)
    (base : ∀ a, z a=true → w i a=false → w j a=false → R) (t : Tree α)
    (yes : eval z t=true) (noI : eval (w i) t=false) (noJ : eval (w j) t=false) :
    R ∨ separates (cuts w t) i j := by
  induction t with
  | leaf a => exact Or.inl (base a yes noI noJ)
  | node b l r il ir =>
    have left (h : R ∨ separates (cuts w l) i j) : R ∨ separates (cuts w (.node b l r)) i j := by
      rcases h with h|⟨c,hc,hs⟩
      · exact Or.inl h
      · exact Or.inr ⟨c,by cases b <;> simp [cuts,hc],hs⟩
    have right (h : R ∨ separates (cuts w r) i j) : R ∨ separates (cuts w (.node b l r)) i j := by
      rcases h with h|⟨c,hc,hs⟩
      · exact Or.inl h
      · exact Or.inr ⟨c,by cases b <;> simp [cuts,hc],hs⟩
    cases b with
    | false =>
      simp only [eval,gate,Bool.false_eq_true,ite_false,Bool.or_eq_true,Bool.or_eq_false_iff] at yes noI noJ
      exact yes.elim (fun h => left (il h noI.1 noJ.1)) (fun h => right (ir h noI.2 noJ.2))
    | true =>
      simp only [eval,gate,ite_true,Bool.and_eq_true] at yes noI noJ
      have lift (h : sides (fun x => cut (eval (w x) l) (eval (w x) r)) i j) :
          R ∨ separates (cuts w (.node true l r)) i j := Or.inr ⟨_,by simp [cuts],h⟩
      cases li : eval (w i) l <;> cases ri : eval (w i) r <;>
        cases lj : eval (w j) l <;> cases rj : eval (w j) r <;>
        simp only [li,ri,lj,rj,Bool.and_true,Bool.and_false] at noI noJ <;> try contradiction
      all_goals first
        | exact left (il yes.1 li lj)
        | exact right (ir yes.2 ri rj)
        | exact lift (by simp [sides,cut,li,ri,lj,rj])
        | simp_all

theorem degreeAppend {I : Type} (a b : List (I → Option Bool)) (i : I) :
    degree (a++b) i = degree a i + degree b i := by simp [degree,List.countP_append]

theorem pack {I : Type} [Fintype I] [DecidableEq I] (ls : List (I → Option Bool))
    (S : Finset I) (sep : ∀ i∈S, ∀ j∈S, i≠j → separates ls i j) (D : Finset I) (incl : D⊆S)
    (d : ℕ) (small : ∀ i∈D, degree ls i ≤ d) : D.card ≤ 2^d ∧ (D.card=2^d → D=S) := by
  classical
  let part (i : I) := (univ : Finset (Fin ls.length)).filter fun k => ((ls.get k) i).isSome
  let bits (i : I) (k : Fin ls.length) := ((ls.get k) i).getD false
  let cube (i : I) := cCube (part i) (bits i)
  let N := 2^ls.length
  have Npos : 0<N := Nat.two_pow_pos _
  have area (i : I) : (cube i).card * 2^(degree ls i) = N := by
    have sz : (part i).card = degree ls i := by
      simpa [part,degree,List.ofFn_get] using (List.countP_ofFn (List.get ls) (fun c => (c i).isSome)).symm
    simpa [cube,N,sz] using cCubeVolume (part i) (bits i)
  have disj : (S : Set I).PairwiseDisjoint cube := by
    intro i hi j hj ne
    obtain ⟨c,hc,colors⟩ := sep i hi j hj ne
    obtain ⟨k,hk⟩ := List.mem_iff_get.mp hc
    change ls[k.val] = c at hk
    apply disjoint_left.mpr
    intro w wi wj
    have a := (cCubeMember (part i) (bits i) w).mp wi
    have b := (cCubeMember (part j) (bits j) w).mp wj
    rcases colors with ⟨l,r⟩|⟨l,r⟩ <;>
      have p := a k (by simp [part,hk,l]) <;>
      have q := b k (by simp [part,hk,r]) <;>
      simp [bits,hk,l,r] at p q <;> exact Bool.noConfusion (p.symm.trans q)
  have cap : (∑ i∈S,(cube i).card) ≤ N := by
    rw [←card_biUnion disj]
    simpa [N] using card_le_univ (S.biUnion cube)
  have hD : D.card*N ≤ (∑ i∈D,(cube i).card)*2^d := by
    calc
      _ = ∑ _i∈D,N := by simp
      _ ≤ ∑ i∈D,(cube i).card*2^d := sum_le_sum fun i hi => by
        rw [←area i]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (small i hi))
      _ = _ := (sum_mul _ _ _).symm
  have cmp := sum_le_sum_of_subset (f:=fun i => (cube i).card) incl
  have lim := Nat.mul_le_mul_right (2^d) (cmp.trans cap)
  have bound : D.card ≤ 2^d := by
    by_contra! more
    have := Nat.mul_lt_mul_of_pos_right more Npos
    nlinarith
  refine ⟨bound,?_⟩
  intro exactD
  apply eq_of_subset_of_card_le incl
  by_contra! lt
  obtain ⟨z,zS,zD⟩ := exists_mem_notMem_of_card_lt_card lt
  have pos : 0<(cube z).card := by
    by_contra! h
    have key := area z
    rw [Nat.le_zero.mp h,zero_mul] at key
    omega
  have extra := sum_le_sum_of_subset (f:=fun i => (cube i).card) (insert_subset zS incl)
  rw [sum_insert zD] at extra
  have strict : (∑ i∈D,(cube i).card) < N := by omega
  have := Nat.mul_lt_mul_of_pos_right strict (Nat.two_pow_pos d)
  rw [exactD] at hD
  nlinarith

end ChargeTree9304

namespace ChargeTree9304
open Finset
open ThresholdFive (singleInput pairInput)

abbrev X := Fin 6
def plug (p : Tree X) (x : X → Bool) : Option X → Bool
  | none => eval x p
  | some i => x i

def combineTop {α : Type} (b : Bool) (l r : Option (Tree α)) : Option (Tree α) :=
  match l,r with
  | some a,some c => some (.node b a c)
  | none,r => if b then r else none
  | l,none => if b then l else none

def setTop {α : Type} : Tree (Option α) → Option (Tree α)
  | .leaf none => none
  | .leaf (some i) => some (.leaf i)
  | .node b l r => combineTop b (setTop l) (setTop r)

def runTop {α : Type} (x : α → Bool) (t : Option (Tree α)) := t.elim true (eval x)
def countTop {α : Type} [DecidableEq α] (i : α) (t : Option (Tree α)) := t.elim 0 (occ i)

theorem evalTop {α : Type} (t : Tree (Option α)) (x : α → Bool) :
    runTop x (setTop t) = eval (fun a => a.elim true x) t := by
  induction t with
  | leaf i => cases i <;> rfl
  | node b l r hl hr =>
    rw [eval,←hl,←hr]
    cases b <;> cases a : setTop l <;> cases c : setTop r <;>
      simp [setTop,combineTop,a,c,runTop,eval,gate]

theorem occTop {α : Type} [DecidableEq α] (t : Tree (Option α)) (i : α) :
    countTop i (setTop t) ≤ occ (some i) t := by
  induction t with
  | leaf j => cases j <;> simp [countTop,setTop,occ,mass]
  | node b l r il ir =>
    change _ ≤ occ (some i) l + occ (some i) r
    cases b <;> cases a : setTop l <;> cases c : setTop r <;>
      simp [setTop,combineTop,a,c,countTop,occ,mass] at * <;> omega

theorem evalMono {α : Type} (t : Tree α) {x y : α → Bool} (le : ∀ i, x i=true → y i=true) :
    eval x t=true → eval y t=true := by
  induction t with
  | leaf i => exact le i
  | node b l r il ir =>
    cases b <;> simp [eval,gate] <;> grind

theorem singMass (t : Tree X) (i : X) :
    mass (fun a => (singleInput i a).toNat) t = occ i t := by
  unfold occ
  congr 1
  funext a; by_cases h : a=i <;> simp [singleInput,h]

theorem plugMassOff (p : Tree X) (q : Tree (Option X)) (i : X) (off : eval (singleInput i) p=false) :
    mass (fun a => (plug p (singleInput i) a).toNat) q=occ (some i) q := by
  unfold occ
  congr 1
  funext a
  cases a with
  | none => simp [plug,off]
  | some j => by_cases h : j=i <;> simp [plug,singleInput,h]

theorem rawSep (t : Tree X) (i j : X) (yes : eval (pairInput i j) t=true)
    (noI : eval (singleInput i) t=false) (noJ : eval (singleInput j) t=false) :
    separates (cuts singleInput t) i j := by
  refine (separate singleInput i j (pairInput i j) False ?_ t yes noI noJ).resolve_left id
  intro a pos ni nj
  simp [pairInput,singleInput] at *
  tauto

theorem noFork (p : Tree X) (q : Tree (Option X))
    (raw : ∀ i, occ i p + occ (some i) q ≤ 2)
    (hs : ∀ i, eval (plug p (singleInput i)) q=false)
    (hp : ∀ i j, i≠j → eval (plug p (pairInput i j)) q=true) : False := by
  classical
  let on := univ.filter fun i : X => eval (singleInput i) p=true
  let off := (univ : Finset X) \ on
  let cs := cuts singleInput p ++ cuts (fun i : X => plug p (singleInput i)) q
  have allSep (i j : X) (ne : i≠j) : separates cs i j := by
    have h := separate (fun i : X => plug p (singleInput i)) i j (plug p (pairInput i j))
      (separates (cuts singleInput p) i j) (by
        intro a pos ni nj
        cases a with
        | none => exact rawSep p i j pos ni nj
        | some k =>
          simp [plug,pairInput,singleInput] at *
          tauto) q (hp i j ne) (hs i) (hs j)
    rcases h with ⟨c,hc,sc⟩|⟨c,hc,sc⟩ <;> exact ⟨c,by simp [cs,hc],sc⟩
  have cold (i : X) (hi : i∈off) : eval (singleInput i) p=false := by
    have := (mem_sdiff.mp hi).2
    simpa [on] using this
  have limited (i : X) (hi : i∈off) : degree cs i ≤ 2 := by
    have a := charge singleInput i p
    have b := charge (fun i : X => plug p (singleInput i)) i q
    rw [singMass,cold i hi] at a
    rw [plugMassOff p q i (cold i hi)] at b
    change degree (_++_) i ≤ 2
    rw [degreeAppend]
    have := raw i
    omega
  have packOff := pack cs univ (fun i _ j _ ne => allSep i j ne) off (subset_univ off) 2 limited
  have off3 : off.card≤3 := by
    by_contra! high
    have same := packOff.2 (by norm_num at *; omega)
    have num : off.card=6 := by simp [same]
    have le := packOff.1
    norm_num at le
    omega
  have total : off.card+on.card=6 := by
    simpa [off] using card_sdiff_add_card_eq_card (subset_univ on)
  have existsOn : on.Nonempty := card_pos.mp (by omega)
  have hot (i : X) (hi : i∈on) : eval (singleInput i) p=true := (mem_filter.mp hi).2
  have hotPair (i j : X) (hi : i∈on) : eval (pairInput i j) p=true :=
    evalMono p (fun k h => by simpa [singleInput,pairInput,of_decide_eq_true h] using (by simp : i=i)) (hot i hi)
  have topAgree (x : X → Bool) (h : eval x p=true) :
      runTop x (setTop q) = eval (plug p x) q := by
    rw [evalTop]
    congr 1
    funext a
    cases a <;> simp [plug,h]
  cases top : setTop q with
  | none =>
    obtain ⟨i,hi⟩ := existsOn
    have z := (topAgree (singleInput i) (hot i hi)).trans (hs i)
    rw [top] at z
    exact Bool.noConfusion z
  | some q' =>
    have single (i : X) (hi : i∈on) : eval (singleInput i) q'=false := by
      simpa [top,runTop] using (topAgree (singleInput i) (hot i hi)).trans (hs i)
    have paired (i j : X) (hi : i∈on) (ne : i≠j) : eval (pairInput i j) q'=true := by
      simpa [top,runTop] using (topAgree (pairInput i j) (hotPair i j hi)).trans (hp i j ne)
    have a := pack (cuts singleInput q') on (fun i hi j hj ne =>
      rawSep q' i j (paired i j hi ne) (single i hi) (single j hj)) on (by rfl) 1 (by
        intro i hi
        have pUse := charge singleInput i p
        rw [singMass,hot i hi] at pUse
        have one := occTop q i
        rw [top] at one
        change occ i q' ≤ _ at one
        have gateUse := charge singleInput i q'
        rw [singMass] at gateUse
        have budget := raw i
        simp only [Bool.toNat_true] at pUse
        omega)
    have ct := a.1
    norm_num at ct
    omega

end ChargeTree9304

namespace ChargeTree9304
open ThresholdSix
open ThresholdFive (TR map_perm_cons singleInput pairInput)
open Finset

def run {α : Type} (σ : α → BF) (t : Tree α) : BF :=
  fun x => eval (fun a => σ a x) t

def stock {α : Type} [DecidableEq α] (i : α) (ts : List (Tree α)) :=
  (ts.map (occ i)).sum

theorem stockPerm {α : Type} [DecidableEq α] (i : α) {xs ys : List (Tree α)} (hp : xs.Perm ys) :
    stock i xs=stock i ys := (hp.map _).sum_eq

theorem consumeTrees {α : Type} [DecidableEq α] (σ : α → BF) (k : Fin 4) (hk : MonoA k)
    {a b : BF} {r : List BF} (ts : List (Tree α)) (hs : (ts.map (run σ)).Perm (a::b::r)) :
    ∃ v t2, run σ v=gF k a b ∧ (t2.map (run σ)).Perm r ∧
      ∀ i, occ i v + stock i t2=stock i ts := by
  obtain ⟨l,t1,first,rfl,rem1⟩ := map_perm_cons (run σ) hs
  obtain ⟨r',t2,second,rfl,rem2⟩ := map_perm_cons (run σ) rem1
  refine ⟨.node (decide (k=0)) l r',t2,?_,rem2,?_⟩
  · rcases mono_cases k hk with rfl|rfl <;> rfl
  · intro i
    have a := stockPerm i first
    have b := stockPerm i second
    change occ i l + occ i r' + stock i t2=stock i ts
    simp only [stock,List.map_cons,List.sum_cons] at a b ⊢
    omega

theorem freeForest {α : Type} [DecidableEq α] (σ : α → BF) {F : BF} {s : ℕ} {ws : List BF}
    (h : MR [F] s ws) (ts : List (Tree α)) (acts : (ts.map (run σ)).Perm ws)
    (full : ws.length=s+1) :
    ∃ t : Tree α, run σ t=F ∧ ∀ i, occ i t=stock i ts := by
  induction s generalizing ws ts with
  | zero =>
    have hp := acts.trans ((TR.inv h).1 rfl)
    obtain ⟨t,t2,per,e,tail⟩ := map_perm_cons _ hp
    have empty : t2=[] := List.length_eq_zero_iff.mp (by simpa using tail.length_eq)
    subst t2
    refine ⟨t,e,fun i => ?_⟩
    rw [stockPerm i per]; simp [stock]
  | succ s ih =>
    obtain ⟨k,u,a,b,r,hk,perm,hr⟩ := (TR.inv h).2 s rfl
    have cap := TR.len hr
    have len := perm.length_eq
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil] at cap len
    obtain rfl : u=0 := by omega
    obtain ⟨v,t2,val,rem,cost⟩ := consumeTrees σ k hk ts (acts.trans perm)
    obtain ⟨t,hev,ct⟩ := ih hr (v::t2)
      (by simpa only [Nat.zero_add,List.map_cons,List.replicate_one,List.singleton_append,val] using rem.cons (gF k a b))
      (by simp; omega)
    refine ⟨t,hev,fun i => (ct i).trans (?_ : stock i (v::t2)=stock i ts)⟩
    exact cost i

def raiseT {α : Type} : Tree α → Tree (Option α)
  | .leaf a => .leaf (some a)
  | .node b l r => .node b (raiseT l) (raiseT r)

def withGate (v : Tree X) (a : Option X) : BF := fun x => plug v x a

theorem runRaise (p t : Tree X) : run (withGate p) (raiseT t)=run var t := by
  funext x
  induction t with
  | leaf a => rfl
  | node b l r il ir =>
    change gate b (run (withGate p) (raiseT l) x) (run (withGate p) (raiseT r) x) = gate b (run var l x) (run var r x)
    rw [il,ir]

theorem occRaise (t : Tree X) (i : X) : occ (some i) (raiseT t)=occ i t := by
  induction t with
  | leaf a => simp [occ,raiseT,mass]
  | node b l r il ir => exact congrArg₂ (·+·) il ir

theorem oneForest {F : BF} {s : ℕ} {ws : List BF} (h : MR [F] s ws)
    (ts : List (Tree X)) (acts : (ts.map (run var)).Perm ws) (full : ws.length=s) :
    ∃ (v : Tree X) (t : Tree (Option X)), run (withGate v) t=F ∧
      ∀ i, occ i v+occ (some i) t=stock i ts := by
  induction s generalizing ws ts with
  | zero =>
    have len := ((TR.inv h).1 rfl).length_eq
    simp only [List.length_cons,List.length_nil] at len
    omega
  | succ s ih =>
    obtain ⟨k,u,a,b,r,hk,perm,hr⟩ := (TR.inv h).2 s rfl
    have cap := TR.len hr
    have len := perm.length_eq
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil] at cap len
    obtain ⟨v,t2,val,rem,cost⟩ := consumeTrees var k hk ts (acts.trans perm)
    have choices : u=0 ∨ u=1 := by omega
    rcases choices with rfl|rfl
    · obtain ⟨p,t,he,ct⟩ := ih hr (v::t2)
        (by simpa only [Nat.zero_add,List.map_cons,List.replicate_one,List.singleton_append,val] using rem.cons (gF k a b))
        (by simp; omega)
      exact ⟨p,t,he,fun i => (ct i).trans (cost i)⟩
    · let fresh : Tree (Option X) := .leaf none
      have rem' : ((t2.map raiseT).map (run (withGate v))).Perm r := by
        simpa only [List.map_map,Function.comp_def,runRaise] using rem
      have hval : run (withGate v) fresh=gF k a b := val
      let remaining := fresh :: fresh :: t2.map raiseT
      obtain ⟨t,he,ct⟩ := freeForest (withGate v) hr remaining
        (by simpa [remaining,hval] using (rem'.cons (gF k a b)).cons (gF k a b))
        (by simp; omega)
      refine ⟨v,t,he,fun i => ?_⟩
      rw [ct]
      have eq : stock (some i) remaining=stock i t2 := by
        simp [stock,remaining,fresh,occ,mass,List.map_map,Function.comp_def,
          show ∀ a : Tree X, mass (fun b : Option X => if b=some i then 1 else 0) (raiseT a)=occ i a from fun a => occRaise a i]
      rw [eq,cost i]

theorem rawStock (idx : List X) (i : X) : stock i (idx.map Tree.leaf)=idx.count i := by
  induction idx with
  | nil => rfl
  | cons a l ih =>
    simp only [stock,List.map_cons,List.sum_cons,occ,mass,List.count_cons] at ih ⊢
    rw [ih]
    by_cases ne : a=i <;> simp [ne] <;> omega

theorem manyLeaves (F : BF) (hF : ThrL (fun _ => True) F) (idx : List X) (s : ℕ)
    (h : MR [F] s (idx.map var)) (many : ∀ i, 2 ≤ idx.count i) (small : s≤12) : False := by
  classical
  have cap := TR.len h
  simp only [List.length_map,List.length_cons,List.length_nil] at cap
  have count := len_counts idx
  have sumLo (i : X) := many i
  have h0 := sumLo 0
  have h1 := sumLo 1
  have h2 := sumLo 2
  have h3 := sumLo 3
  have h4 := sumLo 4
  have h5 := sumLo 5
  have perm : ((idx.map Tree.leaf).map (run var)).Perm (idx.map var) := by
    rw [List.map_map]
    exact List.Perm.refl _
  by_cases full : idx.length=s+1
  · obtain ⟨t,e,ct⟩ := freeForest var h (idx.map Tree.leaf) perm (by simpa using full)
    have deg (i : X) : degree (cuts singleInput t) i ≤ idx.count i := by
      have a := charge singleInput i t
      rw [singMass,ct,rawStock] at a
      omega
    let D := (univ : Finset X).filter fun i => 2=idx.count i
    have sep (i j : X) (ne : i≠j) : separates (cuts singleInput t) i j :=
      rawSep t i j ((congrFun e _).trans (hF.2 i j trivial trivial ne))
        ((congrFun e _).trans (hF.1 i trivial)) ((congrFun e _).trans (hF.1 j trivial))
    have bound := (pack (cuts singleInput t) univ (fun i _ j _ ne => sep i j ne) D (subset_univ D) 2 (by
      intro i hi
      have := (mem_filter.mp hi).2
      have := deg i
      omega)).1
    have sumD : ∑ i : X, (if i∈D then 2 else 3 : ℕ) ≤ ∑ i : X, idx.count i := by
      apply sum_le_sum
      intro i _
      by_cases hi : i∈D
      · simp only [hi,ite_true]; exact many i
      · have diff : 2≠idx.count i := by simpa [D] using hi
        simp only [hi,ite_false]
        have := many i
        omega
    rw [sum_ite] at sumD
    have sizeOff : ((univ : Finset X).filter fun i => i∉D).card = 6-D.card := by
      have eq : ((univ : Finset X).filter fun i => i∉D)=univ\D := by ext; simp
      rw [eq,card_sdiff_of_subset (subset_univ D)]; simp
    simp only [filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul,sizeOff] at sumD
    simp only [Fin.sum_univ_six] at sumD
    change D.card*2+(6-D.card)*3 ≤ idx.count 0+idx.count 1+idx.count 2+idx.count 3+idx.count 4+idx.count 5 at sumD
    norm_num at bound
    omega
  · have exactLen : idx.length=s := by omega
    obtain ⟨v,t,e,ct⟩ := oneForest h (idx.map Tree.leaf) perm (by simpa using exactLen)
    have max (i : X) : idx.count i ≤ 2 := by
      fin_cases i <;> first
      | change idx.count 0 ≤ 2; omega
      | change idx.count 1 ≤ 2; omega
      | change idx.count 2 ≤ 2; omega
      | change idx.count 3 ≤ 2; omega
      | change idx.count 4 ≤ 2; omega
      | change idx.count 5 ≤ 2; omega
    apply noFork v t (fun i => by rw [ct,rawStock]; exact max i)
    · intro i
      exact (congrFun e _).trans (hF.1 i trivial)
    · intro i j ne
      exact (congrFun e _).trans (hF.2 i j trivial trivial ne)

end ChargeTree9304

namespace ThresholdSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open ThresholdFive (UC UC_le UC_gate)

def gv (g : Gate) (W : List BF) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)

def wiresF : List Gate → List BF → List BF
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])

theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 6 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

theorem wires_eq (x : Fin 6 → Bool) : ∀ (gs : List Gate) (W : List BF),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun w => w x) = (wiresF gs W).map fun w => w x
  | [], W => rfl
  | g :: gs, W => by
    simp only [List.foldl_cons, wiresF]
    rw [← wires_eq x gs (W ++ [gv g W])]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, gv, getD_map_x]

theorem getD_mem (W : List BF) (i : ℕ) : W.getD i zF ∈ W ∨ W.getD i zF = zF := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[i]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

def oneF : BF := fun _ => true
def Ready (S : BF → Prop) (w : BF) := w=zF ∨ w=oneF ∨ S w

theorem monoForm (g : Gate) (W : List BF) (op : g.op = GateOp.and ∨ g.op = GateOp.or)
    (arity : g.inputs.length≤2) (S : BF → Prop) (available : ∀ w∈W, Ready S w) :
    Ready S (gv g W) ∨ ∃ k a b, MonoA k ∧ S a ∧ S b ∧ gv g W=gF k a b := by
  have get (i : ℕ) : Ready S (W.getD i zF) :=
    (getD_mem W i).elim (available _) Or.inl
  have binary (k : Fin 4) (hk : MonoA k) (a b : BF) (h : gv g W=gF k a b)
      (ha : Ready S a) (hb : Ready S b) :
      Ready S (gv g W) ∨ ∃ k a b, MonoA k ∧ S a ∧ S b ∧ gv g W=gF k a b := by
    rcases mono_cases k hk with rfl|rfl <;> rw [h]
    · rcases ha with rfl|rfl|aS
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl hb
      · rcases hb with rfl|rfl|bS
        · exact Or.inl (Or.inl (funext fun x => Bool.and_false _))
        · exact Or.inl (Or.inr (Or.inr (by simpa [gF_and,oneF] using aS)))
        · exact Or.inr ⟨0,a,b,hk,aS,bS,rfl⟩
    · rcases ha with rfl|rfl|aS
      · exact Or.inl hb
      · exact Or.inl (Or.inr (Or.inl rfl))
      · rcases hb with rfl|rfl|bS
        · exact Or.inl (Or.inr (Or.inr (by simpa [gF_or,zF] using aS)))
        · exact Or.inl (Or.inr (Or.inl (funext fun x => Bool.or_true _)))
        · exact Or.inr ⟨1,a,b,hk,aS,bS,rfl⟩
  rcases g with ⟨operation,ins⟩
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · rcases op with rfl|rfl
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inl rfl)
  · rcases op with rfl|rfl <;> apply Or.inl <;> convert get i using 1 <;> congr 1 <;> funext x <;> simp [gv,GateOp.eval]
  · rcases op with rfl|rfl
    · exact binary 0 (by simp [MonoA] : MonoA 0) _ _ (by funext x; simp [gv,GateOp.eval,gF_and]) (get i) (get j)
    · exact binary 1 (by simp [MonoA] : MonoA 1) _ _ (by funext x; simp [gv,GateOp.eval,gF_or]) (get i) (get j)
  · simp at arity

theorem circuitRun (gs : List Gate) (o : ℕ) (mono : ∀ g∈gs,
    (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) (S : BF → Prop)
    (W : List BF) (stored : ∀ w∈W, Ready S w) :
    Ready (UC gF MonoA gs.length S) ((wiresF gs W).getD o zF) := by
  induction gs generalizing S W with
  | nil => exact (getD_mem W o).elim (stored _) Or.inl
  | cons g gs ih =>
    have tail := fun f (hf : f∈gs) => mono f (List.mem_cons_of_mem _ hf)
    obtain ⟨op,arity⟩ := mono g (by simp)
    rcases monoForm g W op arity S stored with free|⟨k,a,b,hk,ha,hb,eq⟩
    · have prev := ih tail S (W++[gv g W]) (by
        intro w hw
        rcases List.mem_append.mp hw with left|right
        · exact stored _ left
        · simpa using (List.mem_singleton.mp right ▸ free : Ready S w))
      rcases prev with h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (UC_le (by simp) h))
    · let A (w : BF) := w=gF k a b ∨ S w
      have prev := ih tail A (W++[gv g W]) (by
        intro w hw
        rcases List.mem_append.mp hw with left|right
        · exact (stored w left).imp id (fun q => q.imp id Or.inr)
        · obtain rfl := List.mem_singleton.mp right
          exact Or.inr (Or.inr (Or.inl eq)))
      rcases prev with h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (UC_gate k a b hk ha hb h))

theorem monoToRun {C : Circuit} (mono : Monotone2 C) (F : BF) (hF : ThrL (fun _ => True) F)
    (acts : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=F x) :
    ∃ t, t≤C.size ∧ ∃ ws, (∀ w∈ws, ∃ i, w=var i) ∧ MR [F] t ws := by
  have same : (wiresF C.gates (List.ofFn var)).getD C.output zF=F := by
    funext x
    rw [←acts x,←getD_map_x,←wires_eq]
    simp only [Circuit.eval,Circuit.wires,List.map_ofFn]
    rfl
  have h := circuitRun C.gates C.output mono (fun w => ∃ i, w=var i) (List.ofFn var) (by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact Or.inr (Or.inr ⟨i,rfl⟩))
  rw [same] at h
  rcases h with hz|hu|real
  · exact False.elim (thr_ne_zero hF hz)
  · have bad := hF.1 0 trivial
    rw [hu] at bad
    contradiction
  · exact to_run hF real

end ThresholdSix

namespace ThresholdSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open ThresholdFive (TR UC_le singleInput pairInput)

theorem noTwelveRun : ∀ (s : ℕ) (y0 : BF) (yt : List BF) (ws : List BF), MR (y0 :: yt) s ws →
    (∀ w ∈ ws, ∃ i, w = var i) → s + yt.length ≤ 12 →
    ThrL (fun _ => True) (outF (y0 :: yt)) → False := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro y0 yt ws h hw hs hF
    have hlen := TR.len h
    obtain ⟨idx, rfl⟩ := vars_list ws hw
    have hpres : ∀ i, i ∈ idx := by
      intro i
      by_contra hi
      obtain ⟨j, hj, -⟩ := ex_third i i
      have hd := TRF_det h (pairInput i j) (singleInput j) (by
        intro w hw'
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
        have : m ≠ i := fun e => hi (e ▸ hm)
        simp [var, pairInput, singleInput, this])
      have h2 := outF_congr _ _ _ hd
      rw [hF.1 j trivial, hF.2 i j trivial trivial (Ne.symm hj)] at h2
      exact Bool.noConfusion h2
    simp only [List.length_map, List.length_cons] at hlen
    by_cases hall : ∀ i, 2 ≤ idx.count i
    · exact ChargeTree9304.manyLeaves (outF (y0::yt)) hF idx (s+yt.length) (complete_run y0 yt h) hall hs
    · obtain ⟨x, hx⟩ := not_forall.1 hall
      have hx1 : idx.count x = 1 := by
        have := List.count_pos_iff.2 (hpres x)
        omega
      have hp : (idx.map var).Perm (var x :: (idx.erase x).map var) :=
        (List.perm_cons_erase (hpres x)).map var
      have hnx : x ∉ idx.erase x := by
        intro hm
        have := List.count_pos_iff.2 hm
        rw [List.count_erase_self] at this
        omega
      have hinv : ∀ w ∈ (idx.erase x).map var, InvX x w := by
        intro w hw'
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
        exact InvX_var fun e => hnx (e ▸ hm)
      have hsu := SU x y0 yt hF s _ (TR.perm hp h) hinv
      unfold SUc at hsu
      rcases hsu with ⟨hA1, hA2⟩ | ⟨c, h0, ys', s', hs', hl, hthr, hrun⟩
      · have hno : otop x ∉ (idx.erase x).map var := by
          intro hm
          obtain ⟨m, -, he⟩ := List.mem_map.1 hm
          obtain ⟨j, hj1, hj2⟩ := ex_third m x
          have h5 := congrFun he (singleInput j)
          have h6 : var m (singleInput j) = false := by simp [var, singleInput, Ne.symm hj1]
          have h7 : otop x (singleInput j) = true := by
            simp only [otop, decide_eq_true_eq]
            exact ⟨j, hj2, by simp [singleInput]⟩
          rw [h6, h7] at h5
          exact Bool.noConfusion h5
        simp only [hno, ite_false] at hA1 hA2
        have h6 := hA2 (fun w => w = otop x ∨ ∃ j, w = var (x.succAbove j)) (by
          intro w hw'
          obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
          have hmx : m ≠ x := fun e => hnx (e ▸ hm)
          obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hmx
          exact Or.inr ⟨j, by rw [hj]⟩) (Or.inl rfl)
        have h7 := top_elim (otop x) _ (fun w => ∃ j, w = var (x.succAbove j)) _ (by
          rintro w ⟨j, rfl⟩ p hp'
          simp only [otop, decide_eq_true_eq]
          exact ⟨x.succAbove j, Fin.succAbove_ne x j, hp'⟩) (by
          intro he
          have h8 := (thr_rst hF x).1 0
          rw [he] at h8
          have h9 : otop x (singleInput (x.succAbove 0)) = true := by
            simp only [otop, decide_eq_true_eq]
            exact ⟨x.succAbove 0, Fin.succAbove_ne x 0, by simp [singleInput]⟩
          rw [h9] at h8
          exact Bool.noConfusion h8) h6
        exact fiveRestriction x.succAbove Fin.succAbove_right_injective _ (thr_rst hF x).1 (thr_rst hF x).2
          (UC_le (by omega) h7)
      · refine ih s' (by omega) h0 ys' _ hrun ?_ (by omega) hthr
        intro w hw'
        rcases List.mem_append.1 hw' with hw' | hw'
        · exact ⟨x, List.eq_of_mem_replicate hw'⟩
        · obtain ⟨m, -, rfl⟩ := List.mem_map.1 hw'
          exact ⟨m, rfl⟩

theorem threshold13 {C : Circuit} (mono : Monotone2 C) (acts : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=decide (Crown9304.two x)) : 13≤C.size := by
  let F : BF := fun x => decide (Crown9304.two x)
  have thr : ThrL (fun _ => True) F := by
    refine ⟨?_,?_⟩
    · exact (show ∀ i : Fin 6, True → F (singleInput i)=false by decide)
    · exact (show ∀ i j : Fin 6, True → True → i≠j → F (pairInput i j)=true by decide)
  obtain ⟨s,sz,ws,hw,run⟩ := monoToRun mono F thr acts
  by_contra! short
  apply noTwelveRun s F [] ws run hw (by simp; omega)
  have eq : outF [F] = F := funext fun x => by simp [outF]
  rw [eq]
  exact thr

theorem solution : ¬ PEqualNP.Represents.RepSizeAtMost Crown9304.A 18 := by
  rintro ⟨C,mono,size,rep⟩
  obtain ⟨D,hd,sz,acts⟩ := Crown9304.shortThreshold mono rep size
  have := threshold13 hd acts
  omega

end ThresholdSix

end PEqualNP.Outside.L_meta_18186

theorem PEqualNP.Outside.L_meta_18186 : ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => decide (u ≠ v)) s → 18 ≤ s := by
  rintro s ⟨C, mono, size, rep⟩
  by_contra h
  exact PEqualNP.Outside.L_meta_18186.ThresholdSix.solution ⟨C, mono, by omega, rep⟩
