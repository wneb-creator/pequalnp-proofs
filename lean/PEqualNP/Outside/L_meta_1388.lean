import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1388

-- Adapted from PEqualNP/Outside/L_meta_616.lean at f502132ed757 (Apache-2.0).
-- Changes: nested under the assigned module and renamed the cubic bound.

namespace LMeta616

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

lemma elim_smaller_circuit {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
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
      (hfun _).mpr ⟨u0, v0, huv0, by simp, by simp⟩
    unfold Circuit.eval at ht
    rw [wires_oob C _ C.output (by omega)] at ht
    exact absurd ht (by decide)
  have hzero : C.eval (List.ofFn (fun _ : Fin n => false)) = false := by
    cases h : C.eval (List.ofFn (fun _ : Fin n => false)) with
    | false => rfl
    | true =>
      obtain ⟨_, _, _, hu, _⟩ := (hfun _).mp h
      exact absurd hu (by decide)
  have hout_ne : skip = true → C.output ≠ n + j0 := fun h => (hunused h).1
  cases hout : res.1.getD C.output (Sum.inl false) with
  | inl b =>
    cases b
    · have ht := hcore.2.2.2.2 (fun t : Fin n => decide (t = u0 ∨ t = v0)) C.output hout_lt hout_ne
      rw [hout] at ht
      change false = C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) at ht
      have ht2 : C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true :=
        (hfun _).mpr ⟨u0, v0, huv0, by simp, by simp⟩
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

lemma large_indep_set {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 1 ≤ n)
    (hcubic : ∀ v : Fin n, (G.neighborSet v).ncard = 3)
    (hno4 : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) :
    ∃ J : Finset (Fin n), (∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v) ∧ n + 1 ≤ 4 * J.card := by
  classical
  have hdeg3 : ∀ v : Fin n, G.degree v = 3 := by
    intro v
    have h := hcubic v
    rw [Set.ncard_eq_toFinset_card'] at h
    have heq : (G.neighborSet v).toFinset = G.neighborFinset v := by
      ext u; simp
    rw [heq] at h
    exact h
  let closedN : Finset (Fin n) → Finset (Fin n) := fun J => J.biUnion (fun u => insert u (G.neighborFinset u))
  have hclosedN_card : ∀ u : Fin n, (insert u (G.neighborFinset u)).card = 4 := by
    intro u
    rw [Finset.card_insert_of_notMem, ← SimpleGraph.degree, hdeg3 u]
    rw [SimpleGraph.mem_neighborFinset]
    exact G.loopless.irrefl u
  have hstep : ∀ k : ℕ, ∀ J : Finset (Fin n), (Finset.univ \ closedN J).card = k →
      (∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v) → (closedN J).card + 1 ≤ 4 * J.card →
      ∃ J' : Finset (Fin n), (∀ u ∈ J', ∀ v ∈ J', ¬ G.Adj u v) ∧ n + 1 ≤ 4 * J'.card := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro J hk hind hcard
      by_cases hemp : (Finset.univ \ closedN J).Nonempty
      · obtain ⟨u, hu⟩ := hemp
        have huNot : u ∉ closedN J := (Finset.mem_sdiff.mp hu).2
        have huNotJ : u ∉ J := fun huJ => huNot (Finset.mem_biUnion.mpr ⟨u, huJ, Finset.mem_insert_self u _⟩)
        have huNoAdj : ∀ v ∈ J, ¬ G.Adj u v := fun v hv huv =>
          huNot (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset G v u).mpr huv.symm)⟩)
        set J1 := insert u J
        have hind1 : ∀ a ∈ J1, ∀ b ∈ J1, ¬ G.Adj a b := by
          intro a ha b hb
          rcases Finset.mem_insert.mp ha with rfl | haJ <;> rcases Finset.mem_insert.mp hb with rfl | hbJ
          · exact G.loopless.irrefl _
          · exact huNoAdj b hbJ
          · exact fun h => huNoAdj a haJ h.symm
          · exact hind a haJ b hbJ
        have hJ1card : J1.card = J.card + 1 := Finset.card_insert_of_notMem huNotJ
        have hcl1 : closedN J1 = insert u (G.neighborFinset u) ∪ closedN J := Finset.biUnion_insert
        have hcl1_card : (closedN J1).card + 1 ≤ 4 * J1.card := by
          rw [hcl1, hJ1card]
          have hun := Finset.card_union_le (insert u (G.neighborFinset u)) (closedN J)
          rw [hclosedN_card u] at hun
          omega
        have hsub : Finset.univ \ closedN J1 ⊂ Finset.univ \ closedN J := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨?_, ?_⟩
          · intro x hx
            rw [Finset.mem_sdiff] at hx ⊢
            refine ⟨hx.1, fun hxcl => hx.2 ?_⟩
            rw [hcl1]; exact Finset.mem_union_right _ hxcl
          · intro heq
            have hu1 : u ∈ Finset.univ \ closedN J1 := heq ▸ hu
            have hu_in : u ∈ closedN J1 := by rw [hcl1]; exact Finset.mem_union_left _ (Finset.mem_insert_self u _)
            exact (Finset.mem_sdiff.mp hu1).2 hu_in
        have hklt : (Finset.univ \ closedN J1).card < k := by
          rw [← hk]; exact Finset.card_lt_card hsub
        exact ih _ hklt J1 rfl hind1 hcl1_card
      · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
        have heq : closedN J = Finset.univ := Finset.eq_univ_iff_forall.mpr (fun x => hemp (Finset.mem_univ x))
        rw [heq, Finset.card_univ, Fintype.card_fin] at hcard
        exact ⟨J, hind, hcard⟩
  let v0 : Fin n := ⟨0, by omega⟩
  have hv0deg : (G.neighborFinset v0).card = 3 := hdeg3 v0
  rw [Finset.card_eq_three] at hv0deg
  obtain ⟨u1, u2, u3, h12, h13, h23, hN0⟩ := hv0deg
  have hu1 : G.Adj v0 u1 := (SimpleGraph.mem_neighborFinset G v0 u1).mp (hN0 ▸ by simp)
  have hu2 : G.Adj v0 u2 := (SimpleGraph.mem_neighborFinset G v0 u2).mp (hN0 ▸ by simp)
  have hu3 : G.Adj v0 u3 := (SimpleGraph.mem_neighborFinset G v0 u3).mp (hN0 ▸ by simp)
  obtain ⟨a, b, hab, hna, hvb1, hvb2⟩ : ∃ a b : Fin n, a ≠ b ∧ ¬ G.Adj a b ∧ G.Adj v0 a ∧ G.Adj v0 b := by
    by_cases h : G.Adj u1 u2
    · by_cases h' : G.Adj u2 u3
      · exfalso
        exact hno4 v0 u1 u2 u3 (G.ne_of_adj hu1) (G.ne_of_adj hu2) (G.ne_of_adj hu3) h12 h13 h23 hu1 h h' hu3.symm
      · exact ⟨u2, u3, h23, h', hu2, hu3⟩
    · exact ⟨u1, u2, h12, h, hu1, hu2⟩
  set J0 : Finset (Fin n) := {a, b}
  have hind0 : ∀ u ∈ J0, ∀ v ∈ J0, ¬ G.Adj u v := by
    intro u hu v hv
    simp only [J0, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact G.loopless.irrefl _
    · exact hna
    · exact fun h => hna h.symm
    · exact G.loopless.irrefl _
  have hcl0 : (closedN J0).card + 1 ≤ 4 * J0.card := by
    have hJ0c : J0.card = 2 := Finset.card_pair hab
    have hcl_eq : closedN J0 = insert a (G.neighborFinset a) ∪ insert b (G.neighborFinset b) := by
      simp [closedN, J0]
    have hv0_inter : v0 ∈ insert a (G.neighborFinset a) ∩ insert b (G.neighborFinset b) := by
      rw [Finset.mem_inter]
      exact ⟨Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset G a v0).mpr hvb1.symm),
             Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset G b v0).mpr hvb2.symm)⟩
    have hinter_pos : 1 ≤ (insert a (G.neighborFinset a) ∩ insert b (G.neighborFinset b)).card :=
      Finset.card_pos.mpr ⟨v0, hv0_inter⟩
    have hun := Finset.card_union_add_card_inter (insert a (G.neighborFinset a)) (insert b (G.neighborFinset b))
    rw [hclosedN_card a, hclosedN_card b] at hun
    rw [hcl_eq, hJ0c]
    omega
  exact hstep _ J0 rfl hind0 hcl0

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

set_option maxHeartbeats 2000000 in
lemma main_bound (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcubic : ∀ v : Fin n, (G.neighborSet v).ncard = 3)
    (hno4 : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (ht_ex : ∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t)
    (ht_min : ∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) :
    ∀ s : ℕ, ∀ C : Circuit, C.size = s →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      n + t ≤ s := by
  classical
  have hdeg3 : ∀ v : Fin n, G.degree v = 3 := by
    intro v
    have h := hcubic v
    rw [Set.ncard_eq_toFinset_card'] at h
    have heq : (G.neighborSet v).toFinset = G.neighborFinset v := by ext u; simp
    rw [heq] at h
    exact h
  have hdistinct_nbrs : ∀ v w : Fin n, v ≠ w → ∃ u : Fin n, G.Adj v u ∧ ¬ G.Adj w u := by
    intro v w hvw
    by_contra hall
    have hsub : G.neighborFinset v ⊆ G.neighborFinset w := by
      intro u hu
      rw [SimpleGraph.mem_neighborFinset] at hu ⊢
      by_contra hnw
      exact hall ⟨u, hu, hnw⟩
    have hcard : (G.neighborFinset v).card = 3 := hdeg3 v
    rw [Finset.card_eq_three] at hcard
    obtain ⟨u1, u2, u3, h12, _, _, hset⟩ := hcard
    have hv1 : G.Adj v u1 := (SimpleGraph.mem_neighborFinset G v u1).mp (hset ▸ by simp)
    have hv2 : G.Adj v u2 := (SimpleGraph.mem_neighborFinset G v u2).mp (hset ▸ by simp)
    have hw1 : G.Adj w u1 := (SimpleGraph.mem_neighborFinset G w u1).mp (hsub (hset ▸ by simp))
    have hw2 : G.Adj w u2 := (SimpleGraph.mem_neighborFinset G w u2).mp (hsub (hset ▸ by simp))
    exact hno4 v u1 w u2 (G.ne_of_adj hv1) hvw (G.ne_of_adj hv2) (G.ne_of_adj hw1).symm h12 (G.ne_of_adj hw2) hv1 hw1.symm hw2 hv2.symm
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro C hCsize hmono hfun
    have hCglen : C.gates.length = s := hCsize
    by_cases hn0 : n = 0
    · subst hn0
      have ht0 : t ≤ 0 := ht_min ∅ (fun u => Fin.elim0 u)
      omega
    have hn1 : 1 ≤ n := by omega
    have hedge : ∃ u v : Fin n, G.Adj u v := by
      let v0 : Fin n := ⟨0, hn1⟩
      have hpos : 0 < (G.neighborFinset v0).card := by rw [← SimpleGraph.degree, hdeg3 v0]; omega
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      exact ⟨v0, u, (SimpleGraph.mem_neighborFinset G v0 u).mp hu⟩
    have hmin : ∀ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' → C'.size < s →
        (∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) → n + t ≤ s := by
      intro C' hC'm hC'sz hC'eq
      have hC'fun : ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
        intro x; rw [hC'eq x, hfun x]
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
        obtain ⟨C', hm', hsz', heq'⟩ := elim_smaller_circuit G C hmono hfun hedge j0 hj0len (fun _ => Sum.inl false) false
          (fun _ _ _ => trivial) (fun _ x _ _ _ _ => (hf x).symm) (by intro h; cases h)
        exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
      · intro ht
        obtain ⟨C', hm', hsz', heq'⟩ := elim_smaller_circuit G C hmono hfun hedge j0 hj0len (fun _ => Sum.inl true) false
          (fun _ _ _ => trivial) (fun _ x _ _ _ _ => (ht x).symm) (by intro h; cases h)
        exact hnot_smaller C' hm' (by rw [← hCsize]; exact hsz') heq'
      · intro w0 hw0 heqw
        obtain ⟨C', hm', hsz', heq'⟩ := elim_smaller_circuit G C hmono hfun hedge j0 hj0len (fun tbl => tbl.getD w0 (Sum.inl false)) false
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
            obtain ⟨a, b, hab, ha, hb⟩ := (hfun _).mp h
            simp only [decide_eq_true_eq] at ha hb
            subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
        unfold Circuit.eval at hfv
        rw [wires_input C _ C.output hw] at hfv
        simp [v] at hfv
      · by_contra hge
        obtain ⟨u0, v0, huv0⟩ := hedge
        have ht : C.eval (List.ofFn (fun t : Fin n => decide (t = u0 ∨ t = v0))) = true :=
          (hfun _).mpr ⟨u0, v0, huv0, by simp, by simp⟩
        unfold Circuit.eval at ht
        rw [wires_oob C _ C.output (by omega)] at ht
        exact absurd ht (by decide)
    have hs_pos : 1 ≤ s := by omega
    have hgate_used : ∀ j < s, n + j ≠ C.output → ∃ j' : Fin C.gates.length, n + j ∈ (C.gates[j'.val]).inputs := by
      intro j hjs hne
      by_contra hnone
      have hjlen : j < C.gates.length := by omega
      obtain ⟨C', hm', hsz', heq'⟩ := elim_smaller_circuit G C hmono hfun hedge j hjlen (fun _ => Sum.inl false) true
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
      have hpos : 0 < (G.neighborFinset v).card := by rw [← SimpleGraph.degree, hdeg3 v]; omega
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
          obtain ⟨a, b, hab, ha, hb⟩ := (hfun x).mp h
          simp only [x, decide_eq_true_eq] at ha hb
          subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
      have hf2 : C.eval (List.ofFn x') = true := by
        rw [hfun]
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
      obtain ⟨a, b, hab, ha, hb⟩ := (hfun _).mp h1
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
            obtain ⟨a, b, hab, ha, hb⟩ := (hfun x).mp h
            simp only [x, decide_eq_true_eq] at ha hb
            subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
        have hf1 : C.eval (List.ofFn y) = true := by
          rw [hfun]
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
            obtain ⟨a, b, hab, ha, hb⟩ := (hfun x).mp h
            simp only [x, decide_eq_true_eq] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact absurd hab (G.loopless.irrefl _)
            · exact absurd hab hnw
            · exact absurd hab.symm hnw
            · exact absurd hab (G.loopless.irrefl _)
        have hf1 : C.eval (List.ofFn y) = true := by
          rw [hfun]
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
          obtain ⟨a, b, hab, ha, hb⟩ := (hfun x).mp h
          simp only [x, decide_eq_true_eq] at ha hb
          subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
      have hf1 : C.eval (List.ofFn y) = true := by
        rw [hfun]
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
          have hpos : 1 < (G.neighborFinset a).card := by rw [← SimpleGraph.degree, hdeg3 a]; omega
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
    have ht_le_T : t ≤ Tbranch.card := ht_min Tbranch hvc
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
    have hs_eq : s = n + t - 1 := by omega
    have hT_eq : Tbranch.card = t := by omega
    have houtdeg_eq2 : ∀ w ∈ Simg, outdeg w = 2 := by
      intro w hw
      have hge2 : 2 ≤ outdeg w := by
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp hv).2
      by_contra hne2
      have hgt1 : 1 < outdeg w - 1 := by omega
      have hstrict : ∑ _u ∈ Simg, 1 < ∑ u ∈ Simg, (outdeg u - 1) :=
        Finset.sum_lt_sum (fun u hu => by
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
          have := (Finset.mem_filter.mp hv).2; omega) ⟨w, hw, hgt1⟩
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hSimg_card] at hstrict
      omega
    have houtdeg_eq1_outside : ∀ w < n + s - 1, w ∉ Simg → outdeg w = 1 := by
      intro w hw hwNot
      have hge1 := houtdeg_ge1 w hw
      by_contra hne1
      have hpos : 0 < outdeg w - 1 := by omega
      have hadd : (∑ u ∈ Simg, (outdeg u - 1)) + (outdeg w - 1) ≤ ∑ u ∈ Finset.range (n + s - 1), (outdeg u - 1) := by
        have hsub2 : insert w Simg ⊆ Finset.range (n + s - 1) :=
          Finset.insert_subset (Finset.mem_range.mpr hw) hSimg_sub
        have := Finset.sum_le_sum_of_subset (f := fun u => outdeg u - 1) hsub2
        rw [Finset.sum_insert hwNot] at this
        omega
      omega
    set I : Finset (Fin n) := Finset.univ \ Tbranch
    have hI_card : I.card = n - t := by
      have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Tbranch)
      change I.card + Tbranch.card = (Finset.univ : Finset (Fin n)).card at this
      simp only [Finset.card_univ, Fintype.card_fin, hT_eq] at this
      omega
    have hI_bound : t < 3 * I.card := by
      obtain ⟨J, hJind, hJcard⟩ := large_indep_set G hn1 hcubic hno4
      have hJvc : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G (Finset.univ \ J) := by
        intro u v huv
        by_contra hne
        have huJ : u ∈ J := by
          by_contra h; exact hne (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, h⟩))
        have hvJ : v ∈ J := by
          by_contra h; exact hne (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, h⟩))
        exact hJind u huJ v hvJ huv
      have htJ : t ≤ (Finset.univ \ J).card := ht_min _ hJvc
      have hJsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ J)
      simp only [Finset.card_univ, Fintype.card_fin] at hJsum
      omega
    have hT_nbr_I : ∀ v ∈ Tbranch, (G.neighborFinset v ∩ I).card ≤ 1 := by
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
        obtain ⟨a, b, hab, ha, hb⟩ := (hfun ev).mp ht
        simp only [ev, decide_eq_true_eq] at ha hb
        subst ha; subst hb; exact G.loopless.irrefl _ hab
      have hTv_lt : ∀ w ∈ Tv, w < n + s - 1 := by
        intro w hw
        have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
        have hne : w ≠ n + s - 1 := fun h => hout_not_Tv (h ▸ hw)
        omega
      have hTv_outdeg : ∀ w ∈ Tv, outdeg w = if w = orEnd v.val then 2 else 1 := by
        intro w hw
        by_cases heq : w = orEnd v.val
        · simp only [heq, ↓reduceIte]
          exact houtdeg_eq2 _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
        · simp only [heq, ↓reduceIte]
          apply houtdeg_eq1_outside w (hTv_lt w hw)
          intro hS
          obtain ⟨v', _, hv'eq⟩ := Finset.mem_image.mp hS
          have hv'ne : v' ≠ v := fun h => heq (hv'eq.symm.trans (congrArg (fun x : Fin n => orEnd x.val) h))
          have h0 := hs_zero_other v' v hv'ne.symm
          have h1 := (Finset.mem_filter.mp hw).2
          rw [← hv'eq, h0] at h1
          exact absurd h1 (by decide)
      have hsum_Tv_outdeg : ∑ w ∈ Tv, outdeg w = Tv.card + 1 := by
        have hrew : ∑ w ∈ Tv, outdeg w = ∑ w ∈ Tv, (if w = orEnd v.val then 2 else 1) :=
          Finset.sum_congr rfl hTv_outdeg
        rw [hrew, ← Finset.add_sum_erase _ _ hsv_in_Tv]
        simp only [↓reduceIte]
        have hrest : ∑ w ∈ Tv.erase (orEnd v.val), (if w = orEnd v.val then 2 else 1) = (Tv.erase (orEnd v.val)).card := by
          trans ∑ _w ∈ Tv.erase (orEnd v.val), 1
          · apply Finset.sum_congr rfl
            intro w hw; simp [(Finset.mem_erase.mp hw).1]
          · simp
        rw [hrest]
        have := Finset.card_erase_add_one hsv_in_Tv
        omega
      let Ev : Finset (Fin C.gates.length) :=
        Finset.univ.filter (fun j : Fin C.gates.length => n + j.val ∉ Tv ∧ ∃ i ∈ (C.gates[j.val]).inputs, i ∈ Tv)
      have hmem_Ev : ∀ j : Fin C.gates.length, j ∈ Ev ↔ n + j.val ∉ Tv ∧ ∃ i ∈ (C.gates[j.val]'j.isLt).inputs, i ∈ Tv := fun j => by
        simp only [Ev, Finset.mem_filter, Finset.mem_univ, true_and]
      have hEv_le2 : Ev.card ≤ 2 := by
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
      have hu_inj : ∀ u1 ∈ G.neighborFinset v ∩ I, ∀ u2 ∈ G.neighborFinset v ∩ I,
          nextOf (orEnd u1.val) = nextOf (orEnd u2.val) → u1 = u2 := by
        intro u1 hu1 u2 hu2 heq
        have hvu1 : G.Adj v u1 := (SimpleGraph.mem_neighborFinset G v u1).mp (Finset.mem_inter.mp hu1).1
        have hvu2 : G.Adj v u2 := (SimpleGraph.mem_neighborFinset G v u2).mp (Finset.mem_inter.mp hu2).1
        have hu1NotT : u1 ∉ Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu1).2).2
        have hu2NotT : u2 ∉ Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu2).2).2
        obtain ⟨hlt1, z1, hord1, hz1lt, hz1ne, hz1ch⟩ := hother_input_and u1 hu1NotT
        have hz1t : (C.wires (List.ofFn ev)).getD z1 false = true :=
          hand_z_true u1 hu1NotT v hvu1.symm hlt1 z1 hord1 hz1lt hz1ne hz1ch
        have hsu20 : (C.wires (List.ofFn ev)).getD (orEnd u2.val) false = false :=
          hs_zero_other u2 v (G.ne_of_adj hvu2)
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
      have hcard_le2 : (G.neighborFinset v ∩ I).card ≤ 2 := by
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
            exact hu_inj u1 hu1 u2 hu2 (congrArg Fin.val heq))
        omega
      by_contra hgt1
      have hcard_eq2 : (G.neighborFinset v ∩ I).card = 2 := by omega
      rw [Finset.card_eq_two] at hcard_eq2
      obtain ⟨u1, u2, hu12, hN_I⟩ := hcard_eq2
      have hu1_in : u1 ∈ G.neighborFinset v ∩ I := hN_I ▸ by simp
      have hu2_in : u2 ∈ G.neighborFinset v ∩ I := hN_I ▸ by simp
      obtain ⟨hlt1, hEv1⟩ := hu_maps_Ev u1 hu1_in
      obtain ⟨hlt2, hEv2⟩ := hu_maps_Ev u2 hu2_in
      have hEv_ne : (⟨nextOf (orEnd u1.val), hlt1⟩ : Fin C.gates.length) ≠ ⟨nextOf (orEnd u2.val), hlt2⟩ :=
        fun h => hu12 (hu_inj u1 hu1_in u2 hu2_in (congrArg Fin.val h))
      have hEv_eq : Ev = {⟨nextOf (orEnd u1.val), hlt1⟩, ⟨nextOf (orEnd u2.val), hlt2⟩} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        · rw [Finset.card_pair hEv_ne]; exact hEv_le2
      have hdegv : (G.neighborFinset v).card = 3 := hdeg3 v
      have hdiff_pos : 0 < (G.neighborFinset v \ (G.neighborFinset v ∩ I)).card := by
        have h1 := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left (s₁ := G.neighborFinset v) (s₂ := I))
        have h2 : (G.neighborFinset v ∩ I).card = 2 := by rw [hN_I, Finset.card_pair hu12]
        omega
      obtain ⟨v', hv'⟩ := Finset.card_pos.mp hdiff_pos
      have hvv' : G.Adj v v' := (SimpleGraph.mem_neighborFinset G v v').mp (Finset.mem_sdiff.mp hv').1
      have hv'not : v' ∉ G.neighborFinset v ∩ I := (Finset.mem_sdiff.mp hv').2
      have hv'ne1 : v' ≠ u1 := fun h => hv'not (h ▸ hu1_in)
      have hv'ne2 : v' ≠ u2 := fun h => hv'not (h ▸ hu2_in)
      have hvv'_ne : v ≠ v' := G.ne_of_adj hvv'
      let x0 : Fin n → Bool := fun t => decide (t = v')
      let x1 : Fin n → Bool := Function.update x0 v true
      have hnot_Tv_eq : ∀ w < n + s, w ∉ Tv →
          (C.wires (List.ofFn x0)).getD w false = (C.wires (List.ofFn x1)).getD w false := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ihw =>
          intro hwlt hwNot
          by_cases hw1 : w < n
          · rw [wires_input C x0 w hw1, wires_input C x1 w hw1]
            have hne : (⟨w, hw1⟩ : Fin n) ≠ v := by
              intro h
              have hwv : w = v.val := congrArg Fin.val h
              exact hwNot (hwv ▸ hv_in_Tv)
            exact (Function.update_of_ne hne true x0).symm
          · have hjlt : w - n < C.gates.length := by have : C.gates.length = s := hCsize; omega
            set j := w - n
            have hwj : w = n + j := by omega
            by_cases hjEv : (⟨j, hjlt⟩ : Fin C.gates.length) ∈ Ev
            · rw [hEv_eq, Finset.mem_insert, Finset.mem_singleton] at hjEv
              have hand_zero : ∀ (uk : Fin n), uk ∈ G.neighborFinset v ∩ I → v' ≠ uk →
                  j = nextOf (orEnd uk.val) →
                  (C.wires (List.ofFn x0)).getD w false = (C.wires (List.ofFn x1)).getD w false := by
                intro uk huk hv'uk hjeq
                have huk_notT : uk ∉ Tbranch := (Finset.mem_sdiff.mp (Finset.mem_inter.mp huk).2).2
                have hvuk : G.Adj v uk := (SimpleGraph.mem_neighborFinset G v uk).mp (Finset.mem_inter.mp huk).1
                obtain ⟨h1uk, _, handuk⟩ := hand_exit uk huk_notT
                obtain ⟨_, hmem_su, _⟩ := hnextOf_spec (orEnd uk.val) (hs_ne_out uk) h1uk
                have hsu_lt : orEnd uk.val < n + j := by rw [hjeq]; exact hnextOf_gt _ (hs_ne_out uk) h1uk
                have hsu_not_Tv : orEnd uk.val ∉ Tv := by
                  intro hm
                  have h1 := (Finset.mem_filter.mp hm).2
                  have h0 := hs_zero_other uk v (G.ne_of_adj hvuk)
                  rw [h0] at h1; exact absurd h1 (by decide)
                have hsu_eq := ihw (orEnd uk.val) (by omega) (by omega) hsu_not_Tv
                have hsu_x0 : (C.wires (List.ofFn x0)).getD (orEnd uk.val) false = false :=
                  hs_zero_other uk v' hv'uk
                have hsu_x1 : (C.wires (List.ofFn x1)).getD (orEnd uk.val) false = false :=
                  hsu_eq.symm.trans hsu_x0
                have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
                have hgop : (C.gates[j]'hjlt).op = GateOp.and := by
                  simpa only [hjeq] using handuk
                have hmem_su' : orEnd uk.val ∈ (C.gates[j]'hjlt).inputs := by
                  simpa only [hjeq] using hmem_su
                have hf_and : ∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD (orEnd uk.val) false = false →
                    (C.wires (List.ofFn y)).getD w false = false := by
                  intro y hy0
                  rw [hwj, wires_gate_ofFn C y j _ hg, hgop]
                  change ((C.gates[j]'hjlt).inputs.map fun i => if i < n + j then (C.wires (List.ofFn y)).getD i false else false).all id = false
                  cases hv_all : ((C.gates[j]'hjlt).inputs.map fun i => if i < n + j then (C.wires (List.ofFn y)).getD i false else false).all id with
                  | false => rfl
                  | true =>
                    have ht := List.all_eq_true.mp hv_all _ (List.mem_map_of_mem hmem_su')
                    simp only [id_eq, hsu_lt, ↓reduceIte, hy0] at ht
                    exact absurd ht (by decide)
                exact (hf_and x0 hsu_x0).trans (hf_and x1 hsu_x1).symm
              rcases hjEv with h1 | h2
              · exact hand_zero u1 hu1_in hv'ne1 (congrArg Fin.val h1)
              · exact hand_zero u2 hu2_in hv'ne2 (congrArg Fin.val h2)
            · have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
              rw [hwj, wires_gate_ofFn C x0 j _ hg, wires_gate_ofFn C x1 j _ hg]
              congr 1
              apply List.map_congr_left
              intro i hi
              by_cases hilt : i < n + j
              · simp only [hilt, ↓reduceIte]
                have hiNot : i ∉ Tv := fun hiTv => hjEv ((hmem_Ev ⟨j, hjlt⟩).mpr ⟨hwj ▸ hwNot, i, hi, hiTv⟩)
                exact ihw i (by omega) (by omega) hiNot
              · simp only [hilt, ↓reduceIte]
      have heval := hnot_Tv_eq C.output (by omega) (hout_last ▸ hout_not_Tv)
      change C.eval (List.ofFn x0) = C.eval (List.ofFn x1) at heval
      have hf0 : C.eval (List.ofFn x0) = false := by
        cases h : C.eval (List.ofFn x0) with
        | false => rfl
        | true =>
          obtain ⟨a, b, hab, ha, hb⟩ := (hfun x0).mp h
          simp only [x0, decide_eq_true_eq] at ha hb
          subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
      have hf1 : C.eval (List.ofFn x1) = true := by
        rw [hfun]
        exact ⟨v, v', hvv', by simp [x1], by simp [x1, x0, hvv'_ne.symm]⟩
      rw [hf0, hf1] at heval; exact absurd heval (by decide)
    have hdouble_count : 3 * I.card ≤ Tbranch.card := by
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
      have hLHS_eq : ∑ u ∈ I, (G.neighborFinset u ∩ Tbranch).card = 3 * I.card := by
        trans ∑ _u ∈ I, 3
        · apply Finset.sum_congr rfl
          intro u hu
          have hsub : G.neighborFinset u ⊆ Tbranch := by
            intro v hv
            have huv : G.Adj u v := (SimpleGraph.mem_neighborFinset G u v).mp hv
            rcases hvc u v huv with huT | hvT
            · exact absurd huT (Finset.mem_sdiff.mp hu).2
            · exact hvT
          rw [Finset.inter_eq_left.mpr hsub, ← SimpleGraph.degree, hdeg3 u]
        · simp [mul_comm]
      have hRHS_le : ∑ v ∈ Tbranch, (G.neighborFinset v ∩ I).card ≤ Tbranch.card := by
        have := Finset.sum_le_sum hT_nbr_I
        simpa using this
      omega
    omega

end LMeta616

theorem cubicBound : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ v : Fin n, (G.neighborSet v).ncard = 3) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → n + t ≤ C.size := by
  classical
  intro n t G C hcubic hno4 ht_ex ht_min hmono hfun
  exact LMeta616.main_bound n t G hcubic hno4 ht_ex ht_min C.size C rfl hmono hfun

namespace WireComponents
open PEqualNP.CircuitLowerBounds

private def step (v : List Bool) (g : Gate) :=
  v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]

private def Dep {n} (f : Fin n → ℕ) (a : ℕ) (v : (Fin n → Bool) → Bool) :=
  ∀ x y, (∀ p, f p = a → x p = y p) → v x = v y

private theorem liftDep {n f a v} (h : @Dep n f a v) (r : ℕ → ℕ) :
    Dep (r ∘ f) (r a) v :=
  fun x y e => h x y fun p hp => e p (congrArg r hp)

private theorem read_append (v : List Bool) (b : Bool) (i : ℕ) :
    (v ++ [b]).getD i false = if v.length = i then b else v.getD i false := by
  by_cases e : v.length = i
  · subst i; simp [List.getD_eq_getElem?_getD]
  · by_cases h : i < v.length
    · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h,e]
    · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
      simp [e]

private theorem walk {n} (gs : List Gate) (ar : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (f : Fin n → ℕ) (v : (Fin n → Bool) → List Bool) (l : ℕ)
    (len : ∀ x, (v x).length = l)
    (u : ∀ i, ∃ a, Dep f a (fun x => (v x).getD i false)) :
    ∃ h : Fin n → ℕ, (Finset.univ.image f).card ≤ (Finset.univ.image h).card + gs.length ∧
      ∀ i, ∃ a, Dep h a (fun x => (gs.foldl step (v x)).getD i false) := by
  induction gs generalizing f v l with
  | nil => exact ⟨f,by simp,u⟩
  | cons g gs ih =>
    let val := fun x => g.op.eval (g.inputs.map fun i => (v x).getD i false)
    suffices H : ∃ r : ℕ → ℕ, (Finset.univ.image f).card ≤
        (Finset.univ.image (r ∘ f)).card + 1 ∧ ∃ a, Dep (r ∘ f) a val by
      obtain ⟨r,c,a,ha⟩ := H
      obtain ⟨h,d,hu⟩ := ih (fun k hk => ar k (by simp [hk])) (r ∘ f)
        (fun x => step (v x) g) (l+1) (by simp [step,len]) (by
          intro i
          simp only [step,read_append,len]
          split
          · exact ⟨a,ha⟩
          · obtain ⟨b,hb⟩ := u i
            exact ⟨r b,liftDep hb r⟩)
      exact ⟨h,by simp only [List.length_cons]; omega,hu⟩
    have hg := ar g (by simp)
    cases hi : g.inputs with
    | nil => exact ⟨id,by simp,0,by simp [Dep,val,hi]⟩
    | cons i rest =>
      obtain ⟨a,ha⟩ := u i
      cases rest with
      | nil =>
        refine ⟨id,by simp,a,fun x y e => ?_⟩
        simp only [val,hi,List.map_cons,List.map_nil]
        rw [show (v x).getD i false = (v y).getD i false from ha x y e]
      | cons j rest =>
        cases rest with
        | cons k ks => simp [hi] at hg
        | nil =>
          obtain ⟨b,hb⟩ := u j
          let r := fun c : ℕ => if c = b then a else c
          have ra : r a = a := by simp [r]
          have rb : r b = a := by simp [r]
          refine ⟨r,?_,a,fun x y e => ?_⟩
          · have sub : Finset.univ.image f ⊆ insert b (Finset.univ.image (r ∘ f)) := by
              rintro _ hc
              obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hc
              by_cases eq : f p = b
              · simp [eq]
              · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p,hp,by simp [r,eq]⟩)
            exact (Finset.card_le_card sub).trans (Finset.card_insert_le ..)
          · simp only [val,hi,List.map_cons,List.map_nil]
            have ei : (v x).getD i false = (v y).getD i false :=
              liftDep ha r x y (by rwa [ra])
            have ej : (v x).getD j false = (v y).getD j false :=
              liftDep hb r x y (by rwa [rb])
            rw [ei,ej]

theorem coloring {n : ℕ} (C : Circuit) (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ f : Fin n → ℕ, n ≤ (Finset.univ.image f).card + C.size ∧
      ∀ w, ∃ k, ∀ x y : Fin n → Bool, (∀ p, f p = k → x p = y p) →
        (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
  obtain ⟨f,c,h⟩ := walk C.gates arity (Fin.val : Fin n → ℕ) List.ofFn n (by simp) (by
    intro i
    refine ⟨i,fun x y e => ?_⟩
    by_cases small : i < n
    · simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,small] using e ⟨i,small⟩ rfl
    · simp [List.getD_eq_getElem?_getD,small])
  exact ⟨f,by simpa [Circuit.size,Finset.card_image_of_injective _ Fin.val_injective] using c,h⟩

end WireComponents

namespace FanoPartition

abbrev Pair := Fin 7 × Fin 7
abbrev inc (e : Pair) : Prop :=
  e.2.val = e.1.val ∨ (e.2.val + 1) % 7 = e.1.val ∨ (e.2.val + 3) % 7 = e.1.val
def E := Finset.univ.filter inc
private def tour (i : Fin 14) : Pair :=
  (⟨((i.val+1)/2)%7, Nat.mod_lt _ (by decide)⟩, ⟨i.val/2, by omega⟩)
private def vertex (i : Fin 14) : Fin 14 :=
  if i.val % 2 = 0 then Fin.castAdd 7 (tour i).1 else Fin.natAdd 7 (tour i).2

theorem partition_bound (f : Fin 14 → ℕ) (s : ℕ)
    (budget : (Finset.univ.image f).card + s ≥ 14) (hs : s ≤ 12) :
    (E.filter fun e => f (Fin.castAdd 7 e.1) = f (Fin.natAdd 7 e.2)).card < s + 8 := by
  classical
  let same (e : Pair) := f (Fin.castAdd 7 e.1) = f (Fin.natAdd 7 e.2)
  let D := E.filter fun e => ¬same e
  let T := Finset.univ.filter fun i => f (vertex i) ≠ f (vertex (i+1))
  have cover : Finset.univ.image f ⊆ T.image (fun i => f (vertex i)) := by
    intro c hc
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨i, hi⟩ := (show ∀ x, ∃ i, vertex i = x by decide) x
    by_contra hn
    have step (j : Fin 14) (hj : f (vertex j) = f x) : f (vertex (j+1)) = f x := by
      by_contra ne
      exact hn (Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [hj] using Ne.symm ne⟩,hj⟩)
    have alln (n : ℕ) : f (vertex (i + n • (1 : Fin 14))) = f x := by
      induction n with
      | zero => simp [hi]
      | succ n ih => simpa [succ_nsmul,add_assoc] using step _ ih
    have singleton : Finset.univ.image f ⊆ {f x} := by
      intro z hz
      obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨j,rfl⟩ := (show ∀ y, ∃ j, vertex j = y by decide) y
      obtain ⟨k,hk⟩ := (show ∀ i j : Fin 14, ∃ k : Fin 14, i + k.val • (1 : Fin 14) = j by decide) i j
      exact Finset.mem_singleton.mpr (hk ▸ alln k.val)
    have := Finset.card_le_card singleton
    simp at this
    omega
  have incl : T.image tour ⊆ D := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    have hi' := (Finset.mem_filter.mp hi).2
    refine Finset.mem_filter.mpr ⟨(show ∀ i, tour i ∈ E by decide) i, ?_⟩
    have orient : ∀ i, (vertex i = Fin.castAdd 7 (tour i).1 ∧ vertex (i+1) = Fin.natAdd 7 (tour i).2) ∨
        (vertex i = Fin.natAdd 7 (tour i).2 ∧ vertex (i+1) = Fin.castAdd 7 (tour i).1) := by decide
    rcases orient i with ⟨a,b⟩ | ⟨a,b⟩ <;> simp only [a,b] at hi'
    · exact hi'
    · exact Ne.symm hi'
  have h1 := (Finset.card_le_card cover).trans Finset.card_image_le
  have h2 := Finset.card_le_card incl
  have inj : Function.Injective tour := by intro i j; exact (show ∀ i j, tour i = tour j → i = j by decide) i j
  rw [Finset.card_image_of_injective _ inj] at h2
  have h3 := Finset.card_filter_add_card_filter_not (s := E) same
  have h4 : E.card = 21 := by decide
  change (E.filter same).card < s + 8
  change (E.filter same).card + D.card = E.card at h3
  omega

end FanoPartition

namespace Diagonal
open PEqualNP.CircuitLowerBounds FanoPartition
abbrev point (e : Pair) := Fin.castAdd 7 e.1
abbrev line (e : Pair) := Fin.natAdd 7 e.2
def pair (e : Pair) (v : Fin 14) := if v=point e then true else if v=line e then true else false
def unit (v i : Fin 14) := decide (i=v)
def value (C : Circuit) (w : ℕ) (x : Fin 14 → Bool) := (C.wires (List.ofFn x)).getD w false

theorem split {C : Circuit} {s J : ℕ} (A B : Fin J → ℕ) (D : Finset Pair)
    (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (size : C.size = s)
    (sub : D ⊆ E)
    (sound : ∀ j x, value C (A j) x = true → value C (B j) x = true →
      ∃ p l : Fin 7, inc (p,l) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
    (live : ∀ e ∈ D, ∃ j, value C (A j) (pair e) = true ∧ value C (B j) (pair e) = true ∧
       value C (A j) (unit (point e)) = false ∧ value C (B j) (unit (point e)) = false)
    (many : s+J+7 ≤ D.card) :
    s = 13 ∧ J = 1 ∧ D = E := by
  classical
  have non : D.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e,he⟩ := non
  obtain ⟨j,_⟩ := live e he
  have jp := j.isLt
  have card : E.card = 21 := by decide
  have lim := Finset.card_le_card sub
  have h : ¬s ≤ 12 := by
    intro hs
    obtain ⟨f,cost,dep⟩ := WireComponents.coloring (n:=14) C arity
    have colored : D ⊆ E.filter (fun e => f (point e) = f (line e)) := by
      intro e he
      obtain ⟨j,pa,pb,za,zb⟩ := live e he
      refine Finset.mem_filter.mpr ⟨sub he,?_⟩
      by_contra diff
      have eq (w : ℕ) (yes : value C w (pair e) = true) (no : value C w (unit (point e)) = false) :
          value C w (unit (line e)) = true := by
        obtain ⟨k,kw⟩ := dep w
        have lk : f (line e) = k := by
          by_contra ne
          have h := kw (pair e) (unit (point e)) (by
            intro v hv
            have notL : v ≠ line e := fun eq => ne (eq ▸ hv)
            by_cases eq : v = point e <;> simp only [pair,unit,eq,notL,ite_true,ite_false,decide_true,decide_false])
          change value C w _ = value C w _ at h
          rw [yes,no] at h; contradiction
        have h := kw (pair e) (unit (line e)) (by
          intro v hv
          have notP : v ≠ point e := fun eq => diff ((eq ▸ hv).trans lk.symm)
          simp [pair,unit,notP])
        exact h.symm.trans yes
      obtain ⟨p,l,_,on_,_⟩ := sound j (unit (line e)) (eq _ pa za) (eq _ pb zb)
      have impossible := congrArg Fin.val (of_decide_eq_true on_)
      simp [line, Fin.val_natAdd] at impossible
      omega
    have count := partition_bound f s (by omega) hs
    have exactBound : D.card < s+8 := (Finset.card_le_card colored).trans_lt count
    omega
  have eq : D.card = E.card := by omega
  exact ⟨by omega,by omega,Finset.eq_of_subset_of_card_le sub eq.ge⟩

end Diagonal

namespace FanoProduct

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CoverPromise

abbrev rel (u v : Fin 14) : Prop :=
  u.val < 7 ∧ 7 ≤ v.val ∧
    (v.val - 7 = u.val ∨ (v.val - 7 + 1) % 7 = u.val ∨ (v.val - 7 + 3) % 7 = u.val)

abbrev G := SimpleGraph.fromRel rel
def pair (u v w : Fin 14) := decide (w = u ∨ w = v)
def wire (C : Circuit) (i : ℕ) (x : Fin 14 → Bool) := (C.wires (List.ofFn x)).getD i false

private theorem cubic (v : Fin 14) : (G.neighborSet v).ncard = 3 := by
  let N (u : Fin 14) := Finset.univ.filter (G.Adj u)
  have eq : G.neighborSet v = ↑(N v) := by ext; simp [N]
  rw [eq, Set.ncard_coe_finset]
  exact (show ∀ u, (N u).card = 3 by decide) v

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem noSquare : ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c →
    b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a := by decide +kernel

theorem impossible (C : Circuit) (a b : ℕ) (mono : Monotone2 C) (small : C.size ≤ 13)
    (accept : ∀ u v, rel u v → wire C a (pair u v) = true ∧ wire C b (pair u v) = true)
    (sound : ∀ x, wire C a x = true → wire C b x = true →
      ∃ u v, rel u v ∧ x u = true ∧ x v = true) : False := by
  classical
  let g : Gate := ⟨.and, [a,b]⟩
  let D : Circuit := ⟨C.gates ++ [g], 14 + C.size⟩
  have dmono : Monotone2 D := by
    intro z hz
    change z ∈ C.gates ++ [g] at hz
    simp only [List.mem_append,List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact mono _ hz
    · exact ⟨Or.inl rfl, Nat.le_refl 2⟩
  have evalD (x : Fin 14 → Bool) : D.eval (List.ofFn x) = true ↔
      wire C a x = true ∧ wire C b x = true := by
    have len : (C.wires (List.ofFn x)).length = 14 + C.size := by
      change (C.gates.foldl LMeta616.step (List.ofFn x)).length = _
      rw [LMeta616.foldl_step_len,List.length_ofFn]
      rfl
    change ((C.gates ++ [g]).foldl LMeta616.step (List.ofFn x)).getD (14 + C.size) false = true ↔ _
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← len]
    change ((C.wires (List.ofFn x)) ++ [_]).getD (C.wires (List.ofFn x)).length false = true ↔ _
    rw [LMeta616.getD_append_self]
    change ([wire C a x, wire C b x].all id = true) ↔ _
    simp
  have correct (x : Fin 14 → Bool) : D.eval (List.ofFn x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    rw [evalD]
    constructor
    · rintro ⟨ha,hb⟩
      obtain ⟨u,v,h,hu,hv⟩ := sound x ha hb
      have ne : u ≠ v := by intro e; subst v; obtain ⟨h1,h2,_⟩ := h; omega
      exact ⟨u,v,⟨ne, Or.inl h⟩,hu,hv⟩
    · rintro ⟨u,v,h,hu,hv⟩
      have lift (i j : Fin 14) (hij : rel i j) (hi : x i = true) (hj : x j = true) := by
        have le' (w) : pair i j w = true → x w = true := by
          simp only [pair,decide_eq_true_eq]; rintro (rfl|rfl) <;> assumption
        exact And.intro (LMeta616.wires_mono C mono _ _ le' a (accept i j hij).1)
          (LMeta616.wires_mono C mono _ _ le' b (accept i j hij).2)
      rcases h.2 with h|h
      · exact lift _ _ h hu hv
      · exact lift _ _ h hv hu
  have ex : ∃ t, ∃ S : Finset (Fin 14), IsVertexCover G S ∧ S.card = t :=
    ⟨_, Finset.univ, fun _ _ _ => Or.inl (Finset.mem_univ _), rfl⟩
  have bound := cubicBound 14 (Nat.find ex) G D cubic noSquare
    (Nat.find_spec ex) (fun S hs => Nat.find_min' ex ⟨S,hs,rfl⟩) dmono correct
  obtain ⟨S,hS,hcard⟩ := Nat.find_spec ex
  have edge := hS 0 7 (by decide)
  have pos : 0 < S.card := Finset.card_pos.mpr (edge.elim (fun h => ⟨_,h⟩) (fun h => ⟨_,h⟩))
  have sz : D.size = C.size + 1 := by simp [Circuit.size,D]
  omega

private abbrev incident (e : Fin 7 × Fin 7) : Prop :=
  e.2.val = e.1.val ∨ (e.2.val + 1) % 7 = e.1.val ∨ (e.2.val + 3) % 7 = e.1.val


theorem endpoint (C : Circuit) (a b : ℕ) (mono : Monotone2 C) (sz : C.size ≤ 13)
    (sound : ∀ x : Fin 14 → Bool, wire C a x = true → wire C b x = true →
      ∃ p w : Fin 7, incident (p,w) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 w) = true)
    (all : ∀ e ∈ Finset.univ.filter incident,
      let x := fun v => if v = Fin.castAdd 7 e.1 then true else if v = Fin.natAdd 7 e.2 then true else false
      wire C a x = true ∧ wire C b x = true) : False := by
  apply impossible C a b mono sz
  · intro u v h
    obtain ⟨p,w,hi,rfl,rfl⟩ := (show ∀ u v, rel u v → ∃ p w : Fin 7,
      incident (p,w) ∧ u = Fin.castAdd 7 p ∧ v = Fin.natAdd 7 w by decide) u v h
    have eq (i j : Fin 14) : pair i j = (fun v => if v = i then true else if v = j then true else false) := by
      funext v; by_cases h : v = i <;> simp [pair,h]
    rw [eq]
    exact all (p,w) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  · intro x ha hb
    obtain ⟨p,w,h,hp,hw⟩ := sound x ha hb
    exact ⟨_,_,(show ∀ p w : Fin 7, incident (p,w) → rel (Fin.castAdd 7 p) (Fin.natAdd 7 w) by decide) p w h,hp,hw⟩

end FanoProduct

end PEqualNP.Outside.L_meta_1388

open PEqualNP.Outside.L_meta_1388 in
theorem PEqualNP.Outside.L_meta_1388 : ¬ (∃ (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (Jn : ℕ) (fa fb : Fin Jn → ℕ) (fr : ℕ), PEqualNP.MetaComplexity.Monotone2 Ckt ∧ Ckt.size ≤ 16 ∧ Jn ≤ 6 ∧ (∀ jd : Fin Jn, (Ckt.lineDegrees (7 + 7) (Finset.Ico 7 (7 + 7))).getD (fa jd) 0 ≤ 2 ∧ (Ckt.lineDegrees (7 + 7) (Finset.Ico 7 (7 + 7))).getD (fb jd) 0 ≤ 2) ∧ (∀ (jb : Fin Jn) (zz : Fin (7 + 7) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin 7), (lb.val = pa.val ∨ (lb.val + 1) % 7 = pa.val ∨ (lb.val + 3) % 7 = pa.val) ∧ zz (Fin.castAdd 7 pa) = true ∧ zz (Fin.natAdd 7 lb) = true) ∧ Ckt.size + Jn + 7 ≤ (Finset.univ.filter (fun e2 : Fin 7 × Fin 7 => (e2.2.val = e2.1.val ∨ (e2.2.val + 1) % 7 = e2.1.val ∨ (e2.2.val + 3) % 7 = e2.1.val) ∧ (Ckt.wires (List.ofFn (fun vq : Fin (7 + 7) => if vq = Fin.castAdd 7 e2.1 then true else if vq = Fin.natAdd 7 e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (7 + 7) => if vq = Fin.castAdd 7 e2.1 then true else if vq = Fin.natAdd 7 e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (7 + 7) => if vq = Fin.castAdd 7 e2.1 then true else if vq = Fin.natAdd 7 e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (7 + 7) => if vq = Fin.castAdd 7 e2.1 then true else if vq = Fin.natAdd 7 e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (7 + 7) => if vq = Fin.castAdd 7 e2.1 then true else if vq = Fin.natAdd 7 e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (7 + 7) => decide (vp = Fin.castAdd 7 e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (7 + 7) => decide (vp = Fin.castAdd 7 e2.1)))).getD (fb jk) false = false)).card) := by
  classical
  rintro ⟨C,J,a,b,r,mono,_,_,_,sound,many⟩
  let diag := FanoPartition.E.filter fun e =>
    Diagonal.value C r (Diagonal.pair e) = false ∧
    (∃ j, Diagonal.value C (a j) (Diagonal.pair e) = true ∧ Diagonal.value C (b j) (Diagonal.pair e) = true) ∧
    ∀ j, Diagonal.value C (a j) (Diagonal.pair e) = true → Diagonal.value C (b j) (Diagonal.pair e) = true →
      Diagonal.value C (a j) (Diagonal.unit (Diagonal.point e)) = false ∧
      Diagonal.value C (b j) (Diagonal.unit (Diagonal.point e)) = false
  have sz : C.size + J + 7 ≤ diag.card := by
    apply many.trans
    apply Finset.card_le_card
    intro e he
    obtain ⟨inc,rest⟩ := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩,rest⟩
  have live (e) (he : e ∈ diag) := (Finset.mem_filter.mp he).2
  obtain ⟨c13,j1,all⟩ := Diagonal.split a b diag (fun g hg => (mono g hg).2) rfl
    (Finset.filter_subset ..) sound (by
      intro e he
      obtain ⟨_,⟨j,ha,hb⟩,h⟩ := live e he
      exact ⟨j,ha,hb,h j ha hb⟩) sz
  subst J
  apply FanoProduct.endpoint C (a 0) (b 0) mono c13.le
  · exact sound 0
  · intro e he
    obtain ⟨j,ha,hb⟩ := (live e (all.symm ▸ he)).2.1
    have eq : j = 0 := Subsingleton.elim .. 
    exact eq ▸ And.intro ha hb
