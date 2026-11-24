import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1482

abbrev incidence (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

lemma incidence_refl (p : Fin 13) : incidence p p := Or.inl rfl

lemma line_degree :
    ∀ l : Fin 13, ((Finset.univ : Finset (Fin 13)).filter fun p => incidence p l).card = 4 := by
  decide

lemma point_degree :
    ∀ p : Fin 13, ((Finset.univ : Finset (Fin 13)).filter fun l => incidence p l).card = 4 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma no_four_cycle :
    ∀ p q l m : Fin 13,
      incidence p l → incidence p m → incidence q l → incidence q m → p = q ∨ l = m := by
  decide

lemma incidence_count :
    ((Finset.univ : Finset (Fin 13 × Fin 13)).filter fun e => incidence e.1 e.2).card = 52 := by
  decide

lemma cover_card_lower_bound (points lines : Finset (Fin 13))
    (hcover : ∀ p l : Fin 13, incidence p l → p ∈ points ∨ l ∈ lines) :
    13 ≤ points.card + lines.card := by
  have hsub : (Finset.univ : Finset (Fin 13)) ⊆ points ∪ lines := by
    intro p _
    exact Finset.mem_union.mpr (hcover p p (incidence_refl p))
  calc
    13 = (Finset.univ : Finset (Fin 13)).card := by simp
    _ ≤ (points ∪ lines).card := Finset.card_le_card hsub
    _ ≤ points.card + lines.card := Finset.card_union_le points lines

lemma missing_linear_witness
    (n m : ℕ) (isAnd : Fin m → Prop) [DecidablePred isAnd]
    (left right : Fin m → ℕ)
    (hleft : ∀ j, left j < n + j.val)
    (hright : ∀ j, right j < n + j.val)
    (a b d : ℕ → Bool)
    (hin : ∀ i < n, b i = true → a i = true ∨ d i = true)
    (ha : ∀ j, a (n + j.val) =
      if isAnd j then a (left j) && a (right j) else a (left j) || a (right j))
    (hb : ∀ j, b (n + j.val) =
      if isAnd j then b (left j) && b (right j) else b (left j) || b (right j))
    (hd : ∀ j, d (n + j.val) =
      if isAnd j then (a (left j) && d (right j)) || (d (left j) && a (right j))
      else d (left j) || d (right j))
    (o : ℕ) (ho : o < n + m) (hao : a o = false) (hbo : b o = true)
    (hdo : d o = false) :
    ∃ j : Fin m, isAnd j ∧ b (left j) = true ∧ b (right j) = true ∧
      a (left j) = false ∧ a (right j) = false ∧
      d (left j) = true ∧ d (right j) = true := by
  revert ho hao hbo hdo
  induction o using Nat.strong_induction_on with
  | ind o ih =>
    intro ho hao hbo hdo
    by_cases hoi : o < n
    · have := hin o hoi hbo
      simp [hao, hdo] at this
    · let j : Fin m := ⟨o - n, by omega⟩
      have hjo : n + j.val = o := by dsimp [j]; omega
      have hlj : left j < o := by simpa only [hjo] using hleft j
      have hrj : right j < o := by simpa only [hjo] using hright j
      have hae := ha j
      have hbe := hb j
      have hde := hd j
      rw [hjo, hao] at hae
      rw [hjo, hbo] at hbe
      rw [hjo, hdo] at hde
      by_cases hj : isAnd j
      · simp only [if_pos hj] at hae hbe hde
        have hbl : b (left j) = true := by
          cases hl : b (left j) <;> cases hr : b (right j) <;> simp [hl, hr] at hbe ⊢
        have hbr : b (right j) = true := by
          cases hl : b (left j) <;> cases hr : b (right j) <;> simp [hl, hr] at hbe ⊢
        by_cases hal : a (left j) = true
        · have har : a (right j) = false := by
            cases hr : a (right j) <;> simp [hal, hr] at hae ⊢
          have hdr : d (right j) = false := by
            cases hr : d (right j) <;> simp [hal, hr] at hde ⊢
          exact ih (right j) hrj (by omega) har hbr hdr
        · have hal' : a (left j) = false := Bool.eq_false_of_not_eq_true hal
          by_cases har : a (right j) = true
          · have hdl : d (left j) = false := by
              cases hl : d (left j) <;> simp [har, hl] at hde ⊢
            exact ih (left j) hlj (by omega) hal' hbl hdl
          · have har' : a (right j) = false := Bool.eq_false_of_not_eq_true har
            by_cases hdl : d (left j) = true
            · by_cases hdr : d (right j) = true
              · exact ⟨j, hj, hbl, hbr, hal', har', hdl, hdr⟩
              · exact ih (right j) hrj (by omega) har' hbr
                  (Bool.eq_false_of_not_eq_true hdr)
            · exact ih (left j) hlj (by omega) hal' hbl
                (Bool.eq_false_of_not_eq_true hdl)
      · simp only [if_neg hj] at hae hbe hde
        have hal : a (left j) = false := by
          cases hl : a (left j) <;> simp [hl] at hae ⊢
        have har : a (right j) = false := by
          cases hr : a (right j) <;> simp [hr] at hae ⊢
        have hdl : d (left j) = false := by
          cases hl : d (left j) <;> simp [hl] at hde ⊢
        have hdr : d (right j) = false := by
          cases hr : d (right j) <;> simp [hr] at hde ⊢
        have hbor : b (left j) = true ∨ b (right j) = true := by
          cases hl : b (left j) <;> cases hr : b (right j) <;> simp [hl, hr] at hbe ⊢
        rcases hbor with hbl | hbr
        · exact ih (left j) hlj (by omega) hal hbl hdl
        · exact ih (right j) hrj (by omega) har hbr hdr

lemma addCases_monotone {n m : ℕ} (x x' : Fin n → Bool) (y y' : Fin m → Bool)
    (hx : ∀ p, x p = true → x' p = true) (hy : ∀ l, y l = true → y' l = true) :
    ∀ i : Fin (n + m), Fin.addCases x y i = true → Fin.addCases x' y' i = true := by
  intro i
  refine Fin.addCases (fun p => ?_) (fun l => ?_) i
  · simpa using hx p
  · simpa using hy l

def zeroLineClosure {P L : Type} [Fintype P] (I : P → L → Prop) [DecidableRel I]
    (x : P → Bool) (l : L) : Bool :=
  decide (∀ p : P, x p = true → ¬ I p l)

def zeroPointClosure {P L : Type} [Fintype L] (I : P → L → Prop) [DecidableRel I]
    (y : L → Bool) (p : P) : Bool :=
  decide (∀ l : L, y l = true → ¬ I p l)

lemma critical_inputs_correct {P L : Type} [Fintype P] [Fintype L]
    [DecidableEq P] [DecidableEq L] (I : P → L → Prop) [DecidableRel I]
    (F : (P → Bool) → (L → Bool) → Bool)
    (hmono : ∀ x y x' y', (∀ p, x p = true → x' p = true) →
      (∀ l, y l = true → y' l = true) → F x y = true → F x' y' = true)
    (hpos : ∀ p l, I p l →
      F (fun p' => decide (p' = p)) (fun l' => decide (l' = l)) = true)
    (hneg : ∀ x, F (zeroPointClosure I (zeroLineClosure I x)) (zeroLineClosure I x) = false) :
    ∀ x y, F x y = true ↔ ∃ p l, I p l ∧ x p = true ∧ y l = true := by
  intro x y
  constructor
  · intro hf
    by_contra hn
    have hx : ∀ p, x p = true → zeroPointClosure I (zeroLineClosure I x) p = true := by
      intro p hp
      simp only [zeroPointClosure, decide_eq_true_eq]
      intro l hl
      exact (of_decide_eq_true hl) p hp
    have hy : ∀ l, y l = true → zeroLineClosure I x l = true := by
      intro l hl
      simp only [zeroLineClosure, decide_eq_true_eq]
      intro p hp hip
      exact hn ⟨p, l, hip, hp, hl⟩
    have h := hmono x y _ _ hx hy hf
    rw [hneg] at h
    exact Bool.noConfusion h
  · rintro ⟨p, l, hip, hp, hl⟩
    apply hmono _ _ x y _ _ (hpos p l hip)
    · intro p' hp'
      simp only [decide_eq_true_eq] at hp'
      simpa only [hp'] using hp
    · intro l' hl'
      simp only [decide_eq_true_eq] at hl'
      simpa only [hl'] using hl

open PEqualNP.CircuitLowerBounds

lemma linearValues_unique (n : ℕ) (C : Circuit) (c v w : ℕ → Bool)
    (hg : ∀ j g, C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j)
    (hi : ∀ i, i < n → v i = w i)
    (hv : ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
      (g.op = GateOp.and → v (n + j) = ((c a && v b) || (v a && c b))) ∧
      (g.op = GateOp.or → v (n + j) = (v a || v b)))
    (hw : ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
      (g.op = GateOp.and → w (n + j) = ((c a && w b) || (w a && c b))) ∧
      (g.op = GateOp.or → w (n + j) = (w a || w b))) :
    ∀ i, i < n + C.size → v i = w i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hil
    by_cases hin : i < n
    · exact hi i hin
    · let j := i - n
      have hj : j < C.gates.length := by
        dsimp [j]
        unfold Circuit.size at hil
        omega
      have hji : n + j = i := by dsimp [j]; omega
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hg j C.gates[j] hget
      have havw : v a = w a := ih a (by omega) (by omega)
      have hbvw : v b = w b := ih b (by omega) (by omega)
      obtain ⟨hva, hvo⟩ := hv j C.gates[j] a b hget hab
      obtain ⟨hwa, hwo⟩ := hw j C.gates[j] a b hget hab
      rw [← hji]
      rcases hop with hop | hop
      · rw [hva hop, hwa hop, havw, hbvw]
      · rw [hvo hop, hwo hop, havw, hbvw]

lemma twoBlock_values_eq (n : ℕ) (v w : ℕ → Bool) (a b : Fin n → Bool)
    (hv : ∀ i : Fin n, v i.val = a i ∧ v (n + i.val) = b i)
    (hw : ∀ i : Fin n, w i.val = a i ∧ w (n + i.val) = b i) :
    ∀ i, i < n + n → v i = w i := by
  intro i hi
  by_cases hin : i < n
  · exact (hv ⟨i, hin⟩).1.trans (hw ⟨i, hin⟩).1.symm
  · have hd : i - n < n := by omega
    have he : n + (i - n) = i := by omega
    have h := (hv ⟨i - n, hd⟩).2.trans (hw ⟨i - n, hd⟩).2.symm
    simpa only [he] using h

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  have h : ∀ (gs : List Gate) (x : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
        x.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro x; simp
    | cons g gs ih =>
      intro x
      rw [List.foldl_cons, ih]
      simp; omega
  exact h C.gates x

lemma output_lt_of_eval_true (C : Circuit) (x : List Bool) (h : C.eval x = true) :
    C.output < x.length + C.size := by
  by_contra hn
  have ho : (C.wires x).length ≤ C.output := by rw [wires_length]; omega
  have hf : C.eval x = false := List.getD_eq_default _ _ ho
  rw [hf] at h
  exact Bool.noConfusion h

lemma wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  have h : ∀ (gs : List Gate) (x : List Bool), i < x.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) x).getD i false =
        x.getD i false := by
    intro gs
    induction gs with
    | nil => intro x hi; rfl
    | cons g gs ih =>
      intro x hi
      rw [List.foldl_cons, ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hi
  exact h C.gates x hi

lemma output_ge_of_zero_singletons (n : ℕ) (C : Circuit)
    (h : ∀ i : Fin n, C.eval (List.ofFn (fun j : Fin n => decide (j = i))) = false) :
    n ≤ C.output := by
  by_contra ho
  have ho' : C.output < n := by omega
  let i : Fin n := ⟨C.output, ho'⟩
  have hfalse := h i
  have heq : C.eval (List.ofFn (fun j : Fin n => decide (j = i))) = true := by
    unfold Circuit.eval
    rw [wires_input _ _ _ (by simp; omega)]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp [i]
  rw [heq] at hfalse
  exact Bool.noConfusion hfalse

def recurrenceRun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma recurrenceRun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    recurrenceRun (g :: gs) x =
      recurrenceRun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

lemma recurrenceRun_length (gs : List Gate) (x : List Bool) :
    (recurrenceRun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [recurrenceRun]
  | cons g gs ih => rw [recurrenceRun_cons, ih]; simp; omega

lemma recurrenceRun_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (recurrenceRun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [recurrenceRun_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma recurrenceRun_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    recurrenceRun gs x = recurrenceRun (gs.drop j) (recurrenceRun (gs.take j) x) := by
  simpa only [recurrenceRun, List.foldl_append] using
    congrArg (fun l : List Gate => recurrenceRun l x) (List.take_append_drop j gs).symm

lemma wire_value_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (j : ℕ) (g : Gate) (a b : ℕ)
    (hg : C.gates[j]? = some g) (hin : g.inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval [(C.wires (List.ofFn x)).getD a false,
        (C.wires (List.ofFn x)).getD b false] := by
  have hj : j < C.gates.length := by
    by_contra hj
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  have hgg : C.gates[j] = g := by
    rw [List.getElem?_eq_getElem hj] at hg
    exact Option.some.inj hg
  let earlier := recurrenceRun (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = n + j := by
    simp [earlier, recurrenceRun_length, Nat.min_eq_left hj.le]
  have split : recurrenceRun C.gates (List.ofFn x) =
      recurrenceRun (g :: C.gates.drop (j + 1)) earlier := by
    rw [recurrenceRun_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj, hgg]
  have read (r : ℕ) (hr : r < n + j) :
      earlier.getD r false = (C.wires (List.ofFn x)).getD r false := by
    change earlier.getD r false = (recurrenceRun C.gates (List.ofFn x)).getD r false
    rw [split]
    exact (recurrenceRun_getD _ earlier r (by omega)).symm
  change (recurrenceRun C.gates (List.ofFn x)).getD (n + j) false = _
  rw (occs := [1]) [split]
  rw (occs := [1]) [recurrenceRun_cons]
  rw [recurrenceRun_getD _ _ _ (by simp [plen]),
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, hin, List.map_cons,
    List.map_nil, read a ha, read b hb]

lemma binary_gate_monotone (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b c d : Bool) (ha : a = true → c = true) (hb : b = true → d = true) :
    op.eval [a, b] = true → op.eval [c, d] = true := by
  rcases hop with rfl | rfl <;>
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all [GateOp.eval]

lemma wires_fin_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    (C.wires (List.ofFn x)).getD p.val false = x p := by
  rw [wires_input _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma wire_values_monotone {n : ℕ} (C : Circuit)
    (hg : ∀ j g, C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) :
    ∀ i, i < n + C.size →
      (C.wires (List.ofFn x)).getD i false = true →
      (C.wires (List.ofFn y)).getD i false = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hil hv
    by_cases hin : i < n
    · rw [wires_fin_input C x ⟨i, hin⟩] at hv
      rw [wires_fin_input C y ⟨i, hin⟩]
      exact hxy _ hv
    · let j := i - n
      have hj : j < C.gates.length := by
        dsimp [j]
        unfold Circuit.size at hil
        omega
      have hji : n + j = i := by dsimp [j]; omega
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hg j C.gates[j] hget
      have hcx := wire_value_gate C x j C.gates[j] a b hget hab ha hb
      have hcy := wire_value_gate C y j C.gates[j] a b hget hab ha hb
      rw [← hji, hcx] at hv
      rw [← hji, hcy]
      exact binary_gate_monotone _ hop _ _ _ _
        (ih a (by omega) (by omega)) (ih b (by omega) (by omega)) hv

lemma circuit_eval_monotone {n : ℕ} (C : Circuit)
    (hg : ∀ j g, C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true)
    (hx : C.eval (List.ofFn x) = true) : C.eval (List.ofFn y) = true := by
  have ho : C.output < n + C.size := by
    simpa only [List.length_ofFn] using output_lt_of_eval_true C (List.ofFn x) hx
  exact wire_values_monotone C hg x y hxy C.output ho hx

lemma circuit_missing_linear_witness
    (n : ℕ) (C : Circuit)
    (hgate : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j)
    (x y : Fin n → Bool) (d : ℕ → Bool)
    (hin : ∀ i < n, (C.wires (List.ofFn y)).getD i false = true →
      (C.wires (List.ofFn x)).getD i false = true ∨ d i = true)
    (hd : ∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g →
      g.inputs = [a, b] →
      (g.op = GateOp.and → d (n + j) =
        (((C.wires (List.ofFn x)).getD a false && d b) ||
          (d a && (C.wires (List.ofFn x)).getD b false))) ∧
      (g.op = GateOp.or → d (n + j) = (d a || d b)))
    (o : ℕ) (ho : o < n + C.size)
    (hxo : (C.wires (List.ofFn x)).getD o false = false)
    (hyo : (C.wires (List.ofFn y)).getD o false = true)
    (hdo : d o = false) :
    ∃ (j : ℕ) (g : Gate) (a b : ℕ),
      C.gates[j]? = some g ∧ g.op = GateOp.and ∧ g.inputs = [a, b] ∧
      a ≠ b ∧ a < n + j ∧ b < n + j ∧
      (C.wires (List.ofFn y)).getD a false = true ∧
      (C.wires (List.ofFn y)).getD b false = true ∧
      (C.wires (List.ofFn x)).getD a false = false ∧
      (C.wires (List.ofFn x)).getD b false = false ∧ d a = true ∧ d b = true := by
  classical
  let gs (j : Fin C.size) : Gate := C.gates[j.val]'(by simpa [Circuit.size] using j.isLt)
  have hgs (j : Fin C.size) : C.gates[j.val]? = some (gs j) := by
    simp [gs]
  have hspec (j : Fin C.size) :
      ∃ a b : ℕ, (gs j).inputs = [a, b] ∧ a ≠ b ∧ a < n + j.val ∧ b < n + j.val :=
    (hgate j.val (gs j) (hgs j)).2
  choose left right hinput hne hleft hright using hspec
  let isAnd (j : Fin C.size) : Prop := (gs j).op = GateOp.and
  have hrec (z : Fin n → Bool) (j : Fin C.size) :
      (C.wires (List.ofFn z)).getD (n + j.val) false =
        if isAnd j then
          (C.wires (List.ofFn z)).getD (left j) false &&
            (C.wires (List.ofFn z)).getD (right j) false
        else
          (C.wires (List.ofFn z)).getD (left j) false ||
            (C.wires (List.ofFn z)).getD (right j) false := by
    rw [wire_value_gate C z j.val (gs j) (left j) (right j)
      (hgs j) (hinput j) (hleft j) (hright j)]
    by_cases hj : isAnd j
    · have hj' : (gs j).op = GateOp.and := hj
      simp [hj, hj', GateOp.eval]
    · have hj' : (gs j).op = GateOp.or :=
        (hgate j.val (gs j) (hgs j)).1.resolve_left hj
      simp [hj, hj', GateOp.eval]
  have hdrec (j : Fin C.size) : d (n + j.val) =
      if isAnd j then
        ((C.wires (List.ofFn x)).getD (left j) false && d (right j)) ||
          (d (left j) && (C.wires (List.ofFn x)).getD (right j) false)
      else d (left j) || d (right j) := by
    by_cases hj : isAnd j
    · rw [if_pos hj]
      exact (hd j.val (gs j) (left j) (right j) (hgs j) (hinput j)).1 hj
    · rw [if_neg hj]
      exact (hd j.val (gs j) (left j) (right j) (hgs j) (hinput j)).2
        ((hgate j.val (gs j) (hgs j)).1.resolve_left hj)
  obtain ⟨j, hj, hbl, hbr, hal, har, hdl, hdr⟩ :=
    missing_linear_witness n C.size isAnd left right hleft hright
      (fun i => (C.wires (List.ofFn x)).getD i false)
      (fun i => (C.wires (List.ofFn y)).getD i false) d
      hin (hrec x) (hrec y) hdrec o ho hxo hyo hdo
  exact ⟨j.val, gs j, left j, right j, hgs j, hj, hinput j,
    hne j, hleft j, hright j, hbl, hbr, hal, har, hdl, hdr⟩

lemma circuit_critical_inputs_correct {n m : ℕ} (C : Circuit)
    (I : Fin n → Fin m → Prop) [DecidableRel I]
    (hg : ∀ j g, C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a, b] ∧ a < (n + m) + j ∧ b < (n + m) + j)
    (hpos : ∀ p l, I p l → C.eval (List.ofFn
      (Fin.addCases (fun p' => decide (p' = p)) (fun l' => decide (l' = l)))) = true)
    (hneg : ∀ x, C.eval (List.ofFn
      (Fin.addCases (zeroPointClosure I (zeroLineClosure I x)) (zeroLineClosure I x))) = false) :
    ∀ x y, C.eval (List.ofFn (Fin.addCases x y)) = true ↔
      ∃ p l, I p l ∧ x p = true ∧ y l = true := by
  apply critical_inputs_correct I (fun x y => C.eval (List.ofFn (Fin.addCases x y)))
  · intro x y x' y' hx hy hf
    exact circuit_eval_monotone C hg _ _ (addCases_monotone x x' y y' hx hy) hf
  · exact hpos
  · exact hneg

lemma cover_eq_one_side (points lines : Finset (Fin 13))
    (hcover : ∀ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) → p ∈ points ∨ l ∈ lines)
    (hcard : points.card + lines.card = 13) :
    points = Finset.univ ∨ lines = Finset.univ := by
  have hu : points ∪ lines = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro p
    exact Finset.mem_union.mpr (hcover p p (Or.inl rfl))
  have hc : (points ∩ lines).card = 0 := by
    have hh := Finset.card_union_add_card_inter points lines
    rw [hu] at hh
    simp only [Finset.card_univ, Fintype.card_fin] at hh
    omega
  have hd : Disjoint points lines :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hc)
  by_cases hp : points.Nonempty
  · left
    obtain ⟨p, hp⟩ := hp
    have hstep (q : Fin 13) (hq : q ∈ points) : q + 1 ∈ points := by
      rcases hcover (q + 1) q (Or.inr (Or.inl rfl)) with h | h
      · exact h
      · exact False.elim (Finset.disjoint_left.mp hd hq h)
    have hall : ∀ k : ℕ, (fun z : Fin 13 => z + 1)^[k] p ∈ points := by
      intro k
      induction k with
      | zero => exact hp
      | succ k ih =>
        simpa only [Function.iterate_succ_apply'] using
          hstep ((fun z : Fin 13 => z + 1)^[k] p) ih
    apply Finset.eq_univ_of_forall
    intro q
    have hreach : ∀ p q : Fin 13, ∃ k : Fin 13,
        (fun z : Fin 13 => z + 1)^[k.val] p = q := by decide
    obtain ⟨k, hk⟩ := hreach p q
    simpa only [hk] using hall k.val
  · right
    have hpoints : points = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
    simpa [hpoints] using hu

open PEqualNP.CircuitLowerBounds

def boundaryCircuit : Circuit :=
  { gates := [
      ⟨GateOp.or, [13, 17]⟩,
      ⟨GateOp.or, [26, 23]⟩,
      ⟨GateOp.or, [27, 25]⟩,
      ⟨GateOp.and, [0, 28]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.or, [30, 18]⟩,
      ⟨GateOp.or, [31, 24]⟩,
      ⟨GateOp.and, [1, 32]⟩,
      ⟨GateOp.or, [13, 15]⟩,
      ⟨GateOp.or, [34, 16]⟩,
      ⟨GateOp.or, [35, 20]⟩,
      ⟨GateOp.and, [3, 36]⟩,
      ⟨GateOp.or, [14, 16]⟩,
      ⟨GateOp.or, [38, 17]⟩,
      ⟨GateOp.or, [39, 21]⟩,
      ⟨GateOp.and, [4, 40]⟩,
      ⟨GateOp.or, [15, 17]⟩,
      ⟨GateOp.or, [42, 18]⟩,
      ⟨GateOp.or, [43, 22]⟩,
      ⟨GateOp.and, [5, 44]⟩,
      ⟨GateOp.or, [16, 18]⟩,
      ⟨GateOp.or, [46, 19]⟩,
      ⟨GateOp.or, [47, 23]⟩,
      ⟨GateOp.and, [6, 48]⟩,
      ⟨GateOp.or, [17, 19]⟩,
      ⟨GateOp.or, [50, 20]⟩,
      ⟨GateOp.or, [51, 24]⟩,
      ⟨GateOp.and, [7, 52]⟩,
      ⟨GateOp.or, [18, 20]⟩,
      ⟨GateOp.or, [54, 21]⟩,
      ⟨GateOp.or, [55, 25]⟩,
      ⟨GateOp.and, [8, 56]⟩,
      ⟨GateOp.or, [13, 19]⟩,
      ⟨GateOp.or, [58, 21]⟩,
      ⟨GateOp.or, [59, 22]⟩,
      ⟨GateOp.and, [9, 60]⟩,
      ⟨GateOp.or, [14, 20]⟩,
      ⟨GateOp.or, [62, 22]⟩,
      ⟨GateOp.or, [63, 23]⟩,
      ⟨GateOp.and, [10, 64]⟩,
      ⟨GateOp.or, [15, 21]⟩,
      ⟨GateOp.or, [66, 23]⟩,
      ⟨GateOp.or, [67, 24]⟩,
      ⟨GateOp.and, [11, 68]⟩,
      ⟨GateOp.or, [16, 22]⟩,
      ⟨GateOp.or, [70, 24]⟩,
      ⟨GateOp.or, [71, 25]⟩,
      ⟨GateOp.and, [12, 72]⟩,
      ⟨GateOp.or, [29, 33]⟩,
      ⟨GateOp.or, [74, 37]⟩,
      ⟨GateOp.or, [75, 41]⟩,
      ⟨GateOp.or, [76, 45]⟩,
      ⟨GateOp.or, [77, 49]⟩,
      ⟨GateOp.or, [78, 53]⟩,
      ⟨GateOp.or, [79, 57]⟩,
      ⟨GateOp.or, [80, 61]⟩,
      ⟨GateOp.or, [81, 65]⟩,
      ⟨GateOp.or, [82, 69]⟩,
      ⟨GateOp.or, [83, 73]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.or, [85, 19]⟩,
      ⟨GateOp.or, [86, 25]⟩,
      ⟨GateOp.or, [84, 2]⟩,
      ⟨GateOp.or, [84, 87]⟩,
      ⟨GateOp.and, [88, 89]⟩],
    output := 90 }

def boundaryBase (x : Fin 26 → Bool) : Bool :=
  ((((((((((((x 0 && (((x 13 || x 17) || x 23) || x 25)) || (x 1 && (((x 13 || x 14) || x 18) || x 24))) || (x 3 && (((x 13 || x 15) || x 16) || x 20))) || (x 4 && (((x 14 || x 16) || x 17) || x 21))) || (x 5 && (((x 15 || x 17) || x 18) || x 22))) || (x 6 && (((x 16 || x 18) || x 19) || x 23))) || (x 7 && (((x 17 || x 19) || x 20) || x 24))) || (x 8 && (((x 18 || x 20) || x 21) || x 25))) || (x 9 && (((x 13 || x 19) || x 21) || x 22))) || (x 10 && (((x 14 || x 20) || x 22) || x 23))) || (x 11 && (((x 15 || x 21) || x 23) || x 24))) || (x 12 && (((x 16 || x 22) || x 24) || x 25)))

def boundaryNeighbor (x : Fin 26 → Bool) : Bool :=
  (((x 14 || x 15) || x 19) || x 25)

lemma boundaryCircuit_size : boundaryCircuit.size = 65 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma boundaryCircuit_eval (x : Fin 26 → Bool) :
    boundaryCircuit.eval (List.ofFn x) =
      ((boundaryBase x || x 2) && (boundaryBase x || boundaryNeighbor x)) := by
  simp [boundaryCircuit, Circuit.eval, Circuit.wires, GateOp.eval, boundaryBase, boundaryNeighbor]

lemma factorization (f r n : Bool) :
    ((f || r) && (f || n)) = (f || (r && n)) := by
  cases f <;> cases r <;> cases n <;> rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma boundaryCircuit_correct (x : Fin 26 → Bool) :
    boundaryCircuit.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  rw [boundaryCircuit_eval, factorization]
  simp only [boundaryBase, boundaryNeighbor, Bool.or_eq_true, Bool.and_eq_true]
  simp [Fin.exists_fin_succ]
  simp only [and_or_left]
  apply Iff.of_eq
  ac_rfl

set_option maxHeartbeats 4000000 in
lemma boundaryCircuit_legal : ∀ j g, boundaryCircuit.gates[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j := by
  intro j g hg
  have hj : j < 65 := by
    by_contra hn
    have hlen : boundaryCircuit.gates.length ≤ j := by change 65 ≤ j; omega
    rw [List.getElem?_eq_none hlen] at hg
    cases hg
  interval_cases j <;> simp [boundaryCircuit] at hg <;> subst g <;> simp

def boundaryPointValues : List Bool := [true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma boundary_point_wires :
    boundaryCircuit.wires (List.ofFn (fun i : Fin 26 => decide (i = Fin.castAdd 13 (0 : Fin 13)))) =
      boundaryPointValues := by
  have hx : List.ofFn (fun i : Fin 26 => decide (i = Fin.castAdd 13 (0 : Fin 13))) = [true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
    decide +kernel
  rw [hx]
  simp [boundaryCircuit, Circuit.wires, GateOp.eval, boundaryPointValues]

def boundaryLineValues : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma boundary_line_wires :
    boundaryCircuit.wires (List.ofFn (fun i : Fin 26 => decide (i = Fin.natAdd 13 (0 : Fin 13)))) =
      boundaryLineValues := by
  have hx : List.ofFn (fun i : Fin 26 => decide (i = Fin.natAdd 13 (0 : Fin 13))) = [false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false] := by
    decide +kernel
  rw [hx]
  simp [boundaryCircuit, Circuit.wires, GateOp.eval, boundaryLineValues]

def boundaryV (i : ℕ) : Bool := decide (i ∈ ({13, 26, 27, 28, 29, 30, 31, 32, 34, 35, 36, 58, 59, 60, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 88, 89} : Finset ℕ))

lemma boundaryV_input : ∀ i : Fin 13,
    boundaryV i.val = false ∧ boundaryV (13 + i.val) = decide (i = 0) := by
  decide +kernel

lemma boundaryV_output : boundaryV boundaryCircuit.output = false := by
  decide +kernel

set_option maxHeartbeats 8000000 in
lemma boundaryV_recurrence : ∀ (j : ℕ) (g : Gate) (a b : ℕ),
    boundaryCircuit.gates[j]? = some g → g.inputs = [a, b] →
    (g.op = GateOp.and → boundaryV (26 + j) =
      (((boundaryCircuit.wires (List.ofFn (fun i : Fin 26 => decide (i = Fin.castAdd 13 (0 : Fin 13))))).getD a false && boundaryV b) ||
        (boundaryV a && (boundaryCircuit.wires (List.ofFn (fun i : Fin 26 => decide (i = Fin.castAdd 13 (0 : Fin 13))))).getD b false))) ∧
    (g.op = GateOp.or → boundaryV (26 + j) = (boundaryV a || boundaryV b)) := by
  intro j g a b hg hin
  have hj : j < 65 := by
    by_contra hn
    have hlen : boundaryCircuit.gates.length ≤ j := by change 65 ≤ j; omega
    rw [List.getElem?_eq_none hlen] at hg
    cases hg
  simp only [boundary_point_wires]
  interval_cases j <;> simp [boundaryCircuit] at hg <;> subst g <;>
    simp only [List.cons.injEq, and_true] at hin <;>
    rcases hin with ⟨rfl, rfl⟩ <;> simp [boundaryV, boundaryPointValues]

def boundaryW (i : ℕ) : Bool := decide (i ∈ ({0, 29, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 88, 89} : Finset ℕ))

lemma boundaryW_input : ∀ i : Fin 13,
    boundaryW i.val = decide (i = 0) ∧ boundaryW (13 + i.val) = false := by
  decide +kernel

lemma boundaryW_output : boundaryW boundaryCircuit.output = false := by
  decide +kernel

set_option maxHeartbeats 8000000 in
lemma boundaryW_recurrence : ∀ (j : ℕ) (g : Gate) (a b : ℕ),
    boundaryCircuit.gates[j]? = some g → g.inputs = [a, b] →
    (g.op = GateOp.and → boundaryW (26 + j) =
      (((boundaryCircuit.wires (List.ofFn (fun i : Fin 26 => decide (i = Fin.natAdd 13 (0 : Fin 13))))).getD a false && boundaryW b) ||
        (boundaryW a && (boundaryCircuit.wires (List.ofFn (fun i : Fin 26 => decide (i = Fin.natAdd 13 (0 : Fin 13))))).getD b false))) ∧
    (g.op = GateOp.or → boundaryW (26 + j) = (boundaryW a || boundaryW b)) := by
  intro j g a b hg hin
  have hj : j < 65 := by
    by_contra hn
    have hlen : boundaryCircuit.gates.length ≤ j := by change 65 ≤ j; omega
    rw [List.getElem?_eq_none hlen] at hg
    cases hg
  simp only [boundary_line_wires]
  interval_cases j <;> simp [boundaryCircuit] at hg <;> subst g <;>
    simp only [List.cons.injEq, and_true] at hin <;>
    rcases hin with ⟨rfl, rfl⟩ <;> simp [boundaryW, boundaryLineValues]


lemma boundary_exists_at_65 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size = 65 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧ (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  refine ⟨boundaryCircuit, boundaryCircuit_size, boundaryCircuit_legal,
    boundaryCircuit_correct, 0, 0, Or.inl rfl, ?_, ?_⟩
  · exact ⟨boundaryV, boundaryV_input, boundaryV_recurrence, boundaryV_output⟩
  · exact ⟨boundaryW, boundaryW_input, boundaryW_recurrence, boundaryW_output⟩

end PEqualNP.Outside.L_meta_1482
