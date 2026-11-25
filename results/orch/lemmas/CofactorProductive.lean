import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Iterate
import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Outside.L_meta_2602_aux

abbrev incident (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

lemma point_degree : ∀ p : Fin 13,
    (Finset.univ.filter fun l => incident p l).card = 4 := by
  decide

lemma line_degree : ∀ l : Fin 13,
    (Finset.univ.filter fun p => incident p l).card = 4 := by
  decide

lemma diagonal_incident (p : Fin 13) : incident p p := Or.inl rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma no_rectangle : ∀ p q l m : Fin 13,
    p ≠ q → incident p l → incident p m → incident q l → incident q m → l = m := by
  decide

lemma incidence_card :
    (Finset.univ.filter fun e : Fin 13 × Fin 13 => incident e.1 e.2).card = 52 := by
  decide

lemma deleted_incidence_card :
    (Finset.univ.filter fun e : Fin 13 × Fin 13 =>
      incident e.1 e.2 ∧ e.1 ≠ 0 ∧ e.2 ≠ 0).card = 45 := by
  decide

lemma vertex_cover_card (S T : Finset (Fin 13))
    (h : ∀ p l, incident p l → p ∈ S ∨ l ∈ T) :
    13 ≤ S.card + T.card := by
  have cover : (Finset.univ : Finset (Fin 13)) ⊆ S ∪ T := by
    intro i _
    exact Finset.mem_union.mpr (h i i (diagonal_incident i))
  have hc := Finset.card_le_card cover
  have hu := Finset.card_union_le S T
  have hn : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
  omega

lemma deleted_vertex_cover_card (S T : Finset (Fin 13))
    (h : ∀ p l, incident p l → p ≠ 0 → l ≠ 0 → p ∈ S ∨ l ∈ T) :
    12 ≤ S.card + T.card := by
  have cover : (Finset.univ.erase 0 : Finset (Fin 13)) ⊆ S ∪ T := by
    intro i hi
    have hn : i ≠ 0 := (Finset.mem_erase.mp hi).1
    exact Finset.mem_union.mpr (h i i (diagonal_incident i) hn hn)
  have hc := Finset.card_le_card cover
  have hu := Finset.card_union_le S T
  have hn : (Finset.univ.erase 0 : Finset (Fin 13)).card = 12 := by decide
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma successor_orbit : ∀ i j : Fin 13, ∃ k : Fin 13,
    (fun p : Fin 13 => p + 1)^[k.val] i = j := by
  decide

lemma minimum_vertex_cover (S T : Finset (Fin 13))
    (h : ∀ p l, incident p l → p ∈ S ∨ l ∈ T)
    (hsz : S.card + T.card ≤ 13) :
    (S = ∅ ∧ T = Finset.univ) ∨ (S = Finset.univ ∧ T = ∅) := by
  have hu : S ∪ T = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact h i i (diagonal_incident i)
  have hi : S ∩ T = ∅ := by
    apply Finset.card_eq_zero.mp
    have hc := Finset.card_union_add_card_inter S T
    have hn : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
    rw [hu, hn] at hc
    omega
  have disj (i : Fin 13) (hs : i ∈ S) (ht : i ∈ T) : False := by
    have hm := Finset.mem_inter.mpr ⟨hs, ht⟩
    simpa [hi] using hm
  by_cases he : S = ∅
  · left
    refine ⟨he, ?_⟩
    ext i
    simp only [Finset.mem_univ, iff_true]
    simpa [he] using h i i (diagonal_incident i)
  · right
    have step (i : Fin 13) (hs : i ∈ S) : i + 1 ∈ S := by
      rcases h (i + 1) i (Or.inr (Or.inl rfl)) with hs' | ht
      · exact hs'
      · exact (disj i hs ht).elim
    obtain ⟨i, hiS⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have walk (k : ℕ) : (fun p : Fin 13 => p + 1)^[k] i ∈ S := by
      induction k with
      | zero => exact hiS
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact step _ ih
    have all (j : Fin 13) : j ∈ S := by
      obtain ⟨k, hk⟩ := successor_orbit i j
      rw [← hk]
      exact walk k.val
    constructor
    · ext j
      simp only [Finset.mem_univ, iff_true]
      exact all j
    · apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      exact disj j (all j) hj

lemma rectangle_thin (S T : Finset (Fin 13))
    (h : ∀ p ∈ S, ∀ l ∈ T, incident p l) : S.card ≤ 1 ∨ T.card ≤ 1 := by
  by_cases hs : S.card ≤ 1
  · exact Or.inl hs
  by_cases ht : T.card ≤ 1
  · exact Or.inr ht
  exfalso
  apply hs
  apply Finset.card_le_one.mpr
  intro p hp q hq
  by_contra hpq
  apply ht
  apply Finset.card_le_one.mpr
  intro l hl m hm
  exact no_rectangle p q l m hpq (h p hp l hl) (h p hp m hm)
    (h q hq l hl) (h q hq m hm)

lemma rectangle_card_le_four (S T : Finset (Fin 13))
    (h : ∀ p ∈ S, ∀ l ∈ T, incident p l) : S.card * T.card ≤ 4 := by
  by_cases hs : S = ∅
  · simp [hs]
  by_cases ht : T = ∅
  · simp [ht]
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hs
  obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.mpr ht
  have hbS : S.card ≤ 4 := by
    have sub : S ⊆ Finset.univ.filter (fun q => incident q l) := by
      intro q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, h q hq l hl⟩
    simpa [line_degree l] using Finset.card_le_card sub
  have hbT : T.card ≤ 4 := by
    have sub : T ⊆ Finset.univ.filter (fun m => incident p m) := by
      intro m hm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ m, h p hp m hm⟩
    simpa [point_degree p] using Finset.card_le_card sub
  have hpS : 0 < S.card := Finset.card_pos.mpr ⟨p, hp⟩
  have hpT : 0 < T.card := Finset.card_pos.mpr ⟨l, hl⟩
  rcases rectangle_thin S T h with hS | hT
  · have he : S.card = 1 := by omega
    simpa [he] using hbT
  · have he : T.card = 1 := by omega
    simpa [he] using hbS

lemma rectangle_cover_count {k : ℕ} (A B : Fin k → Finset (Fin 13))
    (valid : ∀ i, ∀ p ∈ A i, ∀ l ∈ B i, incident p l)
    (cover : ∀ p l, incident p l → ∃ i, p ∈ A i ∧ l ∈ B i) : 13 ≤ k := by
  classical
  have pick (p : Fin 13) : ∃ i, p ∈ A i ∧ p ∈ B i :=
    cover p p (diagonal_incident p)
  let f (p : Fin 13) : Fin k := Classical.choose (pick p)
  have hf (p : Fin 13) : p ∈ A (f p) ∧ p ∈ B (f p) :=
    Classical.choose_spec (pick p)
  have inj : Function.Injective f := by
    intro p q he
    have hq := hf q
    rw [← he] at hq
    rcases rectangle_thin (A (f p)) (B (f p)) (valid (f p)) with ha | hb
    · exact Finset.card_le_one.mp ha p (hf p).1 q hq.1
    · exact Finset.card_le_one.mp hb p (hf p).2 q hq.2
  simpa using Fintype.card_le_of_injective f inj

lemma singleton_of_small_card (S : Finset (Fin 13)) (p : Fin 13)
    (hp : p ∈ S) (hs : S.card ≤ 1) : S = {p} := by
  ext q
  constructor
  · intro hq
    exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hs q hq p hp)
  · intro hq
    have he : q = p := Finset.mem_singleton.mp hq
    simpa [he] using hp

lemma normalized_rectangles_orientation (A B : Fin 13 → Finset (Fin 13))
    (valid : ∀ i, ∀ p ∈ A i, ∀ l ∈ B i, incident p l)
    (diag : ∀ i, i ∈ A i ∧ i ∈ B i)
    (cover : ∀ p l, incident p l → ∃ i, p ∈ A i ∧ l ∈ B i) :
    (∀ i, A i = {i}) ∨ (∀ i, B i = {i}) := by
  classical
  have side (i : Fin 13) : A i = {i} ∨ B i = {i} := by
    rcases rectangle_thin (A i) (B i) (valid i) with ha | hb
    · exact Or.inl (singleton_of_small_card (A i) i (diag i).1 ha)
    · exact Or.inr (singleton_of_small_card (B i) i (diag i).2 hb)
  let S := Finset.univ.filter fun i => A i = {i}
  have smem (i : Fin 13) : i ∈ S ↔ A i = {i} := by simp [S]
  have hcover (p l : Fin 13) (edge : incident p l) : p ∈ S ∨ l ∈ Sᶜ := by
    obtain ⟨i, hp, hl⟩ := cover p l edge
    by_cases ha : A i = {i}
    · rw [ha] at hp
      have he : p = i := Finset.mem_singleton.mp hp
      subst p
      exact Or.inl ((smem i).mpr ha)
    · have hb := (side i).resolve_left ha
      rw [hb] at hl
      have he : l = i := Finset.mem_singleton.mp hl
      subst l
      exact Or.inr (Finset.mem_compl.mpr (fun hi => ha ((smem i).mp hi)))
  have hsize : S.card + Sᶜ.card ≤ 13 := by
    have hc := Finset.card_add_card_compl S
    simpa using hc.le
  rcases minimum_vertex_cover S Sᶜ hcover hsize with hS | hS
  · right
    intro i
    apply (side i).resolve_left
    intro ha
    have hi : i ∈ S := (smem i).mpr ha
    simpa [hS.1] using hi
  · left
    intro i
    apply (smem i).mp
    rw [hS.1]
    exact Finset.mem_univ i

lemma normalized_rectangles_exact (A B : Fin 13 → Finset (Fin 13))
    (valid : ∀ i, ∀ p ∈ A i, ∀ l ∈ B i, incident p l)
    (diag : ∀ i, i ∈ A i ∧ i ∈ B i)
    (cover : ∀ p l, incident p l → ∃ i, p ∈ A i ∧ l ∈ B i) :
    (∀ i, A i = {i} ∧ B i = Finset.univ.filter (fun l => incident i l)) ∨
    (∀ i, B i = {i} ∧ A i = Finset.univ.filter (fun p => incident p i)) := by
  rcases normalized_rectangles_orientation A B valid diag cover with ha | hb
  · left
    intro i
    refine ⟨ha i, ?_⟩
    ext l
    constructor
    · intro hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, valid i i (diag i).1 l hl⟩
    · intro hl
      obtain ⟨j, hi, hj⟩ := cover i l (Finset.mem_filter.mp hl).2
      rw [ha j] at hi
      have he : i = j := Finset.mem_singleton.mp hi
      simpa [he] using hj
  · right
    intro i
    refine ⟨hb i, ?_⟩
    ext p
    constructor
    · intro hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, valid i p hp i (diag i).2⟩
    · intro hp
      obtain ⟨j, hj, hi⟩ := cover p i (Finset.mem_filter.mp hp).2
      rw [hb j] at hi
      have he : i = j := Finset.mem_singleton.mp hi
      simpa [he] using hj

end PEqualNP.Outside.L_meta_2602_aux

namespace PEqualNP.Outside.L_meta_2602_aux.CircuitAdapter

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def gateStep {α : Type} (op : GateOp → List α → α) (dflt : α)
    (ws : List α) (g : Gate) : List α :=
  ws ++ [op g.op (g.inputs.map fun i => ws.getD i dflt)]

lemma gateStep_length {α : Type} (op : GateOp → List α → α) (dflt : α) (ws : List α) (g : Gate) :
    (gateStep op dflt ws g).length = ws.length + 1 := by
  simp [gateStep]

lemma prefix_value {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) (i : ℕ) (hi : i < ws.length) :
    (gs.foldl (gateStep op dflt) ws).getD i dflt = ws.getD i dflt := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by rw [gateStep_length]; omega)]
    simp only [gateStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wireCount {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) :
    (gs.foldl (gateStep op dflt) ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, gateStep_length, List.length_cons]
    omega

lemma indexed_value {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) (j : ℕ) (g : Gate)
    (hj : gs[j]? = some g) (hback : ∀ i ∈ g.inputs, i < ws.length + j) :
    (gs.foldl (gateStep op dflt) ws).getD (ws.length + j) dflt =
      op g.op (g.inputs.map fun i => (gs.foldl (gateStep op dflt) ws).getD i dflt) := by
  induction gs generalizing ws j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst g0
      rw [Nat.add_zero, List.foldl_cons, prefix_value _ _ _ _ _ (by rw [gateStep_length]; omega)]
      have hstep : (gateStep op dflt ws g).getD ws.length dflt =
          op g.op (g.inputs.map fun i => ws.getD i dflt) := by
        simp only [gateStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (le_refl ws.length)]
        simp
      rw [hstep]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hlt : i < ws.length := by simpa using hback i hi
      rw [prefix_value _ _ _ _ _ (by rw [gateStep_length]; omega)]
      simp only [gateStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      rw [List.foldl_cons]
      have hidx : ws.length + (j + 1) = (gateStep op dflt ws g0).length + j := by
        rw [gateStep_length]
        omega
      rw [hidx]
      exact ih (gateStep op dflt ws g0) j hj (by simpa only [hidx] using hback)


def wire (n : ℕ) (C : Circuit) (i : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD i false

def isOr (C : Circuit) (j : ℕ) : Bool :=
  match (gateAt C j).op with
  | .or => true
  | _ => false

def left (C : Circuit) (j : ℕ) : ℕ := (gateAt C j).inputs.getD 0 0

def right (C : Circuit) (j : ℕ) : ℕ := (gateAt C j).inputs.getD 1 0

lemma wire_input (n : ℕ) (C : Circuit) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    wire n C i x = x ⟨i,hi⟩ := by
  have hi' : i < (List.ofFn x).length := by simpa using hi
  change (C.gates.foldl (gateStep GateOp.eval false) (List.ofFn x)).getD i false = _
  rw [prefix_value _ _ _ _ _ hi', List.getD_eq_getElem _ _ hi', List.getElem_ofFn]

lemma wire_outside (n : ℕ) (C : Circuit) (i : ℕ) (hi : n + C.size ≤ i)
    (x : Fin n → Bool) : wire n C i x = false := by
  change (C.gates.foldl (gateStep GateOp.eval false) (List.ofFn x)).getD i false = false
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · simpa only [wireCount, List.length_ofFn, Circuit.size] using hi

lemma gate_mem (C : Circuit) (j : ℕ) (hj : j < C.size) : gateAt C j ∈ C.gates := by
  change j < C.gates.length at hj
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma gate_inputs (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.size) : (gateAt C j).inputs = [left C j, right C j] := by
  obtain ⟨a,b,hg⟩ := List.length_eq_two.mp (hC.2.2 _ (gate_mem C j hj))
  simp [left, right, hg]

lemma left_lt (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.size) : left C j < n + j := by
  apply hC.2.1 j hj
  simp [gate_inputs n C hC j hj]

lemma right_lt (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.size) : right C j < n + j := by
  apply hC.2.1 j hj
  simp [gate_inputs n C hC j hj]

lemma wire_gate (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.size) (x : Fin n → Bool) :
    wire n C (n+j) x =
      if isOr C j then wire n C (left C j) x || wire n C (right C j) x
      else wire n C (left C j) x && wire n C (right C j) x := by
  have hit : C.gates[j]? = some (gateAt C j) := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem?_eq_getElem hj
  have hback : ∀ i ∈ (gateAt C j).inputs, i < (List.ofFn x).length + j := by
    simpa only [List.length_ofFn] using hC.2.1 j hj
  have hv := indexed_value GateOp.eval false C.gates (List.ofFn x) j (gateAt C j) hit hback
  rw [List.length_ofFn, gate_inputs n C hC j hj] at hv
  rcases hC.1 _ (gate_mem C j hj) with hop | hop
  · rw [hop] at hv
    change wire n C (n+j) x =
      (wire n C (left C j) x && (wire n C (right C j) x && true)) at hv
    simpa [isOr, hop] using hv
  · rw [hop] at hv
    change wire n C (n+j) x =
      (wire n C (left C j) x || (wire n C (right C j) x || false)) at hv
    simpa [isOr, hop] using hv

lemma wire_monotone (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∀ i < n + C.size, ∀ x y : Fin n → Bool,
      (∀ p, x p = true → y p = true) → wire n C i x = true → wire n C i y = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi x y hxy hx
    by_cases hin : i < n
    · rw [wire_input n C i hin] at hx ⊢
      exact hxy _ hx
    · let j := i - n
      have hij : i = n + j := by dsimp [j]; omega
      have hj : j < C.size := by omega
      have ha := left_lt n C hC j hj
      have hb := right_lt n C hC j hj
      rw [hij, wire_gate n C hC j hj] at hx ⊢
      cases hop : isOr C j
      · simp only [hop, Bool.false_eq_true, ↓reduceIte] at hx ⊢
        obtain ⟨hx1,hx2⟩ := Bool.and_eq_true_iff.mp hx
        exact Bool.and_eq_true_iff.mpr
          ⟨ih (left C j) (by omega) (by omega) x y hxy hx1,
           ih (right C j) (by omega) (by omega) x y hxy hx2⟩
      · simp only [hop, ↓reduceIte] at hx ⊢
        rcases Bool.or_eq_true_iff.mp hx with hx | hx
        · exact Bool.or_eq_true_iff.mpr (Or.inl (ih (left C j) (by omega) (by omega) x y hxy hx))
        · exact Bool.or_eq_true_iff.mpr (Or.inr (ih (right C j) (by omega) (by omega) x y hxy hx))

lemma eval_is_wire (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    C.eval (List.ofFn x) = wire n C C.output x := rfl

lemma count_filter_range {α : Type} (p : α → Bool) (d : α) (gs : List α) :
    ((Finset.range gs.length).filter (fun j => p (gs.getD j d) = true)).card =
      (gs.filter p).length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    have old :
        (Finset.range gs.length).filter (fun j => p ((gs ++ [g]).getD j d) = true) =
        (Finset.range gs.length).filter (fun j => p (gs.getD j d) = true) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      by_cases hj : j < gs.length
      · rw [List.getD_append _ _ _ _ hj]
      · simp [hj]
    have last : (gs ++ [g]).getD gs.length d = g := by
      simp [List.getD_eq_getElem?_getD]
    rw [List.length_append, List.length_singleton, Finset.range_add_one,
      Finset.filter_insert, last, old, List.filter_append, List.length_append]
    cases hp : p g <;> simp [hp] <;>
      simpa only [List.getD_eq_getElem?_getD] using ih

lemma or_count (C : Circuit) :
    ((Finset.range C.size).filter (fun j => isOr C j = true)).card =
      PEqualNP.ReadTwo.nOr C := by
  let : DecidableEq GateOp := gateOpDecEq
  have hp (j : ℕ) : isOr C j = decide ((gateAt C j).op = .or) := by
    unfold isOr
    cases (gateAt C j).op <;> rfl
  simp_rw [hp]
  exact count_filter_range (fun g : Gate => decide (g.op = .or)) ⟨.or, []⟩ C.gates

end PEqualNP.Outside.L_meta_2602_aux.CircuitAdapter

namespace PEqualNP.Outside.L_meta_2602_aux.ProductiveBound

lemma unary_union_bound {α : Type} [DecidableEq α] (U : Finset ℕ) (f : ℕ → Finset α) (l r : ℕ → ℕ)
    (N0 : ℕ) (hleaf : ∀ j < N0, j ∉ U → (f j).card ≤ 1 ∨ ∃ p < j, f j ⊆ f p)
    (hU : ∀ j ∈ U, l j < j ∧ r j < j ∧ f j = f (l j) ∪ f (r j)) :
    ∀ N ≤ N0, ∀ V : Finset ℕ, V ⊆ Finset.range N →
      (V.biUnion f).card ≤ V.card + (U.filter (fun j => j < N)).card := by
  intro N
  induction N with
  | zero =>
    intro _ V hV
    have : V = ∅ := by simpa using hV
    subst this
    simp
  | succ N ih =>
    intro hN V hV
    have hmono : (U.filter (fun j => j < N)).card ≤ (U.filter (fun j => j < N + 1)).card :=
      Finset.card_le_card (fun j hj => by
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, by omega⟩)
    by_cases hNV : N ∈ V
    · have hV' : V.erase N ⊆ Finset.range N := by
        intro j hj
        have h1 := Finset.mem_erase.1 hj
        have h2 := Finset.mem_range.1 (hV h1.2)
        exact Finset.mem_range.2 (by omega)
      have hcard : (V.erase N).card + 1 = V.card := Finset.card_erase_add_one hNV
      have hsplit : V.biUnion f = f N ∪ (V.erase N).biUnion f := by
        conv_lhs => rw [← Finset.insert_erase hNV]
        rw [Finset.biUnion_insert]
      by_cases hNU : N ∈ U
      · obtain ⟨hl, hr, hf⟩ := hU N hNU
        have hV2 : insert (l N) (insert (r N) (V.erase N)) ⊆ Finset.range N := by
          intro j hj
          rcases Finset.mem_insert.1 hj with rfl | hj
          · exact Finset.mem_range.2 hl
          · rcases Finset.mem_insert.1 hj with rfl | hj
            · exact Finset.mem_range.2 hr
            · exact hV' hj
        have h1 := ih (by omega) _ hV2
        have hsub : V.biUnion f ⊆ (insert (l N) (insert (r N) (V.erase N))).biUnion f := by
          rw [hsplit, hf, Finset.biUnion_insert, Finset.biUnion_insert, Finset.union_assoc]
        have h2 := Finset.card_le_card hsub
        have h3 : (insert (l N) (insert (r N) (V.erase N))).card ≤ (V.erase N).card + 2 :=
          (Finset.card_insert_le _ _).trans (by
            have := Finset.card_insert_le (r N) (V.erase N)
            omega)
        have h4 : (U.filter (fun j => j < N + 1)).card = (U.filter (fun j => j < N)).card + 1 := by
          have : U.filter (fun j => j < N + 1) = insert N (U.filter (fun j => j < N)) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hj, hlt⟩
              by_cases e : j = N
              · exact Or.inl e
              · exact Or.inr ⟨hj, by omega⟩
            · rintro (rfl | ⟨hj, hlt⟩)
              · exact ⟨hNU, by omega⟩
              · exact ⟨hj, by omega⟩
          rw [this, Finset.card_insert_of_notMem (by simp)]
        omega
      · rcases hleaf N (by omega) hNU with hleaf | ⟨p, hp, hsub⟩
        · have h1 := ih (by omega) _ hV'
          have h3 : (V.biUnion f).card ≤ (f N).card + ((V.erase N).biUnion f).card := by
            rw [hsplit]
            exact Finset.card_union_le _ _
          omega
        · have hV2 : insert p (V.erase N) ⊆ Finset.range N := by
            intro j hj
            rcases Finset.mem_insert.1 hj with rfl | hj
            · exact Finset.mem_range.2 hp
            · exact hV' hj
          have h1 := ih (by omega) _ hV2
          have hsubV : V.biUnion f ⊆ (insert p (V.erase N)).biUnion f := by
            rw [hsplit, Finset.biUnion_insert]
            exact Finset.union_subset_union_left hsub
          have h2 := Finset.card_le_card hsubV
          have h3 := Finset.card_insert_le p (V.erase N)
          omega
    · have hV' : V ⊆ Finset.range N := by
        intro j hj
        have h2 := Finset.mem_range.1 (hV hj)
        have : j ≠ N := fun e => hNV (e ▸ hj)
        exact Finset.mem_range.2 (by omega)
      have h1 := ih (by omega) V hV'
      omega


def BitMonotone {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def singleton {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def Below {n : ℕ} (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f x = true → ∃ i ∈ A, x i = true

lemma and_below {n : ℕ} (A : Finset (Fin n)) (f g : (Fin n → Bool) → Bool)
    (hf : BitMonotone f) (hg : BitMonotone g)
    (hfg : Below A (fun x => f x && g x)) : Below A f ∨ Below A g := by
  let z : Fin n → Bool := fun i => decide (i ∉ A)
  have hzero : (f z && g z) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have := hfg z h
    simp [z] at this
  have recover (h : (Fin n → Bool) → Bool) (hm : BitMonotone h)
      (hz : h z = false) : Below A h := by
    intro x hx
    by_contra hno
    have hle : ∀ i, x i = true → z i = true := by
      intro i hi
      simp only [z, decide_eq_true_eq]
      exact fun hiA => hno ⟨i, hiA, hi⟩
    have ht := hm x z hle hx
    rw [hz] at ht
    contradiction
  cases hF : f z
  · exact Or.inl (recover f hf hF)
  · exact Or.inr (recover g hg (by simpa [hF] using hzero))

def support (n : ℕ) (F : ℕ → (Fin n → Bool) → Bool) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => F i (singleton p) = true)

noncomputable def productive (v n k : ℕ) (A : Finset (Fin v))
    (F : ℕ → (Fin v → Bool) → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + k)).filter (fun i => n ≤ i ∧ op (i - n) = true ∧
    Below A (F i) ∧ ¬ support v F (a (i - n)) ⊆ support v F (b (i - n)) ∧
    ¬ support v F (b (i - n)) ⊆ support v F (a (i - n)))

lemma productive_charge_bound (v n k : ℕ) (A : Finset (Fin v))
    (F : ℕ → (Fin v → Bool) → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ)
    (hseed : ∀ i < n, Below A (F i) → (support v F i).card ≤ 1)
    (hgate : ∀ j < k, ∀ x, F (n + j) x =
      if op j then F (a j) x || F (b j) x else F (a j) x && F (b j) x)
    (ha : ∀ j < k, a j < n + j) (hb : ∀ j < k, b j < n + j)
    (hmono : ∀ i < n + k, BitMonotone (F i))
    (out : ℕ) (hout : out < n + k)
    (hspec : ∀ x, F out x = true ↔ ∃ i ∈ A, x i = true) :
    A.card ≤ (productive v n k A F op a b).card + 1 := by
  classical
  let fs (i : ℕ) := if Below A (F i) then support v F i else ∅
  let l (i : ℕ) := a (i - n)
  let r (i : ℕ) := b (i - n)
  have input_small (i : ℕ) (hi : i < n) : (fs i).card ≤ 1 := by
    by_cases hbelow : Below A (F i)
    · simpa only [fs, if_pos hbelow] using hseed i hi hbelow
    · simp [fs, hbelow]
  have or_below (w : ℕ) (hwn : n ≤ w) (hw : w < n + k)
      (hop : op (w - n) = true) (hbelow : Below A (F w)) :
      Below A (F (a (w - n))) ∧ Below A (F (b (w - n))) := by
    have hj : w - n < k := by omega
    have heq : n + (w - n) = w := by omega
    constructor
    · intro x hx
      apply hbelow x
      rw [← heq, hgate (w - n) hj x, hop]
      simp [hx]
    · intro x hx
      apply hbelow x
      rw [← heq, hgate (w - n) hj x, hop]
      simp [hx]
  have or_union (w : ℕ) (hwn : n ≤ w) (hw : w < n + k)
      (hop : op (w - n) = true) (hbelow : Below A (F w)) :
      fs w = fs (l w) ∪ fs (r w) := by
    have hj : w - n < k := by omega
    have heq : n + (w - n) = w := by omega
    obtain ⟨hba, hbb⟩ := or_below w hwn hw hop hbelow
    simp only [fs, l, r, if_pos hbelow, if_pos hba, if_pos hbb]
    ext p
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [← heq, hgate (w - n) hj (singleton p), hop]
    simp
  have union_step (w : ℕ) (hw : w ∈ productive v n k A F op a b) :
      l w < w ∧ r w < w ∧ fs w = fs (l w) ∪ fs (r w) := by
    simp only [productive, Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hwk, hwn, hop, hbelow, _, _⟩ := hw
    have hj : w - n < k := by omega
    refine ⟨by dsimp [l]; have := ha (w - n) hj; omega,
      by dsimp [r]; have := hb (w - n) hj; omega,
      or_union w hwn hwk hop hbelow⟩
  have unary_step (w : ℕ) (hw : w < n + k)
      (hnu : w ∉ productive v n k A F op a b) :
      (fs w).card ≤ 1 ∨ ∃ p < w, fs w ⊆ fs p := by
    by_cases hsmall : (fs w).card ≤ 1
    · exact Or.inl hsmall
    · right
      have hbelow : Below A (F w) := by
        by_contra hno
        simp [fs, hno] at hsmall
      have hwn : n ≤ w := by
        by_contra hno
        exact hsmall (input_small w (by omega))
      have hj : w - n < k := by omega
      have heq : n + (w - n) = w := by omega
      have haj : a (w - n) < w := by have := ha (w - n) hj; omega
      have hbj : b (w - n) < w := by have := hb (w - n) hj; omega
      cases hop : op (w - n)
      · have hand : Below A (fun x => F (a (w - n)) x && F (b (w - n)) x) := by
          intro x hx
          apply hbelow x
          rw [← heq, hgate (w - n) hj x, hop]
          exact hx
        rcases and_below A (F (a (w - n))) (F (b (w - n)))
            (hmono _ (by omega)) (hmono _ (by omega)) hand with hba | hbb
        · refine ⟨a (w - n), haj, ?_⟩
          intro p hp
          have ht : F w (singleton p) = true := by simpa [fs, hbelow, support] using hp
          rw [← heq, hgate (w - n) hj (singleton p), hop] at ht
          have hpa := (Bool.and_eq_true_iff.mp ht).1
          simpa [fs, hba, support] using hpa
        · refine ⟨b (w - n), hbj, ?_⟩
          intro p hp
          have ht : F w (singleton p) = true := by simpa [fs, hbelow, support] using hp
          rw [← heq, hgate (w - n) hj (singleton p), hop] at ht
          have hpb := (Bool.and_eq_true_iff.mp ht).2
          simpa [fs, hbb, support] using hpb
      · obtain ⟨hba, hbb⟩ := or_below w hwn hw hop hbelow
        have hor := or_union w hwn hw hop hbelow
        by_cases hab : support v F (a (w - n)) ⊆ support v F (b (w - n))
        · refine ⟨b (w - n), hbj, ?_⟩
          rw [hor]
          have hsub : fs (l w) ⊆ fs (r w) := by
            simpa only [fs, l, r, if_pos hba, if_pos hbb] using hab
          exact Finset.union_subset hsub (Finset.Subset.refl _)
        · have hba' : support v F (b (w - n)) ⊆ support v F (a (w - n)) := by
            by_contra hn
            apply hnu
            simp only [productive, Finset.mem_filter, Finset.mem_range]
            exact ⟨hw, hwn, hop, hbelow, hab, hn⟩
          refine ⟨a (w - n), haj, ?_⟩
          rw [hor]
          have hsub : fs (r w) ⊆ fs (l w) := by
            simpa only [fs, l, r, if_pos hba, if_pos hbb] using hba'
          exact Finset.union_subset (Finset.Subset.refl _) hsub
  have hbelowout : Below A (F out) := fun x hx => (hspec x).1 hx
  have hfout : fs out = A := by
    ext p
    simp only [fs, if_pos hbelowout, support, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [singleton] using hspec (singleton p)
  have hfil : (productive v n k A F op a b).filter (fun j => j < n + k) =
      productive v n k A F op a b := by
    apply Finset.filter_true_of_mem
    intro j hj
    exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have h := unary_union_bound (productive v n k A F op a b) fs l r (n + k)
    unary_step union_step (n + k) le_rfl {out} (by simpa using hout)
  simpa only [Finset.singleton_biUnion, Finset.card_singleton, hfout, hfil, Nat.add_comm] using h

lemma cofactor_productive_sum_bound (v n k m d : ℕ) (A : Fin m → Finset (Fin v))
    (F : Fin m → ℕ → (Fin v → Bool) → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ)
    (hseed : ∀ t i, i < n → Below (A t) (F t i) → (support v (F t) i).card ≤ 1)
    (hgate : ∀ t j, j < k → ∀ x, F t (n + j) x =
      if op j then F t (a j) x || F t (b j) x else F t (a j) x && F t (b j) x)
    (ha : ∀ j < k, a j < n + j) (hb : ∀ j < k, b j < n + j)
    (hmono : ∀ t i, i < n + k → BitMonotone (F t i))
    (out : Fin m → ℕ) (hout : ∀ t, out t < n + k)
    (hspec : ∀ t x, F t (out t) x = true ↔ ∃ i ∈ A t, x i = true)
    (hsize : ∀ t, (A t).card = d) :
    m * (d - 1) ≤ ∑ t : Fin m, (productive v n k (A t) (F t) op a b).card := by
  classical
  have each (t : Fin m) : d - 1 ≤ (productive v n k (A t) (F t) op a b).card := by
    have h := productive_charge_bound v n k (A t) (F t) op a b (hseed t) (hgate t)
      ha hb (hmono t) (out t) (hout t) (hspec t)
    rw [hsize t] at h
    omega
  calc
    m * (d - 1) = ∑ _ : Fin m, (d - 1) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun t _ => each t)

end PEqualNP.Outside.L_meta_2602_aux.ProductiveBound
namespace PEqualNP.Outside.L_meta_2602_aux.CofactorProductive

open PEqualNP.CircuitLowerBounds ProductiveBound

def pointInput (t : Fin 13) (x : Fin 13 → Bool) (i : Fin 26) : Bool :=
  if h : i.val < 13 then decide (i.val = t.val) else x ⟨i.val - 13, by omega⟩

lemma pointInput_point (t p : Fin 13) (x : Fin 13 → Bool) :
    pointInput t x ⟨p.val, by omega⟩ = decide (p = t) := by
  simp [pointInput, p.isLt, Fin.ext_iff]

lemma pointInput_line (t l : Fin 13) (x : Fin 13 → Bool) :
    pointInput t x ⟨13 + l.val, by omega⟩ = x l := by
  simp [pointInput, show ¬ 13 + l.val < 13 by omega]

def cofactor (C : Circuit) (t : Fin 13) (i : ℕ) (x : Fin 13 → Bool) : Bool :=
  CircuitAdapter.wire 26 C i (pointInput t x)

lemma cofactor_seed (C : Circuit) (t : Fin 13) (A : Finset (Fin 13))
    (i : ℕ) (hi : i < 26) (hbelow : Below A (cofactor C t i)) :
    (support 13 (cofactor C t) i).card ≤ 1 := by
  classical
  by_cases hp : i < 13
  · have heq (x : Fin 13 → Bool) : cofactor C t i x = decide (i = t.val) := by
      unfold cofactor
      rw [CircuitAdapter.wire_input 26 C i hi]
      simp [pointInput, hp]
    by_cases hit : i = t.val
    · have h := hbelow (fun _ => false) (by rw [heq]; simp [hit])
      simp at h
    · have hs : support 13 (cofactor C t) i = ∅ := by
        ext p
        simp [support, heq, hit]
      simp [hs]
  · let l : Fin 13 := ⟨i - 13, by omega⟩
    have heq (x : Fin 13 → Bool) : cofactor C t i x = x l := by
      unfold cofactor
      rw [CircuitAdapter.wire_input 26 C i hi]
      simp [pointInput, hp, l]
    have hs : support 13 (cofactor C t) i = {l} := by
      ext p
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, heq,
          ProductiveBound.singleton, decide_eq_true_eq, Finset.mem_singleton]
      exact eq_comm
    simp [hs]

lemma cofactor_mono (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 26 C)
    (t : Fin 13) (i : ℕ) (hi : i < 26 + C.size) :
    BitMonotone (cofactor C t i) := by
  intro x y hxy hx
  apply CircuitAdapter.wire_monotone 26 C hC i hi (pointInput t x) (pointInput t y) _ hx
  intro p hp
  by_cases hi : p.val < 13
  · simpa only [pointInput, dif_pos hi] using hp
  · simp only [pointInput, dif_neg hi] at hp ⊢
    exact hxy _ hp

lemma cofactor_productive_lower_bound (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hout : C.output < 26 + C.size)
    (spec : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, incident p l ∧ x ⟨p.val, by omega⟩ = true ∧
        x ⟨13 + l.val, by omega⟩ = true) :
    39 ≤ ∑ t : Fin 13,
      (productive 13 26 C.size (Finset.univ.filter (fun l => incident t l))
        (cofactor C t) (CircuitAdapter.isOr C) (CircuitAdapter.left C)
        (CircuitAdapter.right C)).card := by
  classical
  let A : Fin 13 → Finset (Fin 13) := fun t => Finset.univ.filter (fun l => incident t l)
  have hgate (t : Fin 13) (j : ℕ) (hj : j < C.size) (x : Fin 13 → Bool) :
      cofactor C t (26 + j) x =
      if CircuitAdapter.isOr C j then
        cofactor C t (CircuitAdapter.left C j) x || cofactor C t (CircuitAdapter.right C j) x
      else cofactor C t (CircuitAdapter.left C j) x && cofactor C t (CircuitAdapter.right C j) x :=
    CircuitAdapter.wire_gate 26 C hC j hj (pointInput t x)
  have hspec (t : Fin 13) (x : Fin 13 → Bool) :
      cofactor C t C.output x = true ↔ ∃ l ∈ A t, x l = true := by
    rw [cofactor, ← CircuitAdapter.eval_is_wire]
    rw [spec]
    simp only [pointInput_point, pointInput_line, decide_eq_true_eq]
    constructor
    · rintro ⟨p, l, hpl, hpt, hl⟩
      subst p
      exact ⟨l, by simpa [A] using hpl, hl⟩
    · rintro ⟨l, hl, hx⟩
      exact ⟨t, l, by simpa [A] using hl, rfl, hx⟩
  have hsize (t : Fin 13) : (A t).card = 4 := point_degree t
  have h := cofactor_productive_sum_bound 13 26 C.size 13 4 A (cofactor C)
    (CircuitAdapter.isOr C) (CircuitAdapter.left C) (CircuitAdapter.right C)
    (fun t i hi hb => cofactor_seed C t (A t) i hi hb) hgate
    (CircuitAdapter.left_lt 26 C hC) (CircuitAdapter.right_lt 26 C hC)
    (cofactor_mono C hC) (fun _ => C.output) (fun _ => hout) hspec hsize
  exact h

end PEqualNP.Outside.L_meta_2602_aux.CofactorProductive
