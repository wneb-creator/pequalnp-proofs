import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1735_aux
/- Supporting result for L-meta-1735. Sources: checked L2074, L5242,
   and the neighborhood-counting argument of checked reduction R1882_1.
   This proves only the exactly-two nested-junk case. -/

namespace Support

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover


def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma dep (n : ℕ) (C : Circuit) (hR : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2) :
    ∀ k, k ≤ C.gates.length → ∀ W : Finset ℕ, (∀ w ∈ W, w < n + k) →
      ∃ T : Finset (Fin n), T.card ≤ k + W.card ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
          ∀ w ∈ W, val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro k
  induction k with
  | zero =>
    intro _ W hW
    refine ⟨Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ W), ?_, ?_⟩
    · rw [Nat.zero_add, ← Finset.card_image_of_injective _ Fin.val_injective]
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      exact (Finset.mem_filter.1 hi).2
    · intro x y h w hw
      have hw' : w < n := by simpa using hW w hw
      have e : ∀ z : Fin n → Bool, (List.ofFn z).getD w false = z ⟨w, hw'⟩ := by
        intro z; simp [List.getD_eq_getElem?_getD, hw']
      rw [val_input (by simp) hw', val_input (by simp) hw', e, e]
      exact h ⟨w, hw'⟩ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)
  | succ k ih =>
    intro hk W hW
    by_cases hmem : n + k ∈ W
    · obtain ⟨W2, hW2⟩ : ∃ W2 : Finset ℕ, W2 = W.erase (n + k) ∪
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset := ⟨_, rfl⟩
      have hlt2 : ∀ w ∈ W2, w < n + k := by
        intro w hw
        rw [hW2] at hw
        rcases Finset.mem_union.1 hw with h | h
        · have h1 := hW w (Finset.mem_of_mem_erase h)
          have h2 := Finset.ne_of_mem_erase h
          omega
        · simp at h; exact h.2
      have hs1 : ∀ w ∈ W, w ≠ n + k → w ∈ W2 := by
        intro w hw hne
        rw [hW2]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      have hs2 : ∀ i ∈ (gateAt C k).inputs, i < n + k → i ∈ W2 := by
        intro i hi hlt
        rw [hW2]
        exact Finset.mem_union_right _ (by simp [hi, hlt])
      have hc : W2.card + 1 ≤ W.card + 2 := by
        rw [hW2]
        have h1 := Finset.card_union_le (W.erase (n + k))
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset
        have h2 : ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset.card ≤ 2 :=
          (List.toFinset_card_le _).trans
            ((List.length_filter_le _ _).trans (hR k (by omega)).le)
        have h3 := Finset.card_erase_of_mem hmem
        have h4 : 0 < W.card := Finset.card_pos.2 ⟨_, hmem⟩
        omega
      obtain ⟨T, hT, hdep⟩ := ih (by omega) W2 hlt2
      refine ⟨T, by omega, ?_⟩
      intro x y h w hw
      by_cases hwk : w = n + k
      · rw [hwk, val_gate (by simp) (by omega), val_gate (by simp) (by omega)]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hlt : i < n + k
        · simp only [ite_eq_left hlt]
          exact hdep x y h i (hs2 i hi hlt)
        · simp only [ite_eq_right hlt]
      · exact hdep x y h w (hs1 w hw hwk)
    · obtain ⟨T, hT, hdep⟩ := ih (by omega) W (by
        intro w hw
        have h1 := hW w hw
        have h2 : w ≠ n + k := fun h => hmem (h ▸ hw)
        omega)
      exact ⟨T, by omega, hdep⟩

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) :
    G.support.ncard ≤ C.size + 1 := by
  obtain ⟨T, hT, hdep⟩ : ∃ T : Finset (Fin n), T.card ≤ C.gates.length + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
        val C (List.ofFn x) C.output = val C (List.ofFn y) C.output := by
    by_cases ho : C.output < n + C.gates.length
    · obtain ⟨T, hT, hdep⟩ := dep n C (fun j hj => h2 _ (gateAt_mem hj)) C.gates.length le_rfl
        {C.output} (by simpa using ho)
      exact ⟨T, by simpa using hT, fun x y h => hdep x y h _ (by simp)⟩
    · exact ⟨∅, by simp, fun x y _ => by
        rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]⟩
  have hsub : G.support ⊆ (T : Set (Fin n)) := by
    intro v hv
    obtain ⟨u, huv⟩ := (SimpleGraph.mem_support G).1 hv
    by_contra hvT
    have e := hdep (fun w => decide (w = u ∨ w = v)) (fun w => decide (w = u)) (by
      intro i hi
      have hne : i ≠ v := fun h => hvT (h ▸ hi)
      simp [hne])
    have fx : val C (List.ofFn (fun w => decide (w = u ∨ w = v))) C.output =
        graphFun G ∅ (fun w => decide (w = u ∨ w = v)) :=
      congrFun hF (fun w => decide (w = u ∨ w = v))
    have fy : val C (List.ofFn (fun w => decide (w = u))) C.output =
        graphFun G ∅ (fun w => decide (w = u)) :=
      congrFun hF (fun w => decide (w = u))
    have t1 : graphFun G ∅ (fun w => decide (w = u ∨ w = v)) = true := by
      unfold graphFun
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_iff]
      exact ⟨v, u, huv, by simp, by simp⟩
    have t2 : graphFun G ∅ (fun w => decide (w = u)) = false := by
      unfold graphFun
      rw [Bool.or_eq_false_iff]
      refine ⟨by simp, ?_⟩
      rw [decide_eq_false_iff_not]
      rintro ⟨a, b, hab, ha, hb⟩
      have ha' : a = u := by simpa using ha
      have hb' : b = u := by simpa using hb
      exact hab.ne (ha'.trans hb'.symm)
    rw [fx, fy, t1, t2] at e
    cases e
  calc G.support.ncard ≤ (T : Set (Fin n)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet T)
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ C.size + 1 := hT

end Support

lemma Support : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → x2.support.ncard ≤ x4.size + (1 : ℕ) := by
  intro n G _ C hL
  exact PEqualNP.Outside.L_meta_1735_aux.Support.main n G C hL.1.2.2 hL.2.1


namespace TwoJunk.Base

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

open PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

lemma pairInput_comm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp only [pairInput, or_comm]

lemma sub_zero2 : (1 : Fin 2) - 0 = 1 := by decide

lemma sub_one2 : (1 : Fin 2) - 1 = 0 := by decide

lemma edge_witness : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∀ x7 ∈ PEqualNP.TopForm.Ustar x2 x4, (∃ (x9 : Fin x1) (x10 : Fin x1), x7 = s(x9, x10) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x2 x4, ∃ (x12 : Fin (2 : ℕ)), ∃ x13 ∈ PEqualNP.TopForm.junk x2 x4, x9 ∈ PEqualNP.TopForm.side x4 x11 x12 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 ((1 : Fin (2 : ℕ)) - x12)) x13 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x13 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1), x7 = s(x9, x10) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x2 x4, ∃ x12 ∈ PEqualNP.TopForm.junk x2 x4, ∃ x13 ∈ PEqualNP.TopForm.junk x2 x4, x12 ≠ x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 (0 : Fin (2 : ℕ))) x12 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 (1 : Fin (2 : ℕ))) x13 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x13 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true := by
  intro n G _ C hL hT e
  induction e using Sym2.ind with
  | _ u v =>
  intro huv
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [PEqualNP.TopForm.Ustar, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet] at huv
  obtain ⟨hadj, hns⟩ := huv
  have hF : ∀ u v : Fin n, PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
      (PEqualNP.EdgeOwnership.pairInput u v) = true → G.Adj u v :=
    fun u v h => (PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.graphFun_pair G u v).mp h
  have hout : ∀ x : Fin n → Bool, PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.val C (List.ofFn x) C.output =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x :=
    fun x => congrFun hfun x
  obtain ⟨a, halen, hnor, hreach, hval⟩ :=
    PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.edge_trace G (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
      hF hout u v ((PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.graphFun_pair G u v).mpr hadj)
  have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op =
      PEqualNP.CircuitLowerBounds.GateOp.and := by
    rcases hAO _ (PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.gateAt_mem halen) with h | h
    · exact h
    · exact (hnor h).elim
  have hbel : PEqualNP.TopForm.BelowF G C a := fun x hx =>
    PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.below_of_reach
      (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) hout a hreach x hx
  have hatop : a ∈ PEqualNP.TopForm.tops G C := by
    simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨halen, hop, hbel⟩
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.gateAt_mem halen))
  have e0 : PEqualNP.TopForm.opnd C a 0 = p := by simp [PEqualNP.TopForm.opnd, hin]
  have e1 : PEqualNP.TopForm.opnd C a 1 = q := by simp [PEqualNP.TopForm.opnd, hin]
  have hpq := (PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.val_and (n := n) (by simp) halen hop).mp hval
  have hpin : p ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs := by rw [hin]; simp
  have hqin : q ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs := by rw [hin]; simp
  have hp := hpq p hpin
  have hq := hpq q hqin
  have junk_of : ∀ (w : ℕ), w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs →
      w < n + a → ∀ h, h < C.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or →
      Relation.ReflTransGen (PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.OrStep n C) w (n + h) →
      h ∈ PEqualNP.TopForm.junk G C ∧ ¬ PEqualNP.TopForm.BelowF G C h ∧
        PEqualNP.CleanedNonEdge.OrReaches n C w h := by
    intro w hwin hwlt h hh hhor hr
    have hhand : (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op =
        PEqualNP.CircuitLowerBounds.GateOp.and := by
      rcases hAO _ (PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.gateAt_mem hh) with h3 | h3
      · exact h3
      · exact (hhor h3).elim
    have hcone : PEqualNP.EdgeOwnership.InCone n C h a :=
      PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.operand_cone halen hwin hwlt hr
    have hnb : ¬ PEqualNP.TopForm.BelowF G C h := fun hb2 => hT h hh a halen hhand hb2 hop hcone
    have hdirty : PEqualNP.CleanedNonEdge.IsDirtyAnd n G C h := by
      unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
      refine ⟨hhand, hh, ?_⟩
      by_contra hne
      apply hnb
      intro x hx
      by_contra hfx
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
    have hjunk : h ∈ PEqualNP.TopForm.junk G C := by
      unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
    exact ⟨hjunk, hnb, PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.reach_orReaches hr h rfl hh⟩
  rcases PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.operand_trace (C := C) u v p hp.2 with
    ⟨t1, ht1, hr1⟩ | ⟨h1, hh1, hhor1, hr1, hv1⟩
  · rcases PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.operand_trace (C := C) u v q hq.2 with
      ⟨t2, ht2, hr2⟩ | ⟨h2', hh2, hhor2, hr2, hv2⟩
    · exfalso
      apply hns
      have hadj12 : G.Adj t1 t2 :=
        PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.side_adj G (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
          hF a halen hop hbel p q hin hp.1 hq.1 t1 t2 hr1 hr2
      have hne : t1 ≠ t2 := G.ne_of_adj hadj12
      have hs : s(u, v) = s(t1, t2) := by
        rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
        · exact (hne (h1.trans h2.symm)).elim
        · rw [h1, h2]
        · rw [h1, h2]; exact Sym2.eq_swap
        · exact (hne (h1.trans h2.symm)).elim
      rw [hs]
      simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_product]
      refine ⟨a, hatop, (t1, t2), ⟨?_, ?_⟩, rfl⟩
      · simp only [PEqualNP.TopForm.side, e0]
        exact PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.reach_mem_orIn t1 hr1
      · simp only [PEqualNP.TopForm.side, e1]
        exact PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.reach_mem_orIn t2 hr2
    · obtain ⟨hj, _, hor⟩ := junk_of q hqin hq.1 h2' hh2 hhor2 hr2
      left
      have hside : t1 ∈ PEqualNP.TopForm.side C a 0 := by
        simp only [PEqualNP.TopForm.side, e0]
        exact PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.reach_mem_orIn t1 hr1
      have hor' : PEqualNP.CleanedNonEdge.OrReaches n C
          (PEqualNP.TopForm.opnd C a ((1 : Fin 2) - 0)) h2' := by
        rw [PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.sub_zero2, e1]; exact hor
      rcases ht1 with rfl | rfl
      · exact ⟨t1, v, rfl, a, hatop, 0, h2', hj, hside, hor', hv2⟩
      · refine ⟨t1, u, Sym2.eq_swap, a, hatop, 0, h2', hj, hside, hor', ?_⟩
        rw [PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.pairInput_comm]; exact hv2
  · obtain ⟨hj1, hnb1, hor1⟩ := junk_of p hpin hp.1 h1 hh1 hhor1 hr1
    rcases PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.operand_trace (C := C) u v q hq.2 with
      ⟨t2, ht2, hr2⟩ | ⟨h2', hh2, hhor2, hr2, hv2⟩
    · left
      have hside : t2 ∈ PEqualNP.TopForm.side C a 1 := by
        simp only [PEqualNP.TopForm.side, e1]
        exact PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.reach_mem_orIn t2 hr2
      have hor' : PEqualNP.CleanedNonEdge.OrReaches n C
          (PEqualNP.TopForm.opnd C a ((1 : Fin 2) - 1)) h1 := by
        rw [PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.sub_one2, e0]; exact hor1
      rcases ht2 with rfl | rfl
      · exact ⟨t2, v, rfl, a, hatop, 1, h1, hj1, hside, hor', hv1⟩
      · refine ⟨t2, u, Sym2.eq_swap, a, hatop, 1, h1, hj1, hside, hor', ?_⟩
        rw [PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.pairInput_comm]; exact hv1
    · obtain ⟨hj2, _, hor2⟩ := junk_of q hqin hq.1 h2' hh2 hhor2 hr2
      right
      refine ⟨u, v, rfl, a, hatop, h1, hj1, h2', hj2, ?_, ?_, ?_, hv1, hv2⟩
      · intro heq
        subst heq
        apply hnb1
        intro x hx
        apply hbel
        show PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.val C (List.ofFn x) (n + a) = true
        rw [PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.val_and (n := n) (by simp) halen hop, hin]
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ⟨hp.1, PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.orStep_up (n := n) (by simp) hr1 hx⟩
        · exact ⟨hq.1, PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base.orStep_up (n := n) (by simp) hr2 hx⟩
      · rw [e0]; exact hor1
      · rw [e1]; exact hor2

end TwoJunk.Base



namespace TwoJunk

def gSupport {α : Type*} (A B S : Finset α) : Prop :=
  (∃ u ∈ S, u ∈ A) ∧ ∃ v ∈ S, v ∈ B

def hSupport {α : Type*} (A B P Q : Finset α) (a b : Bool) (S : Finset α) : Prop :=
  ((∃ u ∈ S, u ∈ P) ∨ (a = true ∧ gSupport A B S)) ∧
  ((∃ v ∈ S, v ∈ Q) ∨ (b = true ∧ gSupport A B S))

lemma gSupport_mono {α : Type*} {A B S T : Finset α} (sub : S ⊆ T) :
    gSupport A B S → gSupport A B T := by
  rintro ⟨⟨u, hu, hA⟩, v, hv, hB⟩
  exact ⟨⟨u, sub hu, hA⟩, v, sub hv, hB⟩

lemma gSupport_small {α : Type*} [DecidableEq α] {A B T : Finset α}
    (h : gSupport A B T) :
    ∃ S : Finset α, S ⊆ T ∧ S.card ≤ 2 ∧ gSupport A B S := by
  obtain ⟨⟨u, hu, hA⟩, v, hv, hB⟩ := h
  refine ⟨{u,v}, ?_, ?_, ⟨⟨u, by simp, hA⟩, v, by simp, hB⟩⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | h
    · exact hu
    · exact Finset.mem_singleton.mp h ▸ hv
  · simpa only [Finset.card_singleton] using Finset.card_insert_le u ({v} : Finset α)

lemma joint_bad_support {α : Type*} [DecidableEq α] (A B P Q : Finset α) (a b : Bool)
    (bad : Finset α → Prop)
    (down : ∀ {S T : Finset α}, S ⊆ T → bad T → bad S)
    (badG : ∃ S, bad S ∧ gSupport A B S)
    (badH : ∃ S, bad S ∧ hSupport A B P Q a b S) :
    ∃ Sg Sh : Finset α, bad Sg ∧ gSupport A B Sg ∧ bad Sh ∧
      hSupport A B P Q a b Sh ∧ (Sg ∪ Sh).card ≤ 4 := by
  obtain ⟨T, hT, hp, hq⟩ := badH
  rcases hp with ⟨u,hu,hP⟩ | ⟨ha,hg⟩ <;> rcases hq with ⟨v,hv,hQ⟩ | ⟨hb,hg'⟩
  · obtain ⟨U,hU,hg⟩ := badG
    obtain ⟨S,hs,sc,gs⟩ := gSupport_small hg
    have incl : ({u,v} : Finset α) ⊆ T := Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv)
    refine ⟨S,{u,v},down hs hU,gs,down incl hT,⟨Or.inl ⟨u,by simp,hP⟩, Or.inl ⟨v,by simp,hQ⟩⟩,?_⟩
    have hc : ({u,v} : Finset α).card ≤ 2 := by
      simpa only [Finset.card_singleton] using Finset.card_insert_le u ({v} : Finset α)
    have hcard := Finset.card_union_le S ({u,v} : Finset α)
    omega
  · obtain ⟨S,hs,sc,gs⟩ := gSupport_small hg'
    have inc : S ⊆ insert u S := Finset.subset_insert u S
    refine ⟨S,insert u S,down hs hT,gs,down (Finset.insert_subset hu hs) hT,
      ⟨Or.inl ⟨u,Finset.mem_insert_self _ _,hP⟩, Or.inr ⟨hb,gSupport_mono inc gs⟩⟩,?_⟩
    rw [Finset.union_eq_right.mpr inc]
    have hcard := Finset.card_insert_le u S
    omega
  · obtain ⟨S,hs,sc,gs⟩ := gSupport_small hg
    have inc : S ⊆ insert v S := Finset.subset_insert v S
    refine ⟨S,insert v S,down hs hT,gs,down (Finset.insert_subset hv hs) hT,
      ⟨Or.inr ⟨ha,gSupport_mono inc gs⟩,Or.inl ⟨v,Finset.mem_insert_self _ _,hQ⟩⟩,?_⟩
    rw [Finset.union_eq_right.mpr inc]
    have hcard := Finset.card_insert_le v S
    omega
  · obtain ⟨S,hs,sc,gs⟩ := gSupport_small hg
    refine ⟨S,S,down hs hT,gs,down hs hT,⟨Or.inr ⟨ha,gs⟩,Or.inr ⟨hb,gs⟩⟩,?_⟩
    rw [Finset.union_idempotent]
    omega

end TwoJunk

namespace TwoJunk.Structural

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_1735_aux.TwoJunk.Base

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma inCone_lt {i j : ℕ} (hc : InCone n C i j) : i < j := by
  have go : ∀ j i, InCone n C i j → i < j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro i hc
      obtain ⟨_, k, hkj, _, hi⟩ := (inCone_iff n C i j).mp hc
      rcases hi with rfl | hi
      · exact hkj
      · exact (ih k hkj i hi).trans hkj
  exact go j i hc

lemma inCone_trans {i j k : ℕ} (hij : InCone n C i j) (hjk : InCone n C j k) :
    InCone n C i k := by
  have go : ∀ k j, InCone n C j k → InCone n C i j → InCone n C i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro j hjk hij
      obtain ⟨hk, t, htk, htin, hjt⟩ := (inCone_iff n C j k).mp hjk
      apply (inCone_iff n C i k).mpr
      refine ⟨hk, t, htk, htin, Or.inr ?_⟩
      rcases hjt with rfl | hjt
      · exact hij
      · exact ih t htk j hjt hij
  exact go k j hjk hij

lemma junk_spec {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  exact ⟨ha.1, ha.2.1, ha.2.2.2⟩

lemma and_ancestor_junk (hTop : TopForm G C) {a k : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hk : k < C.gates.length) (hkand : (gateAt C k).op = GateOp.and)
    (hc : InCone n C k a) : k ∈ junk G C := by
  have hnb : ¬ BelowF G C k := fun hb => hTop k hk a ha hkand hb hand hc
  have hd : IsDirtyAnd n G C k := by
    unfold IsDirtyAnd IsDirty
    refine ⟨hkand, hk, ?_⟩
    by_contra he
    apply hnb
    intro x hx
    by_contra hf
    exact he ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hd⟩

lemma opnd_mem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  have hlen := hAO.2.2 _ (gateAt_mem ha)
  unfold opnd
  have hb : b.val < (gateAt C a).inputs.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
  exact List.getElem_mem hb

lemma opnd_lt (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a := hAO.2.1 a ha _ (opnd_mem hAO ha b)

lemma mem_inputs_iff_opnd (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (w : ℕ) :
    w ∈ (gateAt C a).inputs ↔ ∃ b : Fin 2, opnd C a b = w := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
  constructor
  · intro hw
    rw [hin] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨0, by simp [opnd, hin]⟩
    · exact ⟨1, by simp [opnd, hin]⟩
  · rintro ⟨b, rfl⟩
    exact opnd_mem hAO ha b

lemma and_true_iff (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  change val C (List.ofFn x) (n + a) = true ↔ _
  rw [val_and (n := n) (by simp) ha hand]
  constructor
  · intro hv b
    exact (hv _ (opnd_mem hAO ha b)).2
  · intro hv w hw
    obtain ⟨b, rfl⟩ := (mem_inputs_iff_opnd hAO ha w).mp hw
    exact ⟨opnd_lt hAO ha b, hv b⟩

lemma wire_mono (hAO : IsAO2 n C) (x y : Fin n → Bool)
    (hxy : ∀ u, x u = true → y u = true) :
    ∀ w, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have hx : x ⟨w, hw⟩ = true := (val_ofFn C x ⟨w, hw⟩).symm.trans hv
      exact (val_ofFn C y ⟨w, hw⟩).trans (hxy _ hx)
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rcases hAO.1 _ (gateAt_mem hk) with hop | hop
        · apply (val_and (n := n) (by simp) hk hop).mpr
          intro i hi
          obtain ⟨hlt, hvi⟩ := (val_and (n := n) (by simp) hk hop).mp hv i hi
          exact ⟨hlt, ih i hlt hvi⟩
        · obtain ⟨i, hi, hlt, hvi⟩ := (val_or (n := n) (by simp) hk hop).mp hv
          exact (val_or (n := n) (by simp) hk hop).mpr ⟨i, hi, hlt, ih i hlt hvi⟩

lemma gate_mono (hAO : IsAO2 n C) (x y : Fin n → Bool)
    (hxy : ∀ u, x u = true → y u = true) (a : ℕ)
    (hx : gateVal n C a x = true) : gateVal n C a y = true :=
  wire_mono hAO x y hxy (n + a) hx

lemma and_operand_iff (hAO : IsAO2 n C) (hTop : TopForm G C) {a p : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hp : p ∈ (gateAt C a).inputs) (x : Fin n → Bool) :
    val C (List.ofFn x) p = true ↔
      (∃ u ∈ orIn n C p, x u = true) ∨
      ∃ k ∈ junk G C, InCone n C k a ∧ OrReaches n C p k ∧ gateVal n C k x = true := by
  constructor
  · intro hv
    obtain ⟨w, hr, hvw, hw⟩ := or_trace (n := n) (C := C) (x := List.ofFn x) (by simp) p hv
    rcases hw with hw | ⟨k, hk, rfl, hnor⟩
    · exact Or.inl ⟨⟨w, hw⟩, reach_mem_orIn ⟨w, hw⟩ hr,
        (val_ofFn C x ⟨w, hw⟩).symm.trans hvw⟩
    · have hkand : (gateAt C k).op = GateOp.and := by
        rcases hAO.1 _ (gateAt_mem hk) with hand | hor
        · exact hand
        · exact (hnor hor).elim
      have hc := operand_cone ha hp (hAO.2.1 a ha p hp) hr
      exact Or.inr ⟨k, and_ancestor_junk hTop ha hand hk hkand hc,
        hc, reach_orReaches hr k rfl hk, hvw⟩
  · rintro (⟨u, hu, hxu⟩ | ⟨k, _, _, hr, hv⟩)
    · exact reach_var_val x p u (mem_orIn_reach u hu) hxu
    · exact orStep_up (n := n) (by simp) (orReaches_reach k p hr).1 hv

lemma lower_operand_iff (hAO : IsAO2 n C) (hTop : TopForm G C) {g h : ℕ}
    (hj : junk G C = {g, h}) (cone : InCone n C g h) (b : Fin 2) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C g b) = true ↔ ∃ u ∈ side C g b, x u = true := by
  have hgm : g ∈ junk G C := by rw [hj]; simp
  obtain ⟨hg, hgand, _⟩ := junk_spec hgm
  constructor
  · intro hv
    rcases (and_operand_iff hAO hTop hg hgand (opnd_mem hAO hg b) x).mp hv with
      hraw | ⟨k, hkj, hkg, _, _⟩
    · exact hraw
    · have hkg' := inCone_lt hkg
      have hgh := inCone_lt cone
      have hk : k = g ∨ k = h := by simpa [hj] using hkj
      omega
  · rintro ⟨u, hu, hxu⟩
    exact reach_var_val x _ u (mem_orIn_reach u hu) hxu

lemma upper_operand_iff (hAO : IsAO2 n C) (hTop : TopForm G C) {g h : ℕ}
    (hj : junk G C = {g, h}) (cone : InCone n C g h) (b : Fin 2) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C h b) = true ↔
      (∃ u ∈ side C h b, x u = true) ∨
      (OrReaches n C (opnd C h b) g ∧ gateVal n C g x = true) := by
  have hhm : h ∈ junk G C := by rw [hj]; simp
  obtain ⟨hh, hhand, _⟩ := junk_spec hhm
  constructor
  · intro hv
    rcases (and_operand_iff hAO hTop hh hhand (opnd_mem hAO hh b) x).mp hv with
      hraw | ⟨k, hkj, hkh, hr, hvk⟩
    · exact Or.inl hraw
    · have hkh' := inCone_lt hkh
      have hk : k = g ∨ k = h := by simpa [hj] using hkj
      have hkg : k = g := by omega
      subst k
      exact Or.inr ⟨hr, hvk⟩
  · rintro (⟨u, hu, hxu⟩ | ⟨hr, hvg⟩)
    · exact reach_var_val x _ u (mem_orIn_reach u hu) hxu
    · exact orStep_up (n := n) (by simp) (orReaches_reach g _ hr).1 hvg

lemma upper_reaches (hAO : IsAO2 n C) (hTop : TopForm G C) {g h : ℕ}
    (hj : junk G C = {g, h}) (cone : InCone n C g h) :
    ∃ b : Fin 2, OrReaches n C (opnd C h b) g := by
  have hgm : g ∈ junk G C := by rw [hj]; simp
  have hhm : h ∈ junk G C := by rw [hj]; simp
  obtain ⟨hg, hgand, _⟩ := junk_spec hgm
  obtain ⟨hh, hhand, _⟩ := junk_spec hhm
  have only_g : ∀ k, InCone n C k h → (gateAt C k).op ≠ GateOp.or → k = g := by
    intro k hkh hnor
    have hkh' := inCone_lt hkh
    have hk : k < C.gates.length := by omega
    have hkand : (gateAt C k).op = GateOp.and := by
      rcases hAO.1 _ (gateAt_mem hk) with hand | hor
      · exact hand
      · exact (hnor hor).elim
    have hkj := and_ancestor_junk hTop hh hhand hk hkand hkh
    have hc : k = g ∨ k = h := by simpa [hj] using hkj
    omega
  have go : ∀ k, InCone n C k h → (g = k ∨ InCone n C g k) →
      OrReaches n C (n + k) g := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hkh hgk
      rcases hgk with rfl | hgk
      · exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
      · have hgk' := inCone_lt hgk
        have hkor : (gateAt C k).op = GateOp.or := by
          by_contra hnor
          have hkg := only_g k hkh hnor
          omega
        obtain ⟨hk, t, htk, htin, hgt⟩ := (inCone_iff n C g k).mp hgk
        have htkc : InCone n C t k :=
          (inCone_iff n C t k).mpr ⟨hk, t, htk, htin, Or.inl rfl⟩
        have hth := inCone_trans htkc hkh
        exact (orReaches_iff n C k g).mpr
          ⟨hk, Or.inr ⟨hkor, n + t, htin, by omega, ih t htk hth hgt⟩⟩
  obtain ⟨_, k, hkh, hkin, hgk⟩ := (inCone_iff n C g h).mp cone
  have hkc : InCone n C k h := (inCone_iff n C k h).mpr ⟨hh, k, hkh, hkin, Or.inl rfl⟩
  obtain ⟨b, hb⟩ := (mem_inputs_iff_opnd hAO hh (n + k)).mp hkin
  refine ⟨b, ?_⟩
  rw [hb]
  exact go k hkc hgk

end TwoJunk.Structural


namespace TwoJunk.GraphSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def input {n : ℕ} (S : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∈ S)

def support {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun v => x v = true)

lemma input_support {n : ℕ} (x : Fin n → Bool) : input (support x) = x := by
  funext v
  cases hv : x v <;> simp [input, support, hv]

def bad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) : Prop :=
  graphFun G ∅ (input S) = false

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) :
    graphFun G ∅ (input S) = true ↔ ∃ u v, G.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, input]

lemma bad_down {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {S T : Finset (Fin n)} (sub : S ⊆ T) (hT : bad G T) : bad G S := by
  apply Bool.eq_false_iff.mpr
  intro hS
  obtain ⟨u,v,huv,hu,hv⟩ := (graph_true G S).mp hS
  have contra := (graph_true G T).mpr ⟨u,v,huv,sub hu,sub hv⟩
  change graphFun G ∅ (input T) = false at hT
  rw [hT] at contra
  contradiction

lemma adj_of_insert {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {S : Finset (Fin n)} {r : Fin n} (hS : bad G S)
    (h : graphFun G ∅ (input (insert r S)) = true) : ∃ v ∈ S, G.Adj r v := by
  obtain ⟨u,v,huv,hu,hv⟩ := (graph_true G (insert r S)).mp h
  rcases Finset.mem_insert.mp hu with eu|huS <;> rcases Finset.mem_insert.mp hv with ev|hvS
  · rw [eu,ev] at huv
    exact (G.irrefl huv).elim
  · exact ⟨v,hvS,eu ▸ huv⟩
  · exact ⟨u,huS,ev ▸ huv.symm⟩
  · have contra := (graph_true G S).mpr ⟨u,v,huv,huS,hvS⟩
    change graphFun G ∅ (input S) = false at hS
    rw [hS] at contra
    contradiction

lemma insert_neighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (r : Fin n) (hS : bad G S)
    (h : graphFun G ∅ (input (insert r S)) = true) : ∃ v ∈ S, G.Adj r v :=
  adj_of_insert G hS h

lemma hSupport_up {α : Type*} {A B P Q S T : Finset α} {a b : Bool}
    (sub : S ⊆ T) (ht : hSupport A B P Q a b S) : hSupport A B P Q a b T := by
  have liftSide (R : Finset α) (f : Bool) :
      ((∃ u ∈ S, u ∈ R) ∨ (f = true ∧ gSupport A B S)) →
      ((∃ u ∈ T, u ∈ R) ∨ (f = true ∧ gSupport A B T)) := by
    rintro (⟨u,hu,hr⟩ | ⟨hf,hg⟩)
    · exact Or.inl ⟨u,sub hu,hr⟩
    · exact Or.inr ⟨hf,gSupport_mono sub hg⟩
  exact ⟨liftSide P a ht.1,liftSide Q b ht.2⟩

lemma joint_gate_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (A B P Q : Finset (Fin n)) (a b : Bool)
    (low : ∀ S, gateVal n C g (input S) = true ↔ gSupport A B S)
    (high : ∀ S, gateVal n C h (input S) = true ↔ hSupport A B P Q a b S)
    (dg : ∃ x, gateVal n C g x = true ∧ graphFun G ∅ x = false)
    (dh : ∃ x, gateVal n C h x = true ∧ graphFun G ∅ x = false) :
    ∃ Sg Sh : Finset (Fin n), bad G Sg ∧ gateVal n C g (input Sg) = true ∧
      bad G Sh ∧ gateVal n C h (input Sh) = true ∧ (Sg ∪ Sh).card ≤ 4 := by
  obtain ⟨xg,gx,fg⟩ := dg
  obtain ⟨xh,hx,fh⟩ := dh
  have badG : ∃ S, bad G S ∧ gSupport A B S := by
    refine ⟨support xg, by simpa only [bad,input_support] using fg, (low _).mp ?_⟩
    simpa only [input_support] using gx
  have badH : ∃ S, bad G S ∧ hSupport A B P Q a b S := by
    refine ⟨support xh, by simpa only [bad,input_support] using fh, (high _).mp ?_⟩
    simpa only [input_support] using hx
  obtain ⟨Sg,Sh,hg,gs,hh,hs,hcard⟩ :=
    joint_bad_support A B P Q a b (bad G) (fun {_ _} sub hT => bad_down G sub hT) badG badH
  exact ⟨Sg,Sh,hg,(low Sg).mpr gs,hh,(high Sh).mpr hs,hcard⟩

end TwoJunk.GraphSupport

namespace TwoJunk.Final

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_1735_aux.TwoJunk

lemma two_cases : ∀ b c : Fin 2, c = b ∨ c = 1 - b := by decide

lemma forall_two {P : Fin 2 → Prop} : (∀ b, P b) ↔ P 0 ∧ P 1 := by
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · rintro ⟨h0,h1⟩ b
    rcases two_cases 0 b with rfl | hb
    · exact h0
    · have hb1 : b = 1 := by simpa using hb
      simpa only [hb1] using h1

lemma reach_up {n : ℕ} {C : Circuit} {w k : ℕ} (x : Fin n → Bool)
    (hr : OrReaches n C w k) (hv : gateVal n C k x = true) :
    Base.val C (List.ofFn x) w = true :=
  Base.orStep_up (n := n) (by simp) (Base.orReaches_reach k w hr).1 hv

lemma raw_up {n : ℕ} {C : Circuit} {w : ℕ} (x : Fin n → Bool) (u : Fin n)
    (hu : u ∈ orIn n C w) (hx : x u = true) :
    Base.val C (List.ofFn x) w = true :=
  Base.reach_var_val x w u (Base.mem_orIn_reach u hu) hx

lemma top_force {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {t : ℕ} (ht : t ∈ tops G C)
    (x : Fin n → Bool)
    (hv : ∀ b : Fin 2, Base.val C (List.ofFn x) (opnd C t b) = true) :
    graphFun G ∅ x = true := by
  have hs : t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ BelowF G C t := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ht
  exact hs.2.2 x ((Structural.and_true_iff hAO hs.1 hs.2.1 x).2 hv)

lemma top_pair_force {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {t g h : ℕ} (ht : t ∈ tops G C)
    (r0 : OrReaches n C (opnd C t 0) g)
    (r1 : OrReaches n C (opnd C t 1) h)
    (x : Fin n → Bool) (vg : gateVal n C g x = true) (vh : gateVal n C h x = true) :
    graphFun G ∅ x = true := by
  apply top_force hAO ht x
  exact forall_two.mpr ⟨reach_up x r0 vg, reach_up x r1 vh⟩

lemma single_neighbor {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {t j : ℕ} (ht : t ∈ tops G C)
    (b : Fin 2) (u : Fin n) (hu : u ∈ side (n := n) C t b)
    (hr : OrReaches n C (opnd C t (1 - b)) j)
    (S : Finset (Fin n)) (hb : GraphSupport.bad G S)
    (hv : gateVal n C j (GraphSupport.input S) = true) :
    ∃ r ∈ S, G.Adj u r := by
  apply GraphSupport.adj_of_insert G hb
  let x := GraphSupport.input (insert u S)
  have hmono : ∀ v, GraphSupport.input S v = true → x v = true := by
    intro v hv
    simp only [x, GraphSupport.input, decide_eq_true_eq] at hv ⊢
    exact Finset.mem_insert_of_mem hv
  have hv' := Structural.gate_mono hAO (GraphSupport.input S) x hmono j hv
  apply top_force hAO ht x
  intro c
  rcases two_cases b c with rfl | rfl
  · exact raw_up x u hu (by simp [x, GraphSupport.input])
  · exact reach_up x hr hv'

lemma double_neighbor {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hTop : PEqualNP.TopForm.TopForm G C)
    {g h : ℕ} (hj : junk G C = {g,h}) (hc : InCone n C g h)
    (S : Finset (Fin n)) (hb : GraphSupport.bad G S)
    (hvg : gateVal n C g (GraphSupport.input S) = true)
    (u v : Fin n) (hvh : gateVal n C h (pairInput u v) = true)
    (force : ∀ x, gateVal n C g x = true → gateVal n C h x = true → graphFun G ∅ x = true) :
    (∃ r ∈ S, G.Adj u r) ∨ ∃ r ∈ S, G.Adj v r := by
  have hhj : h ∈ junk G C := by simp [hj]
  have hd : IsDirtyAnd n G C h := (Finset.mem_filter.mp hhj).2
  obtain ⟨b,hr⟩ := Structural.upper_reaches hAO hTop hj hc
  have hnr : ¬ OrReaches n C (opnd C h (1-b)) g := by
    intro hr'
    have hh : gateVal n C h (GraphSupport.input S) = true := by
      apply (Structural.and_true_iff hAO hd.2.1 hd.1 _).2
      intro c
      rcases two_cases b c with rfl | rfl
      · exact reach_up _ hr hvg
      · exact reach_up _ hr' hvg
    have ht := force _ hvg hh
    rw [show graphFun G ∅ (GraphSupport.input S) = false from hb] at ht
    cases ht
  have hparent := (Structural.and_true_iff hAO hd.2.1 hd.1 _).1 hvh (1-b)
  have hraw := (Structural.upper_operand_iff hAO hTop hj hc (1-b) (pairInput u v)).1 hparent
  rcases hraw with ⟨r,hrs,hrv⟩ | ⟨hbad,_⟩
  · have hrpair := (Base.pairInput_true u v r).1 hrv
    have hn : ∃ z ∈ S, G.Adj r z := by
      apply GraphSupport.adj_of_insert G hb
      let x := GraphSupport.input (insert r S)
      have hmono : ∀ z, GraphSupport.input S z = true → x z = true := by
        intro z hz
        simp only [x, GraphSupport.input, decide_eq_true_eq] at hz ⊢
        exact Finset.mem_insert_of_mem hz
      have vg := Structural.gate_mono hAO (GraphSupport.input S) x hmono g hvg
      apply force x vg
      apply (Structural.and_true_iff hAO hd.2.1 hd.1 x).2
      intro c
      rcases two_cases b c with rfl | rfl
      · exact reach_up x hr vg
      · exact raw_up x r hrs (by simp [x, GraphSupport.input])
    rcases hrpair with rfl | rfl
    · exact Or.inl hn
    · exact Or.inr hn
  · exact (hnr hbad).elim

lemma raw_support {n : ℕ} (S A : Finset (Fin n)) :
    (∃ u ∈ A, GraphSupport.input S u = true) ↔ ∃ u ∈ S, u ∈ A := by
  simp only [GraphSupport.input, decide_eq_true_eq]
  exact exists_congr fun _ => and_comm

lemma support_witnesses {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hTop : PEqualNP.TopForm.TopForm G C)
    {g h : ℕ} (hj : junk G C = {g,h}) (hc : InCone n C g h) :
    ∃ Sg Sh : Finset (Fin n), GraphSupport.bad G Sg ∧
      gateVal n C g (GraphSupport.input Sg) = true ∧ GraphSupport.bad G Sh ∧
      gateVal n C h (GraphSupport.input Sh) = true ∧ (Sg ∪ Sh).card ≤ 4 := by
  have hgm : g ∈ junk G C := by simp [hj]
  have hhm : h ∈ junk G C := by simp [hj]
  obtain ⟨hg,hgand,dg⟩ := Structural.junk_spec hgm
  obtain ⟨hh,hhand,dh⟩ := Structural.junk_spec hhm
  let A := side (n := n) C g 0
  let B := side (n := n) C g 1
  let P := side (n := n) C h 0
  let Q := side (n := n) C h 1
  let a := decide (OrReaches n C (opnd C h 0) g)
  let b := decide (OrReaches n C (opnd C h 1) g)
  have low : ∀ S, gateVal n C g (GraphSupport.input S) = true ↔ gSupport A B S := by
    intro S
    rw [Structural.and_true_iff hAO hg hgand, forall_two,
      Structural.lower_operand_iff hAO hTop hj hc 0,
      Structural.lower_operand_iff hAO hTop hj hc 1,
      raw_support S, raw_support S]
    rfl
  have high : ∀ S, gateVal n C h (GraphSupport.input S) = true ↔
      hSupport A B P Q a b S := by
    intro S
    rw [Structural.and_true_iff hAO hh hhand, forall_two,
      Structural.upper_operand_iff hAO hTop hj hc 0,
      Structural.upper_operand_iff hAO hTop hj hc 1,
      raw_support S, raw_support S, low S]
    simp only [hSupport, a, b, decide_eq_true_eq, P, Q]
  exact GraphSupport.joint_gate_support G C g h A B P Q a b low high dg dh

lemma cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hTop : PEqualNP.TopForm.TopForm G C)
    (hcard : (junk G C).card = 2)
    (nested : ∃ g ∈ junk G C, ∃ h ∈ junk G C, InCone n C g h) :
    ∃ K : Finset (Fin n), K.card ≤ 4 ∧
      ∀ e ∈ Ustar G C, ∃ u v : Fin n, e = s(u,v) ∧
        ((∃ r ∈ K, G.Adj u r) ∨ ∃ r ∈ K, G.Adj v r) := by
  obtain ⟨g,hg,h,hh,hc⟩ := nested
  have hgh : g ≠ h := Nat.ne_of_lt (Structural.inCone_lt hc)
  have hsub : ({g,h} : Finset ℕ) ⊆ junk G C := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hg
    · exact hh
  have hj : junk G C = {g,h} :=
    (Finset.eq_of_subset_of_card_le hsub (by simp [hcard, hgh])).symm
  obtain ⟨Sg,Sh,hbg,hvg,hbh,hvh,hsize⟩ := support_witnesses hL.1 hTop hj hc
  refine ⟨Sg ∪ Sh,hsize,?_⟩
  intro e he
  rcases Base.edge_witness n G C hL hTop e he with
    ⟨u,v,hev,t,ht,b,j,hjmem,hu,hr,_⟩ |
    ⟨u,v,hev,t,ht,j,hjmem,k,hkmem,hjk,r0,r1,vj,vk⟩
  · refine ⟨u,v,hev,Or.inl ?_⟩
    have hjcases : j = g ∨ j = h := by simpa [hj] using hjmem
    rcases hjcases with rfl | rfl
    · obtain ⟨r,hrs,ha⟩ := single_neighbor hL.1 ht b u hu hr Sg hbg hvg
      exact ⟨r,Finset.mem_union_left _ hrs,ha⟩
    · obtain ⟨r,hrs,ha⟩ := single_neighbor hL.1 ht b u hu hr Sh hbh hvh
      exact ⟨r,Finset.mem_union_right _ hrs,ha⟩
  · refine ⟨u,v,hev,?_⟩
    have hjcases : j = g ∨ j = h := by simpa [hj] using hjmem
    have hkcases : k = g ∨ k = h := by simpa [hj] using hkmem
    have hnear : (∃ r ∈ Sg, G.Adj u r) ∨ ∃ r ∈ Sg, G.Adj v r := by
      rcases hjcases with rfl | rfl <;> rcases hkcases with rfl | rfl
      · exact (hjk rfl).elim
      · exact double_neighbor hL.1 hTop hj hc Sg hbg hvg u v vk
          (fun x vg vh => top_pair_force hL.1 ht r0 r1 x vg vh)
      · exact double_neighbor hL.1 hTop hj hc Sg hbg hvg u v vj
          (fun x vg vh => top_pair_force hL.1 ht r0 r1 x vh vg)
      · exact (hjk rfl).elim
    rcases hnear with ⟨r,hrs,ha⟩ | ⟨r,hrs,ha⟩
    · exact Or.inl ⟨r,Finset.mem_union_left _ hrs,ha⟩
    · exact Or.inr ⟨r,Finset.mem_union_left _ hrs,ha⟩

end TwoJunk.Final



open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

lemma nested_two_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (hcard : (junk G C).card = 2)
    (hnested : ∃ g ∈ junk G C, ∃ h ∈ junk G C, InCone n C g h) :
    (Ustar G C).card ≤ 4 * (C.size + 1) := by
  let V := Fin n
  let Near (G : SimpleGraph V) (S : Finset V) (p : V) : Prop :=
    ∃ z ∈ S, G.Adj p z

  let NoTriangle (G : SimpleGraph V) : Prop :=
    ∀ p z w, G.Adj p z → G.Adj p w → ¬ G.Adj z w

  let UniqueCommonNeighbor (G : SimpleGraph V) : Prop :=
    ∀ p z a b, p ≠ z → G.Adj p a → G.Adj z a → G.Adj p b → G.Adj z b → a = b

  have noTriangle_of_girth (G : SimpleGraph V)
      (hg : ∀ p (w : G.Walk p p), w.IsCycle → 5 ≤ w.length) : NoTriangle G := by
    intro p z u hpz hpu hzu
    let w : G.Walk p p := .cons hpz (.cons hzu (.cons hpu.symm .nil))
    have hc : w.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
      constructor
      · rw [SimpleGraph.Walk.isPath_def]
        simp [w, hzu.ne, hpz.ne.symm, hpu.ne.symm]
      · simp [w]
    have h := hg p w hc
    simp [w] at h

  have uniqueCommonNeighbor_of_girth (G : SimpleGraph V)
      (hg : ∀ p (w : G.Walk p p), w.IsCycle → 5 ≤ w.length) : UniqueCommonNeighbor G := by
    intro p z a b hpz hpa hza hpb hzb
    by_contra hab
    let w : G.Walk p p := .cons hpa (.cons hza.symm (.cons hzb (.cons hpb.symm .nil)))
    have hc : w.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
      constructor
      · rw [SimpleGraph.Walk.isPath_def]
        simp [w, hpz.symm, hab, hza.ne.symm, hpa.ne.symm, hzb.ne, hpb.ne.symm]
      · simp [w]
    have h := hg p w hc
    simp [w] at h

  let neighborhoodEdges (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset (Sym2 V)) (z : V) :=
    E.filter (fun e => ∃ p q, e = s(p, q) ∧ G.Adj z p)

  have one_neighborhood_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
      (h3 : NoTriangle G) (h4 : UniqueCommonNeighbor G) (E : Finset (Sym2 V))
      (hE : E ⊆ G.edgeFinset) (D : Finset V)
      (hD : ∀ p q, G.Adj p q → p ∈ D ∧ q ∈ D) (z : V) :
      (neighborhoodEdges G E z).card ≤ D.card := by
    classical
    let bucket (v : V) := E.filter (fun e =>
      (e = s(z, v) ∧ G.Adj z v) ∨
      (v ≠ z ∧ ¬ G.Adj z v ∧ ∃ u, e = s(u, v) ∧ G.Adj z u))
    have hB (v : V) (hv : v ∈ D) : (bucket v).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro e he f hf
      obtain ⟨heE, heB⟩ := Finset.mem_filter.mp he
      obtain ⟨hfE, hfB⟩ := Finset.mem_filter.mp hf
      rcases heB with ⟨rfl, heA⟩ | ⟨hvZ, hvA, u, rfl, hzu⟩ <;>
        rcases hfB with ⟨rfl, hfA⟩ | ⟨hvZ', hvA', w, rfl, hzw⟩
      · rfl
      · exact False.elim (hvA' heA)
      · exact False.elim (hvA hfA)
      · have huv : G.Adj u v := G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp (hE heE))
        have hwv : G.Adj w v := G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp (hE hfE))
        rw [h4 v z u w hvZ (G.adj_symm huv) hzu (G.adj_symm hwv) hzw]
    have hcov : neighborhoodEdges G E z ⊆ D.biUnion bucket := by
      intro e he
      have he' : e ∈ E ∧ ∃ p q, e = s(p, q) ∧ G.Adj z p := Finset.mem_filter.mp he
      obtain ⟨heE, p, q, rfl, hzp⟩ := he'
      have hpq : G.Adj p q := G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp (hE heE))
      have hpD := (hD p q hpq).1
      have hqD := (hD p q hpq).2
      by_cases hqz : q = z
      · subst q
        refine Finset.mem_biUnion.mpr ⟨p, hpD, Finset.mem_filter.mpr ⟨heE, Or.inl ?_⟩⟩
        exact ⟨Sym2.eq_swap, hzp⟩
      · have hnq : ¬ G.Adj z q := fun hzq => h3 z p q hzp hzq hpq
        exact Finset.mem_biUnion.mpr ⟨q, hqD,
          Finset.mem_filter.mpr ⟨heE, Or.inr ⟨hqz, hnq, p, rfl, hzp⟩⟩⟩
    have htotal := Finset.card_biUnion_le_card_mul D bucket 1 hB
    exact (Finset.card_le_card hcov).trans (by simpa using htotal)

  have neighborhood_cover_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
      (h3 : NoTriangle G) (h4 : UniqueCommonNeighbor G) (E : Finset (Sym2 V))
      (hE : E ⊆ G.edgeFinset) (D : Finset V)
      (hD : ∀ p q, G.Adj p q → p ∈ D ∧ q ∈ D) (S : Finset V)
      (hc : ∀ e ∈ E, ∃ p q, e = s(p, q) ∧ (Near G S p ∨ Near G S q)) :
      E.card ≤ S.card * D.card := by
    classical
    have hsub : E ⊆ S.biUnion (neighborhoodEdges G E) := by
      intro e he
      obtain ⟨p, q, eq, hp | hq⟩ := hc e he
      · obtain ⟨z, hz, hpz⟩ := hp
        refine Finset.mem_biUnion.mpr ⟨z, hz, ?_⟩
        exact Finset.mem_filter.mpr ⟨he, p, q, eq, G.adj_symm hpz⟩
      · obtain ⟨z, hz, hqz⟩ := hq
        refine Finset.mem_biUnion.mpr ⟨z, hz, ?_⟩
        exact Finset.mem_filter.mpr ⟨he, q, p, eq.trans Sym2.eq_swap, G.adj_symm hqz⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul S _ _
      (fun z _ => one_neighborhood_card_le G h3 h4 E hE D hD z))
  classical
  obtain ⟨K, hK, hcov⟩ := TwoJunk.Final.cover G C hL hTop hcard hnested
  let support := (Finset.univ : Finset (Fin n)).filter (fun p => p ∈ G.support)
  have hsSet : (support : Set (Fin n)) = G.support := by
    ext p
    simp [support]
  have hsCard : support.card = G.support.ncard := by
    rw [← hsSet, Set.ncard_coe_finset]
  have hsMem (p q : Fin n) (hadj : G.Adj p q) : p ∈ support ∧ q ∈ support := by
    have hp : p ∈ G.support := ⟨q, hadj⟩
    have hq : q ∈ G.support := ⟨p, hadj.symm⟩
    simp [support, hp, hq]
  have hCount := neighborhood_cover_card_le G (noTriangle_of_girth G hg)
    (uniqueCommonNeighbor_of_girth G hg) (Ustar G C) Finset.sdiff_subset
    support hsMem K hcov
  exact hCount.trans (Nat.mul_le_mul hK (hsCard.trans_le (Support n G C hL)))



namespace Parallel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma no4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have e1 := G.ne_of_adj hab
  have e2 := G.ne_of_adj hbc
  have e3 := G.ne_of_adj hcd
  have e4 := G.ne_of_adj hda
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, e2, e3, e4, hbd, Ne.symm e1, Ne.symm hac]
    · simp [e1, e2, hac, hbd, Ne.symm e1, Ne.symm e4]
  have h5 := hg a _ hcyc
  simp at h5

-- A certificate and a context are compatible when no edge runs between them.
def Apart {V : Type*} (E : V → V → Prop) (A B : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ¬ E a b

lemma apart_symm {V : Type*} {E : V → V → Prop} (hs : ∀ a b, E a b → E b a)
    {A B : Finset V} (h : Apart E A B) : Apart E B A :=
  fun b hb a ha hba => h a ha b hb (hs _ _ hba)

lemma apart_union_right {V : Type*} [DecidableEq V] {E : V → V → Prop}
    {A B D : Finset V} : Apart E A (B ∪ D) ↔ Apart E A B ∧ Apart E A D := by
  constructor
  · intro h
    exact ⟨fun x hx y hy => h x hx y (Finset.mem_union_left _ hy),
      fun x hx y hy => h x hx y (Finset.mem_union_right _ hy)⟩
  · rintro ⟨h₁, h₂⟩ x hx y hy
    exact (Finset.mem_union.mp hy).elim (h₁ x hx y) (h₂ x hx y)

lemma apart_union_left {V : Type*} [DecidableEq V] {E : V → V → Prop}
    {A B D : Finset V} : Apart E (A ∪ B) D ↔ Apart E A D ∧ Apart E B D := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (Finset.mem_union_left _ hx),
      fun x hx => h x (Finset.mem_union_right _ hx)⟩
  · rintro ⟨h₁, h₂⟩ x hx
    exact (Finset.mem_union.mp hx).elim (h₁ x) (h₂ x)

lemma union_bound {I V : Type*} [DecidableEq V] (A : Finset I) (F : I → Finset V)
    (b : ℕ) (h : ∀ i ∈ A, (F i).card ≤ b) : (A.biUnion F).card ≤ A.card * b := by
  calc
    _ ≤ ∑ i ∈ A, (F i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, b := Finset.sum_le_sum h
    _ = _ := by simp

def vertices {V : Type*} [DecidableEq V] (A : Finset (Finset V)) : Finset V :=
  A.biUnion id

lemma vertices_bound {V : Type*} [DecidableEq V] (A : Finset (Finset V)) (t : ℕ)
    (h : ∀ W ∈ A, W.card ≤ t) : (vertices A).card ≤ A.card * t :=
  union_bound A id t h

lemma subset_vertices {V : Type*} [DecidableEq V] {A : Finset (Finset V)} {W : Finset V}
    (h : W ∈ A) : W ⊆ vertices A :=
  fun _ hw => Finset.mem_biUnion.mpr ⟨W, h, hw⟩

def common {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a b : Fin n) :=
  Finset.univ.filter fun z => G.Adj a z ∧ G.Adj b z

def Rep {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (A R : Finset (Finset (Fin n))) : Prop :=
  R ⊆ A ∧ ∀ S : Finset (Fin n), S.card ≤ k →
    ∀ W ∈ A, Apart G.Adj W S → ∃ Z ∈ R, Apart G.Adj Z S

def budget (t : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => 1 + t * (budget t k + (budget t k * t) * budget t k)

-- Each context vertex blocking the seed hits one of its at most t vertices.
-- The remaining k vertices can be handled recursively. A second contact pins
-- the blocker to the unique common neighbour of two different vertices.
lemma representatives {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (t k : ℕ) (A : Finset (Finset (Fin n)))
    (hA : ∀ W ∈ A, W.card ≤ t) :
    ∃ R, Rep G k A R ∧ R.card ≤ budget t k := by
  classical
  induction k generalizing A with
  | zero =>
    by_cases h : A.Nonempty
    · obtain ⟨W, hW⟩ := h
      refine ⟨{W}, ⟨Finset.singleton_subset_iff.mpr hW, ?_⟩, by simp [budget]⟩
      intro S hS _ _ _
      have hs : S = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨W, by simp, by subst S; simp [Apart]⟩
    · exact ⟨∅, ⟨Finset.empty_subset _, fun _ _ W hW => (h ⟨W, hW⟩).elim⟩, by simp⟩
  | succ k ih =>
    by_cases h : A.Nonempty
    · obtain ⟨W₀, h₀⟩ := h
      let F (a : Fin n) := A.filter (fun W => a ∉ W)
      let H (b : Fin n) := A.filter (fun W => ∀ w ∈ W, ¬ G.Adj w b)
      have exF (a : Fin n) := ih (F a) (fun W hW => hA W (Finset.mem_filter.mp hW).1)
      have exH (b : Fin n) := ih (H b) (fun W hW => hA W (Finset.mem_filter.mp hW).1)
      choose R hR rBound using exF
      choose T hT tBound using exH
      let B (a : Fin n) := (vertices (R a)).biUnion (common G a)
      have bBound (a : Fin n) : (B a).card ≤ budget t k * t := by
        have ha (w : Fin n) (hw : w ∈ vertices (R a)) : a ≠ w := by
          obtain ⟨W, hW, hw⟩ := Finset.mem_biUnion.mp hw
          exact fun heq => (Finset.mem_filter.mp ((hR a).1 hW)).2 (heq ▸ hw)
        calc
          _ ≤ (vertices (R a)).card * 1 := union_bound _ _ _ (fun w hw => h4 a w (ha w hw))
          _ ≤ (R a).card * t := by
            rw [Nat.mul_one]
            exact vertices_bound _ _ (fun W hW => hA W (Finset.mem_filter.mp ((hR a).1 hW)).1)
          _ ≤ _ := Nat.mul_le_mul_right _ (rBound a)
      let P (a : Fin n) := R a ∪ (B a).biUnion T
      let Q := insert W₀ (W₀.biUnion P)
      refine ⟨Q, ⟨?_, ?_⟩, ?_⟩
      · intro W hW
        rcases Finset.mem_insert.mp hW with rfl | hw
        · exact h₀
        obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hw
        rcases Finset.mem_union.mp ha with hr | ht
        · exact (Finset.mem_filter.mp ((hR a).1 hr)).1
        obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp ht
        exact (Finset.mem_filter.mp ((hT b).1 hb)).1
      · intro S hS W hW hwS
        by_cases good : Apart G.Adj W₀ S
        · exact ⟨W₀, Finset.mem_insert_self .., good⟩
        simp only [Apart, not_forall, Classical.not_not] at good
        obtain ⟨a, ha, b, hb, hab⟩ := good
        have hs : (S.erase b).card ≤ k := by rw [Finset.card_erase_of_mem hb]; omega
        have hwS' : Apart G.Adj W (S.erase b) :=
          fun w hw z hz => hwS w hw z (Finset.mem_of_mem_erase hz)
        have combine (Z : Finset (Fin n)) (hZ : Z ∈ P a)
            (hz : Apart G.Adj Z (S.erase b)) (hzb : ∀ w ∈ Z, ¬ G.Adj w b) :
            ∃ X ∈ Q, Apart G.Adj X S := by
          refine ⟨Z, Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha, hZ⟩), ?_⟩
          intro w hw z hzS
          by_cases h : z = b
          · subst z; exact hzb w hw
          · exact hz w hw z (Finset.mem_erase.mpr ⟨h, hzS⟩)
        by_cases hB : b ∈ B a
        · have hwH : W ∈ H b := Finset.mem_filter.mpr ⟨hW, fun w hw => hwS w hw b hb⟩
          obtain ⟨Z, hZ, hz⟩ := (hT b).2 _ hs W hwH hwS'
          exact combine Z (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hB, hZ⟩)) hz
            (Finset.mem_filter.mp ((hT b).1 hZ)).2
        · have hwF : W ∈ F a := Finset.mem_filter.mpr ⟨hW, fun haw => hwS a haw b hb hab⟩
          obtain ⟨Z, hZ, hz⟩ := (hR a).2 _ hs W hwF hwS'
          refine combine Z (Finset.mem_union_left _ hZ) hz ?_
          intro w hw hwb
          exact hB (Finset.mem_biUnion.mpr ⟨w, subset_vertices hZ hw,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hwb⟩⟩)
      · have pBound (a : Fin n) : (P a).card ≤ budget t k + (budget t k * t) * budget t k :=
          (Finset.card_union_le ..).trans (Nat.add_le_add (rBound a)
            ((union_bound _ T _ (fun b _ => tBound b)).trans (Nat.mul_le_mul_right _ (bBound a))))
        calc
          Q.card ≤ (W₀.biUnion P).card + 1 := Finset.card_insert_le ..
          _ ≤ W₀.card * _ + 1 := Nat.add_le_add_right (union_bound _ _ _ (fun a _ => pBound a)) _
          _ ≤ t * _ + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right _ (hA W₀ h₀)) _
          _ = _ := Nat.add_comm ..
    · exact ⟨∅, ⟨Finset.empty_subset _, fun _ _ W hW => (h ⟨W, hW⟩).elim⟩, by simp⟩

-- Delete the tested edge. Its two endpoints now form an independent input.
def away {n : ℕ} (G : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) (a b : Fin n) : Prop :=
  G.Adj a b ∧ s(a, b) ≠ e

lemma away_symm {n : ℕ} {G : SimpleGraph (Fin n)} {e : Sym2 (Fin n)}
    (a b : Fin n) (h : away G e a b) : away G e b a :=
  ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩

lemma pair_apart {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    Apart (away G s(u, v)) {u, v} {u, v} := by
  intro a ha b hb h
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact G.irrefl h.1
  · exact h.2 rfl
  · exact h.2 (Sym2.eq_swap ..)
  · exact G.irrefl h.1

lemma apart_weaken {n : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    (h : Apart G.Adj A B) (e : Sym2 (Fin n)) : Apart (away G e) A B :=
  fun x hx y hy hxy => h x hx y hy hxy.1

def doubleNbr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Finset (Fin n)) :=
  D.biUnion fun a => D.biUnion fun b => if a = b then ∅ else common G a b

def charge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Finset (Fin n)) :=
  (D ×ˢ (D ∪ doubleNbr G D)).image fun p => s(p.1, p.2)

lemma charge_mem {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {D : Finset (Fin n)}
    {a b : Fin n} (ha : a ∈ D) (hb : b ∈ D ∪ doubleNbr G D) : s(a, b) ∈ charge G D :=
  Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

lemma charge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (D : Finset (Fin n)) (d : ℕ) (hD : D.card ≤ d) : (charge G D).card ≤ d * (d + d * d) := by
  have hDouble : (doubleNbr G D).card ≤ d * d := by
    refine (union_bound D _ d ?_).trans (Nat.mul_le_mul_right _ hD)
    intro a _
    refine (union_bound D _ 1 ?_).trans (by simpa using hD)
    intro b _
    split_ifs with h
    · simp
    · exact h4 a b h
  calc
    _ ≤ (D ×ˢ (D ∪ doubleNbr G D)).card := Finset.card_image_le
    _ = D.card * (D ∪ doubleNbr G D).card := Finset.card_product ..
    _ ≤ _ := Nat.mul_le_mul hD ((Finset.card_union_le ..).trans (Nat.add_le_add hD hDouble))

lemma recover_independent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {D W : Finset (Fin n)} {e : Sym2 (Fin n)} (he : e ∉ charge G D) (hw : W ⊆ D)
    (h : Apart (away G e) W W) : Apart G.Adj W W := by
  intro a ha b hb hab
  apply h a ha b hb
  exact ⟨hab, fun eq => he (eq ▸ charge_mem (hw ha) (Finset.mem_union_left _ (hw hb)))⟩

-- An outer context vertex with a unique contact in D can simply be
-- omitted when that contact is deleted. Two contacts put it in doubleNbr.
lemma transfer_rep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {D : Finset (Fin n)} {e : Sym2 (Fin n)} (he : e ∉ charge G D)
    {A R : Finset (Finset (Fin n))} {k : ℕ} (hr : Rep G k A R)
    (hD : ∀ W ∈ A, W ⊆ D) {S : Finset (Fin n)} (hs : S.card ≤ k)
    {W : Finset (Fin n)} (hw : W ∈ A) (h : Apart (away G e) W S) :
    ∃ Z ∈ R, Apart (away G e) Z S := by
  classical
  let T := S.filter (fun b => ¬ ∃ a ∈ D, G.Adj a b ∧ s(a, b) = e)
  have hT : Apart G.Adj W T := by
    intro a ha b hb hab
    obtain ⟨hbs, hn⟩ := Finset.mem_filter.mp hb
    exact h a ha b hbs ⟨hab, fun eq => hn ⟨a, hD W hw ha, hab, eq⟩⟩
  obtain ⟨Z, hZ, hz⟩ := hr.2 T ((Finset.card_filter_le ..).trans hs) W hw hT
  refine ⟨Z, hZ, ?_⟩
  intro z hzin b hb hzb
  by_cases hbt : b ∈ T
  · exact hz z hzin b hbt hzb.1
  have hh : ∃ a ∈ D, G.Adj a b ∧ s(a, b) = e := by
    by_contra hn
    exact hbt (Finset.mem_filter.mpr ⟨hb, hn⟩)
  obtain ⟨a, ha, hab, eq⟩ := hh
  have hne : a ≠ z := fun az => hzb.2 (az ▸ eq)
  have hzD := hD Z (hr.1 hZ) hzin
  have hbD : b ∈ doubleNbr G D := by
    refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_biUnion.mpr ⟨z, hzD, ?_⟩⟩
    rw [ite_eq_right hne]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hzb.1⟩
  exact he (eq ▸ charge_mem ha (Finset.mem_union_right _ hbD))

-- The rank counts possible AND layers. A top has rank two and only junk
-- AND gates can occur lower down. A junk gate has no AND gate below it.
def seen (n : ℕ) (C : Circuit) (J : Finset ℕ) (w : ℕ) : Prop :=
  ∃ i ∈ J, ∃ j, w = n + j ∧ (i = j ∨ InCone n C i j)

noncomputable def rank {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (w : ℕ) : ℕ := by
  classical
  exact if seen n C (tops G C) w then 2 else if seen n C (junk G C) w then 1 else 0

lemma rank_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) :
    rank G C w ≤ 2 := by
  unfold rank
  split_ifs <;> decide

lemma seen_operand {n : ℕ} {C : Circuit} {J : Finset ℕ} {j w : ℕ} (hj : j < C.gates.length)
    (hin : w ∈ (gateAt C j).inputs) (hlt : w < n + j) (hs : seen n C J w) :
    ∃ i ∈ J, InCone n C i j := by
  obtain ⟨i, hi, k, rfl, hk⟩ := hs
  exact ⟨i, hi, (inCone_iff ..).mpr ⟨hj, k, by omega, hin, hk⟩⟩

lemma rank_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    {j w : ℕ} (hj : j < C.gates.length) (hin : w ∈ (gateAt C j).inputs) (hlt : w < n + j) :
    rank G C w ≤ rank G C (n + j) := by
  have propagate (J : Finset ℕ) (hs : seen n C J w) : seen n C J (n + j) := by
    obtain ⟨i, hi, h⟩ := seen_operand hj hin hlt hs
    exact ⟨i, hi, j, rfl, Or.inr h⟩
  unfold rank
  split_ifs <;> first | decide | solve_by_elim

lemma rank_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hT : TopForm G C)
    (hJ : ∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬ InCone n C i j)
    {j w : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hin : w ∈ (gateAt C j).inputs) (hlt : w < n + j) :
    rank G C w < rank G C (n + j) := by
  classical
  let _ : DecidableEq GateOp := gateOpDecEq
  have hnt : ¬ seen n C (tops G C) w := by
    intro hs
    obtain ⟨i, hi, hc⟩ := seen_operand hj hin hlt hs
    obtain ⟨hi, hand, hbel⟩ := Finset.mem_filter.mp hi
    exact hT i (Finset.mem_range.mp hi) j hj hand hbel hop hc
  by_cases clean : BelowF G C j
  · have hjt : j ∈ tops G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop, clean⟩
    have hs : seen n C (tops G C) (n + j) := ⟨j, hjt, j, rfl, Or.inl rfl⟩
    simp only [rank, ite_eq_right hnt, ite_eq_left hs]
    split_ifs <;> decide
  · have hd : IsDirty n G C j := by
      unfold BelowF at clean
      push Not at clean
      obtain ⟨x, hx, hf⟩ := clean
      exact ⟨hj, x, hx, by simpa using hf⟩
    have hjj : j ∈ junk G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop, hd⟩
    have hs : seen n C (junk G C) (n + j) := ⟨j, hjj, j, rfl, Or.inl rfl⟩
    have hnj : ¬ seen n C (junk G C) w := by
      intro h
      obtain ⟨i, hi, hc⟩ := seen_operand hj hin hlt h
      exact hJ i hi j hjj hc
    simp only [rank, ite_eq_right hnt, ite_eq_right hnj, ite_eq_left hs]
    split_ifs <;> decide

def fires {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Prop :=
  val C (List.ofFn x) w = true

lemma fires_input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    fires C i x ↔ x i = true := by
  unfold fires
  rw [val_input (n := n) (by simp) i.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma fires_gate {n : ℕ} (C : Circuit) {j p q : ℕ} (hj : j < C.gates.length)
    (hin : (gateAt C j).inputs = [p, q]) (hp : p < n + j) (hq : q < n + j)
    (x : Fin n → Bool) :
    ((gateAt C j).op = GateOp.and → (fires C (n + j) x ↔ fires C p x ∧ fires C q x)) ∧
    ((gateAt C j).op = GateOp.or → (fires C (n + j) x ↔ fires C p x ∨ fires C q x)) := by
  unfold fires
  rw [val_gate (n := n) (by simp) hj, hin]
  constructor <;> intro hop <;> simp [hop, hp, hq, GateOp.eval]

def repLimit := budget 4 8

def gateBound :=
  let d := 8 * repLimit
  d * (d + d * d)

def Forces {n : ℕ} (C : Circuit) (w : ℕ) (W : Finset (Fin n)) : Prop :=
  ∀ x : Fin n → Bool, (∀ v ∈ W, x v = true) → fires C w x

def Facts {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (w d : ℕ)
    (R : Finset (Finset (Fin n))) : Prop :=
  ∀ W ∈ R, W.card ≤ 2 ^ d ∧ Apart G.Adj W W ∧ Forces C w W

-- A wire of rank d leaves room for four extra context vertices at each
-- lower AND layer. The graph in this invariant has the tested edge removed.
def Catches {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (w d : ℕ)
    (B : Finset (Sym2 (Fin n))) (R : Finset (Finset (Fin n))) : Prop :=
  ∀ u v : Fin n, s(u, v) ∉ B → fires C w (pairInput u v) →
    ∀ S : Finset (Fin n), S.card + 4 * d ≤ 8 → Apart (away G s(u, v)) {u, v} S →
      ∃ W ∈ R, Apart (away G s(u, v)) W S

def Summary {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (w d : ℕ)
    (B : Finset (Sym2 (Fin n))) (R : Finset (Finset (Fin n))) : Prop :=
  R.card ≤ repLimit ∧ Facts G C w d R ∧ Catches G C w d B R

lemma small_power {d : ℕ} (hd : d ≤ 2) : 2 ^ d ≤ 4 := Nat.pow_le_pow_right (by decide) hd

lemma summary_mono {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {w d : ℕ}
    {B B' : Finset (Sym2 (Fin n))} {R : Finset (Finset (Fin n))}
    (h : Summary G C w d B R) (hsub : B ⊆ B') : Summary G C w d B' R :=
  ⟨h.1, h.2.1, fun u v he => h.2.2 u v (fun hin => he (hsub hin))⟩

lemma input_summary {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (i : Fin n)
    (d : ℕ) (B : Finset (Sym2 (Fin n))) : Summary G C i d B {{i}} := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_singleton]
    change 1 ≤ 1 + _
    omega
  · intro W hW
    obtain rfl := Finset.mem_singleton.mp hW
    refine ⟨by simpa using (Nat.one_le_pow d 2 (by decide)), ?_, ?_⟩
    · intro a ha b hb
      obtain rfl := Finset.mem_singleton.mp ha
      obtain rfl := Finset.mem_singleton.mp hb
      exact G.irrefl
    · intro x hx
      exact (fires_input ..).mpr (hx _ (Finset.mem_singleton_self _))
  · intro u v _ hx S _ hS
    obtain hu | hv := (pairInput_true ..).mp ((fires_input ..).mp hx)
    · exact ⟨{i}, by simp, fun a ha => hS a (by simp [Finset.mem_singleton.mp ha, hu])⟩
    · exact ⟨{i}, by simp, fun a ha => hS a (by simp [Finset.mem_singleton.mp ha, hv])⟩

lemma compress {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {w d : ℕ} (hd : d ≤ 2) {D : Finset (Fin n)} {A : Finset (Finset (Fin n))}
    {B : Finset (Sym2 (Fin n))} (hD : ∀ W ∈ A, W ⊆ D) (hc : charge G D ⊆ B)
    (hf : Facts G C w d A) (ht : Catches G C w d B A) :
    ∃ R, Summary G C w d B R := by
  obtain ⟨R, hr, hb⟩ := representatives G h4 4 8 A (fun W hW => (hf W hW).1.trans (small_power hd))
  refine ⟨R, hb, fun W hW => hf W (hr.1 hW), ?_⟩
  intro u v he hfire S hs hS
  obtain ⟨W, hW, hwS⟩ := ht u v he hfire S hs hS
  exact transfer_rep G (fun h => he (hc h)) hr hD (by omega) hW hwS

lemma or_summary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q w dp dq d : ℕ} (hd : d ≤ 2) (hp : dp ≤ d) (hq : dq ≤ d)
    (sem : ∀ x : Fin n → Bool, fires C w x ↔ fires C p x ∨ fires C q x)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    (hP : Summary G C p dp B P) (hQ : Summary G C q dq B Q) :
    ∃ R, Summary G C w d (B ∪ charge G (vertices P ∪ vertices Q)) R := by
  let D := vertices P ∪ vertices Q
  apply compress G h4 C hd (D := D) (A := P ∪ Q) _ (Finset.subset_union_right)
  · intro W hW
    rcases Finset.mem_union.mp hW with h | h
    · obtain ⟨hw, hi, hf⟩ := hP.2.1 W h
      exact ⟨hw.trans (Nat.pow_le_pow_right (by decide) hp), hi,
        fun x hx => (sem x).mpr (Or.inl (hf x hx))⟩
    · obtain ⟨hw, hi, hf⟩ := hQ.2.1 W h
      exact ⟨hw.trans (Nat.pow_le_pow_right (by decide) hq), hi,
        fun x hx => (sem x).mpr (Or.inr (hf x hx))⟩
  · intro u v he hx S hs hS
    have he' : s(u, v) ∉ B := fun h => he (Finset.mem_union_left _ h)
    rcases (sem _).mp hx with h | h
    · obtain ⟨W, hw, ha⟩ := hP.2.2 u v he' h S (by omega) hS
      exact ⟨W, Finset.mem_union_left _ hw, ha⟩
    · obtain ⟨W, hw, ha⟩ := hQ.2.2 u v he' h S (by omega) hS
      exact ⟨W, Finset.mem_union_right _ hw, ha⟩
  · intro W hW
    rcases Finset.mem_union.mp hW with h | h
    · exact (subset_vertices h).trans Finset.subset_union_left
    · exact (subset_vertices h).trans Finset.subset_union_right

lemma add_powers {a b d : ℕ} (ha : a < d) (hb : b < d) : 2 ^ a + 2 ^ b ≤ 2 ^ d := by
  cases d with
  | zero => omega
  | succ k =>
    rw [pow_succ, Nat.mul_two]
    exact Nat.add_le_add (Nat.pow_le_pow_right (by decide) (by omega))
      (Nat.pow_le_pow_right (by decide) (by omega))

lemma and_summary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q w dp dq d : ℕ} (hd : d ≤ 2) (hp : dp < d) (hq : dq < d)
    (sem : ∀ x : Fin n → Bool, fires C w x ↔ fires C p x ∧ fires C q x)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    (hP : Summary G C p dp B P) (hQ : Summary G C q dq B Q) :
    ∃ R, Summary G C w d (B ∪ charge G (vertices P ∪ vertices Q)) R := by
  classical
  let D := vertices P ∪ vertices Q
  let raw := P.biUnion fun U => Q.image (fun V => U ∪ V)
  let A := raw.filter (fun W => Apart G.Adj W W)
  have memRaw (W : Finset (Fin n)) : W ∈ raw ↔ ∃ U ∈ P, ∃ V ∈ Q, U ∪ V = W := by
    simp only [raw, Finset.mem_biUnion, Finset.mem_image]
  have inD (U V : Finset (Fin n)) (hu : U ∈ P) (hv : V ∈ Q) : U ∪ V ⊆ D :=
    Finset.union_subset_union (subset_vertices hu) (subset_vertices hv)
  have subD (W : Finset (Fin n)) (hw : W ∈ A) : W ⊆ D := by
    obtain ⟨U, hu, V, hv, rfl⟩ := (memRaw W).mp (Finset.mem_filter.mp hw).1
    exact inD U V hu hv
  apply compress G h4 C hd subD Finset.subset_union_right
  · intro W hW
    obtain ⟨hw, hi⟩ := Finset.mem_filter.mp hW
    obtain ⟨U, hu, V, hv, rfl⟩ := (memRaw W).mp hw
    obtain ⟨hsU, _, hfU⟩ := hP.2.1 U hu
    obtain ⟨hsV, _, hfV⟩ := hQ.2.1 V hv
    refine ⟨(Finset.card_union_le ..).trans ((Nat.add_le_add hsU hsV).trans (add_powers hp hq)),
      hi, ?_⟩
    intro x hx
    exact (sem x).mpr ⟨hfU x (fun z hz => hx z (Finset.mem_union_left _ hz)),
      hfV x (fun z hz => hx z (Finset.mem_union_right _ hz))⟩
  · intro u v he hx S hs hS
    let e := s(u, v)
    let E := away G e
    have heB : e ∉ B := fun h => he (Finset.mem_union_left _ h)
    have heD : e ∉ charge G D := fun h => he (Finset.mem_union_right _ h)
    obtain ⟨hpf, hqf⟩ := (sem _).mp hx
    have hpairs : ({u, v} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    have hs₁ : (S ∪ {u, v}).card + 4 * dp ≤ 8 := by
      have hh := Finset.card_union_le S {u, v}
      omega
    obtain ⟨U, hu, huC⟩ := hP.2.2 u v heB hpf (S ∪ {u, v}) hs₁
      (apart_union_right.mpr ⟨hS, pair_apart G u v⟩)
    obtain ⟨huS, huPair⟩ := apart_union_right.mp huC
    have hpairU := apart_symm (away_symm (G := G) (e := e)) huPair
    obtain ⟨hsU, hiU, _⟩ := hP.2.1 U hu
    have hs₁' := hsU.trans (small_power (by omega))
    have hs₂ : (S ∪ U).card + 4 * dq ≤ 8 := by
      have hh := Finset.card_union_le S U
      omega
    obtain ⟨V, hv, hvC⟩ := hQ.2.2 u v heB hqf (S ∪ U) hs₂
      (apart_union_right.mpr ⟨hS, hpairU⟩)
    obtain ⟨hvS, hvU⟩ := apart_union_right.mp hvC
    have huV := apart_symm (away_symm (G := G) (e := e)) hvU
    have hiV := (hQ.2.1 V hv).2.1
    have hi : Apart E (U ∪ V) (U ∪ V) :=
      apart_union_left.mpr ⟨apart_union_right.mpr ⟨apart_weaken hiU e, huV⟩,
        apart_union_right.mpr ⟨hvU, apart_weaken hiV e⟩⟩
    refine ⟨U ∪ V, Finset.mem_filter.mpr ⟨(memRaw _).mpr ⟨U, hu, V, hv, rfl⟩, ?_⟩,
      apart_union_left.mpr ⟨huS, hvS⟩⟩
    exact recover_independent G heD (inD U V hu hv) hi

lemma stage_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) {p q dp dq : ℕ} (hp : dp ≤ 2) (hq : dq ≤ 2)
    {B : Finset (Sym2 (Fin n))} {P Q : Finset (Finset (Fin n))}
    (hP : Summary G C p dp B P) (hQ : Summary G C q dq B Q) :
    (charge G (vertices P ∪ vertices Q)).card ≤ gateBound := by
  apply charge_bound G h4 _ (8 * repLimit)
  have sizeP := (vertices_bound P 4 (fun W hW => (hP.2.1 W hW).1.trans (small_power hp))).trans
    (Nat.mul_le_mul_right _ hP.1)
  have sizeQ := (vertices_bound Q 4 (fun W hW => (hQ.2.1 W hW).1.trans (small_power hq))).trans
    (Nat.mul_le_mul_right _ hQ.1)
  have h := Finset.card_union_le (vertices P) (vertices Q)
  omega

-- Go through the gates in order, retaining one common set of charged edges.
lemma prefix_summaries {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hJ : ∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬ InCone n C i j)
    (k : ℕ) (hk : k ≤ C.gates.length) :
    ∃ B : Finset (Sym2 (Fin n)), B.card ≤ k * gateBound ∧
      ∀ w < n + k, ∃ R, Summary G C w (rank G C w) B R := by
  induction k with
  | zero =>
    refine ⟨∅, by simp, ?_⟩
    intro w hw
    let i : Fin n := ⟨w, by omega⟩
    exact ⟨_, input_summary G C i _ _⟩
  | succ j ih =>
    have hj : j < C.gates.length := by omega
    obtain ⟨B, hB, prev⟩ := ih (by omega)
    have hmem := gateAt_mem hj
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ hmem)
    have hpin : p ∈ (gateAt C j).inputs := by simp [hin]
    have hqin : q ∈ (gateAt C j).inputs := by simp [hin]
    have hp := hAO.2.1 j hj p hpin
    have hq := hAO.2.1 j hj q hqin
    obtain ⟨P, hP⟩ := prev p hp
    obtain ⟨Q, hQ⟩ := prev q hq
    let B' := B ∪ charge G (vertices P ∪ vertices Q)
    have step : ∃ R, Summary G C (n + j) (rank G C (n + j)) B' R := by
      have sem := fires_gate C hj hin hp hq
      rcases hAO.1 _ hmem with ha | ho
      · exact and_summary G h4 C (rank_le ..) (rank_and G C hT hJ hj ha hpin hp)
          (rank_and G C hT hJ hj ha hqin hq) (fun x => (sem x).1 ha) hP hQ
      · exact or_summary G h4 C (rank_le ..) (rank_operand G C hj hpin hp)
          (rank_operand G C hj hqin hq) (fun x => (sem x).2 ho) hP hQ
    refine ⟨B', ?_, ?_⟩
    · rw [Nat.succ_mul]
      exact (Finset.card_union_le ..).trans
        (Nat.add_le_add hB (stage_cost G h4 C (rank_le ..) (rank_le ..) hP hQ))
    · intro w hw
      by_cases hold : w < n + j
      · obtain ⟨R, hr⟩ := prev w hold
        exact ⟨R, summary_mono hr Finset.subset_union_left⟩
      · have he : w = n + j := by omega
        exact he ▸ step

-- At the output an uncharged edge would produce an independent certificate
-- forcing the graph function. Turning on just those vertices contradicts it.
lemma edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hT : TopForm G C) (hJ : ∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬ InCone n C i j) :
    G.edgeFinset.card ≤ C.size * gateBound := by
  obtain ⟨B, hB, hAll⟩ := prefix_summaries G h4 C hAO hT hJ C.gates.length le_rfl
  refine (Finset.card_le_card (show G.edgeFinset ⊆ B from ?_)).trans hB
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    intro he
    by_contra hu
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
    have equiv (x : Fin n → Bool) : fires C C.output x ↔ graphFun G ∅ x = true := by
      change PEqualNP.MetaComplexity.circuitFun n C x = true ↔ _
      rw [hfun]
    have hfire := (equiv _).mpr ((graphFun_pair G u v).mpr hadj)
    have hlen : C.output < n + C.gates.length := by
      by_contra! h
      have hf := val_ge (C := C) (x := List.ofFn (pairInput u v)) (by simp) h
      exact Bool.noConfusion (hf.symm.trans hfire)
    obtain ⟨R, hr⟩ := hAll C.output hlen
    have hd := rank_le G C C.output
    obtain ⟨W, hW, _⟩ := hr.2.2 u v hu hfire ∅ (by simp; omega) (by simp [Apart])
    obtain ⟨_, hi, force⟩ := hr.2.1 W hW
    let x (i : Fin n) := decide (i ∈ W)
    have yes := (equiv x).mp (force x (by simp [x]))
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, x] at yes
    obtain ⟨a, b, hab, ha, hb⟩ := yes
    exact hi a ha b hb hab

end Parallel



open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

/-- The posted bound holds uniformly when there are at most two junk gates. -/
lemma at_most_two_bound : ∃ c : ℕ, ∀ n (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit),
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    IsLeastAO G C → TopForm G C → (junk G C).card ≤ 2 →
    (Ustar G C).card ≤ c * (C.size + 1) := by
  refine ⟨max 4 Parallel.gateBound, ?_⟩
  intro n G _ C hg hL hTop hjCard
  classical
  by_cases hnested : ∃ g ∈ junk G C, ∃ h ∈ junk G C, InCone n C g h
  · have hTwo : (junk G C).card = 2 := by
      obtain ⟨g, hgJ, h, hhJ, hcone⟩ := hnested
      have hne : g ≠ h := Nat.ne_of_lt (TwoJunk.Structural.inCone_lt hcone)
      have hsub : ({g, h} : Finset ℕ) ⊆ junk G C := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hgJ
        · exact hhJ
      have hlo := Finset.card_le_card hsub
      have hpair : ({g,h} : Finset ℕ).card = 2 := by simp [hne]
      omega
    exact (nested_two_bound G C hg hL hTop hTwo hnested).trans
      (Nat.mul_le_mul_right _ (Nat.le_max_left 4 Parallel.gateBound))
  · have hJ : ∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬ InCone n C i j := by
      intro i hi j hj hc
      exact hnested ⟨i, hi, j, hj, hc⟩
    have h4 : NoFourCycle G := by
      intro a b hab
      by_contra! h
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
      obtain ⟨_, hau, hbu⟩ := Finset.mem_filter.mp hu
      obtain ⟨_, hav, hbv⟩ := Finset.mem_filter.mp hv
      exact Parallel.no4 G hg a u b v hau hbu.symm hbv hav.symm hab huv
    calc
      (Ustar G C).card ≤ G.edgeFinset.card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ C.size * Parallel.gateBound := Parallel.edge_bound G h4 C hL.1 hL.2.1 hTop hJ
      _ ≤ Parallel.gateBound * (C.size + 1) := by
        rw [Nat.mul_comm C.size]
        exact Nat.mul_le_mul_left _ (by omega)
      _ ≤ max 4 Parallel.gateBound * (C.size + 1) :=
        Nat.mul_le_mul_right _ (Nat.le_max_right 4 Parallel.gateBound)

end PEqualNP.Outside.L_meta_1735_aux
