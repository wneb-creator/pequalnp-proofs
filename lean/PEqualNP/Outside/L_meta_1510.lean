import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1510
open PEqualNP.CircuitLowerBounds

theorem getD_app_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def dg (n : ℕ) (M : Finset ℕ) (G : List Gate) (x : ℕ) : ℕ :=
  ((Circuit.mk G 0).lineDegrees n M).getD x 0

def vl (n : ℕ) (G : List Gate) (z : Fin n → Bool) (x : ℕ) : Bool :=
  ((Circuit.mk G 0).wires (List.ofFn z)).getD x false

theorem ld_snoc (n : ℕ) (M : Finset ℕ) (G : List Gate) (g : Gate) :
    (Circuit.mk (G ++ [g]) 0).lineDegrees n M
      = (Circuit.mk G 0).lineDegrees n M ++ [g.lineDegree ((Circuit.mk G 0).lineDegrees n M)] := by
  simp [Circuit.lineDegrees, List.foldl_append]

theorem ld_len (n : ℕ) (M : Finset ℕ) (G : List Gate) :
    ((Circuit.mk G 0).lineDegrees n M).length = n + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [Circuit.lineDegrees]
  | append_singleton G g ih => rw [ld_snoc]; simp [ih]; omega

theorem wr_snoc (G : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.mk (G ++ [g]) 0).wires x
      = (Circuit.mk G 0).wires x ++ [g.op.eval (g.inputs.map fun i => ((Circuit.mk G 0).wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wr_len (n : ℕ) (G : List Gate) (z : Fin n → Bool) :
    ((Circuit.mk G 0).wires (List.ofFn z)).length = n + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton G g ih => rw [wr_snoc]; simp [ih]; omega

theorem dg_snoc_lt (n : ℕ) (M : Finset ℕ) (G : List Gate) (g : Gate) (x : ℕ) (h : x < n + G.length) :
    dg n M (G ++ [g]) x = dg n M G x := by
  unfold dg; rw [ld_snoc]; exact getD_app_lt _ _ _ _ (by rw [ld_len]; exact h)

theorem vl_snoc_lt (n : ℕ) (G : List Gate) (g : Gate) (z : Fin n → Bool) (x : ℕ) (h : x < n + G.length) :
    vl n (G ++ [g]) z x = vl n G z x := by
  unfold vl; rw [wr_snoc]; exact getD_app_lt _ _ _ _ (by rw [wr_len]; exact h)

theorem dg_app_lt (n : ℕ) (M : Finset ℕ) (G H : List Gate) (x : ℕ) (h : x < n + G.length) :
    dg n M (G ++ H) x = dg n M G x := by
  induction H using List.reverseRecOn with
  | nil => simp
  | append_singleton H g ih =>
    rw [← List.append_assoc, dg_snoc_lt _ _ _ _ _ (by simp; omega), ih]

theorem vl_app_lt (n : ℕ) (G H : List Gate) (z : Fin n → Bool) (x : ℕ) (h : x < n + G.length) :
    vl n (G ++ H) z x = vl n G z x := by
  induction H using List.reverseRecOn with
  | nil => simp
  | append_singleton H g ih =>
    rw [← List.append_assoc, vl_snoc_lt _ _ _ _ _ (by simp; omega), ih]

theorem dg_ge (n : ℕ) (M : Finset ℕ) (G : List Gate) (x : ℕ) (h : n + G.length ≤ x) :
    dg n M G x = 0 := by
  unfold dg; exact getD_ge _ _ _ (by rw [ld_len]; exact h)

theorem vl_ge (n : ℕ) (G : List Gate) (z : Fin n → Bool) (x : ℕ) (h : n + G.length ≤ x) :
    vl n G z x = false := by
  unfold vl; exact getD_ge _ _ _ (by rw [wr_len]; exact h)

theorem dg_new (n : ℕ) (M : Finset ℕ) (G : List Gate) (g : Gate) :
    dg n M (G ++ [g]) (n + G.length) = g.lineDegree ((Circuit.mk G 0).lineDegrees n M) := by
  unfold dg; rw [ld_snoc]
  have h := ld_len n M G
  rw [← h]; exact getD_app_len _ _ _

theorem vl_new (n : ℕ) (G : List Gate) (g : Gate) (z : Fin n → Bool) :
    vl n (G ++ [g]) z (n + G.length)
      = g.op.eval (g.inputs.map fun i => ((Circuit.mk G 0).wires (List.ofFn z)).getD i false) := by
  unfold vl; rw [wr_snoc]
  have h := wr_len n G z
  rw [← h]; exact getD_app_len _ _ _


theorem ev_and1 (p : Bool) : GateOp.and.eval [p] = p := by simp [GateOp.eval]
theorem ev_and2 (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by simp [GateOp.eval]
theorem ev_or1 (p : Bool) : GateOp.or.eval [p] = p := by simp [GateOp.eval]
theorem ev_or2 (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by simp [GateOp.eval]

theorem ld_and0 (D : List ℕ) : (Gate.mk GateOp.and []).lineDegree D = 0 := by
  simp [Gate.lineDegree]
theorem ld_and1 (D : List ℕ) (a : ℕ) : (Gate.mk GateOp.and [a]).lineDegree D = D.getD a 0 := by
  simp [Gate.lineDegree]
theorem ld_and2 (D : List ℕ) (a c : ℕ) :
    (Gate.mk GateOp.and [a, c]).lineDegree D = D.getD a 0 + D.getD c 0 := by
  simp [Gate.lineDegree]
theorem ld_or0 (D : List ℕ) : (Gate.mk GateOp.or []).lineDegree D = 0 := by
  simp [Gate.lineDegree]
theorem ld_or1 (D : List ℕ) (a : ℕ) : (Gate.mk GateOp.or [a]).lineDegree D = D.getD a 0 := by
  simp [Gate.lineDegree]
theorem ld_or2 (D : List ℕ) (a c : ℕ) :
    (Gate.mk GateOp.or [a, c]).lineDegree D = max (D.getD a 0) (D.getD c 0) := by
  simp [Gate.lineDegree]

theorem ld_congr (g : Gate) (D D' : List ℕ) (h : ∀ i ∈ g.inputs, D.getD i 0 = D'.getD i 0) :
    g.lineDegree D = g.lineDegree D' := by
  unfold Gate.lineDegree
  rw [List.map_congr_left h]

theorem vl_mid (n : ℕ) (B H1 : List Gate) (g : Gate) (H2 : List Gate) (z : Fin n → Bool) (j : ℕ)
    (hj : j = n + B.length + H1.length) :
    vl n (B ++ (H1 ++ g :: H2)) z j
      = g.op.eval (g.inputs.map fun i => vl n (B ++ H1) z i) := by
  have e : B ++ (H1 ++ g :: H2) = (B ++ H1 ++ [g]) ++ H2 := by simp
  rw [e, vl_app_lt _ _ _ _ _ (by simp; omega)]
  have h := vl_new n (B ++ H1) g z
  have e2 : n + (B ++ H1).length = j := by simp; omega
  rw [e2] at h
  exact h

theorem dg_mid (n : ℕ) (M : Finset ℕ) (B H1 : List Gate) (g : Gate) (H2 : List Gate) (j : ℕ)
    (hj : j = n + B.length + H1.length) :
    dg n M (B ++ (H1 ++ g :: H2)) j
      = g.lineDegree ((Circuit.mk (B ++ H1) 0).lineDegrees n M) := by
  have e : B ++ (H1 ++ g :: H2) = (B ++ H1 ++ [g]) ++ H2 := by simp
  rw [e, dg_app_lt _ _ _ _ _ (by simp; omega)]
  have h := dg_new n M (B ++ H1) g
  have e2 : n + (B ++ H1).length = j := by simp; omega
  rw [e2] at h
  exact h

theorem vl_mid_old (n : ℕ) (B H1 : List Gate) (g : Gate) (H2 : List Gate) (z : Fin n → Bool) (j : ℕ)
    (hj : j = n + B.length + H1.length) (hin : ∀ i ∈ g.inputs, i < n + B.length) :
    vl n (B ++ (H1 ++ g :: H2)) z j
      = g.op.eval (g.inputs.map fun i => vl n B z i) := by
  rw [vl_mid n B H1 g H2 z j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact vl_app_lt _ _ _ _ _ (hin i hi)

theorem dg_mid_old (n : ℕ) (M : Finset ℕ) (B H1 : List Gate) (g : Gate) (H2 : List Gate) (j : ℕ)
    (hj : j = n + B.length + H1.length) (hin : ∀ i ∈ g.inputs, i < n + B.length) :
    dg n M (B ++ (H1 ++ g :: H2)) j
      = g.lineDegree ((Circuit.mk B 0).lineDegrees n M) := by
  rw [dg_mid n M B H1 g H2 j hj]
  apply ld_congr
  intro i hi
  exact dg_app_lt n M B H1 i (hin i hi)

theorem vl_mid_and (n : ℕ) (B H1 : List Gate) (a c : ℕ) (H2 : List Gate) (z : Fin n → Bool) (j : ℕ)
    (hj : j = n + B.length + H1.length) (ha : a < n + B.length) (hc : c < n + B.length) :
    vl n (B ++ (H1 ++ Gate.mk GateOp.and [a, c] :: H2)) z j = (vl n B z a && vl n B z c) := by
  rw [vl_mid_old n B H1 _ H2 z j hj (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)]
  exact ev_and2 _ _

theorem vl_mid_or (n : ℕ) (B H1 : List Gate) (a c : ℕ) (H2 : List Gate) (z : Fin n → Bool) (j : ℕ)
    (hj : j = n + B.length + H1.length) :
    vl n (B ++ (H1 ++ Gate.mk GateOp.or [a, c] :: H2)) z j
      = (vl n (B ++ H1) z a || vl n (B ++ H1) z c) := by
  rw [vl_mid n B H1 _ H2 z j hj]
  exact ev_or2 _ _

theorem dg_mid_and (n : ℕ) (M : Finset ℕ) (B H1 : List Gate) (a c : ℕ) (H2 : List Gate) (j : ℕ)
    (hj : j = n + B.length + H1.length) (ha : a < n + B.length) (hc : c < n + B.length) :
    dg n M (B ++ (H1 ++ Gate.mk GateOp.and [a, c] :: H2)) j = dg n M B a + dg n M B c := by
  rw [dg_mid_old n M B H1 _ H2 j hj (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)]
  exact ld_and2 _ _ _

theorem dg_mid_or (n : ℕ) (M : Finset ℕ) (B H1 : List Gate) (a c : ℕ) (H2 : List Gate) (j : ℕ)
    (hj : j = n + B.length + H1.length) :
    dg n M (B ++ (H1 ++ Gate.mk GateOp.or [a, c] :: H2)) j
      = max (dg n M (B ++ H1) a) (dg n M (B ++ H1) c) := by
  rw [dg_mid n M B H1 _ H2 j hj]
  exact ld_or2 _ _ _

def ablk (b a0 a1 a2 c0 c1 c2 : ℕ) : List Gate := [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0], Gate.mk GateOp.or [b + 4, b + 5], Gate.mk GateOp.or [b + 7, b + 6]]

def sblk (g0 g1 g2 : Gate) : List Gate :=
  [g0, Gate.mk GateOp.or [], Gate.mk GateOp.or [], g1, Gate.mk GateOp.or [], Gate.mk GateOp.or [], Gate.mk GateOp.or [], Gate.mk GateOp.or [], g2]

def sl (d : ℕ) : ℕ := if d = 0 then 0 else if d = 1 then 3 else 8

theorem and_blk_vl (n : ℕ) (B : List Gate) (z : Fin n → Bool) (b a0 a1 a2 c0 c1 c2 : ℕ)
    (hb : b = n + B.length)
    (ha0 : a0 < n + B.length) (ha1 : a1 < n + B.length) (ha2 : a2 < n + B.length)
    (hc0 : c0 < n + B.length) (hc1 : c1 < n + B.length) (hc2 : c2 < n + B.length) :
    vl n (B ++ ablk b a0 a1 a2 c0 c1 c2) z b = (vl n B z a0 && vl n B z c0) ∧
    vl n (B ++ ablk b a0 a1 a2 c0 c1 c2) z (b + 3)
      = ((vl n B z a0 && vl n B z c1) || (vl n B z a1 && vl n B z c0)) ∧
    vl n (B ++ ablk b a0 a1 a2 c0 c1 c2) z (b + 8)
      = (((vl n B z a0 && vl n B z c2) || (vl n B z a1 && vl n B z c1)) || (vl n B z a2 && vl n B z c0)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact vl_mid_and n B [] a0 c0 _ z b (by subst hb; simp) ha0 hc0
  · have e1 : vl n (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0]]) z (b + 1) = (vl n B z a0 && vl n B z c1) :=
      vl_mid_and n B [Gate.mk GateOp.and [a0, c0]] a0 c1 _ z (b + 1) (by subst hb; simp) ha0 hc1
    have e2 : vl n (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0]]) z (b + 2) = (vl n B z a1 && vl n B z c0) :=
      vl_mid_and n B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1]] a1 c0 _ z (b + 2) (by subst hb; simp) ha1 hc0
    have e3 : vl n (B ++ ablk b a0 a1 a2 c0 c1 c2) z (b + 3)
        = (vl n (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0]]) z (b + 1) || vl n (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0]]) z (b + 2)) :=
      vl_mid_or n B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0]] (b + 1) (b + 2) _ z (b + 3) (by subst hb; simp)
    rw [e1, e2] at e3
    exact e3
  · have e4 : vl n (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0]]) z (b + 4) = (vl n B z a0 && vl n B z c2) :=
      vl_mid_and n B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2]] a0 c2 _ z (b + 4) (by subst hb; simp) ha0 hc2
    have e5 : vl n (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0]]) z (b + 5) = (vl n B z a1 && vl n B z c1) :=
      vl_mid_and n B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2]] a1 c1 _ z (b + 5) (by subst hb; simp) ha1 hc1
    have e6 : vl n (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0], Gate.mk GateOp.or [b + 4, b + 5]]) z (b + 6) = (vl n B z a2 && vl n B z c0) :=
      vl_mid_and n B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1]] a2 c0 _ z (b + 6) (by subst hb; simp) ha2 hc0
    have e7 : vl n (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0], Gate.mk GateOp.or [b + 4, b + 5]]) z (b + 7)
        = (vl n (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0]]) z (b + 4) || vl n (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0]]) z (b + 5)) :=
      vl_mid_or n B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0]] (b + 4) (b + 5) _ z (b + 7) (by subst hb; simp)
    have e8 : vl n (B ++ ablk b a0 a1 a2 c0 c1 c2) z (b + 8)
        = (vl n (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0], Gate.mk GateOp.or [b + 4, b + 5]]) z (b + 7) || vl n (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0], Gate.mk GateOp.or [b + 4, b + 5]]) z (b + 6)) :=
      vl_mid_or n B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0], Gate.mk GateOp.or [b + 4, b + 5]] (b + 7) (b + 6) _ z (b + 8) (by subst hb; simp)
    rw [e7, e4, e5, e6] at e8
    exact e8

theorem and_blk_dg (n : ℕ) (M : Finset ℕ) (B : List Gate) (b a0 a1 a2 c0 c1 c2 : ℕ)
    (hb : b = n + B.length)
    (ha0 : a0 < n + B.length) (ha1 : a1 < n + B.length) (ha2 : a2 < n + B.length)
    (hc0 : c0 < n + B.length) (hc1 : c1 < n + B.length) (hc2 : c2 < n + B.length) :
    dg n M (B ++ ablk b a0 a1 a2 c0 c1 c2) b = dg n M B a0 + dg n M B c0 ∧
    dg n M (B ++ ablk b a0 a1 a2 c0 c1 c2) (b + 3)
      = max (dg n M B a0 + dg n M B c1) (dg n M B a1 + dg n M B c0) ∧
    dg n M (B ++ ablk b a0 a1 a2 c0 c1 c2) (b + 8)
      = max (max (dg n M B a0 + dg n M B c2) (dg n M B a1 + dg n M B c1)) (dg n M B a2 + dg n M B c0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact dg_mid_and n M B [] a0 c0 _ b (by subst hb; simp) ha0 hc0
  · have e1 : dg n M (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0]]) (b + 1) = dg n M B a0 + dg n M B c1 :=
      dg_mid_and n M B [Gate.mk GateOp.and [a0, c0]] a0 c1 _ (b + 1) (by subst hb; simp) ha0 hc1
    have e2 : dg n M (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0]]) (b + 2) = dg n M B a1 + dg n M B c0 :=
      dg_mid_and n M B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1]] a1 c0 _ (b + 2) (by subst hb; simp) ha1 hc0
    have e3 : dg n M (B ++ ablk b a0 a1 a2 c0 c1 c2) (b + 3)
        = max (dg n M (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0]]) (b + 1)) (dg n M (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0]]) (b + 2)) :=
      dg_mid_or n M B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0]] (b + 1) (b + 2) _ (b + 3) (by subst hb; simp)
    rw [e1, e2] at e3
    exact e3
  · have e4 : dg n M (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0]]) (b + 4) = dg n M B a0 + dg n M B c2 :=
      dg_mid_and n M B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2]] a0 c2 _ (b + 4) (by subst hb; simp) ha0 hc2
    have e5 : dg n M (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0]]) (b + 5) = dg n M B a1 + dg n M B c1 :=
      dg_mid_and n M B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2]] a1 c1 _ (b + 5) (by subst hb; simp) ha1 hc1
    have e6 : dg n M (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0], Gate.mk GateOp.or [b + 4, b + 5]]) (b + 6) = dg n M B a2 + dg n M B c0 :=
      dg_mid_and n M B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1]] a2 c0 _ (b + 6) (by subst hb; simp) ha2 hc0
    have e7 : dg n M (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0], Gate.mk GateOp.or [b + 4, b + 5]]) (b + 7)
        = max (dg n M (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0]]) (b + 4)) (dg n M (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0]]) (b + 5)) :=
      dg_mid_or n M B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0]] (b + 4) (b + 5) _ (b + 7) (by subst hb; simp)
    have e8 : dg n M (B ++ ablk b a0 a1 a2 c0 c1 c2) (b + 8)
        = max (dg n M (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0], Gate.mk GateOp.or [b + 4, b + 5]]) (b + 7)) (dg n M (B ++ [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0], Gate.mk GateOp.or [b + 4, b + 5]]) (b + 6)) :=
      dg_mid_or n M B [Gate.mk GateOp.and [a0, c0], Gate.mk GateOp.and [a0, c1], Gate.mk GateOp.and [a1, c0], Gate.mk GateOp.or [b + 1, b + 2], Gate.mk GateOp.and [a0, c2], Gate.mk GateOp.and [a1, c1], Gate.mk GateOp.and [a2, c0], Gate.mk GateOp.or [b + 4, b + 5]] (b + 7) (b + 6) _ (b + 8) (by subst hb; simp)
    rw [e7, e4, e5, e6] at e8
    exact e8

theorem sblk_vl (n : ℕ) (B : List Gate) (z : Fin n → Bool) (f : ℕ → Gate) (d : ℕ) (hd : d ≤ 2)
    (hin : ∀ i ∈ (f d).inputs, i < n + B.length) :
    vl n (B ++ sblk (f 0) (f 1) (f 2)) z (n + B.length + sl d)
      = (f d).op.eval ((f d).inputs.map fun i => vl n B z i) := by
  have h3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases h3 with rfl | rfl | rfl
  · exact vl_mid_old n B [] (f 0) _ z _ (by simp [sl]) hin
  · exact vl_mid_old n B [f 0, Gate.mk GateOp.or [], Gate.mk GateOp.or []] (f 1) _ z _ (by simp [sl]) hin
  · exact vl_mid_old n B [f 0, Gate.mk GateOp.or [], Gate.mk GateOp.or [], f 1, Gate.mk GateOp.or [], Gate.mk GateOp.or [], Gate.mk GateOp.or [], Gate.mk GateOp.or []] (f 2) [] z _ (by simp [sl]) hin

theorem sblk_dg (n : ℕ) (M : Finset ℕ) (B : List Gate) (f : ℕ → Gate) (d : ℕ) (hd : d ≤ 2)
    (hin : ∀ i ∈ (f d).inputs, i < n + B.length) :
    dg n M (B ++ sblk (f 0) (f 1) (f 2)) (n + B.length + sl d)
      = (f d).lineDegree ((Circuit.mk B 0).lineDegrees n M) := by
  have h3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases h3 with rfl | rfl | rfl
  · exact dg_mid_old n M B [] (f 0) _ _ (by simp [sl]) hin
  · exact dg_mid_old n M B [f 0, Gate.mk GateOp.or [], Gate.mk GateOp.or []] (f 1) _ _ (by simp [sl]) hin
  · exact dg_mid_old n M B [f 0, Gate.mk GateOp.or [], Gate.mk GateOp.or [], f 1, Gate.mk GateOp.or [], Gate.mk GateOp.or [], Gate.mk GateOp.or [], Gate.mk GateOp.or []] (f 2) [] _ (by simp [sl]) hin

theorem ite_p {α : Type} (c : Prop) (inst : Decidable c) (a b : α) (h : c) : @ite α c inst a b = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse h' => exact absurd h h'

theorem ite_n {α : Type} (c : Prop) (inst : Decidable c) (a b : α) (h : ¬ c) : @ite α c inst a b = b := by
  cases inst with
  | isTrue h' => exact absurd h' h
  | isFalse _ => rfl

noncomputable def tg (g : Gate) (acc : List (WithTop ℕ)) : WithTop ℕ :=
  @ite (WithTop ℕ) (g.op = GateOp.and) (Classical.propDecidable _) (g.inputs.map fun i => acc.getD i ⊤).sum (@ite (WithTop ℕ) (g.op = GateOp.or) (Classical.propDecidable _) ((g.inputs.map fun i => acc.getD i ⊤).foldr min ⊤) ⊤)

noncomputable def tw (ti : List (WithTop ℕ)) (G : List Gate) : List (WithTop ℕ) :=
  G.foldl (fun acc g => acc ++ [tg g acc]) ti

theorem tw_snoc (ti : List (WithTop ℕ)) (G : List Gate) (g : Gate) :
    tw ti (G ++ [g]) = tw ti G ++ [tg g (tw ti G)] := by
  simp [tw, List.foldl_append]

theorem tw_len (ti : List (WithTop ℕ)) (G : List Gate) : (tw ti G).length = ti.length + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [tw]
  | append_singleton G g ih => rw [tw_snoc]; simp [ih]; omega

theorem tw_lt (ti : List (WithTop ℕ)) (G : List Gate) (g : Gate) (i : ℕ) (h : i < ti.length + G.length) :
    (tw ti (G ++ [g])).getD i ⊤ = (tw ti G).getD i ⊤ := by
  rw [tw_snoc]; exact getD_app_lt _ _ _ _ (by rw [tw_len]; exact h)

theorem tw_new (ti : List (WithTop ℕ)) (G : List Gate) (g : Gate) (j : ℕ) (hj : j = ti.length + G.length) :
    (tw ti (G ++ [g])).getD j ⊤ = tg g (tw ti G) := by
  rw [tw_snoc, hj, ← tw_len ti G]; exact getD_app_len _ _ _

theorem tg_and (l : List ℕ) (acc : List (WithTop ℕ)) :
    tg (Gate.mk GateOp.and l) acc = (l.map fun i => acc.getD i ⊤).sum := by
  unfold tg; exact ite_p _ _ _ _ rfl

theorem tg_or (l : List ℕ) (acc : List (WithTop ℕ)) :
    tg (Gate.mk GateOp.or l) acc = (l.map fun i => acc.getD i ⊤).foldr min ⊤ := by
  unfold tg
  rw [ite_n _ _ _ _ (by intro h; cases h), ite_p _ _ _ _ rfl]

theorem tg_and0 (acc : List (WithTop ℕ)) : tg (Gate.mk GateOp.and []) acc = 0 := by
  rw [tg_and]; rfl
theorem tg_and1 (acc : List (WithTop ℕ)) (x : ℕ) : tg (Gate.mk GateOp.and [x]) acc = acc.getD x ⊤ := by
  rw [tg_and]; show (acc.getD x ⊤ :: []).sum = _; rw [List.sum_cons, List.sum_nil, add_zero]
theorem tg_and2 (acc : List (WithTop ℕ)) (x y : ℕ) :
    tg (Gate.mk GateOp.and [x, y]) acc = acc.getD x ⊤ + acc.getD y ⊤ := by
  rw [tg_and]; show (acc.getD x ⊤ :: acc.getD y ⊤ :: []).sum = _
  rw [List.sum_cons, List.sum_cons, List.sum_nil, add_zero]
theorem tg_or0 (acc : List (WithTop ℕ)) : tg (Gate.mk GateOp.or []) acc = ⊤ := by
  rw [tg_or]; rfl
theorem tg_or1 (acc : List (WithTop ℕ)) (x : ℕ) : tg (Gate.mk GateOp.or [x]) acc = acc.getD x ⊤ := by
  rw [tg_or]; show min (acc.getD x ⊤) ⊤ = _; exact min_top_right _
theorem tg_or2 (acc : List (WithTop ℕ)) (x y : ℕ) :
    tg (Gate.mk GateOp.or [x, y]) acc = min (acc.getD x ⊤) (acc.getD y ⊤) := by
  rw [tg_or]; show min (acc.getD x ⊤) (min (acc.getD y ⊤) ⊤) = _; rw [min_top_right]

theorem tsplit (a b : WithTop ℕ) (d : ℕ) (h : a + b ≤ (d : WithTop ℕ)) :
    ∃ i j : ℕ, i + j = d ∧ a ≤ (i : WithTop ℕ) ∧ b ≤ (j : WithTop ℕ) := by
  by_cases ha : a = ⊤
  · subst ha; simp at h
  by_cases hb : b = ⊤
  · subst hb; simp at h
  obtain ⟨a', rfl⟩ := WithTop.ne_top_iff_exists.mp ha
  obtain ⟨b', rfl⟩ := WithTop.ne_top_iff_exists.mp hb
  have h1 : ((a' : ℕ) : WithTop ℕ) + ((b' : ℕ) : WithTop ℕ) ≤ ((d : ℕ) : WithTop ℕ) := h
  have h' : a' + b' ≤ d := by exact_mod_cast h1
  have h2 : ((b' : ℕ) : WithTop ℕ) ≤ ((d - a' : ℕ) : WithTop ℕ) := by
    exact_mod_cast (show b' ≤ d - a' by omega)
  exact ⟨a', d - a', by omega, le_refl _, h2⟩

def lc (N i d : ℕ) : ℕ :=
  if i < N then i else if i < N + N then (if d = 0 then N + N else i)
  else N + N + (9 * (i - (N + N)) + 1) + sl d

def rf (N k i d : ℕ) : ℕ := if i < N + N + k then lc N i d else N + N

def blk (N k b : ℕ) (g : Gate) : List Gate :=
  match g.op, g.inputs with
  | GateOp.and, [x, y] =>
    ablk b (rf N k x 0) (rf N k x 1) (rf N k x 2) (rf N k y 0) (rf N k y 1) (rf N k y 2)
  | o, l => sblk (Gate.mk o (l.map fun i => rf N k i 0)) (Gate.mk o (l.map fun i => rf N k i 1))
      (Gate.mk o (l.map fun i => rf N k i 2))

theorem blk_simple (N k b : ℕ) (op : GateOp) (l : List ℕ)
    (hx : ¬ (op = GateOp.and ∧ l.length = 2)) (hop : op = GateOp.and ∨ op = GateOp.or) :
    blk N k b (Gate.mk op l) = sblk (Gate.mk op (l.map fun i => rf N k i 0))
      (Gate.mk op (l.map fun i => rf N k i 1)) (Gate.mk op (l.map fun i => rf N k i 2)) := by
  rcases hop with rfl | rfl <;> rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨t, l⟩⟩⟩ <;>
    first | rfl | (exfalso; simp at hx)

theorem blk_len (N k b : ℕ) (g : Gate) : (blk N k b g).length = 9 := by
  unfold blk; split <;> rfl

theorem blk_mono (N k b : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ h ∈ blk N k b g, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 := by
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only at hop hl
  unfold blk
  split
  · simp [ablk]
  · rcases hop with rfl | rfl <;> simp [sblk, hl]

def bld (N : ℕ) (G : List Gate) : List Gate :=
  G.foldl (fun acc g => acc ++ blk N ((acc.length - 1) / 9) (N + N + acc.length) g) [Gate.mk GateOp.or []]

theorem bld_snoc' (N : ℕ) (G : List Gate) (g : Gate) :
    bld N (G ++ [g]) = bld N G ++ blk N (((bld N G).length - 1) / 9) (N + N + (bld N G).length) g := by
  simp [bld, List.foldl_append]

theorem bld_len (N : ℕ) (G : List Gate) : (bld N G).length = 9 * G.length + 1 := by
  induction G using List.reverseRecOn with
  | nil => rfl
  | append_singleton G g ih => rw [bld_snoc', List.length_append, blk_len, ih]; simp; omega

theorem bld_snoc (N : ℕ) (G : List Gate) (g : Gate) :
    bld N (G ++ [g]) = bld N G ++ blk N G.length (N + N + (bld N G).length) g := by
  have e : ((bld N G).length - 1) / 9 = G.length := by rw [bld_len]; omega
  rw [bld_snoc', e]

theorem bld_mono (N : ℕ) (G : List Gate)
    (hG : ∀ g ∈ G, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ h ∈ bld N G, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 := by
  induction G using List.reverseRecOn with
  | nil => intro h hh; simp [bld] at hh; subst hh; simp
  | append_singleton G g ih =>
    intro h hh
    rw [bld_snoc, List.mem_append] at hh
    rcases hh with hh | hh
    · exact ih (fun g' hg' => hG g' (by simp [hg'])) h hh
    · exact blk_mono N _ _ g (hG g (by simp)) h hh

theorem lc_lt (N k i d : ℕ) (h : i < N + N + k) : lc N i d < N + N + (9 * k + 1) := by
  unfold lc sl; split_ifs <;> omega

theorem lc_new (N k d : ℕ) : lc N (N + N + k) d = N + N + (9 * k + 1) + sl d := by
  unfold lc; split_ifs <;> omega

theorem rf_lt (N k i d : ℕ) (h : i < N + N + k) : rf N k i d = lc N i d := by
  unfold rf; exact ite_p _ _ _ _ h

theorem rf_ge (N k i d : ℕ) (h : ¬ i < N + N + k) : rf N k i d = N + N := by
  unfold rf; exact ite_n _ _ _ _ h

def Inv (N : ℕ) (z : Fin (N + N) → Bool) (ti : List (WithTop ℕ)) (G : List Gate) : Prop :=
  vl (N + N) (bld N G) z (N + N) = false ∧
  dg (N + N) (Finset.Ico N (N + N)) (bld N G) (N + N) = 0 ∧
  ∀ i d, i < N + N + G.length → d ≤ 2 →
    (vl (N + N) (bld N G) z (lc N i d) = true → vl (N + N) G z i = true) ∧
    dg (N + N) (Finset.Ico N (N + N)) (bld N G) (lc N i d) ≤ d ∧
    ((tw ti G).getD i ⊤ ≤ (d : WithTop ℕ) → vl (N + N) (bld N G) z (lc N i d) = true)

theorem ref_facts (N : ℕ) (z : Fin (N + N) → Bool) (ti : List (WithTop ℕ)) (G : List Gate)
    (hti : ti.length = N + N) (hI : Inv N z ti G) (i d : ℕ) (hd : d ≤ 2) :
    rf N G.length i d < N + N + (bld N G).length ∧
    (vl (N + N) (bld N G) z (rf N G.length i d) = true → vl (N + N) G z i = true) ∧
    dg (N + N) (Finset.Ico N (N + N)) (bld N G) (rf N G.length i d) ≤ d ∧
    ((tw ti G).getD i ⊤ ≤ (d : WithTop ℕ) → vl (N + N) (bld N G) z (rf N G.length i d) = true) := by
  by_cases h : i < N + N + G.length
  · rw [rf_lt _ _ _ _ h]
    exact ⟨by rw [bld_len]; exact lc_lt N _ i d h, hI.2.2 i d h hd⟩
  · rw [rf_ge _ _ _ _ h]
    refine ⟨by rw [bld_len]; omega, ?_, ?_, ?_⟩
    · intro h'; rw [hI.1] at h'; cases h'
    · rw [hI.2.1]; omega
    · intro h'
      rw [getD_ge _ _ _ (by rw [tw_len, hti]; omega)] at h'
      simp at h'

theorem simple_level (N : ℕ) (z : Fin (N + N) → Bool) (ti : List (WithTop ℕ)) (G : List Gate)
    (hti : ti.length = N + N) (hI : Inv N z ti G) (op : GateOp) (l : List ℕ) (d : ℕ) (hd : d ≤ 2)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : l.length ≤ 2)
    (hx : ¬ (op = GateOp.and ∧ l.length = 2)) :
    (op.eval ((l.map fun i => rf N G.length i d).map fun i => vl (N + N) (bld N G) z i) = true →
      op.eval (l.map fun i => vl (N + N) G z i) = true) ∧
    (Gate.mk op (l.map fun i => rf N G.length i d)).lineDegree
      ((Circuit.mk (bld N G) 0).lineDegrees (N + N) (Finset.Ico N (N + N))) ≤ d ∧
    (tg (Gate.mk op l) (tw ti G) ≤ (d : WithTop ℕ) →
      op.eval ((l.map fun i => rf N G.length i d).map fun i => vl (N + N) (bld N G) z i) = true) := by
  have R := fun i => ref_facts N z ti G hti hI i d hd
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨t, l⟩⟩⟩
  · rcases hop with rfl | rfl
    · refine ⟨fun _ => rfl, ?_, fun _ => rfl⟩
      show (Gate.mk GateOp.and []).lineDegree _ ≤ d
      rw [ld_and0]; omega
    · refine ⟨fun h => h, ?_, ?_⟩
      · show (Gate.mk GateOp.or []).lineDegree _ ≤ d
        rw [ld_or0]; omega
      · intro h; rw [tg_or0] at h; simp at h
  · rcases hop with rfl | rfl
    · refine ⟨?_, ?_, ?_⟩
      · show GateOp.and.eval [vl (N + N) (bld N G) z (rf N G.length x d)] = true →
          GateOp.and.eval [vl (N + N) G z x] = true
        simp only [ev_and1]; exact (R x).2.1
      · show (Gate.mk GateOp.and [rf N G.length x d]).lineDegree _ ≤ d
        rw [ld_and1]; exact (R x).2.2.1
      · show tg (Gate.mk GateOp.and [x]) (tw ti G) ≤ _ →
          GateOp.and.eval [vl (N + N) (bld N G) z (rf N G.length x d)] = true
        rw [tg_and1, ev_and1]; exact (R x).2.2.2
    · refine ⟨?_, ?_, ?_⟩
      · show GateOp.or.eval [vl (N + N) (bld N G) z (rf N G.length x d)] = true →
          GateOp.or.eval [vl (N + N) G z x] = true
        simp only [ev_or1]; exact (R x).2.1
      · show (Gate.mk GateOp.or [rf N G.length x d]).lineDegree _ ≤ d
        rw [ld_or1]; exact (R x).2.2.1
      · show tg (Gate.mk GateOp.or [x]) (tw ti G) ≤ _ →
          GateOp.or.eval [vl (N + N) (bld N G) z (rf N G.length x d)] = true
        rw [tg_or1, ev_or1]; exact (R x).2.2.2
  · rcases hop with rfl | rfl
    · exact absurd ⟨rfl, rfl⟩ hx
    · refine ⟨?_, ?_, ?_⟩
      · show GateOp.or.eval [vl (N + N) (bld N G) z (rf N G.length x d),
            vl (N + N) (bld N G) z (rf N G.length y d)] = true →
          GateOp.or.eval [vl (N + N) G z x, vl (N + N) G z y] = true
        simp only [ev_or2, Bool.or_eq_true]; exact Or.imp (R x).2.1 (R y).2.1
      · show (Gate.mk GateOp.or [rf N G.length x d, rf N G.length y d]).lineDegree _ ≤ d
        rw [ld_or2]; exact max_le (R x).2.2.1 (R y).2.2.1
      · show tg (Gate.mk GateOp.or [x, y]) (tw ti G) ≤ _ →
          GateOp.or.eval [vl (N + N) (bld N G) z (rf N G.length x d),
            vl (N + N) (bld N G) z (rf N G.length y d)] = true
        rw [tg_or2, ev_or2, Bool.or_eq_true, min_le_iff]
        exact Or.imp (R x).2.2.2 (R y).2.2.2
  · simp at hl

theorem blk_spec (N : ℕ) (z : Fin (N + N) → Bool) (ti : List (WithTop ℕ)) (G : List Gate) (g : Gate)
    (hti : ti.length = N + N)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hI : Inv N z ti G) (d : ℕ) (hd : d ≤ 2) :
    (vl (N + N) (bld N G ++ blk N G.length (N + N + (bld N G).length) g) z
        (N + N + (bld N G).length + sl d) = true →
      vl (N + N) (G ++ [g]) z (N + N + G.length) = true) ∧
    dg (N + N) (Finset.Ico N (N + N)) (bld N G ++ blk N G.length (N + N + (bld N G).length) g)
      (N + N + (bld N G).length + sl d) ≤ d ∧
    ((tw ti (G ++ [g])).getD (N + N + G.length) ⊤ ≤ (d : WithTop ℕ) →
      vl (N + N) (bld N G ++ blk N G.length (N + N + (bld N G).length) g) z
        (N + N + (bld N G).length + sl d) = true) := by
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only at hop hl
  have hC : vl (N + N) (G ++ [Gate.mk op l]) z (N + N + G.length)
      = op.eval (l.map fun i => vl (N + N) G z i) := vl_new (N + N) G (Gate.mk op l) z
  have hT : (tw ti (G ++ [Gate.mk op l])).getD (N + N + G.length) ⊤ = tg (Gate.mk op l) (tw ti G) :=
    tw_new ti G _ (N + N + G.length) (by rw [hti])
  rw [hC, hT]
  by_cases hx : op = GateOp.and ∧ l.length = 2
  · obtain ⟨rfl, h2⟩ := hx
    obtain ⟨x, y, rfl⟩ : ∃ x y, l = [x, y] := List.length_eq_two.mp h2
    have R := fun i e (he : e ≤ 2) => ref_facts N z ti G hti hI i e he
    have Rx0 := R x 0 (by omega)
    have Rx1 := R x 1 (by omega)
    have Rx2 := R x 2 (by omega)
    have Ry0 := R y 0 (by omega)
    have Ry1 := R y 1 (by omega)
    have Ry2 := R y 2 (by omega)
    obtain ⟨v0, v3, v8⟩ := and_blk_vl (N + N) (bld N G) z (N + N + (bld N G).length)
      (rf N G.length x 0) (rf N G.length x 1) (rf N G.length x 2)
      (rf N G.length y 0) (rf N G.length y 1) (rf N G.length y 2) rfl
      Rx0.1 Rx1.1 Rx2.1 Ry0.1 Ry1.1 Ry2.1
    obtain ⟨d0, d3, d8⟩ := and_blk_dg (N + N) (Finset.Ico N (N + N)) (bld N G) (N + N + (bld N G).length)
      (rf N G.length x 0) (rf N G.length x 1) (rf N G.length x 2)
      (rf N G.length y 0) (rf N G.length y 1) (rf N G.length y 2) rfl
      Rx0.1 Rx1.1 Rx2.1 Ry0.1 Ry1.1 Ry2.1
    have hb : blk N G.length (N + N + (bld N G).length) (Gate.mk GateOp.and [x, y])
        = ablk (N + N + (bld N G).length) (rf N G.length x 0) (rf N G.length x 1) (rf N G.length x 2)
          (rf N G.length y 0) (rf N G.length y 1) (rf N G.length y 2) := rfl
    have hE : GateOp.and.eval ([x, y].map fun i => vl (N + N) G z i)
        = (vl (N + N) G z x && vl (N + N) G z y) := ev_and2 _ _
    rw [hb, tg_and2, hE]
    have a0 := Rx0.2.2.1
    have a1 := Rx1.2.2.1
    have a2 := Rx2.2.2.1
    have c0 := Ry0.2.2.1
    have c1 := Ry1.2.2.1
    have c2 := Ry2.2.2.1
    have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd3 with rfl | rfl | rfl
    · have es : N + N + (bld N G).length + sl 0 = N + N + (bld N G).length := by simp [sl]
      rw [es, v0, d0]
      refine ⟨?_, by omega, ?_⟩
      · intro h
        rw [Bool.and_eq_true] at h ⊢
        exact ⟨Rx0.2.1 h.1, Ry0.2.1 h.2⟩
      · intro h
        obtain ⟨i, j, hij, hi, hj⟩ := tsplit _ _ _ h
        obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
        simp [Rx0.2.2.2 hi, Ry0.2.2.2 hj]
    · have es : N + N + (bld N G).length + sl 1 = N + N + (bld N G).length + 3 := by simp [sl]
      rw [es, v3, d3]
      refine ⟨?_, max_le (by omega) (by omega), ?_⟩
      · intro h
        rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
        rw [Bool.and_eq_true]
        rcases h with h | h
        · exact ⟨Rx0.2.1 h.1, Ry1.2.1 h.2⟩
        · exact ⟨Rx1.2.1 h.1, Ry0.2.1 h.2⟩
      · intro h
        obtain ⟨i, j, hij, hi, hj⟩ := tsplit _ _ _ h
        have h2 : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
        rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [Rx0.2.2.2 hi, Ry1.2.2.2 hj]
        · simp [Rx1.2.2.2 hi, Ry0.2.2.2 hj]
    · have es : N + N + (bld N G).length + sl 2 = N + N + (bld N G).length + 8 := by simp [sl]
      rw [es, v8, d8]
      refine ⟨?_, max_le (max_le (by omega) (by omega)) (by omega), ?_⟩
      · intro h
        rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true,
          Bool.and_eq_true] at h
        rw [Bool.and_eq_true]
        rcases h with (h | h) | h
        · exact ⟨Rx0.2.1 h.1, Ry2.2.1 h.2⟩
        · exact ⟨Rx1.2.1 h.1, Ry1.2.1 h.2⟩
        · exact ⟨Rx2.2.1 h.1, Ry0.2.1 h.2⟩
      · intro h
        obtain ⟨i, j, hij, hi, hj⟩ := tsplit _ _ _ h
        have h2 : (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 1) ∨ (i = 2 ∧ j = 0) := by omega
        rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [Rx0.2.2.2 hi, Ry2.2.2.2 hj]
        · simp [Rx1.2.2.2 hi, Ry1.2.2.2 hj]
        · simp [Rx2.2.2.2 hi, Ry0.2.2.2 hj]
  · have hb := blk_simple N G.length (N + N + (bld N G).length) op l hx hop
    rw [hb]
    have R := fun i => ref_facts N z ti G hti hI i d hd
    have S := simple_level N z ti G hti hI op l d hd hop hl hx
    have hin : ∀ r ∈ (l.map fun i => rf N G.length i d), r < N + N + (bld N G).length := by
      intro r hr
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
      exact (R i).1
    have hv : vl (N + N) (bld N G ++ sblk (Gate.mk op (l.map fun i => rf N G.length i 0))
          (Gate.mk op (l.map fun i => rf N G.length i 1)) (Gate.mk op (l.map fun i => rf N G.length i 2))) z
          (N + N + (bld N G).length + sl d)
        = op.eval ((l.map fun i => rf N G.length i d).map fun i => vl (N + N) (bld N G) z i) :=
      sblk_vl (N + N) (bld N G) z (fun e => Gate.mk op (l.map fun i => rf N G.length i e)) d hd hin
    have hdg : dg (N + N) (Finset.Ico N (N + N)) (bld N G ++ sblk (Gate.mk op (l.map fun i => rf N G.length i 0))
          (Gate.mk op (l.map fun i => rf N G.length i 1)) (Gate.mk op (l.map fun i => rf N G.length i 2)))
          (N + N + (bld N G).length + sl d)
        = (Gate.mk op (l.map fun i => rf N G.length i d)).lineDegree
          ((Circuit.mk (bld N G) 0).lineDegrees (N + N) (Finset.Ico N (N + N))) :=
      sblk_dg (N + N) (Finset.Ico N (N + N)) (bld N G) (fun e => Gate.mk op (l.map fun i => rf N G.length i e)) d hd hin
    rw [hv, hdg]
    exact S

theorem inv_step (N : ℕ) (z : Fin (N + N) → Bool) (ti : List (WithTop ℕ)) (G : List Gate) (g : Gate)
    (hti : ti.length = N + N)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hI : Inv N z ti G) : Inv N z ti (G ++ [g]) := by
  have hbl := bld_len N G
  refine ⟨?_, ?_, ?_⟩
  · rw [bld_snoc, vl_app_lt _ _ _ _ _ (by omega)]; exact hI.1
  · rw [bld_snoc, dg_app_lt _ _ _ _ _ (by omega)]; exact hI.2.1
  · intro i d hi hd
    rw [bld_snoc]
    by_cases h : i < N + N + G.length
    · have hl := lc_lt N G.length i d h
      rw [vl_app_lt _ _ _ _ _ (by omega), dg_app_lt _ _ _ _ _ (by omega), vl_snoc_lt _ _ _ _ _ h,
        tw_lt _ _ _ _ (by omega)]
      exact hI.2.2 i d h hd
    · have e : i = N + N + G.length := by
        rw [List.length_append, List.length_singleton] at hi; omega
      subst e
      have e2 : lc N (N + N + G.length) d = N + N + (bld N G).length + sl d := by
        rw [lc_new, hbl]
      rw [e2]
      exact blk_spec N z ti G g hti hg hI d hd

theorem dg_inp (n : ℕ) (M : Finset ℕ) (G : List Gate) (x : ℕ) (h : x < n) :
    dg n M G x = if x ∈ M then 1 else 0 := by
  have h1 := dg_app_lt n M [] G x (by simpa using h)
  rw [List.nil_append] at h1
  rw [h1]
  unfold dg
  simp only [Circuit.lineDegrees, List.foldl_nil]
  rw [List.getD_eq_getElem?_getD]
  simp [List.getElem?_range h]

theorem inv_base (N : ℕ) (z : Fin (N + N) → Bool) (ti : List (WithTop ℕ))
    (hP : ∀ i, i < N → ∀ d : ℕ, ti.getD i ⊤ ≤ (d : WithTop ℕ) → vl (N + N) [] z i = true)
    (hL : ∀ i, N ≤ i → i < N + N → ∀ d : ℕ, ti.getD i ⊤ ≤ (d : WithTop ℕ) →
      1 ≤ d ∧ vl (N + N) [] z i = true) : Inv N z ti [] := by
  have hz1 : vl (N + N) (bld N []) z (N + N) = false := by
    show vl (N + N) ([] ++ [Gate.mk GateOp.or []]) z (N + N + ([] : List Gate).length) = false
    rw [vl_new]; rfl
  have hz2 : dg (N + N) (Finset.Ico N (N + N)) (bld N []) (N + N) = 0 := by
    show dg (N + N) (Finset.Ico N (N + N)) ([] ++ [Gate.mk GateOp.or []]) (N + N + ([] : List Gate).length) = 0
    rw [dg_new]; exact ld_or0 _
  refine ⟨hz1, hz2, ?_⟩
  intro i d hi hd
  have hi' : i < N + N := by simpa using hi
  have hv : vl (N + N) (bld N []) z i = vl (N + N) [] z i :=
    vl_snoc_lt (N + N) [] (Gate.mk GateOp.or []) z i (by simpa using hi')
  have hdd : dg (N + N) (Finset.Ico N (N + N)) (bld N []) i = if i ∈ Finset.Ico N (N + N) then 1 else 0 :=
    dg_inp _ _ _ _ hi'
  by_cases h1 : i < N
  · have e : lc N i d = i := by unfold lc; exact ite_p _ _ _ _ h1
    rw [e, hv, hdd]
    refine ⟨fun h => h, ?_, ?_⟩
    · rw [ite_n _ _ _ _ (by simp; omega)]; omega
    · exact hP i h1 d
  · by_cases h0 : d = 0
    · have e : lc N i d = N + N := by
        unfold lc; rw [ite_n _ _ _ _ h1, ite_p _ _ _ _ hi', ite_p _ _ _ _ h0]
      rw [e, hz1, hz2]
      refine ⟨(fun h => by cases h), by omega, ?_⟩
      intro h
      have := (hL i (by omega) hi' d h).1
      omega
    · have e : lc N i d = i := by
        unfold lc; rw [ite_n _ _ _ _ h1, ite_p _ _ _ _ hi', ite_n _ _ _ _ h0]
      rw [e, hv, hdd]
      refine ⟨fun h => h, ?_, ?_⟩
      · rw [ite_p _ _ _ _ (by simp; omega)]; omega
      · intro h; exact (hL i (by omega) hi' d h).2

theorem inv_all (N : ℕ) (z : Fin (N + N) → Bool) (ti : List (WithTop ℕ)) (hti : ti.length = N + N)
    (hP : ∀ i, i < N → ∀ d : ℕ, ti.getD i ⊤ ≤ (d : WithTop ℕ) → vl (N + N) [] z i = true)
    (hL : ∀ i, N ≤ i → i < N + N → ∀ d : ℕ, ti.getD i ⊤ ≤ (d : WithTop ℕ) →
      1 ≤ d ∧ vl (N + N) [] z i = true) (G : List Gate)
    (hG : ∀ g ∈ G, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) : Inv N z ti G := by
  induction G using List.reverseRecOn with
  | nil => exact inv_base N z ti hP hL
  | append_singleton G g ih =>
    exact inv_step N z ti G g hti (hG g (by simp)) (ih (fun g' hg' => hG g' (by simp [hg'])))

theorem getD_ofFn {α : Type} (n : ℕ) (f : Fin n → α) (i : ℕ) (h : i < n) (d : α) :
    (List.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_rep (n : ℕ) (i : ℕ) : (List.replicate n (⊤ : WithTop ℕ)).getD i ⊤ = ⊤ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem full : ∀ (N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (echo : Fin N → Fin N → WithTop ℕ),
    (∀ (p w : Fin N), echo p w = (C.gates.foldl (fun acc g => acc ++ [@ite (WithTop ℕ) (g.op = PEqualNP.CircuitLowerBounds.GateOp.and) (Classical.propDecidable _) (g.inputs.map fun i => acc.getD i ⊤).sum (@ite (WithTop ℕ) (g.op = PEqualNP.CircuitLowerBounds.GateOp.or) (Classical.propDecidable _) ((g.inputs.map fun i => acc.getD i ⊤).foldr min ⊤) ⊤)]) (List.ofFn (fun k : Fin (N + N) => if k = Fin.castAdd N p then (0 : WithTop ℕ) else if k = Fin.natAdd N w then (1 : WithTop ℕ) else ⊤))).getD C.output ⊤) →
    PEqualNP.MetaComplexity.Monotone2 C →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C' ∧
      C'.size ≤ 9 * C.size + 1 ∧
      PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) C' 2 ∧
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) C' z = true →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = true) ∧
      (∀ p w : Fin N, 1 ≤ echo p w → echo p w ≤ 2 →
        PEqualNP.MetaComplexity.circuitFun (N + N) C' (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w))
          = PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w))) := by
  intro N C echo hecho hm
  have hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨a, b⟩ := hm g hg
    exact ⟨by simpa using a, b⟩
  have hA : ∀ z : Fin (N + N) → Bool, Inv N z (List.replicate (N + N) ⊤) C.gates := by
    intro z
    refine inv_all N z _ (by simp) ?_ ?_ C.gates hG
    · intro i _ d h; rw [getD_rep] at h; simp at h
    · intro i _ _ d h; rw [getD_rep] at h; simp at h
  refine ⟨⟨bld N C.gates, rf N C.gates.length C.output 2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨a, b⟩ := bld_mono N C.gates hG g hg
    exact ⟨by simpa using a, b⟩
  · show (bld N C.gates).length ≤ 9 * C.gates.length + 1
    rw [bld_len]
  · exact (ref_facts N (fun _ => false) _ C.gates (by simp) (hA _) C.output 2 (le_refl _)).2.2.1
  · intro z hz
    exact (ref_facts N z _ C.gates (by simp) (hA z) C.output 2 (le_refl _)).2.1 hz
  · intro p w h1 h2
    have hti : (List.ofFn (fun k : Fin (N + N) => if k = Fin.castAdd N p then (0 : WithTop ℕ) else if k = Fin.natAdd N w then (1 : WithTop ℕ) else ⊤)).length = N + N := by simp
    have hI : Inv N (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w))
        (List.ofFn (fun k : Fin (N + N) => if k = Fin.castAdd N p then (0 : WithTop ℕ) else if k = Fin.natAdd N w then (1 : WithTop ℕ) else ⊤)) C.gates := by
      refine inv_all N _ _ hti ?_ ?_ C.gates hG
      · intro i hi d h
        rw [getD_ofFn _ _ _ (by omega)] at h
        show (List.ofFn _).getD i false = true
        rw [getD_ofFn _ _ _ (by omega)]
        by_cases e1 : (⟨i, by omega⟩ : Fin (N + N)) = Fin.castAdd N p
        · exact decide_eq_true (Or.inl e1)
        · by_cases e2 : (⟨i, by omega⟩ : Fin (N + N)) = Fin.natAdd N w
          · exact decide_eq_true (Or.inr e2)
          · rw [ite_n _ _ _ _ e1, ite_n _ _ _ _ e2] at h
            simp at h
      · intro i hi hi2 d h
        rw [getD_ofFn _ _ _ hi2] at h
        have e1 : ¬ (⟨i, hi2⟩ : Fin (N + N)) = Fin.castAdd N p := by
          intro e
          have := congrArg Fin.val e
          simp at this
          omega
        by_cases e2 : (⟨i, hi2⟩ : Fin (N + N)) = Fin.natAdd N w
        · refine ⟨?_, ?_⟩
          · rw [ite_n _ _ _ _ e1, ite_p _ _ _ _ e2] at h
            exact_mod_cast h
          · show (List.ofFn _).getD i false = true
            rw [getD_ofFn _ _ _ hi2]
            exact decide_eq_true (Or.inr e2)
        · rw [ite_n _ _ _ _ e1, ite_n _ _ _ _ e2] at h
          simp at h
    have R := ref_facts N _ _ C.gates hti hI C.output 2 (le_refl _)
    have h3 : (tw (List.ofFn (fun k : Fin (N + N) => if k = Fin.castAdd N p then (0 : WithTop ℕ) else if k = Fin.natAdd N w then (1 : WithTop ℕ) else ⊤)) C.gates).getD C.output ⊤ ≤ ((2 : ℕ) : WithTop ℕ) := by
      have h4 := hecho p w
      rw [h4] at h2
      exact h2
    have h5 := R.2.2.2 h3
    have h6 := R.2.1 h5
    show vl (N + N) (bld N C.gates) _ (rf N C.gates.length C.output 2) = vl (N + N) C.gates _ C.output
    rw [h5, h6]

end PEqualNP.Outside.L_meta_1510

theorem PEqualNP.Outside.L_meta_1510 : ∀ (N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (echo : Fin N → Fin N → WithTop ℕ),
    (∀ (p w : Fin N), echo p w = (C.gates.foldl (fun acc g => acc ++ [@ite (WithTop ℕ) (g.op = PEqualNP.CircuitLowerBounds.GateOp.and) (Classical.propDecidable _) (g.inputs.map fun i => acc.getD i ⊤).sum (@ite (WithTop ℕ) (g.op = PEqualNP.CircuitLowerBounds.GateOp.or) (Classical.propDecidable _) ((g.inputs.map fun i => acc.getD i ⊤).foldr min ⊤) ⊤)]) (List.ofFn (fun k : Fin (N + N) => if k = Fin.castAdd N p then (0 : WithTop ℕ) else if k = Fin.natAdd N w then (1 : WithTop ℕ) else ⊤))).getD C.output ⊤) →
    PEqualNP.MetaComplexity.Monotone2 C →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C' ∧
      C'.size ≤ 9 * C.size + 1 ∧
      PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) C' 2 ∧
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) C' z = true →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = true) ∧
      (∀ p w : Fin N, 1 ≤ echo p w → echo p w ≤ 2 →
        PEqualNP.MetaComplexity.circuitFun (N + N) C' (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w))
          = PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w))) :=
  PEqualNP.Outside.L_meta_1510.full
