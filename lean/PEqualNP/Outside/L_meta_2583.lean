import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

namespace A3692

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_stepW_len (gs : List Gate) (inp : List Bool) :
    (gs.foldl stepW inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp
  | cons g rest ih =>
    simp [List.foldl, stepW, ih]
    omega

private lemma wires_eq_foldl (C : Circuit) (inp : List Bool) :
    C.wires inp = C.gates.foldl stepW inp := rfl

private lemma wires_len (C : Circuit) (inp : List Bool) :
    (C.wires inp).length = inp.length + C.gates.length := by
  simpa [wires_eq_foldl] using foldl_stepW_len C.gates inp

private lemma getD_append_left (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_append_self (l1 : List Bool) (b : Bool) :
    (l1 ++ [b]).getD l1.length false = b := by
  simp [List.getD]

private lemma getD_of_ge (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD, List.getElem?_eq_none hi]

private lemma getD_ofFn {n : ℕ} (z : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn z).getD i false = z ⟨i, hi⟩ := by
  simp [List.getD, hi]

private def wireVal (n : ℕ) (gs : List Gate) (z : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl stepW (List.ofFn z)).getD i false

private lemma wireVal_append_gate_lt (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool)
    (i : ℕ) (hi : i < n + gs.length) :
    wireVal n (gs ++ [g]) z i = wireVal n gs z i := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  exact getD_append_left _ _ i (by omega)

private lemma wireVal_append_gate_self (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool) :
    wireVal n (gs ++ [g]) z (n + gs.length) =
      g.op.eval (g.inputs.map (fun i => wireVal n gs z i)) := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  rw [← hlen]
  exact getD_append_self (gs.foldl stepW (List.ofFn z)) _

private def gateAtL (gs : List Gate) (j : ℕ) : Gate :=
  gs.getD j ⟨GateOp.or, []⟩

private lemma gateAtL_append_lt (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtL (gs ++ [g]) j = gateAtL gs j := by
  simp [gateAtL, List.getD, List.getElem?_append_left hj]

private lemma gateAtL_append_self (gs : List Gate) (g : Gate) :
    gateAtL (gs ++ [g]) gs.length = g := by
  simp [gateAtL, List.getD]

private def Good (x1 x2 : ℕ) (S : Bool → Finset ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gateAtL gs j).inputs, i < x1 + x2 + j) ∧
  (∀ b : Bool, ∀ w ∈ S b, w < x1 + x2 + gs.length) ∧
  (∀ b : Bool, ∀ w ∈ S b,
    (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
    ∃ j < gs.length, w = x1 + x2 + j ∧ (gateAtL gs j).op = GateOp.or ∧
      ∀ u ∈ (gateAtL gs j).inputs, u ∈ S b) ∧
  (∀ j < gs.length, (gateAtL gs j).op = GateOp.and →
    ∃ a c : ℕ, (gateAtL gs j).inputs = [a, c] ∧ a ∈ S false ∧ c ∈ S true)

private def S0 (x1 x2 : ℕ) (b : Bool) : Finset ℕ :=
  if b then Finset.Ico x1 (x1 + x2) else Finset.range x1

private lemma good_init (x1 x2 : ℕ) : Good x1 x2 (S0 x1 x2) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; cases hg
  · intro j hj; simp at hj
  · intro b w hw
    cases b <;> simp [S0] at hw <;> omega
  · intro b w hw
    left
    cases b <;> simp [S0] at hw
    · exact ⟨by omega, by simp [show ¬(x1 ≤ w) by omega]⟩
    · exact ⟨hw.2, by simp [hw.1]⟩
  · intro j hj; simp at hj

private lemma mem_S0_false {x1 x2 : ℕ} (p : Fin x1) : p.1 ∈ S0 x1 x2 false := by
  simp [S0, p.2]

private lemma mem_S0_true {x1 x2 : ℕ} (l : Fin x2) : x1 + l.1 ∈ S0 x1 x2 true := by
  simp [S0]

private lemma good_append_or_side {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) (b : Bool) {u v : ℕ} (hu : u ∈ S b) (hv : v ∈ S b) :
    let w := x1 + x2 + gs.length
    let S' : Bool → Finset ℕ := fun b' => if b' = b then insert w (S b') else S b'
    Good x1 x2 S' (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have hu_lt : u < x1 + x2 + gs.length := hLt b u hu
  have hv_lt : v < x1 + x2 + gs.length := hLt b v hv
  dsimp only
  have hSub : ∀ b' : Bool, S b' ⊆ (if b' = b then insert (x1 + x2 + gs.length) (S b') else S b') := by
    intro b'
    by_cases hbb : b' = b
    · simp [hbb]
    · simp [hbb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    by_cases hbb : b' = b
    · simp only [hbb, ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · omega
      · have := hLt b w hw; omega
    · simp only [hbb, ite_false] at hw
      have := hLt b' w hw; omega
  · intro b' w hw
    by_cases hbb : b' = b
    · subst hbb
      simp only [ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · right
        refine ⟨gs.length, by simp, rfl, ?_, ?_⟩
        · rw [gateAtL_append_self]
        · rw [gateAtL_append_self]
          intro t ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact hSub b' hu
          · exact hSub b' hv
      · rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
        · exact Or.inl h1
        · right
          refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
          · rw [gateAtL_append_lt _ _ _ hj]; exact hop
          · rw [gateAtL_append_lt _ _ _ hj]
            intro t ht
            exact hSub b' (hin t ht)
    · simp only [hbb, ite_false] at hw
      rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
      · exact Or.inl h1
      · right
        refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
        · rw [gateAtL_append_lt _ _ _ hj]; exact hop
        · rw [gateAtL_append_lt _ _ _ hj]
          intro t ht
          simp only [hbb, ite_false]
          exact hin t ht
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      rcases hAnd j hlt hop with ⟨a, c, hin, ha, hc⟩
      exact ⟨a, c, hin, hSub false ha, hSub true hc⟩
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_or_top {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) {u v : ℕ} (hu : u < x1 + x2 + gs.length) (hv : v < x1 + x2 + gs.length) :
    Good x1 x2 S (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b w hw; omega
  · intro b w hw
    rcases hSide b w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_and {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) {a c : ℕ} (ha : a ∈ S false) (hc : c ∈ S true) :
    Good x1 x2 S (gs ++ [⟨GateOp.and, [a, c]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have ha_lt : a < x1 + x2 + gs.length := hLt false a ha
  have hc_lt : c < x1 + x2 + gs.length := hLt true c hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inl rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b' w hw; omega
  · intro b' w hw
    rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self]
      exact ⟨a, c, rfl, ha, hc⟩

private lemma addOrInSide {x1 x2 : ℕ} (b : Bool) (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u ∈ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S' gs' ∧
        (∀ b', S b' ⊆ S' b') ∧
        w ∈ S' b ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨S, gs, u, by simp, hG, fun _ => Finset.Subset.rfl, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t ∈ S b := fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
      have hu1 : u ∈ S1 b := hSub1 b (hws u (by simp))
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      let S2 : Bool → Finset ℕ := fun b' => if b' = b then insert w (S1 b') else S1 b'
      have hG2 : Good x1 x2 S2 gs2 := good_append_or_side hG1 b hu1 hw1
      have hSub2 : ∀ b', S b' ⊆ S2 b' := by
        intro b'
        refine Finset.Subset.trans (hSub1 b') ?_
        by_cases hbb : b' = b
        · simp [S2, hbb]
        · simp [S2, hbb]
      have hw2 : w ∈ S2 b := by simp [S2]
      have hu_lt : u < x1 + x2 + gs.length := hG.2.2.1 b u (hws u (by simp))
      refine ⟨S2, gs2, w, ?_, hG2, hSub2, hw2, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private lemma addOrTop {x1 x2 : ℕ} (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u < x1 + x2 + gs.length) →
      ∃ (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S gs' ∧
        w < x1 + x2 + gs'.length ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨gs, u, by simp, hG, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t < x1 + x2 + gs.length :=
        fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨gs1, w1, hlen1, hG1, hw1, hPres1, hVal1⟩
      have hu_lt : u < x1 + x2 + gs.length := hws u (by simp)
      have hu1 : u < x1 + x2 + gs1.length := by omega
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      have hG2 : Good x1 x2 S gs2 := good_append_or_top hG1 hu1 hw1
      refine ⟨gs2, w, ?_, hG2, ?_, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · simp [gs2, w]
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private abbrev Star (x1 x2 : ℕ) := (Fin x1 × List (Fin x2)) ⊕ (Fin x2 × List (Fin x1))

private def starSize {x1 x2 : ℕ} : Star x1 x2 → ℕ
  | Sum.inl (_, ls) => ls.length
  | Sum.inr (_, ps) => ps.length

private def starEval {x1 x2 : ℕ} (z : Fin (x1 + x2) → Bool) : Star x1 x2 → Bool
  | Sum.inl (p, ls) => z (Fin.castAdd x2 p) && ls.any (fun l => z (Fin.natAdd x1 l))
  | Sum.inr (l, ps) => ps.any (fun p => z (Fin.castAdd x2 p)) && z (Fin.natAdd x1 l)

private lemma wireVal_input_left {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (p : Fin x1) :
    wireVal (x1 + x2) gs z p.1 = z (Fin.castAdd x2 p) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : p.1 < x1 + x2 := by omega
    rw [getD_ofFn z p.1 hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma wireVal_input_right {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (l : Fin x2) :
    wireVal (x1 + x2) gs z (x1 + l.1) = z (Fin.natAdd x1 l) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : x1 + l.1 < x1 + x2 := by omega
    rw [getD_ofFn z (x1 + l.1) hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma addStar {x1 x2 : ℕ} (st : Star x1 x2) (hpos : 0 < starSize st)
    (S : Bool → Finset ℕ) (gs : List Gate)
    (hG : Good x1 x2 S gs) (hBase : ∀ b, S0 x1 x2 b ⊆ S b) :
    ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
      gs'.length = gs.length + starSize st ∧
      Good x1 x2 S' gs' ∧
      (∀ b, S b ⊆ S' b) ∧
      w < x1 + x2 + gs'.length ∧
      (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
      (∀ z, wireVal (x1 + x2) gs' z w = starEval z st) := by
  cases st with
  | inl pl =>
    rcases pl with ⟨p, ls⟩
    have hne_ls : ls ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ls.map (fun l => x1 + l.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ls]
    have hws_mem : ∀ u ∈ ws, u ∈ S true := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨l, _, rfl⟩
      exact hBase true (mem_S0_true l)
    rcases addOrInSide true ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wL, hlen1, hG1, hSub1, hwL, hPres1, hVal1⟩
    have hp1 : p.1 ∈ S1 false := hSub1 false (hBase false (mem_S0_false p))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [p.1, wL]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 hp1 hwL
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ls.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_left, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun l : Fin x2 => wireVal (x1 + x2) gs z (x1 + l.1)) =
          (fun l : Fin x2 => z (Fin.natAdd x1 l)) := by
        funext l
        exact wireVal_input_right gs z l
      simp [Function.comp_def, hfn]
  | inr lp =>
    rcases lp with ⟨l, ps⟩
    have hne_ps : ps ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ps.map (fun p => p.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ps]
    have hws_mem : ∀ u ∈ ws, u ∈ S false := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨p, _, rfl⟩
      exact hBase false (mem_S0_false p)
    rcases addOrInSide false ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wP, hlen1, hG1, hSub1, hwP, hPres1, hVal1⟩
    have hl1 : x1 + l.1 ∈ S1 true := hSub1 true (hBase true (mem_S0_true l))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [wP, x1 + l.1]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 hwP hl1
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ps.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_right, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun p : Fin x1 => wireVal (x1 + x2) gs z p.1) =
          (fun p : Fin x1 => z (Fin.castAdd x2 p)) := by
        funext p
        exact wireVal_input_left gs z p
      simp [Function.comp_def, hfn]

private lemma addStars {x1 x2 : ℕ} (stars : List (Star x1 x2))
    (hpos : ∀ st ∈ stars, 0 < starSize st) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ b, S0 x1 x2 b ⊆ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (ws : List ℕ),
        gs'.length = gs.length + (stars.map starSize).sum ∧
        ws.length = stars.length ∧
        Good x1 x2 S' gs' ∧
        (∀ w ∈ ws, w < x1 + x2 + gs'.length) ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, ws.any (fun w => wireVal (x1 + x2) gs' z w) = stars.any (fun st => starEval z st)) := by
  induction stars with
  | nil =>
    intro S gs hG _
    refine ⟨S, gs, [], by simp, rfl, hG, by simp, ?_, ?_⟩
    · intro z i _; rfl
    · intro z; simp
  | cons st rest ih =>
    intro S gs hG hBase
    rcases addStar st (hpos st (by simp)) S gs hG hBase with
      ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
    have hBase1 : ∀ b, S0 x1 x2 b ⊆ S1 b := fun b => Finset.Subset.trans (hBase b) (hSub1 b)
    have hpos_rest : ∀ s ∈ rest, 0 < starSize s := fun s hs => hpos s (List.mem_cons_of_mem st hs)
    rcases ih hpos_rest S1 gs1 hG1 hBase1 with
      ⟨S2, gs2, ws2, hlen2, hwslen2, hG2, hws2_lt, hPres2, hVal2⟩
    refine ⟨S2, gs2, w1 :: ws2, ?_, ?_, hG2, ?_, ?_, ?_⟩
    · simp [hlen2, hlen1, Nat.add_assoc]
    · simp [hwslen2]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact hws2_lt w hw
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [hPres2 z i hi1]
      exact hPres1 z i hi
    · intro z
      simp only [List.any_cons]
      rw [hPres2 z w1 hw1, hVal1 z, hVal2 z]

private lemma circuit_from_good {x1 x2 : ℕ} (S : Bool → Finset ℕ) (gs : List Gate) (out : ℕ)
    (hG : Good x1 x2 S gs) :
    let C : Circuit := ⟨gs, out⟩
    IsAO2 (x1 + x2) C ∧
    (∀ b : Bool, ∀ w ∈ S b,
      (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
      ∃ j < C.size, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
        ∀ u ∈ (gateAt C j).inputs, u ∈ S b) ∧
    (∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ a c : ℕ, (gateAt C j).inputs = [a, c] ∧ a ∈ S false ∧ c ∈ S true) := by
  rcases hG with ⟨hAO, hRB, _, hSide, hAnd⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg; exact (hAO g hg).1
  · intro j hj i hi; exact hRB j hj i hi
  · intro g hg; exact (hAO g hg).2
  · intro b w hw; exact hSide b w hw
  · intro j hj hop; exact hAnd j hj hop

end A3692

open A3692 in
theorem t3692 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),   (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),       PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧         x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧           (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x3 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) ∧             have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7;             (∀ (x10 : Bool), ∀ x11 ∈ x8 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨ ∃ x13 < x7.size, x11 = x1 + x2 + x13 ∧ (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧ ∀ x10 < x7.size, (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 Bool.false ∧ x14 ∈ x8 Bool.true := by
  intro x1 x2 E A B hcov
  by_cases hE : E = ∅
  · subst hE
    refine ⟨⟨[], x1 + x2⟩, fun _ => ∅, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg; cases hg
      · intro j hj; simp at hj
      · intro g hg; cases hg
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro z
      simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_nil, Finset.notMem_empty,
        false_and, exists_false, decide_false]
      exact getD_of_ge (List.ofFn z) (x1 + x2) (by simp)
    · intro b w hw; simp at hw
    · intro j hj; simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hj
  · have hE_ne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
    let NA : Fin x1 → Finset (Fin x2) := fun p => Finset.univ.filter (fun l => (p, l) ∈ E)
    let NB : Fin x2 → Finset (Fin x1) := fun l => Finset.univ.filter (fun p => (p, l) ∈ E ∧ p ∉ A)
    let A' : Finset (Fin x1) := A.filter (fun p => (NA p).Nonempty)
    let B' : Finset (Fin x2) := B.filter (fun l => (NB l).Nonempty)
    let starsA : List (Star x1 x2) := A'.toList.map (fun p => Sum.inl (p, (NA p).toList))
    let starsB : List (Star x1 x2) := B'.toList.map (fun l => Sum.inr (l, (NB l).toList))
    let stars : List (Star x1 x2) := starsA ++ starsB
    have hpos : ∀ st ∈ stars, 0 < starSize st := by
      intro st hst
      simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
      rcases hst with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hp).2
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hl).2
    have hsumA : (starsA.map starSize).sum = ∑ p ∈ A', (NA p).card := by
      have h1 : (starsA.map starSize) = A'.toList.map (fun p => (NA p).card) := by
        simp [starsA, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hsumB : (starsB.map starSize).sum = ∑ l ∈ B', (NB l).card := by
      have h1 : (starsB.map starSize) = B'.toList.map (fun l => (NB l).card) := by
        simp [starsB, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hcardE : (∑ p ∈ A', (NA p).card) + (∑ l ∈ B', (NB l).card) = E.card := by
      let EA : Finset (Fin x1 × Fin x2) := A'.biUnion (fun p => (NA p).image (fun l => (p, l)))
      let EB : Finset (Fin x1 × Fin x2) := B'.biUnion (fun l => (NB l).image (fun p => (p, l)))
      have hEA_card : EA.card = ∑ p ∈ A', (NA p).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro p _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
        · intro p1 _ p2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨l1, _, rfl⟩
          rcases he2 with ⟨l2, _, heq⟩
          exact hne (Prod.mk.inj heq).1.symm
      have hEB_card : EB.card = ∑ l ∈ B', (NB l).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro l _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)
        · intro l1 _ l2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨p1, _, rfl⟩
          rcases he2 with ⟨p2, _, heq⟩
          exact hne (Prod.mk.inj heq).2.symm
      have hdisj : Disjoint EA EB := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        simp only [EA, EB, Finset.mem_biUnion, Finset.mem_image] at he1 he2
        rcases he1 with ⟨p1, hp1, l1, _, rfl⟩
        rcases he2 with ⟨l2, _, p2, hp2, heq⟩
        have hp_eq : p2 = p1 := (Prod.mk.inj heq).1
        subst hp_eq
        have hp1A : p2 ∈ A := (Finset.mem_filter.mp hp1).1
        have hp2nA : p2 ∉ A := (Finset.mem_filter.mp hp2).2.2
        exact hp2nA hp1A
      have hunion : EA ∪ EB = E := by
        ext ⟨p, l⟩
        simp only [EA, EB, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro (⟨p1, _, l1, hl1, heq⟩ | ⟨l1, _, p1, hp1, heq⟩)
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hl1).2
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hp1).2.1
        · intro hpl
          by_cases hpA : p ∈ A
          · left
            refine ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩,
              l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, rfl⟩
          · right
            have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
            refine ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩,
              p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, rfl⟩
      rw [← hEA_card, ← hEB_card, ← Finset.card_union_of_disjoint hdisj, hunion]
    have hsum_stars : (stars.map starSize).sum = E.card := by
      simp only [stars, List.map_append, List.sum_append, hsumA, hsumB, hcardE]
    have hstars_len : stars.length = A'.card + B'.card := by
      simp [stars, starsA, starsB]
    have hstars_ne : stars ≠ [] := by
      intro hnil
      have h0 : E.card = 0 := by
        rw [← hsum_stars, hnil]; rfl
      exact (Finset.card_pos.mpr hE_ne).ne' h0
    rcases addStars stars hpos (S0 x1 x2) [] (good_init x1 x2) (fun _ => Finset.Subset.rfl) with
      ⟨S1, gs1, ws1, hlen1, hwslen1, hG1, hws1_lt, _, hVal1⟩
    have hws1_ne : ws1 ≠ [] := by
      intro hnil
      apply hstars_ne
      apply List.eq_nil_of_length_eq_zero
      rw [← hwslen1, hnil]
      rfl
    rcases addOrTop ws1 hws1_ne S1 gs1 hG1 hws1_lt with
      ⟨gs2, wOut, hlen2, hG2, _, hPres2, hVal2⟩
    let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs2, wOut⟩
    have hC := circuit_from_good S1 gs2 wOut hG2
    refine ⟨C, S1, hC.1, ?_, ?_, hC.2.1, hC.2.2⟩
    · have hA' : A'.card ≤ A.card := Finset.card_filter_le _ _
      have hB' : B'.card ≤ B.card := Finset.card_filter_le _ _
      have hk_pos : 1 ≤ ws1.length := by
        cases ws1 with
        | nil => exact absurd rfl hws1_ne
        | cons _ _ => simp
      simp only [C, PEqualNP.CircuitLowerBounds.Circuit.size, hlen2, hlen1, List.length_nil,
        Nat.zero_add, hsum_stars, hwslen1, hstars_len]
      omega
    · intro z
      have hcf : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C z = wireVal (x1 + x2) gs2 z wOut := rfl
      rw [hcf, hVal2 z, hVal1 z]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨st, hst, hst_eval⟩
        simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
        rcases hst with ⟨p, _, rfl⟩ | ⟨l, _, rfl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨hzp, l, hl, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hl).2, hzp, hzl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨⟨p, hp, hzp⟩, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hp).2.1, hzp, hzl⟩
      · rintro ⟨p, l, hpl, hzp, hzl⟩
        by_cases hpA : p ∈ A
        · refine ⟨Sum.inl (p, (NA p).toList), ?_, ?_⟩
          · simp only [stars, starsA, List.mem_append, List.mem_map, Finset.mem_toList]
            left
            exact ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨hzp, l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, hzl⟩
        · have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
          refine ⟨Sum.inr (l, (NB l).toList), ?_, ?_⟩
          · simp only [stars, starsB, List.mem_append, List.mem_map, Finset.mem_toList]
            right
            exact ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, hzp⟩, hzl⟩

namespace B6579

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadK PEqualNP.TopForm

def s2230_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2230_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2230_stepWire x := rfl

lemma s2230_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2230_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepWire]
    omega

lemma s2230_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2230_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepWire w g).length := by simp [s2230_stepWire]; omega
    rw [ih (s2230_stepWire w g) hlt]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2230_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2230_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_length, List.length_ofFn]

lemma s2230_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2230_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2230_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2230_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2230_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2230_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2230_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2230_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2230_foldl_stepWire_length, hpre_len]
  have hCj : s2230_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2230_foldl_stepWire_getD_lt post (s2230_stepWire w0 gj) (n + k) (by simp [s2230_stepWire]; omega)]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2230_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2230_getD_ge_length w0 i (by omega)

lemma s2230_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2230_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2230_W]
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]


def s2230_FR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def s2230_stepR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [s2230_FR S k R g]

lemma s2230_readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) := by
  first
    | rfl
    | (unfold readVectors; congr 1; funext R g; rcases g with ⟨op, ins⟩; cases op <;> rfl)

lemma s2230_FR_or (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) (h : g.op = GateOp.or) :
    s2230_FR S k R g =
      (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) [] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.or := h
  subst h2
  rfl

lemma s2230_FR_and (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate)
    (h : g.op = GateOp.and) :
    s2230_FR S k R g = (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.and := h
  subst h2
  rfl

lemma s2230_foldR_length (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    (gs.foldl (s2230_stepR S k) R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepR]
    omega

lemma s2230_foldR_getD_lt (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ)
    (hi : i < R.length) : (gs.foldl (s2230_stepR S k) R).getD i [] = R.getD i [] := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepR S k R g).length := by simp [s2230_stepR]; omega
    rw [ih (s2230_stepR S k R g) hlt]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def s2230_RV (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

lemma s2230_RV_input (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : w < n) :
    s2230_RV C n S k w = leafVectors S k w := by
  simp only [s2230_RV]
  rw [s2230_readVectors_eq, s2230_foldR_getD_lt S k C.gates ((List.range n).map (leafVectors S k)) w
    (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma s2230_RV_gate (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j : ℕ) (hj : j < C.gates.length) :
    ∃ Rp : List (List (List ℕ)),
      (∀ i, i < n + j → Rp.getD i [] = s2230_RV C n S k i) ∧
      s2230_RV C n S k (n + j) = s2230_FR S k Rp (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [s2230_gateAt_eq C j hj]; exact hgj
  rw [hga]
  obtain ⟨Rp, hRp⟩ : ∃ Rp, Rp = pre.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) :=
    ⟨_, rfl⟩
  have hlen : Rp.length = n + j := by
    rw [hRp, s2230_foldR_length]
    simp only [List.length_map, List.length_range, hpre_len]
  have hall : readVectors C n S k = post.foldl (s2230_stepR S k) (s2230_stepR S k Rp gj) := by
    rw [s2230_readVectors_eq, hgs, List.foldl_append, List.foldl_cons, hRp]
  have hlen1 : (s2230_stepR S k Rp gj).length = n + j + 1 := by
    simp [s2230_stepR, hlen]
  refine ⟨Rp, ?_, ?_⟩
  · intro i hi
    simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) i (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < Rp.length by omega)]
  · simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) (n + j) (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, hlen]

lemma s2230_mem_foldl_insertNew (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ L.foldl insertNew acc) : v ∈ acc ∨ v ∈ L := by
  induction L generalizing acc with
  | nil => exact Or.inl h
  | cons x L ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h1 | h1
    · unfold insertNew at h1
      split_ifs at h1
      · exact Or.inl h1
      · rcases List.mem_append.1 h1 with h2 | h2
        · exact Or.inl h2
        · have h3 : v = x := by simpa using h2
          exact Or.inr (by simp [h3])
    · exact Or.inr (List.mem_cons_of_mem _ h1)

lemma s2230_mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) (h : v ∈ andStep k A B) :
    ∃ u ∈ A, ∃ u2 ∈ B, v = capAdd k u u2 := by
  unfold andStep at h
  rcases s2230_mem_foldl_insertNew _ _ _ h with h1 | h1
  · simp at h1
  · simp only [List.mem_flatMap, List.mem_map] at h1
    obtain ⟨u, hu, u2, hu2, rfl⟩ := h1
    exact ⟨u, hu, u2, hu2, rfl⟩

lemma s2230_capAdd_pair (k x1 y1 x2 y2 : ℕ) :
    capAdd k [x1, y1] [x2, y2] = [min (x1 + x2) (k + 1), min (y1 + y2) (k + 1)] := by
  first
    | rfl
    | simp [capAdd]

lemma s2230_leaf_eq (a b w : ℕ) :
    leafVectors [a, b] 1 w =
      if w ∈ [a, b] then [[if a = w then 1 else 0, if b = w then 1 else 0]] else [] := by
  first
    | rfl
    | (unfold leafVectors; simp)


lemma mem_foldl_insertNew_of_acc (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ acc) : v ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil => exact h
  | cons x L ih =>
    rw [List.foldl_cons]
    apply ih
    unfold insertNew
    split_ifs
    · exact h
    · exact List.mem_append_left _ h

lemma mem_foldl_insertNew_of_mem (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ L) : v ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil => simp at h
  | cons x L ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with h1 | h1
    · apply mem_foldl_insertNew_of_acc
      subst h1
      unfold insertNew
      split_ifs with h2
      · exact h2
      · simp
    · exact ih _ h1

lemma mem_andStep_of (k : ℕ) (A B : List (List ℕ)) (u u2 : List ℕ) (hu : u ∈ A) (hu2 : u2 ∈ B) :
    capAdd k u u2 ∈ andStep k A B := by
  unfold andStep
  apply mem_foldl_insertNew_of_mem
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨u, hu, u2, hu2, rfl⟩

lemma mem_orFold (As : List (List (List ℕ))) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ acc ∨ ∃ A ∈ As, v ∈ A) :
    v ∈ As.foldl (fun acc A => A.foldl insertNew acc) acc := by
  induction As generalizing acc with
  | nil =>
    rcases h with h | ⟨A, hA, _⟩
    · exact h
    · simp at hA
  | cons A0 As ih =>
    rw [List.foldl_cons]
    apply ih
    rcases h with h | ⟨A, hA, hv⟩
    · exact Or.inl (mem_foldl_insertNew_of_acc _ _ _ h)
    · rcases List.mem_cons.1 hA with h1 | h1
      · subst h1
        exact Or.inl (mem_foldl_insertNew_of_mem _ _ _ hv)
      · exact Or.inr ⟨A, h1, hv⟩

lemma capAdd_map (L : List ℕ) (f g : ℕ → ℕ) (k : ℕ) :
    capAdd k (L.map f) (L.map g) = L.map (fun j => min (f j + g j) (k + 1)) := by
  unfold capAdd
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]

def uv (L : List ℕ) (i : ℕ) : List ℕ := L.map fun j => if j = i then min 1 (1 + 1) else 0

lemma mem_setList {n : ℕ} (S : Finset (Fin n)) (w : ℕ) (hw : w < n) (h : (⟨w, hw⟩ : Fin n) ∈ S) :
    w ∈ setList S := by
  unfold setList
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  exact ⟨⟨w, hw⟩, h, rfl⟩

theorem inv (x1 x2 : ℕ) (C : Circuit) (x4 : Bool → Finset ℕ) (hC : IsAO2 (x1 + x2) C)
    (hx4 : ∀ (b : Bool), ∀ w ∈ x4 b, (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
      ∃ j < C.size, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
        ∀ i ∈ (gateAt C j).inputs, i ∈ x4 b)
    (hand : ∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ (a : ℕ) (c : ℕ), (gateAt C j).inputs = [a, c] ∧ a ∈ x4 false ∧ c ∈ x4 true)
    (S : Finset (Fin (x1 + x2))) :
    ∀ w, s2230_W (x1 + x2) C (setInput S) w = true →
      (∃ v ∈ s2230_RV C (x1 + x2) (setList S) 1 w, ∀ a ∈ v, a ≤ 1) ∧
      (∀ b, w ∈ x4 b → ∃ i, decide (x1 ≤ i) = b ∧
        uv (setList S) i ∈ s2230_RV C (x1 + x2) (setList S) 1 w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  obtain ⟨hAO, hRB, _⟩ := hC
  by_cases hwn : w < x1 + x2
  · have hS : (⟨w, hwn⟩ : Fin (x1 + x2)) ∈ S := by
      rw [s2230_W_input (x1 + x2) C _ w hwn] at hw
      simpa [setInput] using hw
    have hmem : w ∈ setList S := mem_setList S w hwn hS
    have hRV : s2230_RV C (x1 + x2) (setList S) 1 w = [uv (setList S) w] := by
      rw [s2230_RV_input C (x1 + x2) (setList S) 1 w hwn]
      unfold leafVectors uv
      rw [if_pos hmem]
    refine ⟨⟨uv (setList S) w, by rw [hRV]; exact List.mem_singleton_self _, ?_⟩, ?_⟩
    · intro a ha
      unfold uv at ha
      simp only [List.mem_map] at ha
      obtain ⟨j, _, rfl⟩ := ha
      split_ifs <;> omega
    · intro b hb
      refine ⟨w, ?_, by rw [hRV]; exact List.mem_singleton_self _⟩
      rcases hx4 b w hb with ⟨_, hside⟩ | ⟨j, _, hj, _⟩
      · exact hside
      · omega
  · by_cases hwl : w < x1 + x2 + C.gates.length
    swap
    · exfalso
      have hf : s2230_W (x1 + x2) C (setInput S) w = false := by
        unfold s2230_W
        exact s2230_getD_ge_length _ _ (by rw [s2230_wires_length]; omega)
      rw [hf] at hw
      exact Bool.false_ne_true hw
    obtain ⟨j, rfl⟩ : ∃ j, w = x1 + x2 + j := ⟨w - (x1 + x2), by omega⟩
    have hj : j < C.gates.length := by omega
    have hgW := s2230_W_gate (x1 + x2) C (setInput S) j hj
    obtain ⟨Rp, hRp, hRVj⟩ := s2230_RV_gate C (x1 + x2) (setList S) 1 j hj
    have hRB' : ∀ i ∈ (gateAt C j).inputs, i < x1 + x2 + j := hRB j hj
    have hmapW : ((gateAt C j).inputs.map fun i =>
        if i < x1 + x2 + j then s2230_W (x1 + x2) C (setInput S) i else false) =
        (gateAt C j).inputs.map fun i => s2230_W (x1 + x2) C (setInput S) i := by
      refine List.map_congr_left fun i hi => ?_
      rw [if_pos (hRB' i hi)]
    have hmapR : ((gateAt C j).inputs.map fun i => Rp.getD i []) =
        (gateAt C j).inputs.map fun i => s2230_RV C (x1 + x2) (setList S) 1 i := by
      refine List.map_congr_left fun i hi => ?_
      exact hRp i (hRB' i hi)
    have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
      hAO (gateAt C j) (by rw [s2230_gateAt_eq C j hj]; exact List.getElem_mem hj)
    have hor_true : (gateAt C j).op = GateOp.or →
        ∃ i ∈ (gateAt C j).inputs, s2230_W (x1 + x2) C (setInput S) i = true := by
      intro ho
      have hw' := hw
      rw [hgW, hmapW, ho] at hw'
      simpa [GateOp.eval] using hw'
    have hor_mem : (gateAt C j).op = GateOp.or → ∀ i ∈ (gateAt C j).inputs,
        ∀ v ∈ s2230_RV C (x1 + x2) (setList S) 1 i,
          v ∈ s2230_RV C (x1 + x2) (setList S) 1 (x1 + x2 + j) := by
      intro ho i hi v hv
      rw [hRVj, s2230_FR_or _ _ _ _ ho, hmapR]
      apply mem_orFold
      exact Or.inr ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, hv⟩
    refine ⟨?_, ?_⟩
    · rcases hop with ho | ho
      · obtain ⟨a, c, hac, ha, hc⟩ := hand j hj ho
        have hw' := hw
        rw [hgW, hmapW, ho, hac] at hw'
        have hwa : s2230_W (x1 + x2) C (setInput S) a = true ∧
            s2230_W (x1 + x2) C (setInput S) c = true := by
          simpa [GateOp.eval] using hw'
        have hRBa : a < x1 + x2 + j := hRB' a (by rw [hac]; simp)
        have hRBc : c < x1 + x2 + j := hRB' c (by rw [hac]; simp)
        obtain ⟨ia, hia, hA⟩ := (ih a hRBa hwa.1).2 false ha
        obtain ⟨ic, hic, hCc⟩ := (ih c hRBc hwa.2).2 true hc
        have hne : ia ≠ ic := by
          rintro rfl
          rw [hia] at hic
          exact Bool.false_ne_true hic
        refine ⟨capAdd 1 (capAdd 1 ((setList S).map fun _ => 0) (uv (setList S) ia))
          (uv (setList S) ic), ?_, ?_⟩
        · rw [hRVj, s2230_FR_and _ _ _ _ ho, hmapR, hac]
          simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
          exact mem_andStep_of _ _ _ _ _
            (mem_andStep_of _ _ _ _ _ (List.mem_singleton_self _) hA) hCc
        · intro e he
          unfold uv at he
          rw [capAdd_map, capAdd_map] at he
          simp only [List.mem_map] at he
          obtain ⟨t, _, rfl⟩ := he
          split_ifs <;> omega
      · obtain ⟨i, hi, hwi⟩ := hor_true ho
        obtain ⟨v, hv, hle⟩ := (ih i (hRB' i hi) hwi).1
        exact ⟨v, hor_mem ho i hi v hv, hle⟩
    · intro b hb
      rcases hx4 b _ hb with ⟨hlt, _⟩ | ⟨j', _, hjj, ho, hins⟩
      · omega
      · have hjj' : j' = j := by omega
        subst hjj'
        obtain ⟨i, hi, hwi⟩ := hor_true ho
        obtain ⟨ia, hia, hA⟩ := (ih i (hRB' i hi) hwi).2 b (hins i hi)
        exact ⟨ia, hia, hor_mem ho i hi _ hA⟩

end B6579

theorem t6579 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Bool → Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x3 → (∀ (x6 : Bool), ∀ x7 ∈ x4 x6, x7 < x1 + x2 ∧ Decidable.decide (x1 ≤ x7) = x6 ∨ ∃ x9 < x3.size, x7 = x1 + x2 + x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).inputs, x10 ∈ x4 x6) → (∀ x7 < x3.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).inputs = [x10, x11] ∧ x10 ∈ x4 Bool.false ∧ x11 ∈ x4 Bool.true) → PEqualNP.ReadK.IsReadK (x1 + x2) x3 (1 : ℕ) := by
  intro x1 x2 C x4 hC hx4 hand S hS
  have hout : PEqualNP.Outside.L_meta_2583.B6579.s2230_W (x1 + x2) C (PEqualNP.ReadK.setInput S)
      C.output = true := hS.1
  obtain ⟨⟨v, hv, hle⟩, _⟩ :=
    PEqualNP.Outside.L_meta_2583.B6579.inv x1 x2 C x4 hC hx4 hand S C.output hout
  unfold PEqualNP.ReadK.readsAtMost
  apply List.any_eq_true.2
  refine ⟨v, hv, ?_⟩
  apply List.all_eq_true.2
  intro a ha
  exact decide_eq_true (hle a ha)

lemma readOneCover : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧ (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) ∧ PEqualNP.ReadK.IsReadK (x1 + x2) x7 (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 hcov
  obtain ⟨C, F, hao, hsize, hfun, hF1, hF2⟩ := PEqualNP.Outside.L_meta_2583.t3692 x1 x2 x3 x4 x5 hcov
  exact ⟨C, hao, hsize, hfun, PEqualNP.Outside.L_meta_2583.t6579 x1 x2 C F hao hF1 hF2⟩


lemma incidence_readOne_upper (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (N + N) D ∧
      D.size ≤ (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card + N - 1 ∧
      (∀ y : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) D y =
          decide (∃ p l : Fin N, I p l ∧
            y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧
      PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  classical
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  obtain ⟨D, hao, hsize, hfun, hread⟩ := readOneCover N N E Finset.univ ∅
    (fun e he => Or.inl (Finset.mem_univ e.1))
  refine ⟨D, hao, ?_, ?_, hread⟩
  · simpa using hsize
  · intro y
    simpa [E] using hfun y

lemma incidence_edge_card (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hcard : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card = N * (q + 1) := by
  classical
  calc
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card =
        ∑ e : Fin N × Fin N, if I e.1 e.2 then 1 else 0 := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ l : Fin N, ∑ p : Fin N, if I p l then 1 else 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ l : Fin N, (Finset.univ.filter (fun p => I p l)).card := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = N * (q + 1) := by simp [hcard]

lemma plane_readOne_upper (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hcard : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (N + N) D ∧
      D.size ≤ N * (q + 2) - 1 ∧
      (∀ y : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) D y =
          decide (∃ p l : Fin N, I p l ∧
            y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧
      PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  obtain ⟨D, hao, hsize, hfun, hread⟩ := incidence_readOne_upper N I
  refine ⟨D, hao, ?_, hfun, hread⟩
  rw [incidence_edge_card q N I hcard] at hsize
  have hnum : N * (q + 1) + N = N * (q + 2) := by ring
  simpa only [hnum] using hsize

end PEqualNP.Outside.L_meta_2583


-- The live-wire count and meeting-gate proof adapt checked L_meta_614 to pair evaluations.
namespace PEqualNP.Outside.L_meta_2583_aux.LibraryLower.GraphProof

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
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n+p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

theorem next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a ≤ b := by
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
  | refl =>
    intro d q
    exact Or.inr q
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
    · let i : Fin n := ⟨j,hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n+C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n+p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n+p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n+p) := ⟨hlt,p,g,hg,rfl,ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha',hs,hj⟩⟩

end PEqualNP.Outside.L_meta_2583_aux.LibraryLower.GraphProof


namespace PEqualNP.Outside.L_meta_2583_aux.LibraryLower.GraphProof

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
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
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
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

def point (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

theorem point_mono {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

theorem point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

def Carries (C : Circuit) (v : Fin n) (a : ℕ) : Prop :=
  val C (point {v}) a ≠ val C (point (∅ : Finset (Fin n))) a

theorem carries_iff (hC : Monotone2 C) {v : Fin n} {a : ℕ} :
    Carries C v a ↔
      val C (point {v}) a = true ∧ val C (point (∅ : Finset (Fin n))) a = false := by
  have hm := acts_mono hC (point_mono (Finset.empty_subset {v})) a
  unfold Carries
  cases ha : val C (point {v}) a <;>
    cases hb : val C (point (∅ : Finset (Fin n))) a <;> simp_all

theorem singleton_path {v : Fin n} {a : ℕ} (ha : Live n C a) (hd : Carries C v a) :
    Trace n C (Carries C v) v.val a := by
  obtain ⟨i, hi, hpath⟩ := difference C (point {v}) (point ∅) a ha hd
  have e : i = v := by
    by_contra h
    exact hi (by simp [point, h])
  exact e ▸ hpath

theorem influence {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b ≤ j ∧ val C x b ≠ val C y b) := by
  obtain ⟨i, hi, trace⟩ := difference C x y j hj hd
  have e : i = v := by
    by_contra h
    exact hi (agrees i h)
  subst i
  rcases align path unique j trace with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨trace_le hb, trace_start hb hd⟩

noncomputable def readers (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (fun b => LNext n C a b)

theorem next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

theorem mem_readers {a b : ℕ} : b ∈ readers n C a ↔ LNext n C a b := by
  classical
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨next_in_range h.1, h⟩⟩

def Branch (n : ℕ) (C : Circuit) (a : ℕ) : Prop := 2 ≤ (readers n C a).card

theorem nonbranch_unique {a j j' : ℕ} (h : ¬ Branch n C a)
    (hj : LNext n C a j) (hj' : LNext n C a j') : j = j' := by
  apply Finset.card_le_one_iff.1 (show (readers n C a).card ≤ 1 from by
    unfold Branch at h; omega) (mem_readers.2 hj) (mem_readers.2 hj')

def Eligible (C : Circuit) (v : Fin n) : Prop := ∃ b, Live n C b ∧ Carries C v b ∧ Branch n C b

noncomputable def firstBranch (C : Circuit) (v : Fin n) (h : Eligible C v) : ℕ := by
  classical exact Nat.find h

theorem firstBranch_spec (v : Fin n) (h : Eligible C v) :
    Live n C (firstBranch C v h) ∧ Carries C v (firstBranch C v h) ∧ Branch n C (firstBranch C v h) := by
  classical exact Nat.find_spec h

theorem firstBranch_unique (v : Fin n) (h : Eligible C v) :
    ∀ a j j', a < firstBranch C v h → Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  classical
  intro a j j' hl hc hj hj'
  apply nonbranch_unique _ hj hj'
  intro hb
  exact (Nat.not_le_of_gt hl) (Nat.find_min' h ⟨live_before hj.1 hj.2,hc,hb⟩)

theorem no_eligible_unique {v : Fin n} (h : ¬ Eligible C v) :
    ∀ a j j', Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  intro a j j' hc hj hj'
  exact nonbranch_unique (fun hb => h ⟨a,live_before hj.1 hj.2,hc,hb⟩) hj hj'

end PEqualNP.Outside.L_meta_2583_aux.LibraryLower.GraphProof


namespace PEqualNP.Outside.L_meta_2583_aux.LibraryLower.GraphProof

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

def GraphEval (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v w : Fin n, val C (point {v,w}) C.output = true ↔ G.Adj v w

theorem point_pair (he : GraphEval C G) (v w : Fin n) :
    val C (point {v,w}) C.output = true ↔ G.Adj v w := he v w

theorem point_contains_edge (hC : Monotone2 C) (he : GraphEval C G)
    {u v : Fin n} {S : Finset (Fin n)} (hu : u ∈ S) (hv : v ∈ S) (edge : G.Adj u v) :
    val C (point S) C.output = true :=
  acts_mono hC (point_mono (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv)))
    C.output ((he u v).mpr edge)

theorem point_pair_quiet (he : GraphEval C G) {v w : Fin n} (hn : ¬ G.Adj v w) :
    val C (point {v,w}) C.output = false := by
  rw [← Bool.not_eq_true, point_pair he]
  exact hn

theorem point_single_quiet (he : GraphEval C G) (v : Fin n) :
    val C (point {v}) C.output = false := by
  simpa using point_pair_quiet he (G.irrefl (v := v))

theorem edge_at_output (he : GraphEval C G) {v w : Fin n} (hvw : G.Adj v w) :
    n ≤ C.output ∧ C.output < n+C.gates.length := by
  have hp := (point_pair he v w).2 hvw
  constructor
  · by_contra! hl
    let i : Fin n := ⟨C.output,hl⟩
    have hv := point_single_quiet he i
    rw [show C.output = i.val from rfl,val_input] at hv
    simp [point] at hv
  · by_contra! hgt
    rw [val_beyond C _ hgt] at hp
    contradiction

theorem two_inputs {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hl : l.length ≤ 2) :
    ∀ i ∈ l, i = a ∨ i = b := by
  have hsub : ({a,b} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb
  have hcard : l.toFinset.card ≤ ({a,b} : Finset ℕ).card := by
    simpa [hne] using l.toFinset_card_le.trans hl
  have hEq := Finset.eq_of_subset_of_card_le hsub hcard
  intro i hi
  have hm : i ∈ ({a,b} : Finset ℕ) := hEq.symm ▸ (List.mem_toFinset.mpr hi)
  simpa using hm

theorem carries_separate (hC : Monotone2 C) {v w : Fin n} {a : ℕ}
    (h1 : val C (point {v}) a = true) (h0 : val C (point {w}) a = false) :
    Carries C v a ∧ ¬ Carries C w a := by
  have hb : val C (point (∅ : Finset (Fin n))) a = false := by
    rw [← Bool.not_eq_true]
    intro hc
    have hh := acts_mono hC (point_mono (Finset.empty_subset {w})) a hc
    rw [h0] at hh
    contradiction
  rw [carries_iff hC,carries_iff hC]
  simp [h1,h0,hb]

theorem meeting_gate (hC : Monotone2 C) (he : GraphEval C G) {v w : Fin n}
    (hvw : G.Adj v w) :
    ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ Live n C (n+p) ∧
      LNext n C a (n+p) ∧ LNext n C b (n+p) ∧
      Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
      (∀ i ∈ g.inputs, i = a ∨ i = b) := by
  classical
  let P (i : ℕ) := Live n C i ∧ val C (point {v,w}) i = true ∧
    val C (point {v}) i = false ∧ val C (point {w}) i = false
  have hex : ∃ i, P i :=
    ⟨C.output, .refl, (point_pair he v w).2 hvw, point_single_quiet he v, point_single_quiet he w⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have earlier (i : ℕ) (hlt : i < j) (hl : Live n C i)
      (htrue : val C (point {v,w}) i = true) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    by_contra! h
    have h' : P i := ⟨hl, htrue, by simpa using h.1, by simpa using h.2⟩
    exact (Nat.not_le_of_gt hlt) (Nat.find_min' hex h')
  have hge : n ≤ j := by
    by_contra! hh
    let i : Fin n := ⟨j,hh⟩
    obtain ⟨_,ht,hv,hw⟩ := hj
    rw [show j = i.val from rfl,val_input] at ht hv hw
    simp only [point,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with h | h
    · simp [point,h] at hv
    · simp [point,h] at hw
  have hlt : j < n+C.gates.length := by
    by_contra! hh
    have ht := hj.2.1
    rw [val_beyond C _ hh] at ht
    contradiction
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have ep : n+p = j := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hl := hC g (List.mem_of_getElem? hg)
  have hh : Live n C (n+p) := ep ▸ hj.1
  have hs1 : val C (point {v,w}) (n+p) = true := ep ▸ hj.2.1
  have hs2 : val C (point {v}) (n+p) = false := ep ▸ hj.2.2.1
  have hs3 : val C (point {w}) (n+p) = false := ep ▸ hj.2.2.2
  have reads (i : ℕ) (hi : i < n+p) (hm : i ∈ g.inputs) : LNext n C i (n+p) :=
    ⟨⟨hi,p,g,hg,rfl,hm⟩,hh⟩
  have hAnd : g.op = GateOp.and := by
    rcases hl.1 with h | h
    · exact h
    have hop : g.op = GateOp.or := h
    simp only [val_gate C _ hg, hop, GateOp.eval, List.any_map, Function.comp_apply, id,
      List.any_eq_true] at hs1
    obtain ⟨i,hi,ht⟩ := hs1
    have hi' : i < n+p := by
      by_contra hh'
      simp [operand,hh'] at ht
    have ht' : val C (point {v,w}) i = true := by simpa [operand,hi'] using ht
    rcases earlier i (ep ▸ hi') (live_before (reads i hi' hi).1 hh) ht' with hV | hW
    · have hs := hs2
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hV⟩).elim
    · have hs := hs3
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hW⟩).elim
  have hAll : ∀ i ∈ g.inputs, operand C (point {v,w}) (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hs1
  have hFalse (x : Fin n → Bool) (hX : val C x (n+p) = false) :
      ∃ i ∈ g.inputs, operand C x (n+p) i = false := by
    by_contra! h
    have ht : val C x (n+p) = true := by
      rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
      intro i hi
      simpa using h i hi
    rw [hX] at ht
    contradiction
  obtain ⟨a,ha,hwa⟩ := hFalse _ hs3
  obtain ⟨b,hb,hvb⟩ := hFalse _ hs2
  have before (i : ℕ) (h : i ∈ g.inputs) : i < n+p := by
    by_contra hi
    have hX := hAll i h
    simp [operand,hi] at hX
  have ha' := before a ha
  have hb' := before b hb
  rw [operand,ite_eq_left ha'] at hwa
  rw [operand,ite_eq_left hb'] at hvb
  have near (i : ℕ) (h : i ∈ g.inputs) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    have hi := before i h
    apply earlier i (ep ▸ hi) (live_before (reads i hi h).1 hh)
    simpa [operand,hi] using hAll i h
  have hva := (near a ha).resolve_right (by rw [hwa]; decide)
  have hwb := (near b hb).resolve_left (by rw [hvb]; decide)
  have hne : a ≠ b := fun e => Bool.noConfusion (hva.symm.trans (e ▸ hvb))
  exact ⟨p,g,a,b,hg,hAnd,hh,reads a ha' ha,reads b hb' hb,
    (carries_separate hC hva hwa).1,(carries_separate hC hva hwa).2,
    (carries_separate hC hwb hvb).1,(carries_separate hC hwb hvb).2,
    two_inputs ha hb hne hl.2⟩

theorem covers_edge (hC : Monotone2 C) (he : GraphEval C G) {v w a₀ b₀ : Fin n}
    (hvw : G.Adj v w) (ha₀ : G.Adj v a₀) (_ha₁ : a₀ ≠ w)
    (hb₀ : G.Adj w b₀) (_hb₁ : b₀ ≠ v) (hind : a₀ = b₀ ∨ ¬ G.Adj a₀ b₀) :
    Eligible C v ∨ Eligible C w := by
  by_contra! bad
  obtain ⟨p,g,a,b,hg,hAnd,hj,ha,hb,hva,hwa,hwb,hvb,hs⟩ := meeting_gate hC he hvw
  have pathV : Trace n C (Carries C v) v.val (n+p) :=
    (singleton_path (live_before ha.1 ha.2) hva).tail ⟨hva,ha⟩
  have pathW : Trace n C (Carries C w) w.val (n+p) :=
    (singleton_path (live_before hb.1 hb.2) hwb).tail ⟨hwb,hb⟩
  have uniqueV : ∀ k j j', k < n+p → Carries C v k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.1 k j j'
  have uniqueW : ∀ k j j', k < n+p → Carries C w k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.2 k j j'
  let S : Finset (Fin n) := {a₀,b₀}
  let x := point S
  let y := point (insert v S)
  let z := point (insert w S)
  have hzero : val C x C.output = false :=
    point_pair_quiet he (hind.elim (fun e => e ▸ G.irrefl (v := a₀)) id)
  have hY : val C y C.output = true := point_contains_edge hC he (u:=v) (v:=a₀) (by simp) (by simp [S]) ha₀
  have hZ : val C z C.output = true := point_contains_edge hC he (u:=w) (v:=b₀) (by simp) (by simp [S]) hb₀
  have jout := next_le hj
  have hvj := influence pathV uniqueV (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C y C.output from by rw [hzero,hY]; decide)
  have hwj := influence pathW uniqueW (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C z C.output from by rw [hzero,hZ]; decide)
  have hdiffV := (hvj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hdiffW := (hwj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hX : val C x (n+p) = false := by
    rw [← Bool.not_eq_true]
    intro htrue
    exact hdiffV (htrue.trans (acts_mono hC (point_mono (Finset.subset_insert _ _)) _ htrue).symm)
  have hyj : val C y (n+p) = true := by
    rw [hX] at hdiffV
    simpa using hdiffV.symm
  have hzj : val C z (n+p) = true := by
    rw [hX] at hdiffW
    simpa using hdiffW.symm
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
  have hYall : ∀ i ∈ g.inputs, operand C y (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hyj
  have hZall : ∀ i ∈ g.inputs, operand C z (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hzj
  have hin (i : ℕ) : LNext n C i (n+p) → i ∈ g.inputs := by
    rintro ⟨⟨_,k,g',he',hk,hmem⟩,_⟩
    have e : k=p := by omega
    subst k
    rw [hg] at he'
    cases he'
    exact hmem
  have hxA := hZall a (hin a ha)
  have hxB := hYall b (hin b hb)
  rw [operand,ite_eq_left ha.1.1,← hAX] at hxA
  rw [operand,ite_eq_left hb.1.1,← hBX] at hxB
  have hs' : val C x (n+p) = true := by
    rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
    intro i hi
    rcases hs i hi with rfl | rfl
    · simpa [Function.comp_apply,operand,ha.1.1] using hxA
    · simpa [Function.comp_apply,operand,hb.1.1] using hxB
  rw [hX] at hs'
  contradiction

end PEqualNP.Outside.L_meta_2583_aux.LibraryLower.GraphProof


namespace PEqualNP.Outside.L_meta_2583_aux.LibraryLower.GraphProof

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

theorem value_at_branch {v : Fin n} {x y : Fin n → Bool} (hv : Eligible C v)
    (agrees : ∀ i, i ≠ v → x i = y i)
    (hb : val C x (firstBranch C v hv) = val C y (firstBranch C v hv)) :
    val C x C.output = val C y C.output := by
  by_contra h
  have spec := firstBranch_spec v hv
  have path := singleton_path spec.1 spec.2.1
  rcases influence path (firstBranch_unique v hv) agrees ReflTransGen.refl h with bad | bad
  · exact (Nat.not_lt_of_ge (next_le spec.1)) bad.1
  · exact bad.2 hb

theorem branch_injective (hC : Monotone2 C) (he : GraphEval C G)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u))
    {v w : Fin n} (hv : Eligible C v) (hw : Eligible C w)
    (h : firstBranch C v hv = firstBranch C w hw) : v = w := by
  classical
  by_contra hne
  let b := firstBranch C v hv
  have hw_b : firstBranch C w hw = b := h.symm
  have hvtrue : val C (point {v}) b = true :=
    (carries_iff hC).1 (firstBranch_spec v hv).2.1 |>.1
  have hwtrue : val C (point {w}) b = true := by
    rw [← hw_b]
    exact (carries_iff hC).1 (firstBranch_spec w hw).2.1 |>.1
  by_cases hadj : G.Adj v w
  · have hbig : val C (point (insert w ({v} : Finset (Fin n)))) b = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) b hvtrue
    have eq := value_at_branch hw
      (x := point {v}) (y := point (insert w ({v} : Finset (Fin n))))
      (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hvtrue,hbig])
    have hy : val C (point (insert w ({v} : Finset (Fin n)))) C.output = true :=
      (point_pair he w v).2 (G.adj_symm hadj)
    rw [point_single_quiet he v,hy] at eq
    contradiction
  obtain ⟨u,hu⟩ := htwins v w hne hadj
  have hx : val C (point {v,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hvtrue
  have hy : val C (point {w,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hwtrue
  have hxyz : val C (point (insert w ({v,u} : Finset (Fin n)))) b = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) b hx
  have hEq : (insert w ({v,u} : Finset (Fin n))) = insert v {w,u} :=
    Finset.insert_comm _ _ _
  have e1 := value_at_branch hw
    (x := point {v,u}) (y := point (insert w ({v,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hx,hxyz])
  have e2 := value_at_branch hv
    (x := point {w,u}) (y := point (insert v ({w,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [← hEq]; exact hy.trans hxyz.symm)
  have e : val C (point {v,u}) C.output = val C (point {w,u}) C.output :=
    e1.trans (by rw [hEq,e2])
  apply hu
  rw [← point_pair he v u, ← point_pair he w u, e]

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

theorem mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

theorem input_live (he : GraphEval C G) {v u : Fin n} (hvu : G.Adj v u) :
    Live n C v.val := by
  have hx : val C (point {u}) C.output = false := point_single_quiet he u
  have hy : val C (point {v,u}) C.output = true := (point_pair he v u).2 hvu
  obtain ⟨i,hi,trace⟩ := difference C (point {u}) (point {v,u}) C.output ReflTransGen.refl
    (by rw [hx,hy]; decide)
  have ei : i=v := by
    by_contra h
    exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b,hb,_⟩
  · rw [h]
    exact .refl
  · exact live_before hb.2.1 hb.2.2

theorem live_readers_nonempty {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    (readers n C a).Nonempty := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b,mem_readers.2 ⟨hb,hpath⟩⟩

theorem readers_filter (a : ℕ) :
    open Classical in readers n C a = (living n C).filter (fun b => LNext n C a b) := by
  classical
  ext b
  simp only [mem_readers,Finset.mem_filter,mem_living]
  exact ⟨fun h => ⟨⟨next_in_range h.1,h.2⟩,h⟩, And.right⟩

theorem incoming_bound {j : ℕ} (hC : Monotone2 C) (hj : j ∈ living n C) :
    open Classical in ((living n C).filter fun i => LNext n C i j).card ≤ if j<n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_,⟨_,p,g,hg,hp,_⟩,_⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j=n+p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_,⟨_,q,g',hg',hq,hm⟩,_⟩ := Finset.mem_filter.1 ha
    have ep : p=q := by omega
    subst q
    rw [hg] at hg'
    cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)

theorem branch_budget (hC : Monotone2 C) (he : GraphEval C G)
    (hdegree : ∀ v : Fin n, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in n + ((living n C).filter (Branch n C)).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have hSub : Finset.range n ⊆ W := by
    intro a ha
    have hi := Finset.mem_range.1 ha
    let v : Fin n := ⟨a,hi⟩
    obtain ⟨u,hu⟩ := hdegree v
    exact mem_living.2 ⟨by omega,input_live he hu⟩
  have hW : W.card = n + S.card := by
    have h := Finset.card_sdiff_add_card_eq_card hSub
    have e : W \ Finset.range n = S := by ext a; simp [S]
    rw [e,Finset.card_range] at h
    omega
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simpa [heq,hb] using hb'
      · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change n+B.card ≤ C.gates.length+1
  omega

end PEqualNP.Outside.L_meta_2583_aux.LibraryLower.GraphProof



namespace PEqualNP.Outside.L_meta_2583_aux.LibraryLower.GraphProof
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem size_of_cover {n t : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hdegree : ∀ v : Fin n, ∃ w, G.Adj v w)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w →
      ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u))
    (hpath : ∀ v w : Fin n, G.Adj v w → ∃ a b : Fin n,
      G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b))
    (hcover : ∀ S : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ S ∨ b ∈ S) → t ≤ S.card)
    (hC : Monotone2 C) (hE : GraphEval C G) : n + t ≤ C.size + 1 := by
  classical
  by_cases hn : n = 0
  · subst n
    have ht := hcover ∅ (fun v => Fin.elim0 v)
    simp at ht
    omega
  let i : Fin n := ⟨0,by omega⟩
  obtain ⟨w,edge⟩ := hdegree i
  have hlt := (edge_at_output hE edge).2
  have houtput : C.output ∈ living n C := mem_living.2 ⟨hlt, Relation.ReflTransGen.refl⟩
  let S : Finset (Fin n) := Finset.univ.filter (Eligible C)
  have hS (u : Fin n) : u ∈ S ↔ Eligible C u := by simp [S]
  have htc : t ≤ S.card := by
    apply hcover
    intro v w hvw
    obtain ⟨a,b,hva,haw,hwb,hbv,hab⟩ := hpath v w hvw
    exact (covers_edge hC hE hvw hva haw hwb hbv hab).imp (hS v).mpr (hS w).mpr
  let B := (living n C).filter (Branch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f,hu]
  have hcap : S.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn f
    · intro u hu
      have hs := (hS u).mp hu
      have hb := firstBranch_spec u hs
      have hw := (next_le hb.1).trans_lt hlt
      show f u ∈ B
      rw [hf u hs]
      exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hw,hb.1⟩,hb.2.2⟩
    · intro u hu v hv same
      have hsu := (hS u).mp hu
      have hsv := (hS v).mp hv
      rw [hf u hsu,hf v hsv] at same
      exact branch_injective hC hE htwins hsu hsv same
  exact (Nat.add_le_add_left (htc.trans hcap) n).trans (branch_budget hC hE hdegree houtput)

end PEqualNP.Outside.L_meta_2583_aux.LibraryLower.GraphProof

namespace PEqualNP.Outside.L_meta_2583_aux.LibraryLower.Plane

-- The plane degree count and cover count follow checked L_meta_1955.
theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

theorem cardL {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ p ∈ A, (B.filter (fun w => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

theorem cardR {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ w ∈ B, (A.filter (fun p => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.card_filter]

theorem cover {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpt : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (A B : Finset (Fin N)) (hc : ∀ p w : Fin N, I p w → p ∈ A ∨ w ∈ B) :
    N ≤ A.card + B.card := by
  have hE : (((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = N * (q + 1) := by
    rw [cardR, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hA : ((A ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = A.card * (q + 1) := by
    rw [cardL, Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_const, smul_eq_mul]
  have hB : (((Finset.univ : Finset (Fin N)) ×ˢ B).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = B.card * (q + 1) := by
    rw [cardR, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, smul_eq_mul]
  have hsub : ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)
      ⊆ ((A ×ˢ (Finset.univ : Finset (Fin N))).filter (fun pw : Fin N × Fin N => I pw.1 pw.2))
        ∪ (((Finset.univ : Finset (Fin N)) ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)) := by
    rintro ⟨p, w⟩ h
    have hI : I p w := (Finset.mem_filter.mp h).2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product]
    rcases hc p w hI with h1 | h1
    · exact Or.inl ⟨⟨h1, Finset.mem_univ _⟩, hI⟩
    · exact Or.inr ⟨⟨Finset.mem_univ _, h1⟩, hI⟩
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hE, hA, hB, ← Nat.add_mul] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.succ_pos q)


theorem left_ne_right {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  have := p.isLt
  omega

def graph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) where
  Adj u v := ∃ p l : Fin N, I p l ∧ (Fin.castAdd N p = u ∨ Fin.castAdd N p = v) ∧
    (Fin.natAdd N l = u ∨ Fin.natAdd N l = v)
  symm := ⟨by
    rintro u v ⟨p,l,h,hp,hl⟩
    exact ⟨p,l,h,hp.symm,hl.symm⟩⟩
  loopless := ⟨by
    rintro v ⟨p,l,h,hp,hl⟩
    exact left_ne_right p l ((hp.elim id id).trans (hl.elim id id).symm)⟩

theorem adj_ll {N : ℕ} (I : Fin N → Fin N → Prop) (p r : Fin N) :
    ¬ (graph I).Adj (Fin.castAdd N p) (Fin.castAdd N r) := by
  rintro ⟨a,b,_,_,h⟩
  exact h.elim (fun he => left_ne_right p b he.symm) (fun he => left_ne_right r b he.symm)

theorem adj_rr {N : ℕ} (I : Fin N → Fin N → Prop) (l m : Fin N) :
    ¬ (graph I).Adj (Fin.natAdd N l) (Fin.natAdd N m) := by
  rintro ⟨a,b,_,h,_⟩
  exact h.elim (left_ne_right a l) (left_ne_right a m)

theorem adj_lr {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
    (graph I).Adj (Fin.castAdd N p) (Fin.natAdd N l) ↔ I p l := by
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    have hp := Fin.castAdd_inj.mp (ha.resolve_right (left_ne_right a l))
    have hl := (Fin.natAdd_inj N).mp (hb.resolve_left (left_ne_right p b).symm)
    simpa [hp,hl] using hab
  · intro hi
    exact ⟨p,l,hi,Or.inl rfl,Or.inr rfl⟩

theorem adj_rl {N : ℕ} (I : Fin N → Fin N → Prop) (l p : Fin N) :
    (graph I).Adj (Fin.natAdd N l) (Fin.castAdd N p) ↔ I p l :=
  ((graph I).adj_comm _ _).trans (adj_lr I p l)

theorem no_square {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (u v a b : Fin (N+N)) (uv : u ≠ v) (ab : a ≠ b)
    (ua : (graph I).Adj u a) (ub : (graph I).Adj u b)
    (va : (graph I).Adj v a) (vb : (graph I).Adj v b) : False := by
  have rect {p r l m : Fin N} (pr : p ≠ r) (lm : l ≠ m)
      (pl : I p l) (rl : I r l) (pm : I p m) (rm : I r m) : False :=
    lm ((hu p r pr).unique ⟨pl,rl⟩ ⟨pm,rm⟩)
  induction u using Fin.addCases <;> induction v using Fin.addCases <;>
    induction a using Fin.addCases <;> induction b using Fin.addCases <;>
    simp_all only [adj_ll,adj_rr,adj_lr,adj_rl]
  all_goals first
    | exact rect (fun e => uv (congrArg (Fin.castAdd N) e)) (fun e => ab (congrArg (Fin.natAdd N) e)) ua va ub vb
    | exact rect (fun e => ab (congrArg (Fin.castAdd N) e)) (fun e => uv (congrArg (Fin.natAdd N) e)) ua ub va vb

theorem other_neighbor {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (rows : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card=q+1)
    (cols : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card=q+1)
    (v w : Fin (N+N)) : ∃ u : Fin (N+N), (graph I).Adj v u ∧ u ≠ w := by
  have pick {x y : Fin (N+N)} (ne : x≠y) (hx : (graph I).Adj v x) (hy : (graph I).Adj v y) :
      ∃ u, (graph I).Adj v u ∧ u≠w := by
    by_cases he : x=w
    · exact ⟨y,hy,fun ey => ne (he.trans ey.symm)⟩
    · exact ⟨x,hx,he⟩
  suffices distinct : ∃ x y : Fin (N+N), x≠y ∧ (graph I).Adj v x ∧ (graph I).Adj v y by
    obtain ⟨x,y,ne,hx,hy⟩ := distinct
    exact pick ne hx hy
  induction v using Fin.addCases with
  | left p =>
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (show 1 < (Finset.univ.filter (fun l => I p l)).card by rw [rows]; omega)
    exact ⟨Fin.natAdd N a,Fin.natAdd N b,fun e => ne ((Fin.natAdd_inj N).mp e),
      (adj_lr _ _ _).mpr (Finset.mem_filter.mp ha).2,(adj_lr _ _ _).mpr (Finset.mem_filter.mp hb).2⟩
  | right l =>
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (show 1 < (Finset.univ.filter (fun p => I p l)).card by rw [cols]; omega)
    exact ⟨Fin.castAdd N a,Fin.castAdd N b,fun e => ne (Fin.castAdd_inj.mp e),
      (adj_rl _ _ _).mpr (Finset.mem_filter.mp ha).2,(adj_rl _ _ _).mpr (Finset.mem_filter.mp hb).2⟩

theorem vertex_cover {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (rows : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card=q+1)
    (cols : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card=q+1)
    (T : Finset (Fin (N+N))) (hits : ∀ a b, (graph I).Adj a b → a∈T ∨ b∈T) : N ≤ T.card := by
  classical
  let A := Finset.univ.filter (fun p : Fin N => Fin.castAdd N p ∈ T)
  let B := Finset.univ.filter (fun l : Fin N => Fin.natAdd N l ∈ T)
  have cost := cover q I cols rows A B (by
    intro p l hp
    simpa [A,B] using hits _ _ ((adj_lr _ _ _).mpr hp))
  let left : Fin N ↪ Fin (N+N) := ⟨Fin.castAdd N,fun _ _ => Fin.castAdd_inj.mp⟩
  let right : Fin N ↪ Fin (N+N) := ⟨Fin.natAdd N,fun _ _ => (Fin.natAdd_inj N).mp⟩
  have separate : Disjoint (A.map left) (B.map right) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨p,_,rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨l,_,he⟩ := Finset.mem_map.mp hz'
    exact left_ne_right p l he.symm
  have sub : A.map left ∪ B.map right ⊆ T := by
    intro z hz
    rcases Finset.mem_union.mp hz with ha|hb
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp ha
      exact (Finset.mem_filter.mp hp).2
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hb
      exact (Finset.mem_filter.mp hl).2
  have hc := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint separate,Finset.card_map,Finset.card_map] at hc
  exact cost.trans hc

end PEqualNP.Outside.L_meta_2583_aux.LibraryLower.Plane

namespace PEqualNP.Outside.L_meta_2583_aux.LibraryLower

lemma lower_threeN_base :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin (x2 + x2)), (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = x11 ∨ x13 = x12)) = Bool.true ↔ ∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ (Fin.castAdd x2 x13 = x11 ∨ Fin.castAdd x2 x13 = x12) ∧ (Fin.natAdd x2 x14 = x11 ∨ Fin.natAdd x2 x14 = x12)) → (3 : ℕ) * x2 ≤ x5.size + (1 : ℕ) := by
  classical
  intro q N I inst C hq hn hline hu hC pairs
  let G := Plane.graph I
  have cols (l : Fin N) : (Finset.univ.filter (fun p => I p l)).card = q+1 := by
    rw [← Fintype.card_coe]
    refine (Fintype.card_congr (Equiv.subtypeEquivRight ?_)).trans (hline l)
    intro p
    simp
  have rows := Plane.lines_through q N I hq hn cols hu
  have other (v w : Fin (N+N)) : ∃ a, G.Adj v a ∧ a ≠ w :=
    Plane.other_neighbor I hq rows cols v w
  have degree (v : Fin (N+N)) : ∃ w, G.Adj v w := by
    obtain ⟨w,hw,_⟩ := other v v
    exact ⟨w,hw⟩
  have twins (v w : Fin (N+N)) (ne : v ≠ w) (_ : ¬ G.Adj v w) :
      ∃ u, ¬ (G.Adj v u ↔ G.Adj w u) := by
    obtain ⟨a,va⟩ := degree v
    obtain ⟨b,vb,ba⟩ := other v a
    by_cases wa : G.Adj w a
    · by_cases wb : G.Adj w b
      · exact (Plane.no_square I hu v w a b ne ba.symm va vb wa wb).elim
      · exact ⟨b,fun he => wb (he.mp vb)⟩
    · exact ⟨a,fun he => wa (he.mp va)⟩
  have path (v w : Fin (N+N)) (vw : G.Adj v w) :
      ∃ a b, G.Adj v a ∧ a≠w ∧ G.Adj w b ∧ b≠v ∧ (a=b ∨ ¬G.Adj a b) := by
    obtain ⟨a,va,aw⟩ := other v w
    obtain ⟨b,wb,bv⟩ := other w v
    exact ⟨a,b,va,aw,wb,bv,Or.inr (fun ab =>
      Plane.no_square I hu v b w a bv.symm aw.symm vw va wb.symm ab.symm)⟩
  have eval : GraphProof.GraphEval C G := by
    intro a b
    have input : GraphProof.point ({a,b} : Finset (Fin (N+N))) = fun i => decide (i=a ∨ i=b) := by
      funext i
      simp [GraphProof.point]
    change C.eval (List.ofFn (GraphProof.point {a,b})) = true ↔ G.Adj a b
    rw [input]
    exact pairs a b
  have bound := GraphProof.size_of_cover (t:=N) G C degree twins path (Plane.vertex_cover I rows cols) hC eval
  omega


lemma lower_threeN
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) :
    3 * N ≤ C.size + 1 := by
  apply lower_threeN_base q N I C hq hN
  · intro l
    rw [← hline l, ← Fintype.card_coe]
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro p
    simp
  · exact hunique
  · intro g hg
    exact ⟨hAO.1 g hg, (hAO.2.2 g hg).le⟩
  · intro a b
    rw [hfun, decide_eq_true_eq]
    simp

end PEqualNP.Outside.L_meta_2583_aux.LibraryLower


namespace PEqualNP.Outside.L_meta_2583

lemma normalize_above_upper (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hsize : N * (q + 2) - 1 ≤ C.size) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ y : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) D y =
          decide (∃ p l : Fin N, I p l ∧
            y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  obtain ⟨D, hao, hbound, hfun, hread⟩ := plane_readOne_upper q N I hline
  exact ⟨D, hao, hfun, hbound.trans hsize, hread⟩

lemma failure_implies_size_window
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true))
    (hfail : ¬ ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ y : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) D y =
          decide (∃ p l : Fin N, I p l ∧
            y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1) :
    3 * N ≤ C.size + 1 ∧ C.size + 1 < N * (q + 2) := by
  constructor
  · exact PEqualNP.Outside.L_meta_2583_aux.LibraryLower.lower_threeN
      q N I C hq hN hline hunique hAO hfun
  · by_contra! h
    exact hfail (normalize_above_upper q N I C hline (by omega))

end PEqualNP.Outside.L_meta_2583


namespace PEqualNP.Outside.L_meta_2583_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_gateStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl gateStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, gateStep, List.length_append, List.length_singleton]
    omega

lemma list_getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d : α)
    (hi : i < l1.length) : (l1 ++ l2).getD i d = l1.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi]

lemma foldl_gateStep_getD_of_lt (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (gs.foldl gateStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : i < (gateStep w g).length := by
      simp only [gateStep, List.length_append, List.length_singleton]
      omega
    rw [ih (gateStep w g) hlen]
    exact list_getD_append_left w _ i false hi

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_gateStep_length C.gates x

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [show (C.wires (List.ofFn x)).getD i false = (List.ofFn x).getD i false from
    foldl_gateStep_getD_of_lt C.gates (List.ofFn x) i (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma incidence_singleton_false (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (w : Fin (P + L)) :
    decide (∃ p l, I p l ∧ decide (Fin.castAdd L p = w) = true ∧
      decide (Fin.natAdd P l = w) = true) = false := by
  apply decide_eq_false
  rintro ⟨p, l, _, hp, hl⟩
  have hp' := of_decide_eq_true hp
  have hl' := of_decide_eq_true hl
  have he := congrArg Fin.val (hp'.trans hl'.symm)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at he
  omega

lemma no_input_below (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hF : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (w : ℕ) (hw : w < P + L) : ¬ WireBelowOutput (P + L) C w := by
  intro h
  let z : Fin (P + L) → Bool := fun i => decide (i = ⟨w, hw⟩)
  have hv : (C.wires (List.ofFn z)).getD w false = true := by
    rw [wires_input C z w hw]
    simp [z]
  have hc : circuitFun (P + L) C z = true := h z hv
  have hz : circuitFun (P + L) C z = false := by
    rw [hF]
    exact incidence_singleton_false P L I ⟨w, hw⟩
  rw [hz] at hc
  contradiction

lemma incidence_output_valid (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hne : ∃ p l, I p l)
    (hF : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    C.output < P + L + C.gates.length := by
  by_contra hout
  have hzero : circuitFun (P + L) C (fun _ => true) = false := by
    unfold circuitFun Circuit.eval
    apply List.getD_eq_default
    rw [wires_length, List.length_ofFn]
    omega
  have hone : circuitFun (P + L) C (fun _ => true) = true := by
    rw [hF]
    apply decide_eq_true
    obtain ⟨p, l, hpl⟩ := hne
    exact ⟨p, l, hpl, rfl, rfl⟩
  rw [hzero] at hone
  contradiction

lemma incidence_output_is_gate (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hF : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    P + L ≤ C.output := by
  by_contra hout
  have hb : WireBelowOutput (P + L) C C.output := by
    intro z hz
    exact hz
  exact no_input_below P L I C hF C.output (by omega) hb

end PEqualNP.Outside.L_meta_2583_aux


namespace PEqualNP.Outside.L_meta_2583

lemma sides_disjoint (N : ℕ) (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  change p.val = N + l.val at hv
  omega

lemma incidence_prime_iff (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧
          z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (S : Finset (Fin (N + N))) :
    PEqualNP.ReadK.IsPrimeImplicant (N + N) C S ↔
      ∃ p l : Fin N, I p l ∧ S = {Fin.castAdd N p, Fin.natAdd N l} := by
  classical
  constructor
  · intro hS
    obtain ⟨p, l, hI, hp, hl⟩ : ∃ p l : Fin N,
        I p l ∧ Fin.castAdd N p ∈ S ∧ Fin.natAdd N l ∈ S := by
      simpa [hfun, PEqualNP.ReadK.setInput] using hS.1
    refine ⟨p, l, hI, ?_⟩
    have hsub : {Fin.castAdd N p, Fin.natAdd N l} ⊆ S := by
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hp hl
    by_contra hne
    have hss : {Fin.castAdd N p, Fin.natAdd N l} ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩
    have hfalse := hS.2 _ (Finset.mem_ssubsets.mpr hss)
    have htrue : PEqualNP.MetaComplexity.circuitFun (N + N) C
        (PEqualNP.ReadK.setInput {Fin.castAdd N p, Fin.natAdd N l}) = true := by
      rw [hfun, decide_eq_true_eq]
      exact ⟨p, l, hI, by simp [PEqualNP.ReadK.setInput], by simp [PEqualNP.ReadK.setInput]⟩
    rw [htrue] at hfalse
    cases hfalse
  · rintro ⟨p, l, hI, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hfun, decide_eq_true_eq]
      exact ⟨p, l, hI, by simp [PEqualNP.ReadK.setInput], by simp [PEqualNP.ReadK.setInput]⟩
    · intro T hT
      rw [hfun, decide_eq_false_iff_not]
      rintro ⟨a, b, _, ha, hb⟩
      have haT : Fin.castAdd N a ∈ T := by simpa [PEqualNP.ReadK.setInput] using ha
      have hbT : Fin.natAdd N b ∈ T := by simpa [PEqualNP.ReadK.setInput] using hb
      have hss := Finset.mem_ssubsets.mp hT
      have hap : Fin.castAdd N a = Fin.castAdd N p := by
        have hmem := hss.subset haT
        rcases Finset.mem_insert.mp hmem with h | h
        · exact h
        · exact (sides_disjoint N a l (Finset.mem_singleton.mp h)).elim
      have hbl : Fin.natAdd N b = Fin.natAdd N l := by
        have hmem := hss.subset hbT
        rcases Finset.mem_insert.mp hmem with h | h
        · exact (sides_disjoint N p b h.symm).elim
        · exact Finset.mem_singleton.mp h
      have hpT : Fin.castAdd N p ∈ T := by simpa only [hap] using haT
      have hlT : Fin.natAdd N l ∈ T := by simpa only [hbl] using hbT
      have hback : {Fin.castAdd N p, Fin.natAdd N l} ⊆ T := by
        simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hpT hlT
      have hlt := Finset.card_lt_card hss
      have hle := Finset.card_le_card hback
      omega

lemma readk_setList_pair {n : ℕ} (a b : Fin n) (hab : a < b) :
    PEqualNP.ReadK.setList ({a, b} : Finset (Fin n)) = [a.val, b.val] := by
  have key : ∀ x y : Fin n, x < y → y < x → x = y :=
    fun x y h1 h2 => absurd h1 (lt_asymm h2)
  have hp1 : List.Pairwise (fun x y : Fin n => x < y)
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) :=
    List.Pairwise.filter _ (List.pairwise_lt_finRange n)
  have hp2 : List.Pairwise (fun x y : Fin n => x < y) [a, b] := by
    simp [hab]
  have hperm : List.Perm
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) [a, b] := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.Nodup.filter _ (List.nodup_finRange n)
    · simp [ne_of_lt hab]
    · ext x
      simp
  have h : (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))) = [a, b] :=
    List.Perm.eq_of_pairwise (fun x y _ _ => key x y) hp1 hp2 hperm
  unfold PEqualNP.ReadK.setList
  rw [h]
  rfl
lemma incidence_setList_pair (N : ℕ) (p l : Fin N) :
    PEqualNP.ReadK.setList ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) =
      [p.val, N + l.val] := by
  have hp : Fin.castAdd N p < Fin.natAdd N l := by
    change p.val < N + l.val
    omega
  exact readk_setList_pair _ _ hp

lemma incidence_isReadK_iff (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧
          z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) (k : ℕ) :
    PEqualNP.ReadK.IsReadK (N + N) C k ↔
      ∀ p l : Fin N, I p l → PEqualNP.ReadK.readsAtMost C (N + N) [p.val, N + l.val] k = true := by
  constructor
  · intro h p l hI
    have hs := h _ ((incidence_prime_iff N I C hfun _).mpr ⟨p, l, hI, rfl⟩)
    rwa [incidence_setList_pair] at hs
  · intro h S hS
    obtain ⟨p, l, hI, rfl⟩ := (incidence_prime_iff N I C hfun S).mp hS
    rw [incidence_setList_pair]
    exact h p l hI

end PEqualNP.Outside.L_meta_2583

namespace PEqualNP.Outside.L_meta_2583

lemma failure_has_unread_pair
    (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true))
    (hfail : ¬ ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ y : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) D y =
          decide (∃ p l : Fin N, I p l ∧
            y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1) :
    ∃ p l : Fin N, I p l ∧
      PEqualNP.ReadK.readsAtMost C (N + N) [p.val, N + l.val] 1 = false := by
  have hn : ¬ PEqualNP.ReadK.IsReadK (N + N) C 1 := by
    intro hr
    exact hfail ⟨C, hAO, hfun, le_rfl, hr⟩
  rw [incidence_isReadK_iff N I C hfun] at hn
  push_neg at hn
  obtain ⟨p, l, hI, hbad⟩ := hn
  refine ⟨p, l, hI, ?_⟩
  cases hv : PEqualNP.ReadK.readsAtMost C (N + N) [p.val, N + l.val] 1 <;> simp_all

end PEqualNP.Outside.L_meta_2583
