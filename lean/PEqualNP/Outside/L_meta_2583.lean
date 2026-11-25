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
lemma t3692 : ∀ (x1 x2 : ℕ) (E : Finset (Fin x1 × Fin x2))
    (A : Finset (Fin x1)) (B : Finset (Fin x2)),
    (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) →
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Bool → Finset ℕ),
      PEqualNP.TopForm.IsAO2 (x1 + x2) C ∧
      C.size ≤ E.card + A.card + B.card - 1 ∧
      (∀ z : Fin (x1 + x2) → Bool, PEqualNP.MetaComplexity.circuitFun (x1 + x2) C z =
        decide (∃ p l, (p, l) ∈ E ∧ z (Fin.castAdd x2 p) = true ∧
          z (Fin.natAdd x1 l) = true)) ∧
      (∀ b, ∀ w ∈ F b, w < x1 + x2 ∧ decide (x1 ≤ w) = b ∨
        ∃ j < C.size, w = x1 + x2 + j ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, i ∈ F b) ∧
      (∀ j < C.size,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∃ a b, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, b] ∧
          a ∈ F false ∧ b ∈ F true) ∧
      ((∀ p ∈ A, ∃ l, (p, l) ∈ E) →
        (∀ l ∈ B, ∃ p, (p, l) ∈ E ∧ p ∉ A) →
        C.size = E.card + A.card + B.card - 1) := by
  intro x1 x2 E A B hcov
  by_cases hE : E = ∅
  · subst hE
    refine ⟨⟨[], x1 + x2⟩, fun _ => ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · intro hApos hBpos
      have hA : A = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨l, hl⟩ := hApos p hp
        exact Finset.notMem_empty _ hl
      have hB : B = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro l hl
        obtain ⟨p, hp, _⟩ := hBpos l hl
        exact Finset.notMem_empty _ hp
      simp [PEqualNP.CircuitLowerBounds.Circuit.size, hA, hB]
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
    refine ⟨C, S1, hC.1, ?_, ?_, hC.2.1, hC.2.2, ?_⟩
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

    · intro hApos hBpos
      have hAA : A' = A := by
        apply Finset.filter_eq_self.mpr
        intro p hp
        obtain ⟨l, hl⟩ := hApos p hp
        exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩⟩
      have hBB : B' = B := by
        apply Finset.filter_eq_self.mpr
        intro l hl
        obtain ⟨p, hp, hpa⟩ := hBpos l hl
        exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp, hpa⟩⟩
      have hk_pos : 1 ≤ ws1.length := by
        cases ws1 with
        | nil => exact absurd rfl hws1_ne
        | cons _ _ => simp
      simp only [C, PEqualNP.CircuitLowerBounds.Circuit.size, hlen2, hlen1, List.length_nil,
        Nat.zero_add, hsum_stars, hwslen1, hstars_len, hAA, hBB] at hk_pos ⊢
      omega

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

lemma inv (x1 x2 : ℕ) (C : Circuit) (x4 : Bool → Finset ℕ) (hC : IsAO2 (x1 + x2) C)
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

lemma t6579 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Bool → Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x3 → (∀ (x6 : Bool), ∀ x7 ∈ x4 x6, x7 < x1 + x2 ∧ Decidable.decide (x1 ≤ x7) = x6 ∨ ∃ x9 < x3.size, x7 = x1 + x2 + x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).inputs, x10 ∈ x4 x6) → (∀ x7 < x3.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).inputs = [x10, x11] ∧ x10 ∈ x4 Bool.false ∧ x11 ∈ x4 Bool.true) → PEqualNP.ReadK.IsReadK (x1 + x2) x3 (1 : ℕ) := by
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

lemma star_cover_read_one : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧ (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) ∧ PEqualNP.ReadK.IsReadK (x1 + x2) x7 (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 hcov
  obtain ⟨C, F, hao, hsize, hfun, hF1, hF2, _⟩ := PEqualNP.Outside.L_meta_2583.t3692 x1 x2 x3 x4 x5 hcov
  exact ⟨C, hao, hsize, hfun, PEqualNP.Outside.L_meta_2583.t6579 x1 x2 C F hao hF1 hF2⟩


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma incidence_edges_card (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card = N * (q + 1) := by
  classical
  let F (l : Fin N) : Finset (Fin N × Fin N) :=
    (Finset.univ.filter (fun p => I p l)).map ⟨fun p => (p, l), fun _ _ h => congrArg Prod.fst h⟩
  have hF (l : Fin N) (e : Fin N × Fin N) : e ∈ F l ↔ I e.1 l ∧ e.2 = l := by
    constructor
    · intro he
      obtain ⟨p, hp, ht⟩ := Finset.mem_map.mp he
      change (p, l) = e at ht
      rw [← ht]
      exact ⟨(Finset.mem_filter.mp hp).2, rfl⟩
    · rintro ⟨hi, hh⟩
      refine Finset.mem_map.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
      exact Prod.ext rfl hh.symm
  have heq : Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2) =
      Finset.univ.biUnion F := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hF]
    exact ⟨fun h => ⟨e.2, h, rfl⟩, fun ⟨l, hi, he⟩ => he ▸ hi⟩
  rw [heq, Finset.card_biUnion]
  · simp [F, hL]
  · intro l _ l' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    exact hne (((hF l e).mp he).2.symm.trans ((hF l' e).mp he').2)

lemma canonical_plane_read_one_exact (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) ∧
      D.size = N * (q + 2) - 1 ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  classical
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2)
  obtain ⟨D, F, hAO, _, hfun, hF1, hF2, hexact⟩ :=
    t3692 N N E ∅ Finset.univ (by intro e _; exact Or.inr (Finset.mem_univ _))
  refine ⟨D, hAO, ?_, ?_, t6579 N N D F hAO hF1 hF2⟩
  · intro z
    simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and] using hfun z
  · have hsize := hexact (by simp) (by
      intro l _
      have hpos : 0 < (Finset.univ.filter (fun p => I p l)).card := by rw [hL l]; omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
      exact ⟨p, by simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and] using hp,
        Finset.notMem_empty _⟩)
    have hcard : E.card = N * (q + 1) := incidence_edges_card q N I hL
    simpa only [Finset.card_empty, Finset.card_univ, Fintype.card_fin, hcard, Nat.add_zero,
      Nat.mul_add, Nat.mul_one, Nat.mul_two, Nat.add_assoc] using hsize

lemma canonical_plane_read_one (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) ∧
      D.size ≤ N * (q + 2) - 1 ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  obtain ⟨D, hAO, hfun, hsize, hread⟩ := canonical_plane_read_one_exact q N I hL
  exact ⟨D, hAO, hfun, hsize.le, hread⟩

lemma normalization_given_bound (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hbound : N * (q + 2) - 1 ≤ C.size) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ y : Fin (N + N) → Bool, circuitFun (N + N) D y =
        decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧
          y (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  obtain ⟨D, hAO, hfun, hsize, hread⟩ := canonical_plane_read_one q N I hL
  exact ⟨D, hAO, hfun, hsize.trans hbound, hread⟩


namespace Sharp

namespace General


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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

open PEqualNP.CleanedNonEdge in
lemma s2230_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma s2230_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma s2230_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma s2230_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2230_orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma s2230_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2230_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2230_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2230_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2230_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2230_orFold_getD_lt n post _ m (by omega)]
    exact s2230_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2230_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

open PEqualNP.CleanedNonEdge PEqualNP.ReadK PEqualNP.TopForm

lemma s2230_orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  unfold OrReaches
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2230_orSets_mem_iff n C j j hj]
  exact Or.inl rfl

lemma s2230_orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : OrReaches n C i g) : OrReaches n C (n + j) g := by
  unfold OrReaches at h ⊢
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2230_orSets_mem_iff n C j g hj]
  exact Or.inr ⟨hop, i, hi, h.1, hlt, h.2⟩

lemma s2230_mem_filter_iff_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma s2230_mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold orIn
  exact ⟨fun h => ((s2230_mem_filter_iff_gen _ _ _ _).1 h).2,
    fun h => (s2230_mem_filter_iff_gen _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma s2230_orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ orIn n C i) : a ∈ orIn n C (n + j) := by
  rw [s2230_mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, s2230_orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, s2230_orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

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

lemma s2230_inv (n : ℕ) (C : Circuit) (a b : Fin n) (hC : IsAO2 n C) (hab : a.val < b.val) :
    ∀ w : ℕ, ∀ v ∈ s2230_RV C n [a.val, b.val] 1 w, ∃ x y : ℕ, v = [x, y] ∧ 1 ≤ x + y ∧
      (x = 1 → y = 0 →
        a ∈ orIn n C w ∧ s2230_W n C (fun k1 : Fin n => decide (k1 = a)) w = true) ∧
      (x = 0 → y = 1 →
        b ∈ orIn n C w ∧ s2230_W n C (fun k1 : Fin n => decide (k1 = b)) w = true) ∧
      (x = 1 → y = 1 → ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
        OrReaches n C w j ∧
        ((a ∈ side (n := n) C j 0 ∧ b ∈ side (n := n) C j 1) ∨
          (b ∈ side (n := n) C j 0 ∧ a ∈ side (n := n) C j 1))) := by
  obtain ⟨hAnd, hBack, hTwo⟩ := hC
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    by_cases hwn : w < n
    · rw [s2230_RV_input C n _ 1 w hwn, s2230_leaf_eq] at hv
      by_cases hwa : a.val = w
      · have hwb : ¬ b.val = w := by omega
        rw [if_pos (List.mem_cons.2 (Or.inl hwa.symm)), if_pos hwa, if_neg hwb] at hv
        have hv2 : v = [1, 0] := List.mem_singleton.1 hv
        refine ⟨1, 0, hv2, by omega, ?_, ?_, ?_⟩
        · intro _ _
          refine ⟨?_, ?_⟩
          · rw [s2230_mem_orIn]
            exact Or.inl hwa
          · rw [s2230_W_input n C _ w hwn]
            exact decide_eq_true (Fin.ext hwa.symm)
        · intro h3 h4
          omega
        · intro h3 h4
          omega
      · by_cases hwb : b.val = w
        · rw [if_pos (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl hwb.symm)))),
            if_neg hwa, if_pos hwb] at hv
          have hv2 : v = [0, 1] := List.mem_singleton.1 hv
          refine ⟨0, 1, hv2, by omega, ?_, ?_, ?_⟩
          · intro h3 h4
            omega
          · intro _ _
            refine ⟨?_, ?_⟩
            · rw [s2230_mem_orIn]
              exact Or.inl hwb
            · rw [s2230_W_input n C _ w hwn]
              exact decide_eq_true (Fin.ext hwb.symm)
          · intro h3 h4
            omega
        · exfalso
          have hm : ¬ w ∈ [a.val, b.val] := by
            intro hm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            omega
          rw [if_neg hm] at hv
          simp at hv
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      by_cases hj : j < C.gates.length
      · have hmem : gateAt C j ∈ C.gates := by
          rw [s2230_gateAt_eq C j hj]
          exact List.getElem_mem hj
        have hlen2 := hTwo _ hmem
        have hback := hBack j hj
        obtain ⟨Rp, hRp, hRV⟩ := s2230_RV_gate C n [a.val, b.val] 1 j hj
        rcases hinp : (gateAt C j).inputs with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, rest⟩⟩⟩
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2
        · have hm1 : i1 ∈ (gateAt C j).inputs := by rw [hinp]; simp
          have hm2 : i2 ∈ (gateAt C j).inputs := by rw [hinp]; simp
          have hi1 : i1 < n + j := hback i1 hm1
          have hi2 : i2 < n + j := hback i2 hm2
          rcases hAnd _ hmem with hop | hop
          · rw [hRV, s2230_FR_and _ _ _ _ hop, hinp] at hv
            simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
              hRp i1 hi1, hRp i2 hi2] at hv
            obtain ⟨t, ht, u2, hu2, rfl⟩ := s2230_mem_andStep _ _ _ _ hv
            obtain ⟨z, hz, u1, hu1, rfl⟩ := s2230_mem_andStep _ _ _ _ ht
            have hz2 : z = [0, 0] := by simpa using hz
            subst hz2
            obtain ⟨x1, y1, rfl, h1, ha1, hb1, _⟩ := ih i1 hi1 u1 hu1
            obtain ⟨x2, y2, rfl, h2, ha2, hb2, _⟩ := ih i2 hi2 u2 hu2
            refine ⟨min (min (0 + x1) (1 + 1) + x2) (1 + 1),
              min (min (0 + y1) (1 + 1) + y2) (1 + 1), ?_, by omega, ?_, ?_, ?_⟩
            · rw [s2230_capAdd_pair, s2230_capAdd_pair]
            · intro hx hy
              omega
            · intro hx hy
              omega
            · intro hx hy
              have hcase : (x1 = 1 ∧ y1 = 0 ∧ x2 = 0 ∧ y2 = 1) ∨
                  (x1 = 0 ∧ y1 = 1 ∧ x2 = 1 ∧ y2 = 0) := by omega
              refine ⟨j, hj, hop, s2230_orReaches_self n C j hj, ?_⟩
              have hs0 : side (n := n) C j 0 = orIn n C i1 := by
                first
                  | (unfold side opnd; rw [hinp]; rfl)
                  | simp [side, opnd, hinp]
              have hs1 : side (n := n) C j 1 = orIn n C i2 := by
                first
                  | (unfold side opnd; rw [hinp]; rfl)
                  | simp [side, opnd, hinp]
              rw [hs0, hs1]
              rcases hcase with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
              · exact Or.inl ⟨(ha1 e1 e2).1, (hb2 e3 e4).1⟩
              · exact Or.inr ⟨(hb1 e1 e2).1, (ha2 e3 e4).1⟩
          · rw [hRV, s2230_FR_or _ _ _ _ hop, hinp] at hv
            simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
              hRp i1 hi1, hRp i2 hi2] at hv
            have hsrc : ∃ i, i ∈ (gateAt C j).inputs ∧ i < n + j ∧
                v ∈ s2230_RV C n [a.val, b.val] 1 i := by
              rcases s2230_mem_foldl_insertNew _ _ _ hv with h | h
              · rcases s2230_mem_foldl_insertNew _ _ _ h with h3 | h3
                · simp at h3
                · exact ⟨i1, hm1, hi1, h3⟩
              · exact ⟨i2, hm2, hi2, h⟩
            obtain ⟨i, him, hilt, hvi⟩ := hsrc
            obtain ⟨x, y, hxy, h1, ha1, hb1, hab1⟩ := ih i hilt v hvi
            have hW : ∀ z : Fin n → Bool, s2230_W n C z i = true → s2230_W n C z (n + j) = true := by
              intro z hz
              rw [s2230_W_gate n C z j hj, hop]
              simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
              exact ⟨i, him, by simp only [hilt, ite_true]; exact hz⟩
            refine ⟨x, y, hxy, h1, ?_, ?_, ?_⟩
            · intro hx hy
              exact ⟨s2230_orIn_up n C j i a hj hop him hilt (ha1 hx hy).1, hW _ (ha1 hx hy).2⟩
            · intro hx hy
              exact ⟨s2230_orIn_up n C j i b hj hop him hilt (hb1 hx hy).1, hW _ (hb1 hx hy).2⟩
            · intro hx hy
              obtain ⟨j2, hj2, hop2, hr2, hsd⟩ := hab1 hx hy
              exact ⟨j2, hj2, hop2, s2230_orReaches_step n C j i j2 hj hop him hilt hr2, hsd⟩
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2 <;> omega
      · exfalso
        have hnil : s2230_RV C n [a.val, b.val] 1 (n + j) = [] := by
          simp only [s2230_RV]
          rw [s2230_readVectors_eq]
          exact List.getD_eq_default _ _ (by
            rw [s2230_foldR_length]
            simp only [List.length_map, List.length_range]
            omega)
        rw [hnil] at hv
        simp at hv

lemma s2230 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin n), PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → a < b → PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = true → ∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j ∧ ((a ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ b ∈ PEqualNP.TopForm.side (n := n) C j 1) ∨ (b ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ a ∈ PEqualNP.TopForm.side (n := n) C j 1)) := by
  intro n C a b hC hsingle hab hread
  have hlt : a.val < b.val := hab
  unfold readsAtMost at hread
  rw [List.any_eq_true] at hread
  obtain ⟨v, hv, hall⟩ := hread
  obtain ⟨x, y, rfl, h1, ha, hb, hab2⟩ := s2230_inv n C a b hC hlt C.output v hv
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hall
  obtain ⟨hx, hy⟩ := hall
  have hcases : (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 1) := by omega
  rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exfalso
    have h3 : circuitFun n C (fun k1 : Fin n => decide (k1 = a)) = true := (ha e1 e2).2
    rw [hsingle a] at h3
    exact Bool.false_ne_true h3
  · exfalso
    have h3 : circuitFun n C (fun k1 : Fin n => decide (k1 = b)) = true := (hb e1 e2).2
    rw [hsingle b] at h3
    exact Bool.false_ne_true h3
  · exact hab2 e1 e2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def s2231_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2231_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2231_stepWire x := rfl

lemma s2231_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2231_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2231_stepWire]
    omega

lemma s2231_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2231_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2231_stepWire w g).length := by simp [s2231_stepWire]; omega
    rw [ih (s2231_stepWire w g) hlt]
    simp [s2231_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2231_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2231_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2231_wires_eq_foldl, s2231_foldl_stepWire_length, List.length_ofFn]

lemma s2231_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2231_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2231_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2231_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2231_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2231_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2231_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2231_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2231_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2231_foldl_stepWire_length, hpre_len]
  have hCj : s2231_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2231_W]
    rw [s2231_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2231_foldl_stepWire_getD_lt post (s2231_stepWire w0 gj) (n + k) (by simp [s2231_stepWire]; omega)]
    simp [s2231_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2231_W]
    rw [s2231_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2231_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2231_getD_ge_length w0 i (by omega)

lemma s2231_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2231_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2231_W]
  rw [s2231_wires_eq_foldl, s2231_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma s2231_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma s2231_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma s2231_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma s2231_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2231_orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma s2231_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2231_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2231_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2231_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2231_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2231_orFold_getD_lt n post _ m (by omega)]
    exact s2231_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2231_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma s2231_W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : s2231_W n C x i = true) : s2231_W n C x (n + r) = true := by
  rw [s2231_W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [if_pos hlt]; exact hv⟩

lemma s2231_W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and)
    (h : ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ s2231_W n C x i = true) :
    s2231_W n C x (n + r) = true := by
  rw [s2231_W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  intro i hi
  rw [if_pos (h i hi).1]; exact (h i hi).2

open PEqualNP.CleanedNonEdge in
lemma s2231_reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : s2231_W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → s2231_W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (s2231_orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact s2231_W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma s2231_reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : s2231_W n C x (n + g) = true) : s2231_W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := s2231_reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [s2231_orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma s2231_mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma s2231_side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    s2231_W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := s2231_mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, s2231_W_input n C x i.val i.isLt]; exact hx
  · have hk1 : s2231_W n C x (n + k) = true := by
      apply s2231_W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [s2231_W_input n C x i.val i.isLt]; exact hx
    exact s2231_reach_up n C x _ k hreach hk1

def s2231_px {n : ℕ} (u v : Fin n) : Fin n → Bool := fun k => decide (k = u ∨ k = v)

lemma s2231_px_self {n : ℕ} (t : Fin n) : s2231_px t t = (fun k : Fin n => decide (k = t)) := by
  funext k; simp [s2231_px]

lemma s2231_part1 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hNF : PEqualNP.TopForm.NoFourCycle G) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (h1 : ∀ a1 : Fin n, circuitFun n C (fun k1 => decide (k1 = a1)) = false)
    (h2 : ∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 →
      circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C C.output j) :
    (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 →
        w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧
      (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 →
        ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧
      ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨
        (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1) := by
  obtain ⟨_, hRB, hlen2⟩ := hAO
  have hgm : gateAt C j ∈ C.gates := by rw [s2231_gateAt_eq C j hj]; exact List.getElem_mem hj
  have hl2 : (gateAt C j).inputs.length = 2 := hlen2 _ hgm
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a0, b0, hl⟩ := List.length_eq_two.mp hl2
  have e0 : PEqualNP.TopForm.opnd C j 0 = a0 := by
    unfold PEqualNP.TopForm.opnd; rw [hl]; rfl
  have e1 : PEqualNP.TopForm.opnd C j 1 = b0 := by
    unfold PEqualNP.TopForm.opnd; rw [hl]; rfl
  have hcross : ∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 →
      ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → u ≠ v ∧ G.Adj u v := by
    intro u hu v hv
    have hxu : s2231_px u v u = true := by simp [s2231_px]
    have hxv : s2231_px u v v = true := by simp [s2231_px]
    have va := s2231_side_val n C (s2231_px u v) j 0 u hu hxu
    have vb := s2231_side_val n C (s2231_px u v) j 1 v hv hxv
    rw [e0] at va
    rw [e1] at vb
    have hg : s2231_W n C (s2231_px u v) (n + j) = true := by
      apply s2231_W_and n C (s2231_px u v) j hj hop
      intro i hi
      have hi2 := hi
      rw [hl] at hi2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi2
      rcases hi2 with h | h
      · exact ⟨hrb i hi, by rw [h]; exact va⟩
      · exact ⟨hrb i hi, by rw [h]; exact vb⟩
    have hW : circuitFun n C (s2231_px u v) = true := s2231_reach_up n C (s2231_px u v) C.output j hr hg
    have hne : u ≠ v := by
      intro e
      subst e
      rw [s2231_px_self] at hW
      have hf : true = false := hW.symm.trans (h1 _)
      cases hf
    refine ⟨hne, ?_⟩
    by_contra hna
    have hf : true = false := hW.symm.trans (h2 u v hne hna)
    cases hf
  refine ⟨?_, fun u hu v hv => (hcross u hu v hv).2, ?_⟩
  · intro w hw0 hw1
    exact (hcross w hw0 w hw1).1 rfl
  · by_contra hcon
    push_neg at hcon
    obtain ⟨c0, c1⟩ := hcon
    obtain ⟨u, hu, u2, hu2, hne⟩ := Finset.one_lt_card.mp c0
    obtain ⟨v, hv, v2, hv2, hnv⟩ := Finset.one_lt_card.mp c1
    have hc := hNF u u2 hne
    rw [Finset.card_le_one] at hc
    exact hnv (hc v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcross u hu v hv).2,
      (hcross u2 hu2 v hv).2⟩) v2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hcross u hu v2 hv2).2, (hcross u2 hu2 v2 hv2).2⟩))

def s2231_cen (n : ℕ) (C : Circuit) (i : ℕ) : Finset (Fin n) :=
  if (PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1 then PEqualNP.TopForm.side (n := n) C i 0
  else if (PEqualNP.TopForm.side (n := n) C i 1).card ≤ 1 then
    PEqualNP.TopForm.side (n := n) C i 1
  else ∅

lemma s2231_cen_card (n : ℕ) (C : Circuit) (i : ℕ) : (s2231_cen n C i).card ≤ 1 := by
  unfold s2231_cen
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · simp

lemma s2231 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.OrReaches n C C.output j → (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 → w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧ (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 → ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1)) ∧ (∀ F : Finset ℕ, (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), ∃ i ∈ F, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i ∧ ((e.1 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.2 ∈ PEqualNP.TopForm.side (n := n) C i 1) ∨ (e.2 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.1 ∈ PEqualNP.TopForm.side (n := n) C i 1))) → ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)), e3.1 ∈ T ∨ e3.2 ∈ T) := by
  intro n G _ C hNF hAO h1 h2
  have P1 := s2231_part1 n G C hNF hAO h1 h2
  refine ⟨P1, ?_⟩
  intro F hF
  refine ⟨F.biUnion (s2231_cen n C), ?_, ?_⟩
  · have hc1 : (F.biUnion (s2231_cen n C)).card ≤ F.sum (fun i => (s2231_cen n C i).card) :=
      Finset.card_biUnion_le
    have hc2 : F.sum (fun i => (s2231_cen n C i).card) ≤ F.sum (fun _ : ℕ => (1 : ℕ)) :=
      Finset.sum_le_sum (fun i _ => s2231_cen_card n C i)
    have hc3 : F.sum (fun _ : ℕ => (1 : ℕ)) = F.card := by simp
    exact le_trans hc1 (le_trans hc2 (le_of_eq hc3))
  · intro e he
    obtain ⟨i, hiF, hi, hop, hreach, hside⟩ := hF e he
    obtain ⟨_, _, hcard⟩ := P1 i hi hop hreach
    by_cases c0 : (PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1
    · have hc : s2231_cen n C i = PEqualNP.TopForm.side (n := n) C i 0 := by
        unfold s2231_cen; rw [if_pos c0]
      rcases hside with ⟨h, _⟩ | ⟨h, _⟩
      · left; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩
      · right; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩
    · have c1 : (PEqualNP.TopForm.side (n := n) C i 1).card ≤ 1 := hcard.resolve_left c0
      have hc : s2231_cen n C i = PEqualNP.TopForm.side (n := n) C i 1 := by
        unfold s2231_cen; rw [if_neg c0, if_pos c1]
      rcases hside with ⟨_, h⟩ | ⟨_, h⟩
      · right; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩
      · left; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma s2233_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma s2233_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [s2233_gateAt_eq hj]; exact List.getElem_mem hj

open PEqualNP.CleanedNonEdge

lemma s2233_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2233_orSets_char (n : ℕ) (gs : List Gate) :
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
      rw [s2233_orSets_len]; simp
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

lemma s2233_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := s2233_orSets_char n C.gates g k
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

lemma s2233_tail_step (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w, OrReaches n C w g → g ≠ w - n →
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        n + g ∈ (gateAt C k).inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h hne
    have hnw : n ≤ w := h.1
    obtain ⟨k0, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (s2233_orReaches_iff n C k0 g).mp h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · exact (hne (by omega)).elim
    · have hself : OrReaches n C (n + k0) k0 :=
        (s2233_orReaches_iff n C k0 k0).mpr ⟨hk, Or.inl rfl⟩
      by_cases hg : g = i - n
      · refine ⟨k0, hk, hself, hop, ?_⟩
        have hni : n ≤ i := hr.1
        have e : n + g = i := by omega
        rw [e]
        exact hi
      · obtain ⟨k, hkl, hrk, hopk, hin⟩ := ih i hlt hr hg
        exact ⟨k, hkl,
          (s2233_orReaches_iff n C k0 k).mpr ⟨hk, Or.inr ⟨hop, i, hi, hlt, hrk⟩⟩, hopk, hin⟩

def s2233_par (n : ℕ) (C : Circuit) (O : Finset ℕ) : Finset ℕ :=
  O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))

lemma s2233_par_card (n : ℕ) (C : Circuit) (O : Finset ℕ)
    (h : ∀ k ∈ O, (gateAt C k).inputs.length = 2) : (s2233_par n C O).card ≤ O.card * 2 := by
  unfold s2233_par
  calc (O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))).card
      ≤ ∑ k ∈ O, (((gateAt C k).inputs.toFinset).image (fun w => w - n)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ O, 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.card_image_le.trans
          ((List.toFinset_card_le _).trans (le_of_eq (h k hk)))
    _ = O.card * 2 := by rw [Finset.sum_const, smul_eq_mul]

lemma s2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hC hF
  obtain ⟨_, _, hlen⟩ := hC
  obtain ⟨O, hO⟩ : ∃ O : Finset ℕ, ∀ i, i ∈ O ↔ (i < C.gates.length ∧
      (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i) :=
      by
    have hfin : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i}.Finite := by
      apply (Finset.finite_toSet (Finset.range C.gates.length)).subset
      intro i hi
      have hi2 : i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
          OrReaches n C C.output i := Eq.mp Set.mem_setOf_eq hi
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hi2.1)
    refine ⟨hfin.toFinset, fun i => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hset : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} = (↑O : Set ℕ) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.mem_coe, hO]
  rw [hset, Set.ncard_coe_finset]
  have hdisj : Disjoint F O := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h1 := (hF a ha).2.1
    have h2 := ((hO a).mp hb).2.1
    rw [h1] at h2
    exact GateOp.noConfusion h2
  have hsub : F ∪ O ⊆ insert (C.output - n) (s2233_par n C O) := by
    intro g hg
    have hr : OrReaches n C C.output g := by
      rcases Finset.mem_union.mp hg with h | h
      · exact (hF g h).2.2
      · exact ((hO g).mp h).2.2
    by_cases hgo : g = C.output - n
    · exact Finset.mem_insert.mpr (Or.inl hgo)
    · obtain ⟨k, hk, hrk, hop, hin⟩ := s2233_tail_step n C g C.output hr hgo
      refine Finset.mem_insert.mpr (Or.inr ?_)
      unfold s2233_par
      exact Finset.mem_biUnion.mpr ⟨k, (hO k).mpr ⟨hk, hop, hrk⟩,
        Finset.mem_image.mpr ⟨n + g, List.mem_toFinset.mpr hin, by omega⟩⟩
  have hcard := s2233_par_card n C O (fun k hk => hlen _ (s2233_gateAt_mem ((hO k).mp hk).1))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 := Finset.card_insert_le (C.output - n) (s2233_par n C O)
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

def s2234_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2234_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2234_stepWire x := rfl

lemma s2234_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2234_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2234_stepWire]
    omega

lemma s2234_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2234_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2234_stepWire w g).length := by simp [s2234_stepWire]; omega
    rw [ih (s2234_stepWire w g) hlt]
    simp [s2234_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2234_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2234_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2234_wires_eq_foldl, s2234_foldl_stepWire_length, List.length_ofFn]

lemma s2234_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2234_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2234_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2234_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2234_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2234_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2234_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2234_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2234_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2234_foldl_stepWire_length, hpre_len]
  have hCj : s2234_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2234_W]
    rw [s2234_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2234_foldl_stepWire_getD_lt post (s2234_stepWire w0 gj) (n + k) (by simp [s2234_stepWire]; omega)]
    simp [s2234_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2234_W]
    rw [s2234_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2234_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2234_getD_ge_length w0 i (by omega)

lemma s2234_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2234_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2234_W]
  rw [s2234_wires_eq_foldl, s2234_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma s2234_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2234_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

lemma s2234_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma s2234_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2234_orStep_getD_lt n cs g k hk

lemma s2234_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2234_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2234_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2234_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2234_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2234_orFold_getD_lt n post _ m (by omega)]
    exact s2234_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2234_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma s2234_qorSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [s2234_orFold_length]
  simp

lemma s2234_qreach_iff (n : ℕ) (C : Circuit) (k g : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ OrReaches n C w g) := by
  have e : n + k - n = k := by omega
  constructor
  · intro h
    have h2 := h.2
    rw [e] at h2
    rcases (s2234_orSets_mem_iff n C k g hk).1 h2 with h3 | ⟨hop, w, hw, hn, hlt, hx⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, hlt, hn, hx⟩
  · intro h
    refine ⟨by omega, ?_⟩
    rw [e]
    refine (s2234_orSets_mem_iff n C k g hk).2 ?_
    rcases h with h | ⟨hop, w, hw, hlt, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hr.1, hlt, hr.2⟩

lemma s2234_qreach_bound (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    n ≤ w ∧ w - n < C.gates.length := by
  refine ⟨h.1, ?_⟩
  by_contra hc
  have h2 := h.2
  have hlen : (orSets n C).length ≤ w - n := by rw [s2234_qorSets_len]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen] at h2
  simp at h2

lemma s2234_qreach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := (s2234_qreach_iff n C k k hk).2 (Or.inl rfl)

lemma s2234_qreach_le (n : ℕ) (C : Circuit) (g : ℕ) : ∀ w : ℕ, OrReaches n C w g → n + g ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w g h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (s2234_qreach_iff n C k g hk).1 h with h3 | ⟨_, w', _, hlt, hr⟩
    · omega
    · have := ih w' hlt hr
      omega

lemma s2234_qreach_trans (n : ℕ) (C : Circuit) (i g : ℕ) (hg : OrReaches n C (n + i) g) :
    ∀ w : ℕ, OrReaches n C w i → OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w i h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (s2234_qreach_iff n C k i hk).1 h with h3 | ⟨hop, w', hw', hlt, hr⟩
    · rw [← h3]; exact hg
    · exact (s2234_qreach_iff n C k g hk).2 (Or.inr ⟨hop, w', hw', hlt, ih w' hlt hr⟩)

lemma s2234_qmem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n) :
    b ∈ PEqualNP.TopForm.orIn n C w ↔ ((b : ℕ) = w ∨ ∃ k, k < C.gates.length ∧
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (b : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma s2234_qorIn_eq_self (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    ∀ b ∈ PEqualNP.TopForm.orIn n C w, (b : ℕ) = w := by
  intro b hb
  rcases (s2234_qmem_orIn n C w b).1 hb with h | ⟨k', hk', hr, hop', hi⟩
  · exact h
  · exfalso
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w k' hr
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have e : n + k - n = k := by omega
    rw [e] at hw h2
    rcases (s2234_qreach_iff n C k k' h2).1 hr with h | ⟨hop, _⟩
    · rw [h] at hop'
      exact hw ⟨h1, h2, hop'⟩
    · exact hw ⟨h1, h2, hop⟩

lemma s2234_qorIn_small (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have h1 := s2234_qorIn_eq_self n C w hw a ha
  have h2 := s2234_qorIn_eq_self n C w hw b hb
  exact Fin.ext (by omega)

lemma s2234_qorIn_or (n : ℕ) (C : Circuit) (k a b : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    PEqualNP.TopForm.orIn n C (n + k) =
      PEqualNP.TopForm.orIn n C a ∪ PEqualNP.TopForm.orIn n C b := by
  have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
  have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
  ext i
  rw [Finset.mem_union, s2234_qmem_orIn, s2234_qmem_orIn, s2234_qmem_orIn]
  constructor
  · rintro (h | ⟨k', hk', hr, hop', hi⟩)
    · exfalso
      have := i.2
      omega
    · rcases (s2234_qreach_iff n C k k' hk).1 hr with h | ⟨_, w, hw, hwlt, hr'⟩
      · rw [h, hin, List.mem_cons, List.mem_singleton] at hi
        rcases hi with h4 | h4
        · exact Or.inl (Or.inl h4)
        · exact Or.inr (Or.inl h4)
      · rw [hin, List.mem_cons, List.mem_singleton] at hw
        rcases hw with h4 | h4
        · rw [h4] at hr'
          exact Or.inl (Or.inr ⟨k', hk', hr', hop', hi⟩)
        · rw [h4] at hr'
          exact Or.inr (Or.inr ⟨k', hk', hr', hop', hi⟩)
  · rintro ((h | ⟨k', hk', hr, hop', hi⟩) | (h | ⟨k', hk', hr, hop', hi⟩))
    · exact Or.inr ⟨k, hk, s2234_qreach_self n C k hk, hop, by rw [h]; exact hma⟩
    · exact Or.inr ⟨k', hk', (s2234_qreach_iff n C k k' hk).2 (Or.inr ⟨hop, a, hma, ha, hr⟩), hop', hi⟩
    · exact Or.inr ⟨k, hk, s2234_qreach_self n C k hk, hop, by rw [h]; exact hmb⟩
    · exact Or.inr ⟨k', hk', (s2234_qreach_iff n C k k' hk).2 (Or.inr ⟨hop, b, hmb, hb, hr⟩), hop', hi⟩

lemma s2234_qorIn_sub (n : ℕ) (C : Circuit) (i w : ℕ) (hr : OrReaches n C w i) :
    PEqualNP.TopForm.orIn n C (n + i) ⊆ PEqualNP.TopForm.orIn n C w := by
  intro b hb
  rcases (s2234_qmem_orIn n C (n + i) b).1 hb with h | ⟨k, hk, hr', hop, hi⟩
  · exfalso
    have := b.2
    omega
  · exact (s2234_qmem_orIn n C w b).2 (Or.inr ⟨k, hk, s2234_qreach_trans n C i k hr' w hr, hop, hi⟩)

lemma s2234_qval_reach (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : s2234_W n C x (n + g) = true) :
    ∀ w : ℕ, OrReaches n C w g → s2234_W n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w g h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (s2234_qreach_iff n C k g hk).1 h with h3 | ⟨hop, w', hw', hlt, hr⟩
    · rw [← h3]; exact hv
    · rw [s2234_W_gate n C x k hk, hop]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
      exact ⟨w', hw', by simp only [hlt, ite_true]; exact ih w' hlt hr⟩

lemma s2234_qval_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n)
    (hb : b ∈ PEqualNP.TopForm.orIn n C w) :
    s2234_W n C (fun r : Fin n => decide (r = b)) w = true := by
  rcases (s2234_qmem_orIn n C w b).1 hb with h | ⟨k, hk, hr, hop, hi⟩
  · rw [← h, s2234_W_input n C _ (b : ℕ) b.2]
    simp
  · refine s2234_qval_reach n C _ k ?_ w hr
    rw [s2234_W_gate n C _ k hk, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    have hlt : (b : ℕ) < n + k := by
      have := b.2
      omega
    refine ⟨(b : ℕ), hi, ?_⟩
    simp only [hlt, ite_true]
    rw [s2234_W_input n C _ (b : ℕ) b.2]
    simp

lemma s2234_qpart1 (n : ℕ) (C : Circuit)
    (h0 : ∀ a1 : Fin n, circuitFun n C (fun k1 => decide (k1 = a1)) = false)
    (i : ℕ) (hcard : 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card) :
    ¬ OrReaches n C C.output i := by
  intro hr
  have hpos : 0 < (PEqualNP.TopForm.orIn n C (n + i)).card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.1 hpos
  have h1 := s2234_qval_orIn n C (n + i) b hb
  have h2 := s2234_qval_reach n C _ i h1 C.output hr
  have h3 : s2234_W n C (fun r : Fin n => decide (r = b)) C.output = false := h0 b
  rw [h2] at h3
  cases h3

noncomputable def s2234_srv (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset ℕ :=
  @Finset.filter ℕ (fun i => (gateAt C i).op = GateOp.or ∧
    2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card ∧ ∃ w ∈ R, OrReaches n C w i)
    (fun _ => Classical.propDecidable _) (Finset.range C.gates.length)

lemma s2234_qmem_srv (n : ℕ) (C : Circuit) (R : Finset ℕ) (i : ℕ) :
    i ∈ s2234_srv n C R ↔ (i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card ∧ ∃ w ∈ R, OrReaches n C w i) := by
  unfold s2234_srv
  rw [@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _), Finset.mem_range]

lemma s2234_qsrv_mono (n : ℕ) (C : Circuit) (R R' : Finset ℕ) (h : R ⊆ R') :
    s2234_srv n C R ⊆ s2234_srv n C R' := by
  intro i hi
  obtain ⟨h1, h2, h3, w, hw, hr⟩ := (s2234_qmem_srv n C R i).1 hi
  exact (s2234_qmem_srv n C R' i).2 ⟨h1, h2, h3, w, h hw, hr⟩

lemma s2234_qcount (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    ∀ (m : ℕ) (R : Finset ℕ), (∀ w ∈ R, w < m) →
      (R.biUnion (PEqualNP.TopForm.orIn n C)).card ≤ (s2234_srv n C R).card + R.card := by
  intro m
  induction m with
  | zero =>
    intro R hR
    have hRe : R = ∅ := Finset.eq_empty_of_forall_notMem (fun w hw => by
      have := hR w hw
      omega)
    subst hRe
    simp
  | succ m ih =>
    intro R hR
    by_cases hm : m ∈ R
    · have hR0 : ∀ w ∈ R.erase m, w < m := by
        intro w hw
        have h1 := Finset.ne_of_mem_erase hw
        have h2 := hR w (Finset.mem_of_mem_erase hw)
        omega
      have hins : insert m (R.erase m) = R := Finset.insert_erase hm
      have hcardR : (R.erase m).card + 1 = R.card := Finset.card_erase_add_one hm
      have hU : R.biUnion (PEqualNP.TopForm.orIn n C) =
          PEqualNP.TopForm.orIn n C m ∪ (R.erase m).biUnion (PEqualNP.TopForm.orIn n C) := by
        rw [← Finset.biUnion_insert (a := m) (s := R.erase m)
          (t := PEqualNP.TopForm.orIn n C), hins]
      by_cases hs : n ≤ m ∧ m - n < C.gates.length ∧ (gateAt C (m - n)).op = GateOp.or ∧
          2 ≤ (PEqualNP.TopForm.orIn n C m).card
      · obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
        obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
        have e : n + k - n = k := by omega
        rw [e] at hs2 hs3
        have hmem : gateAt C k ∈ C.gates := by
          rw [s2234_gateAt_eq C k hs2]
          exact List.getElem_mem hs2
        have hl := hlen2 _ hmem
        obtain ⟨a, b, hin⟩ : ∃ a b, (gateAt C k).inputs = [a, b] := List.length_eq_two.1 hl
        have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
        have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
        have ha : a < n + k := hRB k hs2 a hma
        have hb : b < n + k := hRB k hs2 b hmb
        have hor := s2234_qorIn_or n C k a b hs2 hs3 hin ha hb
        have hR' : ∀ w ∈ insert a (insert b (R.erase (n + k))), w < n + k := by
          intro w hw
          rw [Finset.mem_insert, Finset.mem_insert] at hw
          rcases hw with h | h | h
          · omega
          · omega
          · exact hR0 w h
        have hih := ih _ hR'
        have hU' : (insert a (insert b (R.erase (n + k)))).biUnion (PEqualNP.TopForm.orIn n C) =
            R.biUnion (PEqualNP.TopForm.orIn n C) := by
          rw [hU, Finset.biUnion_insert, Finset.biUnion_insert, hor, Finset.union_assoc]
        have hc' : (insert a (insert b (R.erase (n + k)))).card ≤ (R.erase (n + k)).card + 2 := by
          have h1 := Finset.card_insert_le a (insert b (R.erase (n + k)))
          have h2 := Finset.card_insert_le b (R.erase (n + k))
          omega
        have hsub : s2234_srv n C (insert a (insert b (R.erase (n + k)))) ⊆ (s2234_srv n C R).erase k := by
          intro i hi
          obtain ⟨h1, h2, h3, w, hw, hr⟩ := (s2234_qmem_srv n C _ i).1 hi
          have hle := s2234_qreach_le n C i w hr
          have hwlt := hR' w hw
          rw [Finset.mem_erase]
          refine ⟨by omega, (s2234_qmem_srv n C R i).2 ⟨h1, h2, h3, ?_⟩⟩
          rw [Finset.mem_insert, Finset.mem_insert] at hw
          rcases hw with h | h | h
          · rw [h] at hr
            exact ⟨n + k, hm, (s2234_qreach_iff n C k i hs2).2 (Or.inr ⟨hs3, a, hma, ha, hr⟩)⟩
          · rw [h] at hr
            exact ⟨n + k, hm, (s2234_qreach_iff n C k i hs2).2 (Or.inr ⟨hs3, b, hmb, hb, hr⟩)⟩
          · exact ⟨w, Finset.mem_of_mem_erase h, hr⟩
        have hkmem : k ∈ s2234_srv n C R :=
          (s2234_qmem_srv n C R k).2 ⟨hs2, hs3, hs4, n + k, hm, s2234_qreach_self n C k hs2⟩
        have hc2 : ((s2234_srv n C R).erase k).card + 1 = (s2234_srv n C R).card :=
          Finset.card_erase_add_one hkmem
        have hc3 := Finset.card_le_card hsub
        rw [hU'] at hih
        omega
      · have hsmall : (PEqualNP.TopForm.orIn n C m).card ≤ 1 := by
          by_cases hs' : n ≤ m ∧ m - n < C.gates.length ∧ (gateAt C (m - n)).op = GateOp.or
          · by_contra hc
            exact hs ⟨hs'.1, hs'.2.1, hs'.2.2, by omega⟩
          · exact s2234_qorIn_small n C m hs'
        have hih := ih _ hR0
        have hmono := Finset.card_le_card (s2234_qsrv_mono n C _ _ (Finset.erase_subset m R))
        have hun := Finset.card_union_le (PEqualNP.TopForm.orIn n C m)
          ((R.erase m).biUnion (PEqualNP.TopForm.orIn n C))
        rw [hU]
        omega
    · refine ih R (fun w hw => ?_)
      have h1 := hR w hw
      have h2 : w ≠ m := fun h => hm (h ▸ hw)
      omega

lemma s2234_qfinal (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (F : Finset ℕ)
    (ctr : ℕ → Fin n) (lf : ℕ → ℕ)
    (hG : PEqualNP.TopForm.NoFourCycle G) (hRB : ReadsBack n C)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hadj : ∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) :
    ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  have key : ∀ (S : Set ℕ) (A B : ℕ), (∀ i, i ∈ S ↔ i ∈ s2234_srv n C (F.image lf)) →
      A ≤ (s2234_srv n C (F.image lf)).card + B → A ≤ S.ncard + B := by
    intro S A B hS hA
    have hSe : S = ((s2234_srv n C (F.image lf) : Finset ℕ) : Set ℕ) := by
      ext i
      exact (hS i).trans Finset.mem_coe.symm
    rw [hSe, Set.ncard_coe_finset]
    exact hA
  refine key _ _ _ ?_ ?_
  · intro i
    rw [Set.mem_ofPred_eq, s2234_qmem_srv]
    constructor
    · rintro ⟨h1, h2, h3, j, hj, hr⟩
      exact ⟨h1, h2, h3, lf j, Finset.mem_image_of_mem lf hj, hr⟩
    · rintro ⟨h1, h2, h3, w, hw, hr⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
      exact ⟨h1, h2, h3, j, hj, hr⟩
  · have hpt : ∀ c : Fin n, ∀ X : Finset (Fin n),
        (∀ b, b ∈ X ↔ ∃ j ∈ F, ctr j = c ∧ b ∈ PEqualNP.TopForm.orIn n C (lf j)) →
        X.card ≤ (s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)).card +
          (F.filter (fun j => ctr j = c)).card := by
      intro c X hX
      have hXe : X = ((F.filter (fun j => ctr j = c)).image lf).biUnion
          (PEqualNP.TopForm.orIn n C) := by
        ext b
        rw [hX b, Finset.mem_biUnion]
        constructor
        · rintro ⟨j, hj, hc, hb⟩
          exact ⟨lf j, Finset.mem_image_of_mem lf (Finset.mem_filter.2 ⟨hj, hc⟩), hb⟩
        · rintro ⟨w, hw, hb⟩
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
          obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
          exact ⟨j, hj1, hj2, hb⟩
      have hc := s2234_qcount n C hRB hlen2
        (((F.filter (fun j => ctr j = c)).image lf).sup id + 1)
        ((F.filter (fun j => ctr j = c)).image lf)
        (fun w hw => Nat.lt_succ_of_le (Finset.le_sup (f := id) hw))
      have hi := Finset.card_image_le (s := F.filter (fun j => ctr j = c)) (f := lf)
      rw [hXe]
      omega
    have hdisj : ∀ c c' : Fin n, c ≠ c' → ∀ i,
        i ∈ s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf) →
        i ∈ s2234_srv n C ((F.filter (fun j => ctr j = c')).image lf) → False := by
      intro c c' hne i h1 h2
      obtain ⟨hi, hop, hcard, w, hw, hr⟩ := (s2234_qmem_srv n C _ i).1 h1
      obtain ⟨_, _, _, w', hw', hr'⟩ := (s2234_qmem_srv n C _ i).1 h2
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hw'
      obtain ⟨hjF, hjc⟩ := Finset.mem_filter.1 hj
      obtain ⟨hjF', hjc'⟩ := Finset.mem_filter.1 hj'
      refine absurd (le_trans hcard (le_trans (Finset.card_le_card ?_) (hG c c' hne))) (by omega)
      intro b hb
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [← hjc]
        exact hadj j hjF b (s2234_qorIn_sub n C i (lf j) hr hb)
      · rw [← hjc']
        exact hadj j' hjF' b (s2234_qorIn_sub n C i (lf j') hr' hb)
    have hpd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
        (fun c => s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)) := by
      intro c _ c' _ hne
      exact Finset.disjoint_left.2 (fun i h1 h2 => hdisj c c' hne i h1 h2)
    have hsum1 : ∑ c : Fin n, (s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)).card ≤
        (s2234_srv n C (F.image lf)).card := by
      rw [← Finset.card_biUnion hpd]
      apply Finset.card_le_card
      intro i hi
      obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.1 hi
      exact s2234_qsrv_mono n C _ _ (Finset.image_subset_image (Finset.filter_subset _ _)) hc
    have hsum2 : ∑ c : Fin n, (F.filter (fun j => ctr j = c)).card = F.card :=
      (Finset.card_eq_sum_card_fiberwise (f := ctr) (s := F) (t := Finset.univ)
        (by intro x _; simp)).symm
    have hpt2 : ∀ c ∈ (Finset.univ : Finset (Fin n)), (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤
        (s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)).card +
          (F.filter (fun j => ctr j = c)).card := fun c _ => hpt c _ (fun b => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    refine le_trans (Finset.sum_le_sum hpt2) ?_
    rw [Finset.sum_add_distrib]
    exact add_le_add hsum1 (le_of_eq hsum2)

lemma s2234 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  intro n G hdec C F ctr lf hG hAO h0 hadj
  refine ⟨?_, ?_⟩
  · intro i _ _ hcard _
    exact s2234_qpart1 n C h0 i hcard
  · exact s2234_qfinal n G C F ctr lf hG hAO.2.1 hAO.2.2 hadj

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma three_count (L : ℕ) (F : Finset ℕ) (A B : Set ℕ)
    (hF : ∀ j ∈ F, j < L) (hA : ∀ i ∈ A, i < L) (hB : ∀ i ∈ B, i < L)
    (hFA : ∀ j ∈ F, j ∉ A) (hFB : ∀ j ∈ F, j ∉ B) (hAB : ∀ i ∈ A, i ∉ B) :
    F.card + A.ncard + B.ncard ≤ L := by
  classical
  have hAf : A.Finite := (Set.finite_lt_nat L).subset (fun i hi => hA i hi)
  have hBf : B.Finite := (Set.finite_lt_nat L).subset (fun i hi => hB i hi)
  rw [Set.ncard_eq_toFinset_card A hAf, Set.ncard_eq_toFinset_card B hBf]
  have h1 : Disjoint F hAf.toFinset := by
    rw [Finset.disjoint_left]
    intro j hj hj2
    exact hFA j hj ((Set.Finite.mem_toFinset hAf).mp hj2)
  have h2 : Disjoint (F ∪ hAf.toFinset) hBf.toFinset := by
    rw [Finset.disjoint_left]
    intro j hj hj2
    have hjB := (Set.Finite.mem_toFinset hBf).mp hj2
    rcases Finset.mem_union.mp hj with h | h
    · exact hFB j h hjB
    · exact hAB j ((Set.Finite.mem_toFinset hAf).mp h) hjB
  have h3 : (F ∪ hAf.toFinset) ∪ hBf.toFinset ⊆ Finset.range L := by
    intro j hj
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp hj with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact hF j h
      · exact hA j ((Set.Finite.mem_toFinset hAf).mp h)
    · exact hB j ((Set.Finite.mem_toFinset hBf).mp h)
  have h4 := Finset.card_le_card h3
  rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1, Finset.card_range] at h4
  exact h4

lemma sum_card_ge {n : ℕ} (E : Finset (Fin n × Fin n)) (U : Fin n → Finset (Fin n))
    (hlt : ∀ e ∈ E, e.1 < e.2) (h : ∀ e ∈ E, e.2 ∈ U e.1 ∨ e.1 ∈ U e.2) :
    E.card ≤ ∑ c : Fin n, (U c).card := by
  classical
  have hs := Finset.card_sigma (Finset.univ : Finset (Fin n)) U
  rw [← hs]
  have key1 : ∀ e ∈ E, (if e.2 ∈ U e.1 then (⟨e.1, e.2⟩ : Σ _ : Fin n, Fin n) else ⟨e.2, e.1⟩)
      ∈ (Finset.univ : Finset (Fin n)).sigma U := by
    intro e he
    by_cases hc : e.2 ∈ U e.1
    · rw [if_pos hc]
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hc⟩
    · rw [if_neg hc]
      rcases h e he with h1 | h1
      · exact absurd h1 hc
      · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, h1⟩
  have key2 : ∀ e e2 : Fin n × Fin n, e.1 < e.2 → e2.1 < e2.2 →
      (if e.2 ∈ U e.1 then (⟨e.1, e.2⟩ : Σ _ : Fin n, Fin n) else ⟨e.2, e.1⟩) =
      (if e2.2 ∈ U e2.1 then (⟨e2.1, e2.2⟩ : Σ _ : Fin n, Fin n) else ⟨e2.2, e2.1⟩) → e = e2 := by
    intro e e2 h1 h2 heq
    by_cases c1 : e.2 ∈ U e.1
    · by_cases c2 : e2.2 ∈ U e2.1
      · rw [if_pos c1, if_pos c2] at heq
        have ha : e.1 = e2.1 := congrArg Sigma.fst heq
        have hb : e.2 = e2.2 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        exact Prod.ext ha hb
      · rw [if_pos c1, if_neg c2] at heq
        have ha : e.1 = e2.2 := congrArg Sigma.fst heq
        have hb : e.2 = e2.1 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        rw [ha, hb] at h1
        exact absurd h1 (lt_asymm h2)
    · by_cases c2 : e2.2 ∈ U e2.1
      · rw [if_neg c1, if_pos c2] at heq
        have ha : e.2 = e2.1 := congrArg Sigma.fst heq
        have hb : e.1 = e2.2 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        rw [ha, hb] at h1
        exact absurd h1 (lt_asymm h2)
      · rw [if_neg c1, if_neg c2] at heq
        have ha : e.2 = e2.2 := congrArg Sigma.fst heq
        have hb : e.1 = e2.1 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        exact Prod.ext hb ha
  refine Finset.card_le_card_of_injOn
    (fun e => if e.2 ∈ U e.1 then (⟨e.1, e.2⟩ : Σ _ : Fin n, Fin n) else ⟨e.2, e.1⟩) ?_ ?_
  · intro e he
    exact key1 e he
  · intro e he e2 he2 heq
    exact key2 e e2 (hlt e he) (hlt e2 he2) heq

lemma core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (E : Finset (Fin n × Fin n))
    (hlt : ∀ e ∈ E, e.1 < e.2)
    (h30 : ∀ e ∈ E, ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      ((e.1 ∈ side (n := n) C j 0 ∧ e.2 ∈ side (n := n) C j 1) ∨
        (e.2 ∈ side (n := n) C j 0 ∧ e.1 ∈ side (n := n) C j 1)))
    (h31a : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → OrReaches n C C.output j →
      (∀ w : Fin n, w ∈ side (n := n) C j 0 → w ∉ side (n := n) C j 1) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 → G.Adj u v) ∧
      ((side (n := n) C j 0).card ≤ 1 ∨ (side (n := n) C j 1).card ≤ 1))
    (h31b : ∀ F : Finset ℕ, (∀ e ∈ E, ∃ i ∈ F, i < C.gates.length ∧
        (gateAt C i).op = GateOp.and ∧ OrReaches n C C.output i ∧
        ((e.1 ∈ side (n := n) C i 0 ∧ e.2 ∈ side (n := n) C i 1) ∨
          (e.2 ∈ side (n := n) C i 0 ∧ e.1 ∈ side (n := n) C i 1))) →
      ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ E, e3.1 ∈ T ∨ e3.2 ∈ T)
    (h33 : ∀ F : Finset ℕ, (∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        OrReaches n C C.output j) →
      F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i} + 1)
    (h34 : ∀ (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ),
      (∀ j ∈ F, ∀ b : Fin n, b ∈ orIn n C (lf j) → G.Adj (ctr j) b) →
      (∀ i < C.gates.length, (gateAt C i).op = GateOp.or → 2 ≤ (orIn n C (n + i)).card →
        (∃ j1 ∈ F, OrReaches n C (lf j1) i) → ¬ OrReaches n C C.output i) ∧
      ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n =>
        ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))).card ≤
        Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
          2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2} + F.card) :
    ∃ T : Finset (Fin n), (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧ E.card + T.card ≤ C.size + 1 := by
  classical
  by_cases hE : E = ∅
  · subst hE
    refine ⟨∅, ?_, ?_⟩
    · intro e he
      simp at he
    · rw [Finset.card_empty, Finset.card_empty]
      exact Nat.zero_le _
  obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hE
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ, ∀ j, j ∈ F ↔ (j < C.gates.length ∧
      (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty) :=
    ⟨(Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty),
      fun j => by rw [Finset.mem_filter, Finset.mem_range]⟩
  have hper : ∀ j : ℕ, ∃ (c : Fin n) (l : ℕ), j ∈ F →
      (∀ b : Fin n, b ∈ orIn n C l → G.Adj c b) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 →
        (c = u ∧ v ∈ orIn n C l) ∨ (c = v ∧ u ∈ orIn n C l)) := by
    intro j
    by_cases hj : j ∈ F
    · obtain ⟨hjl, hand, hor, hn0, hn1⟩ := (hF j).mp hj
      obtain ⟨hdis, hadj, hcard⟩ := h31a j hjl hand hor
      rcases hcard with hc | hc
      · obtain ⟨c, hc0⟩ := hn0
        refine ⟨c, opnd C j 1, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact hadj c hc0 b hb
        · intro u hu v hv
          exact Or.inl ⟨Finset.card_le_one.mp hc c hc0 u hu, hv⟩
      · obtain ⟨c, hc1⟩ := hn1
        refine ⟨c, opnd C j 0, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact (hadj b hb c hc1).symm
        · intro u hu v hv
          exact Or.inr ⟨Finset.card_le_one.mp hc c hc1 v hv, hu⟩
    · exact ⟨e0.1, 0, fun h => absurd h hj⟩
  choose ctr lf hcl using hper
  have hw : ∀ e ∈ E, ∃ i ∈ F, i < C.gates.length ∧
      (gateAt C i).op = GateOp.and ∧ OrReaches n C C.output i ∧
      ((e.1 ∈ side (n := n) C i 0 ∧ e.2 ∈ side (n := n) C i 1) ∨
        (e.2 ∈ side (n := n) C i 0 ∧ e.1 ∈ side (n := n) C i 1)) := by
    intro e he
    obtain ⟨j, hjl, hand, hor, hs⟩ := h30 e he
    refine ⟨j, (hF j).mpr ⟨hjl, hand, hor, ?_, ?_⟩, hjl, hand, hor, hs⟩
    · rcases hs with hs | hs
      · exact ⟨e.1, hs.1⟩
      · exact ⟨e.2, hs.1⟩
    · rcases hs with hs | hs
      · exact ⟨e.2, hs.2⟩
      · exact ⟨e.1, hs.2⟩
  obtain ⟨T, hTc, hTcov⟩ := h31b F hw
  have hFand : ∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j := by
    intro j hj
    obtain ⟨ha, hb, hc, _⟩ := (hF j).mp hj
    exact ⟨ha, hb, hc⟩
  have h3 := h33 F hFand
  obtain ⟨h4a, h4b⟩ := h34 F ctr lf (fun j hj => (hcl j hj).1)
  have hEsum := le_trans (sum_card_ge E (fun c => Finset.univ.filter (fun b2 : Fin n =>
      ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))) hlt (by
    intro e he
    obtain ⟨j, hjF, _, _, _, hs⟩ := hw e he
    rcases hs with hs | hs
    · rcases (hcl j hjF).2 e.1 hs.1 e.2 hs.2 with h | h
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
    · rcases (hcl j hjF).2 e.2 hs.1 e.1 hs.2 with h | h
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩))) h4b
  have hcount := three_count C.gates.length F
    {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i}
    {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
      2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2}
    (fun j hj => (hFand j hj).1) (fun i hi => hi.1) (fun i hi => hi.1)
    (fun j hj hjA => by
      have h1 := (hFand j hj).2.1
      have h2 : (gateAt C j).op = GateOp.or := hjA.2.1
      rw [h2] at h1
      cases h1)
    (fun j hj hjB => by
      have h1 := (hFand j hj).2.1
      have h2 : (gateAt C j).op = GateOp.or := hjB.2.1
      rw [h2] at h1
      cases h1)
    (fun i hi hiB => h4a i hi.1 hi.2.1 hiB.2.2.1 hiB.2.2.2 hi.2.2)
  refine ⟨T, hTcov, ?_⟩
  have hsz : C.size = C.gates.length := rfl
  rw [hsz]
  omega

lemma S35_main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → ∃ T : Finset (Fin n), (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), e.1 ∈ T ∨ e.2 ∈ T) ∧ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).card + T.card ≤ C.size + 1 := by
  intro n G _ C h4 hA h1 h2
  have h31 := s2231 n G C h4 hA h1 h2
  exact core n G C _ (fun e he => (Finset.mem_filter.mp he).2.1)
    (fun e he => s2230 n C e.1 e.2 hA h1 (Finset.mem_filter.mp he).2.1
      (Finset.mem_filter.mp he).2.2.2)
    h31.1 h31.2 (fun F => s2233 n C F hA) (fun F ctr lf => s2234 n G C F ctr lf h4 hA h1)

lemma cor_setList_pair {n : ℕ} (a b : Fin n) (hab : a < b) :
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

lemma main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → PEqualNP.ReadK.IsReadK n C 1 → ∃ T : Finset (Fin n), (∀ u2 v2 : Fin n, G.Adj u2 v2 → u2 ∈ T ∨ v2 ∈ T) ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  intro n G _ C h4 hAO hfun hread
  have hw1 : ∀ a1 : Fin n,
      PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false := by
    intro a1
    rw [hfun, decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    have hu1 : u = a1 := by simpa using hu
    have hv1 : v = a1 := by simpa using hv
    exact huv.ne (hu1.trans hv1.symm)
  have hw2 : ∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 →
      PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false := by
    intro a2 b2 hne hna
    rw [hfun, decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    have hu1 : u = a2 ∨ u = b2 := by simpa using hu
    have hv1 : v = a2 ∨ v = b2 := by simpa using hv
    rcases hu1 with h1 | h1 <;> rcases hv1 with h2 | h2
    · exact huv.ne (h1.trans h2.symm)
    · rw [h1, h2] at huv
      exact hna huv
    · rw [h1, h2] at huv
      exact hna huv.symm
    · exact huv.ne (h1.trans h2.symm)
  have hrd : ∀ a b : Fin n, a < b → G.Adj a b →
      PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = true := by
    intro a b hab hadj
    have hpi : PEqualNP.ReadK.IsPrimeImplicant n C ({a, b} : Finset (Fin n)) := by
      constructor
      · rw [hfun, decide_eq_true_eq]
        exact ⟨a, b, hadj, by simp [PEqualNP.ReadK.setInput], by simp [PEqualNP.ReadK.setInput]⟩
      · intro T hT
        rw [hfun, decide_eq_false_iff_not]
        rintro ⟨u, v, huv, hu, hv⟩
        have hu1 : u ∈ T := by simpa [PEqualNP.ReadK.setInput] using hu
        have hv1 : v ∈ T := by simpa [PEqualNP.ReadK.setInput] using hv
        obtain ⟨hsub, hnot⟩ := Finset.ssubset_def.mp (Finset.mem_ssubsets.mp hT)
        have hu2 := hsub hu1
        have hv2 := hsub hv1
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu2 hv2
        have hboth : a ∈ T ∧ b ∈ T := by
          rcases hu2 with h1 | h1 <;> rcases hv2 with h2 | h2
          · exact absurd (h1.trans h2.symm) huv.ne
          · rw [h1] at hu1
            rw [h2] at hv1
            exact ⟨hu1, hv1⟩
          · rw [h1] at hu1
            rw [h2] at hv1
            exact ⟨hv1, hu1⟩
          · exact absurd (h1.trans h2.symm) huv.ne
        apply hnot
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · rw [hx]
          exact hboth.1
        · rw [hx]
          exact hboth.2
    have h1 := hread ({a, b} : Finset (Fin n)) hpi
    rw [cor_setList_pair a b hab] at h1
    exact h1
  obtain ⟨T, hT, hcard⟩ := S35_main_aux n G C h4 hAO hw1 hw2
  refine ⟨T, ?_, ?_⟩
  · intro u2 v2 huv
    rcases lt_trichotomy u2 v2 with hlt | heq | hgt
    · exact hT (u2, v2) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hlt, huv, hrd u2 v2 hlt huv⟩)
    · exact absurd heq huv.ne
    · exact (hT (v2, u2) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hgt, huv.symm, hrd v2 u2 hgt huv.symm⟩)).symm
  · have hsub : G.edgeFinset ⊆ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).image (fun e : Fin n × Fin n => Sym2.mk e.1 e.2) := by
      intro e he
      obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
      rw [SimpleGraph.mem_edgeFinset] at he
      have he2 : Sym2.mk u v ∈ G.edgeSet := he
      have huv : G.Adj u v := (SimpleGraph.mem_edgeSet G).mp he2
      rcases lt_trichotomy u v with hlt | heq | hgt
      · exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hlt, huv, hrd u v hlt huv⟩, rfl⟩
      · exact absurd heq huv.ne
      · exact Finset.mem_image.mpr ⟨(v, u), Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hgt, huv.symm, hrd v u hgt huv.symm⟩, Sym2.eq_swap⟩
    have hle := (Finset.card_le_card hsub).trans Finset.card_image_le
    exact le_trans (Nat.add_le_add_right hle T.card) hcard

end General


def cross {m n : ℕ} (E : Finset (Fin m × Fin n)) : (Fin m ⊕ Fin n) → (Fin m ⊕ Fin n) → Prop
  | .inl p, .inr q => (p,q) ∈ E
  | .inr q, .inl p => (p,q) ∈ E
  | _, _ => False

def graph {m n : ℕ} (E : Finset (Fin m × Fin n)) : SimpleGraph (Fin (m+n)) where
  Adj u v := cross E (finSumFinEquiv.symm u) (finSumFinEquiv.symm v)
  symm := ⟨by
    intro u v
    cases finSumFinEquiv.symm u <;> cases finSumFinEquiv.symm v <;> simp [cross]⟩
  loopless := ⟨by
    intro u
    cases finSumFinEquiv.symm u <;> simp [cross]⟩

lemma noRectangle {m n : ℕ} (E : Finset (Fin m × Fin n))
    (hf : ∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) :
    @PEqualNP.TopForm.NoFourCycle _ (graph E) (Classical.decRel _) := by
  classical
  intro a b hab
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨hau,hbu⟩ := (Finset.mem_filter.mp hu).2
  obtain ⟨hav,hbv⟩ := (Finset.mem_filter.mp hv).2
  by_contra huv
  cases a using Fin.addCases <;> cases b using Fin.addCases <;>
    cases u using Fin.addCases <;> cases v using Fin.addCases <;>
    simp [graph,cross] at hau hbu hav hbv hab huv
  all_goals apply hf _ _ _ _ (by assumption) (by assumption) <;> exact ⟨by assumption,by assumption,by assumption,by assumption⟩

lemma counts {m n : ℕ} (E : Finset (Fin m × Fin n)) :
    E.card ≤ (letI := Classical.decRel (graph E).Adj; (graph E).edgeFinset.card) := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : Fin m × Fin n => Sym2.mk (Fin.castAdd n p.1) (Fin.natAdd m p.2))
  · intro p hp
    rw [Finset.mem_coe,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    simpa [graph,cross] using hp
  · rintro ⟨a,b⟩ _ ⟨c,d⟩ _ eq
    rcases (Sym2.mk_eq_mk_iff (p := (Fin.castAdd n a, Fin.natAdd m b)) (q := (Fin.castAdd n c, Fin.natAdd m d))).mp eq with forward|reverse
    · have hf := congrArg Prod.fst forward
      have hs := congrArg Prod.snd forward
      exact Prod.ext (by simpa using hf) (by simpa using hs)
    · have h : Fin.castAdd n a = Fin.natAdd m d := congrArg Prod.fst reverse
      have h' := congrArg Fin.val h
      simp at h'
      omega


lemma bipartite_cover : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → PEqualNP.ReadK.IsReadK (x1 + x2) x4 (1 : ℕ) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro m n E C rect ao computes readOne
  let G := graph E
  letI : DecidableRel G.Adj := Classical.decRel _
  have hfunc (x : Fin (m+n) → Bool) :
      PEqualNP.MetaComplexity.circuitFun (m+n) C x =
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
    rw [computes]
    congr 1
    apply propext
    constructor
    · rintro ⟨p,l,he,hp,hl⟩
      exact ⟨Fin.castAdd n p,Fin.natAdd m l,by simpa [G,graph,cross] using he,hp,hl⟩
    · rintro ⟨u,v,ha,hu,hv⟩
      cases u using Fin.addCases <;> cases v using Fin.addCases <;> simp [G,graph,cross] at ha
      · exact ⟨_,_,ha,hu,hv⟩
      · exact ⟨_,_,ha,hv,hu⟩
  obtain ⟨T,covers,bound⟩ := General.main_aux (m+n) G C (noRectangle E rect) ao hfunc readOne
  let S := T.map finSumFinEquiv.symm.toEmbedding
  refine ⟨S.toLeft,S.toRight,?_,?_⟩
  · rintro ⟨p,l⟩ h
    have hit := covers (Fin.castAdd n p) (Fin.natAdd m l) (by simpa [G,graph,cross] using h)
    rcases hit with hp|hl
    · left
      apply Finset.mem_toLeft.mpr
      exact Finset.mem_map.mpr ⟨_,hp,finSumFinEquiv_symm_apply_castAdd p⟩
    · right
      apply Finset.mem_toRight.mpr
      exact Finset.mem_map.mpr ⟨_,hl,finSumFinEquiv_symm_apply_natAdd l⟩
  · have eq : S.toLeft.card + S.toRight.card = T.card := Finset.card_toLeft_add_card_toRight.trans (Finset.card_map _)
    have le : E.card ≤ G.edgeFinset.card := counts E
    omega

lemma lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
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

lemma cardL {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ p ∈ A, (B.filter (fun w => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

lemma cardR {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ w ∈ B, (A.filter (fun p => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.card_filter]

lemma cover {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
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


lemma sharpReadOne (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (hread : PEqualNP.ReadK.IsReadK (N + N) C 1) :
    N * (q + 2) - 1 ≤ C.size := by
  classical
  let E : Finset (Fin N × Fin N) :=
    (Finset.univ ×ˢ Finset.univ).filter (fun e => I e.1 e.2)
  have hrect : ∀ (p p' : Fin N) (l l' : Fin N), p ≠ p' → l ≠ l' →
      ¬ ((p,l) ∈ E ∧ (p,l') ∈ E ∧ (p',l) ∈ E ∧ (p',l') ∈ E) := by
    intro p p' l l' hp hl' h
    exact hl' ((hu p p' hp).unique
      ⟨(Finset.mem_filter.mp h.1).2, (Finset.mem_filter.mp h.2.2.1).2⟩
      ⟨(Finset.mem_filter.mp h.2.1).2, (Finset.mem_filter.mp h.2.2.2).2⟩)
  have hfunE : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
      decide (∃ p l : Fin N, (p,l) ∈ E ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true) := by
    intro z
    simpa [E] using hfun z
  obtain ⟨A, B, hc, hbound⟩ := bipartite_cover N N E C hrect hAO hfunE hread
  have hcover : ∀ p l : Fin N, I p l → p ∈ A ∨ l ∈ B := by
    intro p l hpl
    exact hc (p,l) (by simp [E, hpl])
  have hcard : E.card = N * (q + 1) := by
    unfold E
    rw [cardR, Finset.sum_congr rfl (fun l _ => hl l), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hcov : N ≤ A.card + B.card :=
    cover q I hl (lines_through q N I hq hN hl hu) A B hcover
  have hsize : N * (q + 2) ≤ C.size + 1 := by
    calc
      N * (q + 2) = E.card + N := by rw [hcard]; ring
      _ ≤ E.card + (A.card + B.card) := Nat.add_le_add_left hcov E.card
      _ ≤ C.size + 1 := by simpa [Nat.add_assoc] using hbound
  omega

end Sharp

lemma normalization_iff_bound (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    (∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y =
        decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧
          y (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1) ↔
      N * (q + 2) - 1 ≤ C.size := by
  constructor
  · rintro ⟨D, hAO, hfun, hsize, hread⟩
    exact (Sharp.sharpReadOne q N I D hq hN hL hU hAO hfun hread).trans hsize
  · exact normalization_given_bound q N I C hL



namespace ThreeClause

def Hits {n : ℕ} (A B C : Finset (Fin n)) (u v : Fin n) : Prop :=
  (u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B) ∧ (u ∈ C ∨ v ∈ C)

def NoCentre {n : ℕ} (A B C : Finset (Fin n)) : Prop :=
  ∀ c : Fin n, ∃ u v : Fin n, Hits A B C u v ∧ u ≠ c ∧ v ≠ c

lemma overlap_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (A B C : Finset (Fin n))
    (hsound : ∀ u v, Hits A B C u v → G.Adj u v) (hno : NoCentre A B C) :
    (A ∩ B).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  obtain ⟨hxa, hxb⟩ := Finset.mem_inter.mp hx
  obtain ⟨hya, hyb⟩ := Finset.mem_inter.mp hy
  have unique : ∀ c ∈ C, ∀ d ∈ C, c = d := by
    intro c hc d hd
    apply Finset.card_le_one.mp (hfour x y hxy)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hsound x c ⟨Or.inl hxa, Or.inl hxb, Or.inr hc⟩,
        hsound y c ⟨Or.inl hya, Or.inl hyb, Or.inr hc⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hsound x d ⟨Or.inl hxa, Or.inl hxb, Or.inr hd⟩,
        hsound y d ⟨Or.inl hya, Or.inl hyb, Or.inr hd⟩⟩
  obtain ⟨u, v, huv, _, _⟩ := hno x
  obtain ⟨c, hc⟩ : C.Nonempty := huv.2.2.elim (fun h => ⟨u, h⟩) (fun h => ⟨v, h⟩)
  obtain ⟨u', v', huv', huc, hvc⟩ := hno c
  exact huv'.2.2.elim (fun h => huc (unique u' h c hc))
    (fun h => hvc (unique v' h c hc))

lemma overlaps_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (A B C : Finset (Fin n))
    (hsound : ∀ u v, Hits A B C u v → G.Adj u v) (hno : NoCentre A B C) :
    (A ∩ B).card ≤ 1 ∧ (A ∩ C).card ≤ 1 ∧ (B ∩ C).card ≤ 1 := by
  refine ⟨overlap_small G hfour A B C hsound hno, ?_, ?_⟩
  · apply overlap_small G hfour A C B
    · intro u v h
      exact hsound u v ⟨h.1, h.2.2, h.2.1⟩
    · intro c
      obtain ⟨u, v, h, hu, hv⟩ := hno c
      exact ⟨u, v, ⟨h.1, h.2.2, h.2.1⟩, hu, hv⟩
  · apply overlap_small G hfour B C A
    · intro u v h
      exact hsound u v ⟨h.2.2, h.1, h.2.1⟩
    · intro c
      obtain ⟨u, v, h, hu, hv⟩ := hno c
      exact ⟨u, v, ⟨h.2.1, h.2.2, h.1⟩, hu, hv⟩

lemma one_overlap_empty {n : ℕ} (G : SimpleGraph (Fin n))
    (htri : ∀ u v w, ¬ (G.Adj u v ∧ G.Adj v w ∧ G.Adj w u))
    (A B C : Finset (Fin n)) (hsound : ∀ u v, Hits A B C u v → G.Adj u v) :
    A ∩ B = ∅ ∨ A ∩ C = ∅ ∨ B ∩ C = ∅ := by
  classical
  by_cases hab : A ∩ B = ∅
  · exact Or.inl hab
  by_cases hac : A ∩ C = ∅
  · exact Or.inr (Or.inl hac)
  by_cases hbc : B ∩ C = ∅
  · exact Or.inr (Or.inr hbc)
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hab
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hac
  obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hbc
  obtain ⟨hua, hub⟩ := Finset.mem_inter.mp hu
  obtain ⟨hva, hvc⟩ := Finset.mem_inter.mp hv
  obtain ⟨hwb, hwc⟩ := Finset.mem_inter.mp hw
  exact False.elim (htri u v w
    ⟨hsound u v ⟨Or.inl hua, Or.inl hub, Or.inr hvc⟩,
      hsound v w ⟨Or.inl hva, Or.inr hwb, Or.inl hvc⟩,
      hsound w u ⟨Or.inr hua, Or.inl hwb, Or.inl hwc⟩⟩)

lemma cover_from_overlaps {n : ℕ} (A B C : Finset (Fin n)) (hbc : B ∩ C = ∅)
    (u v : Fin n) (h : Hits A B C u v) :
    u ∈ (A ∩ B) ∪ (A ∩ C) ∨ v ∈ (A ∩ B) ∪ (A ∩ C) := by
  have impossible (x : Fin n) (hb : x ∈ B) (hc : x ∈ C) : False := by
    have hh : x ∈ B ∩ C := Finset.mem_inter.mpr ⟨hb, hc⟩
    simp only [hbc, Finset.notMem_empty] at hh
  rcases h with ⟨ha | ha, hb | hb, hc | hc⟩
  · exact Or.inl (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, hb⟩))
  · exact Or.inl (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, hb⟩))
  · exact Or.inl (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ha, hc⟩))
  · exact (impossible v hb hc).elim
  · exact (impossible u hb hc).elim
  · exact Or.inr (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ha, hc⟩))
  · exact Or.inr (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, hb⟩))
  · exact Or.inr (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, hb⟩))

lemma cover_large {n : ℕ} (A B C T : Finset (Fin n))
    (hactive : ∃ u v, Hits A B C u v) (hno : NoCentre A B C)
    (hcover : ∀ u v, Hits A B C u v → u ∈ T ∨ v ∈ T) : 1 < T.card := by
  obtain ⟨u, v, huv⟩ := hactive
  obtain ⟨c, hc⟩ : T.Nonempty := (hcover u v huv).elim (fun h => ⟨u, h⟩) (fun h => ⟨v, h⟩)
  by_contra hn
  have hsmall : T.card ≤ 1 := by omega
  obtain ⟨u', v', huv', huc, hvc⟩ := hno c
  exact (hcover u' v' huv').elim
    (fun h => huc (Finset.card_le_one.mp hsmall u' h c hc))
    (fun h => hvc (Finset.card_le_one.mp hsmall v' h c hc))

lemma fixed_orientation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (A B C : Finset (Fin n))
    (hsound : ∀ u v, Hits A B C u v → G.Adj u v) (hno : NoCentre A B C)
    (hactive : ∃ u v, Hits A B C u v) (hbc : B ∩ C = ∅) :
    ∃ a b, a ≠ b ∧ A ∩ B = {a} ∧ A ∩ C = {b} ∧
      a ∈ A ∧ a ∈ B ∧ a ∉ C ∧ b ∈ A ∧ b ∈ C ∧ b ∉ B ∧
      (∀ u v, Hits A B C u v ↔
        (u = a ∧ v ∈ C) ∨ (v = a ∧ u ∈ C) ∨
        (u = b ∧ v ∈ B) ∨ (v = b ∧ u ∈ B)) ∧ 2 ≤ A.card := by
  classical
  obtain ⟨habsmall, hacsmall, _⟩ := overlaps_small G hfour A B C hsound hno
  have hlarge : 1 < ((A ∩ B) ∪ (A ∩ C)).card :=
    cover_large A B C _ hactive hno (cover_from_overlaps A B C hbc)
  have habne : (A ∩ B).Nonempty := by
    by_contra h
    have he : A ∩ B = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.empty_union] at hlarge
    omega
  have hacne : (A ∩ C).Nonempty := by
    by_contra h
    have he : A ∩ C = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.union_empty] at hlarge
    omega
  obtain ⟨a, ha⟩ := habne
  obtain ⟨b, hb⟩ := hacne
  obtain ⟨haa, hab⟩ := Finset.mem_inter.mp ha
  obtain ⟨hba, hbc'⟩ := Finset.mem_inter.mp hb
  have hac : a ∉ C := by
    intro h
    have hh : a ∈ B ∩ C := Finset.mem_inter.mpr ⟨hab, h⟩
    simp only [hbc, Finset.notMem_empty] at hh
  have hbb : b ∉ B := by
    intro h
    have hh : b ∈ B ∩ C := Finset.mem_inter.mpr ⟨h, hbc'⟩
    simp only [hbc, Finset.notMem_empty] at hh
  have hne : a ≠ b := by
    intro h
    exact hbb (h ▸ hab)
  have habset : A ∩ B = {a} := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_singleton.mpr (Finset.card_le_one.mp habsmall x hx a ha)
    · intro hx
      simpa only [Finset.mem_singleton.mp hx] using ha
  have hacset : A ∩ C = {b} := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hacsmall x hx b hb)
    · intro hx
      simpa only [Finset.mem_singleton.mp hx] using hb
  refine ⟨a, b, hne, habset, hacset, haa, hab, hac, hba, hbc', hbb, ?_, ?_⟩
  · intro u v
    constructor
    · intro h
      have hcover := cover_from_overlaps A B C hbc u v h
      simp only [habset, hacset, Finset.mem_union, Finset.mem_singleton] at hcover
      rcases hcover with (rfl | rfl) | (rfl | rfl)
      · exact Or.inl ⟨rfl, h.2.2.resolve_left hac⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, h.2.1.resolve_left hbb⟩))
      · exact Or.inr (Or.inl ⟨rfl, h.2.2.resolve_right hac⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h.2.1.resolve_right hbb⟩))
    · rintro (⟨rfl, hv⟩ | ⟨rfl, hu⟩ | ⟨rfl, hv⟩ | ⟨rfl, hu⟩)
      · exact ⟨Or.inl haa, Or.inl hab, Or.inr hv⟩
      · exact ⟨Or.inr haa, Or.inr hab, Or.inl hu⟩
      · exact ⟨Or.inl hba, Or.inr hv, Or.inl hbc'⟩
      · exact ⟨Or.inr hba, Or.inl hu, Or.inr hbc'⟩
  · have hpair : ({a, b} : Finset (Fin n)) ⊆ A := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      exact hx.elim (fun h => h ▸ haa) (fun h => h ▸ hba)
    have hcard := Finset.card_le_card hpair
    simpa only [Finset.card_pair hne] using hcard

lemma cross_hits {n : ℕ} (A B C : Finset (Fin n)) (a b : Fin n)
    (hab : A ∩ B = {a}) (hac : A ∩ C = {b}) (u v : Fin n)
    (hu : u ∈ B) (hv : v ∈ C) : Hits A B C u v ↔ u = a ∨ v = b := by
  have ha : a ∈ A := (Finset.mem_inter.mp (hab.symm ▸ Finset.mem_singleton_self a)).1
  have hb : b ∈ A := (Finset.mem_inter.mp (hac.symm ▸ Finset.mem_singleton_self b)).1
  constructor
  · intro h
    rcases h.1 with h | h
    · have hh : u ∈ A ∩ B := Finset.mem_inter.mpr ⟨h, hu⟩
      simpa only [hab, Finset.mem_singleton] using Or.inl hh
    · have hh : v ∈ A ∩ C := Finset.mem_inter.mpr ⟨h, hv⟩
      simpa only [hac, Finset.mem_singleton] using Or.inr hh
  · rintro (rfl | rfl)
    · exact ⟨Or.inl ha, Or.inl hu, Or.inr hv⟩
    · exact ⟨Or.inr hb, Or.inl hu, Or.inr hv⟩

lemma double_star_card {n : ℕ} (A B C : Finset (Fin n)) (a b : Fin n)
    (hab : A ∩ B = {a}) (hac : A ∩ C = {b}) :
    ((B ×ˢ C).filter (fun e : Fin n × Fin n => e.1 ∈ A ∨ e.2 ∈ A)).card + 1 = B.card + C.card := by
  classical
  have ha : a ∈ B := (Finset.mem_inter.mp (hab.symm ▸ Finset.mem_singleton_self a)).2
  have hb : b ∈ C := (Finset.mem_inter.mp (hac.symm ▸ Finset.mem_singleton_self b)).2
  have heq : (B ×ˢ C).filter (fun e : Fin n × Fin n => e.1 ∈ A ∨ e.2 ∈ A) =
      ({a} ×ˢ C) ∪ (B ×ˢ {b}) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, hh⟩
      rcases (cross_hits A B C a b hab hac e.1 e.2 h1 h2).mp
        ⟨hh, Or.inl h1, Or.inr h2⟩ with h | h
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨h1, h⟩
    · rintro (⟨h, h2⟩ | ⟨h1, h⟩)
      · have h1 : e.1 ∈ B := h ▸ ha
        exact ⟨⟨h1, h2⟩, ((cross_hits A B C a b hab hac e.1 e.2 h1 h2).mpr (Or.inl h)).1⟩
      · have h2 : e.2 ∈ C := h ▸ hb
        exact ⟨⟨h1, h2⟩, ((cross_hits A B C a b hab hac e.1 e.2 h1 h2).mpr (Or.inr h)).1⟩
  have hi : (({a} ×ˢ C) ∩ (B ×ˢ {b}) : Finset (Fin n × Fin n)) = {(a, b)} := by
    ext e
    rcases e with ⟨u, v⟩
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · exact fun h => ⟨h.1.1, h.2.2⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨rfl, hb⟩, ⟨ha, rfl⟩⟩
  have hh := Finset.card_union_add_card_inter ({a} ×ˢ C) (B ×ˢ {b})
  rw [hi] at hh
  simp only [Finset.card_singleton, Finset.card_product, one_mul, mul_one] at hh
  rw [heq]
  omega

lemma strict_occurrence_budget {n : ℕ} (A B C : Finset (Fin n)) (a b : Fin n)
    (hab : A ∩ B = {a}) (hac : A ∩ C = {b}) (hlarge : 2 ≤ A.card) :
    ((B ×ˢ C).filter (fun e : Fin n × Fin n => e.1 ∈ A ∨ e.2 ∈ A)).card + 3 ≤ A.card + B.card + C.card := by
  classical
  have h := double_star_card A B C a b hab hac
  omega

lemma shared_almost_neighborhood_small {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hfour : PEqualNP.TopForm.NoFourCycle G)
    (a b x y : Fin n) (hab : a ≠ b) (S : Finset (Fin n))
    (ha : ∀ u ∈ S, u = x ∨ G.Adj a u) (hb : ∀ u ∈ S, u = y ∨ G.Adj b u) :
    S.card ≤ 3 := by
  have hs : S ⊆ Finset.univ.filter (fun u => G.Adj a u ∧ G.Adj b u) ∪ {x, y} := by
    intro u hu
    by_cases hx : u = x
    · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl hx))
    by_cases hy : u = y
    · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hy)))
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (ha u hu).resolve_left hx, (hb u hu).resolve_left hy⟩)
  have hc := Finset.card_le_card hs
  have hh := Finset.card_union_le
    (Finset.univ.filter (fun u => G.Adj a u ∧ G.Adj b u)) ({x, y} : Finset (Fin n))
  have hp := Finset.card_insert_le x ({y} : Finset (Fin n))
  simp only [Finset.card_singleton] at hp
  have hcommon := hfour a b hab
  omega

end ThreeClause

namespace SharedThreeClauseLedger

lemma edge_multiplicity {n m : ℕ} (E EL ER : Finset (Fin n × Fin m))
    (hcover : EL ∪ ER = E) : EL.card + ER.card = E.card + (EL ∩ ER).card := by
  have h := Finset.card_union_add_card_inter EL ER
  rw [hcover] at h
  exact h.symm

lemma central_edges_double_counted {n m : ℕ} (EL ER F : Finset (Fin n × Fin m))
    (hfl : F ⊆ EL) (hfr : F ⊆ ER) : F.card ≤ (EL ∩ ER).card := by
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_inter.mpr ⟨hfl he, hfr he⟩

lemma centre_budget {n m : ℕ} (EL ER F : Finset (Fin n × Fin m))
    (L ZL : Finset (Fin n)) (R ZR : Finset (Fin m)) (r t : ℕ)
    (hfl : F ⊆ EL) (hfr : F ⊆ ER)
    (hlcover : L ⊆ F.image Prod.fst ∪ ZL) (hrcover : R ⊆ F.image Prod.snd ∪ ZR)
    (hr : F.card ≤ r) (ht : ZL.card + ZR.card ≤ t) :
    L.card + R.card ≤ (EL ∩ ER).card + r + t := by
  have hd := central_edges_double_counted EL ER F hfl hfr
  have hl := Finset.card_le_card hlcover
  have hh := Finset.card_union_le (F.image Prod.fst) ZL
  have hi : (F.image Prod.fst).card ≤ F.card := Finset.card_image_le
  have hrr := Finset.card_le_card hrcover
  have hhh := Finset.card_union_le (F.image Prod.snd) ZR
  have hii : (F.image Prod.snd).card ≤ F.card := Finset.card_image_le
  omega

lemma shared_or_ledger {n m : ℕ} (E EL ER F : Finset (Fin n × Fin m))
    (L ZL : Finset (Fin n)) (R ZR : Finset (Fin m)) (r t pureOr size : ℕ)
    (hcover : EL ∪ ER = E) (hfl : F ⊆ EL) (hfr : F ⊆ ER)
    (hlcover : L ⊆ F.image Prod.fst ∪ ZL) (hrcover : R ⊆ F.image Prod.snd ∪ ZR)
    (hr : F.card ≤ r) (ht : ZL.card + ZR.card ≤ t)
    (hpure : EL.card + ER.card ≤ pureOr + 2 * r + t)
    (hsize : pureOr + 3 * r + 2 * t ≤ size + 1) :
    E.card + L.card + R.card ≤ size + 1 := by
  have hm := edge_multiplicity E EL ER hcover
  have hc := centre_budget EL ER F L ZL R ZR r t hfl hfr hlcover hrcover hr ht
  omega

end SharedThreeClauseLedger

namespace MultiRoot

lemma support_family_bound {α : Type} [DecidableEq α]
    (n m : ℕ) (s : ℕ → Finset α) (a : ℕ → Finset ℕ) (cost : ℕ → ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (hback : ∀ k < m, a k ⊆ Finset.range (n + k))
    (hcost : ∀ k < m, (a k).card ≤ cost k + 1)
    (hcover : ∀ k < m, s (n + k) ⊆ (a k).biUnion s) :
    ∀ t : Finset ℕ, t ⊆ Finset.range (n + m) →
      (t.biUnion s).card ≤ (Finset.range m).sum cost + t.card := by
  induction m with
  | zero =>
    intro t ht
    have h1 := Finset.card_biUnion_le (s := t) (t := s)
    have h2 : ∑ i ∈ t, (s i).card ≤ t.card := by
      calc
        ∑ i ∈ t, (s i).card ≤ ∑ i ∈ t, 1 := Finset.sum_le_sum fun i hi =>
          hinput i (by have := ht hi; simpa using this)
        _ = t.card := by simp
    simpa using h1.trans h2
  | succ m ih =>
    intro t ht
    have hb : ∀ k < m, a k ⊆ Finset.range (n + k) := fun k hk => hback k (by omega)
    have hc : ∀ k < m, (a k).card ≤ cost k + 1 := fun k hk => hcost k (by omega)
    have hv : ∀ k < m, s (n + k) ⊆ (a k).biUnion s := fun k hk => hcover k (by omega)
    by_cases hm : n + m ∈ t
    · let u := t.erase (n + m) ∪ a m
      have hu : u ⊆ Finset.range (n + m) := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · obtain ⟨hne, hit⟩ := Finset.mem_erase.mp hi
          have hi' := Finset.mem_range.mp (ht hit)
          exact Finset.mem_range.mpr (by omega)
        · exact hback m (by omega) hi
      have hsub : t.biUnion s ⊆ u.biUnion s := by
        intro x hx
        obtain ⟨i, hit, hxi⟩ := Finset.mem_biUnion.mp hx
        by_cases him : i = n + m
        · subst i
          obtain ⟨j, hja, hxj⟩ := Finset.mem_biUnion.mp (hcover m (by omega) hxi)
          exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_union_right _ hja, hxj⟩
        · exact Finset.mem_biUnion.mpr ⟨i,
            Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨him, hit⟩), hxi⟩
      have huc : u.card ≤ t.card + cost m := by
        have h1 := Finset.card_union_le (t.erase (n + m)) (a m)
        have h2 := Finset.card_erase_add_one hm
        have h3 := hcost m (by omega)
        dsimp only [u]
        omega
      have hbound := ih hb hc hv u hu
      have hsmall := Finset.card_le_card hsub
      rw [Finset.sum_range_succ]
      change (t.biUnion s).card ≤ (Finset.range m).sum cost + cost m + t.card
      omega
    · have ht' : t ⊆ Finset.range (n + m) := by
        intro i hi
        have hi' := Finset.mem_range.mp (ht hi)
        have hne : i ≠ n + m := by intro h; subst i; exact hm hi
        exact Finset.mem_range.mpr (by omega)
      have hbound := ih hb hc hv t ht'
      rw [Finset.sum_range_succ]
      change (t.biUnion s).card ≤ (Finset.range m).sum cost + cost m + t.card
      omega


lemma small_union {α : Type} [DecidableEq α] (A B : Finset α)
    (h : (A ∪ B).card ≤ 1) : A ∪ B = A ∨ A ∪ B = B := by
  by_cases ha : A = ∅
  · exact Or.inr (by simp [ha])
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr ha
  apply Or.inl
  apply Finset.union_eq_left.mpr
  intro b hb
  have hba := Finset.card_le_one.mp h b (Finset.mem_union_right _ hb)
    a (Finset.mem_union_left _ ha)
  simpa [hba] using ha

lemma neighborhood_budget {α : Type} [DecidableEq α]
    (n m : ℕ) (s : ℕ → Finset α) (a b : ℕ → ℕ) (N : Finset α)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (hstep : ∀ k < m, s (n + k) = s (a k) ∪ s (b k) ∨ s (n + k) = ∅)
    (T : Finset ℕ) (hT : T ⊆ Finset.range (n + m))
    (hTN : ∀ w ∈ T, s w ⊆ N) :
    (T.biUnion s).card ≤
      ((Finset.range m).filter fun k => s (n + k) ⊆ N ∧ 2 ≤ (s (n + k)).card).card +
        T.card := by
  classical
  let ss : ℕ → Finset α := fun w => if s w ⊆ N then s w else ∅
  let cost : ℕ → ℕ := fun k => if s (n + k) ⊆ N ∧ 2 ≤ (s (n + k)).card then 1 else 0
  have hparents : ∀ k < m, ∃ P : Finset ℕ,
      P ⊆ Finset.range (n + k) ∧ P.card ≤ cost k + 1 ∧
        ss (n + k) ⊆ P.biUnion ss := by
    intro k hk
    by_cases he : ss (n + k) = ∅
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp [he]⟩
    have hn : s (n + k) ⊆ N := by
      by_contra h
      exact he (by simp [ss, h])
    have hs : ss (n + k) = s (n + k) := by simp [ss, hn]
    have hu : s (n + k) = s (a k) ∪ s (b k) := by
      rcases hstep k hk with hu | hz
      · exact hu
      · exact False.elim (he (hs.trans hz))
    have hsa : ss (a k) = s (a k) := by
      apply ite_eq_left
      exact Finset.Subset.trans Finset.subset_union_left (hu ▸ hn)
    have hsb : ss (b k) = s (b k) := by
      apply ite_eq_left
      exact Finset.Subset.trans Finset.subset_union_right (hu ▸ hn)
    by_cases hcard : (s (n + k)).card ≤ 1
    · have hsmall : (s (a k) ∪ s (b k)).card ≤ 1 := hu ▸ hcard
      rcases small_union (s (a k)) (s (b k)) hsmall with hleft | hright
      · refine ⟨{a k}, ?_, by simp, ?_⟩
        · simpa using ha k hk
        · simp only [Finset.singleton_biUnion, hs, hsa]
          exact Finset.subset_of_eq (hu.trans hleft)
      · refine ⟨{b k}, ?_, by simp, ?_⟩
        · simpa using hb k hk
        · simp only [Finset.singleton_biUnion, hs, hsb]
          exact Finset.subset_of_eq (hu.trans hright)
    · have htwo : 2 ≤ (s (n + k)).card := by omega
      refine ⟨{a k, b k}, ?_, ?_, ?_⟩
      · intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_range.mpr (ha k hk)
        · exact Finset.mem_range.mpr (hb k hk)
      · simpa [cost, hn, htwo] using (Finset.card_le_two : ({a k, b k} : Finset ℕ).card ≤ 2)
      · simpa only [Finset.biUnion_insert, Finset.singleton_biUnion, hs, hsa, hsb, hu]
          using (Finset.Subset.refl (s (a k) ∪ s (b k)))
  let parents : ℕ → Finset ℕ := fun k => if hk : k < m then (hparents k hk).choose else ∅
  have hp : ∀ k < m, parents k ⊆ Finset.range (n + k) := by
    intro k hk
    simpa [parents, hk] using (hparents k hk).choose_spec.1
  have hc : ∀ k < m, (parents k).card ≤ cost k + 1 := by
    intro k hk
    simpa [parents, hk] using (hparents k hk).choose_spec.2.1
  have hv : ∀ k < m, ss (n + k) ⊆ (parents k).biUnion ss := by
    intro k hk
    simpa [parents, hk] using (hparents k hk).choose_spec.2.2
  have hi : ∀ i < n, (ss i).card ≤ 1 := by
    intro i hin
    dsimp [ss]
    split_ifs
    · exact hinput i hin
    · simp
  have hbound := support_family_bound n m ss parents cost hi hp hc hv T hT
  have hsame : T.biUnion ss = T.biUnion s := by
    apply Finset.biUnion_congr rfl
    intro w hw
    exact ite_eq_left (hTN w hw)
  rw [hsame] at hbound
  have hsum : (Finset.range m).sum cost =
      ((Finset.range m).filter fun k => s (n + k) ⊆ N ∧ 2 ≤ (s (n + k)).card).card := by
    simp only [cost, Finset.sum_boole]
    rfl
  rw [hsum] at hbound
  exact hbound

lemma disjoint_neighborhoods_budget {α β : Type} [DecidableEq α] [DecidableEq β]
    (n m : ℕ) (s : ℕ → Finset α) (a b : ℕ → ℕ)
    (K : Finset β) (N : β → Finset α) (T : β → Finset ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (hstep : ∀ k < m, s (n + k) = s (a k) ∪ s (b k) ∨ s (n + k) = ∅)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + m))
    (hTN : ∀ c ∈ K, ∀ w ∈ T c, s w ⊆ N c)
    (hlinear : ∀ c ∈ K, ∀ d ∈ K, c ≠ d → (N c ∩ N d).card ≤ 1) :
    (∑ c ∈ K, ((T c).biUnion s).card) ≤
      ((Finset.range m).filter fun k => 2 ≤ (s (n + k)).card).card +
        ∑ c ∈ K, (T c).card := by
  classical
  let pool : β → Finset ℕ := fun c =>
    (Finset.range m).filter fun k => s (n + k) ⊆ N c ∧ 2 ≤ (s (n + k)).card
  have hdisjoint : (K : Set β).PairwiseDisjoint pool := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro k hkc hkd
    obtain ⟨_, hcn, htwo⟩ := Finset.mem_filter.mp hkc
    obtain ⟨_, hdn, _⟩ := Finset.mem_filter.mp hkd
    have hs : s (n + k) ⊆ N c ∩ N d := fun x hx =>
      Finset.mem_inter.mpr ⟨hcn hx, hdn hx⟩
    have hbnd := Finset.card_le_card hs
    have hsmall := hlinear c hc d hd hcd
    omega
  have hpool : (∑ c ∈ K, (pool c).card) ≤
      ((Finset.range m).filter fun k => 2 ≤ (s (n + k)).card).card := by
    rw [← Finset.card_biUnion hdisjoint]
    apply Finset.card_le_card
    intro k hk
    obtain ⟨c, _, hkc⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨hkm, _, htwo⟩ := Finset.mem_filter.mp hkc
    exact Finset.mem_filter.mpr ⟨hkm, htwo⟩
  have hsum : (∑ c ∈ K, ((T c).biUnion s).card) ≤
      ∑ c ∈ K, ((pool c).card + (T c).card) := by
    apply Finset.sum_le_sum
    intro c hc
    exact neighborhood_budget n m s a b (N c) hinput ha hb hstep (T c) (hT c hc) (hTN c hc)
  rw [Finset.sum_add_distrib] at hsum
  exact hsum.trans (Nat.add_le_add_right hpool _)

lemma pooled_neighborhood_budget {α β : Type} [DecidableEq α] [DecidableEq β]
    (n m : ℕ) (s : ℕ → Finset α) (a b : ℕ → ℕ)
    (K : Finset β) (N : β → Finset α) (T : β → Finset ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (hstep : ∀ k < m, s (n + k) = s (a k) ∪ s (b k) ∨ s (n + k) = ∅)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + m))
    (hTN : ∀ c ∈ K, ∀ w ∈ T c, s w ⊆ N c)
    (hlinear : ∀ c ∈ K, ∀ d ∈ K, c ≠ d → (N c ∩ N d).card ≤ 1) :
    (∑ c ∈ K, ((T c).biUnion s).card) ≤
      (K.biUnion fun c => (Finset.range m).filter fun k =>
        s (n + k) ⊆ N c ∧ 2 ≤ (s (n + k)).card).card +
        ∑ c ∈ K, (T c).card := by
  classical
  let pool : β → Finset ℕ := fun c =>
    (Finset.range m).filter fun k => s (n + k) ⊆ N c ∧ 2 ≤ (s (n + k)).card
  have hdisjoint : (K : Set β).PairwiseDisjoint pool := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro k hkc hkd
    obtain ⟨_, hcn, htwo⟩ := Finset.mem_filter.mp hkc
    obtain ⟨_, hdn, _⟩ := Finset.mem_filter.mp hkd
    have hs : s (n + k) ⊆ N c ∩ N d := fun x hx =>
      Finset.mem_inter.mpr ⟨hcn hx, hdn hx⟩
    have hbnd := Finset.card_le_card hs
    have hsmall := hlinear c hc d hd hcd
    omega
  have hsum : (∑ c ∈ K, ((T c).biUnion s).card) ≤
      ∑ c ∈ K, ((pool c).card + (T c).card) := by
    apply Finset.sum_le_sum
    intro c hc
    exact neighborhood_budget n m s a b (N c) hinput ha hb hstep (T c) (hT c hc) (hTN c hc)
  rw [Finset.sum_add_distrib, ← Finset.card_biUnion hdisjoint] at hsum
  exact hsum

end MultiRoot



namespace RawOrSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge


lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj


def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

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

lemma orIn_iff_reach {n : ℕ} {C : Circuit} (p : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C p ↔ Relation.ReflTransGen (OrStep n C) p u.val :=
  ⟨mem_orIn_reach u, reach_mem_orIn u⟩

lemma orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [orIn_iff_reach] at ha hb
  have h1 : ∀ c : Fin n, Relation.ReflTransGen (OrStep n C) w c.val → c.val = w := by
    intro c hc
    rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
    · exact h.symm
    · obtain ⟨k, _, h3, _⟩ := hd
      omega
  exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)

lemma orIn_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧
        u ∈ PEqualNP.TopForm.orIn n C w := by
  rw [orIn_iff_reach]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
    · have := u.isLt
      omega
    · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
      have hkk : k' = k := by omega
      subst hkk
      exact ⟨hk', hop, d, hin, hlt, (orIn_iff_reach d u).2 hr⟩
  · rintro ⟨hk, hop, w, hw, hlt, hu⟩
    exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((orIn_iff_reach w u).1 hu)

lemma opnd_lt {n : ℕ} {C : Circuit} (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hRB : ReadsBack n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    PEqualNP.TopForm.opnd C a b < n + a := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem ha))
  have hp : p < n + a := hRB a ha p (by rw [hin]; simp)
  have hq : q < n + a := hRB a ha q (by rw [hin]; simp)
  fin_cases b
  · simpa [PEqualNP.TopForm.opnd, hin] using hp
  · simpa [PEqualNP.TopForm.opnd, hin] using hq

lemma orIn_binary {n : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 n C)
    (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.TopForm.orIn n C (n + k) =
        PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 0) ∪
          PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 1) ∨
      PEqualNP.TopForm.orIn n C (n + k) = ∅ := by
  classical
  by_cases hop : (gateAt C k).op = GateOp.or
  · left
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hk))
    have hp : p < n + k := hAO.2.1 k hk p (by rw [hin]; simp)
    have hq : q < n + k := hAO.2.1 k hk q (by rw [hin]; simp)
    have e0 : PEqualNP.TopForm.opnd C k 0 = p := by simp [PEqualNP.TopForm.opnd, hin]
    have e1 : PEqualNP.TopForm.opnd C k 1 = q := by simp [PEqualNP.TopForm.opnd, hin]
    rw [e0, e1]
    ext u
    rw [Finset.mem_union, orIn_gate]
    simp only [hk, hop, true_and, hin, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨w, (rfl | rfl), _, hu⟩
      · exact Or.inl hu
      · exact Or.inr hu
    · rintro (hu | hu)
      · exact ⟨p, Or.inl rfl, hp, hu⟩
      · exact ⟨q, Or.inr rfl, hq, hu⟩
  · right
    ext u
    simp only [Finset.notMem_empty, iff_false]
    intro hu
    exact hop ((orIn_gate C k u).mp hu).2.1

lemma support_nontrivial_or {n : ℕ} (C : Circuit) (k : ℕ)
    (hcard : 2 ≤ (PEqualNP.TopForm.orIn n C (n + k)).card) :
    (gateAt C k).op = GateOp.or := by
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (PEqualNP.TopForm.orIn n C (n + k)).card by omega)
  exact ((orIn_gate C k u).mp hu).2.1

noncomputable def orGates (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k => (gateAt C k).op = GateOp.or

lemma nontrivial_count_le_or {n : ℕ} (C : Circuit) :
    ((Finset.range C.gates.length).filter fun k =>
      2 ≤ (PEqualNP.TopForm.orIn n C (n + k)).card).card ≤ (orGates C).card := by
  classical
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hkr, hcard⟩ := Finset.mem_filter.mp hk
  exact Finset.mem_filter.mpr ⟨hkr, support_nontrivial_or C k hcard⟩

end RawOrSupport

namespace RawOrSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma circuit_multioutput_or_budget {n : ℕ} (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    {β : Type} [DecidableEq β] (K : Finset β) (N : β → Finset (Fin n)) (T : β → Finset ℕ)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + C.size))
    (hTN : ∀ c ∈ K, ∀ w ∈ T c, PEqualNP.TopForm.orIn n C w ⊆ N c)
    (hlinear : ∀ c ∈ K, ∀ d ∈ K, c ≠ d → (N c ∩ N d).card ≤ 1) :
    (∑ c ∈ K, ((T c).biUnion (PEqualNP.TopForm.orIn n C)).card) ≤
      (orGates C).card + ∑ c ∈ K, (T c).card := by
  have h := MultiRoot.disjoint_neighborhoods_budget n C.gates.length
    (PEqualNP.TopForm.orIn n C) (fun k => PEqualNP.TopForm.opnd C k 0)
    (fun k => PEqualNP.TopForm.opnd C k 1) K N T
    (orIn_input C) (fun k hk => opnd_lt hAO.2.2 hAO.2.1 hk 0)
    (fun k hk => opnd_lt hAO.2.2 hAO.2.1 hk 1) (orIn_binary hAO) hT hTN hlinear
  exact h.trans (Nat.add_le_add_right (nontrivial_count_le_or C) _)

lemma graph_multioutput_or_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (K : Finset (Fin n)) (T : Fin n → Finset ℕ)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + C.size))
    (hTN : ∀ c ∈ K, ∀ w ∈ T c, ∀ u ∈ PEqualNP.TopForm.orIn n C w, G.Adj c u) :
    (∑ c ∈ K, ((T c).biUnion (PEqualNP.TopForm.orIn n C)).card) ≤
      (orGates C).card + ∑ c ∈ K, (T c).card := by
  apply circuit_multioutput_or_budget C hAO K
    (fun c => Finset.univ.filter fun u => G.Adj c u) T hT
  · intro c hc w hw u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTN c hc w hw u hu⟩
  · intro c hc d hd hcd
    have heq : (Finset.univ.filter fun u => G.Adj c u) ∩
        (Finset.univ.filter fun u => G.Adj d u) =
          Finset.univ.filter (fun u => G.Adj c u ∧ G.Adj d u) := by
      ext u
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq]
    exact hfour c d hcd

lemma circuit_pooled_or_budget {n : ℕ} (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    {β : Type} [DecidableEq β] (K : Finset β) (N : β → Finset (Fin n)) (T : β → Finset ℕ)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + C.size))
    (hTN : ∀ c ∈ K, ∀ w ∈ T c, PEqualNP.TopForm.orIn n C w ⊆ N c)
    (hlinear : ∀ c ∈ K, ∀ d ∈ K, c ≠ d → (N c ∩ N d).card ≤ 1) :
    (∑ c ∈ K, ((T c).biUnion (PEqualNP.TopForm.orIn n C)).card) ≤
      (K.biUnion fun c => (Finset.range C.gates.length).filter fun k =>
        PEqualNP.TopForm.orIn n C (n + k) ⊆ N c ∧
          2 ≤ (PEqualNP.TopForm.orIn n C (n + k)).card).card + ∑ c ∈ K, (T c).card := by
  exact MultiRoot.pooled_neighborhood_budget n C.gates.length
    (PEqualNP.TopForm.orIn n C) (fun k => PEqualNP.TopForm.opnd C k 0)
    (fun k => PEqualNP.TopForm.opnd C k 1) K N T
    (orIn_input C) (fun k hk => opnd_lt hAO.2.2 hAO.2.1 hk 0)
    (fun k hk => opnd_lt hAO.2.2 hAO.2.1 hk 1) (orIn_binary hAO) hT hTN hlinear

lemma graph_pooled_or_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (K : Finset (Fin n)) (T : Fin n → Finset ℕ)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + C.size))
    (hTN : ∀ c ∈ K, ∀ w ∈ T c, ∀ u ∈ PEqualNP.TopForm.orIn n C w, G.Adj c u) :
    (∑ c ∈ K, ((T c).biUnion (PEqualNP.TopForm.orIn n C)).card) ≤
      (K.biUnion fun c => (Finset.range C.gates.length).filter fun k =>
        PEqualNP.TopForm.orIn n C (n + k) ⊆ (Finset.univ.filter fun u => G.Adj c u) ∧
          2 ≤ (PEqualNP.TopForm.orIn n C (n + k)).card).card + ∑ c ∈ K, (T c).card := by
  apply circuit_pooled_or_budget C hAO K
    (fun c => Finset.univ.filter fun u => G.Adj c u) T hT
  · intro c hc w hw u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTN c hc w hw u hu⟩
  · intro c hc d hd hcd
    have heq : (Finset.univ.filter fun u => G.Adj c u) ∩
        (Finset.univ.filter fun u => G.Adj d u) =
          Finset.univ.filter (fun u => G.Adj c u ∧ G.Adj d u) := by
      ext u
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq]
    exact hfour c d hcd

end RawOrSupport

namespace PoolSurplus

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def neighborhoodPool {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (K : Finset (Fin n)) : Finset ℕ :=
  K.biUnion fun c => (Finset.range C.gates.length).filter fun k =>
    orIn n C (n + k) ⊆ (Finset.univ.filter fun u => G.Adj c u) ∧
      2 ≤ (orIn n C (n + k)).card

lemma mem_pool {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (K : Finset (Fin n)) {k : ℕ} (hk : k ∈ neighborhoodPool G C K) :
    k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      2 ≤ (orIn n C (n + k)).card := by
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨hkr, _, htwo⟩ := Finset.mem_filter.mp hc
  exact ⟨Finset.mem_range.mp hkr, RawOrSupport.support_nontrivial_or C k htwo, htwo⟩

lemma adjacent_support_outside_pool {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ u v w, ¬ (G.Adj u v ∧ G.Adj v w ∧ G.Adj w u))
    (C : Circuit) (K : Finset (Fin n)) (j : ℕ) (u v : Fin n)
    (huv : G.Adj u v) (hu : u ∈ orIn n C (n + j)) (hv : v ∈ orIn n C (n + j)) :
    j ∉ neighborhoodPool G C K := by
  intro hj
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hj
  have hs := (Finset.mem_filter.mp hc).2.1
  have hcu := (Finset.mem_filter.mp (hs hu)).2
  have hcv := (Finset.mem_filter.mp (hs hv)).2
  exact htri c u v ⟨hcu, huv, hcv.symm⟩

lemma extra_gate_accounting {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ u v w, ¬ (G.Adj u v ∧ G.Adj v w ∧ G.Adj w u))
    (C : Circuit) (K : Finset (Fin n)) (M O : Finset ℕ)
    (hM : ∀ k ∈ M, k < C.gates.length ∧ (gateAt C k).op = GateOp.and)
    (hO : ∀ k ∈ O, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      orIn n C (n + k) = ∅)
    (j : ℕ) (u v : Fin n) (huv : G.Adj u v)
    (hu : u ∈ orIn n C (n + j)) (hv : v ∈ orIn n C (n + j)) :
    (neighborhoodPool G C K).card + M.card + O.card + 1 ≤ C.size := by
  classical
  let R := neighborhoodPool G C K
  have hjfacts := (RawOrSupport.orIn_gate C j u).mp hu
  have hRM : Disjoint R M := by
    apply Finset.disjoint_left.mpr
    intro k hk hm
    have ho := (mem_pool G C K hk).2.1
    have ha := (hM k hm).2
    rw [ha] at ho
    cases ho
  have hRO : Disjoint R O := by
    apply Finset.disjoint_left.mpr
    intro k hk ho
    have htwo := (mem_pool G C K hk).2.2
    rw [(hO k ho).2.2] at htwo
    simp at htwo
  have hMO : Disjoint M O := by
    apply Finset.disjoint_left.mpr
    intro k hm ho
    have ha := (hM k hm).2
    have hb := (hO k ho).2.1
    rw [ha] at hb
    cases hb
  have hjR : j ∉ R := adjacent_support_outside_pool G htri C K j u v huv hu hv
  have hjM : j ∉ M := by
    intro hm
    have ho := hjfacts.2.1
    rw [(hM j hm).2] at ho
    cases ho
  have hjO : j ∉ O := by
    intro ho
    rw [(hO j ho).2.2] at hu
    exact Finset.notMem_empty _ hu
  have hj : j ∉ R ∪ M ∪ O := by simp only [Finset.mem_union, not_or]; exact ⟨⟨hjR, hjM⟩, hjO⟩
  have hRM_O : Disjoint (R ∪ M) O := Finset.disjoint_union_left.mpr ⟨hRO, hMO⟩
  have hsub : insert j (R ∪ M ∪ O) ⊆ Finset.range C.gates.length := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact Finset.mem_range.mpr hjfacts.1
    rcases Finset.mem_union.mp hk with hk | hk
    · rcases Finset.mem_union.mp hk with hk | hk
      · exact Finset.mem_range.mpr (mem_pool G C K hk).1
      · exact Finset.mem_range.mpr (hM k hk).1
    · exact Finset.mem_range.mpr (hO k hk).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hj, Finset.card_union_of_disjoint hRM_O,
    Finset.card_union_of_disjoint hRM, Finset.card_range] at hcard
  exact hcard

lemma strict_multioutput_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G)
    (htri : ∀ u v w, ¬ (G.Adj u v ∧ G.Adj v w ∧ G.Adj w u))
    (C : Circuit) (hAO : IsAO2 n C) (K : Finset (Fin n)) (T : Fin n → Finset ℕ)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + C.size))
    (hTN : ∀ c ∈ K, ∀ w ∈ T c, ∀ u ∈ orIn n C w, G.Adj c u)
    (M O : Finset ℕ)
    (hM : ∀ k ∈ M, k < C.gates.length ∧ (gateAt C k).op = GateOp.and)
    (hO : ∀ k ∈ O, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      orIn n C (n + k) = ∅)
    (j : ℕ) (u v : Fin n) (huv : G.Adj u v)
    (hu : u ∈ orIn n C (n + j)) (hv : v ∈ orIn n C (n + j)) :
    (∑ c ∈ K, ((T c).biUnion (orIn n C)).card) + M.card + O.card + 1 ≤
      C.size + ∑ c ∈ K, (T c).card := by
  have hb := RawOrSupport.graph_pooled_or_budget G hfour C hAO K T hT hTN
  have hc := extra_gate_accounting G htri C K M O hM hO j u v huv hu hv
  change _ ≤ (neighborhoodPool G C K).card + _ at hb
  omega

lemma shared_family_cover_bound {n p l : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G)
    (htri : ∀ u v w, ¬ (G.Adj u v ∧ G.Adj v w ∧ G.Adj w u))
    (C : Circuit) (hAO : IsAO2 n C) (K : Finset (Fin n)) (T : Fin n → Finset ℕ)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + C.size))
    (hTN : ∀ c ∈ K, ∀ w ∈ T c, ∀ u ∈ orIn n C w, G.Adj c u)
    (M O : Finset ℕ)
    (hM : ∀ k ∈ M, k < C.gates.length ∧ (gateAt C k).op = GateOp.and)
    (hO : ∀ k ∈ O, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      orIn n C (n + k) = ∅)
    (j : ℕ) (u v : Fin n) (huv : G.Adj u v)
    (hu : u ∈ orIn n C (n + j)) (hv : v ∈ orIn n C (n + j))
    (E EL ER F : Finset (Fin p × Fin l)) (L ZL : Finset (Fin p)) (R ZR : Finset (Fin l))
    (r t : ℕ) (hcover : EL ∪ ER = E) (hfl : F ⊆ EL) (hfr : F ⊆ ER)
    (hlcover : L ⊆ F.image Prod.fst ∪ ZL) (hrcover : R ⊆ F.image Prod.snd ∪ ZR)
    (hr : F.card ≤ r) (ht : ZL.card + ZR.card ≤ t)
    (hleft : ∀ e ∈ EL, e.1 ∈ L) (hright : ∀ e ∈ ER, e.2 ∈ R)
    (hleaves : EL.card + ER.card ≤ ∑ c ∈ K, ((T c).biUnion (orIn n C)).card)
    (hroots : (∑ c ∈ K, (T c).card) ≤ 2 * r + t)
    (hands : 2 * r + t ≤ M.card) (haggregation : r + t ≤ O.card + 1) :
    (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card ≤ C.size := by
  constructor
  · intro e he
    have he' : e ∈ EL ∪ ER := hcover.symm ▸ he
    exact (Finset.mem_union.mp he').elim (fun h => Or.inl (hleft e h))
      (fun h => Or.inr (hright e h))
  · have hb := strict_multioutput_budget G hfour htri C hAO K T hT hTN M O hM hO
      j u v huv hu hv
    have hm := SharedThreeClauseLedger.edge_multiplicity E EL ER hcover
    have hc := SharedThreeClauseLedger.centre_budget EL ER F L ZL R ZR r t
      hfl hfr hlcover hrcover hr ht
    omega

end PoolSurplus



namespace StarThreeClause

open PEqualNP.MetaComplexity.NestedCover

def clause {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ u ∈ S, x u = true)

def starCNF {n : ℕ} (a : Fin n) (B C : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  x a && (clause B x && clause C x)

lemma triple_safety {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) (B C : Finset (Fin n))
    (hsafe : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true)
    (b c : Fin n) (hb : b ∈ B) (hc : c ∈ C) :
    G.Adj a b ∨ G.Adj a c ∨ G.Adj b c := by
  let x : Fin n → Bool := fun u => decide (u = a ∨ u = b ∨ u = c)
  have ha : x a = true := by simp [x]
  have hbx : x b = true := by simp [x]
  have hcx : x c = true := by simp [x]
  have hB : clause B x = true := by
    apply decide_eq_true
    exact ⟨b, hb, hbx⟩
  have hC : clause C x = true := by
    apply decide_eq_true
    exact ⟨c, hc, hcx⟩
  have hfun := hsafe x (by simp only [starCNF, ha, hB, hC, Bool.and_self])
  have hedge : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simpa [graphFun] using hfun
  obtain ⟨u, v, huv, hu, hv⟩ := hedge
  have hu' : u = a ∨ u = b ∨ u = c := of_decide_eq_true hu
  have hv' : v = a ∨ v = b ∨ v = c := of_decide_eq_true hv
  rcases hu' with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl
  · exact False.elim ((G.ne_of_adj huv) rfl)
  · exact Or.inl huv
  · exact Or.inr (Or.inl huv)
  · exact Or.inl huv.symm
  · exact False.elim ((G.ne_of_adj huv) rfl)
  · exact Or.inr (Or.inr huv)
  · exact Or.inr (Or.inl huv.symm)
  · exact Or.inr (Or.inr huv.symm)
  · exact False.elim ((G.ne_of_adj huv) rfl)

lemma outside_rectangle {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) (B C : Finset (Fin n))
    (hsafe : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true) :
    ∀ b ∈ B, ∀ c ∈ C, ¬ G.Adj a b → ¬ G.Adj a c → G.Adj b c := by
  intro b hb c hc hab hac
  exact ((triple_safety G a B C hsafe b c hb hc).resolve_left hab).resolve_left hac

lemma outside_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (a : Fin n) (B C : Finset (Fin n))
    (hsafe : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true) :
    (B.filter (fun b => ¬ G.Adj a b)).card ≤ 1 ∨
      (C.filter (fun c => ¬ G.Adj a c)).card ≤ 1 := by
  by_cases hb : (B.filter (fun b => ¬ G.Adj a b)).card ≤ 1
  · exact Or.inl hb
  right
  have htwo : 1 < (B.filter (fun b => ¬ G.Adj a b)).card := by omega
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp htwo
  have hsub : C.filter (fun c => ¬ G.Adj a c) ⊆
      Finset.univ.filter (fun c => G.Adj b c ∧ G.Adj d c) := by
    intro c hc
    obtain ⟨hb, hab⟩ := Finset.mem_filter.mp hb
    obtain ⟨hd, had⟩ := Finset.mem_filter.mp hd
    obtain ⟨hc, hac⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      outside_rectangle G a B C hsafe b hb c hc hab hac,
      outside_rectangle G a B C hsafe d hd c hc had hac⟩
  exact (Finset.card_le_card hsub).trans (hfour b d hbd)

lemma chosen_leaf_projection {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (a : Fin n) (B C : Finset (Fin n))
    (hsafe : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true) :
    (∀ b ∈ B, side b ≠ side a → G.Adj a b) ∨
      (∀ c ∈ C, side c ≠ side a → G.Adj a c) := by
  classical
  by_cases hb : ∀ b ∈ B, side b ≠ side a → G.Adj a b
  · exact Or.inl hb
  push Not at hb
  obtain ⟨b, hb, hba, hab⟩ := hb
  right
  intro c hc hca
  by_contra hac
  have hbc := outside_rectangle G a B C hsafe b hb c hc hab hac
  have heq : side b = side c := by
    cases ha : side a <;> cases hb' : side b <;> cases hc' : side c <;> simp_all
  exact hproper b c hbc heq

lemma accepted_pair_iff {n : ℕ} (a u : Fin n) (B C : Finset (Fin n))
    (haB : a ∉ B) (haC : a ∉ C) :
    starCNF a B C (fun v => decide (v = a ∨ v = u)) = true ↔ u ∈ B ∩ C := by
  constructor
  · intro h
    have hBC : clause B (fun v => decide (v = a ∨ v = u)) = true ∧
        clause C (fun v => decide (v = a ∨ v = u)) = true := by
      simpa [starCNF] using h
    have hB := hBC.1
    have hC := hBC.2
    obtain ⟨b, hb, hbx⟩ := of_decide_eq_true hB
    obtain ⟨c, hc, hcx⟩ := of_decide_eq_true hC
    have hbu : b = u := (of_decide_eq_true hbx).resolve_left (fun h => haB (h ▸ hb))
    have hcu : c = u := (of_decide_eq_true hcx).resolve_left (fun h => haC (h ▸ hc))
    exact Finset.mem_inter.mpr ⟨hbu ▸ hb, hcu ▸ hc⟩
  · intro h
    obtain ⟨huB, huC⟩ := Finset.mem_inter.mp h
    have hB : clause B (fun v => decide (v = a ∨ v = u)) = true := by
      apply decide_eq_true
      exact ⟨u, huB, by simp⟩
    have hC : clause C (fun v => decide (v = a ∨ v = u)) = true := by
      apply decide_eq_true
      exact ⟨u, huC, by simp⟩
    rw [starCNF, hB, hC]
    simp

lemma safe_intersection_neighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) (B C : Finset (Fin n))
    (hsafe : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true) :
    ∀ u ∈ B ∩ C, G.Adj a u := by
  intro u hu
  obtain ⟨huB, huC⟩ := Finset.mem_inter.mp hu
  rcases triple_safety G a B C hsafe u u huB huC with h | h | h
  · exact h
  · exact h
  · exact False.elim ((G.ne_of_adj h) rfl)

lemma safe_projection_covers_pairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (a : Fin n) (B C : Finset (Fin n)) (haB : a ∉ B) (haC : a ∉ C)
    (hsafe : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true) :
    ∃ D : Finset (Fin n), (D = B ∨ D = C) ∧
      (∀ u ∈ D, side u ≠ side a → G.Adj a u) ∧
      (∀ u, starCNF a B C (fun v => decide (v = a ∨ v = u)) = true →
        u ∈ D ∧ side u ≠ side a) := by
  have hn := safe_intersection_neighbors G a B C hsafe
  have hside : ∀ u ∈ B ∩ C, side u ≠ side a := by
    intro u hu h
    exact hproper a u (hn u hu) h.symm
  rcases chosen_leaf_projection G side hproper a B C hsafe with hb | hc
  · refine ⟨B, Or.inl rfl, hb, ?_⟩
    intro u hu
    have hi := (accepted_pair_iff a u B C haB haC).mp hu
    exact ⟨(Finset.mem_inter.mp hi).1, hside u hi⟩
  · refine ⟨C, Or.inr rfl, hc, ?_⟩
    intro u hu
    have hi := (accepted_pair_iff a u B C haB haC).mp hu
    exact ⟨(Finset.mem_inter.mp hi).2, hside u hi⟩

lemma outside_in_stray_neighborhood {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a z : Fin n) (B C : Finset (Fin n))
    (hsafe : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true)
    (hz : z ∈ B) (haz : ¬ G.Adj a z) :
    ∀ c ∈ C, ¬ G.Adj a c → G.Adj z c := by
  intro c hc hac
  exact outside_rectangle G a B C hsafe z hz c hc haz hac

lemma small_outside_classification {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) (B : Finset (Fin n))
    (hsmall : (B.filter (fun b => ¬ G.Adj a b)).card ≤ 1) :
    (∀ u ∈ B, G.Adj a u) ∨
      ∃ z ∈ B, ¬ G.Adj a z ∧ ∀ u ∈ B, G.Adj a u ∨ u = z := by
  classical
  by_cases hall : ∀ u ∈ B, G.Adj a u
  · exact Or.inl hall
  push Not at hall
  obtain ⟨z, hz, haz⟩ := hall
  right
  refine ⟨z, hz, haz, ?_⟩
  intro u hu
  by_cases hau : G.Adj a u
  · exact Or.inl hau
  right
  exact Finset.card_le_one.mp hsmall u (Finset.mem_filter.mpr ⟨hu, hau⟩)
    z (Finset.mem_filter.mpr ⟨hz, haz⟩)

lemma same_part_stray {n : ℕ} (G : SimpleGraph (Fin n))
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (a z : Fin n) (B : Finset (Fin n))
    (hB : ∀ u ∈ B, G.Adj a u ∨ u = z) :
    ∀ u ∈ B, side u = side a → u = z := by
  intro u hu hs
  rcases hB u hu with hau | huz
  · exact False.elim (hproper a u hau hs.symm)
  · exact huz

lemma opposite_part_stray {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (a z : Fin n) (B C : Finset (Fin n))
    (hsafe : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true)
    (hz : z ∈ B) (haz : ¬ G.Adj a z) (hside : side z ≠ side a)
    (hB : ∀ u ∈ B, G.Adj a u ∨ u = z) :
    (∀ u ∈ B, side u ≠ side a) ∧
      (∀ u ∈ C, side u ≠ side a → G.Adj a u) ∧
      (∀ u ∈ C, side u = side a → G.Adj z u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu h
    rcases hB u hu with hau | rfl
    · exact hproper a u hau h.symm
    · exact hside h
  · intro u hu hs
    by_contra hau
    have hzu := outside_in_stray_neighborhood G a z B C hsafe hz haz u hu hau
    have heq : side z = side u := by
      cases ha : side a <;> cases hz' : side z <;> cases hu' : side u <;> simp_all
    exact hproper z u hzu heq
  · intro u hu hs
    apply outside_in_stray_neighborhood G a z B C hsafe hz haz u hu
    intro hau
    exact hproper a u hau hs.symm

lemma same_part_stray_projection {n : ℕ} (G : SimpleGraph (Fin n))
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (a z : Fin n) (B : Finset (Fin n)) (hz : side z = side a)
    (hB : ∀ u ∈ B, G.Adj a u ∨ u = z) :
    (∀ u ∈ B, side u ≠ side a → G.Adj a u) ∧
      (B.filter (fun u => side u = side a)).card ≤ 1 := by
  constructor
  · intro u hu hs
    rcases hB u hu with hau | rfl
    · exact hau
    · exact False.elim (hs hz)
  · apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨hu, hus⟩ := Finset.mem_filter.mp hu
    obtain ⟨hv, hvs⟩ := Finset.mem_filter.mp hv
    exact (same_part_stray G side hproper a z B hB u hu hus).trans
      (same_part_stray G side hproper a z B hB v hv hvs).symm

lemma unique_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (a b : Fin n) (S : Finset (Fin n))
    (hlarge : 2 ≤ S.card) (ha : ∀ u ∈ S, G.Adj a u) (hb : ∀ u ∈ S, G.Adj b u) : a = b := by
  by_contra hab
  have hs : S ⊆ Finset.univ.filter (fun u => G.Adj a u ∧ G.Adj b u) := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha u hu, hb u hu⟩
  have hh := Finset.card_le_card hs
  have hn := hfour a b hab
  omega

lemma shared_mixed_support_forces_stray {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (a b z : Fin n) (B C S : Finset (Fin n))
    (hsafe : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true)
    (hz : z ∈ B) (haz : ¬ G.Adj a z) (hSC : S ⊆ C) (hlarge : 2 ≤ S.card)
    (hside : ∀ u ∈ S, side u = side a) (hb : ∀ u ∈ S, G.Adj b u) :
    z = b := by
  apply unique_center G hfour z b S hlarge
  · intro u hu
    apply outside_in_stray_neighborhood G a z B C hsafe hz haz u (hSC hu)
    intro hau
    exact hproper a u hau (hside u hu).symm
  · exact hb

lemma reciprocal_strays {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (a b za zb : Fin n) (Ba Ca Bb Cb Sa Sb : Finset (Fin n))
    (hsafea : ∀ x, starCNF a Ba Ca x = true → graphFun G ∅ x = true)
    (hsafeb : ∀ x, starCNF b Bb Cb x = true → graphFun G ∅ x = true)
    (hza : za ∈ Ba) (haza : ¬ G.Adj a za) (hzb : zb ∈ Bb) (hbzb : ¬ G.Adj b zb)
    (hSa : Sa ⊆ Ca) (hSb : Sb ⊆ Cb) (hla : 2 ≤ Sa.card) (hlb : 2 ≤ Sb.card)
    (hsidea : ∀ u ∈ Sa, side u = side a) (hsideb : ∀ u ∈ Sb, side u = side b)
    (hSaN : ∀ u ∈ Sa, G.Adj b u) (hSbN : ∀ u ∈ Sb, G.Adj a u) :
    za = b ∧ zb = a ∧ ¬ G.Adj a b := by
  have h1 := shared_mixed_support_forces_stray G hfour side hproper a b za Ba Ca Sa
    hsafea hza haza hSa hla hsidea hSaN
  have h2 := shared_mixed_support_forces_stray G hfour side hproper b a zb Bb Cb Sb
    hsafeb hzb hbzb hSb hlb hsideb hSbN
  exact ⟨h1, h2, h1 ▸ haza⟩

end StarThreeClause



namespace ThinProjection

def leaf {n : ℕ} (side : Fin n → Bool) (c : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter fun u => side u ≠ side c

def own {n : ℕ} (side : Fin n → Bool) (c : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter fun u => side u = side c

def Allowed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (c : Fin n) (S : Finset (Fin n)) : Prop :=
  leaf side c S ⊆ Finset.univ.filter (fun u => G.Adj c u) ∧ (own side c S).card ≤ 1

lemma allowed_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (c : Fin n) (S T : Finset (Fin n))
    (hST : S ⊆ T) (hT : Allowed G side c T) : Allowed G side c S := by
  constructor
  · intro u hu
    obtain ⟨hu, hs⟩ := Finset.mem_filter.mp hu
    exact hT.1 (Finset.mem_filter.mpr ⟨hST hu, hs⟩)
  · apply le_trans (Finset.card_le_card (show own side c S ⊆ own side c T from ?_)) hT.2
    intro u hu
    obtain ⟨hu, hs⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨hST hu, hs⟩

lemma distinct_allowed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool)
    (c d : Fin n) (hcd : c ≠ d) (S : Finset (Fin n))
    (hc : Allowed G side c S) (hd : Allowed G side d S)
    (hlc : 2 ≤ (leaf side c S).card) (hld : 2 ≤ (leaf side d S).card) : False := by
  by_cases hs : side c = side d
  · have heq : leaf side c S = leaf side d S := by simp only [leaf, hs]
    have hsub : leaf side c S ⊆ Finset.univ.filter (fun u => G.Adj c u ∧ G.Adj d u) := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp (hc.1 hu)).2,
        (Finset.mem_filter.mp (hd.1 (heq ▸ hu))).2⟩
    have hb := Finset.card_le_card hsub
    have hh := hfour c d hcd
    omega
  · have hp : ∀ u, side u = side c ↔ side u ≠ side d := by
      intro u
      cases hc : side c <;> cases hd : side d <;> cases hu : side u <;> simp_all
    have heq : own side c S = leaf side d S := by
      ext u
      simp only [own, leaf, Finset.mem_filter, hp]
    have hh := hc.2
    rw [heq] at hh
    omega

lemma thin_projection_budget {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool)
    (s : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (K : Finset (Fin n)) (T : Fin n → Finset ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (hstep : ∀ k < m, s (n + k) = s (a k) ∪ s (b k) ∨ s (n + k) = ∅)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + m))
    (hallowed : ∀ c ∈ K, ∀ w ∈ T c, Allowed G side c (s w)) :
    (∑ c ∈ K, ((T c).biUnion (fun w => leaf side c (s w))).card) ≤
      ((Finset.range m).filter fun k => 2 ≤ (s (n + k)).card).card +
        ∑ c ∈ K, (T c).card := by
  classical
  let ss : Fin n → ℕ → Finset (Fin n) := fun c w =>
    if Allowed G side c (s w) then leaf side c (s w) else ∅
  let pool : Fin n → Finset ℕ := fun c =>
    (Finset.range m).filter fun k => 2 ≤ (ss c (n + k)).card
  have hssinput : ∀ c, ∀ i < n, (ss c i).card ≤ 1 := by
    intro c i hi
    dsimp only [ss]
    split_ifs
    · exact (Finset.card_filter_le _ _).trans (hinput i hi)
    · simp
  have hssstep : ∀ c, ∀ k < m,
      ss c (n + k) = ss c (a k) ∪ ss c (b k) ∨ ss c (n + k) = ∅ := by
    intro c k hk
    by_cases hc : Allowed G side c (s (n + k))
    · rcases hstep k hk with hu | he
      · have hac : Allowed G side c (s (a k)) :=
          allowed_mono G side c _ _ (hu ▸ Finset.subset_union_left) hc
        have hbc : Allowed G side c (s (b k)) :=
          allowed_mono G side c _ _ (hu ▸ Finset.subset_union_right) hc
        left
        simp only [ss, hc, hac, hbc, ite_true]
        simp only [hu, leaf, Finset.filter_union]
      · right
        simp [ss, he, leaf]
    · right
      simp [ss, hc]
  have hbound : ∀ c ∈ K,
      ((T c).biUnion (fun w => leaf side c (s w))).card ≤ (pool c).card + (T c).card := by
    intro c hc
    have hh := MultiRoot.neighborhood_budget n m (ss c) a b Finset.univ
      (hssinput c) ha hb (hssstep c) (T c) (hT c hc)
      (fun w hw => Finset.subset_univ _)
    have heq : (T c).biUnion (ss c) = (T c).biUnion (fun w => leaf side c (s w)) := by
      apply Finset.biUnion_congr rfl
      intro w hw
      exact ite_eq_left (hallowed c hc w hw)
    rw [heq] at hh
    simpa only [Finset.subset_univ, true_and, pool] using hh
  have hpoolfacts : ∀ c k, k ∈ pool c →
      Allowed G side c (s (n + k)) ∧ 2 ≤ (leaf side c (s (n + k))).card := by
    intro c k hk
    have hcard := (Finset.mem_filter.mp hk).2
    have hc : Allowed G side c (s (n + k)) := by
      by_contra hn
      simp [ss, hn] at hcard
    exact ⟨hc, by simpa only [ss, hc, ite_true] using hcard⟩
  have hdisjoint : (K : Set (Fin n)).PairwiseDisjoint pool := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro k hkc hkd
    obtain ⟨hac, hlc⟩ := hpoolfacts c k hkc
    obtain ⟨had, hld⟩ := hpoolfacts d k hkd
    exact distinct_allowed G hfour side c d hcd (s (n + k)) hac had hlc hld
  have hpoolcard : (∑ c ∈ K, (pool c).card) ≤
      ((Finset.range m).filter fun k => 2 ≤ (s (n + k)).card).card := by
    rw [← Finset.card_biUnion hdisjoint]
    apply Finset.card_le_card
    intro k hk
    obtain ⟨c, hc, hkc⟩ := Finset.mem_biUnion.mp hk
    have hklt := (Finset.mem_filter.mp hkc).1
    have hcard := (hpoolfacts c k hkc).2
    exact Finset.mem_filter.mpr ⟨hklt, hcard.trans (Finset.card_filter_le _ _)⟩
  have hs := Finset.sum_le_sum (s := K) hbound
  rw [Finset.sum_add_distrib] at hs
  exact hs.trans (Nat.add_le_add_right hpoolcard _)

lemma circuit_thin_projection_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (K : Finset (Fin n)) (T : Fin n → Finset ℕ)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + C.size))
    (hallowed : ∀ c ∈ K, ∀ w ∈ T c, Allowed G side c (PEqualNP.TopForm.orIn n C w)) :
    (∑ c ∈ K, ((T c).biUnion (fun w => leaf side c (PEqualNP.TopForm.orIn n C w))).card) ≤
      ((Finset.range C.gates.length).filter fun k =>
        2 ≤ (PEqualNP.TopForm.orIn n C (n + k)).card).card +
          ∑ c ∈ K, (T c).card := by
  exact thin_projection_budget G hfour side (PEqualNP.TopForm.orIn n C)
    (fun k => PEqualNP.TopForm.opnd C k 0) (fun k => PEqualNP.TopForm.opnd C k 1) K T
    (RawOrSupport.orIn_input C)
    (fun k hk => RawOrSupport.opnd_lt hAO.2.2 hAO.2.1 hk 0)
    (fun k hk => RawOrSupport.opnd_lt hAO.2.2 hAO.2.1 hk 1)
    (RawOrSupport.orIn_binary hAO) hT hallowed

end ThinProjection

namespace ThinFamily

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma nontrivial_gate_accounting {n : ℕ} (C : Circuit) (M O : Finset ℕ)
    (hM : ∀ k ∈ M, k < C.gates.length ∧ (gateAt C k).op = GateOp.and)
    (hO : ∀ k ∈ O, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      orIn n C (n + k) = ∅) :
    ((Finset.range C.gates.length).filter fun k => 2 ≤ (orIn n C (n + k)).card).card +
      M.card + O.card ≤ C.size := by
  classical
  let R := (Finset.range C.gates.length).filter fun k => 2 ≤ (orIn n C (n + k)).card
  have hR : ∀ k ∈ R, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      2 ≤ (orIn n C (n + k)).card := by
    intro k hk
    obtain ⟨hkr, htwo⟩ := Finset.mem_filter.mp hk
    exact ⟨Finset.mem_range.mp hkr, RawOrSupport.support_nontrivial_or C k htwo, htwo⟩
  have hRM : Disjoint R M := by
    apply Finset.disjoint_left.mpr
    intro k hk hm
    have ho := (hR k hk).2.1
    rw [(hM k hm).2] at ho
    cases ho
  have hRO : Disjoint R O := by
    apply Finset.disjoint_left.mpr
    intro k hk ho
    have htwo := (hR k hk).2.2
    rw [(hO k ho).2.2] at htwo
    simp at htwo
  have hMO : Disjoint M O := by
    apply Finset.disjoint_left.mpr
    intro k hm ho
    have hb := (hO k ho).2.1
    rw [(hM k hm).2] at hb
    cases hb
  have hRM_O : Disjoint (R ∪ M) O := Finset.disjoint_union_left.mpr ⟨hRO, hMO⟩
  have hsub : R ∪ M ∪ O ⊆ Finset.range C.gates.length := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · rcases Finset.mem_union.mp hk with hk | hk
      · exact Finset.mem_range.mpr (hR k hk).1
      · exact Finset.mem_range.mpr (hM k hk).1
    · exact Finset.mem_range.mpr (hO k hk).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hRM_O, Finset.card_union_of_disjoint hRM,
    Finset.card_range] at hcard
  exact hcard

lemma shared_family_cover_bound {n p l : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (C : Circuit) (hAO : IsAO2 n C) (K : Finset (Fin n)) (T : Fin n → Finset ℕ)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + C.size))
    (hallowed : ∀ c ∈ K, ∀ w ∈ T c, ThinProjection.Allowed G side c (orIn n C w))
    (M O : Finset ℕ)
    (hM : ∀ k ∈ M, k < C.gates.length ∧ (gateAt C k).op = GateOp.and)
    (hO : ∀ k ∈ O, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      orIn n C (n + k) = ∅)
    (E EL ER F : Finset (Fin p × Fin l)) (L ZL : Finset (Fin p)) (R ZR : Finset (Fin l))
    (r s t : ℕ) (hcover : EL ∪ ER = E) (hfl : F ⊆ EL) (hfr : F ⊆ ER)
    (hlcover : L ⊆ F.image Prod.fst ∪ ZL) (hrcover : R ⊆ F.image Prod.snd ∪ ZR)
    (hr : F.card ≤ r) (ht : ZL.card + ZR.card ≤ s + t)
    (hleft : ∀ e ∈ EL, e.1 ∈ L) (hright : ∀ e ∈ ER, e.2 ∈ R)
    (hleaves : EL.card + ER.card ≤
      ∑ c ∈ K, ((T c).biUnion (fun w => ThinProjection.leaf side c (orIn n C w))).card)
    (hroots : (∑ c ∈ K, (T c).card) ≤ 2 * r + s + t)
    (hands : 2 * r + 2 * s + t ≤ M.card) (haggregation : r + s + t ≤ O.card + 1) :
    (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card + s ≤ C.size + 1 := by
  constructor
  · intro e he
    have he' : e ∈ EL ∪ ER := hcover.symm ▸ he
    exact (Finset.mem_union.mp he').elim (fun h => Or.inl (hleft e h))
      (fun h => Or.inr (hright e h))
  · have hb := ThinProjection.circuit_thin_projection_budget G hfour side C hAO K T hT hallowed
    have hg := nontrivial_gate_accounting C M O hM hO
    have hm := SharedThreeClauseLedger.edge_multiplicity E EL ER hcover
    have hc := SharedThreeClauseLedger.centre_budget EL ER F L ZL R ZR r (s + t)
      hfl hfr hlcover hrcover hr ht
    omega

end ThinFamily

namespace WmaxMatching

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma neighborhood_union_matching {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (p q : Fin n) (S : Finset (Fin n)) (hp : p ∉ S) (hq : q ∉ S)
    (hcover : ∀ u ∈ S, G.Adj p u ∨ G.Adj q u) :
    ∀ x ∈ S, (S.filter (fun y => G.Adj x y)).card ≤ 1 := by
  intro x hx
  have branch (a b : Fin n) (hax : G.Adj a x) (hb : b ∉ S)
      (hS : ∀ u ∈ S, G.Adj a u ∨ G.Adj b u) :
      (S.filter (fun y => G.Adj x y)).card ≤ 1 := by
    have hxb : x ≠ b := by
      intro heq
      exact hb (heq ▸ hx)
    have hsub : S.filter (fun y => G.Adj x y) ⊆
        Finset.univ.filter (fun y => G.Adj x y ∧ G.Adj b y) := by
      intro y hy
      obtain ⟨hy, hxy⟩ := Finset.mem_filter.mp hy
      have hay : ¬ G.Adj a y := by
        intro hadj
        have hax' := hproper a x hax
        have hxy' := hproper x y hxy
        have hay' := hproper a y hadj
        cases ha : side a <;> cases hx' : side x <;> cases hy' : side y <;> simp_all
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy, (hS y hy).resolve_left hay⟩
    exact (Finset.card_le_card hsub).trans (hfour x b hxb)
  rcases hcover x hx with hpx | hqx
  · exact branch p q hpx hq hcover
  · exact branch q p hqx hp (fun u hu => (hcover u hu).symm)

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p q : Fin n) :
    graphFun G ∅ (pairInput p q) = true ↔ G.Adj p q := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    have hu' : u = p ∨ u = q := by simpa [pairInput] using hu
    have hv' : v = p ∨ v = q := by simpa [pairInput] using hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact False.elim ((G.ne_of_adj huv) rfl)
    · exact huv
    · exact huv.symm
    · exact False.elim ((G.ne_of_adj huv) rfl)
  · intro hpq
    exact ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩

lemma graph_triple {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p q w : Fin n)
    (h : graphFun G ∅ (fun u => decide (u = p ∨ u = q ∨ u = w)) = true) :
    G.Adj p q ∨ G.Adj p w ∨ G.Adj q w := by
  have hedge : ∃ u v, G.Adj u v ∧ (u = p ∨ u = q ∨ u = w) ∧
      (v = p ∨ v = q ∨ v = w) := by
    simpa [graphFun] using h
  obtain ⟨u, v, huv, hu, hv⟩ := hedge
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact False.elim ((G.ne_of_adj huv) rfl)
  · exact Or.inl huv
  · exact Or.inr (Or.inl huv)
  · exact Or.inl huv.symm
  · exact False.elim ((G.ne_of_adj huv) rfl)
  · exact Or.inr (Or.inr huv)
  · exact Or.inr (Or.inl huv.symm)
  · exact Or.inr (Or.inr huv.symm)
  · exact False.elim ((G.ne_of_adj huv) rfl)

lemma wmax_avoids_bad_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (p q : Fin n) (hpq : ¬ G.Adj p q)
    (hbad : gateVal n C j (pairInput p q) = true) :
    p ∉ wmax G C j ∧ q ∉ wmax G C j := by
  constructor
  · intro hp
    have hh := (Finset.mem_filter.mp hp).2 (pairInput p q) hbad (by simp [pairInput])
    exact hpq ((graph_pair G p q).mp hh)
  · intro hq
    have hh := (Finset.mem_filter.mp hq).2 (pairInput p q) hbad (by simp [pairInput])
    exact hpq ((graph_pair G p q).mp hh)

lemma wmax_in_bad_pair_neighborhoods {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ)
    (hmono : ∀ x y : Fin n → Bool, (∀ u, x u = true → y u = true) →
      gateVal n C j x = true → gateVal n C j y = true)
    (p q : Fin n) (hpq : ¬ G.Adj p q) (hbad : gateVal n C j (pairInput p q) = true) :
    ∀ w ∈ wmax G C j, G.Adj p w ∨ G.Adj q w := by
  intro w hw
  let x : Fin n → Bool := fun u => decide (u = p ∨ u = q ∨ u = w)
  have hle : ∀ u, pairInput p q u = true → x u = true := by
    intro u hu
    have hu' : u = p ∨ u = q := by simpa [pairInput] using hu
    rcases hu' with rfl | rfl <;> simp [x]
  have hg : gateVal n C j x = true := hmono (pairInput p q) x hle hbad
  have hF := (Finset.mem_filter.mp hw).2 x hg (by simp [x])
  exact (graph_triple G p q w hF).resolve_left hpq

lemma wmax_induced_matching {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (j : ℕ)
    (hmono : ∀ x y : Fin n → Bool, (∀ u, x u = true → y u = true) →
      gateVal n C j x = true → gateVal n C j y = true)
    (p q : Fin n) (hpq : ¬ G.Adj p q) (hbad : gateVal n C j (pairInput p q) = true) :
    ∀ x ∈ wmax G C j, ((wmax G C j).filter (fun y => G.Adj x y)).card ≤ 1 := by
  obtain ⟨hp, hq⟩ := wmax_avoids_bad_pair G C j p q hpq hbad
  exact neighborhood_union_matching G hfour side hproper p q (wmax G C j) hp hq
    (wmax_in_bad_pair_neighborhoods G C j hmono p q hpq hbad)

lemma biclique_in_matching {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S U V : Finset (Fin n))
    (hmatching : ∀ x ∈ S, (S.filter (fun y => G.Adj x y)).card ≤ 1)
    (hUS : U ⊆ S) (hVS : V ⊆ S) (hU : U.Nonempty) (hV : V.Nonempty)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, G.Adj u v) : U.card ≤ 1 ∧ V.card ≤ 1 := by
  obtain ⟨u, hu⟩ := hU
  obtain ⟨v, hv⟩ := hV
  constructor
  · have hsub : U ⊆ S.filter (fun x => G.Adj v x) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨hUS hx, (hUV x hx v hv).symm⟩
    exact (Finset.card_le_card hsub).trans (hmatching v (hVS hv))
  · have hsub : V ⊆ S.filter (fun x => G.Adj u x) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨hVS hx, hUV u hu x hx⟩
    exact (Finset.card_le_card hsub).trans (hmatching u (hUS hu))

def linear {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ u ∈ S, x u = true)

lemma linear_product_wmax {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (U : Finset (Fin n))
    (hsafe : ∀ x, gateVal n C j x && linear U x = true → graphFun G ∅ x = true) :
    U ⊆ wmax G C j := by
  intro u hu
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro x hg hxu
  have hlin : linear U x = true := by
    apply decide_eq_true
    exact ⟨u, hu, hxu⟩
  apply hsafe x
  rw [hg, hlin]
  rfl

lemma linear_product_biclique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U V : Finset (Fin n))
    (hsafe : ∀ x, linear U x && linear V x = true → graphFun G ∅ x = true) :
    ∀ u ∈ U, ∀ v ∈ V, G.Adj u v := by
  intro u hu v hv
  have hU : linear U (pairInput u v) = true := by
    apply decide_eq_true
    exact ⟨u, hu, by simp [pairInput]⟩
  have hV : linear V (pairInput u v) = true := by
    apply decide_eq_true
    exact ⟨v, hv, by simp [pairInput]⟩
  apply (graph_pair G u v).mp
  apply hsafe (pairInput u v)
  rw [hU, hV]
  rfl

lemma terminal_triangle_single_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (j : ℕ)
    (hmono : ∀ x y : Fin n → Bool, (∀ u, x u = true → y u = true) →
      gateVal n C j x = true → gateVal n C j y = true)
    (p q : Fin n) (hpq : ¬ G.Adj p q) (hbad : gateVal n C j (pairInput p q) = true)
    (U V : Finset (Fin n))
    (hJU : ∀ x, gateVal n C j x && linear U x = true → graphFun G ∅ x = true)
    (hJV : ∀ x, gateVal n C j x && linear V x = true → graphFun G ∅ x = true)
    (hUV : ∀ x, linear U x && linear V x = true → graphFun G ∅ x = true) :
    (U ×ˢ V).card ≤ 1 := by
  by_cases hu : U.Nonempty
  · by_cases hv : V.Nonempty
    · have hm := wmax_induced_matching G hfour side hproper C j hmono p q hpq hbad
      obtain ⟨huc, hvc⟩ := biclique_in_matching G (wmax G C j) U V hm
        (linear_product_wmax G C j U hJU) (linear_product_wmax G C j V hJV)
        hu hv (linear_product_biclique G U V hUV)
      rw [Finset.card_product]
      exact (Nat.mul_le_mul huc hvc).trans (by simp)
    · have he : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hv
      simp [he]
  · have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hu
    simp [he]

lemma two_clause_monotone {n : ℕ} (C : Circuit) (j : ℕ) (P Q : Finset (Fin n))
    (hsem : ∀ x, gateVal n C j x = (linear P x && linear Q x)) :
    ∀ x y : Fin n → Bool, (∀ u, x u = true → y u = true) →
      gateVal n C j x = true → gateVal n C j y = true := by
  intro x y hxy hg
  have hx : linear P x = true ∧ linear Q x = true := by simpa [hsem x] using hg
  obtain ⟨p, hp, hxp⟩ := of_decide_eq_true hx.1
  obtain ⟨q, hq, hxq⟩ := of_decide_eq_true hx.2
  have hP : linear P y = true := by
    apply decide_eq_true
    exact ⟨p, hp, hxy p hxp⟩
  have hQ : linear Q y = true := by
    apply decide_eq_true
    exact ⟨q, hq, hxy q hxq⟩
  rw [hsem y, hP, hQ]
  rfl

lemma two_clause_bad_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (P Q : Finset (Fin n))
    (hsem : ∀ x, gateVal n C j x = (linear P x && linear Q x))
    (hdirty : ¬ BelowF G C j) :
    ∃ p ∈ P, ∃ q ∈ Q, ¬ G.Adj p q ∧ gateVal n C j (pairInput p q) = true := by
  classical
  unfold BelowF at hdirty
  push Not at hdirty
  obtain ⟨x, hg, hfalse⟩ := hdirty
  have hx : linear P x = true ∧ linear Q x = true := by simpa [hsem x] using hg
  obtain ⟨p, hp, hxp⟩ := of_decide_eq_true hx.1
  obtain ⟨q, hq, hxq⟩ := of_decide_eq_true hx.2
  refine ⟨p, hp, q, hq, ?_, ?_⟩
  · intro hadj
    apply hfalse
    have he : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := ⟨p, q, hadj, hxp, hxq⟩
    simpa [graphFun] using he
  · have hP : linear P (pairInput p q) = true := by
      apply decide_eq_true
      exact ⟨p, hp, by simp [pairInput]⟩
    have hQ : linear Q (pairInput p q) = true := by
      apply decide_eq_true
      exact ⟨q, hq, by simp [pairInput]⟩
    rw [hsem, hP, hQ]
    rfl

lemma dirty_two_clause_terminal_single_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (j : ℕ) (P Q U V : Finset (Fin n))
    (hsem : ∀ x, gateVal n C j x = (linear P x && linear Q x)) (hdirty : ¬ BelowF G C j)
    (hJU : ∀ x, gateVal n C j x && linear U x = true → graphFun G ∅ x = true)
    (hJV : ∀ x, gateVal n C j x && linear V x = true → graphFun G ∅ x = true)
    (hUV : ∀ x, linear U x && linear V x = true → graphFun G ∅ x = true) :
    (U ×ˢ V).card ≤ 1 := by
  obtain ⟨p, _, q, _, hpq, hbad⟩ := two_clause_bad_pair G C j P Q hsem hdirty
  exact terminal_triangle_single_edge G hfour side hproper C j (two_clause_monotone C j P Q hsem)
    p q hpq hbad U V hJU hJV hUV

lemma linear_lower {n : ℕ} (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
    (hlower : ∀ a ∈ A, ∀ x, x a = true → f x = true) :
    ∀ x, linear A x = true → f x = true := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := of_decide_eq_true hx
  exact hlower a ha x hxa

lemma lower_product_safety {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f g f' g' : (Fin n → Bool) → Bool)
    (hf : ∀ x, f' x = true → f x = true) (hg : ∀ x, g' x = true → g x = true)
    (hsafe : ∀ x, f x && g x = true → graphFun G ∅ x = true) :
    ∀ x, f' x && g' x = true → graphFun G ∅ x = true := by
  intro x hx
  have hh : f' x = true ∧ g' x = true := by simpa using hx
  apply hsafe x
  rw [hf x hh.1, hg x hh.2]
  rfl

lemma mixed_terminal_support_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (j : ℕ)
    (hmono : ∀ x y : Fin n → Bool, (∀ u, x u = true → y u = true) →
      gateVal n C j x = true → gateVal n C j y = true)
    (p q : Fin n) (hpq : ¬ G.Adj p q) (hbad : gateVal n C j (pairInput p q) = true)
    (A B : Finset (Fin n)) (f g : (Fin n → Bool) → Bool)
    (hA : ∀ a ∈ A, ∀ x, x a = true → f x = true)
    (hB : ∀ b ∈ B, ∀ x, x b = true → g x = true)
    (hJf : ∀ x, gateVal n C j x && f x = true → graphFun G ∅ x = true)
    (hJg : ∀ x, gateVal n C j x && g x = true → graphFun G ∅ x = true)
    (hfg : ∀ x, f x && g x = true → graphFun G ∅ x = true) :
    (A ×ˢ B).card ≤ 1 := by
  have hf := linear_lower A f hA
  have hg := linear_lower B g hB
  exact terminal_triangle_single_edge G hfour side hproper C j hmono p q hpq hbad A B
    (lower_product_safety G (gateVal n C j) f (gateVal n C j) (linear A) (fun _ h => h) hf hJf)
    (lower_product_safety G (gateVal n C j) g (gateVal n C j) (linear B) (fun _ h => h) hg hJg)
    (lower_product_safety G f g (linear A) (linear B) hf hg hfg)

lemma dirty_two_clause_mixed_terminal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (j : ℕ) (P Q A B : Finset (Fin n)) (f g : (Fin n → Bool) → Bool)
    (hsem : ∀ x, gateVal n C j x = (linear P x && linear Q x)) (hdirty : ¬ BelowF G C j)
    (hA : ∀ a ∈ A, ∀ x, x a = true → f x = true)
    (hB : ∀ b ∈ B, ∀ x, x b = true → g x = true)
    (hJf : ∀ x, gateVal n C j x && f x = true → graphFun G ∅ x = true)
    (hJg : ∀ x, gateVal n C j x && g x = true → graphFun G ∅ x = true)
    (hfg : ∀ x, f x && g x = true → graphFun G ∅ x = true) :
    (A ×ˢ B).card ≤ 1 := by
  obtain ⟨p, _, q, _, hpq, hbad⟩ := two_clause_bad_pair G C j P Q hsem hdirty
  exact mixed_terminal_support_card G hfour side hproper C j (two_clause_monotone C j P Q hsem)
    p q hpq hbad A B f g hA hB hJf hJg hfg

end WmaxMatching

namespace MergeBudget

lemma nonredundant_support_budget {α : Type} [DecidableEq α]
    (n m : ℕ) (s : ℕ → Finset α) (a b : ℕ → ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (hstep : ∀ k < m, s (n + k) = s (a k) ∪ s (b k) ∨ s (n + k) = ∅)
    (T : Finset ℕ) (hT : T ⊆ Finset.range (n + m)) :
    (T.biUnion s).card ≤
      ((Finset.range m).filter fun k => s (n + k) ≠ ∅ ∧
        ¬ s (n + k) ⊆ s (a k) ∧ ¬ s (n + k) ⊆ s (b k)).card + T.card := by
  classical
  let cost : ℕ → ℕ := fun k => if s (n + k) ≠ ∅ ∧
      ¬ s (n + k) ⊆ s (a k) ∧ ¬ s (n + k) ⊆ s (b k) then 1 else 0
  have hparents : ∀ k < m, ∃ P : Finset ℕ,
      P ⊆ Finset.range (n + k) ∧ P.card ≤ cost k + 1 ∧
        s (n + k) ⊆ P.biUnion s := by
    intro k hk
    by_cases he : s (n + k) = ∅
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp [he]⟩
    by_cases hl : s (n + k) ⊆ s (a k)
    · refine ⟨{a k}, ?_, by simp, ?_⟩
      · simpa using ha k hk
      · simpa only [Finset.singleton_biUnion] using hl
    by_cases hr : s (n + k) ⊆ s (b k)
    · refine ⟨{b k}, ?_, by simp, ?_⟩
      · simpa using hb k hk
      · simpa only [Finset.singleton_biUnion] using hr
    have hu : s (n + k) = s (a k) ∪ s (b k) := (hstep k hk).resolve_right he
    refine ⟨{a k, b k}, ?_, ?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_range.mpr (ha k hk)
      · exact Finset.mem_range.mpr (hb k hk)
    · simpa [cost, he, hl, hr] using (Finset.card_le_two : ({a k, b k} : Finset ℕ).card ≤ 2)
    · simpa only [Finset.biUnion_insert, Finset.singleton_biUnion, hu]
        using (Finset.Subset.refl (s (a k) ∪ s (b k)))
  let parents : ℕ → Finset ℕ := fun k => if hk : k < m then (hparents k hk).choose else ∅
  have hp : ∀ k < m, parents k ⊆ Finset.range (n + k) := by
    intro k hk
    simpa [parents, hk] using (hparents k hk).choose_spec.1
  have hc : ∀ k < m, (parents k).card ≤ cost k + 1 := by
    intro k hk
    simpa [parents, hk] using (hparents k hk).choose_spec.2.1
  have hv : ∀ k < m, s (n + k) ⊆ (parents k).biUnion s := by
    intro k hk
    simpa [parents, hk] using (hparents k hk).choose_spec.2.2
  have hbound := MultiRoot.support_family_bound n m s parents cost hinput hp hc hv T hT
  have hsum : (Finset.range m).sum cost =
      ((Finset.range m).filter fun k => s (n + k) ≠ ∅ ∧
        ¬ s (n + k) ⊆ s (a k) ∧ ¬ s (n + k) ⊆ s (b k)).card := by
    simp only [cost, Finset.sum_boole]
    rfl
  rw [hsum] at hbound
  exact hbound

end MergeBudget

namespace NearMergeCharges

def project {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n) (A : Finset (Fin n)) : Finset (Fin n) := A.filter fun u => G.Adj c u

def Charged {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n) (A B : Finset (Fin n)) : Prop :=
  ¬ project G c A ⊆ project G c B ∧ ¬ project G c B ⊆ project G c A

lemma charged_iff_nonredundant {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n) (A B : Finset (Fin n)) :
    Charged G c A B ↔ project G c (A ∪ B) ≠ project G c A ∧
      project G c (A ∪ B) ≠ project G c B := by
  have hu : project G c (A ∪ B) = project G c A ∪ project G c B := by
    exact Finset.filter_union _ _ _
  rw [hu]
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · intro heq
      apply hb
      intro u h
      rw [← heq]
      exact Finset.mem_union_right _ h
    · intro heq
      apply ha
      intro u h
      rw [← heq]
      exact Finset.mem_union_left _ h
  · rintro ⟨ha, hb⟩
    constructor
    · intro hsub
      exact hb (Finset.union_eq_right.mpr hsub)
    · intro hsub
      exact ha (Finset.union_eq_left.mpr hsub)

lemma charge_witnesses {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n) (A B : Finset (Fin n)) (h : Charged G c A B) :
    ∃ u ∈ A \ B, ∃ v ∈ B \ A, G.Adj c u ∧ G.Adj c v := by
  obtain ⟨ha, hb⟩ := h
  change ¬ (∀ u, u ∈ project G c A → u ∈ project G c B) at ha
  change ¬ (∀ u, u ∈ project G c B → u ∈ project G c A) at hb
  push Not at ha hb
  obtain ⟨u, hu, hun⟩ := ha
  obtain ⟨v, hv, hvn⟩ := hb
  obtain ⟨huA, hcu⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvB, hcv⟩ := Finset.mem_filter.mp hv
  have huB : u ∉ B := fun h => hun (Finset.mem_filter.mpr ⟨h, hcu⟩)
  have hvA : v ∉ A := fun h => hvn (Finset.mem_filter.mpr ⟨h, hcv⟩)
  exact ⟨u, Finset.mem_sdiff.mpr ⟨huA, huB⟩, v,
    Finset.mem_sdiff.mpr ⟨hvB, hvA⟩, hcu, hcv⟩

lemma charged_centers_le_difference_product {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (A B K : Finset (Fin n))
    (hK : ∀ c ∈ K, Charged G c A B) : K.card ≤ ((A \ B) ×ˢ (B \ A)).card := by
  classical
  have hw : ∀ c ∈ K, ∃ p ∈ (A \ B) ×ˢ (B \ A), G.Adj c p.1 ∧ G.Adj c p.2 := by
    intro c hc
    obtain ⟨u, hu, v, hv, hcu, hcv⟩ := charge_witnesses G c A B (hK c hc)
    exact ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, hcu, hcv⟩
  let f : Fin n → Fin n × Fin n := fun c => if hc : c ∈ K then (hw c hc).choose else (c, c)
  have hf : ∀ c ∈ K, f c ∈ (A \ B) ×ˢ (B \ A) ∧ G.Adj c (f c).1 ∧ G.Adj c (f c).2 := by
    intro c hc
    simpa only [f, dite_eq_left hc] using (hw c hc).choose_spec
  apply Finset.card_le_card_of_injOn f
  · intro c hc
    exact (hf c hc).1
  · intro c hc d hd heq
    obtain ⟨hcP, hcu, hcv⟩ := hf c hc
    obtain ⟨_, hdu, hdv⟩ := hf d hd
    rw [← heq] at hdu hdv
    have hne : (f c).1 ≠ (f c).2 := by
      intro h
      have hu := (Finset.mem_product.mp hcP).1
      have hv := (Finset.mem_product.mp hcP).2
      exact (Finset.mem_sdiff.mp hu).2 (h ▸ (Finset.mem_sdiff.mp hv).1)
    exact Finset.card_le_one.mp (hfour (f c).1 (f c).2 hne) c
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcu.symm, hcv.symm⟩) d
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdu.symm, hdv.symm⟩)

lemma small_difference_product {α : Type} [DecidableEq α] (A B : Finset α)
    (hsmall : (A ∪ B).card ≤ 3) : ((A \ B) ×ˢ (B \ A)).card ≤ 2 := by
  have hd : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mp hv).1
  have hs : (A \ B) ∪ (B \ A) ⊆ A ∪ B := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hu).1
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hu).1
  have hsum := (Finset.card_le_card hs).trans hsmall
  rw [Finset.card_union_of_disjoint hd] at hsum
  rw [Finset.card_product]
  have arithmetic : ∀ x y : ℕ, x + y ≤ 3 → x * y ≤ 2 := by
    intro x y hxy
    have hx : x ≤ 3 := by omega
    interval_cases x <;> omega
  exact arithmetic _ _ hsum

lemma small_merge_charge_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (A B K : Finset (Fin n))
    (hsmall : (A ∪ B).card ≤ 3) (hK : ∀ c ∈ K, Charged G c A B) : K.card ≤ 2 :=
  (charged_centers_le_difference_product G hfour A B K hK).trans (small_difference_product A B hsmall)

lemma large_near_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (S : Finset (Fin n)) (hlarge : 4 ≤ S.card)
    (c d : Fin n)
    (hc : (S.filter (fun u => ¬ G.Adj c u)).card ≤ 1)
    (hd : (S.filter (fun u => ¬ G.Adj d u)).card ≤ 1) : c = d := by
  by_contra hcd
  let N := Finset.univ.filter fun u => G.Adj c u ∧ G.Adj d u
  let X := S.filter fun u => ¬ G.Adj c u
  let Y := S.filter fun u => ¬ G.Adj d u
  have hs : S ⊆ N ∪ X ∪ Y := by
    intro u hu
    by_cases hcu : G.Adj c u
    · by_cases hdu : G.Adj d u
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcu, hdu⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, hdu⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, hcu⟩))
  have h1 := Finset.card_le_card hs
  have h2 := Finset.card_union_le (N ∪ X) Y
  have h3 := Finset.card_union_le N X
  have hn : N.card ≤ 1 := hfour c d hcd
  change X.card ≤ 1 at hc
  change Y.card ≤ 1 at hd
  omega

lemma near_merge_charge_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (A B K : Finset (Fin n))
    (hnear : ∀ c ∈ K, ((A ∪ B).filter (fun u => ¬ G.Adj c u)).card ≤ 1)
    (hK : ∀ c ∈ K, Charged G c A B) : K.card ≤ 2 := by
  by_cases hs : (A ∪ B).card ≤ 3
  · exact small_merge_charge_card G hfour A B K hs hK
  have hone : K.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro c hc d hd
    exact large_near_unique G hfour (A ∪ B) (by omega) c d (hnear c hc) (hnear d hd)
  omega

lemma contained_merge_charge_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (A B K : Finset (Fin n))
    (d : Fin n) (hcontained : ∀ u ∈ A ∪ B, G.Adj d u)
    (hK : ∀ c ∈ K, Charged G c A B) : K.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  have hcenter : ∀ c ∈ K, c = d := by
    intro c hc
    by_contra hcd
    obtain ⟨u, hu, v, hv, hcu, hcv⟩ := charge_witnesses G c A B (hK c hc)
    have hdu := hcontained u (Finset.mem_union_left _ (Finset.mem_sdiff.mp hu).1)
    have hdv := hcontained v (Finset.mem_union_right _ (Finset.mem_sdiff.mp hv).1)
    have huv : u = v := Finset.card_le_one.mp (hfour c d hcd) u
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcu, hdu⟩) v
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv, hdv⟩)
    exact (Finset.mem_sdiff.mp hu).2 (huv ▸ (Finset.mem_sdiff.mp hv).1)
  intro c hc e he
  exact (hcenter c hc).trans (hcenter e he).symm

end NearMergeCharges

namespace NearColorCases

open NearMergeCharges

def BAllowed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (c : Fin n) (S : Finset (Fin n)) : Prop :=
  ((∀ u ∈ S, side u ≠ side c) ∧ (S.filter (fun u => ¬ G.Adj c u)).card ≤ 1) ∨
    ((∀ u ∈ S, side u ≠ side c → G.Adj c u) ∧ (S.filter (fun u => side u = side c)).card ≤ 1)

noncomputable def chargeSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (K A B : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact K.filter fun c => BAllowed G side c (A ∪ B) ∧ Charged G c A B

lemma allowed_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (c : Fin n) (S T : Finset (Fin n))
    (hST : S ⊆ T) (hT : BAllowed G side c T) : BAllowed G side c S := by
  have hfilter (p : Fin n → Prop) [DecidablePred p] : S.filter p ⊆ T.filter p := by
    intro u hu
    obtain ⟨hu, hp⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨hST hu, hp⟩
  rcases hT with ⟨hside, hnear⟩ | ⟨hside, hthin⟩
  · exact Or.inl ⟨fun u hu => hside u (hST hu),
      (Finset.card_le_card (hfilter _)).trans hnear⟩
  · exact Or.inr ⟨fun u hu => hside u (hST hu),
      (Finset.card_le_card (hfilter _)).trans hthin⟩

lemma opposite_eq (a b c : Bool) (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma allowed_own_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (c : Fin n) (S : Finset (Fin n))
    (h : BAllowed G side c S) : (S.filter (fun u => side u = side c)).card ≤ 1 := by
  rcases h with ⟨hopp, _⟩ | ⟨_, hthin⟩
  · have he : S.filter (fun u => side u = side c) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨hu, hs⟩ := Finset.mem_filter.mp hu
      exact hopp u hu hs
    simp [he]
  · exact hthin

lemma thin_of_mixed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (c : Fin n) (S : Finset (Fin n))
    (hmixed : ¬ ∀ u ∈ S, ∀ v ∈ S, side u = side v) (h : BAllowed G side c S) :
    (∀ u ∈ S, side u ≠ side c → G.Adj c u) ∧ (S.filter (fun u => side u = side c)).card ≤ 1 := by
  rcases h with ⟨hopp, _⟩ | hthin
  · exact (hmixed (fun u hu v hv => opposite_eq _ _ _ (hopp u hu) (hopp v hv))).elim
  · exact hthin

lemma charged_near_of_pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (c : Fin n) (A B : Finset (Fin n))
    (hpure : ∀ u ∈ A ∪ B, ∀ v ∈ A ∪ B, side u = side v)
    (hallowed : BAllowed G side c (A ∪ B)) (hcharge : Charged G c A B) :
    ((A ∪ B).filter (fun u => ¬ G.Adj c u)).card ≤ 1 := by
  rcases hallowed with ⟨_, hnear⟩ | ⟨hgood, _⟩
  · exact hnear
  · obtain ⟨u, hu, _, _, hcu, _⟩ := charge_witnesses G c A B hcharge
    have huS : u ∈ A ∪ B := Finset.mem_union_left _ (Finset.mem_sdiff.mp hu).1
    have hall : ∀ v ∈ A ∪ B, G.Adj c v := by
      intro v hv
      apply hgood v hv
      intro hvside
      exact hproper c u hcu (hvside.symm.trans (hpure v hv u huS))
    have he : (A ∪ B).filter (fun u => ¬ G.Adj c u) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hv, hvn⟩ := Finset.mem_filter.mp hv
      exact hvn (hall v hv)
    simp [he]

lemma charge_card_pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v) (K A B : Finset (Fin n))
    (hpure : ∀ u ∈ A ∪ B, ∀ v ∈ A ∪ B, side u = side v) :
    (chargeSet G side K A B).card ≤ 2 := by
  classical
  apply near_merge_charge_card G hfour A B (chargeSet G side K A B)
  · intro c hc
    obtain ⟨_, hallowed, hcharge⟩ := Finset.mem_filter.mp hc
    exact charged_near_of_pure G side hproper c A B hpure hallowed hcharge
  · intro c hc
    exact (Finset.mem_filter.mp hc).2.2

lemma distinct_thin_charges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v) (c d : Fin n) (A B : Finset (Fin n))
    (hd : (∀ u ∈ A ∪ B, side u ≠ side d → G.Adj d u) ∧
      ((A ∪ B).filter (fun u => side u = side d)).card ≤ 1)
    (hcharge : Charged G c A B) : c = d := by
  obtain ⟨u, hu, v, hv, hcu, hcv⟩ := charge_witnesses G c A B hcharge
  have huS : u ∈ A ∪ B := Finset.mem_union_left _ (Finset.mem_sdiff.mp hu).1
  have hvS : v ∈ A ∪ B := Finset.mem_union_right _ (Finset.mem_sdiff.mp hv).1
  have huv : u ≠ v := by
    intro heq
    exact (Finset.mem_sdiff.mp hu).2 (heq ▸ (Finset.mem_sdiff.mp hv).1)
  by_contra hcd
  by_cases hs : side c = side d
  · have hdu : G.Adj d u := hd.1 u huS (by intro h; exact hproper c u hcu (hs.trans h.symm))
    have hdv : G.Adj d v := hd.1 v hvS (by intro h; exact hproper c v hcv (hs.trans h.symm))
    exact huv (Finset.card_le_one.mp (hfour c d hcd) u
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcu, hdu⟩) v
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv, hdv⟩))
  · have huown : side u = side d := opposite_eq _ _ _ (Ne.symm (hproper c u hcu)) (Ne.symm hs)
    have hvown : side v = side d := opposite_eq _ _ _ (Ne.symm (hproper c v hcv)) (Ne.symm hs)
    exact huv (Finset.card_le_one.mp hd.2 u (Finset.mem_filter.mpr ⟨huS, huown⟩)
      v (Finset.mem_filter.mpr ⟨hvS, hvown⟩))

lemma charge_card_mixed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v) (K A B : Finset (Fin n))
    (hmixed : ¬ ∀ u ∈ A ∪ B, ∀ v ∈ A ∪ B, side u = side v) :
    (chargeSet G side K A B).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro c hc d hd
  obtain ⟨_, _, hcharge⟩ := Finset.mem_filter.mp hc
  obtain ⟨_, hallowed, _⟩ := Finset.mem_filter.mp hd
  exact distinct_thin_charges G hfour side hproper c d A B
    (thin_of_mixed G side d (A ∪ B) hmixed hallowed) hcharge

lemma charge_card_both_large {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (K A B : Finset (Fin n))
    (hfalse : 2 ≤ ((A ∪ B).filter (fun u => side u = false)).card)
    (htrue : 2 ≤ ((A ∪ B).filter (fun u => side u = true)).card) :
    (chargeSet G side K A B).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨_, hallowed, _⟩ := Finset.mem_filter.mp hc
  have hown := allowed_own_card G side c (A ∪ B) hallowed
  cases hs : side c <;> simp only [hs] at hown <;> omega

lemma charge_card_contained {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool) (K A B : Finset (Fin n))
    (d : Fin n) (hcontained : ∀ u ∈ A ∪ B, G.Adj d u) :
    (chargeSet G side K A B).card ≤ 1 := by
  classical
  apply contained_merge_charge_card G hfour A B (chargeSet G side K A B) d hcontained
  intro c hc
  exact (Finset.mem_filter.mp hc).2.2

lemma charge_card_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (K A B : Finset (Fin n)) (hsmall : (A ∪ B).card ≤ 1) :
    (chargeSet G side K A B).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨_, _, hcharge⟩ := Finset.mem_filter.mp hc
  obtain ⟨u, hu, v, hv, _, _⟩ := charge_witnesses G c A B hcharge
  have heq : u = v := Finset.card_le_one.mp hsmall u
    (Finset.mem_union_left _ (Finset.mem_sdiff.mp hu).1) v
    (Finset.mem_union_right _ (Finset.mem_sdiff.mp hv).1)
  exact (Finset.mem_sdiff.mp hu).2 (heq ▸ (Finset.mem_sdiff.mp hv).1)

lemma charge_card_le_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v) (K A B : Finset (Fin n)) :
    (chargeSet G side K A B).card ≤ 2 := by
  by_cases hpure : ∀ u ∈ A ∪ B, ∀ v ∈ A ∪ B, side u = side v
  · exact charge_card_pure G hfour side hproper K A B hpure
  · exact (charge_card_mixed G hfour side hproper K A B hpure).trans (by omega)

end NearColorCases

namespace NearProjectionBudget

open NearMergeCharges

noncomputable def mergeChargeSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Q : Fin n → Finset (Fin n) → Prop) (K S A B : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact K.filter fun c => S ≠ ∅ ∧ Q c S ∧ Charged G c A B

lemma filtered_projection_budget {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Q : Fin n → Finset (Fin n) → Prop)
    (hQ : ∀ c S U, S ⊆ U → Q c U → Q c S)
    (s : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (K : Finset (Fin n)) (T : Fin n → Finset ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (hstep : ∀ k < m, s (n + k) = s (a k) ∪ s (b k) ∨ s (n + k) = ∅)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + m))
    (hallowed : ∀ c ∈ K, ∀ w ∈ T c, Q c (s w)) :
    (∑ c ∈ K, ((T c).biUnion (fun w => project G c (s w))).card) ≤
      (∑ k ∈ Finset.range m, (mergeChargeSet G Q K (s (n + k)) (s (a k)) (s (b k))).card) +
        ∑ c ∈ K, (T c).card := by
  classical
  let ss : Fin n → ℕ → Finset (Fin n) := fun c w =>
    if Q c (s w) then project G c (s w) else ∅
  let P : ℕ → Fin n → Prop := fun k c =>
    s (n + k) ≠ ∅ ∧ Q c (s (n + k)) ∧ Charged G c (s (a k)) (s (b k))
  have hi : ∀ c, ∀ i < n, (ss c i).card ≤ 1 := by
    intro c i hin
    dsimp only [ss]
    split_ifs
    · exact (Finset.card_filter_le _ _).trans (hinput i hin)
    · simp
  have hsstep : ∀ c, ∀ k < m,
      ss c (n + k) = ss c (a k) ∪ ss c (b k) ∨ ss c (n + k) = ∅ := by
    intro c k hk
    by_cases hc : Q c (s (n + k))
    · rcases hstep k hk with hu | he
      · have hac := hQ c (s (a k)) (s (n + k)) (hu ▸ Finset.subset_union_left) hc
        have hbc := hQ c (s (b k)) (s (n + k)) (hu ▸ Finset.subset_union_right) hc
        left
        simp only [ss, hc, hac, hbc, ite_true]
        simp only [hu, project, Finset.filter_union]
      · right
        simp [ss, he, project]
    · right
      simp [ss, hc]
  have hrow : ∀ c ∈ K,
      ((T c).biUnion (fun w => project G c (s w))).card ≤
        ((Finset.range m).filter fun k => P k c).card + (T c).card := by
    intro c hc
    have hh := MergeBudget.nonredundant_support_budget n m (ss c) a b
      (hi c) ha hb (hsstep c) (T c) (hT c hc)
    have heq : (T c).biUnion (ss c) = (T c).biUnion (fun w => project G c (s w)) := by
      apply Finset.biUnion_congr rfl
      intro w hw
      exact ite_eq_left (hallowed c hc w hw)
    rw [heq] at hh
    apply hh.trans
    apply Nat.add_le_add_right
    apply Finset.card_le_card
    intro k hk
    obtain ⟨hkr, hne, hl, hr⟩ := Finset.mem_filter.mp hk
    have hkm := Finset.mem_range.mp hkr
    have hqc : Q c (s (n + k)) := by
      by_contra hn
      exact hne (by simp [ss, hn])
    have hraw : s (n + k) ≠ ∅ := by
      intro he
      exact hne (by simp [ss, he, project])
    have hu : s (n + k) = s (a k) ∪ s (b k) := (hstep k hkm).resolve_right hraw
    have hqa := hQ c (s (a k)) (s (n + k)) (hu ▸ Finset.subset_union_left) hqc
    have hqb := hQ c (s (b k)) (s (n + k)) (hu ▸ Finset.subset_union_right) hqc
    simp only [ss, hqc, hqa, hqb, ite_true] at hl hr
    have hproj : project G c (s (n + k)) =
        project G c (s (a k)) ∪ project G c (s (b k)) := by
      simp only [hu, project, Finset.filter_union]
    have hcharge : Charged G c (s (a k)) (s (b k)) := by
      constructor
      · intro hab
        apply hr
        rw [hproj]
        exact Finset.union_subset hab (Finset.Subset.refl _)
      · intro hba
        apply hl
        rw [hproj]
        exact Finset.union_subset (Finset.Subset.refl _) hba
    exact Finset.mem_filter.mpr ⟨hkr, hraw, hqc, hcharge⟩
  have hsum := Finset.sum_le_sum (s := K) hrow
  rw [Finset.sum_add_distrib] at hsum
  have hswap : (∑ c ∈ K, ((Finset.range m).filter fun k => P k c).card) =
      ∑ k ∈ Finset.range m, (K.filter fun c => P k c).card := by
    calc
      (∑ c ∈ K, ((Finset.range m).filter fun k => P k c).card) =
          ∑ c ∈ K, ∑ k ∈ Finset.range m, if P k c then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        simp only [Finset.sum_boole]
        rfl
      _ = ∑ k ∈ Finset.range m, ∑ c ∈ K, if P k c then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ k ∈ Finset.range m, (K.filter fun c => P k c).card := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.sum_boole]
        rfl
  rw [hswap] at hsum
  exact hsum

end NearProjectionBudget

namespace CProjectionCharges

def colorPart {n : ℕ} (side : Fin n → Bool) (b : Bool) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter fun u => side u = b

def leaf {n : ℕ} (side : Fin n → Bool) (c : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter fun u => side u ≠ side c

def Pure {n : ℕ} (side : Fin n → Bool) (S : Finset (Fin n)) : Prop :=
  ∃ b : Bool, ∀ u ∈ S, side u = b

def Thick {n : ℕ} (side : Fin n → Bool) (S : Finset (Fin n)) : Prop :=
  2 ≤ (colorPart side false S).card ∧ 2 ≤ (colorPart side true S).card

def Contained {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∃ c : Fin n, ∀ u ∈ S, G.Adj c u

def chargeSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (K S : Finset (Fin n)) : Finset (Fin n) :=
  K.filter fun c => leaf side c S ⊆ Finset.univ.filter (fun u => G.Adj c u) ∧
    2 ≤ (leaf side c S).card

lemma same_color_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool) (K S : Finset (Fin n))
    (c d : Fin n) (hc : c ∈ chargeSet G side K S) (hd : d ∈ chargeSet G side K S)
    (hside : side c = side d) : c = d := by
  by_contra hcd
  obtain ⟨_, hcn, hlarge⟩ := Finset.mem_filter.mp hc
  obtain ⟨_, hdn, _⟩ := Finset.mem_filter.mp hd
  have heq : leaf side c S = leaf side d S := by simp only [leaf, hside]
  have hsub : leaf side c S ⊆ Finset.univ.filter (fun u => G.Adj c u ∧ G.Adj d u) := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp (hcn hu)).2, (Finset.mem_filter.mp (hdn (heq ▸ hu))).2⟩
  have hcard := Finset.card_le_card hsub
  have hbound := hfour c d hcd
  omega

lemma charge_card_le_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool) (K S : Finset (Fin n)) :
    (chargeSet G side K S).card ≤ 2 := by
  let A := chargeSet G side K S
  have hsmall : ∀ b : Bool, (A.filter (fun c => side c = b)).card ≤ 1 := by
    intro b
    apply Finset.card_le_one.mpr
    intro c hc d hd
    obtain ⟨hc, hcb⟩ := Finset.mem_filter.mp hc
    obtain ⟨hd, hdb⟩ := Finset.mem_filter.mp hd
    exact same_color_unique G hfour side K S c d hc hd (hcb.trans hdb.symm)
  have hcover : A.filter (fun c => side c = false) ∪ A.filter (fun c => side c = true) = A := by
    ext c
    cases hs : side c <;> simp [hs]
  have hcard := Finset.card_union_le (A.filter (fun c => side c = false)) (A.filter (fun c => side c = true))
  rw [hcover] at hcard
  have h0 := hsmall false
  have h1 := hsmall true
  exact hcard.trans (by omega)

lemma leaf_of_color {n : ℕ} (side : Fin n → Bool) (c : Fin n) (S : Finset (Fin n)) :
    leaf side c S = colorPart side (!side c) S := by
  ext u
  cases hc : side c <;> cases hu : side u <;> simp [leaf, colorPart, hc, hu]

lemma two_charges_thick {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool) (K S : Finset (Fin n))
    (c d : Fin n) (hc : c ∈ chargeSet G side K S) (hd : d ∈ chargeSet G side K S)
    (hcd : c ≠ d) : Thick side S := by
  have hne : side c ≠ side d := fun h => hcd (same_color_unique G hfour side K S c d hc hd h)
  have hlargec := (Finset.mem_filter.mp hc).2.2
  have hlarged := (Finset.mem_filter.mp hd).2.2
  rw [leaf_of_color] at hlargec hlarged
  unfold Thick
  cases hsc : side c <;> cases hsd : side d <;> simp_all

lemma charge_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool) (K S : Finset (Fin n))
    (hthin : ¬ Thick side S) : (chargeSet G side K S).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro c hc d hd
  by_contra hcd
  exact hthin (two_charges_thick G hfour side K S c d hc hd hcd)

lemma pure_not_thick {n : ℕ} (side : Fin n → Bool) (S : Finset (Fin n))
    (hpure : Pure side S) : ¬ Thick side S := by
  obtain ⟨b, hb⟩ := hpure
  have hempty : colorPart side (!b) S = ∅ := by
    ext u
    simp only [colorPart, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro hu
    rw [hb u hu]
    cases b <;> simp
  intro hthick
  cases b
  · have hh := hthick.2
    have he : colorPart side true S = ∅ := by simpa using hempty
    rw [he] at hh
    simp at hh
  · have hh := hthick.1
    have he : colorPart side false S = ∅ := by simpa using hempty
    rw [he] at hh
    simp at hh

lemma pure_charge_contained {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (K S : Finset (Fin n)) (hpure : Pure side S)
    (c : Fin n) (hc : c ∈ chargeSet G side K S) : Contained G S := by
  obtain ⟨b, hb⟩ := hpure
  obtain ⟨_, hcn, hlarge⟩ := Finset.mem_filter.mp hc
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (leaf side c S).card by omega)
  obtain ⟨hwS, hws⟩ := Finset.mem_filter.mp hw
  have hbc : b ≠ side c := by simpa only [hb w hwS] using hws
  refine ⟨c, ?_⟩
  intro u hu
  have hleaf : u ∈ leaf side c S := Finset.mem_filter.mpr ⟨hu, by simpa only [hb u hu] using hbc⟩
  exact (Finset.mem_filter.mp (hcn hleaf)).2

lemma charge_zero_of_pure_uncontained {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (K S : Finset (Fin n))
    (hpure : Pure side S) (hno : ¬ Contained G S) : (chargeSet G side K S).card = 0 := by
  apply Finset.card_eq_zero.mpr
  ext c
  simp only [Finset.notMem_empty, iff_false]
  intro hc
  exact hno (pure_charge_contained G side K S hpure c hc)

lemma charge_zero_of_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (K S : Finset (Fin n)) (hsmall : S.card ≤ 1) :
    (chargeSet G side K S).card = 0 := by
  apply Finset.card_eq_zero.mpr
  ext c
  simp only [Finset.notMem_empty, iff_false]
  intro hc
  have hlarge := (Finset.mem_filter.mp hc).2.2
  have hle : (leaf side c S).card ≤ S.card := Finset.card_filter_le _ _
  omega

lemma projected_source_budget {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (s : ℕ → Finset (Fin n)) (a b : ℕ → ℕ)
    (K : Finset (Fin n)) (T : Fin n → Finset ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (hstep : ∀ k < m, s (n + k) = s (a k) ∪ s (b k) ∨ s (n + k) = ∅)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + m))
    (hTN : ∀ c ∈ K, ∀ w ∈ T c, ∀ u ∈ leaf side c (s w), G.Adj c u) :
    (∑ c ∈ K, ((T c).biUnion (fun w => leaf side c (s w))).card) ≤
      (∑ k ∈ Finset.range m, (chargeSet G side K (s (n + k))).card) +
        ∑ c ∈ K, (T c).card := by
  classical
  let pool : Fin n → Finset ℕ := fun c => (Finset.range m).filter fun k =>
    leaf side c (s (n + k)) ⊆ Finset.univ.filter (fun u => G.Adj c u) ∧
      2 ≤ (leaf side c (s (n + k))).card
  have hbound : ∀ c ∈ K, ((T c).biUnion (fun w => leaf side c (s w))).card ≤
      (pool c).card + (T c).card := by
    intro c hc
    apply MultiRoot.neighborhood_budget n m (fun w => leaf side c (s w)) a b
      (Finset.univ.filter fun u => G.Adj c u)
    · intro i hi
      exact (Finset.card_filter_le _ _).trans (hinput i hi)
    · exact ha
    · exact hb
    · intro k hk
      rcases hstep k hk with hu | he
      · left
        simp only [leaf, hu, Finset.filter_union]
      · right
        simp [leaf, he]
    · exact hT c hc
    · intro w hw u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTN c hc w hw u hu⟩
  have hsum : (∑ c ∈ K, (pool c).card) =
      ∑ k ∈ Finset.range m, (chargeSet G side K (s (n + k))).card := by
    calc
      (∑ c ∈ K, (pool c).card) = ∑ c ∈ K, ∑ k ∈ Finset.range m,
          if leaf side c (s (n + k)) ⊆ Finset.univ.filter (fun u => G.Adj c u) ∧
            2 ≤ (leaf side c (s (n + k))).card then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        simp only [Finset.sum_boole, pool]
        rfl
      _ = ∑ k ∈ Finset.range m, ∑ c ∈ K,
          if leaf side c (s (n + k)) ⊆ Finset.univ.filter (fun u => G.Adj c u) ∧
            2 ≤ (leaf side c (s (n + k))).card then 1 else 0 := by rw [Finset.sum_comm]
      _ = ∑ k ∈ Finset.range m, (chargeSet G side K (s (n + k))).card := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.sum_boole, chargeSet]
        rfl
  have hs := Finset.sum_le_sum (s := K) hbound
  rw [Finset.sum_add_distrib, hsum] at hs
  exact hs

lemma charge_card_le_one_of_contained {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool) (K S : Finset (Fin n))
    (hcontained : Contained G S) : (chargeSet G side K S).card ≤ 1 := by
  obtain ⟨d, hd⟩ := hcontained
  have heq : ∀ c ∈ chargeSet G side K S, c = d := by
    intro c hc
    by_contra hcd
    obtain ⟨_, hcn, hlarge⟩ := Finset.mem_filter.mp hc
    have hsub : leaf side c S ⊆ Finset.univ.filter (fun u => G.Adj c u ∧ G.Adj d u) := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (hcn hu)).2,
        hd u (Finset.mem_filter.mp hu).1⟩
    have hs := Finset.card_le_card hsub
    have hh := hfour c d hcd
    omega
  apply Finset.card_le_one.mpr
  intro c hc e he
  exact (heq c hc).trans (heq e he).symm

lemma circuit_projected_source_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (K : Finset (Fin n)) (T : Fin n → Finset ℕ)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + C.size))
    (hTN : ∀ c ∈ K, ∀ w ∈ T c, ∀ u ∈ leaf side c (PEqualNP.TopForm.orIn n C w), G.Adj c u) :
    (∑ c ∈ K, ((T c).biUnion (fun w => leaf side c (PEqualNP.TopForm.orIn n C w))).card) ≤
      (∑ k ∈ Finset.range C.gates.length,
        (chargeSet G side K (PEqualNP.TopForm.orIn n C (n + k))).card) + ∑ c ∈ K, (T c).card := by
  exact projected_source_budget G side (PEqualNP.TopForm.orIn n C)
    (fun k => PEqualNP.TopForm.opnd C k 0) (fun k => PEqualNP.TopForm.opnd C k 1) K T
    (RawOrSupport.orIn_input C)
    (fun k hk => RawOrSupport.opnd_lt hAO.2.2 hAO.2.1 hk 0)
    (fun k hk => RawOrSupport.opnd_lt hAO.2.2 hAO.2.1 hk 1)
    (RawOrSupport.orIn_binary hAO) hT hTN

end CProjectionCharges

namespace StarClauseSelector

open PEqualNP.MetaComplexity.NestedCover
open StarThreeClause

def Near {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (a : Fin n) (S : Finset (Fin n)) : Prop :=
  (∀ u ∈ S, side u ≠ side a) ∧ (S.filter (fun u => ¬ G.Adj a u)).card ≤ 1

def Thin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (a : Fin n) (S : Finset (Fin n)) : Prop :=
  (∀ u ∈ S, side u ≠ side a → G.Adj a u) ∧
    (S.filter (fun u => side u = side a)).card ≤ 1

lemma one_pure_clause {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (a : Fin n) (B C : Finset (Fin n))
    (hsafe : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true) :
    (∀ b ∈ B, side b ≠ side a) ∨ (∀ c ∈ C, side c ≠ side a) := by
  classical
  by_cases hb : ∀ b ∈ B, side b ≠ side a
  · exact Or.inl hb
  push Not at hb
  obtain ⟨b, hb, hba⟩ := hb
  right
  intro c hc hca
  rcases triple_safety G a B C hsafe b c hb hc with h | h | h
  · exact hproper a b h hba.symm
  · exact hproper a c h hca.symm
  · exact hproper b c h (hba.trans hca.symm)

lemma oriented_selector {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (hfour : PEqualNP.TopForm.NoFourCycle G) (a : Fin n) (B C : Finset (Fin n))
    (hsafe : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true)
    (hpure : ∀ b ∈ B, side b ≠ side a) :
    ∃ D E : Finset (Fin n), (D = B ∨ D = C) ∧ (E = B ∨ E = C) ∧
      (Near G side a D ∨ Thin G side a D) ∧
      (∀ u ∈ E, side u ≠ side a → G.Adj a u) := by
  classical
  by_cases hclean : ∀ b ∈ B, G.Adj a b
  · refine ⟨B, B, Or.inl rfl, Or.inl rfl, Or.inl ⟨hpure, ?_⟩, ?_⟩
    · have he : B.filter (fun u => ¬ G.Adj a u) = ∅ := by
        ext u
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hu
        exact not_not.mpr (hclean u hu)
      simp [he]
    · intro u hu _
      exact hclean u hu
  push Not at hclean
  obtain ⟨z, hz, haz⟩ := hclean
  have hvalid : ∀ u ∈ C, side u ≠ side a → G.Adj a u := by
    intro u hu hua
    by_contra hau
    have hzu := outside_rectangle G a B C hsafe z hz u hu haz hau
    have hsame : side z = side u := by
      have hza := hpure z hz
      cases h1 : side z <;> cases h2 : side u <;> cases h3 : side a <;> simp_all
    exact hproper z u hzu hsame
  by_cases hthin : (C.filter (fun u => side u = side a)).card ≤ 1
  · exact ⟨C, C, Or.inr rfl, Or.inr rfl, Or.inr ⟨hvalid, hthin⟩, hvalid⟩
  have hnot : ¬ (C.filter (fun u => ¬ G.Adj a u)).card ≤ 1 := by
    intro h
    apply hthin
    apply (Finset.card_le_card ?_).trans h
    intro u hu
    obtain ⟨hu, hua⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨hu, fun hau => hproper a u hau hua.symm⟩
  have hnear := (outside_small G hfour a B C hsafe).resolve_right hnot
  exact ⟨B, C, Or.inl rfl, Or.inr rfl, Or.inl ⟨hpure, hnear⟩, hvalid⟩

lemma safe_clause_selector {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (hfour : PEqualNP.TopForm.NoFourCycle G) (a : Fin n) (B C : Finset (Fin n))
    (hsafe : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true) :
    ∃ D E : Finset (Fin n), (D = B ∨ D = C) ∧ (E = B ∨ E = C) ∧
      (Near G side a D ∨ Thin G side a D) ∧
      (∀ u ∈ E, side u ≠ side a → G.Adj a u) ∧
      B ∩ C ⊆ D.filter (fun u => G.Adj a u) ∧
      B ∩ C ⊆ E.filter (fun u => G.Adj a u) := by
  classical
  have hex : ∃ D E : Finset (Fin n), (D = B ∨ D = C) ∧ (E = B ∨ E = C) ∧
      (Near G side a D ∨ Thin G side a D) ∧
      (∀ u ∈ E, side u ≠ side a → G.Adj a u) := by
    rcases one_pure_clause G side hproper a B C hsafe with hb | hc
    · exact oriented_selector G side hproper hfour a B C hsafe hb
    · have hs : ∀ x, starCNF a C B x = true → graphFun G ∅ x = true := by
        intro x hx
        apply hsafe x
        simpa only [starCNF, Bool.and_comm (clause B x) (clause C x)] using hx
      obtain ⟨D, E, hD, hE, hnear, hvalid⟩ :=
        oriented_selector G side hproper hfour a C B hs hc
      exact ⟨D, E, hD.symm, hE.symm, hnear, hvalid⟩
  obtain ⟨D, E, hD, hE, hnear, hvalid⟩ := hex
  refine ⟨D, E, hD, hE, hnear, hvalid, ?_, ?_⟩
  · intro u hu
    refine Finset.mem_filter.mpr ⟨?_, safe_intersection_neighbors G a B C hsafe u hu⟩
    rcases hD with rfl | rfl
    · exact (Finset.mem_inter.mp hu).1
    · exact (Finset.mem_inter.mp hu).2
  · intro u hu
    refine Finset.mem_filter.mpr ⟨?_, safe_intersection_neighbors G a B C hsafe u hu⟩
    rcases hE with rfl | rfl
    · exact (Finset.mem_inter.mp hu).1
    · exact (Finset.mem_inter.mp hu).2

lemma safe_clause_selector_for_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (hfour : PEqualNP.TopForm.NoFourCycle G) (a : Fin n) (B C : Finset (Fin n))
    (hsafe : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true) :
    ∃ D E : Finset (Fin n), (D = B ∨ D = C) ∧ (E = B ∨ E = C) ∧
      NearColorCases.BAllowed G side a D ∧
      (∀ u ∈ CProjectionCharges.leaf side a E, G.Adj a u) ∧
      B ∩ C ⊆ NearMergeCharges.project G a D ∧
      B ∩ C ⊆ CProjectionCharges.leaf side a E := by
  obtain ⟨D, E, hD, hE, hallowed, hvalid, hBD, hBE⟩ :=
    safe_clause_selector G side hproper hfour a B C hsafe
  refine ⟨D, E, hD, hE, hallowed, ?_, hBD, ?_⟩
  · intro u hu
    exact hvalid u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2
  · intro u hu
    obtain ⟨huE, hau⟩ := Finset.mem_filter.mp (hBE hu)
    exact Finset.mem_filter.mpr ⟨huE, Ne.symm (hproper a u hau)⟩

end StarClauseSelector

namespace ComplementaryBudget

lemma pure_iff_pairwise {n : ℕ} (side : Fin n → Bool) (S : Finset (Fin n)) :
    CProjectionCharges.Pure side S ↔ ∀ u ∈ S, ∀ v ∈ S, side u = side v := by
  constructor
  · rintro ⟨b, hb⟩ u hu v hv
    exact (hb u hu).trans (hb v hv).symm
  · intro h
    by_cases hn : S.Nonempty
    · obtain ⟨u, hu⟩ := hn
      exact ⟨side u, fun v hv => h v hv u hu⟩
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      exact ⟨false, by simp [he]⟩

lemma complementary_charge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v) (K A B : Finset (Fin n)) :
    (NearColorCases.chargeSet G side K A B).card +
      (CProjectionCharges.chargeSet G side K (A ∪ B)).card ≤ 2 := by
  classical
  by_cases hcontained : CProjectionCharges.Contained G (A ∪ B)
  · obtain ⟨d, hd⟩ := hcontained
    have hb := NearColorCases.charge_card_contained G hfour side K A B d hd
    have hc := CProjectionCharges.charge_card_le_one_of_contained G hfour side K (A ∪ B) ⟨d, hd⟩
    omega
  by_cases hpure : CProjectionCharges.Pure side (A ∪ B)
  · have hb := NearColorCases.charge_card_pure G hfour side hproper K A B
      ((pure_iff_pairwise side (A ∪ B)).mp hpure)
    have hc := CProjectionCharges.charge_zero_of_pure_uncontained G side K (A ∪ B) hpure hcontained
    omega
  have hmixed : ¬ ∀ u ∈ A ∪ B, ∀ v ∈ A ∪ B, side u = side v :=
    fun h => hpure ((pure_iff_pairwise side (A ∪ B)).mpr h)
  by_cases hthick : CProjectionCharges.Thick side (A ∪ B)
  · have hb := NearColorCases.charge_card_both_large G side K A B hthick.1 hthick.2
    have hc := CProjectionCharges.charge_card_le_two G hfour side K (A ∪ B)
    omega
  · have hb := NearColorCases.charge_card_mixed G hfour side hproper K A B hmixed
    have hc := CProjectionCharges.charge_card_le_one G hfour side K (A ∪ B) hthick
    omega

lemma node_charge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v) (K S A B : Finset (Fin n))
    (hstep : S = A ∪ B ∨ S = ∅) :
    (NearProjectionBudget.mergeChargeSet G (NearColorCases.BAllowed G side) K S A B).card +
      (CProjectionCharges.chargeSet G side K S).card ≤ if 2 ≤ S.card then 2 else 0 := by
  classical
  rcases hstep with rfl | rfl
  · have hsub : NearProjectionBudget.mergeChargeSet G (NearColorCases.BAllowed G side) K (A ∪ B) A B ⊆
        NearColorCases.chargeSet G side K A B := by
      intro c hc
      obtain ⟨hc, _, hallowed, hcharge⟩ := Finset.mem_filter.mp hc
      exact Finset.mem_filter.mpr ⟨hc, hallowed, hcharge⟩
    have hb := Finset.card_le_card hsub
    by_cases hlarge : 2 ≤ (A ∪ B).card
    · rw [ite_eq_left hlarge]
      have hh := complementary_charge_bound G hfour side hproper K A B
      omega
    · rw [ite_eq_right hlarge]
      have hsmall : (A ∪ B).card ≤ 1 := by omega
      have hB := NearColorCases.charge_card_small G side K A B hsmall
      have hC := CProjectionCharges.charge_zero_of_small G side K (A ∪ B) hsmall
      omega
  · have hb : NearProjectionBudget.mergeChargeSet G (NearColorCases.BAllowed G side) K ∅ A B = ∅ := by
      ext c
      simp [NearProjectionBudget.mergeChargeSet]
    have hc := CProjectionCharges.charge_zero_of_small G side K ∅ (by simp)
    simp [hb, hc]

lemma two_source_budget {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (s : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (K : Finset (Fin n)) (T U : Fin n → Finset ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (hstep : ∀ k < m, s (n + k) = s (a k) ∪ s (b k) ∨ s (n + k) = ∅)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + m))
    (hU : ∀ c ∈ K, U c ⊆ Finset.range (n + m))
    (hallowed : ∀ c ∈ K, ∀ w ∈ T c, NearColorCases.BAllowed G side c (s w))
    (hvalid : ∀ c ∈ K, ∀ w ∈ U c, ∀ v ∈ CProjectionCharges.leaf side c (s w), G.Adj c v)
    (X budget : ℕ)
    (hXb : X ≤ ∑ c ∈ K, ((T c).biUnion (fun w => NearMergeCharges.project G c (s w))).card)
    (hXc : X ≤ ∑ c ∈ K, ((U c).biUnion (fun w => CProjectionCharges.leaf side c (s w))).card)
    (hroots : (∑ c ∈ K, (T c).card) + (∑ c ∈ K, (U c).card) ≤ 2 * budget) :
    X ≤ ((Finset.range m).filter (fun k => 2 ≤ (s (n + k)).card)).card + budget := by
  classical
  let costB : ℕ → ℕ := fun k => (NearProjectionBudget.mergeChargeSet G
    (NearColorCases.BAllowed G side) K (s (n + k)) (s (a k)) (s (b k))).card
  let costC : ℕ → ℕ := fun k => (CProjectionCharges.chargeSet G side K (s (n + k))).card
  have hB := NearProjectionBudget.filtered_projection_budget G (NearColorCases.BAllowed G side)
    (NearColorCases.allowed_mono G side) s a b K T hinput ha hb hstep hT hallowed
  have hC := CProjectionCharges.projected_source_budget G side s a b K U hinput ha hb hstep hU hvalid
  change _ ≤ (Finset.range m).sum costB + _ at hB
  change _ ≤ (Finset.range m).sum costC + _ at hC
  have hcost : (Finset.range m).sum costB + (Finset.range m).sum costC ≤
      2 * ((Finset.range m).filter (fun k => 2 ≤ (s (n + k)).card)).card := by
    have hh : (∑ k ∈ Finset.range m, (costB k + costC k)) ≤
        ∑ k ∈ Finset.range m, if 2 ≤ (s (n + k)).card then 2 else 0 := by
      apply Finset.sum_le_sum
      intro k hk
      exact node_charge_bound G hfour side hproper K (s (n + k)) (s (a k)) (s (b k))
        (hstep k (Finset.mem_range.mp hk))
    rw [Finset.sum_add_distrib] at hh
    have heq : (∑ k ∈ Finset.range m, if 2 ≤ (s (n + k)).card then 2 else 0) =
        2 * ((Finset.range m).filter (fun k => 2 ≤ (s (n + k)).card)).card := by
      calc
        (∑ k ∈ Finset.range m, if 2 ≤ (s (n + k)).card then 2 else 0) =
            ∑ k ∈ Finset.range m, 2 * (if 2 ≤ (s (n + k)).card then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro k hk
          split_ifs <;> rfl
        _ = 2 * ∑ k ∈ Finset.range m, (if 2 ≤ (s (n + k)).card then 1 else 0) := by
          rw [Finset.mul_sum]
        _ = 2 * ((Finset.range m).filter (fun k => 2 ≤ (s (n + k)).card)).card := by
          simp only [Finset.sum_boole]
          rfl
    exact hh.trans_eq heq
  omega

lemma circuit_two_source_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (K : Finset (Fin n)) (T U : Fin n → Finset ℕ)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + C.size))
    (hU : ∀ c ∈ K, U c ⊆ Finset.range (n + C.size))
    (hallowed : ∀ c ∈ K, ∀ w ∈ T c, NearColorCases.BAllowed G side c (PEqualNP.TopForm.orIn n C w))
    (hvalid : ∀ c ∈ K, ∀ w ∈ U c,
      ∀ v ∈ CProjectionCharges.leaf side c (PEqualNP.TopForm.orIn n C w), G.Adj c v)
    (X budget : ℕ)
    (hXb : X ≤ ∑ c ∈ K, ((T c).biUnion
      (fun w => NearMergeCharges.project G c (PEqualNP.TopForm.orIn n C w))).card)
    (hXc : X ≤ ∑ c ∈ K, ((U c).biUnion
      (fun w => CProjectionCharges.leaf side c (PEqualNP.TopForm.orIn n C w))).card)
    (hroots : (∑ c ∈ K, (T c).card) + (∑ c ∈ K, (U c).card) ≤ 2 * budget) :
    X ≤ ((Finset.range C.gates.length).filter (fun k =>
      2 ≤ (PEqualNP.TopForm.orIn n C (n + k)).card)).card + budget := by
  exact two_source_budget G hfour side hproper (PEqualNP.TopForm.orIn n C)
    (fun k => PEqualNP.TopForm.opnd C k 0) (fun k => PEqualNP.TopForm.opnd C k 1) K T U
    (RawOrSupport.orIn_input C)
    (fun k hk => RawOrSupport.opnd_lt hAO.2.2 hAO.2.1 hk 0)
    (fun k hk => RawOrSupport.opnd_lt hAO.2.2 hAO.2.1 hk 1)
    (RawOrSupport.orIn_binary hAO) hT hU hallowed hvalid X budget hXb hXc hroots

end ComplementaryBudget

namespace ComplementaryFamily

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma shared_family_cover_of_budget {n p l : ℕ}
    (C : Circuit)
    (M O : Finset ℕ)
    (hM : ∀ k ∈ M, k < C.gates.length ∧ (gateAt C k).op = GateOp.and)
    (hO : ∀ k ∈ O, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      orIn n C (n + k) = ∅)
    (E EL ER F : Finset (Fin p × Fin l)) (L ZL : Finset (Fin p)) (R ZR : Finset (Fin l))
    (r s t : ℕ) (hcover : EL ∪ ER = E) (hfl : F ⊆ EL) (hfr : F ⊆ ER)
    (hlcover : L ⊆ F.image Prod.fst ∪ ZL) (hrcover : R ⊆ F.image Prod.snd ∪ ZR)
    (hr : F.card ≤ r) (ht : ZL.card + ZR.card ≤ s + t)
    (hleft : ∀ e ∈ EL, e.1 ∈ L) (hright : ∀ e ∈ ER, e.2 ∈ R)
    (hbudget : EL.card + ER.card ≤
      ((Finset.range C.gates.length).filter fun k => 2 ≤ (orIn n C (n + k)).card).card +
        2 * r + s + t)
    (hands : 2 * r + 2 * s + t ≤ M.card) (haggregation : r + s + t ≤ O.card + 1) :
    (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card + s ≤ C.size + 1 := by
  constructor
  · intro e he
    have he' : e ∈ EL ∪ ER := hcover.symm ▸ he
    exact (Finset.mem_union.mp he').elim (fun h => Or.inl (hleft e h))
      (fun h => Or.inr (hright e h))
  · have hg := ThinFamily.nontrivial_gate_accounting C M O hM hO
    have hm := SharedThreeClauseLedger.edge_multiplicity E EL ER hcover
    have hc := SharedThreeClauseLedger.centre_budget EL ER F L ZL R ZR r (s + t)
      hfl hfr hlcover hrcover hr ht
    omega


lemma shared_family_cover_bound {n p l : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (hAO : IsAO2 n C) (K : Finset (Fin n)) (T U : Fin n → Finset ℕ)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + C.size))
    (hU : ∀ c ∈ K, U c ⊆ Finset.range (n + C.size))
    (hallowed : ∀ c ∈ K, ∀ w ∈ T c, NearColorCases.BAllowed G side c (orIn n C w))
    (hvalid : ∀ c ∈ K, ∀ w ∈ U c,
      ∀ v ∈ CProjectionCharges.leaf side c (orIn n C w), G.Adj c v)
    (M O : Finset ℕ)
    (hM : ∀ k ∈ M, k < C.gates.length ∧ (gateAt C k).op = GateOp.and)
    (hO : ∀ k ∈ O, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      orIn n C (n + k) = ∅)
    (E EL ER F : Finset (Fin p × Fin l)) (L ZL : Finset (Fin p)) (R ZR : Finset (Fin l))
    (r s t : ℕ) (hcover : EL ∪ ER = E) (hfl : F ⊆ EL) (hfr : F ⊆ ER)
    (hlcover : L ⊆ F.image Prod.fst ∪ ZL) (hrcover : R ⊆ F.image Prod.snd ∪ ZR)
    (hr : F.card ≤ r) (ht : ZL.card + ZR.card ≤ s + t)
    (hleft : ∀ e ∈ EL, e.1 ∈ L) (hright : ∀ e ∈ ER, e.2 ∈ R)
    (hleavesB : EL.card + ER.card ≤
      ∑ c ∈ K, ((T c).biUnion (fun w => NearMergeCharges.project G c (orIn n C w))).card)
    (hleavesC : EL.card + ER.card ≤
      ∑ c ∈ K, ((U c).biUnion (fun w => CProjectionCharges.leaf side c (orIn n C w))).card)
    (hroots : (∑ c ∈ K, (T c).card) + (∑ c ∈ K, (U c).card) ≤ 2 * (2 * r + s + t))
    (hands : 2 * r + 2 * s + t ≤ M.card) (haggregation : r + s + t ≤ O.card + 1) :
    (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card + s ≤ C.size + 1 := by
  have hb := ComplementaryBudget.circuit_two_source_budget G hfour side hproper C hAO K T U
    hT hU hallowed hvalid (EL.card + ER.card) (2 * r + s + t) hleavesB hleavesC hroots
  exact shared_family_cover_of_budget C M O hM hO E EL ER F L ZL R ZR r s t
    hcover hfl hfr hlcover hrcover hr ht hleft hright
      (by simpa only [Nat.add_assoc] using hb) hands haggregation

end ComplementaryFamily

namespace RelaxedFamily

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma shared_family_cover_of_budget_with_surplus {n p l : ℕ}
    (C : Circuit)
    (M O : Finset ℕ)
    (hM : ∀ k ∈ M, k < C.gates.length ∧ (gateAt C k).op = GateOp.and)
    (hO : ∀ k ∈ O, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      orIn n C (n + k) = ∅)
    (E EL ER F : Finset (Fin p × Fin l)) (L ZL : Finset (Fin p)) (R ZR : Finset (Fin l))
    (r s t surplus : ℕ) (hcover : EL ∪ ER = E) (hfl : F ⊆ EL) (hfr : F ⊆ ER)
    (hlcover : L ⊆ F.image Prod.fst ∪ ZL) (hrcover : R ⊆ F.image Prod.snd ∪ ZR)
    (hr : F.card ≤ r) (ht : ZL.card + ZR.card ≤ s + t)
    (hleft : ∀ e ∈ EL, e.1 ∈ L) (hright : ∀ e ∈ ER, e.2 ∈ R)
    (hbudget : EL.card + ER.card ≤
      ((Finset.range C.gates.length).filter fun k => 2 ≤ (orIn n C (n + k)).card).card +
        2 * r + s + t)
    (hands : 2 * r + s + t + surplus ≤ M.card) (haggregation : r + s + t ≤ O.card + 1) :
    (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card + surplus ≤ C.size + 1 := by
  constructor
  · intro e he
    have he' : e ∈ EL ∪ ER := hcover.symm ▸ he
    exact (Finset.mem_union.mp he').elim (fun h => Or.inl (hleft e h))
      (fun h => Or.inr (hright e h))
  · have hg := ThinFamily.nontrivial_gate_accounting C M O hM hO
    have hm := SharedThreeClauseLedger.edge_multiplicity E EL ER hcover
    have hc := SharedThreeClauseLedger.centre_budget EL ER F L ZL R ZR r (s + t)
      hfl hfr hlcover hrcover hr ht
    omega


lemma shared_family_cover_with_surplus {n p l : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (hAO : IsAO2 n C) (K : Finset (Fin n)) (T U : Fin n → Finset ℕ)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + C.size))
    (hU : ∀ c ∈ K, U c ⊆ Finset.range (n + C.size))
    (hallowed : ∀ c ∈ K, ∀ w ∈ T c, NearColorCases.BAllowed G side c (orIn n C w))
    (hvalid : ∀ c ∈ K, ∀ w ∈ U c,
      ∀ v ∈ CProjectionCharges.leaf side c (orIn n C w), G.Adj c v)
    (M O : Finset ℕ)
    (hM : ∀ k ∈ M, k < C.gates.length ∧ (gateAt C k).op = GateOp.and)
    (hO : ∀ k ∈ O, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      orIn n C (n + k) = ∅)
    (E EL ER F : Finset (Fin p × Fin l)) (L ZL : Finset (Fin p)) (R ZR : Finset (Fin l))
    (r s t surplus : ℕ) (hcover : EL ∪ ER = E) (hfl : F ⊆ EL) (hfr : F ⊆ ER)
    (hlcover : L ⊆ F.image Prod.fst ∪ ZL) (hrcover : R ⊆ F.image Prod.snd ∪ ZR)
    (hr : F.card ≤ r) (ht : ZL.card + ZR.card ≤ s + t)
    (hleft : ∀ e ∈ EL, e.1 ∈ L) (hright : ∀ e ∈ ER, e.2 ∈ R)
    (hleavesB : EL.card + ER.card ≤
      ∑ c ∈ K, ((T c).biUnion (fun w => NearMergeCharges.project G c (orIn n C w))).card)
    (hleavesC : EL.card + ER.card ≤
      ∑ c ∈ K, ((U c).biUnion (fun w => CProjectionCharges.leaf side c (orIn n C w))).card)
    (hroots : (∑ c ∈ K, (T c).card) + (∑ c ∈ K, (U c).card) ≤ 2 * (2 * r + s + t))
    (hands : 2 * r + s + t + surplus ≤ M.card) (haggregation : r + s + t ≤ O.card + 1) :
    (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card + surplus ≤ C.size + 1 := by
  have hb := ComplementaryBudget.circuit_two_source_budget G hfour side hproper C hAO K T U
    hT hU hallowed hvalid (EL.card + ER.card) (2 * r + s + t) hleavesB hleavesC hroots
  exact shared_family_cover_of_budget_with_surplus C M O hM hO E EL ER F L ZL R ZR r s t surplus
    hcover hfl hfr hlcover hrcover hr ht hleft hright
      (by simpa only [Nat.add_assoc] using hb) hands haggregation

end RelaxedFamily

namespace ResidualFamily

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma residual_family_cover_of_budget {n p l : ℕ}
    (C : Circuit)
    (M : Finset ℕ)
    (hM : ∀ k ∈ M, k < C.gates.length ∧ (gateAt C k).op = GateOp.and)
    (E EL ER F : Finset (Fin p × Fin l)) (L ZL : Finset (Fin p)) (R ZR : Finset (Fin l))
    (r s t : ℕ) (hcover : EL ∪ ER = E) (hfl : F ⊆ EL) (hfr : F ⊆ ER)
    (hlcover : L ⊆ F.image Prod.fst ∪ ZL) (hrcover : R ⊆ F.image Prod.snd ∪ ZR)
    (hr : F.card ≤ r) (ht : ZL.card + ZR.card ≤ s + t)
    (hleft : ∀ e ∈ EL, e.1 ∈ L) (hright : ∀ e ∈ ER, e.2 ∈ R)
    (hbudget : EL.card + ER.card ≤
      ((Finset.range C.gates.length).filter fun k => 2 ≤ (orIn n C (n + k)).card).card +
        2 * r + s + t)
    (hands : r ≤ M.card) :
    (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card ≤ C.size + 2 * (r + s + t) := by
  constructor
  · intro e he
    have he' : e ∈ EL ∪ ER := hcover.symm ▸ he
    exact (Finset.mem_union.mp he').elim (fun h => Or.inl (hleft e h))
      (fun h => Or.inr (hright e h))
  · have hg := ThinFamily.nontrivial_gate_accounting (n := n) C M ∅ hM (by simp)
    have hm := SharedThreeClauseLedger.edge_multiplicity E EL ER hcover
    have hc := SharedThreeClauseLedger.centre_budget EL ER F L ZL R ZR r (s + t)
      hfl hfr hlcover hrcover hr ht
    omega


lemma residual_family_cover_bound {n p l : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (hAO : IsAO2 n C) (K : Finset (Fin n)) (T U : Fin n → Finset ℕ)
    (hT : ∀ c ∈ K, T c ⊆ Finset.range (n + C.size))
    (hU : ∀ c ∈ K, U c ⊆ Finset.range (n + C.size))
    (hallowed : ∀ c ∈ K, ∀ w ∈ T c, NearColorCases.BAllowed G side c (orIn n C w))
    (hvalid : ∀ c ∈ K, ∀ w ∈ U c,
      ∀ v ∈ CProjectionCharges.leaf side c (orIn n C w), G.Adj c v)
    (M : Finset ℕ)
    (hM : ∀ k ∈ M, k < C.gates.length ∧ (gateAt C k).op = GateOp.and)
    (E EL ER F : Finset (Fin p × Fin l)) (L ZL : Finset (Fin p)) (R ZR : Finset (Fin l))
    (r s t : ℕ) (hcover : EL ∪ ER = E) (hfl : F ⊆ EL) (hfr : F ⊆ ER)
    (hlcover : L ⊆ F.image Prod.fst ∪ ZL) (hrcover : R ⊆ F.image Prod.snd ∪ ZR)
    (hr : F.card ≤ r) (ht : ZL.card + ZR.card ≤ s + t)
    (hleft : ∀ e ∈ EL, e.1 ∈ L) (hright : ∀ e ∈ ER, e.2 ∈ R)
    (hleavesB : EL.card + ER.card ≤
      ∑ c ∈ K, ((T c).biUnion (fun w => NearMergeCharges.project G c (orIn n C w))).card)
    (hleavesC : EL.card + ER.card ≤
      ∑ c ∈ K, ((U c).biUnion (fun w => CProjectionCharges.leaf side c (orIn n C w))).card)
    (hroots : (∑ c ∈ K, (T c).card) + (∑ c ∈ K, (U c).card) ≤ 2 * (2 * r + s + t))
    (hands : r ≤ M.card) :
    (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card ≤ C.size + 2 * (r + s + t) := by
  have hb := ComplementaryBudget.circuit_two_source_budget G hfour side hproper C hAO K T U
    hT hU hallowed hvalid (EL.card + ER.card) (2 * r + s + t) hleavesB hleavesC hroots
  exact residual_family_cover_of_budget C M hM E EL ER F L ZL R ZR r s t
    hcover hfl hfr hlcover hrcover hr ht hleft hright
      (by simpa only [Nat.add_assoc] using hb) hands

end ResidualFamily

namespace StarRootFamily

def indexFiber {n m : ℕ} (a : Fin m → Fin n) (v : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun i => a i = v

def rootPool {n m : ℕ} (a : Fin m → Fin n) (d : Fin m → ℕ) (v : Fin n) : Finset ℕ :=
  (indexFiber a v).image d

lemma root_pool_mem {n m : ℕ} (a : Fin m → Fin n) (d : Fin m → ℕ) (v : Fin n) (w : ℕ) :
    w ∈ rootPool a d v ↔ ∃ i : Fin m, a i = v ∧ d i = w := by
  simp only [rootPool, indexFiber, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

lemma index_fiber_card_sum {n m : ℕ} (a : Fin m → Fin n) :
    (∑ v : Fin n, (indexFiber a v).card) = m := by
  have hd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint (indexFiber a) := by
    intro v hv u hu hvu
    apply Finset.disjoint_left.mpr
    intro i hiv hiu
    exact hvu ((Finset.mem_filter.mp hiv).2.symm.trans (Finset.mem_filter.mp hiu).2)
  have he : (Finset.univ : Finset (Fin n)).biUnion (indexFiber a) = Finset.univ := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_univ i
    · intro hi
      exact Finset.mem_biUnion.mpr ⟨a i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hc := Finset.card_biUnion hd
  rw [he, Finset.card_univ, Fintype.card_fin] at hc
  exact hc.symm

lemma root_pool_card_bound {n m : ℕ} (a : Fin m → Fin n) (d : Fin m → ℕ) :
    (∑ v : Fin n, (rootPool a d v).card) ≤ m := by
  calc
    (∑ v : Fin n, (rootPool a d v).card) ≤ ∑ v : Fin n, (indexFiber a v).card := by
      apply Finset.sum_le_sum
      intro v hv
      exact Finset.card_image_le
    _ = m := index_fiber_card_sum a



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def centerLeaves {n m : ℕ} (C : Circuit) (a : Fin m → Fin n) (b c : Fin m → ℕ)
    (v : Fin n) : Finset (Fin n) :=
  (indexFiber a v).biUnion fun i => orIn n C (b i) ∩ orIn n C (c i)

lemma select_source_wires {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (a : Fin n) (b c : ℕ)
    (hsafe : ∀ x, StarThreeClause.starCNF a (orIn n C b) (orIn n C c) x = true →
      graphFun G ∅ x = true) :
    ∃ d e : ℕ, (d = b ∨ d = c) ∧ (e = b ∨ e = c) ∧
      NearColorCases.BAllowed G side a (orIn n C d) ∧
      (∀ u ∈ CProjectionCharges.leaf side a (orIn n C e), G.Adj a u) ∧
      orIn n C b ∩ orIn n C c ⊆ NearMergeCharges.project G a (orIn n C d) ∧
      orIn n C b ∩ orIn n C c ⊆ CProjectionCharges.leaf side a (orIn n C e) := by
  obtain ⟨D, E, hD, hE, hallowed, hvalid, hBD, hBE⟩ :=
    StarClauseSelector.safe_clause_selector_for_budget G side hproper hfour a
      (orIn n C b) (orIn n C c) hsafe
  rcases hD with rfl | rfl <;> rcases hE with rfl | rfl
  · exact ⟨b, b, Or.inl rfl, Or.inl rfl, hallowed, hvalid, hBD, hBE⟩
  · exact ⟨b, c, Or.inl rfl, Or.inr rfl, hallowed, hvalid, hBD, hBE⟩
  · exact ⟨c, b, Or.inr rfl, Or.inl rfl, hallowed, hvalid, hBD, hBE⟩
  · exact ⟨c, c, Or.inr rfl, Or.inr rfl, hallowed, hvalid, hBD, hBE⟩

lemma select_source_family {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (a : Fin m → Fin n) (b c : Fin m → ℕ)
    (hb : ∀ i, b i < n + C.size) (hc : ∀ i, c i < n + C.size)
    (hsafe : ∀ i x, StarThreeClause.starCNF (a i) (orIn n C (b i)) (orIn n C (c i)) x = true →
      graphFun G ∅ x = true) :
    ∃ T U : Fin n → Finset ℕ,
      (∀ v, T v ⊆ Finset.range (n + C.size)) ∧
      (∀ v, U v ⊆ Finset.range (n + C.size)) ∧
      (∀ v, ∀ w ∈ T v, NearColorCases.BAllowed G side v (orIn n C w)) ∧
      (∀ v, ∀ w ∈ U v, ∀ u ∈ CProjectionCharges.leaf side v (orIn n C w), G.Adj v u) ∧
      (∀ v, centerLeaves C a b c v ⊆
        (T v).biUnion (fun w => NearMergeCharges.project G v (orIn n C w))) ∧
      (∀ v, centerLeaves C a b c v ⊆
        (U v).biUnion (fun w => CProjectionCharges.leaf side v (orIn n C w))) ∧
      (∑ v : Fin n, (T v).card) ≤ m ∧ (∑ v : Fin n, (U v).card) ≤ m := by
  classical
  have hselect := fun i => select_source_wires G hfour side hproper C (a i) (b i) (c i) (hsafe i)
  choose d e hd he hallowed hvalid hcovB hcovC using hselect
  let T := rootPool a d
  let U := rootPool a e
  refine ⟨T, U, ?_, ?_, ?_, ?_, ?_, ?_, root_pool_card_bound a d, root_pool_card_bound a e⟩
  · intro v w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_range.mpr
    rcases hd i with hdi | hdi
    · rw [hdi]
      exact hb i
    · rw [hdi]
      exact hc i
  · intro v w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_range.mpr
    rcases he i with hei | hei
    · rw [hei]
      exact hb i
    · rw [hei]
      exact hc i
  · intro v w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have hiv := (Finset.mem_filter.mp hi).2
    rw [← hiv]
    exact hallowed i
  · intro v w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have hiv := (Finset.mem_filter.mp hi).2
    rw [← hiv]
    exact hvalid i
  · intro v u hu
    obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp hu
    have hiv := (Finset.mem_filter.mp hi).2
    have hp := hcovB i hui
    rw [hiv] at hp
    exact Finset.mem_biUnion.mpr ⟨d i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hp⟩
  · intro v u hu
    obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp hu
    have hiv := (Finset.mem_filter.mp hi).2
    have hp := hcovC i hui
    rw [hiv] at hp
    exact Finset.mem_biUnion.mpr ⟨e i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hp⟩

lemma shared_star_clause_budget {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (hAO : IsAO2 n C) (a : Fin m → Fin n) (b c : Fin m → ℕ)
    (hb : ∀ i, b i < n + C.size) (hc : ∀ i, c i < n + C.size)
    (hsafe : ∀ i x, StarThreeClause.starCNF (a i) (orIn n C (b i)) (orIn n C (c i)) x = true →
      graphFun G ∅ x = true) :
    (∑ v : Fin n, (centerLeaves C a b c v).card) ≤
      ((Finset.range C.gates.length).filter fun k => 2 ≤ (orIn n C (n + k)).card).card + m := by
  obtain ⟨T, U, hT, hU, hallowed, hvalid, hcovB, hcovC, hrootsB, hrootsC⟩ :=
    select_source_family G hfour side hproper C a b c hb hc hsafe
  apply ComplementaryBudget.circuit_two_source_budget G hfour side hproper C hAO Finset.univ T U
    (fun v _ => hT v) (fun v _ => hU v) (fun v _ => hallowed v) (fun v _ => hvalid v)
    (∑ v : Fin n, (centerLeaves C a b c v).card) m
  · apply Finset.sum_le_sum
    intro v hv
    exact Finset.card_le_card (hcovB v)
  · apply Finset.sum_le_sum
    intro v hv
    exact Finset.card_le_card (hcovC v)
  · omega

lemma mem_centerLeaves_iff_accepted_pair {n m : ℕ}
    (C : Circuit) (a : Fin m → Fin n) (b c : Fin m → ℕ)
    (hab : ∀ i, a i ∉ orIn n C (b i)) (hac : ∀ i, a i ∉ orIn n C (c i))
    (v u : Fin n) :
    u ∈ centerLeaves C a b c v ↔ ∃ i : Fin m, a i = v ∧
      StarThreeClause.starCNF (a i) (orIn n C (b i)) (orIn n C (c i))
        (fun w => decide (w = a i ∨ w = u)) = true := by
  constructor
  · intro hu
    obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp hu
    refine ⟨i, (Finset.mem_filter.mp hi).2, ?_⟩
    exact (StarThreeClause.accepted_pair_iff (a i) u (orIn n C (b i)) (orIn n C (c i))
      (hab i) (hac i)).mpr hui
  · rintro ⟨i, hiv, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiv⟩,
      (StarThreeClause.accepted_pair_iff (a i) u (orIn n C (b i)) (orIn n C (c i))
        (hab i) (hac i)).mp hi⟩

end StarRootFamily

namespace SharedBottomStar

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm StarThreeClause

def groupFun {n : ℕ} (X B C : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  clause X x && (clause B x && clause C x)

def replacement {n : ℕ} (X B C : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  clause X x && clause (B ∩ C) x

lemma group_true {n : ℕ} (X B C : Finset (Fin n)) (x : Fin n → Bool) :
    groupFun X B C x = true ↔
      (∃ a ∈ X, x a = true) ∧ (∃ b ∈ B, x b = true) ∧ (∃ c ∈ C, x c = true) := by
  simp [groupFun, clause]

lemma replacement_true {n : ℕ} (X B C : Finset (Fin n)) (x : Fin n → Bool) :
    replacement X B C x = true ↔ (∃ a ∈ X, x a = true) ∧ (∃ s ∈ B ∩ C, x s = true) := by
  simp [replacement, clause]

lemma replacement_le_group {n : ℕ} (X B C : Finset (Fin n)) :
    ∀ x, replacement X B C x = true → groupFun X B C x = true := by
  intro x hx
  obtain ⟨ha, s, hs, hxs⟩ := (replacement_true X B C x).mp hx
  obtain ⟨hsB, hsC⟩ := Finset.mem_inter.mp hs
  exact (group_true X B C x).mpr ⟨ha, ⟨s, hsB, hxs⟩, ⟨s, hsC, hxs⟩⟩

lemma replacement_monotone {n : ℕ} (X B C : Finset (Fin n)) :
    ∀ x y : Fin n → Bool, (∀ u, x u = true → y u = true) →
      replacement X B C x = true → replacement X B C y = true := by
  intro x y hxy hx
  obtain ⟨⟨a, ha, hxa⟩, ⟨s, hs, hxs⟩⟩ := (replacement_true X B C x).mp hx
  exact (replacement_true X B C y).mpr ⟨⟨a, ha, hxy a hxa⟩, ⟨s, hs, hxy s hxs⟩⟩

lemma group_pair_iff {n : ℕ} (X B C : Finset (Fin n))
    (haway : ∀ a ∈ X, a ∉ B ∧ a ∉ C) (u v : Fin n) :
    groupFun X B C (pairInput u v) = true ↔
      (u ∈ X ∧ v ∈ B ∩ C) ∨ (v ∈ X ∧ u ∈ B ∩ C) := by
  constructor
  · intro h
    obtain ⟨⟨a, ha, hxa⟩, hB, hC⟩ := (group_true X B C (pairInput u v)).mp h
    have hav : a = u ∨ a = v := by simpa [pairInput] using hxa
    have hb : clause B (pairInput u v) = true := decide_eq_true hB
    have hc : clause C (pairInput u v) = true := decide_eq_true hC
    rcases hav with hau | hav
    · subst a
      left
      refine ⟨ha, ?_⟩
      apply (accepted_pair_iff u v B C (haway u ha).1 (haway u ha).2).mp
      change starCNF u B C (pairInput u v) = true
      rw [starCNF, hb, hc]
      simp [pairInput]
    · subst a
      right
      refine ⟨ha, ?_⟩
      have heq : pairInput u v = pairInput v u := by
        funext w
        simp only [pairInput, or_comm]
      rw [heq] at hb hc
      apply (accepted_pair_iff v u B C (haway v ha).1 (haway v ha).2).mp
      change starCNF v B C (pairInput v u) = true
      rw [starCNF, hb, hc]
      simp [pairInput]
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · obtain ⟨hvB, hvC⟩ := Finset.mem_inter.mp hv
      exact (group_true X B C (pairInput u v)).mpr
        ⟨⟨u, hu, by simp [pairInput]⟩, ⟨v, hvB, by simp [pairInput]⟩, ⟨v, hvC, by simp [pairInput]⟩⟩
    · obtain ⟨huB, huC⟩ := Finset.mem_inter.mp hu
      exact (group_true X B C (pairInput u v)).mpr
        ⟨⟨v, hv, by simp [pairInput]⟩, ⟨u, huB, by simp [pairInput]⟩, ⟨u, huC, by simp [pairInput]⟩⟩

lemma replacement_preserves_pairs {n : ℕ} (X B C : Finset (Fin n))
    (haway : ∀ a ∈ X, a ∉ B ∧ a ∉ C) (u v : Fin n) :
    groupFun X B C (pairInput u v) = true ↔ replacement X B C (pairInput u v) = true := by
  constructor
  · intro h
    rcases (group_pair_iff X B C haway u v).mp h with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact (replacement_true X B C (pairInput u v)).mpr
        ⟨⟨u, hu, by simp [pairInput]⟩, ⟨v, hv, by simp [pairInput]⟩⟩
    · exact (replacement_true X B C (pairInput u v)).mpr
        ⟨⟨v, hv, by simp [pairInput]⟩, ⟨u, hu, by simp [pairInput]⟩⟩
  · exact replacement_le_group X B C (pairInput u v)

lemma safe_group_biclique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X B C : Finset (Fin n))
    (hsafe : ∀ a ∈ X, ∀ x, starCNF a B C x = true → graphFun G ∅ x = true) :
    ∀ a ∈ X, ∀ s ∈ B ∩ C, G.Adj a s := by
  intro a ha
  exact safe_intersection_neighbors G a B C (hsafe a ha)

lemma biclique_card_cases {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (X S : Finset (Fin n))
    (hXS : ∀ a ∈ X, ∀ s ∈ S, G.Adj a s) : X.card ≤ 1 ∨ S.card ≤ 1 := by
  by_cases hx : X.card ≤ 1
  · exact Or.inl hx
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < X.card by omega)
  right
  have hsub : S ⊆ Finset.univ.filter (fun s => G.Adj a s ∧ G.Adj b s) := by
    intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hXS a ha s hs, hXS b hb s hs⟩
  exact (Finset.card_le_card hsub).trans (hfour a b hab)

lemma shared_bottom_classification {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (X B C : Finset (Fin n))
    (hsafe : ∀ a ∈ X, ∀ x, starCNF a B C x = true → graphFun G ∅ x = true) :
    X.card ≤ 1 ∨ (B ∩ C).card ≤ 1 :=
  biclique_card_cases G hfour X (B ∩ C) (safe_group_biclique G X B C hsafe)

lemma multiple_leaves_unique_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (X B C : Finset (Fin n))
    (hsafe : ∀ a ∈ X, ∀ x, starCNF a B C x = true → graphFun G ∅ x = true)
    (hlarge : 2 ≤ (B ∩ C).card) : X.card ≤ 1 := by
  rcases shared_bottom_classification G hfour X B C hsafe with hx | hs
  · exact hx
  · omega

lemma singleton_replacement {n : ℕ} (X B C : Finset (Fin n)) (v : Fin n)
    (hS : B ∩ C = {v}) : ∀ x, replacement X B C x = (x v && clause X x) := by
  intro x
  simp [replacement, hS, clause, Bool.and_comm]

lemma distinct_centers_budget {n : ℕ} (X : Finset (Fin n)) (tops : Finset ℕ)
    (center : ℕ → Fin n) (hcovered : X ⊆ tops.image center) : X.card ≤ tops.card :=
  (Finset.card_le_card hcovered).trans Finset.card_image_le

lemma reverse_star_gate_budget {n : ℕ} (X : Finset (Fin n)) (tops : Finset ℕ)
    (center : ℕ → Fin n) (hcovered : X ⊆ tops.image center) (hX : X.Nonempty) :
    (X.card - 1) + 1 ≤ tops.card := by
  have hpos := Finset.card_pos.mpr hX
  have hbound := distinct_centers_budget X tops center hcovered
  omega

lemma replace_in_monotone_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X B C : Finset (Fin n)) (haway : ∀ a ∈ X, a ∉ B ∧ a ∉ C)
    (H : (Fin n → Bool) → Bool)
    (hmono : ∀ x y : Fin n → Bool, (∀ u, x u = true → y u = true) → H x = true → H y = true)
    (hfull : ∀ x, (H x || groupFun X B C x) = graphFun G ∅ x) :
    ∀ x, (H x || replacement X B C x) = graphFun G ∅ x := by
  intro x
  have hiff : (H x || replacement X B C x) = true ↔ graphFun G ∅ x = true := by
    constructor
    · intro hh
      have hh' : H x = true ∨ replacement X B C x = true := by simpa using hh
      have hold : H x = true ∨ groupFun X B C x = true :=
        hh'.elim Or.inl (fun h => Or.inr (replacement_le_group X B C x h))
      rw [← hfull x]
      simpa using hold
    · intro hF
      have hedge : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
        simpa [graphFun] using hF
      obtain ⟨u, v, huv, hxu, hxv⟩ := hedge
      have hpair : graphFun G ∅ (pairInput u v) = true := by
        have he : ∃ a b, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true :=
          ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
        simpa [graphFun] using he
      have hle : ∀ w, pairInput u v w = true → x w = true := by
        intro w hw
        have hw' : w = u ∨ w = v := by simpa [pairInput] using hw
        exact hw'.elim (fun h => h ▸ hxu) (fun h => h ▸ hxv)
      rw [← hfull (pairInput u v)] at hpair
      have hcases : H (pairInput u v) = true ∨ groupFun X B C (pairInput u v) = true := by
        simpa using hpair
      have hout : H x = true ∨ replacement X B C x = true := by
        rcases hcases with hh | hg
        · exact Or.inl (hmono (pairInput u v) x hle hh)
        · exact Or.inr (replacement_monotone X B C (pairInput u v) x hle
            ((replacement_preserves_pairs X B C haway u v).mp hg))
      simpa using hout
  cases hleft : H x || replacement X B C x <;> cases hright : graphFun G ∅ x <;> simp_all

lemma bipartite_reverse_star_read_one (p l : ℕ) (X : Finset (Fin p)) (S : Finset (Fin l))
    (hS : S.card ≤ 1) :
    ∃ D : Circuit, IsAO2 (p + l) D ∧ D.size ≤ X.card ∧
      (∀ x : Fin (p + l) → Bool, circuitFun (p + l) D x =
        decide (∃ a ∈ X, ∃ s ∈ S, x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p s) = true)) ∧
      PEqualNP.ReadK.IsReadK (p + l) D 1 := by
  classical
  obtain ⟨D, hAO, hsize, hfun, hread⟩ := star_cover_read_one p l (X ×ˢ S) ∅ S (by
    intro e he
    exact Or.inr (Finset.mem_product.mp he).2)
  refine ⟨D, hAO, ?_, ?_, hread⟩
  · simp only [Finset.card_product, Finset.card_empty, Nat.add_zero] at hsize
    have hc : S.card = 0 ∨ S.card = 1 := by omega
    rcases hc with hc | hc
    · simp only [hc, Nat.mul_zero, Nat.zero_add, Nat.zero_sub] at hsize
      omega
    · simpa only [hc, Nat.mul_one, Nat.add_sub_cancel] using hsize
  · intro x
    rw [hfun x]
    congr 1
    simp only [Finset.mem_product]
    aesop

lemma raw_gate_pair_unique {n : ℕ} (C : Circuit) (k j j' : ℕ) (a b : Fin n)
    (hfirst : (gateAt C k).inputs = [a.val, n + j] ∨ (gateAt C k).inputs = [n + j, a.val])
    (hsecond : (gateAt C k).inputs = [b.val, n + j'] ∨ (gateAt C k).inputs = [n + j', b.val]) :
    a = b ∧ j = j' := by
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · have he := List.cons.inj (hfirst.symm.trans hsecond)
    have ht := (List.cons.inj he.2).1
    exact ⟨Fin.ext he.1, by omega⟩
  · have he := (List.cons.inj (hfirst.symm.trans hsecond)).1
    have ha := a.isLt
    omega
  · have he := (List.cons.inj (hfirst.symm.trans hsecond)).1
    have hb := b.isLt
    omega
  · have he := List.cons.inj (hfirst.symm.trans hsecond)
    have ht := (List.cons.inj he.2).1
    exact ⟨Fin.ext ht, by omega⟩

lemma label_count_in_top_set {n : ℕ} (C : Circuit) (F : Finset (Fin n × ℕ))
    (top : Fin n × ℕ → ℕ) (M : Finset ℕ) (hmem : ∀ z ∈ F, top z ∈ M)
    (hinputs : ∀ z ∈ F, (gateAt C (top z)).inputs = [z.1.val, n + z.2] ∨
      (gateAt C (top z)).inputs = [n + z.2, z.1.val]) : F.card ≤ M.card := by
  apply Finset.card_le_card_of_injOn top
  · exact hmem
  · intro z hz z' hz' heq
    have hsecond := hinputs z' hz'
    rw [← heq] at hsecond
    obtain ⟨ha, hj⟩ := raw_gate_pair_unique C (top z) z.2 z'.2 z.1 z'.1 (hinputs z hz) hsecond
    exact Prod.ext ha hj

lemma top_image_card {n : ℕ} (C : Circuit) (F : Finset (Fin n × ℕ)) (top : Fin n × ℕ → ℕ)
    (hinputs : ∀ z ∈ F, (gateAt C (top z)).inputs = [z.1.val, n + z.2] ∨
      (gateAt C (top z)).inputs = [n + z.2, z.1.val]) : (F.image top).card = F.card := by
  apply Nat.le_antisymm Finset.card_image_le
  exact label_count_in_top_set C F top (F.image top)
    (fun z hz => Finset.mem_image_of_mem top hz) hinputs

lemma top_image_ands {n : ℕ} (C : Circuit) (F : Finset (Fin n × ℕ)) (top : Fin n × ℕ → ℕ)
    (hkind : ∀ z ∈ F, top z < C.gates.length ∧ (gateAt C (top z)).op = GateOp.and) :
    ∀ k ∈ F.image top, k < C.gates.length ∧ (gateAt C k).op = GateOp.and := by
  intro k hk
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
  exact hkind z hz

end SharedBottomStar

namespace GeneralThreeClauseSelector

open PEqualNP.MetaComplexity.NestedCover StarThreeClause

def cnf3 {n : ℕ} (A B C : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  clause A x && (clause B x && clause C x)

lemma hits_pair {n : ℕ} (A B C : Finset (Fin n)) (u v : Fin n) :
    cnf3 A B C (fun w => decide (w = u ∨ w = v)) = true ↔ ThreeClause.Hits A B C u v := by
  have hc (S : Finset (Fin n)) :
      clause S (fun w => decide (w = u ∨ w = v)) = true ↔ u ∈ S ∨ v ∈ S := by
    constructor
    · intro h
      obtain ⟨w, hw, hx⟩ := of_decide_eq_true h
      rcases of_decide_eq_true hx with rfl | rfl
      · exact Or.inl hw
      · exact Or.inr hw
    · intro h
      apply decide_eq_true
      rcases h with hu | hv
      · exact ⟨u, hu, by simp⟩
      · exact ⟨v, hv, by simp⟩
  simp only [cnf3, Bool.and_eq_true, hc, ThreeClause.Hits]

lemma hits_sound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C : Finset (Fin n))
    (hsafe : ∀ x, cnf3 A B C x = true → graphFun G ∅ x = true) :
    ∀ u v, ThreeClause.Hits A B C u v → G.Adj u v := by
  intro u v h
  have hh := hsafe _ ((hits_pair A B C u v).mpr h)
  have hedge : ∃ a b, G.Adj a b ∧ (a = u ∨ a = v) ∧ (b = u ∨ b = v) := by
    simpa [graphFun] using hh
  obtain ⟨a, b, hab, ha | ha, hb | hb⟩ := hedge
  · subst a; subst b
    exact False.elim ((G.ne_of_adj hab) rfl)
  · simpa only [ha, hb] using hab
  · simpa only [ha, hb] using hab.symm
  · subst a; subst b
    exact False.elim ((G.ne_of_adj hab) rfl)

lemma incident_center_occurs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C : Finset (Fin n))
    (hsound : ∀ u v, ThreeClause.Hits A B C u v → G.Adj u v)
    (a u : Fin n) (h : ThreeClause.Hits A B C a u) : a ∈ A ∨ a ∈ B ∨ a ∈ C := by
  by_contra hn
  push Not at hn
  have huA := h.1.resolve_left hn.1
  have huB := h.2.1.resolve_left hn.2.1
  have huC := h.2.2.resolve_left hn.2.2
  exact (G.ne_of_adj (hsound u u ⟨Or.inl huA, Or.inl huB, Or.inl huC⟩)) rfl

lemma clean_clause_allowed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (a : Fin n) (D : Finset (Fin n)) (hgood : ∀ u ∈ D, G.Adj a u) :
    NearColorCases.BAllowed G side a D := by
  left
  refine ⟨fun u hu => Ne.symm (hproper a u (hgood u hu)), ?_⟩
  have he : D.filter (fun u => ¬ G.Adj a u) = ∅ := by
    ext u
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    exact fun hu => not_not.mpr (hgood u hu)
  simp [he]

lemma selector_first_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (hfour : PEqualNP.TopForm.NoFourCycle G) (a : Fin n) (A B C : Finset (Fin n))
    (hsafe : ∀ x, cnf3 A B C x = true → graphFun G ∅ x = true) (haA : a ∈ A) :
    ∃ D E : Finset (Fin n), (D = B ∨ D = C) ∧ (E = B ∨ E = C) ∧
      NearColorCases.BAllowed G side a D ∧
      (∀ u ∈ CProjectionCharges.leaf side a E, G.Adj a u) ∧
      ∀ u, ThreeClause.Hits A B C a u →
        u ∈ NearMergeCharges.project G a D ∧ u ∈ CProjectionCharges.leaf side a E := by
  have hs := hits_sound G A B C hsafe
  have clean_case (D : Finset (Fin n)) (hD : D = B ∨ D = C)
      (hgood : ∀ u ∈ D, G.Adj a u)
      (hcover : ∀ u, ThreeClause.Hits A B C a u → u ∈ D) :
      ∃ D E : Finset (Fin n), (D = B ∨ D = C) ∧ (E = B ∨ E = C) ∧
        NearColorCases.BAllowed G side a D ∧
        (∀ u ∈ CProjectionCharges.leaf side a E, G.Adj a u) ∧
        ∀ u, ThreeClause.Hits A B C a u →
          u ∈ NearMergeCharges.project G a D ∧ u ∈ CProjectionCharges.leaf side a E := by
    refine ⟨D, D, hD, hD, clean_clause_allowed G side hproper a D hgood, ?_, ?_⟩
    · intro u hu
      exact hgood u (Finset.mem_filter.mp hu).1
    · intro u hu
      have hm := hcover u hu
      exact ⟨Finset.mem_filter.mpr ⟨hm, hgood u hm⟩,
        Finset.mem_filter.mpr ⟨hm, Ne.symm (hproper a u (hgood u hm))⟩⟩
  by_cases haB : a ∈ B
  · have haC : a ∉ C := by
      intro haC
      exact (G.ne_of_adj (hs a a ⟨Or.inl haA, Or.inl haB, Or.inl haC⟩)) rfl
    exact clean_case C (Or.inr rfl)
      (fun u hu => hs a u ⟨Or.inl haA, Or.inl haB, Or.inr hu⟩)
      (fun u hu => hu.2.2.resolve_left haC)
  by_cases haC : a ∈ C
  · exact clean_case B (Or.inl rfl)
      (fun u hu => hs a u ⟨Or.inl haA, Or.inr hu, Or.inl haC⟩)
      (fun u hu => hu.2.1.resolve_left haB)
  have hstar : ∀ x, starCNF a B C x = true → graphFun G ∅ x = true := by
    intro x hx
    have hx' : x a = true ∧ clause B x = true ∧ clause C x = true := by
      simpa only [starCNF, Bool.and_eq_true] using hx
    have hA : clause A x = true := decide_eq_true ⟨a, haA, hx'.1⟩
    exact hsafe x (by simp only [cnf3, hA, hx'.2.1, hx'.2.2, Bool.and_self])
  obtain ⟨D, E, hD, hE, hallow, hvalid, hcovD, hcovE⟩ :=
    StarClauseSelector.safe_clause_selector_for_budget G side hproper hfour a B C hstar
  refine ⟨D, E, hD, hE, hallow, hvalid, ?_⟩
  intro u hu
  have hm : u ∈ B ∩ C := Finset.mem_inter.mpr
    ⟨hu.2.1.resolve_left haB, hu.2.2.resolve_left haC⟩
  exact ⟨hcovD hm, hcovE hm⟩

lemma selector_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (hfour : PEqualNP.TopForm.NoFourCycle G) (a : Fin n) (A B C : Finset (Fin n))
    (hsafe : ∀ x, cnf3 A B C x = true → graphFun G ∅ x = true)
    (ha : a ∈ A ∨ a ∈ B ∨ a ∈ C) :
    ∃ D E : Finset (Fin n), (D = A ∨ D = B ∨ D = C) ∧
      (E = A ∨ E = B ∨ E = C) ∧ NearColorCases.BAllowed G side a D ∧
      (∀ u ∈ CProjectionCharges.leaf side a E, G.Adj a u) ∧
      ∀ u, ThreeClause.Hits A B C a u →
        u ∈ NearMergeCharges.project G a D ∧ u ∈ CProjectionCharges.leaf side a E := by
  rcases ha with ha | ha | ha
  · obtain ⟨D, E, hD, hE, hallow, hvalid, hcov⟩ :=
      selector_first_center G side hproper hfour a A B C hsafe ha
    exact ⟨D, E, Or.inr hD, Or.inr hE, hallow, hvalid, hcov⟩
  · have heq : cnf3 B A C = cnf3 A B C := by
      funext x
      unfold cnf3
      ac_rfl
    obtain ⟨D, E, hD, hE, hallow, hvalid, hcov⟩ :=
      selector_first_center G side hproper hfour a B A C (by simpa only [heq] using hsafe) ha
    refine ⟨D, E, hD.elim Or.inl (fun h => Or.inr (Or.inr h)),
      hE.elim Or.inl (fun h => Or.inr (Or.inr h)), hallow, hvalid, ?_⟩
    intro u hu
    exact hcov u ⟨hu.2.1, hu.1, hu.2.2⟩
  · have heq : cnf3 C A B = cnf3 A B C := by
      funext x
      unfold cnf3
      ac_rfl
    obtain ⟨D, E, hD, hE, hallow, hvalid, hcov⟩ :=
      selector_first_center G side hproper hfour a C A B (by simpa only [heq] using hsafe) ha
    refine ⟨D, E, hD.elim Or.inl (fun h => Or.inr (Or.inl h)),
      hE.elim Or.inl (fun h => Or.inr (Or.inl h)), hallow, hvalid, ?_⟩
    intro u hu
    exact hcov u ⟨hu.2.2, hu.1, hu.2.1⟩

end GeneralThreeClauseSelector

namespace ThreeClauseCenters

open ThreeClause

lemma hits_symm {n : ℕ} (A B C : Finset (Fin n)) (u v : Fin n)
    (h : Hits A B C u v) : Hits A B C v u :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

lemma bipartite_triangle_free {n : ℕ} (G : SimpleGraph (Fin n)) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v) :
    ∀ u v w, ¬ (G.Adj u v ∧ G.Adj v w ∧ G.Adj w u) := by
  intro u v w h
  have huv := hproper u v h.1
  have hvw := hproper v w h.2.1
  have hwu := hproper w u h.2.2
  cases hu : side u <;> cases hv : side v <;> cases hw : side w <;> simp_all

lemma two_centers_fixed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G) (A B C : Finset (Fin n))
    (hsound : ∀ u v, Hits A B C u v → G.Adj u v) (hno : NoCentre A B C)
    (hactive : ∃ u v, Hits A B C u v) (hbc : B ∩ C = ∅) :
    ∃ a b, a ≠ b ∧ Hits A B C a b ∧
      ∀ u v, Hits A B C u v → u = a ∨ v = a ∨ u = b ∨ v = b := by
  obtain ⟨a, b, hab, _, _, haA, haB, _, hbA, hbC, _, hform, _⟩ :=
    fixed_orientation G hfour A B C hsound hno hactive hbc
  refine ⟨a, b, hab, ⟨Or.inl haA, Or.inl haB, Or.inr hbC⟩, ?_⟩
  intro u v hu
  rcases (hform u v).mp hu with h | h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr (Or.inl h.1))
  · exact Or.inr (Or.inr (Or.inr h.1))

lemma two_centers_nonstar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (hfour : PEqualNP.TopForm.NoFourCycle G) (A B C : Finset (Fin n))
    (hsound : ∀ u v, Hits A B C u v → G.Adj u v) (hno : NoCentre A B C)
    (hactive : ∃ u v, Hits A B C u v) :
    ∃ a b, a ≠ b ∧ Hits A B C a b ∧
      ∀ u v, Hits A B C u v → u = a ∨ v = a ∨ u = b ∨ v = b := by
  rcases one_overlap_empty G (bipartite_triangle_free G side hproper) A B C hsound with hab | hac | hbc
  · have hs : ∀ u v, Hits C A B u v → G.Adj u v :=
      fun u v h => hsound u v ⟨h.2.1, h.2.2, h.1⟩
    have hn : NoCentre C A B := by
      intro c
      obtain ⟨u, v, h, hu, hv⟩ := hno c
      exact ⟨u, v, ⟨h.2.2, h.1, h.2.1⟩, hu, hv⟩
    have ha : ∃ u v, Hits C A B u v := by
      obtain ⟨u, v, h⟩ := hactive
      exact ⟨u, v, ⟨h.2.2, h.1, h.2.1⟩⟩
    obtain ⟨a, b, hne, hedge, hcover⟩ := two_centers_fixed G hfour C A B hs hn ha hab
    exact ⟨a, b, hne, ⟨hedge.2.1, hedge.2.2, hedge.1⟩,
      fun u v h => hcover u v ⟨h.2.2, h.1, h.2.1⟩⟩
  · have hs : ∀ u v, Hits B A C u v → G.Adj u v :=
      fun u v h => hsound u v ⟨h.2.1, h.1, h.2.2⟩
    have hn : NoCentre B A C := by
      intro c
      obtain ⟨u, v, h, hu, hv⟩ := hno c
      exact ⟨u, v, ⟨h.2.1, h.1, h.2.2⟩, hu, hv⟩
    have ha : ∃ u v, Hits B A C u v := by
      obtain ⟨u, v, h⟩ := hactive
      exact ⟨u, v, ⟨h.2.1, h.1, h.2.2⟩⟩
    obtain ⟨a, b, hne, hedge, hcover⟩ := two_centers_fixed G hfour B A C hs hn ha hac
    exact ⟨a, b, hne, ⟨hedge.2.1, hedge.1, hedge.2.2⟩,
      fun u v h => hcover u v ⟨h.2.1, h.1, h.2.2⟩⟩
  · exact two_centers_fixed G hfour A B C hsound hno hactive hbc

lemma centers_classification {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : Fin n → Bool) (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (hfour : PEqualNP.TopForm.NoFourCycle G) (A B C : Finset (Fin n))
    (hsound : ∀ u v, Hits A B C u v → G.Adj u v)
    (hactive : ∃ u v, Hits A B C u v) :
    (∃ a, ∀ u v, Hits A B C u v → u = a ∨ v = a) ∨
      (∃ a b, a ≠ b ∧ Hits A B C a b ∧
        ∀ u v, Hits A B C u v → u = a ∨ v = a ∨ u = b ∨ v = b) := by
  classical
  by_cases hc : ∃ a, ∀ u v, Hits A B C u v → u = a ∨ v = a
  · exact Or.inl hc
  right
  have hn : NoCentre A B C := by
    intro c
    by_contra h
    apply hc
    refine ⟨c, ?_⟩
    intro u v hu
    by_contra hne
    have huc : u ≠ c := fun he => hne (Or.inl he)
    have hvc : v ≠ c := fun he => hne (Or.inr he)
    exact h ⟨u, v, hu, huc, hvc⟩
  exact two_centers_nonstar G side hproper hfour A B C hsound hn hactive

end ThreeClauseCenters

namespace MatchingEndpointCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

noncomputable def andGates (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k => (gateAt C k).op = GateOp.and

lemma distinct_pair_endpoints (B : List (ℕ × ℕ))
    (hB : B.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2))
    (i j : Fin B.length) (hij : i ≠ j) :
    (B.get i).1 ≠ (B.get j).1 ∧ (B.get i).1 ≠ (B.get j).2 ∧
      (B.get i).2 ≠ (B.get j).1 ∧ (B.get i).2 ≠ (B.get j).2 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hB.rel_get_of_lt hlt
  · obtain ⟨h11, h12, h21, h22⟩ := hB.rel_get_of_lt hgt
    exact ⟨Ne.symm h11, Ne.symm h21, Ne.symm h12, Ne.symm h22⟩

lemma chosen_endpoint_injOn (B : List (ℕ × ℕ))
    (hB : B.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2))
    (T : Finset (Fin B.length)) (w : Fin B.length → ℕ)
    (hw : ∀ i ∈ T, w i = (B.get i).1 ∨ w i = (B.get i).2) :
    Set.InjOn w T := by
  intro i hi j hj heq
  by_contra hij
  obtain ⟨h11, h12, h21, h22⟩ := distinct_pair_endpoints B hB i j hij
  rcases hw i hi with hiw | hiw <;> rcases hw j hj with hjw | hjw
  · exact h11 (hiw.symm.trans (heq.trans hjw))
  · exact h12 (hiw.symm.trans (heq.trans hjw))
  · exact h21 (hiw.symm.trans (heq.trans hjw))
  · exact h22 (hiw.symm.trans (heq.trans hjw))

lemma chosen_gate_injOn (n : ℕ) (B : List (ℕ × ℕ))
    (hB : B.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2))
    (T : Finset (Fin B.length)) (gate : Fin B.length → ℕ)
    (hgate : ∀ i ∈ T, n + gate i = (B.get i).1 ∨ n + gate i = (B.get i).2) :
    Set.InjOn gate T := by
  intro i hi j hj heq
  apply chosen_endpoint_injOn B hB T (fun k => n + gate k) hgate hi hj
  exact congrArg (fun k => n + k) heq

lemma chosen_gate_image_card (n : ℕ) (B : List (ℕ × ℕ))
    (hB : B.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2))
    (T : Finset (Fin B.length)) (gate : Fin B.length → ℕ)
    (hgate : ∀ i ∈ T, n + gate i = (B.get i).1 ∨ n + gate i = (B.get i).2) :
    (T.image gate).card = T.card := by
  exact Finset.card_image_iff.mpr (chosen_gate_injOn n B hB T gate hgate)

lemma chosen_gate_image_ands (C : Circuit) (B : List (ℕ × ℕ))
    (T : Finset (Fin B.length)) (gate : Fin B.length → ℕ)
    (hkind : ∀ i ∈ T, gate i < C.gates.length ∧ (gateAt C (gate i)).op = GateOp.and) :
    ∀ k ∈ T.image gate, k < C.gates.length ∧ (gateAt C k).op = GateOp.and := by
  intro k hk
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
  exact hkind i hi

lemma chosen_gate_count (n : ℕ) (C : Circuit) (B : List (ℕ × ℕ))
    (hB : B.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2))
    (T : Finset (Fin B.length)) (gate : Fin B.length → ℕ)
    (hgate : ∀ i ∈ T, n + gate i = (B.get i).1 ∨ n + gate i = (B.get i).2)
    (hkind : ∀ i ∈ T, gate i < C.gates.length ∧ (gateAt C (gate i)).op = GateOp.and) :
    T.card ≤ (andGates C).card := by
  classical
  rw [← chosen_gate_image_card n B hB T gate hgate]
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hlt, hop⟩ := chosen_gate_image_ands C B T gate hkind k hk
  change k ∈ (Finset.range C.gates.length).filter fun k => (gateAt C k).op = GateOp.and
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hop⟩

lemma exists_chosen_and_set (n : ℕ) (C : Circuit) (B : List (ℕ × ℕ))
    (hB : B.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2))
    (T : Finset (Fin B.length))
    (hex : ∀ i ∈ T, ∃ j, (n + j = (B.get i).1 ∨ n + j = (B.get i).2) ∧
      j < C.gates.length ∧ (gateAt C j).op = GateOp.and) :
    ∃ M : Finset ℕ, M.card = T.card ∧
      (∀ k ∈ M, k < C.gates.length ∧ (gateAt C k).op = GateOp.and) ∧
      (∀ i ∈ T, ∃ j ∈ M, n + j = (B.get i).1 ∨ n + j = (B.get i).2) := by
  classical
  have hchoice : ∀ i : Fin B.length, ∃ j, i ∈ T →
      (n + j = (B.get i).1 ∨ n + j = (B.get i).2) ∧
        j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
    intro i
    by_cases hi : i ∈ T
    · obtain ⟨j, hj⟩ := hex i hi
      exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose gate hgate using hchoice
  have he : ∀ i ∈ T, n + gate i = (B.get i).1 ∨ n + gate i = (B.get i).2 :=
    fun i hi => (hgate i hi).1
  have hk : ∀ i ∈ T, gate i < C.gates.length ∧ (gateAt C (gate i)).op = GateOp.and :=
    fun i hi => (hgate i hi).2
  refine ⟨T.image gate, chosen_gate_image_card n B hB T gate he,
    chosen_gate_image_ands C B T gate hk, ?_⟩
  intro i hi
  exact ⟨gate i, Finset.mem_image_of_mem gate hi, he i hi⟩

end MatchingEndpointCount

namespace IncidencePoolCount

lemma incidence_pool_count {n p l : ℕ}
    (P : Fin p → Fin n) (L : Fin l → Fin n)
    (hP : Function.Injective P) (hL : Function.Injective L)
    (hPL : ∀ u v, P u ≠ L v)
    (H : Fin n → Finset (Fin n)) (EL ER : Finset (Fin p × Fin l))
    (hEL : ∀ e ∈ EL, L e.2 ∈ H (P e.1))
    (hER : ∀ e ∈ ER, P e.1 ∈ H (L e.2)) :
    EL.card + ER.card ≤ ∑ c : Fin n, (H c).card := by
  classical
  let f : Fin p × Fin l → Fin n × Fin n := fun e => (P e.1, L e.2)
  let g : Fin p × Fin l → Fin n × Fin n := fun e => (L e.2, P e.1)
  let A := EL.image f
  let B := ER.image g
  have hf : Function.Injective f := by
    intro e e' he
    apply Prod.ext
    · exact hP (congrArg Prod.fst he)
    · exact hL (congrArg Prod.snd he)
  have hg : Function.Injective g := by
    intro e e' he
    apply Prod.ext
    · exact hP (congrArg Prod.snd he)
    · exact hL (congrArg Prod.fst he)
  have hA : A.card = EL.card := Finset.card_image_of_injective EL hf
  have hB : B.card = ER.card := Finset.card_image_of_injective ER hg
  have hdisjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp heA
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp heB
    exact hPL a.1 b.2 (congrArg Prod.fst (ha.trans hb.symm))
  let pool : Finset (Fin n × Fin n) :=
    Finset.univ.biUnion fun c => ({c} : Finset (Fin n)) ×ˢ H c
  have hcover : A ∪ B ⊆ pool := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_biUnion.mpr ⟨P a.1, Finset.mem_univ _,
        Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, hEL a ha⟩⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_biUnion.mpr ⟨L a.2, Finset.mem_univ _,
        Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, hER a ha⟩⟩
  have hpool : pool.card ≤ ∑ c : Fin n, (H c).card := by
    have hh := Finset.card_biUnion_le (s := Finset.univ)
      (t := fun c : Fin n => ({c} : Finset (Fin n)) ×ˢ H c)
    simpa only [pool, Finset.card_product, Finset.card_singleton, one_mul] using hh
  calc
    EL.card + ER.card = A.card + B.card := by rw [hA, hB]
    _ = (A ∪ B).card := (Finset.card_union_of_disjoint hdisjoint).symm
    _ ≤ pool.card := Finset.card_le_card hcover
    _ ≤ ∑ c : Fin n, (H c).card := hpool

end IncidencePoolCount

namespace GeneralRootFamily

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

noncomputable def incidentLeaves {n : ℕ} (C : Circuit) (v : Fin n) (b c d : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun u => ThreeClause.Hits (orIn n C b) (orIn n C c) (orIn n C d) v u

noncomputable def centerLeaves {n m : ℕ} (C : Circuit) (a : Fin m → Fin n)
    (b c d : Fin m → ℕ) (v : Fin n) : Finset (Fin n) :=
  (StarRootFamily.indexFiber a v).biUnion fun i => incidentLeaves C (a i) (b i) (c i) (d i)

lemma select_source_wires {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (a : Fin n) (b c d : ℕ)
    (hsafe : ∀ x, GeneralThreeClauseSelector.cnf3 (orIn n C b) (orIn n C c) (orIn n C d) x = true →
      graphFun G ∅ x = true) (hactive : (incidentLeaves C a b c d).Nonempty) :
    ∃ p q : ℕ, (p = b ∨ p = c ∨ p = d) ∧ (q = b ∨ q = c ∨ q = d) ∧
      NearColorCases.BAllowed G side a (orIn n C p) ∧
      (∀ u ∈ CProjectionCharges.leaf side a (orIn n C q), G.Adj a u) ∧
      (∀ u ∈ incidentLeaves C a b c d, u ∈ NearMergeCharges.project G a (orIn n C p) ∧
        u ∈ CProjectionCharges.leaf side a (orIn n C q)) := by
  classical
  obtain ⟨u, hu⟩ := hactive
  have hoccurs := GeneralThreeClauseSelector.incident_center_occurs G
    (orIn n C b) (orIn n C c) (orIn n C d)
    (GeneralThreeClauseSelector.hits_sound G _ _ _ hsafe) a u (Finset.mem_filter.mp hu).2
  obtain ⟨D, E, hD, hE, hallowed, hvalid, hcover⟩ :=
    GeneralThreeClauseSelector.selector_center G side hproper hfour a
      (orIn n C b) (orIn n C c) (orIn n C d) hsafe hoccurs
  have hwire : ∀ S, (S = orIn n C b ∨ S = orIn n C c ∨ S = orIn n C d) →
      ∃ w : ℕ, (w = b ∨ w = c ∨ w = d) ∧ orIn n C w = S := by
    intro S hS
    rcases hS with rfl | rfl | rfl
    · exact ⟨b, Or.inl rfl, rfl⟩
    · exact ⟨c, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨d, Or.inr (Or.inr rfl), rfl⟩
  obtain ⟨p, hp, hpD⟩ := hwire D hD
  obtain ⟨q, hq, hqE⟩ := hwire E hE
  refine ⟨p, q, hp, hq, ?_, ?_, ?_⟩
  · simpa only [hpD] using hallowed
  · simpa only [hqE] using hvalid
  · intro v hv
    simpa only [hpD, hqE] using hcover v (Finset.mem_filter.mp hv).2

lemma select_source_family {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (a : Fin m → Fin n) (b c d : Fin m → ℕ)
    (hb : ∀ i, b i < n + C.size) (hc : ∀ i, c i < n + C.size) (hd : ∀ i, d i < n + C.size)
    (hsafe : ∀ i x, GeneralThreeClauseSelector.cnf3
      (orIn n C (b i)) (orIn n C (c i)) (orIn n C (d i)) x = true → graphFun G ∅ x = true) :
    ∃ T U : Fin n → Finset ℕ,
      (∀ v, T v ⊆ Finset.range (n + C.size)) ∧
      (∀ v, U v ⊆ Finset.range (n + C.size)) ∧
      (∀ v, ∀ w ∈ T v, NearColorCases.BAllowed G side v (orIn n C w)) ∧
      (∀ v, ∀ w ∈ U v, ∀ u ∈ CProjectionCharges.leaf side v (orIn n C w), G.Adj v u) ∧
      (∀ v, centerLeaves C a b c d v ⊆
        (T v).biUnion (fun w => NearMergeCharges.project G v (orIn n C w))) ∧
      (∀ v, centerLeaves C a b c d v ⊆
        (U v).biUnion (fun w => CProjectionCharges.leaf side v (orIn n C w))) ∧
      (∑ v : Fin n, (T v).card) ≤ m ∧ (∑ v : Fin n, (U v).card) ≤ m := by
  classical
  let Active : Fin m → Prop := fun i => (incidentLeaves C (a i) (b i) (c i) (d i)).Nonempty
  have hselect : ∀ i, Active i → ∃ p q : ℕ,
      (p = b i ∨ p = c i ∨ p = d i) ∧ (q = b i ∨ q = c i ∨ q = d i) ∧
      NearColorCases.BAllowed G side (a i) (orIn n C p) ∧
      (∀ u ∈ CProjectionCharges.leaf side (a i) (orIn n C q), G.Adj (a i) u) ∧
      (∀ u ∈ incidentLeaves C (a i) (b i) (c i) (d i),
        u ∈ NearMergeCharges.project G (a i) (orIn n C p) ∧
          u ∈ CProjectionCharges.leaf side (a i) (orIn n C q)) := by
    intro i hi
    exact select_source_wires G hfour side hproper C (a i) (b i) (c i) (d i) (hsafe i) hi
  let p : Fin m → ℕ := fun i => if hi : Active i then (hselect i hi).choose else 0
  let q : Fin m → ℕ := fun i => if hi : Active i then (hselect i hi).choose_spec.choose else 0
  have hprops : ∀ i, Active i →
      (p i = b i ∨ p i = c i ∨ p i = d i) ∧ (q i = b i ∨ q i = c i ∨ q i = d i) ∧
      NearColorCases.BAllowed G side (a i) (orIn n C (p i)) ∧
      (∀ u ∈ CProjectionCharges.leaf side (a i) (orIn n C (q i)), G.Adj (a i) u) ∧
      (∀ u ∈ incidentLeaves C (a i) (b i) (c i) (d i),
        u ∈ NearMergeCharges.project G (a i) (orIn n C (p i)) ∧
          u ∈ CProjectionCharges.leaf side (a i) (orIn n C (q i))) := by
    intro i hi
    simpa only [p, q, dite_eq_left hi] using (hselect i hi).choose_spec.choose_spec
  let T : Fin n → Finset ℕ := fun v => ((StarRootFamily.indexFiber a v).filter Active).image p
  let U : Fin n → Finset ℕ := fun v => ((StarRootFamily.indexFiber a v).filter Active).image q
  have hpool (f : Fin m → ℕ) :
      (∑ v : Fin n, (((StarRootFamily.indexFiber a v).filter Active).image f).card) ≤ m := by
    apply le_trans ?_ (StarRootFamily.root_pool_card_bound a f)
    apply Finset.sum_le_sum
    intro v hv
    apply Finset.card_le_card
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩
  refine ⟨T, U, ?_, ?_, ?_, ?_, ?_, ?_, hpool p, hpool q⟩
  · intro v w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have hiA := (Finset.mem_filter.mp hi).2
    apply Finset.mem_range.mpr
    rcases (hprops i hiA).1 with he | he | he
    · rw [he]; exact hb i
    · rw [he]; exact hc i
    · rw [he]; exact hd i
  · intro v w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have hiA := (Finset.mem_filter.mp hi).2
    apply Finset.mem_range.mpr
    rcases (hprops i hiA).2.1 with he | he | he
    · rw [he]; exact hb i
    · rw [he]; exact hc i
    · rw [he]; exact hd i
  · intro v w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hiF, hiA⟩ := Finset.mem_filter.mp hi
    have hiv := (Finset.mem_filter.mp hiF).2
    rw [← hiv]
    exact (hprops i hiA).2.2.1
  · intro v w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hiF, hiA⟩ := Finset.mem_filter.mp hi
    have hiv := (Finset.mem_filter.mp hiF).2
    rw [← hiv]
    exact (hprops i hiA).2.2.2.1
  · intro v u hu
    obtain ⟨i, hiF, hui⟩ := Finset.mem_biUnion.mp hu
    have hiA : Active i := ⟨u, hui⟩
    have hiv := (Finset.mem_filter.mp hiF).2
    have hp := ((hprops i hiA).2.2.2.2 u hui).1
    rw [hiv] at hp
    exact Finset.mem_biUnion.mpr ⟨p i,
      Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiF, hiA⟩, rfl⟩, hp⟩
  · intro v u hu
    obtain ⟨i, hiF, hui⟩ := Finset.mem_biUnion.mp hu
    have hiA : Active i := ⟨u, hui⟩
    have hiv := (Finset.mem_filter.mp hiF).2
    have hp := ((hprops i hiA).2.2.2.2 u hui).2
    rw [hiv] at hp
    exact Finset.mem_biUnion.mpr ⟨q i,
      Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiF, hiA⟩, rfl⟩, hp⟩

lemma shared_three_clause_budget {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (side : Fin n → Bool)
    (hproper : ∀ u v, G.Adj u v → side u ≠ side v)
    (C : Circuit) (hAO : IsAO2 n C) (a : Fin m → Fin n) (b c d : Fin m → ℕ)
    (hb : ∀ i, b i < n + C.size) (hc : ∀ i, c i < n + C.size) (hd : ∀ i, d i < n + C.size)
    (hsafe : ∀ i x, GeneralThreeClauseSelector.cnf3
      (orIn n C (b i)) (orIn n C (c i)) (orIn n C (d i)) x = true → graphFun G ∅ x = true) :
    (∑ v : Fin n, (centerLeaves C a b c d v).card) ≤
      ((Finset.range C.gates.length).filter fun k => 2 ≤ (orIn n C (n + k)).card).card + m := by
  obtain ⟨T, U, hT, hU, hallowed, hvalid, hcovB, hcovC, hrootsB, hrootsC⟩ :=
    select_source_family G hfour side hproper C a b c d hb hc hd hsafe
  apply ComplementaryBudget.circuit_two_source_budget G hfour side hproper C hAO Finset.univ T U
    (fun v _ => hT v) (fun v _ => hU v) (fun v _ => hallowed v) (fun v _ => hvalid v)
    (∑ v : Fin n, (centerLeaves C a b c d v).card) m
  · apply Finset.sum_le_sum
    intro v hv
    exact Finset.card_le_card (hcovB v)
  · apply Finset.sum_le_sum
    intro v hv
    exact Finset.card_le_card (hcovC v)
  · omega

lemma mem_centerLeaves_iff_accepted_pair {n m : ℕ}
    (C : Circuit) (a : Fin m → Fin n) (b c d : Fin m → ℕ) (v u : Fin n) :
    u ∈ centerLeaves C a b c d v ↔ ∃ i : Fin m, a i = v ∧
      GeneralThreeClauseSelector.cnf3 (orIn n C (b i)) (orIn n C (c i)) (orIn n C (d i))
        (fun w => decide (w = a i ∨ w = u)) = true := by
  classical
  constructor
  · intro hu
    obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp hu
    refine ⟨i, (Finset.mem_filter.mp hi).2, ?_⟩
    exact (GeneralThreeClauseSelector.hits_pair _ _ _ (a i) u).mpr (Finset.mem_filter.mp hui).2
  · rintro ⟨i, hiv, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiv⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (GeneralThreeClauseSelector.hits_pair _ _ _ (a i) u).mp hi⟩⟩

end GeneralRootFamily

end PEqualNP.Outside.L_meta_2583
