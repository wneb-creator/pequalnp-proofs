import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18025

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
    ∃ a c : ℕ, (gateAtL gs j).inputs = [a, c] ∧ a ∈ S true ∧ c ∈ S false)

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
      exact ⟨a, c, hin, hSub true ha, hSub false hc⟩
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
    (hG : Good x1 x2 S gs) {a c : ℕ} (ha : a ∈ S true) (hc : c ∈ S false) :
    Good x1 x2 S (gs ++ [⟨GateOp.and, [a, c]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have ha_lt : a < x1 + x2 + gs.length := hLt true a ha
  have hc_lt : c < x1 + x2 + gs.length := hLt false c hc
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

private abbrev Rectangle (n m : ℕ) := Finset (Fin n) × Finset (Fin m)

private def weight {n m : ℕ} (r : Rectangle n m) : ℕ := r.1.card + r.2.card

private noncomputable def hit {n m : ℕ} (z : Fin (n+m) → Bool) (r : Rectangle n m) : Bool :=
  (r.1.toList.any fun a => z (Fin.castAdd m a)) &&
  (r.2.toList.any fun b => z (Fin.natAdd n b))

private theorem addRectangle {n m : ℕ} (r : Rectangle n m)
    (live : r.1.Nonempty ∧ r.2.Nonempty) (S : Bool → Finset ℕ) (gs : List Gate)
    (good : Good n m S gs) (raws : ∀ b, S0 n m b ⊆ S b) :
    ∃ S' gs' out,
      Good n m S' gs' ∧ (∀ b, S b ⊆ S' b) ∧
      gs'.length + 1 = gs.length + weight r ∧ out < n + m + gs'.length ∧
      (∀ z i, i < n + m + gs.length → wireVal (n+m) gs' z i = wireVal (n+m) gs z i) ∧
      (∀ z, wireVal (n+m) gs' z out = hit z r) := by
  let left := r.1.toList.map (fun a => a.val)
  let right := r.2.toList.map (fun b => n+b.val)
  have lc : left.length = r.1.card := by simp [left]
  have rc : right.length = r.2.card := by simp [right]
  have lpos : 0 < r.1.card := Finset.card_pos.mpr live.1
  have rpos : 0 < r.2.card := Finset.card_pos.mpr live.2
  have ln : left ≠ [] := by intro h; simp [h] at lc; omega
  have rn : right ≠ [] := by intro h; simp [h] at rc; omega
  have hl (a : ℕ) (ha : a ∈ left) : a ∈ S false := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    exact raws false (mem_S0_false i)
  have hr (b : ℕ) (hb : b ∈ right) : b ∈ S true := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
    exact raws true (mem_S0_true i)
  obtain ⟨S1, gs1, u, len1, good1, sub1, uMem, old1, eval1⟩ :=
    addOrInSide false left ln S gs good hl
  obtain ⟨S2, gs2, v, len2, good2, sub2, vMem, old2, eval2⟩ :=
    addOrInSide true right rn S1 gs1 good1 (fun i hi => sub1 true (hr i hi))
  have uMem2 := sub2 false uMem
  have uBound := good1.2.2.1 false u uMem
  have uBound2 := good2.2.2.1 false u uMem2
  have vBound := good2.2.2.1 true v vMem
  let gs3 := gs2 ++ [⟨GateOp.and,[v,u]⟩]
  refine ⟨S2,gs3,n+m+gs2.length,good_append_and good2 vMem uMem2,
    fun b => (sub1 b).trans (sub2 b),?_,by simp [gs3],?_,?_⟩
  · simp only [gs3,List.length_append,List.length_singleton,weight]
    omega
  · intro z i hi
    have q1 : i < n+m+gs1.length := by omega
    have q2 : i < n+m+gs2.length := by omega
    exact (wireVal_append_gate_lt _ _ _ _ _ q2).trans ((old2 z i q1).trans (old1 z i hi))
  · intro z
    rw [wireVal_append_gate_self]
    simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true]
    rw [old2 z u uBound, eval1 z, eval2 z]
    have lf : left.any (fun w => wireVal (n+m) gs z w) =
        r.1.toList.any (fun a => z (Fin.castAdd m a)) := by
      simp only [left,List.any_map,Function.comp_def,wireVal_input_left]
    have rf : right.any (fun w => wireVal (n+m) gs1 z w) =
        r.2.toList.any (fun b => z (Fin.natAdd n b)) := by
      simp only [right,List.any_map,Function.comp_def,wireVal_input_right]
    rw [lf,rf,hit,Bool.and_comm]

private theorem addRectangles {n m : ℕ} (rs : List (Rectangle n m))
    (live : ∀ r ∈ rs, r.1.Nonempty ∧ r.2.Nonempty) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate), Good n m S gs → (∀ b, S0 n m b ⊆ S b) →
    ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (outs : List ℕ),
      Good n m S' gs' ∧ gs'.length + outs.length = gs.length + (rs.map weight).sum ∧
      outs.length = rs.length ∧ (∀ w ∈ outs, w < n + m + gs'.length) ∧
      (∀ z i, i < n + m + gs.length → wireVal (n+m) gs' z i = wireVal (n+m) gs z i) ∧
      (∀ z, outs.any (fun w => wireVal (n+m) gs' z w) = rs.any (hit z)) := by
  induction rs with
  | nil =>
    intro S gs good _
    exact ⟨S,gs,[],good,by simp,rfl,by simp,fun _ _ _ => rfl,fun _ => rfl⟩
  | cons r rs ih =>
    intro S gs good raws
    obtain ⟨S1,gs1,out,good1,sub1,length1,out1,pres1,eval1⟩ :=
      addRectangle r (live r List.mem_cons_self) S gs good raws
    obtain ⟨S2,gs2,outs,good2,length2,list2,out2,pres2,eval2⟩ :=
      ih (fun q hq => live q (List.mem_cons_of_mem _ hq)) S1 gs1 good1
        (fun b => (raws b).trans (sub1 b))
    have grow1 : gs.length ≤ gs1.length := by
      have hp : 0 < r.1.card := Finset.card_pos.mpr (live r List.mem_cons_self).1
      have hq : 0 < r.2.card := Finset.card_pos.mpr (live r List.mem_cons_self).2
      simp only [weight] at length1
      omega
    have grow2 : gs1.length ≤ gs2.length := by
      have sizePositive : ∀ q ∈ rs, 1 ≤ weight q := by
        intro q hq
        have hp := Finset.card_pos.mpr (live q (List.mem_cons_of_mem _ hq)).1
        simp only [weight]
        omega
      have sumBound : rs.length ≤ (rs.map weight).sum := by
        have h : (rs.map (fun _ => 1)).sum ≤ (rs.map weight).sum :=
          List.sum_le_sum (fun q hq => sizePositive q hq)
        simpa using h
      omega
    refine ⟨S2,gs2,out::outs,good2,?_,by simp [list2],?_,?_,?_⟩
    · simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact out2 w hw
    · intro z i hi
      exact (pres2 z i (by omega)).trans (pres1 z i hi)
    · intro z
      rw [List.any_cons,List.any_cons,pres2 z out out1,eval1 z,eval2 z]

private theorem fromGood {n m : ℕ} (S : Bool → Finset ℕ) (gs : List Gate) (out : ℕ)
    (hG : Good n m S gs) :
    PEqualNP.TopForm.IsAO2 (n+m) ⟨gs,out⟩ ∧
      ∀ j < gs.length, (gateAt ⟨gs,out⟩ j).op = .and →
        ∃ a b : ℕ, ∃ L R : Finset ℕ,
          (gateAt ⟨gs,out⟩ j).inputs = [a,b] ∧ a ∈ R ∧ b ∈ L ∧
          (∀ w ∈ L, w < n ∨ ∃ i < gs.length, w = n+m+i ∧
            (gateAt ⟨gs,out⟩ i).op = .or ∧ ∀ t ∈ (gateAt ⟨gs,out⟩ i).inputs, t ∈ L) ∧
          ∀ w ∈ R, n ≤ w ∧ w < n+m ∨ ∃ i < gs.length, w = n+m+i ∧
            (gateAt ⟨gs,out⟩ i).op = .or ∧ ∀ t ∈ (gateAt ⟨gs,out⟩ i).inputs, t ∈ R := by
  obtain ⟨ops,back,_,sides,andPorts⟩ := hG
  refine ⟨⟨fun g hg => (ops g hg).1,back,fun g hg => (ops g hg).2⟩,?_⟩
  intro j hj hop
  obtain ⟨a,b,eq,hR,hL⟩ := andPorts j hj hop
  refine ⟨a,b,S false,S true,eq,hR,hL,?_,?_⟩
  · intro w hw
    rcases sides false w hw with ⟨_,hw'⟩ | hs
    · exact Or.inl (by simpa only [decide_eq_false_iff_not,not_le] using hw')
    · exact Or.inr hs
  · intro w hw
    rcases sides true w hw with ⟨le,hw'⟩ | hs
    · exact Or.inl ⟨of_decide_eq_true hw',le⟩
    · exact Or.inr hs

end PEqualNP.Outside.L_meta_18025

open PEqualNP.Outside.L_meta_18025 in
theorem PEqualNP.Outside.L_meta_18025 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 x6 : ℕ) (x7 : Fin x6 → Finset (Fin x1)) (x8 : Fin x6 → Finset (Fin x2)), ((∀ (x9 : Fin x6), (x7 x9).Nonempty ∧ (x8 x9).Nonempty) ∧ (∀ (x9 : Fin x6), ∀ x10 ∈ x7 x9, ∀ x12 ∈ x8 x9, x3 x10 x12) ∧ ∀ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 → ∃ (x12 : Fin x6), x9 ∈ x7 x12 ∧ x10 ∈ x8 x12) → ∑ x10 : Fin x6, ((x7 x10).card + (x8 x10).card) ≤ x5 + (1 : ℕ) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x11 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x11 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x11.size ≤ x5 ∧ ∀ x12 < x11.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ) (x17 : Finset ℕ) (x18 : Finset ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).inputs = [x15, x16] ∧ x15 ∈ x18 ∧ x16 ∈ x17 ∧ (∀ x19 ∈ x17, x19 < x1 ∨ ∃ x21 < x11.gates.length, x19 = x1 + x2 + x21 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x21).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x21).inputs, x22 ∈ x17) ∧ ∀ x19 ∈ x18, x1 ≤ x19 ∧ x19 < x1 + x2 ∨ ∃ x21 < x11.gates.length, x19 = x1 + x2 + x21 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x21).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x21).inputs, x22 ∈ x18 := by
  intro n m I _ cap k X Y conditions budget
  rcases conditions with ⟨nonempty,valid,cover⟩
  let rs : List (Rectangle n m) := List.ofFn fun i => (X i,Y i)
  obtain ⟨S,gs,outs,good,stepCount,nouts,earlier,preserved,meaning⟩ :=
    addRectangles rs (by
      intro r hr
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      exact nonempty i) (S0 n m) [] (good_init n m) (fun _ => Finset.Subset.rfl)
  have rsSize : rs.length = k := List.length_ofFn
  have costWeight : (rs.map weight).sum = ∑ i : Fin k, ((X i).card+(Y i).card) := by
    simp [rs, weight, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  have semantics (z : Fin (n+m) → Bool) : rs.any (hit z) =
      decide (∃ a b, I a b ∧ z (Fin.castAdd m a) = true ∧ z (Fin.natAdd n b) = true) := by
    rw [Bool.eq_iff_iff,decide_eq_true_eq,List.any_eq_true]
    constructor
    · rintro ⟨r,hr,yes⟩
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      simp only [hit,Bool.and_eq_true,List.any_eq_true,Finset.mem_toList] at yes
      obtain ⟨⟨a,ha,az⟩,⟨b,hb,bz⟩⟩ := yes
      exact ⟨a,b,valid i a ha b hb,az,bz⟩
    · rintro ⟨a,b,e,ha,hb⟩
      obtain ⟨i,hi,hj⟩ := cover a b e
      refine ⟨(X i,Y i),List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
      simp only [hit,Bool.and_eq_true,List.any_eq_true,Finset.mem_toList]
      exact ⟨⟨a,hi,ha⟩,⟨b,hj,hb⟩⟩
  by_cases empty : outs = []
  · have rsEmpty : rs = [] := by apply List.eq_nil_of_length_eq_zero; simpa [empty] using nouts.symm
    have goodEmpty := fromGood (S0 n m) [] (n+m) (good_init n m)
    refine ⟨⟨[],n+m⟩,goodEmpty.1,?_,by simp [PEqualNP.CircuitLowerBounds.Circuit.size],?_⟩
    · intro z
      have hh := semantics z
      rw [rsEmpty,List.any_nil] at hh
      change (List.ofFn z).getD (n+m) false = _
      rw [getD_of_ge _ _ (by simp),hh]
    · exact goodEmpty.2
  · obtain ⟨gs',out,finalSize,finalGood,outBack,finalPres,finalValue⟩ := addOrTop outs empty S gs good earlier
    have plan := fromGood S gs' out finalGood
    refine ⟨⟨gs',out⟩,plan.1,?_,?_,?_⟩
    · intro z
      change wireVal (n+m) gs' z out = _
      rw [finalValue z,meaning z,semantics z]
    · change gs'.length ≤ cap
      have npos : outs.length ≠ 0 := fun h => empty (List.eq_nil_of_length_eq_zero h)
      simp only [costWeight,List.length_nil,Nat.zero_add] at stepCount
      omega
    · exact plan.2
