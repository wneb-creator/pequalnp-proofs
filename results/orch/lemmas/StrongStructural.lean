import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448.cross
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

def cf (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) : List (List ℕ) :=
  gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs

theorem cf_append (n : ℕ) (a b : List Gate) (cs : List (List ℕ)) :
    cf n (a ++ b) cs = cf n b (cf n a cs) := by
  simp [cf, List.foldl_append]

theorem cf_cons (n : ℕ) (g : Gate) (gs : List Gate) (cs : List (List ℕ)) :
    cf n (g :: gs) cs = cf n gs (PEqualNP.EdgeOwnership.coneStep n cs g) := rfl

theorem cs_len (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (PEqualNP.EdgeOwnership.coneStep n cs g).length = cs.length + 1 := by
  unfold PEqualNP.EdgeOwnership.coneStep; simp

theorem cf_len (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)),
    (cf n gs cs).length = cs.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro cs; rfl
  | cons g gs ih =>
    intro cs
    rw [cf_cons, ih, cs_len, List.length_cons]; omega

theorem cf_keep (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ), j < cs.length →
    (cf n gs cs).getD j [] = cs.getD j [] := by
  intro gs
  induction gs with
  | nil => intro cs j _; rfl
  | cons g gs ih =>
    intro cs j hj
    rw [cf_cons, ih _ j (by rw [cs_len]; omega)]
    unfold PEqualNP.EdgeOwnership.coneStep
    exact List.getD_append _ _ _ _ hj

theorem snocD (L : List (List ℕ)) (v : List ℕ) (j : ℕ) (h : L.length = j) :
    (L ++ [v]).getD j [] = v := by
  subst h; simp [List.getD_eq_getElem?_getD]

theorem cone_iff (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) (i : ℕ) :
    i ∈ (cf n gs []).getD j [] ↔ ∃ w ∈ gs[j].inputs, n ≤ w ∧ w < n + j ∧
      (i = w - n ∨ i ∈ (cf n gs []).getD (w - n) []) := by
  have hP : (cf n (gs.take j) []).length = j := by
    rw [cf_len, List.length_take, Nat.min_eq_left (le_of_lt hj)]; simp
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have e : cf n gs [] = cf n (gs.drop (j + 1))
      (PEqualNP.EdgeOwnership.coneStep n (cf n (gs.take j) []) gs[j]) := by
    conv_lhs => rw [hsplit]
    rw [cf_append, cf_cons]
  have hfull : ∀ m, m < j → (cf n gs []).getD m [] = (cf n (gs.take j) []).getD m [] := by
    intro m hm
    rw [e, cf_keep _ _ _ m (by rw [cs_len, hP]; omega)]
    unfold PEqualNP.EdgeOwnership.coneStep
    exact List.getD_append _ _ _ _ (by omega)
  have hj_eq : (cf n gs []).getD j [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cf n (gs.take j) []).length))).flatMap
        (fun w => (w - n) :: (cf n (gs.take j) []).getD (w - n) []) := by
    rw [e, cf_keep _ _ _ j (by rw [cs_len, hP]; omega)]
    unfold PEqualNP.EdgeOwnership.coneStep
    exact snocD _ _ j hP
  rw [hj_eq, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    obtain ⟨hw1, hw2⟩ := List.mem_filter.1 hw
    have hw3 := of_decide_eq_true hw2
    rw [hP] at hw3
    refine ⟨w, hw1, hw3.1, hw3.2, ?_⟩
    rcases List.mem_cons.1 hi with h1 | h1
    · exact Or.inl h1
    · right; rw [hfull _ (by omega)]; exact h1
  · rintro ⟨w, hw1, hw2, hw3, hi⟩
    refine ⟨w, List.mem_filter.2 ⟨hw1, decide_eq_true (by rw [hP]; exact ⟨hw2, hw3⟩)⟩, ?_⟩
    rcases hi with h1 | h1
    · exact List.mem_cons.2 (Or.inl h1)
    · rw [hfull _ (by omega)] at h1
      exact List.mem_cons.2 (Or.inr h1)

theorem cone_lt (n : ℕ) (gs : List Gate) (i j : ℕ) (h : i ∈ (cf n gs []).getD j []) :
    j < gs.length := by
  by_contra hc
  rw [List.getD_eq_default _ _ (by rw [cf_len]; simp; omega)] at h
  cases h

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
theorem valf (n : ℕ) (C : Circuit) (y : Fin n → Bool) (m : ℕ) (hm : m < C.gates.length) :
    gateVal n C m y = (C.gates[m]).op.eval
      (C.gates[m].inputs.map fun i => (wf (C.gates.take m) (List.ofFn y)).getD i false) := by
  have h := gate_val C.gates (List.ofFn y) m hm
  rw [List.length_ofFn] at h
  exact h

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
theorem wire_reach (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (e : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (rec : ∀ j, j < k → (gateAt C j).op = GateOp.or → gateVal n C j e = true →
      (∀ i, InCone n C i j → (gateAt C i).op = GateOp.and → gateVal n C i e = false) →
      ∃ u : Fin n, e u = true ∧ ∀ y : Fin n → Bool, y u = true → gateVal n C j y = true)
    (hown : ∀ i, InCone n C i k → (gateAt C i).op = GateOp.and → gateVal n C i e = false)
    (i : ℕ) (hi : i ∈ C.gates[k].inputs)
    (hv : (wf (C.gates.take k) (List.ofFn e)).getD i false = true) :
    ∃ u : Fin n, e u = true ∧ ∀ y : Fin n → Bool, y u = true →
      (wf (C.gates.take k) (List.ofFn y)).getD i false = true := by
  have hik : i < n + k := by
    by_contra hge
    rw [List.getD_eq_default _ _ (by
      rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hk)]; omega)] at hv
    exact absurd hv (by decide)
  by_cases hin : i < n
  · refine ⟨⟨i, hin⟩, ?_, ?_⟩
    · rw [wf_keep _ _ i (by rw [List.length_ofFn]; exact hin)] at hv
      rw [← getD_ofFn e ⟨i, hin⟩]
      exact hv
    · intro y hy
      rw [wf_keep _ _ i (by rw [List.length_ofFn]; exact hin)]
      rw [← getD_ofFn y ⟨i, hin⟩] at hy
      exact hy
  · have hj : i - n < k := by omega
    have hjl : i - n < C.gates.length := by omega
    have hw : ∀ y : Fin n → Bool, (wf (C.gates.take k) (List.ofFn y)).getD i false
        = gateVal n C (i - n) y := by
      intro y
      rw [← wire_take C.gates (List.ofFn y) k i (by rw [List.length_ofFn]; exact hik) (le_of_lt hk)]
      show _ = (wf C.gates (List.ofFn y)).getD (n + (i - n)) false
      congr 1
      omega
    have hcone : InCone n C (i - n) k :=
      (cone_iff n C.gates k hk (i - n)).2 ⟨i, hi, by omega, hik, Or.inl rfl⟩
    have hop : (gateAt C (i - n)).op = GateOp.or := by
      rw [gateAt_eq C _ hjl]
      rcases (hC _ (List.getElem_mem hjl)).1 with h | h
      · exfalso
        have := hown (i - n) hcone (by rw [gateAt_eq C _ hjl]; exact h)
        rw [← hw e, hv] at this
        exact absurd this (by decide)
      · exact h
    obtain ⟨u, hu1, hu2⟩ := rec (i - n) hj hop (by rw [← hw e]; exact hv)
      (fun i' hc ha => hown i' ((cone_iff n C.gates k hk i').2 ⟨i, hi, by omega, hik, Or.inr hc⟩) ha)
    exact ⟨u, hu1, fun y hy => by rw [hw y]; exact hu2 y hy⟩

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
theorem or_reach (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (e : Fin n → Bool) : ∀ m, m < C.gates.length → (gateAt C m).op = GateOp.or →
      gateVal n C m e = true →
      (∀ i, InCone n C i m → (gateAt C i).op = GateOp.and → gateVal n C i e = false) →
      ∃ u : Fin n, e u = true ∧ ∀ y : Fin n → Bool, y u = true → gateVal n C m y = true := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hop hval hown
    rw [gateAt_eq C m hm] at hop
    have hv2 := hval
    rw [valf n C e m hm, hop] at hv2
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hv2
    obtain ⟨i, hi, hiv⟩ := hv2
    obtain ⟨u, hu1, hu2⟩ := wire_reach n C hC e m hm
      (fun j hj h1 h2 h3 => ih j hj (lt_trans hj hm) h1 h2 h3) hown i hi hiv
    refine ⟨u, hu1, fun y hy => ?_⟩
    rw [valf n C y m hm, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact ⟨i, hi, hu2 y hy⟩

theorem cone_idx (n : ℕ) (gs : List Gate) : ∀ j i, i ∈ (cf n gs []).getD j [] → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i hc
    have hj := cone_lt n gs i j hc
    obtain ⟨w, _, hw1, hw2, hw3⟩ := (cone_iff n gs j hj i).1 hc
    rcases hw3 with e | e
    · omega
    · have := ih (w - n) (by omega) i e
      omega

lemma cross_nonedge : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → ∀ (x8 : ℕ) (x9 x10 x11 x12 : Fin x1), x2.Adj x9 x10 → x2.Adj x11 x12 → PEqualNP.EdgeOwnership.Owns x1 x6 x8 x9 x10 → PEqualNP.EdgeOwnership.Owns x1 x6 x8 x11 x12 → x9 ≠ x11 → x9 ≠ x12 → x10 ≠ x11 → x10 ≠ x12 → ∃ (x21 : Fin x1) (x22 : Fin x1), (x21 = x9 ∨ x21 = x10) ∧ (x22 = x11 ∨ x22 = x12) ∧ ¬x2.Adj x21 x22 ∧ PEqualNP.EdgeOwnership.gateVal x1 x6 x8 (PEqualNP.EdgeOwnership.pairInput x21 x22) = Bool.true := by
  intro n G _ hT hNF C hC k p1 p2 q1 q2 hadj1 hadj2 hO1 hO2 h1 h2 h3 h4
  have pickQ : ∀ a : Fin n, ∃ b : Fin n, (b = q1 ∨ b = q2) ∧ ¬ G.Adj a b := by
    intro a
    by_contra hc
    push Not at hc
    exact hT q1 q2 a hadj2 (hc q2 (Or.inr rfl)).symm (hc q1 (Or.inl rfl))
  have pickP : ∀ b : Fin n, ∃ a : Fin n, (a = p1 ∨ a = p2) ∧ ¬ G.Adj a b := by
    intro b
    by_contra hc
    push Not at hc
    exact hT p1 p2 b hadj1 (hc p2 (Or.inr rfl)) (hc p1 (Or.inl rfl)).symm
  obtain ⟨hk, hop, hv1, hown1⟩ := hO1
  obtain ⟨_, _, hv2, hown2⟩ := hO2
  rw [gateAt_eq C k hk] at hop
  have hown1' : ∀ i, PEqualNP.EdgeOwnership.InCone n C i k →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = GateOp.and →
      PEqualNP.EdgeOwnership.gateVal n C i (PEqualNP.EdgeOwnership.pairInput p1 p2) = false :=
    fun i hc ha => hown1 i (cone_idx n C.gates k i hc) hc ha
  have hown2' : ∀ i, PEqualNP.EdgeOwnership.InCone n C i k →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = GateOp.and →
      PEqualNP.EdgeOwnership.gateVal n C i (PEqualNP.EdgeOwnership.pairInput q1 q2) = false :=
    fun i hc ha => hown2 i (cone_idx n C.gates k i hc) hc ha
  have hall : ∀ e : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C k e = true →
      ∀ i ∈ C.gates[k].inputs, (wf (C.gates.take k) (List.ofFn e)).getD i false = true := by
    intro e he i hi
    rw [valf n C e k hk, hop] at he
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at he
    exact he i hi
  have reach1 : ∀ i ∈ C.gates[k].inputs, ∃ u : Fin n, (u = p1 ∨ u = p2) ∧ ∀ y : Fin n → Bool,
      y u = true → (wf (C.gates.take k) (List.ofFn y)).getD i false = true := by
    intro i hi
    obtain ⟨u, hu1, hu2⟩ := wire_reach n C hC _ k hk
      (fun j hj a b c => or_reach n C hC _ j (lt_trans hj hk) a b c) hown1' i hi (hall _ hv1 i hi)
    exact ⟨u, of_decide_eq_true hu1, hu2⟩
  have reach2 : ∀ i ∈ C.gates[k].inputs, ∃ u : Fin n, (u = q1 ∨ u = q2) ∧ ∀ y : Fin n → Bool,
      y u = true → (wf (C.gates.take k) (List.ofFn y)).getD i false = true := by
    intro i hi
    obtain ⟨u, hu1, hu2⟩ := wire_reach n C hC _ k hk
      (fun j hj a b c => or_reach n C hC _ j (lt_trans hj hk) a b c) hown2' i hi (hall _ hv2 i hi)
    exact ⟨u, of_decide_eq_true hu1, hu2⟩
  have gtrue : ∀ y : Fin n → Bool,
      (∀ i ∈ C.gates[k].inputs, (wf (C.gates.take k) (List.ofFn y)).getD i false = true) →
      PEqualNP.EdgeOwnership.gateVal n C k y = true := by
    intro y hy
    rw [valf n C y k hk, hop]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact hy
  have pl : ∀ a b : Fin n, PEqualNP.EdgeOwnership.pairInput a b a = true :=
    fun a b => decide_eq_true (Or.inl rfl)
  have pr : ∀ a b : Fin n, PEqualNP.EdgeOwnership.pairInput a b b = true :=
    fun a b => decide_eq_true (Or.inr rfl)
  have hlen := (hC _ (List.getElem_mem hk)).2
  match hin : C.gates[k].inputs, hlen with
  | [], _ =>
    obtain ⟨b, hb1, hb2⟩ := pickQ p1
    refine ⟨p1, b, Or.inl rfl, hb1, hb2, gtrue _ ?_⟩
    intro i hi
    rw [hin] at hi
    cases hi
  | [i1], _ =>
    obtain ⟨u, hu0, hu⟩ := reach1 i1 (by rw [hin]; simp)
    obtain ⟨b, hb1, hb2⟩ := pickQ u
    refine ⟨u, b, hu0, hb1, hb2, gtrue _ ?_⟩
    intro i hi
    rw [hin] at hi
    rw [List.mem_singleton.1 hi]
    exact hu _ (pl u b)
  | [i1, i2], _ =>
    obtain ⟨u1, hu1, hU1⟩ := reach1 i1 (by rw [hin]; simp)
    obtain ⟨u2, hu2, hU2⟩ := reach1 i2 (by rw [hin]; simp)
    obtain ⟨w1, hw1, hW1⟩ := reach2 i1 (by rw [hin]; simp)
    obtain ⟨w2, hw2, hW2⟩ := reach2 i2 (by rw [hin]; simp)
    have two : ∀ (a b : Fin n) (y : Fin n → Bool), y a = true → y b = true →
        (∀ z : Fin n → Bool, z a = true → (wf (C.gates.take k) (List.ofFn z)).getD i1 false = true) →
        (∀ z : Fin n → Bool, z b = true → (wf (C.gates.take k) (List.ofFn z)).getD i2 false = true) →
        PEqualNP.EdgeOwnership.gateVal n C k y = true := by
      intro a b y ha hb hA hB
      apply gtrue
      intro i hi
      rw [hin] at hi
      rcases List.mem_pair.1 hi with e | e
      · rw [e]; exact hA y ha
      · rw [e]; exact hB y hb
    by_cases c1 : G.Adj u1 w2
    swap
    · exact ⟨u1, w2, hu1, hw2, c1, two u1 w2 _ (pl _ _) (pr _ _) hU1 hW2⟩
    by_cases c2 : G.Adj w1 u2
    swap
    · exact ⟨u2, w1, hu2, hw1, fun h => c2 h.symm, two w1 u2 (PEqualNP.EdgeOwnership.pairInput u2 w1) (pr _ _) (pl _ _) hW1 hU2⟩
    by_cases c3 : u1 = u2
    · obtain ⟨b, hb1, hb2⟩ := pickQ u1
      exact ⟨u1, b, hu1, hb1, hb2, two u1 u1 (PEqualNP.EdgeOwnership.pairInput u1 b) (pl _ _) (pl _ _) hU1 (c3 ▸ hU2)⟩
    by_cases c4 : w1 = w2
    · obtain ⟨a, ha1, ha2⟩ := pickP w1
      exact ⟨a, w1, ha1, hw1, ha2, two w1 w1 (PEqualNP.EdgeOwnership.pairInput a w1) (pr _ _) (pr _ _) hW1 (c4 ▸ hW2)⟩
    exfalso
    have a12 : G.Adj u1 u2 := by
      rcases hu1 with e1 | e1 <;> rcases hu2 with e2 | e2
      · exact absurd (e1.trans e2.symm) c3
      · rw [e1, e2]; exact hadj1
      · rw [e1, e2]; exact hadj1.symm
      · exact absurd (e1.trans e2.symm) c3
    have b12 : G.Adj w1 w2 := by
      rcases hw1 with e1 | e1 <;> rcases hw2 with e2 | e2
      · exact absurd (e1.trans e2.symm) c4
      · rw [e1, e2]; exact hadj2
      · rw [e1, e2]; exact hadj2.symm
      · exact absurd (e1.trans e2.symm) c4
    have hne : u1 ≠ w1 := by
      rcases hu1 with e1 | e1 <;> rcases hw1 with e2 | e2 <;> rw [e1, e2]
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    have hne2 : u2 ≠ w2 := by
      rcases hu2 with e1 | e1 <;> rcases hw2 with e2 | e2 <;> rw [e1, e2]
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    have hcard := hNF u1 w1 hne
    have : 1 < (Finset.univ.filter fun w => G.Adj u1 w ∧ G.Adj w1 w).card :=
      Finset.one_lt_card.2 ⟨u2, Finset.mem_filter.2 ⟨Finset.mem_univ _, a12, c2⟩,
        w2, Finset.mem_filter.2 ⟨Finset.mem_univ _, c1, b12⟩, hne2⟩
    omega
  | _ :: _ :: _ :: _, h => exact absurd h (by simp)

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma star_of_proper_pair_sound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hm : Monotone2 C)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ u v : Fin n, u ≠ v → gateVal n C j (pairInput u v) = true → G.Adj u v) :
    HasStarProfile n G C := by
  classical
  intro j hj hjand
  have hmeet (u v p q : Fin n) (huv : G.Adj u v) (hpq : G.Adj p q)
      (h1 : Owns n C j u v) (h2 : Owns n C j p q) :
      u = p ∨ u = q ∨ v = p ∨ v = q := by
    by_contra hn
    push Not at hn
    obtain ⟨a, b, ha, hb, hab, hval⟩ :=
      cross_nonedge n G htri hfour C hm j u v p q huv hpq h1 h2 hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
    have hne : a ≠ b := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> tauto
    exact hab (hclean j hj hjand a b hne hval)
  by_cases used : ∃ a b, G.Adj a b ∧ Owns n C j a b
  · right
    obtain ⟨a, b, hab, hoab⟩ := used
    by_cases ha : ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = a ∨ v = a
    · exact ⟨a, ha⟩
    · push Not at ha
      obtain ⟨p, q, hpq, hopq, hpa, hqa⟩ := ha
      have hbpq : p = b ∨ q = b := by
        have h := hmeet p q a b hpq hab hopq hoab
        tauto
      have hext : ∃ w : Fin n, w ≠ a ∧ G.Adj b w ∧
          ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = b ∨ v = b ∨ u = w ∨ v = w := by
        rcases hbpq with rfl | rfl
        · refine ⟨q, hqa, hpq, ?_⟩
          intro u v huv hov
          have h := hmeet u v p q huv hpq hov hopq
          tauto
        · refine ⟨p, hpa, hpq.symm, ?_⟩
          intro u v huv hov
          have h := hmeet u v p q huv hpq hov hopq
          tauto
      obtain ⟨w, hwa, hbw, hmeetw⟩ := hext
      refine ⟨b, ?_⟩
      intro u v huv hov
      by_contra hn
      push Not at hn
      have huva : u = a ∨ v = a := by
        have h := hmeet u v a b huv hab hov hoab
        tauto
      have huvw : u = w ∨ v = w := by
        have h := hmeetw u v huv hov
        tauto
      have hwaAdj : G.Adj w a := by
        rcases huva with h | h
        · subst u
          have hvw : v = w := huvw.resolve_left (Ne.symm hwa)
          simpa [hvw] using huv.symm
        · subst v
          have huw : u = w := huvw.resolve_right (Ne.symm hwa)
          simpa [huw] using huv
      exact htri a b w hab hbw hwaAdj
  · left
    exact fun u v huv ho => used ⟨u, v, huv, ho⟩


end PEqualNP.Outside.L_meta_2448.cross
