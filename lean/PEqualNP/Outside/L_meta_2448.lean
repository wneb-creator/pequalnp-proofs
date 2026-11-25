import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

lemma wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

def build (n : ℕ) : List (Fin n × Fin n) → List Gate
  | [] => [⟨GateOp.or, []⟩]
  | e :: es => build n es ++ [⟨GateOp.and, [(e.1 : ℕ), (e.2 : ℕ)]⟩,
      ⟨GateOp.or, [n + 2 * es.length, n + 2 * es.length + 1]⟩]

lemma build_len (n : ℕ) : ∀ E : List (Fin n × Fin n), (build n E).length = 1 + 2 * E.length := by
  intro E
  induction E with
  | nil => rfl
  | cons e es ih => simp [build, ih]; omega

lemma build_mono (n : ℕ) : ∀ E : List (Fin n × Fin n), ∀ g ∈ build n E,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro E
  induction E with
  | nil => intro g hg; simp [build] at hg; subst hg; simp
  | cons e es ih =>
    intro g hg
    simp only [build, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact ih g hg
    · simp
    · simp

lemma build_val (n : ℕ) (x : Fin n → Bool) : ∀ E : List (Fin n × Fin n),
    (wf (build n E) (List.ofFn x)).getD (n + 2 * E.length) false
      = E.any (fun e => x e.1 && x e.2) := by
  intro E
  induction E with
  | nil =>
    show ((List.ofFn x) ++ [GateOp.eval GateOp.or ([].map fun i => (List.ofFn x).getD i false)]).getD (n + 2 * 0) false = _
    have := getD_snoc_eq (List.ofFn x) (GateOp.eval GateOp.or ([].map fun i => (List.ofFn x).getD i false))
    rw [List.length_ofFn] at this
    rw [Nat.mul_zero, Nat.add_zero, this]
    rfl
  | cons e es ih =>
    have hlen : (wf (build n es) (List.ofFn x)).length = n + 2 * es.length + 1 := by
      rw [wf_len, build_len, List.length_ofFn]; omega
    have h1 : (wf (build n es) (List.ofFn x)).getD (e.1 : ℕ) false = x e.1 := by
      rw [wf_keep _ _ _ (by simp)]; simp
    have h2 : (wf (build n es) (List.ofFn x)).getD (e.2 : ℕ) false = x e.2 := by
      rw [wf_keep _ _ _ (by simp)]; simp
    show (wf (build n es ++ [⟨GateOp.and, [(e.1 : ℕ), (e.2 : ℕ)]⟩,
      ⟨GateOp.or, [n + 2 * es.length, n + 2 * es.length + 1]⟩]) (List.ofFn x)).getD
        (n + 2 * (es.length + 1)) false = _
    rw [wf_append]
    generalize hW : wf (build n es) (List.ofFn x) = W at *
    show ((W ++ [GateOp.eval GateOp.and ([(e.1 : ℕ), (e.2 : ℕ)].map fun i => W.getD i false)]) ++
      [GateOp.eval GateOp.or ([n + 2 * es.length, n + 2 * es.length + 1].map fun i =>
        (W ++ [GateOp.eval GateOp.and ([(e.1 : ℕ), (e.2 : ℕ)].map fun i => W.getD i false)]).getD i false)]).getD
        (n + 2 * (es.length + 1)) false = _
    have e3 : n + 2 * (es.length + 1) = (W ++ [GateOp.eval GateOp.and ([(e.1 : ℕ), (e.2 : ℕ)].map fun i => W.getD i false)]).length := by
      simp [hlen]; omega
    rw [e3, getD_snoc_eq]
    have e4 : n + 2 * es.length + 1 = W.length := by omega
    simp only [List.map_cons, List.map_nil]
    rw [getD_snoc_lt _ _ _ (by omega : n + 2 * es.length < W.length), e4, getD_snoc_eq, ih, h1, h2]
    simp [GateOp.eval, Bool.or_comm]

lemma minimal_exists : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x4 ∧ PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ := by
  classical
  intro n G _
  have hex : ∃ s : ℕ, ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ D.size = s := by
    let E : List (Fin n × Fin n) :=
      ((List.finRange n).product (List.finRange n)).filter (fun e => decide (G.Adj e.1 e.2))
    refine ⟨_, ⟨build n E, n + 2 * E.length⟩, build_mono n E, ?_, rfl⟩
    funext x
    show (wf (build n E) (List.ofFn x)).getD (n + 2 * E.length) false = _
    rw [build_val, Bool.eq_iff_iff]
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, List.any_eq_true, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false, false_or]
    constructor
    · rintro ⟨e, he, h1, h2⟩
      have := (List.mem_filter.mp he).2
      exact ⟨e.1, e.2, by simpa using this, h1, h2⟩
    · rintro ⟨u, v, huv, h1, h2⟩
      exact ⟨(u, v), List.mem_filter.mpr ⟨by simp [List.pair_mem_product], by simpa using huv⟩, h1, h2⟩
  obtain ⟨D, hD, hf, hs⟩ := Nat.find_spec hex
  refine ⟨D, ⟨hD, ?_⟩, hf⟩
  intro D' hD' hf'
  rw [hs]
  exact Nat.find_min' hex ⟨D', hD', hf'.trans hf, rfl⟩

end PEqualNP.Outside.L_meta_2448_aux

namespace PEqualNP.Outside.L_meta_2448.cross
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

lemma getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

def cf (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) : List (List ℕ) :=
  gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs

lemma cf_append (n : ℕ) (a b : List Gate) (cs : List (List ℕ)) :
    cf n (a ++ b) cs = cf n b (cf n a cs) := by
  simp [cf, List.foldl_append]

lemma cf_cons (n : ℕ) (g : Gate) (gs : List Gate) (cs : List (List ℕ)) :
    cf n (g :: gs) cs = cf n gs (PEqualNP.EdgeOwnership.coneStep n cs g) := rfl

lemma cs_len (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (PEqualNP.EdgeOwnership.coneStep n cs g).length = cs.length + 1 := by
  unfold PEqualNP.EdgeOwnership.coneStep; simp

lemma cf_len (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)),
    (cf n gs cs).length = cs.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro cs; rfl
  | cons g gs ih =>
    intro cs
    rw [cf_cons, ih, cs_len, List.length_cons]; omega

lemma cf_keep (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ), j < cs.length →
    (cf n gs cs).getD j [] = cs.getD j [] := by
  intro gs
  induction gs with
  | nil => intro cs j _; rfl
  | cons g gs ih =>
    intro cs j hj
    rw [cf_cons, ih _ j (by rw [cs_len]; omega)]
    unfold PEqualNP.EdgeOwnership.coneStep
    exact List.getD_append _ _ _ _ hj

lemma snocD (L : List (List ℕ)) (v : List ℕ) (j : ℕ) (h : L.length = j) :
    (L ++ [v]).getD j [] = v := by
  subst h; simp [List.getD_eq_getElem?_getD]

lemma cone_iff (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) (i : ℕ) :
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

lemma cone_lt (n : ℕ) (gs : List Gate) (i j : ℕ) (h : i ∈ (cf n gs []).getD j []) :
    j < gs.length := by
  by_contra hc
  rw [List.getD_eq_default _ _ (by rw [cf_len]; simp; omega)] at h
  cases h

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
lemma valf (n : ℕ) (C : Circuit) (y : Fin n → Bool) (m : ℕ) (hm : m < C.gates.length) :
    gateVal n C m y = (C.gates[m]).op.eval
      (C.gates[m].inputs.map fun i => (wf (C.gates.take m) (List.ofFn y)).getD i false) := by
  have h := gate_val C.gates (List.ofFn y) m hm
  rw [List.length_ofFn] at h
  exact h

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
lemma wire_reach (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
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
lemma or_reach (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
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

lemma cone_idx (n : ℕ) (gs : List Gate) : ∀ j i, i ∈ (cf n gs []).getD j [] → i < j := by
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

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma owns_bipartite_on_singleton_silent (n : ℕ) (C : Circuit) (j : ℕ)
    (S : Set (Fin n))
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hs : ∀ u ∈ S, gateVal n C j (pairInput u u) = false) :
    ∃ color : Fin n → Bool, ∀ u ∈ S, ∀ v ∈ S,
      Owns n C j u v → color u ≠ color v := by
  by_cases hex : ∃ u ∈ S, ∃ v ∈ S, Owns n C j u v
  · obtain ⟨u0, hu0, v0, hv0, ho⟩ := hex
    have hj := ho.1
    have hop := ho.2.1
    rw [gateAt_eq C j hj] at hop
    let val (i : ℕ) (u : Fin n) :=
      (wf (C.gates.take j) (List.ofFn (pairInput u u))).getD i false
    have polar (u v : Fin n) (ho : Owns n C j u v) (i : ℕ)
        (hi : i ∈ C.gates[j].inputs) : val i u = true ∨ val i v = true := by
      have hown : ∀ k, InCone n C k j → (gateAt C k).op = GateOp.and →
          gateVal n C k (pairInput u v) = false :=
        fun k hc ha => ho.2.2.2 k (cone_idx n C.gates j k hc) hc ha
      have hv := ho.2.2.1
      rw [valf n C _ j hj, hop] at hv
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hv
      obtain ⟨w, hw, hr⟩ := wire_reach n C hm _ j hj
        (fun k hk a b c => or_reach n C hm _ k (lt_trans hk hj) a b c)
        hown i hi (hv i hi)
      have hwu : w = u ∨ w = v := of_decide_eq_true hw
      rcases hwu with rfl | rfl
      · exact Or.inl (hr _ (by simp [pairInput]))
      · exact Or.inr (hr _ (by simp [pairInput]))
    have silent (u : Fin n) (hu : u ∈ S) (hr : ∀ i ∈ C.gates[j].inputs, val i u = true) : False := by
      have hv : gateVal n C j (pairInput u u) = true := by
        rw [valf n C _ j hj, hop]
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
        exact hr
      rw [hs u hu] at hv
      contradiction
    have hlen := (hm _ (List.getElem_mem hj)).2
    match hin : C.gates[j].inputs, hlen with
    | [], _ => exact (silent u0 hu0 (by simp [hin])).elim
    | [p], _ =>
      rcases polar u0 v0 ho p (by simp [hin]) with hu | hv
      · exact (silent u0 hu0 (by simpa [hin] using hu)).elim
      · exact (silent v0 hv0 (by simpa [hin] using hv)).elim
    | [p, q], _ =>
      have separate (u : Fin n) (hu : u ∈ S) (hp : val p u = true) (hq : val q u = true) : False := by
        apply silent u hu
        intro i hi
        rcases (by simpa only [hin, List.mem_cons, List.not_mem_nil, or_false] using hi :
            i = p ∨ i = q) with rfl | rfl
        · exact hp
        · exact hq
      refine ⟨val p, ?_⟩
      intro u hu v hv huv he
      have hup := polar u v huv p (by simp [hin])
      have huq := polar u v huv q (by simp [hin])
      rcases hup with hup | hvp <;> rcases huq with huq | hvq
      · exact separate u hu hup huq
      · exact separate v hv (he ▸ hup) hvq
      · exact separate u hu (he.symm ▸ hvp) huq
      · exact separate v hv hvp hvq
    | _ :: _ :: _ :: _, h => simp at h
  · refine ⟨fun _ => false, ?_⟩
    intro u hu v hv ho
    exact (hex ⟨u, hu, v, hv, ho⟩).elim

lemma owns_bipartite_of_singleton_silent (n : ℕ) (C : Circuit) (j : ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hs : ∀ u : Fin n, gateVal n C j (pairInput u u) = false) :
    ∃ color : Fin n → Bool, ∀ u v : Fin n,
      Owns n C j u v → color u ≠ color v := by
  obtain ⟨color, hc⟩ := owns_bipartite_on_singleton_silent n C j Set.univ hm (fun u _ => hs u)
  exact ⟨color, fun u v ho => hc u (Set.mem_univ u) v (Set.mem_univ v) ho⟩

lemma odd_owned_closed_walk_has_singleton (n : ℕ) (C : Circuit) (j k : ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (p : ℕ → Fin n)
    (hclosed : p (2 * k + 1) = p 0)
    (hown : ∀ i < 2 * k + 1, Owns n C j (p i) (p (i + 1))) :
    ∃ i ≤ 2 * k + 1, gateVal n C j (pairInput (p i) (p i)) = true := by
  by_contra! hnone
  let S : Set (Fin n) := {u | ∃ i ≤ 2 * k + 1, p i = u}
  have hs : ∀ u ∈ S, gateVal n C j (pairInput u u) = false := by
    rintro u ⟨i, hi, rfl⟩
    exact Bool.eq_false_iff.mpr (hnone i hi)
  obtain ⟨color, hc⟩ := owns_bipartite_on_singleton_silent n C j S hm hs
  have step (i : ℕ) (hi : i < 2 * k + 1) : color (p i) ≠ color (p (i + 1)) :=
    hc (p i) ⟨i, by omega, rfl⟩ (p (i + 1)) ⟨i + 1, by omega, rfl⟩ (hown i hi)
  have two (a b c : Bool) (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
    cases a <;> cases b <;> cases c <;> simp_all
  have even (m : ℕ) (hmk : m ≤ k) : color (p (2 * m)) = color (p 0) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      have h1 := step (2 * m) (by omega)
      have h2 := step (2 * m + 1) (by omega)
      have he := two _ _ _ h1 h2
      calc
        color (p (2 * (m + 1))) = color (p (2 * m)) := by
          convert he.symm using 1
        _ = color (p 0) := ih (by omega)
  have hlast := step (2 * k) (by omega)
  rw [hclosed, even k (le_refl k)] at hlast
  exact hlast rfl

end PEqualNP.Outside.L_meta_2448.cross

namespace PEqualNP.Outside.L_meta_2448.diamond

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wide (n s a b : ℕ) : Circuit :=
  ⟨[⟨.or, [s,a]⟩, ⟨.or, [s,b]⟩, ⟨.and, [n,n+1]⟩], n+2⟩

def narrow (n s a b : ℕ) : Circuit :=
  ⟨[⟨.and, [a,b]⟩, ⟨.or, [s,n]⟩], n+1⟩

lemma read_append_left (w v : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ v).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma read_snoc_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma diamond_eval (w : List Bool) (s a b : ℕ)
    (hs : s < w.length) (ha : a < w.length) (hb : b < w.length) :
    (wide w.length s a b).eval w = (narrow w.length s a b).eval w := by
  simp [wide, narrow, Circuit.eval, Circuit.wires, GateOp.eval,
    List.getElem?_append_left hs, List.getElem?_append_left hb, hs, ha, hb]
  cases w[s] <;> cases w[a] <;> cases w[b] <;> rfl


lemma not_minimal_wide (n s a b : ℕ) (hs : s < n) (ha : a < n) (hb : b < n) :
    ¬ IsMinimalMonoCircuit n (wide n s a b) := by
  intro h
  have hM : Monotone2 (narrow n s a b) := by
    simp [Monotone2, narrow]
  have hF : circuitFun n (narrow n s a b) = circuitFun n (wide n s a b) := by
    funext x
    simpa [circuitFun] using (diamond_eval (List.ofFn x) s a b (by simpa) (by simpa) (by simpa)).symm
  have hsize := h.2 (narrow n s a b) hM hF
  change 3 ≤ 2 at hsize
  omega


def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wf (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma wf_length (gs : List Gate) (w : List Bool) :
    (wf gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wf gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma wf_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wf gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wf gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact read_append_left _ _ _ hi

def rew (m i : ℕ) : ℕ := if m+2 ≤ i then i-1 else i

def renGate (m : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rew m)⟩

def Agree (m : ℕ) (A B : List Bool) : Prop :=
  A.length = B.length + 1 ∧ m+2 < A.length ∧
    ∀ i, i ≠ m → i ≠ m+1 → A.getD i false = B.getD (rew m i) false

lemma agree_append (m : ℕ) (A B : List Bool) (v : Bool) (h : Agree m A B) :
    Agree m (A ++ [v]) (B ++ [v]) := by
  obtain ⟨hlen, hlong, hread⟩ := h
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro i hi hi1
  by_cases hlt : i < A.length
  · have hlt' : rew m i < B.length := by
      unfold rew
      split_ifs <;> omega
    rw [read_append_left _ _ _ hlt, read_append_left _ _ _ hlt']
    exact hread i hi hi1
  · by_cases he : i = A.length
    · subst i
      have hr : rew m A.length = B.length := by
        simp only [rew, ite_eq_left (by omega : m + 2 ≤ A.length)]
        omega
      rw [hr, read_snoc_last, read_snoc_last]
    · have ha : (A ++ [v]).length ≤ i := by simp; omega
      have hb : (B ++ [v]).length ≤ rew m i := by
        simp only [List.length_append, List.length_singleton, rew]
        split_ifs <;> omega
      rw [List.getD_eq_default _ _ ha, List.getD_eq_default _ _ hb]

lemma agree_step (m : ℕ) (A B : List Bool) (g : Gate) (h : Agree m A B)
    (hread : ∀ i ∈ g.inputs, i ≠ m ∧ i ≠ m+1) :
    Agree m (step A g) (step B (renGate m g)) := by
  have hv : g.op.eval (g.inputs.map fun i => A.getD i false) =
      (renGate m g).op.eval ((renGate m g).inputs.map fun i => B.getD i false) := by
    simp only [renGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h.2.2 i (hread i hi).1 (hread i hi).2
  unfold step
  rw [← hv]
  exact agree_append m A B _ h

lemma agree_fold (m : ℕ) (A B : List Bool) (gs : List Gate) (h : Agree m A B)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ≠ m ∧ i ≠ m+1) :
    Agree m (wf gs A) (wf (gs.map (renGate m)) B) := by
  induction gs generalizing A B with
  | nil => exact h
  | cons g gs ih =>
    change Agree m (wf gs (step A g)) (wf (gs.map (renGate m)) (step B (renGate m g)))
    exact ih _ _ (agree_step m A B g h (hread g List.mem_cons_self))
      (fun g hg => hread g (List.mem_cons_of_mem _ hg))


lemma initial_agree (w : List Bool) (s a b : ℕ)
    (hs : s < w.length) (ha : a < w.length) (hb : b < w.length) :
    Agree w.length (wf (wide w.length s a b).gates w)
      (wf (narrow w.length s a b).gates w) := by
  have hL : (wf (wide w.length s a b).gates w).length = w.length + 3 := by
    simp [wf_length, wide]
  have hL' : (wf (narrow w.length s a b).gates w).length = w.length + 2 := by
    simp [wf_length, narrow]
  refine ⟨by omega, by omega, ?_⟩
  intro i hi hi1
  by_cases hlt : i < w.length
  · have hr : rew w.length i = i := by simp [rew]; omega
    rw [hr, wf_keep _ _ _ hlt, wf_keep _ _ _ hlt]
  · by_cases he : i = w.length+2
    · subst i
      have hr : rew w.length (w.length+2) = w.length+1 := by simp [rew]
      rw [hr]
      exact diamond_eval w s a b hs ha hb
    · have hge : (wf (wide w.length s a b).gates w).length ≤ i := by omega
      have hge' : (wf (narrow w.length s a b).gates w).length ≤ rew w.length i := by
        unfold rew
        split_ifs <;> omega
      rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ hge']

def oldCircuit (n : ℕ) (pre post : List Gate) (s a b output : ℕ) : Circuit :=
  ⟨pre ++ (wide (n+pre.length) s a b).gates ++ post, output⟩

def newCircuit (n : ℕ) (pre post : List Gate) (s a b output : ℕ) : Circuit :=
  ⟨pre ++ (narrow (n+pre.length) s a b).gates ++ post.map (renGate (n+pre.length)),
    rew (n+pre.length) output⟩

lemma repair_fun (n : ℕ) (pre post : List Gate) (s a b output : ℕ)
    (hs : s < n+pre.length) (ha : a < n+pre.length) (hb : b < n+pre.length)
    (hread : ∀ g ∈ post, ∀ i ∈ g.inputs, i ≠ n+pre.length ∧ i ≠ n+pre.length+1)
    (hout : output ≠ n+pre.length) (hout1 : output ≠ n+pre.length+1) :
    circuitFun n (oldCircuit n pre post s a b output) =
      circuitFun n (newCircuit n pre post s a b output) := by
  funext x
  let w := wf pre (List.ofFn x)
  have hw : w.length = n+pre.length := by simp [w, wf_length]
  have hA : Agree (n+pre.length) (wf (wide (n+pre.length) s a b).gates w)
      (wf (narrow (n+pre.length) s a b).gates w) := by
    rw [← hw]
    exact initial_agree w s a b (by simpa [hw]) (by simpa [hw]) (by simpa [hw])
  have hF := agree_fold (n+pre.length) _ _ post hA hread
  have result := hF.2.2 output hout hout1
  have hstep : step = (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
  simp only [wf, w, hstep] at result
  simpa only [circuitFun, Circuit.eval, Circuit.wires, oldCircuit, newCircuit,
    List.foldl_append] using result

lemma repair_mono (n : ℕ) (pre post : List Gate) (s a b output : ℕ)
    (hm : Monotone2 (oldCircuit n pre post s a b output)) :
    Monotone2 (newCircuit n pre post s a b output) := by
  intro g hg
  change g ∈ pre ++ (narrow (n+pre.length) s a b).gates ++ post.map (renGate (n+pre.length)) at hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_append.mp hg with hp | hn
    · exact hm g (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hp))))
    · have hnarrow : Monotone2 (narrow (n+pre.length) s a b) := by simp [Monotone2, narrow]
      exact hnarrow g hn
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have h' := hm g' (List.mem_append.mpr (Or.inr hg'))
    simpa [renGate] using h'

lemma repair_size (n : ℕ) (pre post : List Gate) (s a b output : ℕ) :
    (newCircuit n pre post s a b output).size + 1 = (oldCircuit n pre post s a b output).size := by
  simp [newCircuit, oldCircuit, narrow, wide, Circuit.size]
  omega

lemma not_minimal_diamond (n : ℕ) (pre post : List Gate) (s a b output : ℕ)
    (hs : s < n+pre.length) (ha : a < n+pre.length) (hb : b < n+pre.length)
    (hread : ∀ g ∈ post, ∀ i ∈ g.inputs, i ≠ n+pre.length ∧ i ≠ n+pre.length+1)
    (hout : output ≠ n+pre.length) (hout1 : output ≠ n+pre.length+1) :
    ¬ IsMinimalMonoCircuit n (oldCircuit n pre post s a b output) := by
  intro h
  have hsize := h.2 (newCircuit n pre post s a b output) (repair_mono n pre post s a b output h.1)
    (repair_fun n pre post s a b output hs ha hb hread hout hout1).symm
  have he := repair_size n pre post s a b output
  omega

end PEqualNP.Outside.L_meta_2448.diamond

namespace PEqualNP.Outside.L_meta_2448.matching

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wide (n p q a b c d : ℕ) : Circuit :=
  ⟨[⟨.and, [p,q]⟩, ⟨.or, [a,d]⟩, ⟨.or, [b,c]⟩,
    ⟨.and, [n+1,n+2]⟩, ⟨.and, [n,n+3]⟩], n+4⟩

def narrow (n a b c d : ℕ) : Circuit :=
  ⟨[⟨.and, [a,b]⟩, ⟨.and, [c,d]⟩, ⟨.or, [n,n+1]⟩], n+2⟩

lemma read_append_left (w v : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ v).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma read_snoc_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma matching_eval (w : List Bool) (p q a b c d : ℕ)
    (hp : p < w.length) (hq : q < w.length)
    (ha : a < w.length) (hb : b < w.length) (hc : c < w.length) (hd : d < w.length)
    (hP : w.getD p false = (w.getD a false || w.getD c false))
    (hQ : w.getD q false = (w.getD b false || w.getD d false)) :
    (wide w.length p q a b c d).eval w = (narrow w.length a b c d).eval w := by
  have hP' : w[p] = (w[a] || w[c]) := by
    simpa [List.getD_eq_getElem?_getD, hp, ha, hc] using hP
  have hQ' : w[q] = (w[b] || w[d]) := by
    simpa [List.getD_eq_getElem?_getD, hq, hb, hd] using hQ
  simp [wide, narrow, Circuit.eval, Circuit.wires, GateOp.eval,
    List.getElem?_append_left ha, List.getElem?_append_left hb,
    List.getElem?_append_left hc, List.getElem?_append_left hd,
    hp, hq, ha, hb, hc, hd, hP', hQ']
  cases w[a] <;> cases w[b] <;> cases w[c] <;> cases w[d] <;> rfl

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wf (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma wf_length (gs : List Gate) (w : List Bool) :
    (wf gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wf gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma wf_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wf gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wf gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact read_append_left _ _ _ hi

def rew (m i : ℕ) : ℕ := if m+4 ≤ i then i-2 else i

def renGate (m : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rew m)⟩

def Agree (m : ℕ) (A B : List Bool) : Prop :=
  A.length = B.length + 2 ∧ m+4 < A.length ∧
    ∀ i, (i < m ∨ m+4 ≤ i) → A.getD i false = B.getD (rew m i) false

lemma agree_append (m : ℕ) (A B : List Bool) (v : Bool) (h : Agree m A B) :
    Agree m (A ++ [v]) (B ++ [v]) := by
  obtain ⟨hlen, hlong, hread⟩ := h
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro i hi
  by_cases hlt : i < A.length
  · have hlt' : rew m i < B.length := by
      unfold rew
      split_ifs <;> omega
    rw [read_append_left _ _ _ hlt, read_append_left _ _ _ hlt']
    exact hread i hi
  · by_cases he : i = A.length
    · subst i
      have hr : rew m A.length = B.length := by
        simp only [rew, ite_eq_left (by omega : m + 4 ≤ A.length)]
        omega
      rw [hr, read_snoc_last, read_snoc_last]
    · have ha : (A ++ [v]).length ≤ i := by simp; omega
      have hb : (B ++ [v]).length ≤ rew m i := by
        simp only [List.length_append, List.length_singleton, rew]
        split_ifs <;> omega
      rw [List.getD_eq_default _ _ ha, List.getD_eq_default _ _ hb]

lemma agree_step (m : ℕ) (A B : List Bool) (g : Gate) (h : Agree m A B)
    (hread : ∀ i ∈ g.inputs, i < m ∨ m+4 ≤ i) :
    Agree m (step A g) (step B (renGate m g)) := by
  have hv : g.op.eval (g.inputs.map fun i => A.getD i false) =
      (renGate m g).op.eval ((renGate m g).inputs.map fun i => B.getD i false) := by
    simp only [renGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h.2.2 i (hread i hi)
  unfold step
  rw [← hv]
  exact agree_append m A B _ h

lemma agree_fold (m : ℕ) (A B : List Bool) (gs : List Gate) (h : Agree m A B)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < m ∨ m+4 ≤ i) :
    Agree m (wf gs A) (wf (gs.map (renGate m)) B) := by
  induction gs generalizing A B with
  | nil => exact h
  | cons g gs ih =>
    change Agree m (wf gs (step A g)) (wf (gs.map (renGate m)) (step B (renGate m g)))
    exact ih _ _ (agree_step m A B g h (hread g List.mem_cons_self))
      (fun g hg => hread g (List.mem_cons_of_mem _ hg))

lemma initial_agree (w : List Bool) (p q a b c d : ℕ)
    (hp : p < w.length) (hq : q < w.length)
    (ha : a < w.length) (hb : b < w.length) (hc : c < w.length) (hd : d < w.length)
    (hP : w.getD p false = (w.getD a false || w.getD c false))
    (hQ : w.getD q false = (w.getD b false || w.getD d false)) :
    Agree w.length (wf (wide w.length p q a b c d).gates w)
      (wf (narrow w.length a b c d).gates w) := by
  have hL : (wf (wide w.length p q a b c d).gates w).length = w.length + 5 := by
    simp [wf_length, wide]
  have hL' : (wf (narrow w.length a b c d).gates w).length = w.length + 3 := by
    simp [wf_length, narrow]
  refine ⟨by omega, by omega, ?_⟩
  intro i hi
  by_cases hlt : i < w.length
  · have hr : rew w.length i = i := by simp [rew]; omega
    rw [hr, wf_keep _ _ _ hlt, wf_keep _ _ _ hlt]
  · by_cases he : i = w.length+4
    · subst i
      have hr : rew w.length (w.length+4) = w.length+2 := by simp [rew]
      rw [hr]
      exact matching_eval w p q a b c d hp hq ha hb hc hd hP hQ
    · have hge : (wf (wide w.length p q a b c d).gates w).length ≤ i := by omega
      have hge' : (wf (narrow w.length a b c d).gates w).length ≤ rew w.length i := by
        unfold rew
        split_ifs <;> omega
      rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ hge']


def oldCircuit (n : ℕ) (pre post : List Gate) (p q a b c d output : ℕ) : Circuit :=
  ⟨pre ++ (wide (n+pre.length) p q a b c d).gates ++ post, output⟩

def newCircuit (n : ℕ) (pre post : List Gate) (a b c d output : ℕ) : Circuit :=
  ⟨pre ++ (narrow (n+pre.length) a b c d).gates ++ post.map (renGate (n+pre.length)),
    rew (n+pre.length) output⟩

lemma repair_fun (n : ℕ) (pre post : List Gate) (p q a b c d output : ℕ)
    (hp : p < n+pre.length) (hq : q < n+pre.length)
    (ha : a < n+pre.length) (hb : b < n+pre.length) (hc : c < n+pre.length) (hd : d < n+pre.length)
    (hP : ∀ x : Fin n → Bool, let w := wf pre (List.ofFn x)
      w.getD p false = (w.getD a false || w.getD c false))
    (hQ : ∀ x : Fin n → Bool, let w := wf pre (List.ofFn x)
      w.getD q false = (w.getD b false || w.getD d false))
    (hread : ∀ g ∈ post, ∀ i ∈ g.inputs, i < n+pre.length ∨ n+pre.length+4 ≤ i)
    (hout : output < n+pre.length ∨ n+pre.length+4 ≤ output) :
    circuitFun n (oldCircuit n pre post p q a b c d output) =
      circuitFun n (newCircuit n pre post a b c d output) := by
  funext x
  let w := wf pre (List.ofFn x)
  have hw : w.length = n+pre.length := by simp [w, wf_length]
  have hA : Agree (n+pre.length) (wf (wide (n+pre.length) p q a b c d).gates w)
      (wf (narrow (n+pre.length) a b c d).gates w) := by
    rw [← hw]
    exact initial_agree w p q a b c d (by simpa [hw]) (by simpa [hw])
      (by simpa [hw]) (by simpa [hw]) (by simpa [hw]) (by simpa [hw]) (hP x) (hQ x)
  have hF := agree_fold (n+pre.length) _ _ post hA hread
  have result := hF.2.2 output hout
  have hstep : step = (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
  simp only [wf, w, hstep] at result
  simpa only [circuitFun, Circuit.eval, Circuit.wires, oldCircuit, newCircuit,
    List.foldl_append] using result

lemma repair_mono (n : ℕ) (pre post : List Gate) (p q a b c d output : ℕ)
    (hm : Monotone2 (oldCircuit n pre post p q a b c d output)) :
    Monotone2 (newCircuit n pre post a b c d output) := by
  intro g hg
  change g ∈ pre ++ (narrow (n+pre.length) a b c d).gates ++ post.map (renGate (n+pre.length)) at hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_append.mp hg with hp | hn
    · exact hm g (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hp))))
    · have hnarrow : Monotone2 (narrow (n+pre.length) a b c d) := by simp [Monotone2, narrow]
      exact hnarrow g hn
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have h' := hm g' (List.mem_append.mpr (Or.inr hg'))
    simpa [renGate] using h'

lemma repair_size (n : ℕ) (pre post : List Gate) (p q a b c d output : ℕ) :
    (newCircuit n pre post a b c d output).size + 2 =
      (oldCircuit n pre post p q a b c d output).size := by
  simp [newCircuit, oldCircuit, narrow, wide, Circuit.size]
  omega

lemma not_minimal_matching (n : ℕ) (pre post : List Gate) (p q a b c d output : ℕ)
    (hp : p < n+pre.length) (hq : q < n+pre.length)
    (ha : a < n+pre.length) (hb : b < n+pre.length) (hc : c < n+pre.length) (hd : d < n+pre.length)
    (hP : ∀ x : Fin n → Bool, let w := wf pre (List.ofFn x)
      w.getD p false = (w.getD a false || w.getD c false))
    (hQ : ∀ x : Fin n → Bool, let w := wf pre (List.ofFn x)
      w.getD q false = (w.getD b false || w.getD d false))
    (hread : ∀ g ∈ post, ∀ i ∈ g.inputs, i < n+pre.length ∨ n+pre.length+4 ≤ i)
    (hout : output < n+pre.length ∨ n+pre.length+4 ≤ output) :
    ¬ IsMinimalMonoCircuit n (oldCircuit n pre post p q a b c d output) := by
  intro h
  have hsize := h.2 (newCircuit n pre post a b c d output)
    (repair_mono n pre post p q a b c d output h.1)
    (repair_fun n pre post p q a b c d output hp hq ha hb hc hd hP hQ hread hout).symm
  have he := repair_size n pre post p q a b c d output
  omega

end PEqualNP.Outside.L_meta_2448.matching

namespace PEqualNP.Outside.L_meta_2448_aux

lemma doubleStar_guards {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (noFour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (P Q : Finset α) (p q w : α) (hp : p ∈ P) (hq : q ∈ Q)
    (leftEdges : ∀ a ∈ P, G.Adj a q) (rightEdges : ∀ b ∈ Q, G.Adj p b)
    (largeP : 3 ≤ P.card) (largeQ : 3 ≤ Q.card)
    (guard : ∀ a ∈ P, ∀ b ∈ Q, G.Adj a b ∨ G.Adj a w ∨ G.Adj b w) :
    w = p ∨ w = q := by
  by_contra hn
  obtain ⟨hwp, hwq⟩ := not_or.mp hn
  have largeP' : 1 < (P.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  have largeQ' : 1 < (Q.erase q).card := by
    rw [Finset.card_erase_of_mem hq]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp largeP'
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp largeQ'
  obtain ⟨hap, haP⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbp, hbP⟩ := Finset.mem_erase.mp hb
  obtain ⟨hcq, hcQ⟩ := Finset.mem_erase.mp hc
  obtain ⟨hdq, hdQ⟩ := Finset.mem_erase.mp hd
  have cross {u v : α} (hu : u ∈ P) (hv : v ∈ Q) (hup : u ≠ p) (hvq : v ≠ q) :
      ¬ G.Adj u v := by
    intro huv
    exact (noFour u q p v (leftEdges u hu) (leftEdges p hp).symm
      (rightEdges v hv) huv.symm).elim hup (Ne.symm hvq)
  have pSeparate : ¬ (G.Adj a w ∧ G.Adj b w) := by
    rintro ⟨haw, hbw⟩
    exact (noFour a q b w (leftEdges a haP) (leftEdges b hbP).symm hbw haw.symm).elim
      hab (Ne.symm hwq)
  have qSeparate : ¬ (G.Adj c w ∧ G.Adj d w) := by
    rintro ⟨hcw, hdw⟩
    exact (noFour c p d w (rightEdges c hcQ).symm (rightEdges d hdQ) hdw hcw.symm).elim
      hcd (Ne.symm hwp)
  have hac := (guard a haP c hcQ).resolve_left (cross haP hcQ hap hcq)
  have had := (guard a haP d hdQ).resolve_left (cross haP hdQ hap hdq)
  have hbc := (guard b hbP c hcQ).resolve_left (cross hbP hcQ hbp hcq)
  have hbd := (guard b hbP d hdQ).resolve_left (cross hbP hdQ hbp hdq)
  tauto

lemma doubleStar_guard_adjacent {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (noFour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (P Q : Finset α) (p q w : α) (hp : p ∈ P)
    (leftEdges : ∀ a ∈ P, G.Adj a q) (rightEdges : ∀ b ∈ Q, G.Adj p b)
    (largeP : 3 ≤ P.card) (hwq : w ≠ q)
    (guard : ∀ a ∈ P, ∀ b ∈ Q, G.Adj a b ∨ G.Adj a w ∨ G.Adj b w) :
    ∀ v ∈ Q, v ≠ q → G.Adj v w := by
  have largeP' : 1 < (P.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp largeP'
  obtain ⟨hap, haP⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbp, hbP⟩ := Finset.mem_erase.mp hb
  intro v hv hvq
  have cross {u : α} (hu : u ∈ P) (hup : u ≠ p) : ¬ G.Adj u v := by
    intro huv
    exact (noFour u q p v (leftEdges u hu) (leftEdges p hp).symm
      (rightEdges v hv) huv.symm).elim hup (Ne.symm hvq)
  have separate : ¬ (G.Adj a w ∧ G.Adj b w) := by
    rintro ⟨haw, hbw⟩
    exact (noFour a q b w (leftEdges a haP) (leftEdges b hbP).symm hbw haw.symm).elim
      hab (Ne.symm hwq)
  have hav := (guard a haP v hv).resolve_left (cross haP hap)
  have hbv := (guard b hbP v hv).resolve_left (cross hbP hbp)
  tauto

end PEqualNP.Outside.L_meta_2448_aux
