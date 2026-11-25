import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448
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

lemma least_exists : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x4 ∧ PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ := by
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

end PEqualNP.Outside.L_meta_2448
