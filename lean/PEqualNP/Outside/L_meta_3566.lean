import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def IndependentSupport {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

def MaximalIndependentSupport {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Prop :=
  IndependentSupport G S ∧ ∀ T : Finset (Fin n),
    IndependentSupport G T → S ⊆ T → T = S

def supportInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)

lemma independent_extension {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hS : IndependentSupport G S) :
    ∃ T : Finset (Fin n), S ⊆ T ∧ MaximalIndependentSupport G T := by
  classical
  let A : Finset (Finset (Fin n)) := Finset.univ.filter fun T =>
    S ⊆ T ∧ IndependentSupport G T
  have hA : S ∈ A := by simp [A, hS]
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image A Finset.card ⟨S, hA⟩
  have hT' : S ⊆ T ∧ IndependentSupport G T := by simpa [A] using hT
  refine ⟨T, hT'.1, hT'.2, ?_⟩
  intro U hU hTU
  have hUA : U ∈ A := by simp [A, hT'.1.trans hTU, hU]
  exact (Finset.eq_of_subset_of_card_le hTU (hmax U hUA)).symm

lemma graphFun_empty_true_iff {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_pair_true {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {u v : Fin n} (huv : G.Adj u v) :
    graphFun G ∅ (pairInput u v) = true := by
  apply (graphFun_empty_true_iff G _).2
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

lemma graphFun_independent_false {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {S : Finset (Fin n)} (hS : IndependentSupport G S) :
    graphFun G ∅ (supportInput S) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_empty_true_iff G _).mp h
  exact hS u (by simpa [supportInput] using hu) v
    (by simpa [supportInput] using hv) huv

lemma bool_true_of_le {a b : Bool} (hab : a ≤ b) (ha : a = true) : b = true := by
  cases a <;> cases b <;> simp_all [Bool.le_iff_imp]

lemma bool_false_of_le {a b : Bool} (hab : a ≤ b) (hb : b = false) : a = false := by
  cases a <;> cases b <;> simp_all [Bool.le_iff_imp]

lemma graphFun_boundary_iff {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool) (hf : Monotone f) :
    f = graphFun G ∅ ↔
      (∀ u v, G.Adj u v → f (pairInput u v) = true) ∧
      (∀ S : Finset (Fin n), MaximalIndependentSupport G S →
        f (supportInput S) = false) := by
  classical
  constructor
  · intro h
    subst f
    exact ⟨fun _ _ huv => graphFun_pair_true G huv,
      fun _ hS => graphFun_independent_false G hS.1⟩
  · rintro ⟨hpos, hneg⟩
    funext x
    by_cases hx : graphFun G ∅ x = true
    · obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_empty_true_iff G x).mp hx
      have hpx : pairInput u v ≤ x := by
        intro i
        apply Bool.le_iff_imp.mpr
        intro hi
        have hi' : i = u ∨ i = v := by simpa [pairInput] using hi
        rcases hi' with rfl | rfl
        · exact hu
        · exact hv
      exact (bool_true_of_le (hf hpx) (hpos u v huv)).trans hx.symm
    · let S : Finset (Fin n) := Finset.univ.filter fun i => x i = true
      have hS : IndependentSupport G S := by
        intro u hu v hv huv
        apply hx
        exact (graphFun_empty_true_iff G x).2
          ⟨u, v, huv, (Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2⟩
      obtain ⟨T, hST, hT⟩ := independent_extension G S hS
      have hxT : x ≤ supportInput T := by
        intro i
        apply Bool.le_iff_imp.mpr
        intro hi
        simpa [supportInput] using hST (by simp [S, hi])
      have hfx : f x = false := bool_false_of_le (hf hxT) (hneg T hT)
      have hgx : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hx
      exact hfx.trans hgx.symm

end PEqualNP.Outside.L_meta_3566

namespace PEqualNP.Outside.L_meta_3566.Splice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma stepWire_getD_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (stepWire w g).getD i false = w.getD i false := by
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma stepWire_getD_len (w : List Bool) (g : Gate) :
    (stepWire w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs.take j = pre ∧ gs.drop (j + 1) = post ∧
        gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl, rfl, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩

def dropDup (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩

lemma dropDup_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (dropDup n C j i).gates.length + 1 = C.gates.length := by
  simp only [dropDup, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

lemma dropDup_mem (n : ℕ) (C : Circuit) (j i : ℕ) (g : Gate)
    (hg : g ∈ (dropDup n C j i).gates) :
    ∃ g0 ∈ C.gates, g = g0 ∨ g = aliasGate (n + j) i g0 := by
  rcases List.mem_append.mp hg with h | h
  · exact ⟨g, List.mem_of_mem_take h, Or.inl rfl⟩
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h
    exact ⟨g0, List.mem_of_mem_drop hg0, Or.inr rfl⟩

lemma dropDup_gateAt_lt (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length)
    (hk : k < j) : gateAt (dropDup n C j i) k = gateAt C k := by
  have h1 : k < (C.gates.take j).length := by rw [List.length_take]; omega
  simp only [gateAt, dropDup, List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  rw [List.getElem?_take_of_lt hk]

lemma dropDup_gateAt_ge (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length)
    (hjk : j ≤ k) (hk : k + 1 < C.gates.length) :
    gateAt (dropDup n C j i) k = aliasGate (n + j) i (gateAt C (k + 1)) := by
  have h1 : (C.gates.take j).length ≤ k := by rw [List.length_take]; omega
  have h2 : (C.gates.take j).length = j := by rw [List.length_take]; omega
  have h3 : j + 1 + (k - j) = k + 1 := by omega
  simp only [gateAt, dropDup, List.getD_eq_getElem?_getD, List.getElem?_append_right h1, h2,
    List.getElem?_map, List.getElem?_drop, h3]
  rw [List.getElem?_eq_getElem hk]
  rfl

lemma aliasWire_lt (m i u b : ℕ) (hi : i < m) (hm : m ≤ b) (hu : u < b + 1) :
    aliasWire m i u < b := by
  unfold aliasWire shiftDown
  split_ifs <;> omega

lemma dropDup_readsBack (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length)
    (hi : i < n + j) (hrb : ReadsBack n C) : ReadsBack n (dropDup n C j i) := by
  intro k hk u hu
  have hlen := dropDup_length n C j i hj
  by_cases hkj : k < j
  · rw [dropDup_gateAt_lt n C j i k hj hkj] at hu
    exact hrb k (by omega) u hu
  · rw [dropDup_gateAt_ge n C j i k hj (by omega) (by omega)] at hu
    obtain ⟨u0, hu0, rfl⟩ := List.mem_map.mp hu
    have := hrb (k + 1) (by omega) u0 hu0
    exact aliasWire_lt (n + j) i u0 (n + k) hi (by omega) (by omega)

lemma aliasWire_init {m i : ℕ} (_hi : i < m) (u : ℕ) :
    aliasWire m i u = if u = m then i else if u < m then u else u - 1 := by
  simp only [aliasWire, shiftDown]
  split_ifs <;> omega

lemma alias_initial {R : Bool → Bool → Prop} (hr : ∀ b, R b b)
    (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length)
    (h : R (g.op.eval (g.inputs.map fun k => w.getD k false)) (w.getD i false)) :
    ∀ u, R ((stepWire w g).getD u false) (w.getD (aliasWire w.length i u) false) := by
  intro u
  rw [aliasWire_init hi]
  by_cases he : u = w.length
  · subst u
    rw [ite_eq_left rfl, stepWire_getD_len]
    exact h
  · rw [ite_eq_right he]
    by_cases hl : u < w.length
    · rw [ite_eq_left hl, stepWire_getD_lt w g u hl]
      exact hr _
    · rw [ite_eq_right hl]
      rw [getD_ge_length _ _ (by simp [stepWire]; omega),
        getD_ge_length _ _ (by omega)]
      exact hr false

lemma alias_rel_step {R : Bool → Bool → Prop} (hr : ∀ b, R b b)
    (m i : ℕ) (hi : i < m) (a b : List Bool) (hlen : a.length = b.length + 1)
    (hm : m ≤ b.length) (g : Gate)
    (hmono : ∀ (f h : ℕ → Bool), (∀ u, R (f u) (h u)) →
      R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map h)))
    (hab : ∀ u, R (a.getD u false) (b.getD (aliasWire m i u) false)) :
    ∀ u, R ((stepWire a g).getD u false)
      ((stepWire b (aliasGate m i g)).getD (aliasWire m i u) false) := by
  intro u
  by_cases hl : u < a.length
  · rw [stepWire_getD_lt a g u hl,
      stepWire_getD_lt b (aliasGate m i g) (aliasWire m i u)
        (aliasWire_lt m i u b.length hi hm (by omega))]
    exact hab u
  · by_cases he : u = a.length
    · subst u
      have hs : aliasWire m i a.length = b.length := by
        simp only [aliasWire, shiftDown]
        split_ifs <;> omega
      rw [hs, stepWire_getD_len, stepWire_getD_len]
      simpa only [aliasGate, List.map_map, Function.comp_def] using hmono
        (fun k => a.getD k false) (fun k => b.getD (aliasWire m i k) false) hab
    · have hs : (stepWire b (aliasGate m i g)).length ≤ aliasWire m i u := by
        simp only [stepWire, List.length_append, List.length_singleton, aliasWire, shiftDown]
        split_ifs <;> omega
      rw [getD_ge_length _ _ (by simp [stepWire]; omega), getD_ge_length _ _ hs]
      exact hr false

lemma alias_rel_post {R : Bool → Bool → Prop} (hr : ∀ b, R b b)
    (m i : ℕ) (hi : i < m) (a b : List Bool) (hlen : a.length = b.length + 1)
    (hm : m ≤ b.length) (gs : List Gate)
    (hmono : ∀ g ∈ gs, ∀ (f h : ℕ → Bool), (∀ u, R (f u) (h u)) →
      R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map h)))
    (hab : ∀ u, R (a.getD u false) (b.getD (aliasWire m i u) false)) :
    ∀ u, R ((gs.foldl stepWire a).getD u false)
      (((gs.map (aliasGate m i)).foldl stepWire b).getD (aliasWire m i u) false) := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    apply ih (stepWire a g) (stepWire b (aliasGate m i g))
    · simp [stepWire, hlen]
    · simp [stepWire]; omega
    · intro g hg
      exact hmono g (by simp [hg])
    · exact alias_rel_step hr m i hi a b hlen hm g (hmono g (by simp)) hab

lemma dropDup_rel {R : Bool → Bool → Prop} (hr : ∀ b, R b b)
    (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (hmono : ∀ g ∈ C.gates, ∀ (f h : ℕ → Bool), (∀ u, R (f u) (h u)) →
      R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map h)))
    (x : Fin n → Bool)
    (hx : R ((C.wires (List.ofFn x)).getD (n + j) false)
      ((C.wires (List.ofFn x)).getD i false)) :
    R (circuitFun n C x) (circuitFun n (dropDup n C j i) x) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, htake, hdrop, _⟩ := split_gates C.gates j hj
  have hw0_len : (pre.foldl stepWire (List.ofFn x)).length = n + j := by
    rw [foldl_stepWire_length, List.length_ofFn, hpre_len]
  rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons] at hx
  rw [foldl_stepWire_getD_lt post _ i (by rw [stepWire, List.length_append, hw0_len]; omega),
    foldl_stepWire_getD_lt post _ (n + j)
      (by rw [stepWire, List.length_append, hw0_len, List.length_singleton]; omega),
    stepWire_getD_lt _ _ i (by omega)] at hx
  have hx2 := stepWire_getD_len (pre.foldl stepWire (List.ofFn x)) gj
  rw [hw0_len] at hx2
  rw [hx2] at hx
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hr0 := alias_initial hr w0 gj i (by dsimp [w0]; omega) hx
  have hrpost := alias_rel_post hr w0.length i (by dsimp [w0]; omega)
    (stepWire w0 gj) w0 (by simp [stepWire]) (le_refl _) post
    (fun g hg => hmono g (hgs ▸ by simp [hg])) hr0 C.output
  dsimp only [w0] at hrpost
  rw [hw0_len] at hrpost
  simp only [circuitFun, Circuit.eval, dropDup, wires_eq_foldl]
  rw [htake, hdrop, hgs, List.foldl_append, List.foldl_cons, List.foldl_append]
  exact hrpost

lemma bool_and_rel {a b c d : Bool} (hab : a ≤ b) (hcd : c ≤ d) :
    (a && c) ≤ (b && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma bool_or_rel {a b c d : Bool} (hab : a ≤ b) (hcd : c ≤ d) :
    (a || c) ≤ (b || d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma ao_eval_mono (g : Gate) (hao : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f h : ℕ → Bool) (hfh : ∀ u, f u ≤ h u) :
    g.op.eval (g.inputs.map f) ≤ g.op.eval (g.inputs.map h) := by
  obtain ⟨op, inputs⟩ := g
  rcases hao with rfl | rfl
  · simp only [GateOp.eval]
    induction inputs with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.all_cons, id_eq]
      exact bool_and_rel (hfh a) ih
  · simp only [GateOp.eval]
    induction inputs with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.any_cons, id_eq]
      exact bool_or_rel (hfh a) ih

lemma dropDup_le (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length)
    (hi : i < n + j) (hao : AndOrOnly C) (x : Fin n → Bool)
    (hx : (C.wires (List.ofFn x)).getD (n + j) false ≤
      (C.wires (List.ofFn x)).getD i false) :
    circuitFun n C x ≤ circuitFun n (dropDup n C j i) x :=
  dropDup_rel (fun _ => le_refl _) n C j i hj hi
    (fun g hg => ao_eval_mono g (hao g hg)) x hx

lemma dropDup_ge (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length)
    (hi : i < n + j) (hao : AndOrOnly C) (x : Fin n → Bool)
    (hx : (C.wires (List.ofFn x)).getD i false ≤
      (C.wires (List.ofFn x)).getD (n + j) false) :
    circuitFun n (dropDup n C j i) x ≤ circuitFun n C x :=
  dropDup_rel (R := fun a b => b ≤ a) (fun _ => le_refl _) n C j i hj hi
    (fun g hg f h hfh => ao_eval_mono g (hao g hg) h f hfh) x hx

lemma dropDup_ao (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length)
    (hi : i < n + j) (hAO : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.TopForm.IsAO2 n (dropDup n C j i) := by
  obtain ⟨hao, hrb, h2⟩ := hAO
  refine ⟨?_, dropDup_readsBack n C j i hj hi hrb, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, h | h⟩ := dropDup_mem n C j i g hg
    · rw [h]; exact hao g0 hg0
    · rw [h]; exact hao g0 hg0
  · intro g hg
    obtain ⟨g0, hg0, h | h⟩ := dropDup_mem n C j i g hg
    · rw [h]; exact h2 g0 hg0
    · rw [h]; simp only [aliasGate, List.length_map]; exact h2 g0 hg0

lemma stepWire_mono (g : Gate) (hao : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hlen : a.length = b.length)
    (hab : ∀ u, a.getD u false ≤ b.getD u false) :
    ∀ u, (stepWire a g).getD u false ≤ (stepWire b g).getD u false := by
  intro u
  by_cases hl : u < a.length
  · rw [stepWire_getD_lt _ _ _ hl, stepWire_getD_lt _ _ _ (by omega)]
    exact hab u
  · by_cases he : u = a.length
    · rw [he, stepWire_getD_len, hlen, stepWire_getD_len]
      exact ao_eval_mono g hao _ _ hab
    · rw [getD_ge_length _ _ (by simp [stepWire]; omega),
        getD_ge_length _ _ (by simp [stepWire]; omega)]

lemma foldl_mono (gs : List Gate) (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hlen : a.length = b.length)
    (hab : ∀ u, a.getD u false ≤ b.getD u false) :
    ∀ u, (gs.foldl stepWire a).getD u false ≤ (gs.foldl stepWire b).getD u false := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih (fun g hg => hao g (by simp [hg]))
      (stepWire a g) (stepWire b g) (by simp [stepWire, hlen])
      (stepWire_mono g (hao g (by simp)) a b hlen hab)

lemma circuitFun_monotone (n : ℕ) (C : Circuit) (hao : AndOrOnly C) :
    Monotone (circuitFun n C) := by
  intro x y hxy
  apply foldl_mono C.gates hao (List.ofFn x) (List.ofFn y) (by simp)
  intro u
  by_cases hu : u < n
  · rw [List.getD_eq_getElem _ _ (by simpa), List.getD_eq_getElem _ _ (by simpa)]
    simpa using hxy ⟨u, hu⟩
  · rw [getD_ge_length _ _ (by simpa using Nat.le_of_not_gt hu),
      getD_ge_length _ _ (by simpa using Nat.le_of_not_gt hu)]

end PEqualNP.Outside.L_meta_3566.Splice

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma dropDup_boundary_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (hpos : ∀ u v, G.Adj u v →
      (C.wires (List.ofFn (pairInput u v))).getD (n + j) false ≤
      (C.wires (List.ofFn (pairInput u v))).getD i false)
    (hneg : ∀ S : Finset (Fin n), MaximalIndependentSupport G S →
      (C.wires (List.ofFn (supportInput S))).getD i false ≤
      (C.wires (List.ofFn (supportInput S))).getD (n + j) false) :
    circuitFun n (Splice.dropDup n C j i) = graphFun G ∅ := by
  apply (graphFun_boundary_iff G _
    (Splice.circuitFun_monotone n _ (Splice.dropDup_ao n C j i hj hi hAO).1)).2
  constructor
  · intro u v huv
    apply bool_true_of_le (Splice.dropDup_le n C j i hj hi hAO.1 _ (hpos u v huv))
    rw [hfun]
    exact graphFun_pair_true G huv
  · intro S hS
    apply bool_false_of_le (Splice.dropDup_ge n C j i hj hi hAO.1 _ (hneg S hS))
    rw [hfun]
    exact graphFun_independent_false G hS.1

lemma least_boundary_separation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j) :
    (∃ u v, G.Adj u v ∧
      (C.wires (List.ofFn (pairInput u v))).getD (n + j) false = true ∧
      (C.wires (List.ofFn (pairInput u v))).getD i false = false) ∨
    ∃ S : Finset (Fin n), MaximalIndependentSupport G S ∧
      (C.wires (List.ofFn (supportInput S))).getD (n + j) false = false ∧
      (C.wires (List.ofFn (supportInput S))).getD i false = true := by
  classical
  by_contra hbad
  have hfun : circuitFun n (Splice.dropDup n C j i) = graphFun G ∅ := by
    apply dropDup_boundary_correct G C hLeast.1 hLeast.2.1 j i hj hi
    · intro u v huv
      apply Bool.le_iff_imp.mpr
      intro hg
      by_contra hh
      exact hbad (Or.inl ⟨u, v, huv, hg, Bool.eq_false_iff.mpr hh⟩)
    · intro S hS
      apply Bool.le_iff_imp.mpr
      intro hh
      by_contra hg
      exact hbad (Or.inr ⟨S, hS, Bool.eq_false_iff.mpr hg, hh⟩)
  have hsize := hLeast.2.2 _ (Splice.dropDup_ao n C j i hj hi hLeast.1) hfun
  have hlength := Splice.dropDup_length n C j i hj
  simp only [Circuit.size] at hsize
  omega

end PEqualNP.Outside.L_meta_3566


namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm Splice

lemma gate_wire_eval {n : ℕ} (C : Circuit) (hrb : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (C.wires (List.ofFn x)).getD i false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _, _, hgj⟩ := split_gates C.gates j hj
  have hw0_len : (pre.foldl stepWire (List.ofFn x)).length = n + j := by
    rw [foldl_stepWire_length, List.length_ofFn, hpre_len]
  have hgate : gateAt C j = gj := by
    simpa only [gateAt, List.getD_eq_getElem _ _ hj] using hgj
  have hpre : ∀ i, i < n + j →
      (C.wires (List.ofFn x)).getD i false =
        (pre.foldl stepWire (List.ofFn x)).getD i false := by
    intro i hi
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons,
      foldl_stepWire_getD_lt _ _ _ (by simp [stepWire, hw0_len]<;> omega),
      stepWire_getD_lt _ _ _ (by omega)]
  have hm : (gateAt C j).inputs.map (fun i => (C.wires (List.ofFn x)).getD i false) =
      (gateAt C j).inputs.map (fun i => (pre.foldl stepWire (List.ofFn x)).getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact hpre i (hrb j hj i hi)
  rw [hm, hgate, wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons,
    foldl_stepWire_getD_lt _ _ _ (by simp [stepWire, hw0_len]<;> omega)]
  rw [← hw0_len, stepWire_getD_len]

lemma or_input_le_gate {n : ℕ} (C : Circuit) (hrb : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (i : ℕ) (hi : i ∈ (gateAt C j).inputs) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD i false ≤
      (C.wires (List.ofFn x)).getD (n + j) false := by
  rw [gate_wire_eval C hrb j hj x, hop]
  apply Bool.le_iff_imp.mpr
  intro h
  simp only [GateOp.eval, List.any_eq_true, List.mem_map]
  exact ⟨true, ⟨i, hi, h⟩, rfl⟩

lemma and_gate_le_input {n : ℕ} (C : Circuit) (hrb : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (i : ℕ) (hi : i ∈ (gateAt C j).inputs) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD (n + j) false ≤
      (C.wires (List.ofFn x)).getD i false := by
  rw [gate_wire_eval C hrb j hj x, hop]
  apply Bool.le_iff_imp.mpr
  intro h
  have h' := List.all_eq_true.mp h ((C.wires (List.ofFn x)).getD i false)
    (List.mem_map.mpr ⟨i, hi, rfl⟩)
  exact h'

lemma least_or_input_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (i : ℕ) (hi : i ∈ (gateAt C j).inputs) :
    ∃ u v, G.Adj u v ∧
      (C.wires (List.ofFn (pairInput u v))).getD (n + j) false = true ∧
      (C.wires (List.ofFn (pairInput u v))).getD i false = false := by
  rcases least_boundary_separation G C hL j i hj (hL.1.2.1 j hj i hi) with h | h
  · exact h
  · obtain ⟨S, _, hg, hi'⟩ := h
    have hle := or_input_le_gate C hL.1.2.1 j hj hop i hi (supportInput S)
    rw [hg, hi'] at hle
    contradiction

lemma least_and_input_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (i : ℕ) (hi : i ∈ (gateAt C j).inputs) :
    ∃ S : Finset (Fin n), MaximalIndependentSupport G S ∧
      (C.wires (List.ofFn (supportInput S))).getD (n + j) false = false ∧
      (C.wires (List.ofFn (supportInput S))).getD i false = true := by
  rcases least_boundary_separation G C hL j i hj (hL.1.2.1 j hj i hi) with h | h
  · obtain ⟨u, v, _, hg, hi'⟩ := h
    have hle := and_gate_le_input C hL.1.2.1 j hj hop i hi (pairInput u v)
    rw [hg, hi'] at hle
    contradiction
  · exact h

end PEqualNP.Outside.L_meta_3566


namespace PEqualNP.Outside.L_meta_3566.NormalizationObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def matchingCircuit : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [7, 8]⟩,
    ⟨.and, [6, 9]⟩], 10⟩

lemma model : IsAO2 4 matchingCircuit := by decide

lemma size : matchingCircuit.size = 7 := rfl

lemma eval (a b c d : Bool) :
    matchingCircuit.eval [a, b, c, d] = ((a && b) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

def firstDirty (a b c d : Bool) : Bool := (a || c) && (b || d)

def secondDirty (a b c d : Bool) : Bool := (a || d) && (b || c)

lemma identity (a b c d : Bool) :
    (firstDirty a b c d && secondDirty a b c d) = ((a && b) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

lemma noEarlierWireBypass :
    ∀ i : Fin 6, ∃ a b c d : Bool,
      (([a, b, c, d, a || c, b || d].getD i false) && secondDirty a b c d) ≠
        ((a && b) || (c && d)) := by decide

lemma noConstantBypass :
    ∀ k : Bool, ∃ a b c d : Bool,
      (k && secondDirty a b c d) ≠ ((a && b) || (c && d)) := by decide

lemma firstNoSafeVertex :
    ∀ i : Fin 4, ∃ a b c d : Bool,
      firstDirty a b c d = true ∧ [a, b, c, d].getD i false = true ∧
        ((a && b) || (c && d)) = false := by decide

lemma secondNoSafeVertex :
    ∀ i : Fin 4, ∃ a b c d : Bool,
      secondDirty a b c d = true ∧ [a, b, c, d].getD i false = true ∧
        ((a && b) || (c && d)) = false := by decide

abbrev matchingGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun u v => (u = 0 ∧ v = 1) ∨ (u = 2 ∧ v = 3)

lemma noFourCycle : NoFourCycle matchingGraph := by decide

lemma bipartite :
    ∀ u v : Fin 4, matchingGraph.Adj u v →
      decide (u = 0 ∨ u = 2) ≠ decide (v = 0 ∨ v = 2) := by decide

lemma computes :
    PEqualNP.MetaComplexity.circuitFun 4 matchingCircuit =
      PEqualNP.MetaComplexity.NestedCover.graphFun matchingGraph ∅ := by decide

lemma topForm : TopForm matchingGraph matchingCircuit := by decide

lemma exactJunk : junk matchingGraph matchingCircuit = {2, 5} := by decide

lemma exactTops : tops matchingGraph matchingCircuit = {6} := by decide

lemma exactCentreless : centreless matchingGraph matchingCircuit = {6} := by decide

lemma noStarEdges : starEdges matchingGraph matchingCircuit = ∅ := by decide

lemma firstWmax : wmax matchingGraph matchingCircuit 2 = ∅ := by decide

lemma secondWmax : wmax matchingGraph matchingCircuit 5 = ∅ := by decide

def smallerCircuit : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩], 6⟩

lemma smaller_model : IsAO2 4 smallerCircuit := by decide

lemma smaller_computes :
    PEqualNP.MetaComplexity.circuitFun 4 smallerCircuit =
      PEqualNP.MetaComplexity.NestedCover.graphFun matchingGraph ∅ := by decide

lemma notLeast : ¬ IsLeastAO matchingGraph matchingCircuit := by
  intro h
  have := h.2.2 smallerCircuit smaller_model smaller_computes
  change 7 ≤ 3 at this
  contradiction

end PEqualNP.Outside.L_meta_3566.NormalizationObstruction


namespace PEqualNP.Outside.L_meta_3566.MixedColor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

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

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

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

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

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

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha

lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
lemma opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
lemma opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
lemma andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
lemma andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩

lemma reachVal {w h : ℕ} {x : Fin n → Bool} (hr : OrReaches n C w h)
    (hh : gateVal n C h x = true) : val C (List.ofFn x) w = true :=
  orStep_up (n := n) (by simp) (orReaches_reach h _ hr).1 hh
lemma eitherOperand (b c : Fin 2) : c = b ∨ c = 1 - b := by
  fin_cases b <;> fin_cases c <;> decide

lemma orNOfRaw {m : ℕ} (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hn : (orIn n C (n + m)).Nonempty) : m ∈ orN G C := by
  obtain ⟨t, ht⟩ := hn
  simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
  refine ⟨hm, hop, ?_⟩
  intro hb
  have hv : gateVal n C m (pairInput t t) = true :=
    reach_var_val (pairInput t t) _ t (mem_orIn_reach t ht) (pairInput_left t t)
  exact G.irrefl ((graphFun_pair G t t).mp (hb _ hv))

lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma lam_has_common_neighbor (hAO : IsAO2 n C) {m : ℕ} (hm : m ∈ lam G C) :
    ∃ t : Fin n, ∀ u ∈ orIn n C (n + m), G.Adj t u := by
  obtain ⟨_, _, _, a, ha, b, hcard, hr⟩ := Finset.mem_filter.mp hm
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
  have hts : t ∈ side (n := n) C a (1 - b) := by simp [ht]
  obtain ⟨hal, hao, hab⟩ := topData ha
  refine ⟨t, fun u hu => ?_⟩
  apply (graphFun_pair G t u).mp
  apply hab (pairInput t u)
  apply (andValOperands hAO hal hao (pairInput t u)).mpr
  intro c
  rcases eitherOperand b c with rfl | rfl
  · apply reachVal hr
    exact reach_var_val (pairInput t u) _ u (mem_orIn_reach u hu) (pairInput_right t u)
  · exact sideVal hts (pairInput_left t u)

lemma lam_monochromatic (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) {m : ℕ} (hm : m ∈ lam G C) :
    ∀ u ∈ orIn n C (n + m), ∀ v ∈ orIn n C (n + m), s u = s v := by
  obtain ⟨t, ht⟩ := lam_has_common_neighbor hAO hm
  intro u hu v hv
  have hut := hbip t u (ht u hu)
  have hvt := hbip t v (ht v hv)
  cases htcol : s t <;> cases hucol : s u <;> cases hvcol : s v <;> simp_all

def IsMixed (s : Fin n → Bool) (S : Finset (Fin n)) : Prop :=
  ∃ u ∈ S, ∃ v ∈ S, s u ≠ s v

lemma mixed_not_lam (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) {m : ℕ}
    (hmixed : IsMixed s (orIn n C (n + m))) : m ∉ lam G C := by
  intro hm
  obtain ⟨u, hu, v, hv, huv⟩ := hmixed
  exact huv (lam_monochromatic hAO s hbip hm u hu v hv)

lemma mixed_mem_remaining (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) {m : ℕ}
    (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hmixed : IsMixed s (orIn n C (n + m))) : m ∈ orN G C \ lam G C := by
  refine Finset.mem_sdiff.mpr ⟨?_, mixed_not_lam hAO s hbip hmixed⟩
  obtain ⟨u, hu, _, _, _⟩ := hmixed
  exact orNOfRaw hm hop ⟨u, hu⟩

noncomputable def mixedOrs (n : ℕ) (C : Circuit) (s : Fin n → Bool) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun m =>
    (gateAt C m).op = GateOp.or ∧ IsMixed s (orIn n C (n + m))

lemma mixedOrs_subset (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) :
    mixedOrs n C s ⊆ orN G C \ lam G C := by
  classical
  intro m hm
  obtain ⟨hmlt, hop, hmix⟩ := Finset.mem_filter.mp hm
  exact mixed_mem_remaining hAO s hbip (Finset.mem_range.mp hmlt) hop hmix

lemma mixedOrs_card_le_remaining (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) :
    (mixedOrs n C s).card ≤ (orN G C \ lam G C).card :=
  Finset.card_le_card (mixedOrs_subset hAO s hbip)

end PEqualNP.Outside.L_meta_3566.MixedColor


namespace PEqualNP.Outside.L_meta_3566.NormalizationObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxRecDepth 2048 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 8192 in
lemma satisfies_all_boundary_separations :
    ∀ j : Fin 7, ∀ i : Fin (4 + j.val),
      (∃ u v : Fin 4, matchingGraph.Adj u v ∧
        (matchingCircuit.wires (List.ofFn (pairInput u v))).getD (4 + j.val) false = true ∧
        (matchingCircuit.wires (List.ofFn (pairInput u v))).getD i.val false = false) ∨
      ∃ S : Finset (Fin 4), MaximalIndependentSupport matchingGraph S ∧
        (matchingCircuit.wires (List.ofFn (supportInput S))).getD (4 + j.val) false = false ∧
        (matchingCircuit.wires (List.ofFn (supportInput S))).getD i.val false = true := by
  unfold MaximalIndependentSupport IndependentSupport
  intro j i
  fin_cases j <;> fin_cases i <;> decide

set_option maxRecDepth 2048 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 8192 in
lemma no_gate_has_correct_earlier_bypass :
    ∀ j : Fin 7, ∀ i : Fin (4 + j.val), ∃ x : Fin 4 → Bool,
      circuitFun 4 (Splice.dropDup 4 matchingCircuit j.val i.val) x ≠
        graphFun matchingGraph ∅ x := by
  intro j i
  fin_cases j <;> fin_cases i <;> decide

set_option maxRecDepth 2048 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 8192 in
lemma no_gate_has_correct_constant_replacement :
    ∀ j : Fin 7, ∀ b : Bool, ∃ x : Fin 4 → Bool,
      circuitFun 4
        ⟨matchingCircuit.gates.set j.val ⟨if b then GateOp.and else GateOp.or, []⟩,
          matchingCircuit.output⟩ x ≠ graphFun matchingGraph ∅ x := by
  intro j b
  fin_cases j <;> cases b <;> decide

end PEqualNP.Outside.L_meta_3566.NormalizationObstruction


namespace PEqualNP.Outside.L_meta_3566.SampleMinimality

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def Correct {n : ℕ} (P N : Set (Fin n → Bool)) (C : Circuit) : Prop :=
  (∀ x ∈ P, circuitFun n C x = true) ∧ ∀ x ∈ N, circuitFun n C x = false

def Separates {n : ℕ} (P N : Set (Fin n → Bool)) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, ∀ i < n + j,
    (∃ x ∈ P, (C.wires (List.ofFn x)).getD (n + j) false = true ∧
      (C.wires (List.ofFn x)).getD i false = false) ∨
    ∃ x ∈ N, (C.wires (List.ofFn x)).getD (n + j) false = false ∧
      (C.wires (List.ofFn x)).getD i false = true

lemma least_separates {n : ℕ} (P N : Set (Fin n → Bool)) (C : Circuit)
    (hAO : IsAO2 n C) (hC : Correct P N C)
    (hmin : ∀ D : Circuit, IsAO2 n D → Correct P N D → C.size ≤ D.size) :
    Separates P N C := by
  classical
  intro j hj i hi
  by_contra hbad
  have hD : Correct P N (Splice.dropDup n C j i) := by
    constructor
    · intro x hx
      apply bool_true_of_le (Splice.dropDup_le n C j i hj hi hAO.1 x ?_) (hC.1 x hx)
      apply Bool.le_iff_imp.mpr
      intro hg
      by_contra hw
      exact hbad (Or.inl ⟨x, hx, hg, Bool.eq_false_iff.mpr hw⟩)
    · intro x hx
      apply bool_false_of_le (Splice.dropDup_ge n C j i hj hi hAO.1 x ?_) (hC.2 x hx)
      apply Bool.le_iff_imp.mpr
      intro hw
      by_contra hg
      exact hbad (Or.inr ⟨x, hx, Bool.eq_false_iff.mpr hg, hw⟩)
  have hm := hmin _ (Splice.dropDup_ao n C j i hj hi hAO) hD
  have hl := Splice.dropDup_length n C j i hj
  simp only [Circuit.size] at hm
  omega

lemma exists_least {n : ℕ} (P N : Set (Fin n → Bool)) (C : Circuit)
    (hAO : IsAO2 n C) (hC : Correct P N C) :
    ∃ D : Circuit, IsAO2 n D ∧ Correct P N D ∧ D.size ≤ C.size ∧
      ∀ E : Circuit, IsAO2 n E → Correct P N E → D.size ≤ E.size := by
  classical
  let q : ℕ → Prop := fun k => ∃ D : Circuit, IsAO2 n D ∧ Correct P N D ∧ D.size = k
  have hq : ∃ k, q k := ⟨C.size, C, hAO, hC, rfl⟩
  obtain ⟨D, hd, hc, hs⟩ := Nat.find_spec hq
  refine ⟨D, hd, hc, ?_, ?_⟩
  · rw [hs]
    exact Nat.find_min' hq ⟨C, hAO, hC, rfl⟩
  · intro E he hce
    rw [hs]
    exact Nat.find_min' hq ⟨E, he, hce, rfl⟩

lemma bounded_pruning_iff {n : ℕ} (P N : Set (Fin n → Bool)) (k : ℕ) :
    (∃ C : Circuit, IsAO2 n C ∧ Correct P N C ∧ C.size ≤ k) ↔
    ∃ C : Circuit, IsAO2 n C ∧ Correct P N C ∧ C.size ≤ k ∧ Separates P N C := by
  constructor
  · rintro ⟨C, hAO, hC, hk⟩
    obtain ⟨D, hd, hcd, hle, hmin⟩ := exists_least P N C hAO hC
    exact ⟨D, hd, hcd, hle.trans hk, least_separates P N D hd hcd hmin⟩
  · rintro ⟨C, hAO, hC, hk, _⟩
    exact ⟨C, hAO, hC, hk⟩

end PEqualNP.Outside.L_meta_3566.SampleMinimality


namespace PEqualNP.Outside.L_meta_3566.NoMixedObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def circuit : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [6, 7]⟩,
    ⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [9, 10]⟩,
    ⟨.and, [8, 11]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩,
    ⟨.and, [4, 5]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [16, 14]⟩,
    ⟨.or, [17, 15]⟩], 18⟩

abbrev graph : SimpleGraph (Fin 6) := edgeGraph 6 [(0, 1), (0, 3), (1, 2), (4, 5)]

def color (i : Fin 6) : Bool := decide (i = 0 ∨ i = 2 ∨ i = 4)

lemma model : IsAO2 6 circuit := by decide

lemma size : circuit.size = 13 := rfl

lemma bipartite : ∀ u v : Fin 6, graph.Adj u v → color u ≠ color v := by decide

lemma noFourCycle : NoFourCycle graph := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma computes : circuitFun 6 circuit = graphFun graph ∅ := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma topForm : TopForm graph circuit := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma exactJunk : junk graph circuit = {2, 5} := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma exactUstar : Ustar graph circuit = {s(0, 1)} := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma singletonFalse : ∀ j : Fin 13,
    (gateAt circuit j).op = .and →
    ∀ u : Fin 6, gateVal 6 circuit j (pairInput u u) = false := by
  letI := gateOpDecEq
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma rawMonochromatic : ∀ j : Fin 13,
    (gateAt circuit j).op = .or →
    ∀ u ∈ orIn 6 circuit (6 + j), ∀ v ∈ orIn 6 circuit (6 + j), color u = color v := by
  letI := gateOpDecEq
  decide

lemma noMixed : MixedColor.mixedOrs 6 circuit color = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hj, hop, u, hu, v, hv, hcol⟩ := Finset.mem_filter.mp hj
  have hjlt : j < 13 := by simpa [circuit] using Finset.mem_range.mp hj
  exact hcol (rawMonochromatic ⟨j, hjlt⟩ hop u hu v hv)

def positiveSample (k : Fin 4) : Fin 6 × Fin 6 :=
  ![(0, 1), (0, 3), (1, 2), (4, 5)] k

def negativeSample (k : Fin 6) : Finset (Fin 6) :=
  ![{0, 2, 4}, {1, 3, 4}, {2, 3, 4}, {0, 2, 5}, {1, 3, 5}, {2, 3, 5}] k

lemma positive_adj : ∀ k, graph.Adj (positiveSample k).1 (positiveSample k).2 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma negative_maximal : ∀ k, MaximalIndependentSupport graph (negativeSample k) := by
  unfold MaximalIndependentSupport IndependentSupport
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma separation_samples : ∀ j : Fin 13, ∀ i : Fin (6 + j),
    (∃ k : Fin 4,
      gateVal 6 circuit j (pairInput (positiveSample k).1 (positiveSample k).2) = true ∧
      (circuit.wires (List.ofFn (pairInput (positiveSample k).1 (positiveSample k).2))).getD i false = false) ∨
    (∃ k : Fin 6,
      gateVal 6 circuit j (supportInput (negativeSample k)) = false ∧
      (circuit.wires (List.ofFn (supportInput (negativeSample k)))).getD i false = true) := by
  decide

lemma allBoundarySeparation : ∀ j : ℕ, j < circuit.gates.length →
    ∀ i : ℕ, i < 6 + j →
    (∃ u v : Fin 6, graph.Adj u v ∧
      gateVal 6 circuit j (pairInput u v) = true ∧
      (circuit.wires (List.ofFn (pairInput u v))).getD i false = false) ∨
    (∃ S : Finset (Fin 6), MaximalIndependentSupport graph S ∧
      gateVal 6 circuit j (supportInput S) = false ∧
      (circuit.wires (List.ofFn (supportInput S))).getD i false = true) := by
  intro j hj i hi
  have hjlt : j < 13 := by simpa [circuit] using hj
  rcases separation_samples ⟨j, hjlt⟩ ⟨i, hi⟩ with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact Or.inl ⟨(positiveSample k).1, (positiveSample k).2, positive_adj k, hk⟩
  · exact Or.inr ⟨negativeSample k, negative_maximal k, hk⟩

def smallerCircuit : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [0, 3]⟩,
    ⟨.or, [7, 8]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [9, 10]⟩], 11⟩

lemma smallerModel : IsAO2 6 smallerCircuit := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma smallerComputes : circuitFun 6 smallerCircuit = graphFun graph ∅ := by decide

lemma notLeast : ¬ IsLeastAO graph circuit := by
  intro h
  have hle := h.2.2 smallerCircuit smallerModel smallerComputes
  change 13 ≤ 6 at hle
  omega

lemma actualBypassModel : IsAO2 6 (Splice.dropDup 6 circuit 5 0) := by
  exact Splice.dropDup_ao 6 circuit 5 0 (by decide) (by decide) model

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma actualBypassComputes :
    circuitFun 6 (Splice.dropDup 6 circuit 5 0) = graphFun graph ∅ := by decide

lemma actualBypassSize : (Splice.dropDup 6 circuit 5 0).size = 12 := rfl

end PEqualNP.Outside.L_meta_3566.NoMixedObstruction



namespace PEqualNP.Outside.L_meta_3566.RectangleSelection

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def setInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun u => decide (u ∈ S)

def rawOr {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ u ∈ S, x u = true)

def quad {n : ℕ} (A B C D : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  (rawOr A x && rawOr B x) && (rawOr C x && rawOr D x)

def star {n : ℕ} (u : Fin n) (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  x u && rawOr S x

lemma quad_true {n : ℕ} (A B C D : Finset (Fin n)) (x : Fin n → Bool) :
    quad A B C D x = true ↔
      (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true) ∧
      (∃ c ∈ C, x c = true) ∧ (∃ d ∈ D, x d = true) := by
  simp [quad, rawOr, and_assoc]

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : graphFun G ∅ x = true ↔
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  simp [graphFun]

lemma edge_of_two_colors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (L R : Finset (Fin n))
    (hL : ∀ u ∈ L, s u = false) (hR : ∀ v ∈ R, s v = true)
    (hx : graphFun G ∅ (setInput (L ∪ R)) = true) :
    ∃ a ∈ L, ∃ b ∈ R, G.Adj a b := by
  obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G _).mp hx
  have ha' : a ∈ L ∪ R := by simpa [setInput] using ha
  have hb' : b ∈ L ∪ R := by simpa [setInput] using hb
  rcases Finset.mem_union.mp ha' with haL | haR <;>
    rcases Finset.mem_union.mp hb' with hbL | hbR
  · exact False.elim ((hbip a b hab) ((hL a haL).trans (hL b hbL).symm))
  · exact ⟨a, haL, b, hbR, hab⟩
  · exact ⟨b, hbL, a, haR, hab.symm⟩
  · exact False.elim ((hbip a b hab) ((hR a haR).trans (hR b hbR).symm))

lemma pair_colored_intersections {n : ℕ} (s : Fin n → Bool)
    (A B C D : Finset (Fin n))
    (hA : ∀ a ∈ A, s a = false) (hB : ∀ b ∈ B, s b = true)
    (hC : ∀ c ∈ C, s c = false) (hD : ∀ d ∈ D, s d = true)
    (u v : Fin n) :
    quad A B C D (pairInput u v) = true ↔
      (u ∈ A ∩ C ∧ v ∈ B ∩ D) ∨ (v ∈ A ∩ C ∧ u ∈ B ∩ D) := by
  constructor
  · intro h
    obtain ⟨⟨a, ha, hae⟩, ⟨b, hb, hbe⟩, ⟨c, hc, hce⟩, ⟨d, hd, hde⟩⟩ :=
      (quad_true A B C D _).mp h
    have hae' : a = u ∨ a = v := by simpa [pairInput] using hae
    have hbe' : b = u ∨ b = v := by simpa [pairInput] using hbe
    have hce' : c = u ∨ c = v := by simpa [pairInput] using hce
    have hde' : d = u ∨ d = v := by simpa [pairInput] using hde
    have haC := hA a ha
    have hbC := hB b hb
    have hcC := hC c hc
    have hdC := hD d hd
    rcases hae' with rfl | rfl <;> rcases hbe' with rfl | rfl <;>
      rcases hce' with rfl | rfl <;> rcases hde' with rfl | rfl <;>
      simp_all
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · exact (quad_true A B C D _).2
        ⟨⟨u, (Finset.mem_inter.mp hu).1, by simp [pairInput]⟩,
          ⟨v, (Finset.mem_inter.mp hv).1, by simp [pairInput]⟩,
          ⟨u, (Finset.mem_inter.mp hu).2, by simp [pairInput]⟩,
          ⟨v, (Finset.mem_inter.mp hv).2, by simp [pairInput]⟩⟩
    · exact (quad_true A B C D _).2
        ⟨⟨v, (Finset.mem_inter.mp hv).1, by simp [pairInput]⟩,
          ⟨u, (Finset.mem_inter.mp hu).1, by simp [pairInput]⟩,
          ⟨v, (Finset.mem_inter.mp hv).2, by simp [pairInput]⟩,
          ⟨u, (Finset.mem_inter.mp hu).2, by simp [pairInput]⟩⟩

lemma rectangle_small_side {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (I J : Finset (Fin n))
    (hIJ : ∀ u ∈ I, ∀ v ∈ J, G.Adj u v) : I.card ≤ 1 ∨ J.card ≤ 1 := by
  classical
  by_cases hI : I.card ≤ 1
  · exact Or.inl hI
  have hIpos : I.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hIpos
  obtain ⟨c, hc, hca⟩ := Finset.exists_mem_ne (by omega : 1 < I.card) a
  have hsub : J ⊆ Finset.univ.filter fun v => G.Adj a v ∧ G.Adj c v := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hIJ a ha v hv, hIJ c hc v hv⟩
  exact Or.inr ((Finset.card_le_card hsub).trans (h4 a c hca.symm))

lemma star_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) (S : Finset (Fin n)) (hS : ∀ v ∈ S, G.Adj u v) :
    ∀ x, star u S x = true → graphFun G ∅ x = true := by
  intro x hx
  have hx' : x u = true ∧ ∃ v ∈ S, x v = true := by simpa [star, rawOr] using hx
  obtain ⟨hu, v, hv, hxv⟩ := hx'
  exact (graph_true G x).2 ⟨u, v, hS v hv, hu, hxv⟩

lemma left_filter_choice {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B C D : Finset (Fin n))
    (hB : ∀ b ∈ B, s b = true) (hD : ∀ d ∈ D, s d = true)
    (hbelow : ∀ x, quad A B C D x = true → graphFun G ∅ x = true)
    (u : Fin n) (huA : u ∈ A) (huC : u ∈ C) (hucol : s u = false) :
    (∀ b ∈ B, G.Adj u b) ∨ (∀ d ∈ D, G.Adj u d) := by
  classical
  by_cases hUB : ∀ b ∈ B, G.Adj u b
  · exact Or.inl hUB
  push Not at hUB
  obtain ⟨b, hb, hub⟩ := hUB
  right
  intro d hd
  let x := setInput (({u} : Finset (Fin n)) ∪ {b, d})
  have hquad : quad A B C D x = true := by
    apply (quad_true A B C D x).2
    exact ⟨⟨u, huA, by simp [x, setInput]⟩, ⟨b, hb, by simp [x, setInput]⟩,
      ⟨u, huC, by simp [x, setInput]⟩, ⟨d, hd, by simp [x, setInput]⟩⟩
  obtain ⟨a, ha, v, hv, hav⟩ := edge_of_two_colors G s hbip {u} {b, d}
    (by simpa using hucol)
    (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact hB _ hb
        · exact hD _ hd)
    (hbelow x hquad)
  have hau : a = u := Finset.mem_singleton.mp ha
  subst a
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact (hub hav).elim
  · exact hav

lemma right_filter_choice {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B C D : Finset (Fin n))
    (hA : ∀ a ∈ A, s a = false) (hC : ∀ c ∈ C, s c = false)
    (hbelow : ∀ x, quad A B C D x = true → graphFun G ∅ x = true)
    (v : Fin n) (hvB : v ∈ B) (hvD : v ∈ D) (hvcol : s v = true) :
    (∀ a ∈ A, G.Adj v a) ∨ (∀ c ∈ C, G.Adj v c) := by
  classical
  by_cases hVA : ∀ a ∈ A, G.Adj v a
  · exact Or.inl hVA
  push Not at hVA
  obtain ⟨a, ha, hva⟩ := hVA
  right
  intro c hc
  let x := setInput (({a, c} : Finset (Fin n)) ∪ {v})
  have hquad : quad A B C D x = true := by
    apply (quad_true A B C D x).2
    exact ⟨⟨a, ha, by simp [x, setInput]⟩, ⟨v, hvB, by simp [x, setInput]⟩,
      ⟨c, hc, by simp [x, setInput]⟩, ⟨v, hvD, by simp [x, setInput]⟩⟩
  obtain ⟨u, hu, b, hb, hub⟩ := edge_of_two_colors G s hbip {a, c} {v}
    (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hA _ ha
        · exact hC _ hc)
    (by simpa using hvcol)
    (hbelow x hquad)
  have hbv : b = v := Finset.mem_singleton.mp hb
  subst b
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl
  · exact (hva hub.symm).elim
  · exact hub.symm

lemma replacement_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (A B C D : Finset (Fin n))
    (hA : ∀ a ∈ A, s a = false) (hB : ∀ b ∈ B, s b = true)
    (hC : ∀ c ∈ C, s c = false) (hD : ∀ d ∈ D, s d = true)
    (hbelow : ∀ x, quad A B C D x = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧ quad A B C D (pairInput a b) = true) :
    ∃ (u : Fin n) (S : Finset (Fin n)),
      (S = A ∨ S = B ∨ S = C ∨ S = D) ∧
      (∀ x, star u S x = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → quad A B C D (pairInput a b) = true →
        star u S (pairInput a b) = true) := by
  classical
  have hPair := pair_colored_intersections s A B C D hA hB hC hD
  obtain ⟨a, b, hab, habq⟩ := haccept
  have hIJne : (A ∩ C).Nonempty ∧ (B ∩ D).Nonempty := by
    rcases (hPair a b).mp habq with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    · exact ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
  have hIJ : ∀ u ∈ A ∩ C, ∀ v ∈ B ∩ D, G.Adj u v := by
    intro u hu v hv
    have htrue := hbelow (pairInput u v) ((hPair u v).2 (Or.inl ⟨hu, hv⟩))
    obtain ⟨p, q, hpq, hp, hq⟩ := (graph_true G _).mp htrue
    have hp' : p = u ∨ p = v := by simpa [pairInput] using hp
    have hq' : q = u ∨ q = v := by simpa [pairInput] using hq
    rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
    · exact (G.irrefl hpq).elim
    · exact hpq
    · exact hpq.symm
    · exact (G.irrefl hpq).elim
  rcases rectangle_small_side G h4 (A ∩ C) (B ∩ D) hIJ with hI | hJ
  · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp (le_antisymm hI (Finset.card_pos.mpr hIJne.1))
    have huAC : u ∈ A ∩ C := by rw [hu]; simp
    obtain ⟨huA, huC⟩ := Finset.mem_inter.mp huAC
    have hret : ∀ S : Finset (Fin n), B ∩ D ⊆ S →
        ∀ a b, quad A B C D (pairInput a b) = true → star u S (pairInput a b) = true := by
      intro S hS a b hq
      rcases (hPair a b).mp hq with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · have hau : a = u := by simpa [hu] using ha
        subst a
        simp only [star, rawOr, pairInput, true_or, decide_true, Bool.true_and, decide_eq_true_eq]
        exact ⟨b, hS hb, Or.inr rfl⟩
      · have hbu : b = u := by simpa [hu] using hb
        subst b
        simp only [star, rawOr, pairInput, or_true, decide_true, Bool.true_and, decide_eq_true_eq]
        exact ⟨a, hS ha, Or.inl rfl⟩
    rcases left_filter_choice G s hbip A B C D hB hD hbelow u huA huC (hA u huA) with hB' | hD'
    · exact ⟨u, B, Or.inr (Or.inl rfl), star_below G u B hB',
        fun a b _ hq => hret B Finset.inter_subset_left a b hq⟩
    · exact ⟨u, D, Or.inr (Or.inr (Or.inr rfl)), star_below G u D hD',
        fun a b _ hq => hret D Finset.inter_subset_right a b hq⟩
  · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (le_antisymm hJ (Finset.card_pos.mpr hIJne.2))
    have hvBD : v ∈ B ∩ D := by rw [hv]; simp
    obtain ⟨hvB, hvD⟩ := Finset.mem_inter.mp hvBD
    have hret : ∀ S : Finset (Fin n), A ∩ C ⊆ S →
        ∀ a b, quad A B C D (pairInput a b) = true → star v S (pairInput a b) = true := by
      intro S hS a b hq
      rcases (hPair a b).mp hq with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · have hbv : b = v := by simpa [hv] using hb
        subst b
        simp only [star, rawOr, pairInput, or_true, decide_true, Bool.true_and, decide_eq_true_eq]
        exact ⟨a, hS ha, Or.inl rfl⟩
      · have hav : a = v := by simpa [hv] using ha
        subst a
        simp only [star, rawOr, pairInput, true_or, decide_true, Bool.true_and, decide_eq_true_eq]
        exact ⟨b, hS hb, Or.inr rfl⟩
    rcases right_filter_choice G s hbip A B C D hA hC hbelow v hvB hvD (hB v hvB) with hA' | hC'
    · exact ⟨v, A, Or.inl rfl, star_below G v A hA',
        fun a b _ hq => hret A Finset.inter_subset_left a b hq⟩
    · exact ⟨v, C, Or.inr (Or.inr (Or.inl rfl)), star_below G v C hC',
        fun a b _ hq => hret C Finset.inter_subset_right a b hq⟩

lemma replacement_star_ordered {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (A B C D : Finset (Fin n))
    (hA : ∀ a ∈ A, s a = false) (hB : ∀ b ∈ B, s b = true)
    (hC : ∀ c ∈ C, s c = false) (hD : ∀ d ∈ D, s d = true)
    (hbelow : ∀ x, quad A B C D x = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧ quad A B C D (pairInput a b) = true) :
    ∃ (u : Fin n) (S : Finset (Fin n)),
      (S = A ∨ S = B ∨ S = C ∨ S = D) ∧ S.Nonempty ∧ u ∉ S ∧
      (∀ a b, G.Adj a b → quad A B C D (pairInput a b) ≤ star u S (pairInput a b)) ∧
      (∀ x, graphFun G ∅ x = false → star u S x ≤ quad A B C D x) := by
  obtain ⟨u, S, hside, hstar, hretain⟩ :=
    replacement_star G s hbip h4 A B C D hA hB hC hD hbelow haccept
  have hS : S.Nonempty := by
    obtain ⟨a, b, hab, hq⟩ := haccept
    have hs := hretain a b hab hq
    have hs' : pairInput a b u = true ∧ ∃ v ∈ S, pairInput a b v = true := by
      simpa [star, rawOr] using hs
    obtain ⟨v, hv, _⟩ := hs'.2
    exact ⟨v, hv⟩
  have huS : u ∉ S := by
    intro hu
    have hs : star u S (pairInput u u) = true := by
      simp only [star, rawOr, pairInput, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Or.inl trivial, ⟨u, hu, Or.inl rfl⟩⟩
    obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G _).mp (hstar _ hs)
    have ha' : a = u := by simpa [pairInput] using ha
    have hb' : b = u := by simpa [pairInput] using hb
    subst a
    subst b
    exact G.irrefl hab
  refine ⟨u, S, hside, hS, huS, ?_, ?_⟩
  · intro a b hab
    apply Bool.le_iff_imp.mpr
    exact hretain a b hab
  · intro x hx
    apply Bool.le_iff_imp.mpr
    intro hs
    have heq := hstar x hs
    rw [hx] at heq
    cases heq

end PEqualNP.Outside.L_meta_3566.RectangleSelection


namespace PEqualNP.Outside.L_meta_3566.GateReplace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership Splice

def replace (C : Circuit) (j : ℕ) (g : Gate) : Circuit :=
  ⟨C.gates.set j g, C.output⟩

lemma replace_size (C : Circuit) (j : ℕ) (g : Gate) : (replace C j g).size = C.size := by
  simp [replace, Circuit.size]

lemma replace_gateAt (C : Circuit) (j : ℕ) (g : Gate) (hj : j < C.gates.length) (k : ℕ) :
    gateAt (replace C j g) k = if j = k then g else gateAt C k := by
  simp only [gateAt, replace, List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs with he
  · simp [hj]
  · rfl

lemma replace_ao {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgop : g.op = GateOp.and ∨ g.op = GateOp.or) (hglen : g.inputs.length = 2)
    (hgback : ∀ i ∈ g.inputs, i < n + j) : IsAO2 n (replace C j g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    change h ∈ C.gates.set j g at hh
    rw [List.set_eq_take_cons_drop g hj] at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hAO.1 _ (List.mem_of_mem_take hh)
    · rcases List.mem_cons.mp hh with rfl | hh
      · exact hgop
      · exact hAO.1 _ (List.mem_of_mem_drop hh)
  · intro k hk i hi
    have hk' : k < C.gates.length := by simpa [replace] using hk
    rw [replace_gateAt C j g hj k] at hi
    by_cases he : j = k
    · subst k
      simp only [ite_true] at hi
      exact hgback i hi
    · rw [ite_eq_right he] at hi
      exact hAO.2.1 k hk' i hi
  · intro h hh
    change h ∈ C.gates.set j g at hh
    rw [List.set_eq_take_cons_drop g hj] at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hAO.2.2 _ (List.mem_of_mem_take hh)
    · rcases List.mem_cons.mp hh with rfl | hh
      · exact hglen
      · exact hAO.2.2 _ (List.mem_of_mem_drop hh)

lemma step_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b)
    (a b : List Bool) (hlen : a.length = b.length) (g h : Gate)
    (hab : ∀ i, R (a.getD i false) (b.getD i false))
    (hval : R (g.op.eval (g.inputs.map fun i => a.getD i false))
      (h.op.eval (h.inputs.map fun i => b.getD i false))) :
    ∀ i, R ((stepWire a g).getD i false) ((stepWire b h).getD i false) := by
  intro i
  by_cases hi : i < a.length
  · rw [stepWire_getD_lt _ _ _ hi, stepWire_getD_lt _ _ _ (by omega)]
    exact hab i
  · by_cases he : i = a.length
    · rw [he, stepWire_getD_len, hlen, stepWire_getD_len]
      exact hval
    · rw [getD_ge_length _ _ (by simp [stepWire]; omega),
        getD_ge_length _ _ (by simp [stepWire]; omega)]
      exact hrefl false

lemma foldl_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b)
    (gs : List Gate)
    (hmono : ∀ g ∈ gs, ∀ (f h : ℕ → Bool), (∀ i, R (f i) (h i)) →
      R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map h)))
    (a b : List Bool) (hlen : a.length = b.length)
    (hab : ∀ i, R (a.getD i false) (b.getD i false)) :
    ∀ i, R ((gs.foldl stepWire a).getD i false) ((gs.foldl stepWire b).getD i false) := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih (fun g hg => hmono g (by simp [hg]))
      (stepWire a g) (stepWire b g) (by simp [stepWire, hlen])
      (step_rel hrefl a b hlen g g hab (hmono g (by simp) _ _ hab))

lemma replace_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b)
    (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hmono : ∀ g ∈ C.gates, ∀ (f h : ℕ → Bool), (∀ i, R (f i) (h i)) →
      R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map h)))
    (x : Fin n → Bool)
    (hx : R ((C.wires (List.ofFn x)).getD (n + j) false)
      (g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false))) :
    R (circuitFun n C x) (circuitFun n (replace C j g) x) := by
  obtain ⟨pre, post, old, hgs, hpre_len, htake, hdrop, _⟩ := split_gates C.gates j hj
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0 : w0.length = n + j := by
    dsimp [w0]
    rw [foldl_stepWire_length, List.length_ofFn, hpre_len]
  have hpre : ∀ i, i < n + j →
      (C.wires (List.ofFn x)).getD i false = w0.getD i false := by
    intro i hi
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons,
      foldl_stepWire_getD_lt _ _ _ (by change i < (stepWire w0 old).length; simp [stepWire, hw0]; omega),
      stepWire_getD_lt _ _ _ (by change i < w0.length; omega)]
  have hm : g.inputs.map (fun i => (C.wires (List.ofFn x)).getD i false) =
      g.inputs.map (fun i => w0.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact hpre i (hgback i hi)
  rw [hm, wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons,
    foldl_stepWire_getD_lt _ _ _ (by change n+j < (stepWire w0 old).length; simp [stepWire, hw0])] at hx
  have hx2 := stepWire_getD_len w0 old
  rw [hw0] at hx2
  rw [hx2] at hx
  have start := step_rel hrefl w0 w0 rfl old g (fun _ => hrefl _) hx
  have result := foldl_rel hrefl post
    (fun h hh => hmono h (hgs ▸ by simp [hh]))
    (stepWire w0 old) (stepWire w0 g) (by simp [stepWire]) start C.output
  simp only [circuitFun, Circuit.eval, replace, wires_eq_foldl]
  rw [List.set_eq_take_cons_drop g hj, htake, hdrop, hgs,
    List.foldl_append, List.foldl_cons, List.foldl_append, List.foldl_cons]
  exact result

lemma replace_le (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j) (hAO : AndOrOnly C) (x : Fin n → Bool)
    (hx : (C.wires (List.ofFn x)).getD (n + j) false ≤
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false)) :
    circuitFun n C x ≤ circuitFun n (replace C j g) x :=
  replace_rel (fun _ => le_refl _) n C j hj g hgback
    (fun h hh => ao_eval_mono h (hAO h hh)) x hx

lemma replace_ge (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j) (hAO : AndOrOnly C) (x : Fin n → Bool)
    (hx : g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) ≤
      (C.wires (List.ofFn x)).getD (n + j) false) :
    circuitFun n (replace C j g) x ≤ circuitFun n C x :=
  replace_rel (R := fun a b => b ≤ a) (fun _ => le_refl _) n C j hj g hgback
    (fun h hh f k hfk => ao_eval_mono h (hAO h hh) k f hfk) x hx

lemma correct_of_edge_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgop : g.op = GateOp.and ∨ g.op = GateOp.or) (hglen : g.inputs.length = 2)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hpos : ∀ u v, G.Adj u v →
      (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD (n + j) false = true →
      g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD i false) = true)
    (hclean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
      graphFun G ∅ x = true) :
    IsAO2 n (replace C j g) ∧ circuitFun n (replace C j g) = graphFun G ∅ ∧
      (replace C j g).size = C.size := by
  have hd := replace_ao C hAO j hj g hgop hglen hgback
  refine ⟨hd, ?_, replace_size C j g⟩
  apply (graphFun_boundary_iff G _ (circuitFun_monotone n _ hd.1)).2
  constructor
  · intro u v huv
    apply bool_true_of_le (replace_le n C j hj g hgback hAO.1 _
      (Bool.le_iff_imp.mpr (hpos u v huv)))
    rw [hfun]
    exact graphFun_pair_true G huv
  · intro S hS
    have hfalse : g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn (supportInput S))).getD i false) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have := hclean _ ht
      rw [graphFun_independent_false G hS.1] at this
      contradiction
    apply bool_false_of_le (replace_ge n C j hj g hgback hAO.1 _ (by rw [hfalse]; exact Bool.false_le _))
    rw [hfun]
    exact graphFun_independent_false G hS.1

end PEqualNP.Outside.L_meta_3566.GateReplace

namespace PEqualNP.Outside.L_meta_3566.RectangleCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership RectangleSelection

lemma input_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    (C.wires (List.ofFn x)).getD u.val false = x u := by
  rw [Splice.wires_eq_foldl, Splice.foldl_stepWire_getD_lt _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma replace_two_rectangles {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (j : ℕ) (hj : j < C.gates.length)
    (A B K D : Finset (Fin n))
    (hA : ∀ a ∈ A, s a = false) (hB : ∀ b ∈ B, s b = true)
    (hK : ∀ a ∈ K, s a = false) (hD : ∀ b ∈ D, s b = true)
    (wA wB wK wD : ℕ)
    (hbackA : wA < n + j) (hbackB : wB < n + j)
    (hbackK : wK < n + j) (hbackD : wD < n + j)
    (hvA : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD wA false = rawOr A x)
    (hvB : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD wB false = rawOr B x)
    (hvK : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD wK false = rawOr K x)
    (hvD : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD wD false = rawOr D x)
    (hjval : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + j) false = quad A B K D x)
    (hbelow : ∀ x, quad A B K D x = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧ quad A B K D (pairInput a b) = true) :
    ∃ (u : Fin n) (S : Finset (Fin n)) (w : ℕ),
      (S = A ∨ S = B ∨ S = K ∨ S = D) ∧ w < n + j ∧
      (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = rawOr S x) ∧
      IsAO2 n (GateReplace.replace C j ⟨GateOp.and, [u.val, w]⟩) ∧
      circuitFun n (GateReplace.replace C j ⟨GateOp.and, [u.val, w]⟩) = graphFun G ∅ ∧
      (GateReplace.replace C j ⟨GateOp.and, [u.val, w]⟩).size = C.size := by
  obtain ⟨u, S, hside, hclean, hkeep⟩ :=
    replacement_star G s hbip h4 A B K D hA hB hK hD hbelow haccept
  have hw : ∃ w : ℕ, w < n + j ∧
      ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = rawOr S x := by
    rcases hside with rfl | rfl | rfl | rfl
    · exact ⟨wA, hbackA, hvA⟩
    · exact ⟨wB, hbackB, hvB⟩
    · exact ⟨wK, hbackK, hvK⟩
    · exact ⟨wD, hbackD, hvD⟩
  obtain ⟨w, hwback, hwval⟩ := hw
  refine ⟨u, S, w, hside, hwback, hwval, ?_⟩
  have hgate : ∀ x : Fin n → Bool,
      GateOp.and.eval ([u.val, w].map fun i => (C.wires (List.ofFn x)).getD i false) =
        star u S x := by
    intro x
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [input_val, hwval]
    rfl
  apply GateReplace.correct_of_edge_cover G C hAO hfun j hj ⟨GateOp.and, [u.val, w]⟩
    (Or.inl rfl) rfl
  · intro i hi
    simp at hi
    rcases hi with rfl | rfl
    · omega
    · exact hwback
  · intro a b hab ht
    rw [hjval] at ht
    simpa only [hgate] using hkeep a b hab ht
  · intro x ht
    apply hclean x
    simpa only [hgate] using ht

end PEqualNP.Outside.L_meta_3566.RectangleCircuit


namespace PEqualNP.Outside.L_meta_3566.RectangleFamily

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def setInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun u => decide (u ∈ S)

def rawOr {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ u ∈ S, x u = true)

def star {n : ℕ} (u : Fin n) (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  x u && rawOr S x

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : graphFun G ∅ x = true ↔
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  simp [graphFun]

lemma edge_of_two_colors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (L R : Finset (Fin n))
    (hL : ∀ u ∈ L, s u = false) (hR : ∀ v ∈ R, s v = true)
    (hx : graphFun G ∅ (setInput (L ∪ R)) = true) :
    ∃ a ∈ L, ∃ b ∈ R, G.Adj a b := by
  obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G _).mp hx
  have ha' : a ∈ L ∪ R := by simpa [setInput] using ha
  have hb' : b ∈ L ∪ R := by simpa [setInput] using hb
  rcases Finset.mem_union.mp ha' with haL | haR <;>
    rcases Finset.mem_union.mp hb' with hbL | hbR
  · exact False.elim ((hbip a b hab) ((hL a haL).trans (hL b hbL).symm))
  · exact ⟨a, haL, b, hbR, hab⟩
  · exact ⟨b, hbL, a, haR, hab.symm⟩
  · exact False.elim ((hbip a b hab) ((hR a haR).trans (hR b hbR).symm))

lemma rectangle_small_side {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (I J : Finset (Fin n))
    (hIJ : ∀ u ∈ I, ∀ v ∈ J, G.Adj u v) : I.card ≤ 1 ∨ J.card ≤ 1 := by
  classical
  by_cases hI : I.card ≤ 1
  · exact Or.inl hI
  have hIpos : I.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hIpos
  obtain ⟨c, hc, hca⟩ := Finset.exists_mem_ne (by omega : 1 < I.card) a
  have hsub : J ⊆ Finset.univ.filter fun v => G.Adj a v ∧ G.Adj c v := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hIJ a ha v hv, hIJ c hc v hv⟩
  exact Or.inr ((Finset.card_le_card hsub).trans (h4 a c hca.symm))

lemma star_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) (S : Finset (Fin n)) (hS : ∀ v ∈ S, G.Adj u v) :
    ∀ x, star u S x = true → graphFun G ∅ x = true := by
  intro x hx
  have hx' : x u = true ∧ ∃ v ∈ S, x v = true := by simpa [star, rawOr] using hx
  obtain ⟨hu, v, hv, hxv⟩ := hx'
  exact (graph_true G x).2 ⟨u, v, hS v hv, hu, hxv⟩

def common {n k : ℕ} (A : Fin k → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∀ i, u ∈ A i

def family {n k : ℕ} (A B : Fin k → Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∀ i, rawOr (A i) x = true ∧ rawOr (B i) x = true)

lemma family_true {n k : ℕ} (A B : Fin k → Finset (Fin n)) (x : Fin n → Bool) :
    family A B x = true ↔
      ∀ i, (∃ a ∈ A i, x a = true) ∧ (∃ b ∈ B i, x b = true) := by
  simp [family, rawOr]

lemma rawOr_pair {n : ℕ} (S : Finset (Fin n)) (u v : Fin n) :
    rawOr S (pairInput u v) = true ↔ u ∈ S ∨ v ∈ S := by
  simp [rawOr, pairInput, and_or_left, exists_or]

lemma family_pair {n k : ℕ} (hk : 0 < k) (s : Fin n → Bool)
    (A B : Fin k → Finset (Fin n))
    (hA : ∀ i a, a ∈ A i → s a = false) (hB : ∀ i b, b ∈ B i → s b = true)
    (u v : Fin n) :
    family A B (pairInput u v) = true ↔
      (u ∈ common A ∧ v ∈ common B) ∨ (v ∈ common A ∧ u ∈ common B) := by
  constructor
  · intro h
    have h' : ∀ i, (u ∈ A i ∨ v ∈ A i) ∧ (u ∈ B i ∨ v ∈ B i) := by
      intro i
      have hi : rawOr (A i) (pairInput u v) = true ∧ rawOr (B i) (pairInput u v) = true :=
        (of_decide_eq_true h) i
      exact ⟨(rawOr_pair _ _ _).mp hi.1, (rawOr_pair _ _ _).mp hi.2⟩
    let i0 : Fin k := ⟨0, hk⟩
    cases hu : s u with
    | false =>
      have hv : s v = true := by
        rcases (h' i0).2 with hbu | hbv
        · have hc := hB i0 u hbu
          rw [hu] at hc
          cases hc
        · exact hB i0 v hbv
      left
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ u, ?_⟩
        intro i
        rcases (h' i).1 with hau | hav
        · exact hau
        · have hc := hA i v hav
          rw [hv] at hc
          cases hc
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ v, ?_⟩
        intro i
        rcases (h' i).2 with hbu | hbv
        · have hc := hB i u hbu
          rw [hu] at hc
          cases hc
        · exact hbv
    | true =>
      have hv : s v = false := by
        rcases (h' i0).1 with hau | hav
        · have hc := hA i0 u hau
          rw [hu] at hc
          cases hc
        · exact hA i0 v hav
      right
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ v, ?_⟩
        intro i
        rcases (h' i).1 with hau | hav
        · have hc := hA i u hau
          rw [hu] at hc
          cases hc
        · exact hav
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ u, ?_⟩
        intro i
        rcases (h' i).2 with hbu | hbv
        · exact hbu
        · have hc := hB i v hbv
          rw [hv] at hc
          cases hc
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · apply (family_true A B _).2
      intro i
      exact ⟨⟨u, (Finset.mem_filter.mp hu).2 i, by simp [pairInput]⟩,
        ⟨v, (Finset.mem_filter.mp hv).2 i, by simp [pairInput]⟩⟩
    · apply (family_true A B _).2
      intro i
      exact ⟨⟨v, (Finset.mem_filter.mp hv).2 i, by simp [pairInput]⟩,
        ⟨u, (Finset.mem_filter.mp hu).2 i, by simp [pairInput]⟩⟩

lemma family_left_choice {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B : Fin k → Finset (Fin n))
    (hB : ∀ i b, b ∈ B i → s b = true)
    (hbelow : ∀ x, family A B x = true → graphFun G ∅ x = true)
    (u : Fin n) (hu : u ∈ common A) (hucol : s u = false) :
    ∃ i, ∀ b ∈ B i, G.Adj u b := by
  classical
  by_contra hnone
  push Not at hnone
  choose b hb hbad using hnone
  let R : Finset (Fin n) := Finset.univ.image b
  let x := setInput (({u} : Finset (Fin n)) ∪ R)
  have hx : family A B x = true := by
    apply (family_true A B x).2
    intro i
    refine ⟨⟨u, (Finset.mem_filter.mp hu).2 i, by simp [x, setInput]⟩, b i, hb i, ?_⟩
    have hbi : b i ∈ R := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    simp [x, setInput, hbi]
  have hR : ∀ v ∈ R, s v = true := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact hB i (b i) (hb i)
  obtain ⟨a, ha, v, hv, hav⟩ :=
    edge_of_two_colors G s hbip {u} R (by simpa using hucol) hR (hbelow x hx)
  have hau : a = u := Finset.mem_singleton.mp ha
  subst a
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  exact hbad i hav

lemma family_right_choice {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B : Fin k → Finset (Fin n))
    (hA : ∀ i a, a ∈ A i → s a = false)
    (hbelow : ∀ x, family A B x = true → graphFun G ∅ x = true)
    (v : Fin n) (hv : v ∈ common B) (hvcol : s v = true) :
    ∃ i, ∀ a ∈ A i, G.Adj v a := by
  classical
  by_contra hnone
  push Not at hnone
  choose a ha hbad using hnone
  let L : Finset (Fin n) := Finset.univ.image a
  let x := setInput (L ∪ ({v} : Finset (Fin n)))
  have hx : family A B x = true := by
    apply (family_true A B x).2
    intro i
    refine ⟨⟨a i, ha i, ?_⟩, v, (Finset.mem_filter.mp hv).2 i, by simp [x, setInput]⟩
    have hai : a i ∈ L := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    simp [x, setInput, hai]
  have hL : ∀ u ∈ L, s u = false := by
    intro u hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    exact hA i (a i) (ha i)
  obtain ⟨u, hu, b, hb, hub⟩ :=
    edge_of_two_colors G s hbip L {v} hL (by simpa using hvcol) (hbelow x hx)
  have hbv : b = v := Finset.mem_singleton.mp hb
  subst b
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
  exact hbad i hub.symm

lemma replacement_star {n k : ℕ} (hk : 0 < k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (A B : Fin k → Finset (Fin n))
    (hA : ∀ i a, a ∈ A i → s a = false) (hB : ∀ i b, b ∈ B i → s b = true)
    (hbelow : ∀ x, family A B x = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧ family A B (pairInput a b) = true) :
    ∃ (u : Fin n) (i : Fin k) (S : Finset (Fin n)),
      (S = A i ∨ S = B i) ∧
      (∀ x, star u S x = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → family A B (pairInput a b) = true →
        star u S (pairInput a b) = true) := by
  classical
  have hPair := family_pair hk s A B hA hB
  obtain ⟨a, b, hab, habf⟩ := haccept
  have hIJne : (common A).Nonempty ∧ (common B).Nonempty := by
    rcases (hPair a b).mp habf with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    · exact ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
  have hIJ : ∀ u ∈ common A, ∀ v ∈ common B, G.Adj u v := by
    intro u hu v hv
    have htrue := hbelow (pairInput u v) ((hPair u v).2 (Or.inl ⟨hu, hv⟩))
    obtain ⟨p, q, hpq, hp, hq⟩ := (graph_true G _).mp htrue
    have hp' : p = u ∨ p = v := by simpa [pairInput] using hp
    have hq' : q = u ∨ q = v := by simpa [pairInput] using hq
    rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
    · exact (G.irrefl hpq).elim
    · exact hpq
    · exact hpq.symm
    · exact (G.irrefl hpq).elim
  let i0 : Fin k := ⟨0, hk⟩
  rcases rectangle_small_side G h4 (common A) (common B) hIJ with hI | hJ
  · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp (le_antisymm hI (Finset.card_pos.mpr hIJne.1))
    have huA : u ∈ common A := by rw [hu]; simp
    obtain ⟨i, hi⟩ := family_left_choice G s hbip A B hB hbelow u huA
      (hA i0 u ((Finset.mem_filter.mp huA).2 i0))
    refine ⟨u, i, B i, Or.inr rfl, star_below G u (B i) hi, ?_⟩
    intro a b _ hq
    rcases (hPair a b).mp hq with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · have hau : a = u := by simpa [hu] using ha
      subst a
      simp only [star, rawOr, pairInput, true_or, decide_true, Bool.true_and, decide_eq_true_eq]
      exact ⟨b, (Finset.mem_filter.mp hb).2 i, Or.inr rfl⟩
    · have hbu : b = u := by simpa [hu] using hb
      subst b
      simp only [star, rawOr, pairInput, or_true, decide_true, Bool.true_and, decide_eq_true_eq]
      exact ⟨a, (Finset.mem_filter.mp ha).2 i, Or.inl rfl⟩
  · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (le_antisymm hJ (Finset.card_pos.mpr hIJne.2))
    have hvB : v ∈ common B := by rw [hv]; simp
    obtain ⟨i, hi⟩ := family_right_choice G s hbip A B hA hbelow v hvB
      (hB i0 v ((Finset.mem_filter.mp hvB).2 i0))
    refine ⟨v, i, A i, Or.inl rfl, star_below G v (A i) hi, ?_⟩
    intro a b _ hq
    rcases (hPair a b).mp hq with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · have hbv : b = v := by simpa [hv] using hb
      subst b
      simp only [star, rawOr, pairInput, or_true, decide_true, Bool.true_and, decide_eq_true_eq]
      exact ⟨a, (Finset.mem_filter.mp ha).2 i, Or.inl rfl⟩
    · have hav : a = v := by simpa [hv] using ha
      subst a
      simp only [star, rawOr, pairInput, true_or, decide_true, Bool.true_and, decide_eq_true_eq]
      exact ⟨b, (Finset.mem_filter.mp hb).2 i, Or.inr rfl⟩

end PEqualNP.Outside.L_meta_3566.RectangleFamily

namespace PEqualNP.Outside.L_meta_3566.RectangleCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma replace_rectangle_family {n k : ℕ} (hk : 0 < k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (j : ℕ) (hj : j < C.gates.length) (A B : Fin k → Finset (Fin n))
    (hA : ∀ i a, a ∈ A i → s a = false) (hB : ∀ i b, b ∈ B i → s b = true)
    (wA wB : Fin k → ℕ)
    (hbackA : ∀ i, wA i < n + j) (hbackB : ∀ i, wB i < n + j)
    (hvA : ∀ i (x : Fin n → Bool),
      (C.wires (List.ofFn x)).getD (wA i) false = RectangleFamily.rawOr (A i) x)
    (hvB : ∀ i (x : Fin n → Bool),
      (C.wires (List.ofFn x)).getD (wB i) false = RectangleFamily.rawOr (B i) x)
    (hjval : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + j) false = RectangleFamily.family A B x)
    (hbelow : ∀ x, RectangleFamily.family A B x = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧ RectangleFamily.family A B (pairInput a b) = true) :
    ∃ (u : Fin n) (i : Fin k) (S : Finset (Fin n)) (w : ℕ),
      (S = A i ∨ S = B i) ∧ w < n + j ∧
      (∀ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD w false = RectangleFamily.rawOr S x) ∧
      IsAO2 n (GateReplace.replace C j ⟨GateOp.and, [u.val, w]⟩) ∧
      circuitFun n (GateReplace.replace C j ⟨GateOp.and, [u.val, w]⟩) = graphFun G ∅ ∧
      (GateReplace.replace C j ⟨GateOp.and, [u.val, w]⟩).size = C.size := by
  obtain ⟨u, i, S, hside, hclean, hkeep⟩ :=
    RectangleFamily.replacement_star hk G s hbip h4 A B hA hB hbelow haccept
  have hw : ∃ w : ℕ, w < n + j ∧ ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD w false = RectangleFamily.rawOr S x := by
    rcases hside with rfl | rfl
    · exact ⟨wA i, hbackA i, hvA i⟩
    · exact ⟨wB i, hbackB i, hvB i⟩
  obtain ⟨w, hwback, hwval⟩ := hw
  refine ⟨u, i, S, w, hside, hwback, hwval, ?_⟩
  have hgate : ∀ x : Fin n → Bool,
      GateOp.and.eval ([u.val, w].map fun i => (C.wires (List.ofFn x)).getD i false) =
        RectangleFamily.star u S x := by
    intro x
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [input_val, hwval]
    rfl
  apply GateReplace.correct_of_edge_cover G C hAO hfun j hj ⟨GateOp.and, [u.val, w]⟩
    (Or.inl rfl) rfl
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl
    · omega
    · exact hwback
  · intro a b hab ht
    rw [hjval] at ht
    simpa only [hgate] using hkeep a b hab ht
  · intro x ht
    apply hclean x
    simpa only [hgate] using ht

end PEqualNP.Outside.L_meta_3566.RectangleCircuit



namespace PEqualNP.Outside.L_meta_3566.PureFunctionFamily

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def family {n k : ℕ} (L R : Fin k → (Fin n → Bool) → Bool) (x : Fin n → Bool) : Bool :=
  decide (∀ i, L i x = true ∧ R i x = true)

def maskTrue {n : ℕ} (s x : Fin n → Bool) : Fin n → Bool :=
  fun v => if s v = true then x v else false

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : graphFun G ∅ x = true ↔
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  simp [graphFun]

lemma true_of_le {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  exact Bool.le_iff_imp.mp h ha

lemma existing_filter {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (L R : Fin k → (Fin n → Bool) → Bool)
    (hLmono : ∀ i, Monotone (L i)) (hRmono : ∀ i, Monotone (R i))
    (hRpure : ∀ i x, R i x = R i (maskTrue s x))
    (hbelow : ∀ x, family L R x = true → graphFun G ∅ x = true)
    (u : Fin n) (hucol : s u = false)
    (hLu : ∀ i, L i (pairInput u u) = true) :
    ∃ i, ∀ x, x u && R i x = true → graphFun G ∅ x = true := by
  classical
  by_contra hnone
  push Not at hnone
  choose X hX hbad using hnone
  have hX' : ∀ i, X i u = true ∧ R i (X i) = true := by
    intro i
    simpa using hX i
  have hXu : ∀ i, X i u = true := fun i => (hX' i).1
  have hXR : ∀ i, R i (X i) = true := fun i => (hX' i).2
  let x : Fin n → Bool := fun v => decide (v = u ∨ ∃ i, s v = true ∧ X i v = true)
  have hxu : x u = true := by simp [x]
  have hsingle : pairInput u u ≤ x := by
    intro v
    apply Bool.le_iff_imp.mpr
    intro hv
    have hvu : v = u := by simpa [pairInput] using hv
    subst v
    exact hxu
  have hmask : ∀ i, maskTrue s (X i) ≤ x := by
    intro i v
    apply Bool.le_iff_imp.mpr
    intro hv
    have hcolor : s v = true := by
      by_contra hcolor
      simp [maskTrue, hcolor] at hv
    have hXv : X i v = true := by simpa [maskTrue, hcolor] using hv
    change decide (v = u ∨ ∃ i, s v = true ∧ X i v = true) = true
    exact decide_eq_true (Or.inr ⟨i, hcolor, hXv⟩)
  have hfamily : family L R x = true := by
    apply decide_eq_true
    intro i
    constructor
    · exact true_of_le (hLmono i hsingle) (hLu i)
    · apply true_of_le (hRmono i (hmask i))
      rw [← hRpure i (X i)]
      exact hXR i
  obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G x).mp (hbelow x hfamily)
  have ha' : a = u ∨ ∃ i, s a = true ∧ X i a = true := by simpa [x] using ha
  have hb' : b = u ∨ ∃ i, s b = true ∧ X i b = true := by simpa [x] using hb
  rcases ha' with rfl | ⟨i, hacol, hai⟩ <;>
    rcases hb' with rfl | ⟨j, hbcol, hbj⟩
  · exact G.irrefl hab
  · exact hbad j ((graph_true G (X j)).2 ⟨_, _, hab, hXu j, hbj⟩)
  · exact hbad i ((graph_true G (X i)).2 ⟨_, _, hab, hai, hXu i⟩)
  · exact (hbip a b hab) (hacol.trans hbcol.symm)


lemma mask_pair {n : ℕ} (s : Fin n → Bool) (u v : Fin n)
    (hu : s u = true) (hv : s v = false) :
    maskTrue s (pairInput u v) = pairInput u u := by
  funext w
  by_cases hwu : w = u
  · subst w
    simp [maskTrue, pairInput, hu]
  · by_cases hwv : w = v
    · subst w
      simp [maskTrue, pairInput, hv, hwu]
    · simp [maskTrue, pairInput, hwu, hwv]

lemma mask_pair_swap {n : ℕ} (s : Fin n → Bool) (u v : Fin n)
    (hu : s u = false) (hv : s v = true) :
    maskTrue s (pairInput u v) = pairInput v v := by
  have hswap : pairInput u v = pairInput v u := by
    funext w
    simp [pairInput, or_comm]
  rw [hswap]
  exact mask_pair s v u hv hu

lemma mask_single_false {n : ℕ} (s : Fin n → Bool) (u : Fin n)
    (hu : s u = false) : maskTrue s (pairInput u u) = (fun _ => false) := by
  funext w
  by_cases hwu : w = u
  · subst w
    simp [maskTrue, hu]
  · simp [maskTrue, pairInput, hwu]

lemma singleton_color {n : ℕ} (s : Fin n → Bool) (f : (Fin n → Bool) → Bool)
    (hpure : ∀ x, f x = f (maskTrue s x)) (hzero : f (fun _ => false) = false)
    (u : Fin n) (hu : f (pairInput u u) = true) : s u = true := by
  cases hs : s u with
  | false =>
    rw [hpure (pairInput u u), mask_single_false s u hs, hzero] at hu
    cases hu
  | true => rfl

def commonSupport {n k : ℕ} (F : Fin k → (Fin n → Bool) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∀ i, F i (pairInput u u) = true

lemma family_pair_left_right {n k : ℕ} (s : Fin n → Bool)
    (L R : Fin k → (Fin n → Bool) → Bool)
    (hLpure : ∀ i x, L i x = L i (maskTrue (fun w => !(s w)) x))
    (hRpure : ∀ i x, R i x = R i (maskTrue s x))
    (u v : Fin n) (hu : s u = false) (hv : s v = true) :
    family L R (pairInput u v) = true ↔ u ∈ commonSupport L ∧ v ∈ commonSupport R := by
  have hLu : ∀ i, L i (pairInput u v) = L i (pairInput u u) := by
    intro i
    rw [hLpure i (pairInput u v), mask_pair (fun w => !(s w)) u v (by simp [hu]) (by simp [hv])]
  have hRv : ∀ i, R i (pairInput u v) = R i (pairInput v v) := by
    intro i
    rw [hRpure i (pairInput u v), mask_pair_swap s u v hu hv]
  simp only [family, decide_eq_true_eq, commonSupport, Finset.mem_filter,
    Finset.mem_univ, true_and, hLu, hRv]
  exact forall_and

lemma accepted_pair_common {n k : ℕ} (G : SimpleGraph (Fin n))
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (L R : Fin k → (Fin n → Bool) → Bool)
    (hLpure : ∀ i x, L i x = L i (maskTrue (fun w => !(s w)) x))
    (hRpure : ∀ i x, R i x = R i (maskTrue s x))
    (u v : Fin n) (huv : G.Adj u v)
    (hf : family L R (pairInput u v) = true) :
    (u ∈ commonSupport L ∧ v ∈ commonSupport R) ∨
      (v ∈ commonSupport L ∧ u ∈ commonSupport R) := by
  cases hu : s u with
  | false =>
    have hv : s v = true := by
      cases hv : s v with
      | false => exact ((hbip u v huv) (hu.trans hv.symm)).elim
      | true => rfl
    exact Or.inl ((family_pair_left_right s L R hLpure hRpure u v hu hv).mp hf)
  | true =>
    have hv : s v = false := by
      cases hv : s v with
      | false => rfl
      | true => exact ((hbip u v huv) (hu.trans hv.symm)).elim
    have hswap : pairInput u v = pairInput v u := by
      funext w
      simp [pairInput, or_comm]
    rw [hswap] at hf
    exact Or.inr ((family_pair_left_right s L R hLpure hRpure v u hv hu).mp hf)

lemma rectangle_small_side {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (I J : Finset (Fin n))
    (hIJ : ∀ u ∈ I, ∀ v ∈ J, G.Adj u v) : I.card ≤ 1 ∨ J.card ≤ 1 := by
  classical
  by_cases hI : I.card ≤ 1
  · exact Or.inl hI
  have hIpos : I.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hIpos
  obtain ⟨c, hc, hca⟩ := Finset.exists_mem_ne (by omega : 1 < I.card) a
  have hsub : J ⊆ Finset.univ.filter fun v => G.Adj a v ∧ G.Adj c v := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hIJ a ha v hv, hIJ c hc v hv⟩
  exact Or.inr ((Finset.card_le_card hsub).trans (h4 a c hca.symm))

lemma replacement_existing_side {n k : ℕ} (hk : 0 < k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : PEqualNP.TopForm.NoFourCycle G)
    (L R : Fin k → (Fin n → Bool) → Bool)
    (hLmono : ∀ i, Monotone (L i)) (hRmono : ∀ i, Monotone (R i))
    (hLpure : ∀ i x, L i x = L i (maskTrue (fun w => !(s w)) x))
    (hRpure : ∀ i x, R i x = R i (maskTrue s x))
    (hLzero : ∀ i, L i (fun _ => false) = false)
    (hRzero : ∀ i, R i (fun _ => false) = false)
    (hbelow : ∀ x, family L R x = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧ family L R (pairInput a b) = true) :
    ∃ (u : Fin n) (i : Fin k) (f : (Fin n → Bool) → Bool),
      (f = L i ∨ f = R i) ∧
      (∀ x, x u && f x = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → family L R (pairInput a b) = true →
        pairInput a b u && f (pairInput a b) = true) := by
  classical
  let i0 : Fin k := ⟨0, hk⟩
  have hLeftColor : ∀ u ∈ commonSupport L, s u = false := by
    intro u hu
    have h := singleton_color (fun w => !(s w)) (L i0) (hLpure i0) (hLzero i0) u
      ((Finset.mem_filter.mp hu).2 i0)
    simpa using h
  have hRightColor : ∀ v ∈ commonSupport R, s v = true := by
    intro v hv
    exact singleton_color s (R i0) (hRpure i0) (hRzero i0) v
      ((Finset.mem_filter.mp hv).2 i0)
  have hPair := accepted_pair_common G s hbip L R hLpure hRpure
  obtain ⟨a, b, hab, habf⟩ := haccept
  have hIJne : (commonSupport L).Nonempty ∧ (commonSupport R).Nonempty := by
    rcases hPair a b hab habf with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    · exact ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
  have hIJ : ∀ u ∈ commonSupport L, ∀ v ∈ commonSupport R, G.Adj u v := by
    intro u hu v hv
    have hf := (family_pair_left_right s L R hLpure hRpure u v
      (hLeftColor u hu) (hRightColor v hv)).2 ⟨hu, hv⟩
    obtain ⟨p, q, hpq, hp, hq⟩ := (graph_true G _).mp (hbelow _ hf)
    have hp' : p = u ∨ p = v := by simpa [pairInput] using hp
    have hq' : q = u ∨ q = v := by simpa [pairInput] using hq
    rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
    · exact (G.irrefl hpq).elim
    · exact hpq
    · exact hpq.symm
    · exact (G.irrefl hpq).elim
  rcases rectangle_small_side G h4 (commonSupport L) (commonSupport R) hIJ with hI | hJ
  · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp (le_antisymm hI (Finset.card_pos.mpr hIJne.1))
    have huL : u ∈ commonSupport L := by rw [hu]; simp
    obtain ⟨i, hi⟩ := existing_filter G s hbip L R hLmono hRmono hRpure hbelow u
      (hLeftColor u huL) (Finset.mem_filter.mp huL).2
    refine ⟨u, i, R i, Or.inr rfl, hi, ?_⟩
    intro a b hab hf
    have hR : R i (pairInput a b) = true := ((of_decide_eq_true hf) i).2
    rcases hPair a b hab hf with ⟨ha, _⟩ | ⟨hb, _⟩
    · have hau : a = u := by simpa [hu] using ha
      subst a
      simp [pairInput, hR]
    · have hbu : b = u := by simpa [hu] using hb
      subst b
      simp [pairInput, hR]
  · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (le_antisymm hJ (Finset.card_pos.mpr hIJne.2))
    have hvR : v ∈ commonSupport R := by rw [hv]; simp
    have hbip' : ∀ u v, G.Adj u v → (!(s u)) ≠ (!(s v)) := by
      intro u v huv hnot
      exact hbip u v huv (by simpa only [Bool.not_not] using congrArg Bool.not hnot)
    have hLpure' : ∀ i x, L i x = L i (maskTrue (fun w => !(s w)) x) := hLpure
    have hbelow' : ∀ x, family R L x = true → graphFun G ∅ x = true := by
      intro x hx
      apply hbelow x
      simpa only [family, decide_eq_true_eq, and_comm] using hx
    obtain ⟨i, hi⟩ := existing_filter G (fun w => !(s w)) hbip' R L hRmono hLmono hLpure' hbelow' v
      (by simp [hRightColor v hvR]) (Finset.mem_filter.mp hvR).2
    refine ⟨v, i, L i, Or.inl rfl, hi, ?_⟩
    intro a b hab hf
    have hL : L i (pairInput a b) = true := ((of_decide_eq_true hf) i).1
    rcases hPair a b hab hf with ⟨_, hb⟩ | ⟨_, ha⟩
    · have hbv : b = v := by simpa [hv] using hb
      subst b
      simp [pairInput, hL]
    · have hav : a = v := by simpa [hv] using ha
      subst a
      simp [pairInput, hL]

end PEqualNP.Outside.L_meta_3566.PureFunctionFamily


namespace PEqualNP.Outside.L_meta_3566.WireFacts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

lemma step_zero (g : Gate) (hao : g.op = .and ∨ g.op = .or)
    (h2 : g.inputs.length = 2) (a : List Bool)
    (ha : ∀ w, a.getD w false = false) :
    ∀ w, (Splice.stepWire a g).getD w false = false := by
  obtain ⟨i, j, hij⟩ := List.length_eq_two.mp h2
  have hval : g.op.eval (g.inputs.map fun w => a.getD w false) = false := by
    rw [hij]
    simp only [List.map_cons, List.map_nil, ha i, ha j]
    rcases hao with hop | hop <;> simp [hop, GateOp.eval]
  intro w
  rcases lt_trichotomy w a.length with hw | hw | hw
  · rw [Splice.stepWire_getD_lt a g w hw]
    exact ha w
  · rw [hw, Splice.stepWire_getD_len]
    exact hval
  · apply Splice.getD_ge_length
    simp only [Splice.stepWire, List.length_append, List.length_singleton]
    omega

lemma foldl_zero (gs : List Gate)
    (hao : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (h2 : ∀ g ∈ gs, g.inputs.length = 2)
    (a : List Bool) (ha : ∀ w, a.getD w false = false) :
    ∀ w, (gs.foldl Splice.stepWire a).getD w false = false := by
  induction gs generalizing a with
  | nil => exact ha
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih (fun g hg => hao g (by simp [hg]))
      (fun g hg => h2 g (by simp [hg])) (Splice.stepWire a g)
      (step_zero g (hao g (by simp)) (h2 g (by simp)) a ha)

lemma wire_zero {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) :
    (C.wires (List.ofFn (fun _ : Fin n => false))).getD w false = false := by
  apply foldl_zero C.gates hAO.1 hAO.2.2
  intro i
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  · exact Splice.getD_ge_length _ _ (by simpa using Nat.le_of_not_gt hi)

lemma wire_monotone {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => (C.wires (List.ofFn x)).getD w false) := by
  change Monotone (circuitFun n {C with output := w})
  exact Splice.circuitFun_monotone n {C with output := w} hAO.1

end PEqualNP.Outside.L_meta_3566.WireFacts

namespace PEqualNP.Outside.L_meta_3566.PureFunctionCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def wireFun {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma replace_pure_family {n k : ℕ} (hk : 0 < k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (j : ℕ) (hj : j < C.gates.length) (wL wR : Fin k → ℕ)
    (hbackL : ∀ i, wL i < n + j) (hbackR : ∀ i, wR i < n + j)
    (hLpure : ∀ i x, wireFun C (wL i) x =
      wireFun C (wL i) (PureFunctionFamily.maskTrue (fun v => !(s v)) x))
    (hRpure : ∀ i x, wireFun C (wR i) x =
      wireFun C (wR i) (PureFunctionFamily.maskTrue s x))
    (hjval : ∀ x : Fin n → Bool, wireFun C (n + j) x =
      PureFunctionFamily.family (fun i => wireFun C (wL i)) (fun i => wireFun C (wR i)) x)
    (hbelow : ∀ x, wireFun C (n + j) x = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧ wireFun C (n + j) (pairInput a b) = true) :
    ∃ (u : Fin n) (i : Fin k) (w : ℕ),
      (w = wL i ∨ w = wR i) ∧ w < n + j ∧
      IsAO2 n (GateReplace.replace C j ⟨GateOp.and, [u.val, w]⟩) ∧
      circuitFun n (GateReplace.replace C j ⟨GateOp.and, [u.val, w]⟩) = graphFun G ∅ ∧
      (GateReplace.replace C j ⟨GateOp.and, [u.val, w]⟩).size = C.size := by
  have hbelow' : ∀ x, PureFunctionFamily.family
      (fun i => wireFun C (wL i)) (fun i => wireFun C (wR i)) x = true →
        graphFun G ∅ x = true := by
    intro x hx
    exact hbelow x (by simpa only [hjval] using hx)
  have haccept' : ∃ a b, G.Adj a b ∧ PureFunctionFamily.family
      (fun i => wireFun C (wL i)) (fun i => wireFun C (wR i)) (pairInput a b) = true := by
    simpa only [hjval] using haccept
  obtain ⟨u, i, f, hside, hclean, hkeep⟩ :=
    PureFunctionFamily.replacement_existing_side hk G s hbip h4
      (fun i => wireFun C (wL i)) (fun i => wireFun C (wR i))
      (fun i => WireFacts.wire_monotone C hAO (wL i))
      (fun i => WireFacts.wire_monotone C hAO (wR i)) hLpure hRpure
      (fun i => WireFacts.wire_zero C hAO (wL i))
      (fun i => WireFacts.wire_zero C hAO (wR i)) hbelow' haccept'
  have hw : ∃ w : ℕ, (w = wL i ∨ w = wR i) ∧ w < n + j ∧
      wireFun (n := n) C w = f := by
    rcases hside with rfl | rfl
    · exact ⟨wL i, Or.inl rfl, hbackL i, rfl⟩
    · exact ⟨wR i, Or.inr rfl, hbackR i, rfl⟩
  obtain ⟨w, hwside, hwback, hwval⟩ := hw
  refine ⟨u, i, w, hwside, hwback, ?_⟩
  have hgate : ∀ x : Fin n → Bool,
      GateOp.and.eval ([u.val, w].map fun t => (C.wires (List.ofFn x)).getD t false) =
        (x u && f x) := by
    intro x
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    rw [RectangleCircuit.input_val]
    change (x u && wireFun C w x) = (x u && f x)
    rw [hwval]
  apply GateReplace.correct_of_edge_cover G C hAO hfun j hj ⟨GateOp.and, [u.val, w]⟩
    (Or.inl rfl) rfl
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl
    · omega
    · exact hwback
  · intro a b hab ht
    change wireFun C (n + j) (pairInput a b) = true at ht
    rw [hjval] at ht
    change GateOp.and.eval ([u.val, w].map fun t =>
      (C.wires (List.ofFn (pairInput a b))).getD t false) = true
    rw [hgate]
    simpa using hkeep a b hab ht
  · intro x ht
    apply hclean x
    change GateOp.and.eval ([u.val, w].map fun t =>
      (C.wires (List.ofFn x)).getD t false) = true at ht
    rw [hgate] at ht
    simpa using ht

end PEqualNP.Outside.L_meta_3566.PureFunctionCircuit

namespace PEqualNP.Outside.L_meta_3566.OneMixedFrontier

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.PureFunctionFamily

lemma augment_left_true {n k : ℕ} (hk : 0 < k)
    (L R : Fin k → (Fin n → Bool) → Bool) (U : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) :
    family (Fin.cases U L) (Fin.cases (R ⟨0, hk⟩) R) x = true ↔
      family L R x = true ∧ U x = true := by
  constructor
  · intro h
    have hh := of_decide_eq_true h
    exact ⟨decide_eq_true (fun i => hh i.succ), (hh 0).1⟩
  · rintro ⟨h, hu⟩
    have hh := of_decide_eq_true h
    apply decide_eq_true
    exact Fin.cases ⟨hu, (hh ⟨0, hk⟩).2⟩ hh

lemma augment_right_true {n k : ℕ} (hk : 0 < k)
    (L R : Fin k → (Fin n → Bool) → Bool) (V : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) :
    family (Fin.cases (L ⟨0, hk⟩) L) (Fin.cases V R) x = true ↔
      family L R x = true ∧ V x = true := by
  constructor
  · intro h
    have hh := of_decide_eq_true h
    exact ⟨decide_eq_true (fun i => hh i.succ), (hh 0).2⟩
  · rintro ⟨h, hv⟩
    have hh := of_decide_eq_true h
    apply decide_eq_true
    exact Fin.cases ⟨(hh ⟨0, hk⟩).1, hv⟩ hh

lemma select_extra_left {n k : ℕ} (hk : 0 < k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (L R : Fin k → (Fin n → Bool) → Bool) (U : (Fin n → Bool) → Bool)
    (hLmono : ∀ i, Monotone (L i)) (hRmono : ∀ i, Monotone (R i)) (hUmono : Monotone U)
    (hLpure : ∀ i x, L i x = L i (maskTrue (fun w => !(s w)) x))
    (hRpure : ∀ i x, R i x = R i (maskTrue s x))
    (hUpure : ∀ x, U x = U (maskTrue (fun w => !(s w)) x))
    (hLzero : ∀ i, L i (fun _ => false) = false)
    (hRzero : ∀ i, R i (fun _ => false) = false) (hUzero : U (fun _ => false) = false)
    (hbelow : ∀ x, family L R x = true → U x = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧ family L R (pairInput a b) = true ∧ U (pairInput a b) = true) :
    ∃ (u : Fin n) (f : (Fin n → Bool) → Bool),
      (f = U ∨ ∃ i, f = L i ∨ f = R i) ∧
      (∀ x, x u && f x = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → family L R (pairInput a b) = true → U (pairInput a b) = true →
        pairInput a b u && f (pairInput a b) = true) := by
  let i0 : Fin k := ⟨0, hk⟩
  let L' : Fin (k + 1) → (Fin n → Bool) → Bool := Fin.cases U L
  let R' : Fin (k + 1) → (Fin n → Bool) → Bool := Fin.cases (R i0) R
  have hbelow' : ∀ x, family L' R' x = true → graphFun G ∅ x = true := by
    intro x hx
    obtain ⟨hh, hu⟩ := (augment_left_true hk L R U x).mp hx
    exact hbelow x hh hu
  have haccept' : ∃ a b, G.Adj a b ∧ family L' R' (pairInput a b) = true := by
    obtain ⟨a, b, hab, hh, hu⟩ := haccept
    exact ⟨a, b, hab, (augment_left_true hk L R U _).2 ⟨hh, hu⟩⟩
  obtain ⟨u, j, f, hf, hfbelow, hfretain⟩ := replacement_existing_side (Nat.succ_pos k)
    G s hbip h4 L' R'
    (Fin.cases hUmono hLmono) (Fin.cases (hRmono i0) hRmono)
    (Fin.cases hUpure hLpure) (Fin.cases (hRpure i0) hRpure)
    (Fin.cases hUzero hLzero) (Fin.cases (hRzero i0) hRzero) hbelow' haccept'
  refine ⟨u, f, ?_, hfbelow, ?_⟩
  · cases j using Fin.cases with
    | zero =>
      change f = U ∨ f = R i0 at hf
      exact hf.elim Or.inl (fun h => Or.inr ⟨i0, Or.inr h⟩)
    | succ i =>
      change f = L i ∨ f = R i at hf
      exact Or.inr ⟨i, hf⟩
  · intro a b hab hh hu
    exact hfretain a b hab ((augment_left_true hk L R U _).2 ⟨hh, hu⟩)

lemma select_extra_right {n k : ℕ} (hk : 0 < k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (L R : Fin k → (Fin n → Bool) → Bool) (V : (Fin n → Bool) → Bool)
    (hLmono : ∀ i, Monotone (L i)) (hRmono : ∀ i, Monotone (R i)) (hVmono : Monotone V)
    (hLpure : ∀ i x, L i x = L i (maskTrue (fun w => !(s w)) x))
    (hRpure : ∀ i x, R i x = R i (maskTrue s x))
    (hVpure : ∀ x, V x = V (maskTrue s x))
    (hLzero : ∀ i, L i (fun _ => false) = false)
    (hRzero : ∀ i, R i (fun _ => false) = false) (hVzero : V (fun _ => false) = false)
    (hbelow : ∀ x, family L R x = true → V x = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧ family L R (pairInput a b) = true ∧ V (pairInput a b) = true) :
    ∃ (u : Fin n) (f : (Fin n → Bool) → Bool),
      (f = V ∨ ∃ i, f = L i ∨ f = R i) ∧
      (∀ x, x u && f x = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → family L R (pairInput a b) = true → V (pairInput a b) = true →
        pairInput a b u && f (pairInput a b) = true) := by
  let i0 : Fin k := ⟨0, hk⟩
  let L' : Fin (k + 1) → (Fin n → Bool) → Bool := Fin.cases (L i0) L
  let R' : Fin (k + 1) → (Fin n → Bool) → Bool := Fin.cases V R
  have hbelow' : ∀ x, family L' R' x = true → graphFun G ∅ x = true := by
    intro x hx
    obtain ⟨hh, hv⟩ := (augment_right_true hk L R V x).mp hx
    exact hbelow x hh hv
  have haccept' : ∃ a b, G.Adj a b ∧ family L' R' (pairInput a b) = true := by
    obtain ⟨a, b, hab, hh, hv⟩ := haccept
    exact ⟨a, b, hab, (augment_right_true hk L R V _).2 ⟨hh, hv⟩⟩
  obtain ⟨u, j, f, hf, hfbelow, hfretain⟩ := replacement_existing_side (Nat.succ_pos k)
    G s hbip h4 L' R'
    (Fin.cases (hLmono i0) hLmono) (Fin.cases hVmono hRmono)
    (Fin.cases (hLpure i0) hLpure) (Fin.cases hVpure hRpure)
    (Fin.cases (hLzero i0) hLzero) (Fin.cases hVzero hRzero) hbelow' haccept'
  refine ⟨u, f, ?_, hfbelow, ?_⟩
  · cases j using Fin.cases with
    | zero =>
      change f = L i0 ∨ f = V at hf
      exact hf.elim (fun h => Or.inr ⟨i0, Or.inl h⟩) Or.inl
    | succ i =>
      change f = L i ∨ f = R i at hf
      exact Or.inr ⟨i, hf⟩
  · intro a b hab hh hv
    exact hfretain a b hab ((augment_right_true hk L R V _).2 ⟨hh, hv⟩)

lemma select_two_stars {n k : ℕ} (hk : 0 < k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (L R : Fin k → (Fin n → Bool) → Bool) (U V : (Fin n → Bool) → Bool)
    (hLmono : ∀ i, Monotone (L i)) (hRmono : ∀ i, Monotone (R i))
    (hUmono : Monotone U) (hVmono : Monotone V)
    (hLpure : ∀ i x, L i x = L i (maskTrue (fun w => !(s w)) x))
    (hRpure : ∀ i x, R i x = R i (maskTrue s x))
    (hUpure : ∀ x, U x = U (maskTrue (fun w => !(s w)) x))
    (hVpure : ∀ x, V x = V (maskTrue s x))
    (hLzero : ∀ i, L i (fun _ => false) = false)
    (hRzero : ∀ i, R i (fun _ => false) = false)
    (hUzero : U (fun _ => false) = false) (hVzero : V (fun _ => false) = false)
    (hbelow : ∀ x, family L R x && (U x || V x) = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧
      family L R (pairInput a b) && (U (pairInput a b) || V (pairInput a b)) = true) :
    ∃ (u v : Fin n) (f g : (Fin n → Bool) → Bool),
      (f = U ∨ f = V ∨ ∃ i, f = L i ∨ f = R i) ∧
      (g = U ∨ g = V ∨ ∃ i, g = L i ∨ g = R i) ∧
      (∀ x, ((x u && f x) || (x v && g x)) = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → family L R (pairInput a b) &&
        (U (pairInput a b) || V (pairInput a b)) = true →
        ((pairInput a b u && f (pairInput a b)) ||
          (pairInput a b v && g (pairInput a b))) = true) := by
  classical
  have hbelowU : ∀ x, family L R x = true → U x = true → graphFun G ∅ x = true := by
    intro x hh hu
    exact hbelow x (by simp [hh, hu])
  have hbelowV : ∀ x, family L R x = true → V x = true → graphFun G ∅ x = true := by
    intro x hh hv
    exact hbelow x (by simp [hh, hv])
  have hmemberU : ∀ f : (Fin n → Bool) → Bool,
      (f = U ∨ ∃ i, f = L i ∨ f = R i) → (f = U ∨ f = V ∨ ∃ i, f = L i ∨ f = R i) := by
    intro f hf
    exact hf.elim Or.inl (fun h => Or.inr (Or.inr h))
  have hmemberV : ∀ f : (Fin n → Bool) → Bool,
      (f = V ∨ ∃ i, f = L i ∨ f = R i) → (f = U ∨ f = V ∨ ∃ i, f = L i ∨ f = R i) := by
    intro f hf
    exact Or.inr hf
  by_cases hU : ∃ a b, G.Adj a b ∧ family L R (pairInput a b) = true ∧ U (pairInput a b) = true
  · obtain ⟨u, f, hf, hfb, hfr⟩ := select_extra_left hk G s hbip h4 L R U
      hLmono hRmono hUmono hLpure hRpure hUpure hLzero hRzero hUzero hbelowU hU
    by_cases hV : ∃ a b, G.Adj a b ∧ family L R (pairInput a b) = true ∧ V (pairInput a b) = true
    · obtain ⟨v, g, hg, hgb, hgr⟩ := select_extra_right hk G s hbip h4 L R V
        hLmono hRmono hVmono hLpure hRpure hVpure hLzero hRzero hVzero hbelowV hV
      refine ⟨u, v, f, g, hmemberU f hf, hmemberV g hg, ?_, ?_⟩
      · intro x hx
        have hx' : (x u && f x) = true ∨ (x v && g x) = true := by simpa using hx
        exact hx'.elim (hfb x) (hgb x)
      · intro a b hab hx
        have hx' : family L R (pairInput a b) = true ∧
            (U (pairInput a b) = true ∨ V (pairInput a b) = true) := by simpa using hx
        rcases hx'.2 with hu | hv
        · simp only [Bool.or_eq_true, Bool.and_eq_true]
          left
          simpa using hfr a b hab hx'.1 hu
        · simp only [Bool.or_eq_true, Bool.and_eq_true]
          right
          simpa using hgr a b hab hx'.1 hv
    · refine ⟨u, u, f, f, hmemberU f hf, hmemberU f hf, ?_, ?_⟩
      · intro x hx
        exact hfb x (by simpa using hx)
      · intro a b hab hx
        have hx' : family L R (pairInput a b) = true ∧
            (U (pairInput a b) = true ∨ V (pairInput a b) = true) := by simpa using hx
        rcases hx'.2 with hu | hv
        · simpa using hfr a b hab hx'.1 hu
        · exact (hV ⟨a, b, hab, hx'.1, hv⟩).elim
  · have hV : ∃ a b, G.Adj a b ∧ family L R (pairInput a b) = true ∧ V (pairInput a b) = true := by
      obtain ⟨a, b, hab, hx⟩ := haccept
      have hx' : family L R (pairInput a b) = true ∧
          (U (pairInput a b) = true ∨ V (pairInput a b) = true) := by simpa using hx
      rcases hx'.2 with hu | hv
      · exact (hU ⟨a, b, hab, hx'.1, hu⟩).elim
      · exact ⟨a, b, hab, hx'.1, hv⟩
    obtain ⟨v, g, hg, hgb, hgr⟩ := select_extra_right hk G s hbip h4 L R V
      hLmono hRmono hVmono hLpure hRpure hVpure hLzero hRzero hVzero hbelowV hV
    refine ⟨v, v, g, g, hmemberV g hg, hmemberV g hg, ?_, ?_⟩
    · intro x hx
      exact hgb x (by simpa using hx)
    · intro a b hab hx
      have hx' : family L R (pairInput a b) = true ∧
          (U (pairInput a b) = true ∨ V (pairInput a b) = true) := by simpa using hx
      rcases hx'.2 with hu | hv
      · exact (hU ⟨a, b, hab, hx'.1, hu⟩).elim
      · simpa using hgr a b hab hx'.1 hv

end PEqualNP.Outside.L_meta_3566.OneMixedFrontier


namespace PEqualNP.Outside.L_meta_3566.AndChild

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma not_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C)
    (j i : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = .and) (hi : i ∈ (gateAt C j).inputs) :
    ¬ (∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD i false = true → graphFun G ∅ x = true) := by
  intro hbelow
  have hib : i < n + j := hLeast.1.2.1 j hj i hi
  rcases least_boundary_separation G C hLeast j i hj hib with
    ⟨u, v, _, hgate, hchild⟩ | ⟨S, hS, _, hchild⟩
  · have hchild' :=
      (((MixedColor.val_and (n := n) (C := C) (x := List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))
        (by simp) hj hop).mp hgate) i hi).2
    change (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD i false = true at hchild'
    rw [hchild] at hchild'
    cases hchild'
  · have hf := hbelow (supportInput S) hchild
    rw [graphFun_independent_false G hS.1] at hf
    cases hf

lemma dirty_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C)
    (j i : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = .and) (hi : i ∈ (gateAt C j).inputs) :
    ∃ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD i false = true ∧ graphFun G ∅ x = false := by
  classical
  have h := not_below G C hLeast j i hj hop hi
  push Not at h
  obtain ⟨x, hx, hg⟩ := h
  exact ⟨x, hx, Bool.eq_false_iff.mpr hg⟩

end PEqualNP.Outside.L_meta_3566.AndChild


namespace PEqualNP.Outside.L_meta_3566.PrivateBlock

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership Splice

def ExceptRel (R : Bool → Bool → Prop) (bad : Finset ℕ) (a b : List Bool) : Prop :=
  ∀ i, i ∉ bad → R (a.getD i false) (b.getD i false)

lemma eval_mono_on (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    (f h : ℕ → Bool) (hfh : ∀ i ∈ g.inputs, f i ≤ h i) :
    g.op.eval (g.inputs.map f) ≤ g.op.eval (g.inputs.map h) := by
  let f' : ℕ → Bool := fun i => if i ∈ g.inputs then f i else false
  let h' : ℕ → Bool := fun i => if i ∈ g.inputs then h i else false
  have hle : ∀ i, f' i ≤ h' i := by
    intro i
    by_cases hi : i ∈ g.inputs
    · simpa [f', h', hi] using hfh i hi
    · simp [f', h', hi]
  have hf : g.inputs.map f' = g.inputs.map f := by
    apply List.map_congr_left
    intro i hi
    simp [f', hi]
  have hh : g.inputs.map h' = g.inputs.map h := by
    apply List.map_congr_left
    intro i hi
    simp [h', hi]
  simpa only [hf, hh] using ao_eval_mono g hg f' h' hle

lemma step_except {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b)
    (bad : Finset ℕ) (a b : List Bool) (hlen : a.length = b.length)
    (g : Gate) (hab : ExceptRel R bad a b)
    (hval : R (g.op.eval (g.inputs.map fun i => a.getD i false))
      (g.op.eval (g.inputs.map fun i => b.getD i false))) :
    ExceptRel R bad (stepWire a g) (stepWire b g) := by
  intro i hi
  by_cases hil : i < a.length
  · rw [stepWire_getD_lt _ _ _ hil, stepWire_getD_lt _ _ _ (by omega)]
    exact hab i hi
  · by_cases hie : i = a.length
    · rw [hie, stepWire_getD_len, hlen, stepWire_getD_len]
      exact hval
    · rw [getD_ge_length _ _ (by simp [stepWire]; omega),
        getD_ge_length _ _ (by simp [stepWire]; omega)]
      exact hrefl false

lemma foldl_except {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b)
    (bad : Finset ℕ) (gs : List Gate)
    (hreads : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ bad)
    (hmono : ∀ g ∈ gs, ∀ (f h : ℕ → Bool),
      (∀ i ∈ g.inputs, R (f i) (h i)) →
        R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map h)))
    (a b : List Bool) (hlen : a.length = b.length) (hab : ExceptRel R bad a b) :
    ExceptRel R bad (gs.foldl stepWire a) (gs.foldl stepWire b) := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun h hh => hreads h (by simp [hh]))
      (fun h hh => hmono h (by simp [hh]))
      (stepWire a g) (stepWire b g) (by simp [stepWire, hlen])
    apply step_except hrefl bad a b hlen g hab
    exact hmono g (by simp) _ _ (fun i hi => hab i (hreads g (by simp) i hi))

def circuit (pre block post : List Gate) (output : ℕ) : Circuit :=
  ⟨pre ++ block ++ post, output⟩

def interior (n : ℕ) (pre block : List Gate) : Finset ℕ :=
  Finset.Ico (n + pre.length) (n + pre.length + block.length - 1)

def blockValue {n : ℕ} (pre block : List Gate) (x : Fin n → Bool) : Bool :=
  (block.foldl stepWire (pre.foldl stepWire (List.ofFn x))).getD
    (n + pre.length + block.length - 1) false

lemma block_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b)
    (n : ℕ) (pre old new post : List Gate) (output : ℕ)
    (hlen : old.length = new.length) (hpos : 0 < old.length)
    (hreads : ∀ g ∈ post, ∀ i ∈ g.inputs, i ∉ interior n pre old)
    (hout : output ∉ interior n pre old)
    (hmono : ∀ g ∈ post, ∀ (f h : ℕ → Bool),
      (∀ i ∈ g.inputs, R (f i) (h i)) →
        R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map h)))
    (x : Fin n → Bool) (hval : R (blockValue pre old x) (blockValue pre new x)) :
    R (circuitFun n (circuit pre old post output) x)
      (circuitFun n (circuit pre new post output) x) := by
  let a := pre.foldl stepWire (List.ofFn x)
  have ha : a.length = n + pre.length := by
    simp [a, foldl_stepWire_length]
  have hstart : ExceptRel R (interior n pre old)
      (old.foldl stepWire a) (new.foldl stepWire a) := by
    intro i hi
    by_cases hlt : i < n + pre.length
    · rw [foldl_stepWire_getD_lt old a i (by omega),
        foldl_stepWire_getD_lt new a i (by omega)]
      exact hrefl _
    · by_cases hend : i < n + pre.length + old.length
      · have heq : i = n + pre.length + old.length - 1 := by
          simp only [interior, Finset.mem_Ico, not_and] at hi
          have h := hi (by omega)
          omega
        rw [heq]
        simpa only [blockValue, hlen] using hval
      · rw [getD_ge_length _ _ (by rw [foldl_stepWire_length, ha]; omega),
          getD_ge_length _ _ (by rw [foldl_stepWire_length, ha]; omega)]
        exact hrefl false
  have hresult := foldl_except hrefl (interior n pre old) post hreads hmono
    (old.foldl stepWire a) (new.foldl stepWire a)
    (by simp only [foldl_stepWire_length, hlen]) hstart output hout
  simpa only [circuitFun, Circuit.eval, circuit, wires_eq_foldl, List.foldl_append] using hresult

lemma correct_of_edge_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre old new post : List Gate) (output : ℕ)
    (hAO : IsAO2 n (circuit pre old post output))
    (hfun : circuitFun n (circuit pre old post output) = graphFun G ∅)
    (hnew : IsAO2 n (circuit pre new post output))
    (hlen : old.length = new.length) (hblock : 0 < old.length)
    (hreads : ∀ g ∈ post, ∀ i ∈ g.inputs, i ∉ interior n pre old)
    (hout : output ∉ interior n pre old)
    (hkeep : ∀ a b, G.Adj a b → blockValue pre old (pairInput a b) = true →
      blockValue pre new (pairInput a b) = true)
    (hclean : ∀ x : Fin n → Bool, blockValue pre new x = true → graphFun G ∅ x = true) :
    circuitFun n (circuit pre new post output) = graphFun G ∅ ∧
      (circuit pre new post output).size = (circuit pre old post output).size := by
  have hpost : ∀ g ∈ post, g.op = .and ∨ g.op = .or := by
    intro g hg
    exact hAO.1 g (by simp [circuit, hg])
  constructor
  · apply (graphFun_boundary_iff G _ (circuitFun_monotone n _ hnew.1)).2
    constructor
    · intro a b hab
      apply bool_true_of_le (block_rel (R := (· ≤ ·)) (fun _ => le_refl _) n
        pre old new post output hlen hblock hreads hout
        (fun g hg => eval_mono_on g (hpost g hg)) (pairInput a b)
        (Bool.le_iff_imp.mpr (hkeep a b hab)))
      rw [hfun]
      exact graphFun_pair_true G hab
    · intro S hS
      have hn : blockValue pre new (supportInput S) = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        have hf := hclean _ ht
        rw [graphFun_independent_false G hS.1] at hf
        cases hf
      apply bool_false_of_le (block_rel (R := fun a b => b ≤ a) (fun _ => le_refl _) n
        pre old new post output hlen hblock hreads hout
        (fun g hg f h hh => eval_mono_on g (hpost g hg) h f hh) (supportInput S)
        (by rw [hn]; exact Bool.false_le _))
      rw [hfun]
      exact graphFun_independent_false G hS.1
  · simp [circuit, Circuit.size, hlen]


lemma replace_ao {n : ℕ} (pre old new post : List Gate) (output : ℕ)
    (hAO : IsAO2 n (circuit pre old post output)) (hlen : old.length = new.length)
    (hnewop : ∀ g ∈ new, g.op = .and ∨ g.op = .or)
    (hnewlen : ∀ g ∈ new, g.inputs.length = 2)
    (hnewback : ∀ j < new.length, ∀ i ∈ (new.getD j ⟨.or, []⟩).inputs,
      i < n + pre.length + j) : IsAO2 n (circuit pre new post output) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact hAO.1 g (by simp [circuit, hg])
    · exact hnewop g hg
    · exact hAO.1 g (by simp [circuit, hg])
  · intro j hj i hi
    change i ∈ ((pre ++ new ++ post).getD j ⟨.or, []⟩).inputs at hi
    by_cases hjpre : j < pre.length
    · have hjo : j < (circuit pre old post output).gates.length := by
        simp [circuit]
        omega
      have hgo : gateAt (circuit pre old post output) j = pre.getD j ⟨.or, []⟩ := by
        simp only [gateAt, circuit]
        rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ hjpre]
      rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ hjpre] at hi
      apply hAO.2.1 j hjo i
      simpa only [hgo] using hi
    · by_cases hjblock : j < pre.length + new.length
      · rw [List.getD_append _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by omega)] at hi
        have hb := hnewback (j - pre.length) (by omega) i hi
        omega
      · have hjo : j < (circuit pre old post output).gates.length := by
          simpa [circuit, hlen] using hj
        have hgo : gateAt (circuit pre old post output) j =
            post.getD (j - (pre.length + new.length)) ⟨.or, []⟩ := by
          simp only [gateAt, circuit]
          rw [List.getD_append_right _ _ _ _ (by simp [hlen]; omega)]
          simp only [List.length_append, hlen]
        rw [List.getD_append_right _ _ _ _ (by simp; omega)] at hi
        simp only [List.length_append] at hi
        apply hAO.2.1 j hjo i
        simpa only [hgo] using hi
  · intro g hg
    simp only [circuit, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact hAO.2.2 g (by simp [circuit, hg])
    · exact hnewlen g hg
    · exact hAO.2.2 g (by simp [circuit, hg])

def twoStars (m u v p q : ℕ) : List Gate :=
  [⟨.and, [u, p]⟩, ⟨.and, [v, q]⟩, ⟨.or, [m, m + 1]⟩]

lemma twoStars_length (m u v p q : ℕ) : (twoStars m u v p q).length = 3 := rfl

lemma twoStars_ao {n : ℕ} (pre old post : List Gate) (output : ℕ)
    (hAO : IsAO2 n (circuit pre old post output)) (hlen : old.length = 3)
    (u v p q : ℕ) (hu : u < n + pre.length) (hv : v < n + pre.length)
    (hp : p < n + pre.length) (hq : q < n + pre.length) :
    IsAO2 n (circuit pre (twoStars (n + pre.length) u v p q) post output) := by
  apply replace_ao pre old _ post output hAO (by simpa only [twoStars_length] using hlen)
  · intro g hg
    simp only [twoStars, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  · intro g hg
    simp only [twoStars, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> rfl
  · intro j hj i hi
    have hj' : j < 3 := hj
    interval_cases j <;> simp [twoStars] at hi <;>
      rcases hi with rfl | rfl <;> omega

lemma twoStars_value (a : List Bool) (u v p q : ℕ)
    (hu : u < a.length) (hv : v < a.length) (hp : p < a.length) (hq : q < a.length) :
    ((twoStars a.length u v p q).foldl stepWire a).getD (a.length + 2) false =
      ((a.getD u false && a.getD p false) || (a.getD v false && a.getD q false)) := by
  let g0 : Gate := ⟨.and, [u, p]⟩
  let g1 : Gate := ⟨.and, [v, q]⟩
  let g2 : Gate := ⟨.or, [a.length, a.length + 1]⟩
  have h0len : (stepWire a g0).length = a.length + 1 := by simp [stepWire]
  have h1len : (stepWire (stepWire a g0) g1).length = a.length + 2 := by simp [stepWire]
  have h0 : (stepWire a g0).getD a.length false = (a.getD u false && a.getD p false) := by
    rw [stepWire_getD_len]
    simp [g0, GateOp.eval]
  have h1 : (stepWire (stepWire a g0) g1).getD (a.length + 1) false =
      (a.getD v false && a.getD q false) := by
    rw [← h0len, stepWire_getD_len]
    simp only [g1, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true]
    rw [stepWire_getD_lt a g0 v hv, stepWire_getD_lt a g0 q hq]
  change (stepWire (stepWire (stepWire a g0) g1) g2).getD (a.length + 2) false = _
  rw [← h1len, stepWire_getD_len]
  simp only [g2, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
    List.any_nil, id_eq, Bool.or_false]
  rw [stepWire_getD_lt (stepWire a g0) g1 a.length (by omega), h0, h1]


def prefixFun {n : ℕ} (pre : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (pre.foldl stepWire (List.ofFn x)).getD w false

def starFun {n : ℕ} (pre : List Gate) (u v : Fin n) (p q : ℕ) (x : Fin n → Bool) : Bool :=
  (x u && prefixFun pre p x) || (x v && prefixFun pre q x)

lemma twoStars_blockValue {n : ℕ} (pre : List Gate) (u v : Fin n) (p q : ℕ)
    (hp : p < n + pre.length) (hq : q < n + pre.length) (x : Fin n → Bool) :
    blockValue pre (twoStars (n + pre.length) u.val v.val p q) x =
      starFun pre u v p q x := by
  let a := pre.foldl stepWire (List.ofFn x)
  have ha : a.length = n + pre.length := by simp [a, foldl_stepWire_length]
  have hi : ∀ t : Fin n, a.getD t.val false = x t := by
    intro t
    rw [foldl_stepWire_getD_lt pre (List.ofFn x) t.val (by simpa using t.isLt)]
    simp
  have hv := twoStars_value a u.val v.val p q (by omega) (by omega) (by omega) (by omega)
  rw [hi u, hi v] at hv
  simp only [blockValue, twoStars_length]
  have heq : n + pre.length + 3 - 1 = a.length + 2 := by omega
  rw [heq, ← ha]
  exact hv

lemma replace_by_two_stars {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre old post : List Gate) (output : ℕ)
    (hAO : IsAO2 n (circuit pre old post output))
    (hfun : circuitFun n (circuit pre old post output) = graphFun G ∅)
    (hlen : old.length = 3)
    (hreads : ∀ g ∈ post, ∀ i ∈ g.inputs, i ∉ interior n pre old)
    (hout : output ∉ interior n pre old)
    (u v : Fin n) (p q : ℕ) (hp : p < n + pre.length) (hq : q < n + pre.length)
    (hkeep : ∀ a b, G.Adj a b → blockValue pre old (pairInput a b) = true →
      starFun pre u v p q (pairInput a b) = true)
    (hclean : ∀ x : Fin n → Bool, starFun pre u v p q x = true → graphFun G ∅ x = true) :
    IsAO2 n (circuit pre (twoStars (n + pre.length) u.val v.val p q) post output) ∧
      circuitFun n (circuit pre (twoStars (n + pre.length) u.val v.val p q) post output) = graphFun G ∅ ∧
      (circuit pre (twoStars (n + pre.length) u.val v.val p q) post output).size =
        (circuit pre old post output).size := by
  let new := twoStars (n + pre.length) u.val v.val p q
  have hnew := twoStars_ao pre old post output hAO hlen u.val v.val p q (by omega) (by omega) hp hq
  refine ⟨hnew, ?_⟩
  apply correct_of_edge_cover G pre old new post output hAO hfun hnew
    (by simpa [new, twoStars_length] using hlen) (by omega) hreads hout
  · intro a b hab hv
    simpa only [new, twoStars_blockValue pre u v p q hp hq] using hkeep a b hab (by simpa using hv)
  · intro x hx
    apply hclean x
    simpa only [new, twoStars_blockValue pre u v p q hp hq] using hx

lemma replace_one_mixed {n k : ℕ} (hk : 0 < k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre old post : List Gate) (output : ℕ)
    (hAO : IsAO2 n (circuit pre old post output))
    (hfun : circuitFun n (circuit pre old post output) = graphFun G ∅)
    (hlen : old.length = 3)
    (hreads : ∀ g ∈ post, ∀ i ∈ g.inputs, i ∉ interior n pre old)
    (hout : output ∉ interior n pre old)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (L R : Fin k → (Fin n → Bool) → Bool) (U V : (Fin n → Bool) → Bool)
    (hLmono : ∀ i, Monotone (L i)) (hRmono : ∀ i, Monotone (R i))
    (hUmono : Monotone U) (hVmono : Monotone V)
    (hLpure : ∀ i x, L i x = L i (PureFunctionFamily.maskTrue (fun w => !(s w)) x))
    (hRpure : ∀ i x, R i x = R i (PureFunctionFamily.maskTrue s x))
    (hUpure : ∀ x, U x = U (PureFunctionFamily.maskTrue (fun w => !(s w)) x))
    (hVpure : ∀ x, V x = V (PureFunctionFamily.maskTrue s x))
    (hLzero : ∀ i, L i (fun _ => false) = false)
    (hRzero : ∀ i, R i (fun _ => false) = false)
    (hUzero : U (fun _ => false) = false) (hVzero : V (fun _ => false) = false)
    (hwire : ∀ f : (Fin n → Bool) → Bool,
      (f = U ∨ f = V ∨ ∃ i, f = L i ∨ f = R i) →
        ∃ w < n + pre.length, prefixFun pre w = f)
    (hold : ∀ x : Fin n → Bool, blockValue pre old x =
      (PureFunctionFamily.family L R x && (U x || V x)))
    (hbelow : ∀ x : Fin n → Bool, blockValue pre old x = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧ blockValue pre old (pairInput a b) = true) :
    ∃ (u v : Fin n) (p q : ℕ), p < n + pre.length ∧ q < n + pre.length ∧
      (prefixFun pre p = U ∨ prefixFun pre p = V ∨ ∃ i, prefixFun pre p = L i ∨ prefixFun pre p = R i) ∧
      (prefixFun pre q = U ∨ prefixFun pre q = V ∨ ∃ i, prefixFun pre q = L i ∨ prefixFun pre q = R i) ∧
      (∀ x : Fin n → Bool, starFun pre u v p q x = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → blockValue pre old (pairInput a b) = true →
        starFun pre u v p q (pairInput a b) = true) ∧
      IsAO2 n (circuit pre (twoStars (n + pre.length) u.val v.val p q) post output) ∧
      circuitFun n (circuit pre (twoStars (n + pre.length) u.val v.val p q) post output) = graphFun G ∅ ∧
      (circuit pre (twoStars (n + pre.length) u.val v.val p q) post output).size =
        (circuit pre old post output).size := by
  have hbelow' : ∀ x, PureFunctionFamily.family L R x && (U x || V x) = true →
      graphFun G ∅ x = true := by
    intro x hx
    exact hbelow x (by simpa [hold] using hx)
  have haccept' : ∃ a b, G.Adj a b ∧ PureFunctionFamily.family L R (pairInput a b) &&
      (U (pairInput a b) || V (pairInput a b)) = true := by
    simpa [hold] using haccept
  obtain ⟨u, v, f, g, hf, hg, hclean, hkeep⟩ :=
    OneMixedFrontier.select_two_stars hk G s hbip h4 L R U V hLmono hRmono hUmono hVmono
      hLpure hRpure hUpure hVpure hLzero hRzero hUzero hVzero hbelow' haccept'
  obtain ⟨p, hp, hpf⟩ := hwire f hf
  obtain ⟨q, hq, hqg⟩ := hwire g hg
  have hclean' : ∀ x : Fin n → Bool, starFun pre u v p q x = true → graphFun G ∅ x = true := by
    intro x hx
    apply hclean x
    simpa only [starFun, hpf, hqg] using hx
  have hkeep' : ∀ a b, G.Adj a b → blockValue pre old (pairInput a b) = true →
      starFun pre u v p q (pairInput a b) = true := by
    intro a b hab hv
    rw [hold] at hv
    simpa only [starFun, hpf, hqg] using hkeep a b hab (by simpa using hv)
  refine ⟨u, v, p, q, hp, hq, ?_, ?_, hclean', hkeep', ?_⟩
  · simpa only [hpf] using hf
  · simpa only [hqg] using hg
  · exact replace_by_two_stars G pre old post output hAO hfun hlen hreads hout u v p q hp hq hkeep' hclean'

end PEqualNP.Outside.L_meta_3566.PrivateBlock


namespace PEqualNP.Outside.L_meta_3566.OrCharge

lemma frontier_bound {α : Type*} [DecidableEq α]
    (F : ℕ → Finset α) (Q : Finset ℕ) (good : ℕ → Prop)
    (K : ℕ)
    (hstep : ∀ w < K, good w → 1 < (F w).card →
      ∃ A : Finset ℕ, (∀ v ∈ A, v < w ∧ good v) ∧
        F w ⊆ A.biUnion F ∧ A.card ≤ 1 + (if w ∈ Q then 1 else 0))
    (W : Finset ℕ) (hW : ∀ w ∈ W, w < K ∧ good w) :
    (W.biUnion F).card ≤ ((Finset.range K).filter (· ∈ Q)).card + W.card := by
  classical
  induction K generalizing W with
  | zero =>
      have hw : W = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact Nat.not_lt_zero w (hW w hw).1
      simp [hw]
  | succ K ih =>
      have hstep' : ∀ w < K, good w → 1 < (F w).card →
          ∃ A : Finset ℕ, (∀ v ∈ A, v < w ∧ good v) ∧
            F w ⊆ A.biUnion F ∧ A.card ≤ 1 + (if w ∈ Q then 1 else 0) := by
        intro w hw
        exact hstep w (by omega)
      have hcount : ((Finset.range (K + 1)).filter (· ∈ Q)).card =
          ((Finset.range K).filter (· ∈ Q)).card + (if K ∈ Q then 1 else 0) := by
        rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs with hK
        · rw [Finset.card_insert_of_notMem]
          simp
        · simp
      by_cases hKW : K ∈ W
      · have hEr : ∀ w ∈ W.erase K, w < K ∧ good w := by
          intro w hw
          obtain ⟨hwne, hwW⟩ := Finset.mem_erase.mp hw
          obtain ⟨hwlt, hwg⟩ := hW w hwW
          exact ⟨by omega, hwg⟩
        have hWcard : (W.erase K).card + 1 = W.card := Finset.card_erase_add_one hKW
        by_cases hsmall : (F K).card ≤ 1
        · have ih' := ih hstep' (W.erase K) hEr
          have hcover : W.biUnion F = F K ∪ (W.erase K).biUnion F := by
            have he := congrArg (fun T : Finset ℕ => T.biUnion F) (Finset.insert_erase hKW).symm
            simpa only [Finset.biUnion_insert] using he
          have hc : (W.biUnion F).card ≤ (F K).card + ((W.erase K).biUnion F).card := by
            rw [hcover]
            exact Finset.card_union_le _ _
          rw [hcount]
          split_ifs <;> omega
        · obtain ⟨A, hA, hsub, hAc⟩ := hstep K (by omega) (hW K hKW).2 (by omega)
          let W' := W.erase K ∪ A
          have hW' : ∀ w ∈ W', w < K ∧ good w := by
            intro w hw
            rcases Finset.mem_union.mp hw with hw | hw
            · exact hEr w hw
            · exact hA w hw
          have hcover : W.biUnion F ⊆ W'.biUnion F := by
            intro a ha
            obtain ⟨w, hw, ha⟩ := Finset.mem_biUnion.mp ha
            by_cases hwK : w = K
            · subst w
              obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hsub ha)
              exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
            · exact Finset.mem_biUnion.mpr ⟨w,
                Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwK, hw⟩), ha⟩
          have ih' := ih hstep' W' hW'
          have hc := Finset.card_le_card hcover
          have hWc : W'.card ≤ (W.erase K).card + A.card := Finset.card_union_le _ _
          rw [hcount]
          split_ifs at hAc ⊢ <;> omega
      · have hW' : ∀ w ∈ W, w < K ∧ good w := by
          intro w hw
          obtain ⟨hwlt, hwg⟩ := hW w hw
          have hwne : w ≠ K := by
            intro h
            subst w
            contradiction
          exact ⟨by omega, hwg⟩
        have ih' := ih hstep' W hW'
        rw [hcount]
        split_ifs <;> omega

end PEqualNP.Outside.L_meta_3566.OrCharge

namespace PEqualNP.Outside.L_meta_3566.OrCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def wire {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => wire C w (pairInput v v) = true

def complement {n : ℕ} (N : Finset (Fin n)) : Fin n → Bool := fun v => decide (v ∉ N)

noncomputable def charges {n : ℕ} (C : Circuit) (N : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.range (n + C.size)).filter fun w => n ≤ w ∧
    (gateAt C (w - n)).op = .or ∧ 1 < (support (n := n) C w).card ∧
      wire C w (complement N) = false

lemma support_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    support (n := n) C w = {⟨w, hw⟩} := by
  ext v
  change v ∈ (Finset.univ.filter fun a : Fin n => wire C w (pairInput a a) = true) ↔
    v ∈ ({⟨w, hw⟩} : Finset (Fin n))
  rw [Finset.mem_filter, Finset.mem_singleton]
  simp only [Finset.mem_univ, true_and]
  have hin := RectangleCircuit.input_val C (pairInput v v) ⟨w, hw⟩
  change (C.wires (List.ofFn (pairInput v v))).getD w false = _ at hin
  change (C.wires (List.ofFn (pairInput v v))).getD w false = true ↔ v = ⟨w, hw⟩
  rw [hin]
  simp only [pairInput, or_self, decide_eq_true_eq]
  exact eq_comm

lemma support_subset_of_false {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (N : Finset (Fin n)) (w : ℕ) (hfalse : wire C w (complement N) = false) :
    support C w ⊆ N := by
  intro v hv
  have hvtrue : wire C w (pairInput v v) = true := (Finset.mem_filter.mp hv).2
  by_contra hvN
  have hle : pairInput v v ≤ complement N := by
    intro u
    apply Bool.le_iff_imp.mpr
    intro hu
    have huv : u = v := by simpa [pairInput] using hu
    subst u
    simp [complement, hvN]
  have h := WireFacts.wire_monotone C hAO w hle
  change wire C w (pairInput v v) ≤ wire C w (complement N) at h
  rw [hvtrue, hfalse] at h
  contradiction

lemma charge_step {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (N : Finset (Fin n))
    (w : ℕ) (hw : w < n + C.size) (hfalse : wire C w (complement N) = false)
    (hlarge : 1 < (support (n := n) C w).card) :
    ∃ A : Finset ℕ,
      (∀ v ∈ A, v < w ∧ wire C v (complement N) = false) ∧
      support (n := n) C w ⊆ A.biUnion (support (n := n) C) ∧
      A.card ≤ 1 + (if w ∈ charges C N then 1 else 0) := by
  classical
  have hwn : n ≤ w := by
    by_contra hn
    have he := support_input C w (by omega : w < n)
    rw [he, Finset.card_singleton] at hlarge
    omega
  let j := w - n
  have hj : j < C.gates.length := by change w - n < C.gates.length; change w < n + C.gates.length at hw; omega
  have hwj : n + j = w := by omega
  have hgmem : gateAt C j ∈ C.gates := by
    simp only [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have hlen := hAO.2.2 _ hgmem
  have hback : ∀ v ∈ (gateAt C j).inputs, v < w := by
    intro v hv
    have h := hAO.2.1 j hj v hv
    omega
  rcases hAO.1 _ hgmem with hop | hop
  · have hev := gate_wire_eval C hAO.2.1 j hj (complement N)
    rw [hwj, hop] at hev
    change wire C w (complement N) = _ at hev
    rw [hfalse] at hev
    have hex : ∃ v ∈ (gateAt C j).inputs, wire C v (complement N) = false := by
      simpa [GateOp.eval, List.all_eq_false, List.mem_map, wire] using hev.symm
    obtain ⟨v, hv, hvfalse⟩ := hex
    refine ⟨{v}, ?_, ?_, ?_⟩
    · intro a ha
      have hav : a = v := Finset.mem_singleton.mp ha
      subst a
      exact ⟨hback v hv, hvfalse⟩
    · intro a ha
      have ha' := (Finset.mem_filter.mp ha).2
      have hle := and_gate_le_input C hAO.2.1 j hj hop v hv (pairInput a a)
      rw [hwj] at hle
      have htrue := Bool.le_iff_imp.mp hle ha'
      simpa [support, wire] using htrue
    · simp only [Finset.card_singleton]
      omega
  · have hcharge : w ∈ charges C N := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw, hwn, hop, hlarge, hfalse⟩
    refine ⟨(gateAt C j).inputs.toFinset, ?_, ?_, ?_⟩
    · intro v hv
      have hvin := List.mem_toFinset.mp hv
      refine ⟨hback v hvin, ?_⟩
      have hle := or_input_le_gate C hAO.2.1 j hj hop v hvin (complement N)
      rw [hwj] at hle
      change wire C v (complement N) ≤ wire C w (complement N) at hle
      rw [hfalse] at hle
      cases hv : wire C v (complement N) with
      | false => rfl
      | true =>
        rw [hv] at hle
        have he : false = true := Bool.le_iff_imp.mp hle rfl
        cases he
    · intro a ha
      have ha' := (Finset.mem_filter.mp ha).2
      change wire C w (pairInput a a) = true at ha'
      have hev := gate_wire_eval C hAO.2.1 j hj (pairInput a a)
      rw [hwj, hop] at hev
      change wire C w (pairInput a a) = _ at hev
      rw [hev] at ha'
      have hex : ∃ v ∈ (gateAt C j).inputs, wire C v (pairInput a a) = true := by
        simpa [GateOp.eval, List.any_eq_true, List.mem_map, wire] using ha'
      obtain ⟨v, hv, hvtrue⟩ := hex
      exact Finset.mem_biUnion.mpr ⟨v, List.mem_toFinset.mpr hv,
        Finset.mem_filter.mpr ⟨Finset.mem_univ a, hvtrue⟩⟩
    · rw [if_pos hcharge]
      exact (List.toFinset_card_le _).trans (by omega)

lemma support_card_le_charges {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (N : Finset (Fin n)) (w : ℕ) (hw : w < n + C.size)
    (hfalse : wire C w (complement N) = false) :
    (support (n := n) C w).card ≤ (charges C N).card + 1 := by
  classical
  have h := frontier_bound (support (n := n) C) (charges C N)
    (fun v => wire C v (complement N) = false) (n + C.size)
    (charge_step C hAO N) {w} (by simpa using And.intro hw hfalse)
  have hfilter : (Finset.range (n + C.size)).filter (· ∈ charges C N) = charges C N := by
    ext v
    constructor
    · exact fun hv => (Finset.mem_filter.mp hv).2
    · intro hv
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (show v ∈ (Finset.range (n + C.size)).filter _ from hv)).1, hv⟩
  simpa [hfilter] using h

end PEqualNP.Outside.L_meta_3566.OrCharge

namespace PEqualNP.Outside.L_meta_3566.OrCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

noncomputable def orGates (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter fun j => (gateAt C j).op = .or

lemma charges_subset_or_image {n : ℕ} (C : Circuit) (N : Finset (Fin n)) :
    charges C N ⊆ (orGates C).image (fun j => n + j) := by
  classical
  intro w hw
  obtain ⟨hwlt, hwn, hop, _, _⟩ := Finset.mem_filter.mp hw
  have hwlt' := Finset.mem_range.mp hwlt
  apply Finset.mem_image.mpr
  refine ⟨w - n, ?_, by omega⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hop⟩

lemma charges_disjoint {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (N M : Finset (Fin n)) (hNM : (N ∩ M).card ≤ 1) :
    Disjoint (charges C N) (charges C M) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwN hwM
  obtain ⟨_, _, _, hlarge, hfalseN⟩ := Finset.mem_filter.mp hwN
  obtain ⟨_, _, _, _, hfalseM⟩ := Finset.mem_filter.mp hwM
  have hN := support_subset_of_false C hAO N w hfalseN
  have hM := support_subset_of_false C hAO M w hfalseM
  have hsub : support (n := n) C w ⊆ N ∩ M := by
    intro v hv
    exact Finset.mem_inter.mpr ⟨hN hv, hM hv⟩
  have hc := (Finset.card_le_card hsub).trans hNM
  omega

lemma sum_charges_le_orGates {n k : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (N : Fin k → Finset (Fin n))
    (hN : ∀ i j, i ≠ j → (N i ∩ N j).card ≤ 1) :
    (∑ i, (charges C (N i)).card) ≤ (orGates C).card := by
  classical
  have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint (fun i => charges C (N i)) := by
    intro i _ j _ hij
    exact charges_disjoint C hAO (N i) (N j) (hN i j hij)
  have hsub : Finset.univ.biUnion (fun i => charges C (N i)) ⊆
      (orGates C).image (fun j => n + j) := by
    intro w hw
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
    exact charges_subset_or_image C (N i) hwi
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj,
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)] at hc
  simpa using hc

lemma singleton_or_lower_bound {n k : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (w : Fin k → ℕ) (hw : ∀ i, w i < n + C.size)
    (S N : Fin k → Finset (Fin n))
    (hN : ∀ i j, i ≠ j → (N i ∩ N j).card ≤ 1)
    (hpos : ∀ i v, v ∈ S i → wire C (w i) (pairInput v v) = true)
    (hneg : ∀ i, wire C (w i) (complement (N i)) = false) :
    (∑ i, ((S i).card - 1)) ≤ (orGates C).card := by
  have hlocal : ∀ i, (S i).card - 1 ≤ (charges C (N i)).card := by
    intro i
    have hsub : S i ⊆ support C (w i) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hpos i v hv⟩
    have hc := Finset.card_le_card hsub
    have hb := support_card_le_charges C hAO (N i) (w i) (hw i) (hneg i)
    omega
  exact (Finset.sum_le_sum (fun i _ => hlocal i)).trans (sum_charges_le_orGates C hAO N hN)

end PEqualNP.Outside.L_meta_3566.OrCharge


namespace PEqualNP.Outside.L_meta_3566.SemanticPurity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership

def mask {n : ℕ} (s : Fin n → Bool) (b : Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun v => if s v = b then x v else false

def Pure {n : ℕ} (s : Fin n → Bool) (b : Bool) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f x = f (mask s b x)

def ZeroSides {n : ℕ} (s : Fin n → Bool) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ b x, f (mask s b x) = false

def Trichotomy {n : ℕ} (s : Fin n → Bool) (f : (Fin n → Bool) → Bool) : Prop :=
  Pure s false f ∨ Pure s true f ∨ ZeroSides s f

def W (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma mask_opposite {n : ℕ} (s : Fin n → Bool) (b : Bool) (x : Fin n → Bool) :
    mask s b (mask s (!b) x) = (fun _ => false) := by
  funext v
  cases hs : s v <;> cases b <;> simp [mask, hs]

lemma pure_opposite_zero {n : ℕ} (s : Fin n → Bool) (b : Bool)
    (f : (Fin n → Bool) → Bool) (hf : Pure s b f) (hz : f (fun _ => false) = false)
    (x : Fin n → Bool) : f (mask s (!b) x) = false := by
  rw [hf (mask s (!b) x), mask_opposite, hz]

lemma graph_mask_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (b : Bool) (x : Fin n → Bool) : graphFun G ∅ (mask s b x) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_empty_true_iff G _).mp h
  have huc : s u = b := by
    by_contra hc
    simp [mask, hc] at hu
  have hvc : s v = b := by
    by_contra hc
    simp [mask, hc] at hv
  exact (hbip u v huv) (huc.trans hvc.symm)

lemma below_zero_sides {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, f x = true → graphFun G ∅ x = true) : ZeroSides s f := by
  intro b x
  apply Bool.eq_false_iff.mpr
  intro h
  have hg := hf (mask s b x) h
  rw [graph_mask_false G s hbip b x] at hg
  cases hg

lemma pure_and {n : ℕ} (s : Fin n → Bool) (b : Bool)
    (f g : (Fin n → Bool) → Bool) (hf : Pure s b f) (hg : Pure s b g) :
    Pure s b (fun x => f x && g x) := by
  intro x
  dsimp
  rw [hf x, hg x]

lemma zero_and_left {n : ℕ} (s : Fin n → Bool)
    (f g : (Fin n → Bool) → Bool) (hf : ZeroSides s f) :
    ZeroSides s (fun x => f x && g x) := by
  intro b x
  simp [hf b x]

lemma zero_and_right {n : ℕ} (s : Fin n → Bool)
    (f g : (Fin n → Bool) → Bool) (hg : ZeroSides s g) :
    ZeroSides s (fun x => f x && g x) := by
  intro b x
  simp [hg b x]

lemma cross_and_zero {n : ℕ} (s : Fin n → Bool)
    (f g : (Fin n → Bool) → Bool) (hf : Pure s false f) (hg : Pure s true g)
    (hf0 : f (fun _ => false) = false) (hg0 : g (fun _ => false) = false) :
    ZeroSides s (fun x => f x && g x) := by
  intro b x
  cases b
  · have hgz := pure_opposite_zero s true g hg hg0 x
    simpa using congrArg (fun z => f (mask s false x) && z) hgz
  · have hfz := pure_opposite_zero s false f hf hf0 x
    simpa using congrArg (fun z => z && g (mask s true x)) hfz

lemma and_trichotomy {n : ℕ} (s : Fin n → Bool)
    (f g : (Fin n → Bool) → Bool) (hf : Trichotomy s f) (hg : Trichotomy s g)
    (hf0 : f (fun _ => false) = false) (hg0 : g (fun _ => false) = false) :
    Trichotomy s (fun x => f x && g x) := by
  rcases hf with hf | hf | hf <;> rcases hg with hg | hg | hg
  · exact Or.inl (pure_and s false f g hf hg)
  · exact Or.inr (Or.inr (cross_and_zero s f g hf hg hf0 hg0))
  · exact Or.inr (Or.inr (zero_and_right s f g hg))
  · right; right
    have h := cross_and_zero s g f hg hf hg0 hf0
    simpa only [Bool.and_comm] using h
  · exact Or.inr (Or.inl (pure_and s true f g hf hg))
  · exact Or.inr (Or.inr (zero_and_right s f g hg))
  · exact Or.inr (Or.inr (zero_and_left s f g hf))
  · exact Or.inr (Or.inr (zero_and_left s f g hf))
  · exact Or.inr (Or.inr (zero_and_left s f g hf))

lemma W_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    W n C w x = x ⟨w, hw⟩ := by
  exact MixedColor.val_ofFn C x ⟨w, hw⟩

lemma W_ge {n : ℕ} (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w) (x : Fin n → Bool) :
    W n C w x = false :=
  MixedColor.val_ge (n := n) (C := C) (x := List.ofFn x) (by simp) hw

lemma W_gate {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (hab : (gateAt C j).inputs = [a, b]) (x : Fin n → Bool) :
    W n C (n + j) x = (gateAt C j).op.eval [W n C a x, W n C b x] := by
  rw [W, gate_wire_eval C hAO.2.1 j hj x, hab]
  rfl

lemma all_wires_trichotomy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (C : Circuit) (hAO : IsAO2 n C)
    (hOR : ∀ j, j < C.gates.length → (gateAt C j).op = .or →
      ¬ Pure s false (W n C (n + j)) → ¬ Pure s true (W n C (n + j)) →
      ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true) :
    ∀ w, Trichotomy s (W n C w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwi : w < n
    · have hp : Pure s (s ⟨w, hwi⟩) (W n C w) := by
        intro x
        rw [W_input C w hwi x, W_input C w hwi (mask s (s ⟨w, hwi⟩) x)]
        simp [mask]
      cases hs : s ⟨w, hwi⟩
      · exact Or.inl (hs ▸ hp)
      · exact Or.inr (Or.inl (hs ▸ hp))
    by_cases hwo : n + C.gates.length ≤ w
    · left
      intro x
      rw [W_ge C w hwo x, W_ge C w hwo (mask s false x)]
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨a, b, hab⟩ := MixedColor.binaryInputs hAO hj
    have ha : a < n + j := hAO.2.1 j hj a (by simp [hab])
    have hb : b < n + j := hAO.2.1 j hj b (by simp [hab])
    have hao := hAO.1 (gateAt C j) (MixedColor.gateAt_mem hj)
    rcases hao with hop | hop
    · have heq : W n C (n + j) = (fun x => W n C a x && W n C b x) := by
        funext x
        rw [W_gate C hAO j hj a b hab x, hop]
        simp [GateOp.eval]
      rw [heq]
      exact and_trichotomy s (W n C a) (W n C b) (ih a ha) (ih b hb)
        (WireFacts.wire_zero C hAO a) (WireFacts.wire_zero C hAO b)
    · by_cases hp : Pure s false (W n C (n + j))
      · exact Or.inl hp
      by_cases hp' : Pure s true (W n C (n + j))
      · exact Or.inr (Or.inl hp')
      exact Or.inr (Or.inr (below_zero_sides G s hbip _ (hOR j hj hop hp hp')))

lemma mask_le {n : ℕ} (s : Fin n → Bool) (b : Bool) (x : Fin n → Bool) :
    mask s b x ≤ x := by
  intro v
  by_cases hv : s v = b <;> simp [mask, hv]

lemma pure_or_zero_left {n : ℕ} (s : Fin n → Bool) (b : Bool)
    (f g : (Fin n → Bool) → Bool) (hg : Monotone g)
    (hp : Pure s b (fun x => f x || g x)) (hz : ZeroSides s f) :
    (fun x => f x || g x) = g := by
  funext x
  apply le_antisymm
  · calc
      (f x || g x) = g (mask s b x) := by simpa [hz b x] using hp x
      _ ≤ g x := hg (mask_le s b x)
  · exact Bool.le_iff_imp.mpr (by intro h; simp [h])

lemma pure_and_zero_left {n : ℕ} (s : Fin n → Bool) (b : Bool)
    (f g : (Fin n → Bool) → Bool)
    (hp : Pure s b (fun x => f x && g x)) (hz : ZeroSides s f) :
    (fun x => f x && g x) = (fun _ => false) := by
  funext x
  simpa [hz b x] using hp x

lemma wire_one {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (w : ℕ) (hw : w < n + C.gates.length) : W n C w (fun _ => true) = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwi : w < n
    · exact W_input C w hwi (fun _ => true)
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨a, b, hab⟩ := MixedColor.binaryInputs hAO hj
    have ha : a < n + j := hAO.2.1 j hj a (by simp [hab])
    have hb : b < n + j := hAO.2.1 j hj b (by simp [hab])
    rw [W_gate C hAO j hj a b hab, ih a ha (by omega), ih b hb (by omega)]
    rcases hAO.1 (gateAt C j) (MixedColor.gateAt_mem hj) with hop | hop <;>
      simp [hop, GateOp.eval]

lemma not_equal_earlier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (j i : ℕ)
    (hj : j < C.gates.length) (hi : i < n + j) :
    W n C (n + j) ≠ W n C i := by
  intro heq
  rcases least_boundary_separation G C hLeast j i hj hi with ⟨u,v,_,hu,hv⟩ | ⟨S,_,hu,hv⟩
  · have h := congrFun heq (pairInput u v)
    simp only [W] at h
    rw [hu, hv] at h
    cases h
  · have h := congrFun heq (supportInput S)
    simp only [W] at h
    rw [hu, hv] at h
    cases h

lemma pure_gate_no_zero_child {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (C : Circuit) (hLeast : IsLeastAO G C)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i ∈ (gateAt C j).inputs)
    (hp : Pure s false (W n C (n + j)) ∨ Pure s true (W n C (n + j))) :
    ¬ ZeroSides s (W n C i) := by
  intro hz
  obtain ⟨a, b, hab⟩ := MixedColor.binaryInputs hLeast.1 hj
  have ha : a < n + j := hLeast.1.2.1 j hj a (by simp [hab])
  have hb : b < n + j := hLeast.1.2.1 j hj b (by simp [hab])
  obtain ⟨other, hother, heval⟩ : ∃ other, other < n + j ∧
      ∀ x, W n C (n + j) x = (gateAt C j).op.eval [W n C i x, W n C other x] := by
    have hii : i = a ∨ i = b := by simpa [hab] using hi
    rcases hii with hia | hib
    · subst i
      exact ⟨b, hb, W_gate C hLeast.1 j hj a b hab⟩
    · subst i
      refine ⟨a, ha, ?_⟩
      intro x
      rw [W_gate C hLeast.1 j hj a b hab]
      rcases hLeast.1.1 (gateAt C j) (MixedColor.gateAt_mem hj) with hop | hop <;>
        simp [hop, GateOp.eval, Bool.and_comm, Bool.or_comm]
  obtain ⟨color, hp⟩ : ∃ color, Pure s color (W n C (n + j)) := by
    rcases hp with hp | hp
    · exact ⟨false, hp⟩
    · exact ⟨true, hp⟩
  rcases hLeast.1.1 (gateAt C j) (MixedColor.gateAt_mem hj) with hop | hop
  · have heq : W n C (n + j) = (fun x => W n C i x && W n C other x) := by
      funext x
      simpa [hop, GateOp.eval] using heval x
    have hzero := pure_and_zero_left s color (W n C i) (W n C other) (heq ▸ hp) hz
    have hone := wire_one C hLeast.1 (n + j) (by omega)
    rw [heq, hzero] at hone
    cases hone
  · have heq : W n C (n + j) = (fun x => W n C i x || W n C other x) := by
      funext x
      simpa [hop, GateOp.eval] using heval x
    have hdup := pure_or_zero_left s color (W n C i) (W n C other)
      (WireFacts.wire_monotone C hLeast.1 other) (heq ▸ hp) hz
    exact not_equal_earlier G C hLeast j other hj hother (heq.trans hdup)

lemma pure_gate_children {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (C : Circuit) (hLeast : IsLeastAO G C)
    (hOR : ∀ j, j < C.gates.length → (gateAt C j).op = .or →
      ¬ Pure s false (W n C (n + j)) → ¬ Pure s true (W n C (n + j)) →
      ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i ∈ (gateAt C j).inputs)
    (hp : Pure s false (W n C (n + j)) ∨ Pure s true (W n C (n + j))) :
    Pure s false (W n C i) ∨ Pure s true (W n C i) := by
  rcases all_wires_trichotomy G s hbip C hLeast.1 hOR i with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (pure_gate_no_zero_child G s C hLeast j i hj hi hp h)

end PEqualNP.Outside.L_meta_3566.SemanticPurity


namespace PEqualNP.Outside.L_meta_3566.ConeFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership SemanticPurity

def WirePure {n : ℕ} (s : Fin n → Bool) (C : Circuit) (w : ℕ) : Prop :=
  Pure s false (W n C w) ∨ Pure s true (W n C w)

lemma input_pure {n : ℕ} (s : Fin n → Bool) (C : Circuit) (w : ℕ) (hw : w < n) :
    WirePure s C w := by
  have hp : Pure s (s ⟨w, hw⟩) (W n C w) := by
    intro x
    rw [W_input C w hw x, W_input C w hw (mask s (s ⟨w, hw⟩) x)]
    simp [mask]
  cases hs : s ⟨w, hw⟩
  · exact Or.inl (hs ▸ hp)
  · exact Or.inr (hs ▸ hp)

lemma nonclean_frontier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (C : Circuit) (hLeast : IsLeastAO G C)
    (hOR : ∀ j, j < C.gates.length → (gateAt C j).op = .or →
      ¬ Pure s false (W n C (n + j)) → ¬ Pure s true (W n C (n + j)) →
      ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true)
    (w : ℕ) (hw : w < n + C.gates.length)
    (hdirty : ¬ ∀ x, W n C w x = true → graphFun G ∅ x = true) :
    ∃ ws : List ℕ, ws ≠ [] ∧
      (∀ i ∈ ws, i ≤ w ∧ WirePure s C i) ∧
      ∀ x, W n C w x = ws.all (fun i => W n C i x) := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hp : WirePure s C w
    · refine ⟨[w], by simp, ?_, ?_⟩
      · intro i hi
        have hie := List.mem_singleton.mp hi
        simpa only [hie] using (show w ≤ w ∧ WirePure s C w from ⟨le_rfl, hp⟩)
      · intro x
        simp
    have hwi : ¬ w < n := fun h => hp (input_pure s C w h)
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    have hop : (gateAt C j).op = .and := by
      rcases hLeast.1.1 (gateAt C j) (MixedColor.gateAt_mem hj) with h | h
      · exact h
      · exact False.elim (hdirty (hOR j hj h (fun h => hp (Or.inl h))
          (fun h => hp (Or.inr h))))
    obtain ⟨a, b, hab⟩ := MixedColor.binaryInputs hLeast.1 hj
    have ham : a ∈ (gateAt C j).inputs := by simp [hab]
    have hbm : b ∈ (gateAt C j).inputs := by simp [hab]
    have ha : a < n + j := hLeast.1.2.1 j hj a ham
    have hb : b < n + j := hLeast.1.2.1 j hj b hbm
    obtain ⟨as, has, hap, hav⟩ := ih a ha (by omega) (AndChild.not_below G C hLeast j a hj hop ham)
    obtain ⟨bs, hbs, hbp, hbv⟩ := ih b hb (by omega) (AndChild.not_below G C hLeast j b hj hop hbm)
    refine ⟨as ++ bs, ?_, ?_, ?_⟩
    · intro h
      have h' : as = [] ∧ bs = [] := by simpa using h
      exact has h'.1
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact ⟨by have := (hap i hi).1; omega, (hap i hi).2⟩
      · exact ⟨by have := (hbp i hi).1; omega, (hbp i hi).2⟩
    · intro x
      rw [W_gate C hLeast.1 j hj a b hab x, hop]
      simp only [GateOp.eval, List.all_cons,
        List.all_nil, id_eq, Bool.and_true, List.all_append]
      rw [hav, hbv]

lemma and_frontier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (C : Circuit) (hLeast : IsLeastAO G C)
    (hOR : ∀ j, j < C.gates.length → (gateAt C j).op = .or →
      ¬ Pure s false (W n C (n + j)) → ¬ Pure s true (W n C (n + j)) →
      ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and) :
    ∃ ws : List ℕ, ws ≠ [] ∧
      (∀ i ∈ ws, i < n + j ∧ WirePure s C i) ∧
      ∀ x, W n C (n + j) x = ws.all (fun i => W n C i x) := by
  obtain ⟨a, b, hab⟩ := MixedColor.binaryInputs hLeast.1 hj
  have ham : a ∈ (gateAt C j).inputs := by simp [hab]
  have hbm : b ∈ (gateAt C j).inputs := by simp [hab]
  have ha : a < n + j := hLeast.1.2.1 j hj a ham
  have hb : b < n + j := hLeast.1.2.1 j hj b hbm
  obtain ⟨as, has, hap, hav⟩ := nonclean_frontier G s C hLeast hOR a (by omega)
    (AndChild.not_below G C hLeast j a hj hop ham)
  obtain ⟨bs, hbs, hbp, hbv⟩ := nonclean_frontier G s C hLeast hOR b (by omega)
    (AndChild.not_below G C hLeast j b hj hop hbm)
  refine ⟨as ++ bs, ?_, ?_, ?_⟩
  · intro h
    have h' : as = [] ∧ bs = [] := by simpa using h
    exact has h'.1
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ⟨by have := (hap i hi).1; omega, (hap i hi).2⟩
    · exact ⟨by have := (hbp i hi).1; omega, (hbp i hi).2⟩
  · intro x
    rw [W_gate C hLeast.1 j hj a b hab x, hop]
    simp only [GateOp.eval, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, List.all_append]
    rw [hav, hbv]

lemma all_pure {n : ℕ} (s : Fin n → Bool) (C : Circuit) (color : Bool)
    (ws : List ℕ) (hp : ∀ i ∈ ws, Pure s color (W n C i)) :
    Pure s color (fun x => ws.all (fun i => W n C i x)) := by
  induction ws with
  | nil => intro x; rfl
  | cons w ws ih =>
    intro x
    simp only [List.all_cons]
    have ht := ih (fun i hi => hp i (by simp [hi])) x
    dsimp only at ht
    rw [hp w (by simp) x, ht]

lemma clean_not_pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) (hw : w < n + C.gates.length)
    (hclean : ∀ x, W n C w x = true → graphFun G ∅ x = true) :
    ¬ WirePure s C w := by
  intro hp
  obtain ⟨color, hp⟩ : ∃ color, Pure s color (W n C w) := by
    rcases hp with hp | hp
    · exact ⟨false, hp⟩
    · exact ⟨true, hp⟩
  have hone := wire_one C hAO w hw
  rw [hp] at hone
  have hg := hclean _ hone
  rw [graph_mask_false G s hbip color (fun _ => true)] at hg
  cases hg

lemma clean_and_frontier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (C : Circuit) (hLeast : IsLeastAO G C)
    (hOR : ∀ j, j < C.gates.length → (gateAt C j).op = .or →
      ¬ Pure s false (W n C (n + j)) → ¬ Pure s true (W n C (n + j)) →
      ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (hclean : ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true) :
    ∃ ws : List ℕ, ws ≠ [] ∧
      (∀ i ∈ ws, i < n + j ∧ WirePure s C i) ∧
      (∃ i ∈ ws, Pure s false (W n C i)) ∧
      (∃ i ∈ ws, Pure s true (W n C i)) ∧
      ∀ x, W n C (n + j) x = ws.all (fun i => W n C i x) := by
  classical
  obtain ⟨ws, hne, hws, heval⟩ := and_frontier G s C hLeast hOR j hj hop
  have hnot := clean_not_pure G s hbip C hLeast.1 (n + j) (by omega) hclean
  have heq : W n C (n + j) = (fun x => ws.all (fun i => W n C i x)) := funext heval
  refine ⟨ws, hne, hws, ?_, ?_, heval⟩
  · by_contra h
    apply hnot
    right
    rw [heq]
    apply all_pure
    intro i hi
    rcases (hws i hi).2 with hp | hp
    · exact False.elim (h ⟨i, hi, hp⟩)
    · exact hp
  · by_contra h
    apply hnot
    left
    rw [heq]
    apply all_pure
    intro i hi
    rcases (hws i hi).2 with hp | hp
    · exact hp
    · exact False.elim (h ⟨i, hi, hp⟩)

lemma pair_frontier {n : ℕ} (s : Fin n → Bool) (C : Circuit) (ws : List ℕ)
    (hp : ∀ w ∈ ws, WirePure s C w)
    (hleft : ∃ w ∈ ws, Pure s false (W n C w))
    (hright : ∃ w ∈ ws, Pure s true (W n C w)) :
    ∃ (k : ℕ), 0 < k ∧ ∃ (left right : Fin k → ℕ),
      (∀ i, left i ∈ ws ∧ right i ∈ ws) ∧
      (∀ i, Pure s false (W n C (left i))) ∧
      (∀ i, Pure s true (W n C (right i))) ∧
      ∀ x, ws.all (fun w => W n C w x) =
        PureFunctionFamily.family (fun i => W n C (left i)) (fun i => W n C (right i)) x := by
  classical
  obtain ⟨l, hl, hlp⟩ := hleft
  obtain ⟨r, hr, hrp⟩ := hright
  let left : Fin ws.length → ℕ := fun i =>
    if Pure s false (W n C (ws.get i)) then ws.get i else l
  let right : Fin ws.length → ℕ := fun i =>
    if Pure s false (W n C (ws.get i)) then r else ws.get i
  have hmem : ∀ i, left i ∈ ws ∧ right i ∈ ws := by
    intro i
    by_cases hi : Pure s false (W n C (ws.get i)) <;>
      simp only [left, right, hi, ite_true, ite_false]
    · exact ⟨List.get_mem ws i, hr⟩
    · exact ⟨hl, List.get_mem ws i⟩
  refine ⟨ws.length, ?_, left, right, hmem, ?_, ?_, ?_⟩
  · have hn : ws ≠ [] := by intro he; simp [he] at hl
    exact List.length_pos_iff.mpr hn
  · intro i
    by_cases hi : Pure s false (W n C (ws.get i))
    · simp only [left, hi, ite_true]
    · simpa only [left, hi, ite_false] using hlp
  · intro i
    by_cases hi : Pure s false (W n C (ws.get i))
    · simpa only [right, hi, ite_true] using hrp
    · have hp' := (hp (ws.get i) (List.get_mem ws i)).resolve_left hi
      simpa only [right, hi, ite_false] using hp'
  · intro x
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, PureFunctionFamily.family, decide_eq_true_eq]
    constructor
    · intro hx i
      exact ⟨hx (left i) (hmem i).1, hx (right i) (hmem i).2⟩
    · intro hx w hw
      obtain ⟨i, hiw⟩ := List.mem_iff_get.mp hw
      by_cases hi : Pure s false (W n C (ws.get i))
      · have heq : left i = w := by simp only [left, hi, ite_true]; exact hiw
        simpa only [heq] using (hx i).1
      · have heq : right i = w := by simp only [right, hi, ite_false]; exact hiw
        simpa only [heq] using (hx i).2

lemma clean_and_family {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (C : Circuit) (hLeast : IsLeastAO G C)
    (hOR : ∀ j, j < C.gates.length → (gateAt C j).op = .or →
      ¬ Pure s false (W n C (n + j)) → ¬ Pure s true (W n C (n + j)) →
      ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (hclean : ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true) :
    ∃ (k : ℕ), 0 < k ∧ ∃ (left right : Fin k → ℕ),
      (∀ i, left i < n + j ∧ right i < n + j) ∧
      (∀ i, Pure s false (W n C (left i))) ∧
      (∀ i, Pure s true (W n C (right i))) ∧
      ∀ x, W n C (n + j) x =
        PureFunctionFamily.family (fun i => W n C (left i)) (fun i => W n C (right i)) x := by
  obtain ⟨ws, _, hws, hl, hr, heval⟩ := clean_and_frontier G s hbip C hLeast hOR j hj hop hclean
  obtain ⟨k, hk, left, right, hmem, hlp, hrp, hpair⟩ :=
    pair_frontier s C ws (fun w hw => (hws w hw).2) hl hr
  refine ⟨k, hk, left, right, ?_, hlp, hrp, ?_⟩
  · intro i
    exact ⟨(hws _ (hmem i).1).1, (hws _ (hmem i).2).1⟩
  · intro x
    rw [heval, hpair]

lemma mask_true_eq {n : ℕ} (s : Fin n → Bool) (x : Fin n → Bool) :
    mask s true x = PureFunctionFamily.maskTrue s x := by
  rfl

lemma mask_false_eq {n : ℕ} (s : Fin n → Bool) (x : Fin n → Bool) :
    mask s false x = PureFunctionFamily.maskTrue (fun v => !(s v)) x := by
  funext v
  cases hs : s v <;> simp [mask, PureFunctionFamily.maskTrue, hs]

lemma clean_and_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (C : Circuit) (hLeast : IsLeastAO G C)
    (hOR : ∀ j, j < C.gates.length → (gateAt C j).op = .or →
      ¬ Pure s false (W n C (n + j)) → ¬ Pure s true (W n C (n + j)) →
      ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (hclean : ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧ W n C (n + j) (pairInput a b) = true) :
    ∃ (u : Fin n) (w : ℕ), w < n + j ∧ WirePure s C w ∧
      (∀ x, (x u && W n C w x) = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → W n C (n + j) (pairInput a b) = true →
        (pairInput a b u && W n C w (pairInput a b)) = true) := by
  obtain ⟨k, hk, left, right, hback, hlp, hrp, hval⟩ :=
    clean_and_family G s hbip C hLeast hOR j hj hop hclean
  have hlp' : ∀ i x, W n C (left i) x =
      W n C (left i) (PureFunctionFamily.maskTrue (fun v => !(s v)) x) := by
    intro i x
    rw [← mask_false_eq]
    exact hlp i x
  have hrp' : ∀ i x, W n C (right i) x =
      W n C (right i) (PureFunctionFamily.maskTrue s x) := by
    intro i x
    rw [← mask_true_eq]
    exact hrp i x
  have hbelow' : ∀ x, PureFunctionFamily.family
      (fun i => W n C (left i)) (fun i => W n C (right i)) x = true →
      graphFun G ∅ x = true := by
    intro x hx
    exact hclean x (by rw [hval]; exact hx)
  have haccept' : ∃ a b, G.Adj a b ∧ PureFunctionFamily.family
      (fun i => W n C (left i)) (fun i => W n C (right i)) (pairInput a b) = true := by
    simpa only [hval] using haccept
  obtain ⟨u, i, f, hside, hnewclean, hkeep⟩ :=
    PureFunctionFamily.replacement_existing_side hk G s hbip h4
      (fun i => W n C (left i)) (fun i => W n C (right i))
      (fun i => WireFacts.wire_monotone C hLeast.1 (left i))
      (fun i => WireFacts.wire_monotone C hLeast.1 (right i)) hlp' hrp'
      (fun i => WireFacts.wire_zero C hLeast.1 (left i))
      (fun i => WireFacts.wire_zero C hLeast.1 (right i)) hbelow' haccept'
  have hw : ∃ w, w < n + j ∧ WirePure s C w ∧ W n C w = f := by
    rcases hside with rfl | rfl
    · exact ⟨left i, (hback i).1, Or.inl (hlp i), rfl⟩
    · exact ⟨right i, (hback i).2, Or.inr (hrp i), rfl⟩
  obtain ⟨w, hwb, hwp, hwf⟩ := hw
  refine ⟨u, w, hwb, hwp, ?_, ?_⟩
  · simpa [hwf] using hnewclean
  · intro a b hab hv
    rw [hval] at hv
    simpa [hwf] using hkeep a b hab hv

lemma clean_and_star_all {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (C : Circuit) (hLeast : IsLeastAO G C)
    (hOR : ∀ j, j < C.gates.length → (gateAt C j).op = .or →
      ¬ Pure s false (W n C (n + j)) → ¬ Pure s true (W n C (n + j)) →
      ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (hclean : ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true) :
    ∃ (u : Fin n) (w : ℕ), w < n + j ∧ WirePure s C w ∧
      (∀ x, (x u && W n C w x) = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → W n C (n + j) (pairInput a b) = true →
        (pairInput a b u && W n C w (pairInput a b)) = true) := by
  classical
  by_cases haccept : ∃ a b, G.Adj a b ∧ W n C (n + j) (pairInput a b) = true
  · exact clean_and_star G s hbip h4 C hLeast hOR j hj hop hclean haccept
  obtain ⟨u, v, huv, _, _⟩ := (graphFun_empty_true_iff G (fun _ => true)).mp
    (hclean _ (wire_one C hLeast.1 (n + j) (by omega)))
  refine ⟨u, v.val, by omega, input_pure s C v.val v.isLt, ?_, ?_⟩
  · intro x hx
    rw [W_input C v.val v.isLt] at hx
    have hx' : x u = true ∧ x v = true := by simpa only [Bool.and_eq_true] using hx
    exact (graphFun_empty_true_iff G x).mpr ⟨u, v, huv, hx'.1, hx'.2⟩
  · intro a b hab hv
    exact False.elim (haccept ⟨a, b, hab, hv⟩)

lemma pure_star_opposite_color {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (C : Circuit) (hAO : IsAO2 n C) (u : Fin n) (w : ℕ)
    (hw : w < n + C.gates.length) (hwp : WirePure s C w)
    (hclean : ∀ x, (x u && W n C w x) = true → graphFun G ∅ x = true) :
    Pure s (!(s u)) (W n C w) := by
  have hnot : ¬ Pure s (s u) (W n C w) := by
    intro hp
    have hf : W n C w (mask s (s u) (fun _ => true)) = true := by
      rw [← hp (fun _ => true)]
      exact wire_one C hAO w hw
    have hu : mask s (s u) (fun _ => true) u = true := by simp [mask]
    have hg := hclean (mask s (s u) (fun _ => true)) (by rw [hu, hf]; rfl)
    rw [graph_mask_false G s hbip (s u) (fun _ => true)] at hg
    cases hg
  rcases hwp with hp | hp <;> cases hs : s u
  · exact False.elim (hnot (by simpa only [hs] using hp))
  · simpa only [hs, Bool.not_true] using hp
  · simpa only [hs, Bool.not_false] using hp
  · exact False.elim (hnot (by simpa only [hs] using hp))

end PEqualNP.Outside.L_meta_3566.ConeFrontier

namespace PEqualNP.Outside.L_meta_3566.OrCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma charges_subset_orN_image {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (N : Finset (Fin n)) :
    charges C N ⊆ (orN G C).image (fun j => n + j) := by
  classical
  intro w hw
  obtain ⟨hwlt, hwn, hop, hlarge, _⟩ := Finset.mem_filter.mp hw
  have hwlt' := Finset.mem_range.mp hwlt
  apply Finset.mem_image.mpr
  refine ⟨w - n, ?_, by omega⟩
  simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
  refine ⟨by change w - n < C.gates.length; change w < n + C.gates.length at hwlt'; omega, hop, ?_⟩
  intro hbelow
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (support (n := n) C w).card)
  have hvtrue := (Finset.mem_filter.mp hv).2
  have hvtrue' : gateVal n C (w - n) (pairInput v v) = true := by
    change wire C (n + (w - n)) (pairInput v v) = true
    simpa only [Nat.add_sub_of_le hwn] using hvtrue
  have hg := hbelow (pairInput v v) hvtrue'
  have hfalse : graphFun G ∅ (pairInput v v) = false := by
    simp [graphFun, pairInput]
  rw [hfalse] at hg
  cases hg

lemma sum_charges_le_orN {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (N : Fin k → Finset (Fin n))
    (hN : ∀ i j, i ≠ j → (N i ∩ N j).card ≤ 1) :
    (∑ i, (charges C (N i)).card) ≤ (orN G C).card := by
  classical
  have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun i => charges C (N i)) := by
    intro i _ j _ hij
    exact charges_disjoint C hAO (N i) (N j) (hN i j hij)
  have hsub : Finset.univ.biUnion (fun i => charges C (N i)) ⊆
      (orN G C).image (fun j => n + j) := by
    intro w hw
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
    exact charges_subset_orN_image G C (N i) hwi
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj,
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)] at hc
  simpa using hc

lemma singleton_orN_lower_bound {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (w : Fin k → ℕ) (hw : ∀ i, w i < n + C.size)
    (S N : Fin k → Finset (Fin n))
    (hN : ∀ i j, i ≠ j → (N i ∩ N j).card ≤ 1)
    (hpos : ∀ i v, v ∈ S i → wire C (w i) (pairInput v v) = true)
    (hneg : ∀ i, wire C (w i) (complement (N i)) = false) :
    (∑ i, ((S i).card - 1)) ≤ (orN G C).card := by
  have hlocal : ∀ i, (S i).card - 1 ≤ (charges C (N i)).card := by
    intro i
    have hsub : S i ⊆ support C (w i) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hpos i v hv⟩
    have hc := Finset.card_le_card hsub
    have hb := support_card_le_charges C hAO (N i) (w i) (hw i) (hneg i)
    omega
  exact (Finset.sum_le_sum (fun i _ => hlocal i)).trans (sum_charges_le_orN G C hAO N hN)

end PEqualNP.Outside.L_meta_3566.OrCharge

namespace PEqualNP.Outside.L_meta_3566.OrCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma pure_star_false_complement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b)
    (C : Circuit) (hAO : IsAO2 n C) (z : Fin n) (w : ℕ)
    (hpure : ∀ x : Fin n → Bool, wire C w x =
      wire C w (fun v => if s v ≠ s z then x v else false))
    (hclean : ∀ x : Fin n → Bool, x z = true → wire C w x = true → graphFun G ∅ x = true) :
    wire C w (complement (G.neighborFinset z)) = false := by
  classical
  apply Bool.eq_false_iff.mpr
  intro htrue
  let x : Fin n → Bool := fun v => decide (v = z ∨ (s v ≠ s z ∧ ¬ G.Adj z v))
  have hxz : x z = true := by simp [x]
  have hle : (fun v => if s v ≠ s z then complement (G.neighborFinset z) v else false) ≤ x := by
    intro v
    apply Bool.le_iff_imp.mpr
    intro hv
    have hcol : s v ≠ s z := by
      by_contra hnot
      simp [hnot] at hv
    have hn : ¬ G.Adj z v := by
      simpa [hcol, complement] using hv
    exact decide_eq_true (Or.inr ⟨hcol, hn⟩)
  have hwire : wire C w x = true := by
    have hm := WireFacts.wire_monotone C hAO w hle
    apply Bool.le_iff_imp.mp hm
    change wire C w (fun v => if s v ≠ s z then complement (G.neighborFinset z) v else false) = true
    rw [← hpure]
    exact htrue
  have hg := hclean x hxz hwire
  have hex : ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
    simpa [graphFun] using hg
  obtain ⟨a, b, hab, ha, hb⟩ := hex
  have ha' : a = z ∨ (s a ≠ s z ∧ ¬ G.Adj z a) := by simpa [x] using ha
  have hb' : b = z ∨ (s b ≠ s z ∧ ¬ G.Adj z b) := by simpa [x] using hb
  rcases ha' with rfl | ⟨hac, han⟩ <;> rcases hb' with rfl | ⟨hbc, hbn⟩
  · exact G.irrefl hab
  · exact hbn hab
  · exact han hab.symm
  · have heq : s a = s b := by
      cases hs : s z <;> cases ha : s a <;> cases hb : s b <;> simp_all
    exact hbip a b hab heq

lemma pure_star_orN_lower_bound {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b) (h4 : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (z : Fin k → Fin n) (hz : Function.Injective z)
    (w : Fin k → ℕ) (hw : ∀ i, w i < n + C.size) (S : Fin k → Finset (Fin n))
    (hpos : ∀ i v, v ∈ S i → wire C (w i) (pairInput v v) = true)
    (hpure : ∀ i (x : Fin n → Bool), wire C (w i) x =
      wire C (w i) (fun v => if s v ≠ s (z i) then x v else false))
    (hclean : ∀ i (x : Fin n → Bool), x (z i) = true →
      wire C (w i) x = true → graphFun G ∅ x = true) :
    (∑ i, ((S i).card - 1)) ≤ (orN G C).card := by
  apply singleton_orN_lower_bound G C hAO w hw S (fun i => G.neighborFinset (z i))
  · intro i j hij
    have hne : z i ≠ z j := fun h => hij (hz h)
    have he : G.neighborFinset (z i) ∩ G.neighborFinset (z j) =
        Finset.univ.filter (fun v => G.Adj (z i) v ∧ G.Adj (z j) v) := by
      ext v
      simp
    rw [he]
    exact h4 (z i) (z j) hne
  · exact hpos
  · intro i
    exact pure_star_false_complement G s hbip C hAO (z i) (w i) (hpure i) (hclean i)

end PEqualNP.Outside.L_meta_3566.OrCharge

namespace PEqualNP.Outside.L_meta_3566.OrCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma frontier_support_card_le_charges {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (N : Finset (Fin n)) (W : Finset ℕ)
    (hW : ∀ w ∈ W, w < n + C.size ∧ wire C w (complement N) = false) :
    (W.biUnion (support (n := n) C)).card ≤ (charges C N).card + W.card := by
  classical
  have h := frontier_bound (support (n := n) C) (charges C N)
    (fun v => wire C v (complement N) = false) (n + C.size) (charge_step C hAO N) W hW
  have hfilter : (Finset.range (n + C.size)).filter (· ∈ charges C N) = charges C N := by
    ext v
    constructor
    · exact fun hv => (Finset.mem_filter.mp hv).2
    · intro hv
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (show v ∈ (Finset.range (n + C.size)).filter _ from hv)).1, hv⟩
  simpa only [hfilter] using h

lemma grouped_frontier_orN_bound {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (N : Fin k → Finset (Fin n))
    (hN : ∀ i j, i ≠ j → (N i ∩ N j).card ≤ 1)
    (W : Fin k → Finset ℕ) (S : Fin k → Finset (Fin n))
    (hW : ∀ i w, w ∈ W i → w < n + C.size ∧ wire C w (complement (N i)) = false)
    (hS : ∀ i, S i ⊆ (W i).biUnion (support (n := n) C)) :
    (∑ i, (S i).card) ≤ (orN G C).card + ∑ i, (W i).card := by
  have hlocal : ∀ i, (S i).card ≤ (charges C (N i)).card + (W i).card := by
    intro i
    exact (Finset.card_le_card (hS i)).trans
      (frontier_support_card_le_charges C hAO (N i) (W i) (hW i))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hlocal i)
  rw [Finset.sum_add_distrib] at hsum
  exact hsum.trans (Nat.add_le_add_right (sum_charges_le_orN G C hAO N hN) _)

lemma pure_grouped_frontier_orN_bound {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b) (h4 : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (z : Fin k → Fin n) (hz : Function.Injective z)
    (W : Fin k → Finset ℕ) (S : Fin k → Finset (Fin n))
    (hW : ∀ i w, w ∈ W i → w < n + C.size)
    (hS : ∀ i, S i ⊆ (W i).biUnion (support (n := n) C))
    (hpure : ∀ i w, w ∈ W i → ∀ x : Fin n → Bool, wire C w x =
      wire C w (fun v => if s v ≠ s (z i) then x v else false))
    (hclean : ∀ i w, w ∈ W i → ∀ x : Fin n → Bool, x (z i) = true →
      wire C w x = true → graphFun G ∅ x = true) :
    (∑ i, (S i).card) ≤ (orN G C).card + ∑ i, (W i).card := by
  apply grouped_frontier_orN_bound G C hAO (fun i => G.neighborFinset (z i)) _ W S _ hS
  · intro i j hij
    have hne : z i ≠ z j := fun h => hij (hz h)
    have he : G.neighborFinset (z i) ∩ G.neighborFinset (z j) =
        Finset.univ.filter (fun v => G.Adj (z i) v ∧ G.Adj (z j) v) := by
      ext v
      simp
    rw [he]
    exact h4 (z i) (z j) hne
  · intro i w hw
    exact ⟨hW i w hw,
      pure_star_false_complement G s hbip C hAO (z i) w (hpure i w hw) (hclean i w hw)⟩

end PEqualNP.Outside.L_meta_3566.OrCharge

namespace PEqualNP.Outside.L_meta_3566.OrCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma edge_card_le_star_sum {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin k → Fin n) (S : Fin k → Finset (Fin n))
    (hcover : ∀ a b, G.Adj a b → ∃ i,
      (a = z i ∧ b ∈ S i) ∨ (b = z i ∧ a ∈ S i)) :
    G.edgeFinset.card ≤ ∑ i, (S i).card := by
  classical
  let T : Fin k → Finset (Sym2 (Fin n)) := fun i => (S i).image (fun v => s(z i, v))
  have hsub : G.edgeFinset ⊆ Finset.univ.biUnion T := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      obtain ⟨i, hi⟩ := hcover a b hab
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      rcases hi with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
      · exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
      · exact Finset.mem_image.mpr ⟨a, ha, Sym2.eq_swap⟩
  calc
    G.edgeFinset.card ≤ (Finset.univ.biUnion T).card := Finset.card_le_card hsub
    _ ≤ ∑ i, (T i).card := Finset.card_biUnion_le
    _ ≤ ∑ i, (S i).card := Finset.sum_le_sum (fun i _ => Finset.card_image_le)

lemma pure_star_edge_orN_bound {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b) (h4 : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (z : Fin k → Fin n) (hz : Function.Injective z)
    (W : Fin k → Finset ℕ) (S : Fin k → Finset (Fin n))
    (hW : ∀ i w, w ∈ W i → w < n + C.size)
    (hS : ∀ i, S i ⊆ (W i).biUnion (support (n := n) C))
    (hpure : ∀ i w, w ∈ W i → ∀ x : Fin n → Bool, wire C w x =
      wire C w (fun v => if s v ≠ s (z i) then x v else false))
    (hclean : ∀ i w, w ∈ W i → ∀ x : Fin n → Bool, x (z i) = true →
      wire C w x = true → graphFun G ∅ x = true)
    (hcover : ∀ a b, G.Adj a b → ∃ i,
      (a = z i ∧ b ∈ S i) ∨ (b = z i ∧ a ∈ S i)) :
    G.edgeFinset.card ≤ (orN G C).card + ∑ i, (W i).card := by
  exact (edge_card_le_star_sum G z S hcover).trans
    (pure_grouped_frontier_orN_bound G s hbip h4 C hAO z hz W S hW hS hpure hclean)

end PEqualNP.Outside.L_meta_3566.OrCharge

namespace PEqualNP.Outside.L_meta_3566.TopFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OrCharge

noncomputable def leaves {n : ℕ} (C : Circuit) (w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter fun j => (gateAt C j).op = .and ∧
    Relation.ReflTransGen (MixedColor.OrStep n C) w (n + j)

def BelowWire {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wire C w x = true → graphFun G ∅ x = true

lemma leaves_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    leaves (n := n) C w = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨_, _, hpath⟩ := Finset.mem_filter.mp hj
  rcases Relation.ReflTransGen.cases_head hpath with he | ⟨v, hs, _⟩
  · omega
  · obtain ⟨k, _, he, _, _, _⟩ := hs
    omega

lemma leaves_not_or {n : ℕ} (C : Circuit) (j : ℕ)
    (hop : (gateAt C j).op ≠ .or) :
    leaves (n := n) C (n + j) ⊆ {j} := by
  classical
  intro k hk
  obtain ⟨_, _, hpath⟩ := Finset.mem_filter.mp hk
  rcases Relation.ReflTransGen.cases_head hpath with he | ⟨v, hs, _⟩
  · exact Finset.mem_singleton.mpr (by omega)
  · obtain ⟨r, _, he, hor, _, _⟩ := hs
    have hrj : r = j := by omega
    subst r
    exact (hop hor).elim

lemma leaves_or {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .or) :
    leaves (n := n) C (n + j) = (gateAt C j).inputs.toFinset.biUnion (leaves (n := n) C) := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨hklt, hkand, hpath⟩ := Finset.mem_filter.mp hk
    rcases Relation.ReflTransGen.cases_head hpath with he | ⟨v, hs, hrest⟩
    · have hkj : k = j := by omega
      subst k
      rw [hop] at hkand
      cases hkand
    · obtain ⟨r, _, he, _, hvin, _⟩ := hs
      have hrj : r = j := by omega
      subst r
      exact Finset.mem_biUnion.mpr ⟨v, List.mem_toFinset.mpr hvin,
        Finset.mem_filter.mpr ⟨hklt, hkand, hrest⟩⟩
  · intro hk
    obtain ⟨v, hv, hk⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨hklt, hkand, hrest⟩ := Finset.mem_filter.mp hk
    have hvin := List.mem_toFinset.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨hklt, hkand, Relation.ReflTransGen.head ?_ hrest⟩
    exact ⟨j, hj, rfl, hop, hvin, hAO.2.1 j hj v hvin⟩

lemma leaf_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (w j : ℕ) (hw : BelowWire G C w) (hj : j ∈ leaves (n := n) C w) :
    BelowF G C j := by
  classical
  obtain ⟨_, _, hpath⟩ := Finset.mem_filter.mp hj
  intro x hx
  apply hw x
  exact MixedColor.orStep_up (n := n) (by simp) hpath hx

lemma leaves_card_le_orT {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) (hw : w < n + C.size)
    (hbelow : BelowWire G C w) :
    (leaves (n := n) C w).card ≤ (orT G C).card + 1 := by
  classical
  let Q := (orT G C).image (fun j => n + j)
  have hstep : ∀ v < n + C.size, BelowWire G C v → 1 < (leaves (n := n) C v).card →
      ∃ A : Finset ℕ, (∀ u ∈ A, u < v ∧ BelowWire G C u) ∧
        leaves (n := n) C v ⊆ A.biUnion (leaves (n := n) C) ∧
        A.card ≤ 1 + (if v ∈ Q then 1 else 0) := by
    intro v hv hvg hlarge
    have hn : n ≤ v := by
      by_contra hn
      rw [leaves_input C v (by omega), Finset.card_empty] at hlarge
      omega
    let j := v - n
    have hj : j < C.gates.length := by
      change v - n < C.gates.length
      change v < n + C.gates.length at hv
      omega
    have hvj : n + j = v := by omega
    have hgmem := MixedColor.gateAt_mem hj
    have hor : (gateAt C j).op = .or := by
      rcases hAO.1 _ hgmem with hand | hor
      · have hc := Finset.card_le_card (leaves_not_or (n := n) C j (by rw [hand]; intro h; cases h))
        rw [hvj, Finset.card_singleton] at hc
        omega
      · exact hor
    have hvQ : v ∈ Q := by
      apply Finset.mem_image.mpr
      refine ⟨j, ?_, hvj⟩
      simp only [orT, gatesWhere, Finset.mem_filter, Finset.mem_range]
      refine ⟨hj, hor, ?_⟩
      intro x hx
      apply hvg x
      change wire C (n + j) x = true at hx
      simpa only [hvj] using hx
    refine ⟨(gateAt C j).inputs.toFinset, ?_, ?_, ?_⟩
    · intro u hu
      have huin := List.mem_toFinset.mp hu
      refine ⟨by have h := hAO.2.1 j hj u huin; omega, ?_⟩
      intro x hx
      apply hvg x
      have hle := or_input_le_gate C hAO.2.1 j hj hor u huin x
      rw [hvj] at hle
      exact Bool.le_iff_imp.mp hle hx
    · rw [← hvj, leaves_or C hAO j hj hor]
    · rw [if_pos hvQ]
      exact (List.toFinset_card_le _).trans (by have hh := hAO.2.2 _ hgmem; omega)
  have h := frontier_bound (leaves (n := n) C) Q (BelowWire G C) (n + C.size)
    hstep {w} (by simpa using And.intro hw hbelow)
  have hfilter : (Finset.range (n + C.size)).filter (· ∈ Q) = Q := by
    ext v
    constructor
    · exact fun hv => (Finset.mem_filter.mp hv).2
    · intro hv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      have hjparts : j < C.gates.length ∧ (gateAt C j).op = .or ∧ BelowF G C j := by
        simpa only [orT, gatesWhere, Finset.mem_filter, Finset.mem_range] using hj
      have hjlt := hjparts.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by change n + j < n + C.gates.length; omega),
        Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  have hcard : Q.card = (orT G C).card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  simpa [hfilter, hcard] using h

lemma gate_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (w : ℕ) :
    (orN G C).card + (orT G C).card + (leaves (n := n) C w).card ≤ C.size := by
  classical
  have hNT : Disjoint (orN G C) (orT G C) := by
    apply Finset.disjoint_left.mpr
    intro j hjN hjT
    simp only [orN, orT, gatesWhere, Finset.mem_filter, Finset.mem_range] at hjN hjT
    exact hjN.2.2 hjT.2.2
  have hLA : Disjoint (orN G C ∪ orT G C) (leaves (n := n) C w) := by
    apply Finset.disjoint_left.mpr
    intro j hjO hjL
    have hand := (Finset.mem_filter.mp hjL).2.1
    have hor : (gateAt C j).op = .or := by
      rcases Finset.mem_union.mp hjO with hjN | hjT
      · simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hjN
        exact hjN.2.1
      · simp only [orT, gatesWhere, Finset.mem_filter, Finset.mem_range] at hjT
        exact hjT.2.1
    rw [hor] at hand
    cases hand
  have hsub : (orN G C ∪ orT G C) ∪ leaves (n := n) C w ⊆ Finset.range C.size := by
    intro j hj
    rcases Finset.mem_union.mp hj with hjO | hjL
    · rcases Finset.mem_union.mp hjO with hjN | hjT
      · simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hjN
        exact Finset.mem_range.mpr hjN.1
      · simp only [orT, gatesWhere, Finset.mem_filter, Finset.mem_range] at hjT
        exact Finset.mem_range.mpr hjT.1
    · exact (Finset.mem_filter.mp hjL).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hLA, Finset.card_union_of_disjoint hNT, Finset.card_range] at hc
  exact hc

end PEqualNP.Outside.L_meta_3566.TopFrontier


namespace PEqualNP.Outside.L_meta_3566.TopFrontierCoverage

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership MixedColor


lemma input_not_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) :
    ¬ (∀ x : Fin n → Bool, val C (List.ofFn x) u.val = true → graphFun G ∅ x = true) := by
  intro h
  have hsingle : val C (List.ofFn (pairInput u u)) u.val = true := by
    rw [val_ofFn]
    simp [pairInput]
  have hf := (graphFun_pair G u u).mp (h (pairInput u u) hsingle)
  exact G.irrefl hf

lemma true_below_reaches_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool) (w : ℕ)
    (hbelow : ∀ y : Fin n → Bool, val C (List.ofFn y) w = true → graphFun G ∅ y = true)
    (htrue : val C (List.ofFn x) w = true) :
    ∃ j < C.gates.length, (gateAt C j).op = .and ∧
      Relation.ReflTransGen (OrStep n C) w (n + j) ∧
      val C (List.ofFn x) (n + j) = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hn : n ≤ w := by
      by_contra h
      exact input_not_below G C ⟨w, by omega⟩ hbelow
    have hvalid : w < n + C.gates.length := by
      by_contra h
      rw [val_ge (n := n) (by simp) (by omega)] at htrue
      cases htrue
    let j := w - n
    have hj : j < C.gates.length := by dsimp [j]; omega
    have hw : w = n + j := by dsimp [j]; omega
    rcases hAO.1 _ (gateAt_mem hj) with hop | hop
    · exact ⟨j, hj, hop, by rw [hw], by simpa only [hw] using htrue⟩
    · obtain ⟨i, hi, hib, hit⟩ := (val_or (n := n) (C := C) (x := List.ofFn x) (by simp) hj hop).mp
        (by simpa only [hw] using htrue)
      have hstep : OrStep n C w i := ⟨j, hj, hw, hop, hi, hib⟩
      have hbelow_i : ∀ y : Fin n → Bool, val C (List.ofFn y) i = true → graphFun G ∅ y = true := by
        intro y hy
        exact hbelow y (orStep_up (by simp) (Relation.ReflTransGen.single hstep) hy)
      obtain ⟨k, hk, hkop, hpath, hkt⟩ := ih i (by omega) hbelow_i hit
      exact ⟨k, hk, hkop, Relation.ReflTransGen.head hstep hpath, hkt⟩

lemma reached_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (w j : ℕ)
    (hbelow : ∀ y : Fin n → Bool, val C (List.ofFn y) w = true → graphFun G ∅ y = true)
    (hreach : Relation.ReflTransGen (OrStep n C) w (n + j)) : BelowF G C j := by
  intro x hx
  exact hbelow x (orStep_up (by simp) hreach hx)

lemma edge_reaches_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (a b : Fin n) (hab : G.Adj a b) :
    ∃ j ∈ tops G C, Relation.ReflTransGen (OrStep n C) C.output (n + j) ∧
      gateVal n C j (pairInput a b) = true := by
  classical
  have hb : ∀ y : Fin n → Bool, val C (List.ofFn y) C.output = true → graphFun G ∅ y = true := by
    intro y hy
    change circuitFun n C y = true at hy
    simpa only [hfun] using hy
  have ht : val C (List.ofFn (pairInput a b)) C.output = true := by
    change circuitFun n C (pairInput a b) = true
    rw [hfun]
    exact (graphFun_pair G a b).mpr hab
  obtain ⟨j, hj, hop, hr, hv⟩ := true_below_reaches_and G C hAO (pairInput a b) C.output hb ht
  refine ⟨j, ?_, hr, hv⟩
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
  exact ⟨hj, hop, reached_below G C C.output j hb hr⟩

end PEqualNP.Outside.L_meta_3566.TopFrontierCoverage

namespace PEqualNP.Outside.L_meta_3566.StarGrouping

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OrCharge

def group {n : ℕ} (T : Finset ℕ) (c : ℕ → Fin n) (f : ℕ → ℕ) (v : Fin n) : Finset ℕ :=
  (T.filter (fun j => c j = v)).image f

lemma sum_group_card {n : ℕ} (T : Finset ℕ) (c : ℕ → Fin n) (f : ℕ → ℕ) :
    (∑ v, (group T c f v).card) ≤ T.card := by
  have h := Finset.sum_le_sum
    (fun v (_ : v ∈ (Finset.univ : Finset (Fin n))) =>
      (Finset.card_image_le : (group T c f v).card ≤ (T.filter (fun j => c j = v)).card))
  have he := Finset.sum_card_fiberwise_eq_card_filter T (Finset.univ : Finset (Fin n)) c
  simp only [Finset.mem_univ, Finset.filter_true] at he
  exact h.trans_eq he

lemma mask_pair {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b)
    (a b : Fin n) (hab : G.Adj a b) :
    (fun v => if s v ≠ s a then pairInput a b v else false) = pairInput b b := by
  funext v
  have hba : s b ≠ s a := (hbip a b hab).symm
  by_cases hvb : v = b
  · subst v
    simp [pairInput, hba]
  · by_cases hva : v = a
    · subst v
      simp [pairInput, hvb]
    · simp [pairInput, hvb, hva]

lemma star_pair_support {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b)
    (C : Circuit) (z : Fin n) (w : ℕ)
    (hpure : ∀ x : Fin n → Bool, wire C w x =
      wire C w (fun v => if s v ≠ s z then x v else false))
    (a b : Fin n) (hab : G.Adj a b)
    (hz : pairInput a b z = true) (hw : wire C w (pairInput a b) = true) :
    (a = z ∧ b ∈ support (n := n) C w) ∨
      (b = z ∧ a ∈ support (n := n) C w) := by
  have hz' : z = a ∨ z = b := by simpa [pairInput] using hz
  rcases hz' with hza | hzb
  · subst z
    left
    refine ⟨rfl, ?_⟩
    rw [hpure, mask_pair G s hbip a b hab] at hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, hw⟩
  · subst z
    right
    refine ⟨rfl, ?_⟩
    have he : pairInput a b = pairInput b a := by
      funext v
      simp [pairInput, or_comm]
    rw [he, hpure, mask_pair G s hbip b a hab.symm] at hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hw⟩

lemma edge_orN_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b) (h4 : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (T : Finset ℕ) (c : ℕ → Fin n) (f : ℕ → ℕ)
    (hW : ∀ j ∈ T, f j < n + C.size)
    (hpure : ∀ j ∈ T, ∀ x : Fin n → Bool, wire C (f j) x =
      wire C (f j) (fun v => if s v ≠ s (c j) then x v else false))
    (hclean : ∀ j ∈ T, ∀ x : Fin n → Bool, x (c j) = true →
      wire C (f j) x = true → graphFun G ∅ x = true)
    (hcover : ∀ a b, G.Adj a b → ∃ j ∈ T,
      pairInput a b (c j) = true ∧ wire C (f j) (pairInput a b) = true) :
    G.edgeFinset.card ≤ (orN G C).card + T.card := by
  let W := group T c f
  let S : Fin n → Finset (Fin n) := fun v => (W v).biUnion (support (n := n) C)
  have hgroup : ∀ v w, w ∈ W v → ∃ j ∈ T, c j = v ∧ f j = w := by
    intro v w hw
    obtain ⟨j, hj, hjw⟩ := Finset.mem_image.mp hw
    obtain ⟨hjT, hjv⟩ := Finset.mem_filter.mp hj
    exact ⟨j, hjT, hjv, hjw⟩
  have hmember : ∀ j ∈ T, f j ∈ W (c j) := by
    intro j hj
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, rfl⟩, rfl⟩
  have hbound : G.edgeFinset.card ≤ (orN G C).card + ∑ v, (W v).card := by
    apply pure_star_edge_orN_bound G s hbip h4 C hAO id Function.injective_id W S
    · intro v w hw
      obtain ⟨j, hj, _, rfl⟩ := hgroup v w hw
      exact hW j hj
    · intro v
      exact Finset.Subset.refl _
    · intro v w hw x
      obtain ⟨j, hj, rfl, rfl⟩ := hgroup v w hw
      exact hpure j hj x
    · intro v w hw x hx hwx
      obtain ⟨j, hj, rfl, rfl⟩ := hgroup v w hw
      exact hclean j hj x hx hwx
    · intro a b hab
      obtain ⟨j, hj, hc, hf⟩ := hcover a b hab
      refine ⟨c j, ?_⟩
      rcases star_pair_support G s hbip C (c j) (f j) (hpure j hj) a b hab hc hf with
        ⟨hac, hb⟩ | ⟨hbc, ha⟩
      · exact Or.inl ⟨hac, Finset.mem_biUnion.mpr ⟨f j, hmember j hj, hb⟩⟩
      · exact Or.inr ⟨hbc, Finset.mem_biUnion.mpr ⟨f j, hmember j hj, ha⟩⟩
  exact hbound.trans (Nat.add_le_add_left (sum_group_card T c f) _)

end PEqualNP.Outside.L_meta_3566.StarGrouping

namespace PEqualNP.Outside.L_meta_3566.ConditionalStarBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OrCharge TopFrontier

lemma output_valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfun : circuitFun n C = graphFun G ∅) (hne : G.edgeFinset.Nonempty) :
    C.output < n + C.size := by
  obtain ⟨e, he⟩ := hne
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    have ht : MixedColor.val C (List.ofFn (pairInput a b)) C.output = true := by
      change circuitFun n C (pairInput a b) = true
      rw [hfun]
      exact (MixedColor.graphFun_pair G a b).mpr hab
    by_contra hbad
    have hz := MixedColor.val_ge (n := n) (C := C) (x := List.ofFn (pairInput a b))
      (by simp) (show n + C.gates.length ≤ C.output by change n + C.size ≤ C.output; omega)
    rw [hz] at ht
    cases ht

lemma exists_cover_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b) (h4 : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hne : G.edgeFinset.Nonempty) (c : ℕ → Fin n) (f : ℕ → ℕ)
    (hW : ∀ j ∈ tops G C, f j < n + C.size)
    (hpure : ∀ j ∈ tops G C, ∀ x : Fin n → Bool, wire C (f j) x =
      wire C (f j) (fun v => if s v ≠ s (c j) then x v else false))
    (hclean : ∀ j ∈ tops G C, ∀ x : Fin n → Bool, x (c j) = true →
      wire C (f j) x = true → graphFun G ∅ x = true)
    (hretain : ∀ j ∈ tops G C, ∀ a b, G.Adj a b → gateVal n C j (pairInput a b) = true →
      pairInput a b (c j) = true ∧ wire C (f j) (pairInput a b) = true) :
    ∃ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) ∧
      G.edgeFinset.card + K.card ≤ C.size + 1 := by
  classical
  let T := leaves (n := n) C C.output
  have hbelow : BelowWire G C C.output := by
    intro x hx
    change circuitFun n C x = true at hx
    simpa only [hfun] using hx
  have hTtop : ∀ j ∈ T, j ∈ tops G C := by
    intro j hj
    obtain ⟨hjlt, hjand, _⟩ := Finset.mem_filter.mp hj
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨Finset.mem_range.mp hjlt, hjand, leaf_below G C C.output j hbelow hj⟩
  have hcover : ∀ a b, G.Adj a b → ∃ j ∈ T,
      pairInput a b (c j) = true ∧ wire C (f j) (pairInput a b) = true := by
    intro a b hab
    obtain ⟨j, hjtop, hpath, hjtrue⟩ := TopFrontierCoverage.edge_reaches_top G C hAO hfun a b hab
    have hjparts : j < C.gates.length ∧ (gateAt C j).op = .and ∧ BelowF G C j := by
      simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using hjtop
    have hjT : j ∈ T :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjparts.1, hjparts.2.1, hpath⟩
    exact ⟨j, hjT, hretain j hjtop a b hab hjtrue⟩
  have hedge := StarGrouping.edge_orN_bound G s hbip h4 C hAO T c f
    (fun j hj => hW j (hTtop j hj)) (fun j hj => hpure j (hTtop j hj))
    (fun j hj => hclean j (hTtop j hj)) hcover
  have hTcard := leaves_card_le_orT G C hAO C.output (output_valid G C hfun hne) hbelow
  have hcount := gate_count G C C.output
  refine ⟨T.image c, ?_, ?_⟩
  · intro a b hab
    obtain ⟨j, hj, hz, _⟩ := hcover a b hab
    have hz' : c j = a ∨ c j = b := by simpa [pairInput] using hz
    rcases hz' with ha | hb
    · exact Or.inl (Finset.mem_image.mpr ⟨j, hj, ha⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨j, hj, hb⟩)
  · have hK := Finset.card_image_le (s := T) (f := c)
    change T.card ≤ (orT G C).card + 1 at hTcard
    change (orN G C).card + (orT G C).card + T.card ≤ C.size at hcount
    omega

end PEqualNP.Outside.L_meta_3566.ConditionalStarBound

namespace PEqualNP.Outside.L_meta_3566.ConditionalMixedBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership SemanticPurity OrCharge

lemma exists_cover_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b) (h4 : NoFourCycle G)
    (C : Circuit) (hLeast : IsLeastAO G C) (hne : G.edgeFinset.Nonempty)
    (hOR : ∀ j, j < C.gates.length → (gateAt C j).op = .or →
      ¬ Pure s false (W n C (n + j)) → ¬ Pure s true (W n C (n + j)) →
      ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true) :
    ∃ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) ∧
      G.edgeFinset.card + K.card ≤ C.size + 1 := by
  classical
  have hn : Nonempty (Fin n) := by
    obtain ⟨e, _⟩ := hne
    induction e using Sym2.ind with
    | _ a _ => exact ⟨a⟩
  let u0 : Fin n := Classical.choice hn
  have hex : ∀ j : ℕ, ∃ (u : Fin n) (w : ℕ), j ∈ tops G C →
      w < n + C.size ∧
      (∀ x : Fin n → Bool, wire C w x =
        wire C w (fun v => if s v ≠ s u then x v else false)) ∧
      (∀ x : Fin n → Bool, x u = true → wire C w x = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → gateVal n C j (pairInput a b) = true →
        pairInput a b u = true ∧ wire C w (pairInput a b) = true) := by
    intro j
    by_cases hjtop : j ∈ tops G C
    · have hjparts : j < C.gates.length ∧ (gateAt C j).op = .and ∧ BelowF G C j := by
        simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using hjtop
      obtain ⟨u, w, hwb, hwp, hclean, hkeep⟩ := ConeFrontier.clean_and_star_all G s hbip h4
        C hLeast hOR j hjparts.1 hjparts.2.1 hjparts.2.2
      have hwvalid : w < n + C.gates.length := by omega
      have hopp := ConeFrontier.pure_star_opposite_color G s hbip C hLeast.1 u w hwvalid hwp hclean
      refine ⟨u, w, fun _ => ⟨hwvalid, ?_, ?_, ?_⟩⟩
      · intro x
        have he := hopp x
        change wire C w x = wire C w (mask s (!(s u)) x) at he
        have hm : mask s (!(s u)) x = (fun v => if s v ≠ s u then x v else false) := by
          funext v
          cases hv : s v <;> cases hu : s u <;> simp [mask, hv, hu]
        simpa only [hm] using he
      · intro x hxu hxw
        change W n C w x = true at hxw
        exact hclean x (by rw [hxu, hxw]; rfl)
      · intro a b hab hjtrue
        have h := hkeep a b hab hjtrue
        simpa only [Bool.and_eq_true, W, wire] using h
    · exact ⟨u0, 0, fun h => False.elim (hjtop h)⟩
  choose c f hcf using hex
  apply ConditionalStarBound.exists_cover_budget G s hbip h4 C hLeast.1 hLeast.2.1 hne c f
  · intro j hj
    exact (hcf j hj).1
  · intro j hj
    exact (hcf j hj).2.1
  · intro j hj
    exact (hcf j hj).2.2.1
  · intro j hj
    exact (hcf j hj).2.2.2

lemma dirty_mixed_or_of_no_cover_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b) (h4 : NoFourCycle G)
    (C : Circuit) (hLeast : IsLeastAO G C) (hne : G.edgeFinset.Nonempty)
    (hbad : ¬ ∃ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) ∧
      G.edgeFinset.card + K.card ≤ C.size + 1) :
    ∃ j < C.gates.length, (gateAt C j).op = .or ∧
      ¬ Pure s false (W n C (n + j)) ∧ ¬ Pure s true (W n C (n + j)) ∧ ¬ BelowF G C j := by
  classical
  by_contra hnone
  apply hbad
  apply exists_cover_budget G s hbip h4 C hLeast hne
  intro j hj hop hleft hright
  by_contra hnot
  apply hnone
  exact ⟨j, hj, hop, hleft, hright, hnot⟩

end PEqualNP.Outside.L_meta_3566.ConditionalMixedBound


namespace PEqualNP.Outside.L_meta_3566.PaddedStars

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership Splice PrivateBlock

def copy (w : ℕ) : Gate := ⟨.and, [w, w]⟩

def block (m u v p q r : ℕ) : List Gate :=
  twoStars m u v p q ++ List.replicate r (copy (m + 2))

lemma block_length (m u v p q r : ℕ) : (block m u v p q r).length = 3 + r := by
  simp [block, twoStars_length]

lemma copy_value (a : List Bool) (w r : ℕ) (hw : w < a.length) :
    ((List.replicate (r + 1) (copy w)).foldl stepWire a).getD (a.length + r) false =
      a.getD w false := by
  rw [List.replicate_succ', List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : ((List.replicate r (copy w)).foldl stepWire a).length = a.length + r := by
    simp [foldl_stepWire_length]
  rw [← hlen, stepWire_getD_len]
  simp only [copy, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true, Bool.and_self]
  exact foldl_stepWire_getD_lt _ a w hw

lemma block_value {n : ℕ} (pre : List Gate) (u v : Fin n) (p q r : ℕ)
    (hp : p < n + pre.length) (hq : q < n + pre.length) (x : Fin n → Bool) :
    blockValue pre (block (n + pre.length) u.val v.val p q r) x = starFun pre u v p q x := by
  cases r with
  | zero => simpa [block] using twoStars_blockValue pre u v p q hp hq x
  | succ r =>
    let a := (twoStars (n + pre.length) u.val v.val p q).foldl stepWire
      (pre.foldl stepWire (List.ofFn x))
    have ha : a.length = n + pre.length + 3 := by
      simp [a, foldl_stepWire_length, twoStars_length]
    have hv := copy_value a (n + pre.length + 2) r (by omega)
    have hb := twoStars_blockValue pre u v p q hp hq x
    have hi : n + pre.length + (3 + (r + 1)) - 1 = a.length + r := by omega
    change a.getD (n + pre.length + 3 - 1) false = _ at hb
    have hi2 : n + pre.length + 3 - 1 = n + pre.length + 2 := by omega
    rw [hi2] at hb
    simp only [blockValue, block, List.foldl_append, List.length_append, twoStars_length, List.length_replicate]
    rw [hi]
    exact hv.trans hb

lemma block_ao {n : ℕ} (pre old post : List Gate) (output : ℕ)
    (hAO : IsAO2 n (circuit pre old post output)) (r : ℕ) (hlen : old.length = 3 + r)
    (u v : Fin n) (p q : ℕ) (hp : p < n + pre.length) (hq : q < n + pre.length) :
    IsAO2 n (circuit pre (block (n + pre.length) u.val v.val p q r) post output) := by
  apply replace_ao pre old _ post output hAO (by simpa only [block_length] using hlen)
  · intro g hg
    simp only [block, List.mem_append, List.mem_replicate] at hg
    rcases hg with hg | ⟨_, rfl⟩
    · simp only [twoStars, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp
    · simp [copy]
  · intro g hg
    simp only [block, List.mem_append, List.mem_replicate] at hg
    rcases hg with hg | ⟨_, rfl⟩
    · simp only [twoStars, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> rfl
    · rfl
  · intro j hj i hi
    by_cases hj3 : j < 3
    · rw [block, List.getD_append _ _ _ _ (by simpa only [twoStars_length] using hj3)] at hi
      interval_cases j <;> simp [twoStars] at hi <;> rcases hi with rfl | rfl <;> omega
    · have hjr : j - 3 < r := by rw [block_length] at hj; omega
      rw [block, List.getD_append_right _ _ _ _ (by simp only [twoStars_length]; omega)] at hi
      simp only [twoStars_length] at hi
      have heq : (List.replicate r (copy (n + pre.length + 2))).getD (j - 3) ⟨.or, []⟩ =
          copy (n + pre.length + 2) := by
        simp [List.getD_eq_getElem?_getD, hjr]
      rw [heq] at hi
      simp [copy] at hi
      omega

lemma first_copy_gate {n : ℕ} (pre post : List Gate) (output : ℕ)
    (u v : Fin n) (p q r : ℕ) (hr : 0 < r) :
    gateAt (circuit pre (block (n + pre.length) u.val v.val p q r) post output) (pre.length + 3) =
      copy (n + pre.length + 2) := by
  simp only [gateAt, circuit]
  rw [List.getD_append _ _ _ _ (by simp [block_length]; omega),
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [block, List.getD_append_right _ _ _ _ (by simp [twoStars_length])]
  simp [twoStars_length, List.getD_eq_getElem?_getD, hr]

lemma least_private_block_short {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre old post : List Gate) (output : ℕ)
    (hLeast : IsLeastAO G (circuit pre old post output)) (r : ℕ) (hlen : old.length = 3 + r)
    (hreads : ∀ g ∈ post, ∀ i ∈ g.inputs, i ∉ interior n pre old)
    (hout : output ∉ interior n pre old)
    (u v : Fin n) (p q : ℕ) (hp : p < n + pre.length) (hq : q < n + pre.length)
    (hkeep : ∀ a b, G.Adj a b → blockValue pre old (pairInput a b) = true →
      starFun pre u v p q (pairInput a b) = true)
    (hclean : ∀ x : Fin n → Bool, starFun pre u v p q x = true → graphFun G ∅ x = true) : r = 0 := by
  by_contra hr0
  have hr : 0 < r := Nat.pos_of_ne_zero hr0
  let new := block (n + pre.length) u.val v.val p q r
  let D := circuit pre new post output
  have hD : IsAO2 n D := block_ao pre old post output hLeast.1 r hlen u v p q hp hq
  have hspec : circuitFun n D = graphFun G ∅ ∧ D.size = (circuit pre old post output).size := by
    apply correct_of_edge_cover G pre old new post output hLeast.1 hLeast.2.1 hD
      (by simpa only [new, block_length] using hlen) (by omega) hreads hout
    · intro a b hab hx
      simpa only [new, block_value pre u v p q r hp hq] using hkeep a b hab hx
    · intro x hx
      apply hclean x
      simpa only [new, block_value pre u v p q r hp hq] using hx
  have hDL : IsLeastAO G D := ⟨hD, hspec.1, fun E hE hf => by
    rw [hspec.2]
    exact hLeast.2.2 E hE hf⟩
  have hj : pre.length + 3 < D.gates.length := by
    simp only [D, circuit, List.length_append, new, block_length]
    omega
  apply SemanticPurity.not_equal_earlier G D hDL (pre.length + 3) (n + pre.length + 2) hj (by omega)
  funext x
  change (D.wires (List.ofFn x)).getD (n + (pre.length + 3)) false =
    (D.wires (List.ofFn x)).getD (n + pre.length + 2) false
  rw [gate_wire_eval D hD.2.1 _ hj]
  have hgate := first_copy_gate pre post output u v p q r hr
  change gateAt D (pre.length + 3) = copy (n + pre.length + 2) at hgate
  rw [hgate]
  simp [copy, GateOp.eval]

end PEqualNP.Outside.L_meta_3566.PaddedStars


namespace PEqualNP.Outside.L_meta_3566.ParallelRewrite

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma value_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    value C x w = x ⟨w, hw⟩ :=
  MixedColor.val_ofFn C x ⟨w, hw⟩

lemma value_missing {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : value C x w = false :=
  MixedColor.val_ge (n := n) (C := C) (x := List.ofFn x) (by simp) hw

lemma value_gate {n : ℕ} (C : Circuit) (hback : ReadsBack n C)
    (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    value C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (value C x)) :=
  gate_wire_eval C hback j hj x

lemma wire_relation {n : ℕ} (C D : Circuit)
    (hsize : D.gates.length = C.gates.length)
    (hC : ReadsBack n C) (hD : ReadsBack n D) (x : Fin n → Bool)
    (R : ℕ → Bool → Bool → Prop)
    (hinput : ∀ w (hw : w < n), R w (x ⟨w, hw⟩) (x ⟨w, hw⟩))
    (hmissing : ∀ w, n + C.gates.length ≤ w → R w false false)
    (hstep : ∀ j, j < C.gates.length →
      (∀ i, i < n + j → R i (value C x i) (value D x i)) →
      R (n + j)
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (value C x)))
        ((gateAt D j).op.eval ((gateAt D j).inputs.map (value D x)))) :
    ∀ w, R w (value C x w) (value D x w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · rw [value_input C x w hw, value_input D x w hw]
      exact hinput w hw
    by_cases hlim : w < n + C.gates.length
    · let j := w - n
      have hj : j < C.gates.length := by dsimp [j]; omega
      have hjD : j < D.gates.length := by omega
      have heq : n + j = w := by dsimp [j]; omega
      rw [← heq, value_gate C hC x j hj, value_gate D hD x j hjD]
      apply hstep j hj
      intro i hi
      exact ih i (by omega)
    · have hge : n + C.gates.length ≤ w := by omega
      rw [value_missing C x w hge, value_missing D x w (by omega)]
      exact hmissing w hge

lemma preserve_closed_wires {n : ℕ} (C D : Circuit)
    (hsize : D.gates.length = C.gates.length)
    (hC : ReadsBack n C) (hD : ReadsBack n D)
    (P : ℕ → Prop)
    (hsame : ∀ j, j < C.gates.length → P (n + j) → gateAt D j = gateAt C j)
    (hclosed : ∀ j, j < C.gates.length → P (n + j) →
      ∀ i ∈ (gateAt C j).inputs, P i) :
    ∀ x : Fin n → Bool, ∀ w, P w → value D x w = value C x w := by
  intro x
  apply wire_relation C D hsize hC hD x (fun w a b => P w → b = a)
  · intro w hw _
    rfl
  · intro w hw _
    rfl
  · intro j hj ih hp
    rw [hsame j hj hp]
    apply congrArg (gateAt C j).op.eval
    apply List.map_congr_left
    intro i hi
    exact ih i (hC j hj i hi) (hclosed j hj hp i hi)

lemma equality_on_input {n : ℕ} (C D : Circuit)
    (hsize : D.gates.length = C.gates.length)
    (hC : ReadsBack n C) (hD : ReadsBack n D) (x : Fin n → Bool)
    (hlocal : ∀ j, j < C.gates.length →
      (gateAt D j).op.eval ((gateAt D j).inputs.map (value C x)) =
        (gateAt C j).op.eval ((gateAt C j).inputs.map (value C x))) :
    ∀ w, value D x w = value C x w := by
  apply wire_relation C D hsize hC hD x (fun _ a b => b = a)
  · intro w hw
    rfl
  · intro w hw
    rfl
  · intro j hj ih
    rw [← hlocal j hj]
    apply congrArg (gateAt D j).op.eval
    apply List.map_congr_left
    intro i hi
    exact ih i (hD j (by omega) i hi)

lemma function_eq_of_local {n : ℕ} (C D : Circuit)
    (hsize : D.gates.length = C.gates.length) (hout : D.output = C.output)
    (hC : ReadsBack n C) (hD : ReadsBack n D)
    (hlocal : ∀ x : Fin n → Bool, ∀ j, j < C.gates.length →
      (gateAt D j).op.eval ((gateAt D j).inputs.map (value C x)) =
        (gateAt C j).op.eval ((gateAt C j).inputs.map (value C x))) :
    circuitFun n D = circuitFun n C := by
  funext x
  change value D x D.output = value C x C.output
  rw [hout]
  exact equality_on_input C D hsize hC hD x (hlocal x) C.output

lemma gate_eval_mono_on_inputs (g : Gate) (hao : g.op = .and ∨ g.op = .or)
    (f h : ℕ → Bool) (hfh : ∀ i ∈ g.inputs, f i ≤ h i) :
    g.op.eval (g.inputs.map f) ≤ g.op.eval (g.inputs.map h) := by
  let f' : ℕ → Bool := fun i => if i ∈ g.inputs then f i else h i
  have h' : ∀ i, f' i ≤ h i := by
    intro i
    by_cases hi : i ∈ g.inputs
    · simpa [f', hi] using hfh i hi
    · simp [f', hi]
  have hmap : g.inputs.map f' = g.inputs.map f := by
    apply List.map_congr_left
    intro i hi
    simp [f', hi]
  simpa only [hmap] using Splice.ao_eval_mono g hao f' h h'

lemma domination_on_input {n : ℕ} (C D : Circuit)
    (hsize : D.gates.length = C.gates.length)
    (hC : ReadsBack n C) (hD : IsAO2 n D) (x : Fin n → Bool)
    (hlocal : ∀ j, j < C.gates.length →
      (gateAt C j).op.eval ((gateAt C j).inputs.map (value C x)) ≤
        (gateAt D j).op.eval ((gateAt D j).inputs.map (value C x))) :
    ∀ w, value C x w ≤ value D x w := by
  apply wire_relation C D hsize hC hD.2.1 x (fun _ a b => a ≤ b)
  · intro w hw
    exact le_rfl
  · intro w hw
    exact le_rfl
  · intro j hj ih
    apply (hlocal j hj).trans
    have hjD : j < D.gates.length := by omega
    apply gate_eval_mono_on_inputs (gateAt D j) (hD.1 _ (MixedColor.gateAt_mem hjD))
    intro i hi
    exact ih i (hD.2.1 j hjD i hi)

lemma graph_correct_of_local {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hsize : D.gates.length = C.gates.length) (hout : D.output = C.output)
    (hC : ReadsBack n C) (hD : IsAO2 n D) (hfun : circuitFun n C = graphFun G ∅)
    (hnegative : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      ∀ j, j < C.gates.length →
        (gateAt D j).op.eval ((gateAt D j).inputs.map (value C x)) =
          (gateAt C j).op.eval ((gateAt C j).inputs.map (value C x)))
    (hedge : ∀ a b, G.Adj a b → ∀ j, j < C.gates.length →
      (gateAt C j).op.eval ((gateAt C j).inputs.map (value C (pairInput a b))) ≤
        (gateAt D j).op.eval ((gateAt D j).inputs.map (value C (pairInput a b)))) :
    circuitFun n D = graphFun G ∅ := by
  apply (graphFun_boundary_iff G (circuitFun n D) (Splice.circuitFun_monotone n D hD.1)).mpr
  constructor
  · intro a b hab
    have hle := domination_on_input C D hsize hC hD (pairInput a b) (hedge a b hab) C.output
    have htrue : value C (pairInput a b) C.output = true := by
      change circuitFun n C (pairInput a b) = true
      rw [hfun]
      exact graphFun_pair_true G hab
    change value D (pairInput a b) D.output = true
    rw [hout]
    exact bool_true_of_le hle htrue
  · intro S hS
    have hx : graphFun G ∅ (supportInput S) = false := graphFun_independent_false G hS.1
    have heq := equality_on_input C D hsize hC hD.2.1 (supportInput S)
      (hnegative (supportInput S) hx) C.output
    change value D (supportInput S) D.output = false
    rw [hout, heq]
    change circuitFun n C (supportInput S) = false
    rw [hfun]
    exact hx

def rewrite (C : Circuit) (f : Fin C.gates.length → Gate) : Circuit :=
  ⟨List.ofFn f, C.output⟩

lemma rewrite_length (C : Circuit) (f : Fin C.gates.length → Gate) :
    (rewrite C f).gates.length = C.gates.length := by simp [rewrite]

lemma rewrite_size (C : Circuit) (f : Fin C.gates.length → Gate) :
    (rewrite C f).size = C.size := by simp [Circuit.size, rewrite]

lemma rewrite_output (C : Circuit) (f : Fin C.gates.length → Gate) :
    (rewrite C f).output = C.output := rfl

lemma rewrite_gate (C : Circuit) (f : Fin C.gates.length → Gate)
    (j : ℕ) (hj : j < C.gates.length) :
    gateAt (rewrite C f) j = f ⟨j, hj⟩ := by
  simp [rewrite, gateAt, List.getD_eq_getElem?_getD, hj]

lemma rewrite_ao {n : ℕ} (C : Circuit) (f : Fin C.gates.length → Gate)
    (hop : ∀ j, (f j).op = .and ∨ (f j).op = .or)
    (hbinary : ∀ j, (f j).inputs.length = 2)
    (hback : ∀ j, ∀ w ∈ (f j).inputs, w < n + j.val) :
    IsAO2 n (rewrite C f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    change g ∈ List.ofFn f at hg
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
    exact hop j
  · intro j hj w hw
    have hj' : j < C.gates.length := by simpa only [rewrite_length] using hj
    rw [rewrite_gate C f j hj'] at hw
    exact hback ⟨j, hj'⟩ w hw
  · intro g hg
    change g ∈ List.ofFn f at hg
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
    exact hbinary j

lemma rewrite_preserves_closed {n : ℕ} (C : Circuit) (hC : ReadsBack n C)
    (f : Fin C.gates.length → Gate)
    (hback : ReadsBack n (rewrite C f)) (P : ℕ → Prop)
    (hsame : ∀ j : Fin C.gates.length, P (n + j.val) → f j = gateAt C j.val)
    (hclosed : ∀ j, j < C.gates.length → P (n + j) →
      ∀ i ∈ (gateAt C j).inputs, P i) :
    ∀ x : Fin n → Bool, ∀ w, P w → value (rewrite C f) x w = value C x w := by
  apply preserve_closed_wires C (rewrite C f) (rewrite_length C f) hC hback P
  · intro j hj hp
    rw [rewrite_gate C f j hj]
    exact hsame ⟨j, hj⟩ hp
  · exact hclosed

end PEqualNP.Outside.L_meta_3566.ParallelRewrite


namespace PEqualNP.Outside.L_meta_3566.PureTopAux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  SemanticPurity

lemma nonclean_gate_children {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (C : Circuit) (hLeast : IsLeastAO G C)
    (hOR : ∀ j, j < C.gates.length → (gateAt C j).op = .or →
      ¬ Pure s false (W n C (n + j)) → ¬ Pure s true (W n C (n + j)) →
      ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true)
    (j : ℕ) (hj : j < C.gates.length)
    (hdirty : ¬ ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true)
    (i : ℕ) (hi : i ∈ (gateAt C j).inputs) :
    ¬ ∀ x, W n C i x = true → graphFun G ∅ x = true := by
  classical
  rcases hLeast.1.1 (gateAt C j) (MixedColor.gateAt_mem hj) with hop | hop
  · exact AndChild.not_below G C hLeast j i hj hop hi
  · have hp : Pure s false (W n C (n + j)) ∨ Pure s true (W n C (n + j)) := by
      by_contra h
      exact hdirty (hOR j hj hop (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h')))
    have hpi := pure_gate_children G s hbip C hLeast hOR j i hj hi hp
    intro hclean
    have hz := below_zero_sides G s hbip (W n C i) hclean
    have hi' := hLeast.1.2.1 j hj i hi
    have hone := wire_one C hLeast.1 i (by omega)
    rcases hpi with hp | hp
    · rw [hp (fun _ => true), hz false (fun _ => true)] at hone
      cases hone
    · rw [hp (fun _ => true), hz true (fun _ => true)] at hone
      cases hone

end PEqualNP.Outside.L_meta_3566.PureTopAux


namespace PEqualNP.Outside.L_meta_3566.PureTopNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
  SemanticPurity ConeFrontier ParallelRewrite

lemma normalize {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (C : Circuit) (hLeast : IsLeastAO G C)
    (hOR : ∀ j, j < C.gates.length → (gateAt C j).op = .or →
      ¬ Pure s false (W n C (n + j)) → ¬ Pure s true (W n C (n + j)) →
      ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧
      D.gates.length = C.gates.length ∧ D.output = C.output ∧
      (∀ w, (¬ ∀ x, W n C w x = true → graphFun G ∅ x = true) →
        W n D w = W n C w) ∧
      (∀ j, j < D.gates.length → (gateAt D j).op = .and →
        (∀ x, W n D (n + j) x = true → graphFun G ∅ x = true) →
        ∃ (u : Fin n) (w : ℕ), w < n + j ∧
          gateAt D j = ⟨.and, [u.val, w]⟩ ∧
          Pure s (!(s u)) (W n D w) ∧
          (∀ x, (x u && W n D w x) = true → graphFun G ∅ x = true)) := by
  classical
  let Clean : ℕ → Prop := fun w => ∀ x, W n C w x = true → graphFun G ∅ x = true
  let Selected : Fin C.gates.length → Prop := fun j =>
    (gateAt C j.val).op = .and ∧ Clean (n + j.val)
  let T := {j : Fin C.gates.length // Selected j}
  have hchoose : ∀ t : T, ∃ (u : Fin n) (w : ℕ), w < n + t.val.val ∧
      WirePure s C w ∧
      (∀ x, (x u && W n C w x) = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → W n C (n + t.val.val) (pairInput a b) = true →
        (pairInput a b u && W n C w (pairInput a b)) = true) := by
    intro t
    exact clean_and_star_all G s hbip h4 C hLeast hOR t.val.val t.val.isLt t.property.1
      t.property.2
  choose u w hback hpure hclean hkeep using hchoose
  let f : Fin C.gates.length → Gate := fun j =>
    if h : Selected j then ⟨.and, [(u ⟨j, h⟩).val, w ⟨j, h⟩]⟩ else gateAt C j.val
  let D := rewrite C f
  have hlen : D.gates.length = C.gates.length := rewrite_length C f
  have hsize : D.size = C.size := rewrite_size C f
  have hout : D.output = C.output := rfl
  have hgate (j : Fin C.gates.length) : gateAt D j.val = f j :=
    rewrite_gate C f j.val j.isLt
  have hselected (j : Fin C.gates.length) (h : Selected j) :
      gateAt D j.val = ⟨.and, [(u ⟨j, h⟩).val, w ⟨j, h⟩]⟩ := by
    rw [hgate]
    exact dite_eq_left h
  have hunselected (j : Fin C.gates.length) (h : ¬ Selected j) :
      gateAt D j.val = gateAt C j.val := by
    rw [hgate]
    exact dite_eq_right h
  have hAO : IsAO2 n D := by
    apply rewrite_ao C f
    · intro j
      by_cases h : Selected j
      · simp [f, h]
      · simpa [f, h] using hLeast.1.1 (gateAt C j.val) (MixedColor.gateAt_mem j.isLt)
    · intro j
      by_cases h : Selected j
      · simp [f, h]
      · simpa [f, h] using hLeast.1.2.2 (gateAt C j.val) (MixedColor.gateAt_mem j.isLt)
    · intro j i hi
      by_cases h : Selected j
      · simp only [f, dite_eq_left h, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact lt_of_lt_of_le (u ⟨j, h⟩).isLt (Nat.le_add_right n j.val)
        · exact hback ⟨j, h⟩
      · simp only [f, dite_eq_right h] at hi
        exact hLeast.1.2.1 j.val j.isLt i hi
  have heval (t : T) (x : Fin n → Bool) :
      (gateAt D t.val.val).op.eval
        ((gateAt D t.val.val).inputs.map (value C x)) =
        (x (u t) && W n C (w t) x) := by
    rw [hselected t.val t.property]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      Bool.and_true]
    rw [value_input C x (u t).val (u t).isLt]
    rfl
  have hfun : circuitFun n D = graphFun G ∅ := by
    apply graph_correct_of_local G C D hlen hout hLeast.1.2.1 hAO hLeast.2.1
    · intro x hx j hj
      let jf : Fin C.gates.length := ⟨j, hj⟩
      by_cases h : Selected jf
      · have hold : W n C (n + j) x = false := by
          cases hv : W n C (n + j) x
          · rfl
          · have := h.2 x hv
            rw [hx] at this
            cases this
        have hnew : (x (u ⟨jf, h⟩) && W n C (w ⟨jf, h⟩) x) = false := by
          cases hv : (x (u ⟨jf, h⟩) && W n C (w ⟨jf, h⟩) x)
          · rfl
          · have := hclean ⟨jf, h⟩ x hv
            rw [hx] at this
            cases this
        rw [heval ⟨jf, h⟩ x, hnew, ← value_gate C hLeast.1.2.1 x j hj]
        exact hold.symm
      · rw [hunselected jf h]
    · intro a b hab j hj
      let jf : Fin C.gates.length := ⟨j, hj⟩
      by_cases h : Selected jf
      · rw [heval ⟨jf, h⟩ (pairInput a b), ← value_gate C hLeast.1.2.1 (pairInput a b) j hj]
        change W n C (n + j) (pairInput a b) ≤ _
        cases hv : W n C (n + j) (pairInput a b)
        · exact Bool.false_le _
        · rw [hkeep ⟨jf, h⟩ a b hab hv]
      · rw [hunselected jf h]
  have hstable : ∀ x : Fin n → Bool, ∀ z, ¬ Clean z → W n D z x = W n C z x := by
    apply preserve_closed_wires C D hlen hLeast.1.2.1 hAO.2.1 (fun z => ¬ Clean z)
    · intro j hj hz
      apply hunselected ⟨j, hj⟩
      exact fun h => hz h.2
    · intro j hj hz i hi
      exact PureTopAux.nonclean_gate_children G s hbip C hLeast hOR j hj hz i hi
  have hfilter (t : T) : W n D (w t) = W n C (w t) := by
    funext x
    apply hstable x (w t)
    intro hc
    exact clean_not_pure G s hbip C hLeast.1 (w t) (by have := hback t; omega) hc (hpure t)
  refine ⟨D, ⟨hAO, hfun, ?_⟩, hsize, hlen, hout, ?_, ?_⟩
  · intro E hE hEf
    rw [hsize]
    exact hLeast.2.2 E hE hEf
  · intro z hz
    funext x
    exact hstable x z hz
  · intro j hjD hop hc
    have hj : j < C.gates.length := by omega
    let jf : Fin C.gates.length := ⟨j, hj⟩
    have hs : Selected jf := by
      by_contra h
      have hopC : (gateAt C j).op = .and := by rw [← hunselected jf h]; exact hop
      have hd : ¬ Clean (n + j) := fun hcl => h ⟨hopC, hcl⟩
      apply hd
      intro x hx
      apply hc x
      rw [hstable x (n + j) hd]
      exact hx
    let t : T := ⟨jf, hs⟩
    refine ⟨u t, w t, hback t, hselected jf hs, ?_, ?_⟩
    · rw [hfilter t]
      exact pure_star_opposite_color G s hbip C hLeast.1 (u t) (w t)
        (by have := hback t; omega) (hpure t) (hclean t)
    · rw [hfilter t]
      exact hclean t

end PEqualNP.Outside.L_meta_3566.PureTopNormalize


namespace PEqualNP.Outside.L_meta_3566.TwoProductFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership PureFunctionFamily

def PureSides {n k : ℕ} (s : Fin n → Bool)
    (L R : Fin k → (Fin n → Bool) → Bool) : Prop :=
  (∀ i, Monotone (L i)) ∧
  (∀ i, Monotone (R i)) ∧
  (∀ i x, L i x = L i (maskTrue (fun v => !(s v)) x)) ∧
  (∀ i x, R i x = R i (maskTrue s x)) ∧
  (∀ i, L i (fun _ => false) = false) ∧
  (∀ i, R i (fun _ => false) = false)

namespace PureSides
variable {n k : ℕ} {s : Fin n → Bool} {L R : Fin k → (Fin n → Bool) → Bool}

lemma leftMono (h : PureSides s L R) : ∀ i, Monotone (L i) := h.1
lemma rightMono (h : PureSides s L R) : ∀ i, Monotone (R i) := h.2.1
lemma leftPure (h : PureSides s L R) :
    ∀ i x, L i x = L i (maskTrue (fun v => !(s v)) x) := h.2.2.1
lemma rightPure (h : PureSides s L R) :
    ∀ i x, R i x = R i (maskTrue s x) := h.2.2.2.1
lemma leftZero (h : PureSides s L R) : ∀ i, L i (fun _ => false) = false := h.2.2.2.2.1
lemma rightZero (h : PureSides s L R) : ∀ i, R i (fun _ => false) = false := h.2.2.2.2.2

end PureSides

def Member {n k : ℕ} (L R : Fin k → (Fin n → Bool) → Bool)
    (f : (Fin n → Bool) → Bool) : Prop := ∃ i, f = L i ∨ f = R i

lemma all_addCases {α : Sort*} {k p : ℕ} (L : Fin k → α) (P : Fin p → α)
    (Q : α → Prop) (hL : ∀ i, Q (L i)) (hP : ∀ i, Q (P i)) :
    ∀ i, Q (Fin.addCases L P i) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa using hL j
  · intro j
    simpa using hP j

lemma PureSides.append {n k p : ℕ} {s : Fin n → Bool}
    {L R : Fin k → (Fin n → Bool) → Bool} {P Q : Fin p → (Fin n → Bool) → Bool}
    (hL : PureSides s L R) (hP : PureSides s P Q) :
    PureSides s (Fin.addCases L P) (Fin.addCases R Q) := by
  exact ⟨all_addCases L P _ hL.leftMono hP.leftMono,
    all_addCases R Q _ hL.rightMono hP.rightMono,
    all_addCases L P (fun f => ∀ x, f x = f (maskTrue (fun v => !(s v)) x)) hL.leftPure hP.leftPure,
    all_addCases R Q (fun f => ∀ x, f x = f (maskTrue s x)) hL.rightPure hP.rightPure,
    all_addCases L P (fun f => f (fun _ => false) = false) hL.leftZero hP.leftZero,
    all_addCases R Q (fun f => f (fun _ => false) = false) hL.rightZero hP.rightZero⟩

lemma family_add_true {n k p : ℕ}
    (L R : Fin k → (Fin n → Bool) → Bool) (P Q : Fin p → (Fin n → Bool) → Bool)
    (x : Fin n → Bool) :
    family (Fin.addCases L P) (Fin.addCases R Q) x = true ↔
      family L R x = true ∧ family P Q x = true := by
  constructor
  · intro h
    have hh := of_decide_eq_true h
    constructor
    · apply decide_eq_true
      intro i
      simpa using hh (Fin.castAdd p i)
    · apply decide_eq_true
      intro i
      simpa using hh (Fin.natAdd k i)
  · rintro ⟨hL, hP⟩
    have hhL := of_decide_eq_true hL
    have hhP := of_decide_eq_true hP
    apply decide_eq_true
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using hhL j
    · intro j
      simpa using hhP j

lemma member_add {n k p : ℕ}
    (L R : Fin k → (Fin n → Bool) → Bool) (P Q : Fin p → (Fin n → Bool) → Bool)
    (f : (Fin n → Bool) → Bool) :
    Member (Fin.addCases L P) (Fin.addCases R Q) f → Member L R f ∨ Member P Q f := by
  rintro ⟨i, hi⟩
  have hh : ∀ j, (f = Fin.addCases L P j ∨ f = Fin.addCases R Q j) →
      Member L R f ∨ Member P Q f := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro t ht
      exact Or.inl ⟨t, by simpa using ht⟩
    · intro t ht
      exact Or.inr ⟨t, by simpa using ht⟩
  exact hh i hi

lemma select_conjunction {n k p : ℕ} (hkp : 0 < k + p)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (L R : Fin k → (Fin n → Bool) → Bool) (P Q : Fin p → (Fin n → Bool) → Bool)
    (hL : PureSides s L R) (hP : PureSides s P Q)
    (hbelow : ∀ x, family L R x = true → family P Q x = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧ family L R (pairInput a b) = true ∧
      family P Q (pairInput a b) = true) :
    ∃ (u : Fin n) (f : (Fin n → Bool) → Bool),
      (Member L R f ∨ Member P Q f) ∧
      (∀ x, (x u && f x) = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → family L R (pairInput a b) = true →
        family P Q (pairInput a b) = true → (pairInput a b u && f (pairInput a b)) = true) := by
  let L' : Fin (k + p) → (Fin n → Bool) → Bool := Fin.addCases L P
  let R' : Fin (k + p) → (Fin n → Bool) → Bool := Fin.addCases R Q
  have hjoined := hL.append hP
  have hbelow' : ∀ x, family L' R' x = true → graphFun G ∅ x = true := by
    intro x hx
    obtain ⟨hl, hp⟩ := (family_add_true L R P Q x).mp hx
    exact hbelow x hl hp
  have haccept' : ∃ a b, G.Adj a b ∧ family L' R' (pairInput a b) = true := by
    obtain ⟨a, b, hab, hl, hp⟩ := haccept
    exact ⟨a, b, hab, (family_add_true L R P Q _).mpr ⟨hl, hp⟩⟩
  obtain ⟨u, i, f, hf, hclean, hkeep⟩ := replacement_existing_side hkp G s hbip h4 L' R'
    hjoined.leftMono hjoined.rightMono hjoined.leftPure hjoined.rightPure
    hjoined.leftZero hjoined.rightZero hbelow' haccept'
  refine ⟨u, f, member_add L R P Q f ⟨i, hf⟩, ?_, ?_⟩
  · simpa using hclean
  · intro a b hab hl hp
    simpa using hkeep a b hab ((family_add_true L R P Q _).mpr ⟨hl, hp⟩)

def HasStar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : (Fin n → Bool) → Bool) (Allowed : ((Fin n → Bool) → Bool) → Prop) : Prop :=
  ∃ (u : Fin n) (f : (Fin n → Bool) → Bool), Allowed f ∧
    (∀ x, (x u && f x) = true → graphFun G ∅ x = true) ∧
    (∀ a b, G.Adj a b → T (pairInput a b) = true →
      (pairInput a b u && f (pairInput a b)) = true)

lemma select_disjunction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T U : (Fin n → Bool) → Bool) (Allowed : ((Fin n → Bool) → Bool) → Prop)
    (hT : (∃ a b, G.Adj a b ∧ T (pairInput a b) = true) → HasStar G T Allowed)
    (hU : (∃ a b, G.Adj a b ∧ U (pairInput a b) = true) → HasStar G U Allowed)
    (haccept : ∃ a b, G.Adj a b ∧ (T (pairInput a b) || U (pairInput a b)) = true) :
    ∃ (u v : Fin n) (f g : (Fin n → Bool) → Bool), Allowed f ∧ Allowed g ∧
      (∀ x, ((x u && f x) || (x v && g x)) = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → (T (pairInput a b) || U (pairInput a b)) = true →
        ((pairInput a b u && f (pairInput a b)) ||
          (pairInput a b v && g (pairInput a b))) = true) := by
  classical
  by_cases ht : ∃ a b, G.Adj a b ∧ T (pairInput a b) = true
  · obtain ⟨u, f, hf, hfc, hfr⟩ := hT ht
    by_cases hu : ∃ a b, G.Adj a b ∧ U (pairInput a b) = true
    · obtain ⟨v, g, hg, hgc, hgr⟩ := hU hu
      refine ⟨u, v, f, g, hf, hg, ?_, ?_⟩
      · intro x hx
        have hx' : (x u && f x) = true ∨ (x v && g x) = true := by simpa using hx
        exact hx'.elim (hfc x) (hgc x)
      · intro a b hab hx
        have hx' : T (pairInput a b) = true ∨ U (pairInput a b) = true := by simpa using hx
        rcases hx' with ht | hu
        · simp only [Bool.or_eq_true]
          exact Or.inl (hfr a b hab ht)
        · simp only [Bool.or_eq_true]
          exact Or.inr (hgr a b hab hu)
    · refine ⟨u, u, f, f, hf, hf, ?_, ?_⟩
      · intro x hx
        exact hfc x (by simpa using hx)
      · intro a b hab hx
        have hx' : T (pairInput a b) = true ∨ U (pairInput a b) = true := by simpa using hx
        rcases hx' with ht' | hu'
        · simpa using hfr a b hab ht'
        · exact False.elim (hu ⟨a, b, hab, hu'⟩)
  · have hu : ∃ a b, G.Adj a b ∧ U (pairInput a b) = true := by
      obtain ⟨a, b, hab, hx⟩ := haccept
      have hx' : T (pairInput a b) = true ∨ U (pairInput a b) = true := by simpa using hx
      rcases hx' with ht' | hu'
      · exact False.elim (ht ⟨a, b, hab, ht'⟩)
      · exact ⟨a, b, hab, hu'⟩
    obtain ⟨v, g, hg, hgc, hgr⟩ := hU hu
    refine ⟨v, v, g, g, hg, hg, ?_, ?_⟩
    · intro x hx
      exact hgc x (by simpa using hx)
    · intro a b hab hx
      have hx' : T (pairInput a b) = true ∨ U (pairInput a b) = true := by simpa using hx
      rcases hx' with ht' | hu'
      · exact False.elim (ht ⟨a, b, hab, ht'⟩)
      · simpa using hgr a b hab hu'

lemma select_two_products {n k p q : ℕ} (hkp : 0 < k + p) (hkq : 0 < k + q)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (HL HR : Fin k → (Fin n → Bool) → Bool)
    (PL PR : Fin p → (Fin n → Bool) → Bool)
    (QL QR : Fin q → (Fin n → Bool) → Bool)
    (hH : PureSides s HL HR) (hP : PureSides s PL PR) (hQ : PureSides s QL QR)
    (hbelow : ∀ x, (family HL HR x && (family PL PR x || family QL QR x)) = true →
      graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧
      (family HL HR (pairInput a b) &&
        (family PL PR (pairInput a b) || family QL QR (pairInput a b))) = true) :
    ∃ (u v : Fin n) (f g : (Fin n → Bool) → Bool),
      (Member HL HR f ∨ Member PL PR f ∨ Member QL QR f) ∧
      (Member HL HR g ∨ Member PL PR g ∨ Member QL QR g) ∧
      (∀ x, ((x u && f x) || (x v && g x)) = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b →
        (family HL HR (pairInput a b) &&
          (family PL PR (pairInput a b) || family QL QR (pairInput a b))) = true →
        ((pairInput a b u && f (pairInput a b)) ||
          (pairInput a b v && g (pairInput a b))) = true) := by
  let Allowed : ((Fin n → Bool) → Bool) → Prop := fun f =>
    Member HL HR f ∨ Member PL PR f ∨ Member QL QR f
  let T : (Fin n → Bool) → Bool := fun x => family HL HR x && family PL PR x
  let U : (Fin n → Bool) → Bool := fun x => family HL HR x && family QL QR x
  have hdist : ∀ x, (family HL HR x && (family PL PR x || family QL QR x)) = (T x || U x) := by
    intro x
    cases hh : family HL HR x <;> simp [T, U, hh]
  have hT : (∃ a b, G.Adj a b ∧ T (pairInput a b) = true) → HasStar G T Allowed := by
    intro ht
    have hb : ∀ x, family HL HR x = true → family PL PR x = true → graphFun G ∅ x = true := by
      intro x hh hp
      exact hbelow x (by simp [hh, hp])
    have ha : ∃ a b, G.Adj a b ∧ family HL HR (pairInput a b) = true ∧
        family PL PR (pairInput a b) = true := by
      simpa [T] using ht
    obtain ⟨u, f, hf, hfc, hfr⟩ := select_conjunction hkp G s hbip h4 HL HR PL PR hH hP hb ha
    refine ⟨u, f, ?_, hfc, ?_⟩
    · exact hf.elim Or.inl (fun h => Or.inr (Or.inl h))
    · intro a b hab hx
      have hx' : family HL HR (pairInput a b) = true ∧ family PL PR (pairInput a b) = true := by
        simpa [T] using hx
      exact hfr a b hab hx'.1 hx'.2
  have hU : (∃ a b, G.Adj a b ∧ U (pairInput a b) = true) → HasStar G U Allowed := by
    intro hu
    have hb : ∀ x, family HL HR x = true → family QL QR x = true → graphFun G ∅ x = true := by
      intro x hh hq
      exact hbelow x (by simp [hh, hq])
    have ha : ∃ a b, G.Adj a b ∧ family HL HR (pairInput a b) = true ∧
        family QL QR (pairInput a b) = true := by
      simpa [U] using hu
    obtain ⟨v, g, hg, hgc, hgr⟩ := select_conjunction hkq G s hbip h4 HL HR QL QR hH hQ hb ha
    refine ⟨v, g, ?_, hgc, ?_⟩
    · exact hg.elim Or.inl (fun h => Or.inr (Or.inr h))
    · intro a b hab hx
      have hx' : family HL HR (pairInput a b) = true ∧ family QL QR (pairInput a b) = true := by
        simpa [U] using hx
      exact hgr a b hab hx'.1 hx'.2
  have ha : ∃ a b, G.Adj a b ∧ (T (pairInput a b) || U (pairInput a b)) = true := by
    simpa only [hdist] using haccept
  obtain ⟨u, v, f, g, hf, hg, hclean, hkeep⟩ := select_disjunction G T U Allowed hT hU ha
  refine ⟨u, v, f, g, hf, hg, hclean, ?_⟩
  intro a b hab hx
  exact hkeep a b hab (by simpa only [hdist] using hx)

end PEqualNP.Outside.L_meta_3566.TwoProductFrontier

namespace PEqualNP.Outside.L_meta_3566.PrivateProducts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PrivateBlock PureFunctionFamily TwoProductFrontier

lemma least_private_two_products_short {n k p q : ℕ} (hkp : 0 < k + p) (hkq : 0 < k + q)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre old post : List Gate) (output : ℕ)
    (hLeast : IsLeastAO G (circuit pre old post output)) (r : ℕ) (hlen : old.length = 3 + r)
    (hreads : ∀ g ∈ post, ∀ i ∈ g.inputs, i ∉ interior n pre old)
    (hout : output ∉ interior n pre old)
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (HL HR : Fin k → (Fin n → Bool) → Bool)
    (PL PR : Fin p → (Fin n → Bool) → Bool)
    (QL QR : Fin q → (Fin n → Bool) → Bool)
    (hH : PureSides s HL HR) (hP : PureSides s PL PR) (hQ : PureSides s QL QR)
    (hwire : ∀ f : (Fin n → Bool) → Bool,
      (Member HL HR f ∨ Member PL PR f ∨ Member QL QR f) →
        ∃ w < n + pre.length, prefixFun pre w = f)
    (hold : ∀ x : Fin n → Bool, blockValue pre old x =
      (family HL HR x && (family PL PR x || family QL QR x)))
    (hbelow : ∀ x : Fin n → Bool, blockValue pre old x = true → graphFun G ∅ x = true)
    (haccept : ∃ a b, G.Adj a b ∧ blockValue pre old (pairInput a b) = true) : r = 0 := by
  have hbelow' : ∀ x, (family HL HR x && (family PL PR x || family QL QR x)) = true →
      graphFun G ∅ x = true := by
    intro x hx
    exact hbelow x (by simpa only [hold] using hx)
  have haccept' : ∃ a b, G.Adj a b ∧
      (family HL HR (pairInput a b) &&
        (family PL PR (pairInput a b) || family QL QR (pairInput a b))) = true := by
    simpa only [hold] using haccept
  obtain ⟨u, v, f, g, hf, hg, hclean, hkeep⟩ :=
    select_two_products hkp hkq G s hbip h4 HL HR PL PR QL QR hH hP hQ hbelow' haccept'
  obtain ⟨w, hw, hwf⟩ := hwire f hf
  obtain ⟨t, ht, htg⟩ := hwire g hg
  apply PaddedStars.least_private_block_short G pre old post output hLeast r hlen hreads hout u v w t hw ht
  · intro a b hab hx
    rw [hold] at hx
    simpa only [starFun, hwf, htg] using hkeep a b hab hx
  · intro x hx
    apply hclean x
    simpa only [starFun, hwf, htg] using hx

end PEqualNP.Outside.L_meta_3566.PrivateProducts

namespace PEqualNP.Outside.L_meta_3566.GraphFactor

open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma edges_intersection {n : ℕ} (G A B : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel A.Adj] [DecidableRel B.Adj]
    (hfun : ∀ x, graphFun G ∅ x = (graphFun A ∅ x && graphFun B ∅ x)) (u v : Fin n) :
    G.Adj u v ↔ A.Adj u v ∧ B.Adj u v := by
  rw [← MixedColor.graphFun_pair G u v, hfun, Bool.and_eq_true,
    MixedColor.graphFun_pair A u v, MixedColor.graphFun_pair B u v]

lemma exclusive_cross {n : ℕ} (G A B : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel A.Adj] [DecidableRel B.Adj]
    (hfun : ∀ x, graphFun G ∅ x = (graphFun A ∅ x && graphFun B ∅ x))
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (a b c d : Fin n) (ha : s a = false) (hb : s b = true)
    (hc : s c = false) (hd : s d = true)
    (hab : A.Adj a b) (hnotab : ¬ B.Adj a b)
    (hcd : B.Adj c d) (hnotcd : ¬ A.Adj c d) :
    G.Adj a d ∨ G.Adj c b := by
  classical
  let L : Finset (Fin n) := {a, c}
  let R : Finset (Fin n) := {b, d}
  let x := RectangleFamily.setInput (L ∪ R)
  have hxA : graphFun A ∅ x = true := by
    apply (RectangleFamily.graph_true A x).2
    exact ⟨a, b, hab, by simp [x, RectangleFamily.setInput, L, R],
      by simp [x, RectangleFamily.setInput, L, R]⟩
  have hxB : graphFun B ∅ x = true := by
    apply (RectangleFamily.graph_true B x).2
    exact ⟨c, d, hcd, by simp [x, RectangleFamily.setInput, L, R],
      by simp [x, RectangleFamily.setInput, L, R]⟩
  have hxG : graphFun G ∅ x = true := by rw [hfun, hxA, hxB]; rfl
  have hL : ∀ u ∈ L, s u = false := by
    intro u hu
    simp only [L, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl <;> assumption
  have hR : ∀ v ∈ R, s v = true := by
    intro v hv
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  obtain ⟨u, hu, v, hv, huv⟩ := RectangleFamily.edge_of_two_colors G s hbip L R hL hR hxG
  simp only [L, Finset.mem_insert, Finset.mem_singleton] at hu
  simp only [R, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (hnotab ((edges_intersection G A B hfun _ _).mp huv).2).elim
  · exact Or.inl huv
  · exact Or.inr huv
  · exact (hnotcd ((edges_intersection G A B hfun _ _).mp huv).1).elim

lemma exclusive_endpoints_distinct {n : ℕ} (G A B : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel A.Adj] [DecidableRel B.Adj]
    (hfun : ∀ x, graphFun G ∅ x = (graphFun A ∅ x && graphFun B ∅ x))
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (a b c d : Fin n) (ha : s a = false) (hb : s b = true)
    (hc : s c = false) (hd : s d = true)
    (hab : A.Adj a b) (hnotab : ¬ B.Adj a b)
    (hcd : B.Adj c d) (hnotcd : ¬ A.Adj c d) :
    a ≠ c ∧ b ≠ d ∧ a ≠ d ∧ b ≠ c := by
  have he := exclusive_cross G A B hfun s hbip a b c d ha hb hc hd hab hnotab hcd hnotcd
  have hG_ab : ¬ G.Adj a b := fun h => hnotab ((edges_intersection G A B hfun a b).mp h).2
  have hG_cd : ¬ G.Adj c d := fun h => hnotcd ((edges_intersection G A B hfun c d).mp h).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro heq
    subst c
    exact he.elim hG_cd hG_ab
  · intro heq
    subst d
    exact he.elim hG_ab hG_cd
  · intro heq
    subst d
    rw [ha] at hd
    cases hd
  · intro heq
    subst c
    rw [hb] at hc
    cases hc

end PEqualNP.Outside.L_meta_3566.GraphFactor

namespace PEqualNP.Outside.L_meta_3566.RankTwoLocal

def both (A B : Fin 4 → Fin 4 → Bool) (i j : Fin 4) : Bool := A i j && B i j

lemma both_true {A B : Fin 4 → Fin 4 → Bool} {i j : Fin 4}
    (h : A i j = true ∧ B i j = true) : both A B i j = true := by
  simp only [both, h.1, h.2]
  rfl

def NoRectangle (G : Fin 4 → Fin 4 → Bool) : Prop :=
  ∀ a b c d, a ≠ c → b ≠ d →
    ¬ (G a b = true ∧ G a d = true ∧ G c b = true ∧ G c d = true)

def RowSeparate (A B : Fin 4 → Fin 4 → Bool) : Prop :=
  ∀ i j k, A i j = true → B i j = false → A i k = false → B i k = true → False

def ColSeparate (A B : Fin 4 → Fin 4 → Bool) : Prop :=
  ∀ i j k, A i j = true → B i j = false → A k j = false → B k j = true → False

lemma oriented_impossible (A B : Fin 4 → Fin 4 → Bool)
    (hd : ∀ i, A i i = true ∧ B i i = true)
    (ha01 : A 0 1 = true) (ha10 : A 1 0 = true) (ha23 : A 2 3 = true)
    (hb02 : B 0 2 = true) (hb20 : B 2 0 = true)
    (hb13 : B 1 3 = true) (hb31 : B 3 1 = true)
    (hs : A 0 2 = true → A 0 3 = true ∨ A 1 2 = true)
    (h4 : NoRectangle (both A B)) (hr : RowSeparate A B) (hc : ColSeparate A B)
    (hb01 : B 0 1 = false) : False := by
  have gd : ∀ i, both A B i i = true := fun i => both_true (hd i)
  have ha02 : A 0 2 = true := by
    cases h : A 0 2 with
    | false => exact (hr 0 1 2 ha01 hb01 h hb02).elim
    | true => rfl
  have ha31 : A 3 1 = true := by
    cases h : A 3 1 with
    | false => exact (hc 0 1 3 ha01 hb01 h hb31).elim
    | true => rfl
  have g02 : both A B 0 2 = true := both_true ⟨ha02, hb02⟩
  have g31 : both A B 3 1 = true := both_true ⟨ha31, hb31⟩
  have ha20 : A 2 0 = false := by
    cases h : A 2 0 with
    | false => rfl
    | true =>
      exact (h4 0 0 2 2 (by decide) (by decide)
        ⟨gd 0, g02, both_true ⟨h, hb20⟩, gd 2⟩).elim
  have ha13 : A 1 3 = false := by
    cases h : A 1 3 with
    | false => rfl
    | true =>
      exact (h4 1 1 3 3 (by decide) (by decide)
        ⟨gd 1, both_true ⟨h, hb13⟩, g31, gd 3⟩).elim
  have hb10 : B 1 0 = true := by
    cases h : B 1 0 with
    | false => exact (hr 1 0 3 ha10 h ha13 hb13).elim
    | true => rfl
  have hb23 : B 2 3 = true := by
    cases h : B 2 3 with
    | false => exact (hr 2 3 0 ha23 h ha20 hb20).elim
    | true => rfl
  have g10 : both A B 1 0 = true := both_true ⟨ha10, hb10⟩
  have g23 : both A B 2 3 = true := both_true ⟨ha23, hb23⟩
  have ng03 : both A B 0 3 ≠ true := by
    intro h
    exact h4 0 2 2 3 (by decide) (by decide) ⟨g02, h, gd 2, g23⟩
  have ng12 : both A B 1 2 ≠ true := by
    intro h
    exact h4 0 0 1 2 (by decide) (by decide) ⟨gd 0, g02, g10, h⟩
  have ha03 : A 0 3 = false := by
    cases ha : A 0 3 with
    | false => rfl
    | true =>
      cases hb : B 0 3 with
      | false => exact (hc 0 3 1 ha hb ha13 hb13).elim
      | true => exact (ng03 (both_true ⟨ha, hb⟩)).elim
  have ha12 : A 1 2 = false := by
    cases ha : A 1 2 with
    | false => rfl
    | true =>
      cases hb : B 1 2 with
      | false => exact (hr 1 2 3 ha hb ha13 hb13).elim
      | true => exact (ng12 (both_true ⟨ha, hb⟩)).elim
  rcases hs ha02 with h | h
  · rw [ha03] at h
    cases h
  · rw [ha12] at h
    cases h

def flip : Fin 4 → Fin 4 := ![1, 0, 3, 2]

lemma flip_injective : Function.Injective flip := by decide

lemma impossible (A B : Fin 4 → Fin 4 → Bool)
    (hd : ∀ i, A i i = true ∧ B i i = true)
    (ha01 : A 0 1 = true) (ha10 : A 1 0 = true)
    (ha23 : A 2 3 = true) (ha32 : A 3 2 = true)
    (hb02 : B 0 2 = true) (hb20 : B 2 0 = true)
    (hb13 : B 1 3 = true) (hb31 : B 3 1 = true)
    (hs0 : A 0 2 = true → A 0 3 = true ∨ A 1 2 = true)
    (hs1 : A 1 3 = true → A 1 2 = true ∨ A 0 3 = true)
    (h4 : NoRectangle (both A B)) (hr : RowSeparate A B) (hc : ColSeparate A B) : False := by
  by_cases hb01 : B 0 1 = false
  · exact oriented_impossible A B hd ha01 ha10 ha23 hb02 hb20 hb13 hb31 hs0 h4 hr hc hb01
  have hb01t : B 0 1 = true := Bool.eq_true_of_not_eq_false hb01
  have hb10 : B 1 0 = false := by
    cases h : B 1 0 with
    | false => rfl
    | true =>
      exact (h4 0 0 1 1 (by decide) (by decide)
        ⟨both_true (hd 0), both_true ⟨ha01, hb01t⟩,
          both_true ⟨ha10, h⟩, both_true (hd 1)⟩).elim
  let A' : Fin 4 → Fin 4 → Bool := fun i j => A (flip i) (flip j)
  let B' : Fin 4 → Fin 4 → Bool := fun i j => B (flip i) (flip j)
  apply oriented_impossible A' B' (fun i => hd (flip i)) ha10 ha01 ha32 hb13 hb31 hb02 hb20
    hs1 _ _ _ hb10
  · intro a b c d hac hbd
    exact h4 (flip a) (flip b) (flip c) (flip d)
      (fun h => hac (flip_injective h)) (fun h => hbd (flip_injective h))
  · intro i j k
    exact hr (flip i) (flip j) (flip k)
  · intro i j k
    exact hc (flip i) (flip j) (flip k)

def sideA : Fin 4 → Bool := ![false, false, true, true]

def sideB : Fin 4 → Bool := ![false, true, false, true]

def matrix (side extraL extraR : Fin 4 → Bool) (i j : Fin 4) : Bool :=
  (side i == side j) || extraL i || extraR j

lemma two_by_two_matrix_impossible (x y u v : Fin 4 → Bool)
    (h4 : NoRectangle (both (matrix sideA x y) (matrix sideB u v)))
    (hr : RowSeparate (matrix sideA x y) (matrix sideB u v))
    (hc : ColSeparate (matrix sideA x y) (matrix sideB u v)) : False := by
  have hd : ∀ i, matrix sideA x y i i = true ∧ matrix sideB u v i i = true := by
    intro i
    simp [matrix]
  have hs0 : matrix sideA x y 0 2 = true →
      matrix sideA x y 0 3 = true ∨ matrix sideA x y 1 2 = true := by
    intro h
    have h' : x 0 = true ∨ y 2 = true := by simpa [matrix, sideA] using h
    rcases h' with hx | hy
    · exact Or.inl (by simp [matrix, sideA, hx])
    · exact Or.inr (by simp [matrix, sideA, hy])
  have hs1 : matrix sideA x y 1 3 = true →
      matrix sideA x y 1 2 = true ∨ matrix sideA x y 0 3 = true := by
    intro h
    have h' : x 1 = true ∨ y 3 = true := by simpa [matrix, sideA] using h
    rcases h' with hx | hy
    · exact Or.inl (by simp [matrix, sideA, hx])
    · exact Or.inr (by simp [matrix, sideA, hy])
  exact impossible (matrix sideA x y) (matrix sideB u v) hd
    (by simp [matrix, sideA]) (by simp [matrix, sideA])
    (by simp [matrix, sideA]) (by simp [matrix, sideA])
    (by simp [matrix, sideB]) (by simp [matrix, sideB])
    (by simp [matrix, sideB]) (by simp [matrix, sideB]) hs0 hs1 h4 hr hc

end PEqualNP.Outside.L_meta_3566.RankTwoLocal

namespace PEqualNP.Outside.L_meta_3566.RankTwoLocal

def rectangleMatrix (L R : Bool → Fin 4 → Bool) (i j : Fin 4) : Bool :=
  (L false i && R false j) || (L true i && R true j)

lemma rectangleMatrix_eq (L R : Bool → Fin 4 → Bool) (side : Fin 4 → Bool)
    (hside : ∀ i, L (side i) i = true ∧ R (side i) i = true) :
    rectangleMatrix L R = matrix side (fun i => L (!(side i)) i) (fun i => R (!(side i)) i) := by
  funext i j
  have hi := hside i
  have hj := hside j
  cases hsi : side i <;> cases hsj : side j <;>
    simp_all [rectangleMatrix, matrix, Bool.or_comm]

lemma labelled_rectangles_impossible
    (LA RA LB RB : Bool → Fin 4 → Bool)
    (ha : ∀ i, LA (sideA i) i = true ∧ RA (sideA i) i = true)
    (hb : ∀ i, LB (sideB i) i = true ∧ RB (sideB i) i = true)
    (h4 : NoRectangle (both (rectangleMatrix LA RA) (rectangleMatrix LB RB)))
    (hr : RowSeparate (rectangleMatrix LA RA) (rectangleMatrix LB RB))
    (hc : ColSeparate (rectangleMatrix LA RA) (rectangleMatrix LB RB)) : False := by
  rw [rectangleMatrix_eq LA RA sideA ha, rectangleMatrix_eq LB RB sideB hb] at h4 hr hc
  exact two_by_two_matrix_impossible _ _ _ _ h4 hr hc

end PEqualNP.Outside.L_meta_3566.RankTwoLocal

namespace PEqualNP.Outside.L_meta_3566.RankTwoFactor

open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership RankTwoLocal

def label (a b : Bool) : Fin 4 := if a then (if b then 3 else 2) else (if b then 1 else 0)

lemma label_left (a b : Bool) : sideA (label a b) = a := by cases a <;> cases b <;> rfl

lemma label_right (a b : Bool) : sideB (label a b) = b := by cases a <;> cases b <;> rfl

lemma no_rectangle {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (a b c d : Fin n) (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G.Adj a b) (had : G.Adj a d) (hcb : G.Adj c b) (hcd : G.Adj c d) : False := by
  have hc : 1 < (Finset.univ.filter (fun v => G.Adj a v ∧ G.Adj c v)).card := by
    apply Finset.one_lt_card.mpr
    exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hab, hcb⟩,
      d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, had, hcd⟩, hbd⟩
  have hsmall := h4 a c hac
  omega

lemma matching_four_impossible {n : ℕ} (G A B : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel A.Adj] [DecidableRel B.Adj]
    (s : Fin n → Bool) (hbip : ∀ x y, G.Adj x y → s x ≠ s y) (h4 : NoFourCycle G)
    (hfun : ∀ x, graphFun G ∅ x = (graphFun A ∅ x && graphFun B ∅ x))
    (LA RA LB RB : Bool → Finset (Fin n))
    (hA : ∀ x y, s x = false → s y = true →
      (A.Adj x y ↔ ∃ q, x ∈ LA q ∧ y ∈ RA q))
    (hB : ∀ x y, s x = false → s y = true →
      (B.Adj x y ↔ ∃ q, x ∈ LB q ∧ y ∈ RB q))
    (a b : Fin 4 → Fin n) (ha : Function.Injective a) (hb : Function.Injective b)
    (haColor : ∀ i, s (a i) = false) (hbColor : ∀ i, s (b i) = true)
    (hmatch : ∀ i, G.Adj (a i) (b i)) : False := by
  classical
  have hexA : ∀ i, ∃ q, a i ∈ LA q ∧ b i ∈ RA q := by
    intro i
    exact (hA _ _ (haColor i) (hbColor i)).mp ((GraphFactor.edges_intersection G A B hfun _ _).mp (hmatch i)).1
  have hexB : ∀ i, ∃ q, a i ∈ LB q ∧ b i ∈ RB q := by
    intro i
    exact (hB _ _ (haColor i) (hbColor i)).mp ((GraphFactor.edges_intersection G A B hfun _ _).mp (hmatch i)).2
  choose qa hqa using hexA
  choose qb hqb using hexB
  let code : Fin 4 → Fin 4 := fun i => label (qa i) (qb i)
  have hcode : Function.Injective code := by
    intro i j he
    by_contra hij
    have heA : qa i = qa j := by simpa only [code, label_left] using congrArg sideA he
    have heB : qb i = qb j := by simpa only [code, label_right] using congrArg sideB he
    have hacross : A.Adj (a i) (b j) := (hA _ _ (haColor i) (hbColor j)).mpr
      ⟨qa i, (hqa i).1, by rw [heA]; exact (hqa j).2⟩
    have hbcross : B.Adj (a i) (b j) := (hB _ _ (haColor i) (hbColor j)).mpr
      ⟨qb i, (hqb i).1, by rw [heB]; exact (hqb j).2⟩
    have hacross' : A.Adj (a j) (b i) := (hA _ _ (haColor j) (hbColor i)).mpr
      ⟨qa j, (hqa j).1, by rw [← heA]; exact (hqa i).2⟩
    have hbcross' : B.Adj (a j) (b i) := (hB _ _ (haColor j) (hbColor i)).mpr
      ⟨qb j, (hqb j).1, by rw [← heB]; exact (hqb i).2⟩
    have gij := (GraphFactor.edges_intersection G A B hfun _ _).mpr ⟨hacross, hbcross⟩
    have gji := (GraphFactor.edges_intersection G A B hfun _ _).mpr ⟨hacross', hbcross'⟩
    exact no_rectangle G h4 (a i) (b i) (a j) (b j)
      (fun h => hij (ha h)) (fun h => hij (hb h)) (hmatch i) gij gji (hmatch j)
  let e : Fin 4 ≃ Fin 4 := Equiv.ofBijective code ⟨hcode, Finite.surjective_of_injective hcode⟩
  let aa : Fin 4 → Fin n := fun i => a (e.symm i)
  let bb : Fin 4 → Fin n := fun i => b (e.symm i)
  have haa : Function.Injective aa := ha.comp e.symm.injective
  have hbb : Function.Injective bb := hb.comp e.symm.injective
  have hac : ∀ i, s (aa i) = false := fun i => haColor (e.symm i)
  have hbc : ∀ i, s (bb i) = true := fun i => hbColor (e.symm i)
  let LA' : Bool → Fin 4 → Bool := fun q i => decide (aa i ∈ LA q)
  let RA' : Bool → Fin 4 → Bool := fun q i => decide (bb i ∈ RA q)
  let LB' : Bool → Fin 4 → Bool := fun q i => decide (aa i ∈ LB q)
  let RB' : Bool → Fin 4 → Bool := fun q i => decide (bb i ∈ RB q)
  have hmA : ∀ i, LA' (sideA i) i = true ∧ RA' (sideA i) i = true := by
    intro i
    have he : label (qa (e.symm i)) (qb (e.symm i)) = i := e.apply_symm_apply i
    have heA : qa (e.symm i) = sideA i := by simpa only [label_left] using congrArg sideA he
    have h := hqa (e.symm i)
    rw [heA] at h
    exact ⟨decide_eq_true h.1, decide_eq_true h.2⟩
  have hmB : ∀ i, LB' (sideB i) i = true ∧ RB' (sideB i) i = true := by
    intro i
    have he : label (qa (e.symm i)) (qb (e.symm i)) = i := e.apply_symm_apply i
    have heB : qb (e.symm i) = sideB i := by simpa only [label_right] using congrArg sideB he
    have h := hqb (e.symm i)
    rw [heB] at h
    exact ⟨decide_eq_true h.1, decide_eq_true h.2⟩
  have matA : ∀ i j, rectangleMatrix LA' RA' i j = true ↔ A.Adj (aa i) (bb j) := by
    intro i j
    rw [hA _ _ (hac i) (hbc j)]
    simp only [rectangleMatrix, Bool.or_eq_true, Bool.and_eq_true, LA', RA', decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    · rintro ⟨q, h⟩
      cases q
      · exact Or.inl h
      · exact Or.inr h
  have matB : ∀ i j, rectangleMatrix LB' RB' i j = true ↔ B.Adj (aa i) (bb j) := by
    intro i j
    rw [hB _ _ (hac i) (hbc j)]
    simp only [rectangleMatrix, Bool.or_eq_true, Bool.and_eq_true, LB', RB', decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    · rintro ⟨q, h⟩
      cases q
      · exact Or.inl h
      · exact Or.inr h
  have matG : ∀ i j, both (rectangleMatrix LA' RA') (rectangleMatrix LB' RB') i j = true ↔
      G.Adj (aa i) (bb j) := by
    intro i j
    rw [both, Bool.and_eq_true, matA, matB, GraphFactor.edges_intersection G A B hfun]
  apply labelled_rectangles_impossible LA' RA' LB' RB' hmA hmB
  · intro i j k l hik hjl hg
    exact no_rectangle G h4 (aa i) (bb j) (aa k) (bb l)
      (fun h => hik (haa h)) (fun h => hjl (hbb h))
      ((matG i j).mp hg.1) ((matG i l).mp hg.2.1)
      ((matG k j).mp hg.2.2.1) ((matG k l).mp hg.2.2.2)
  · intro i j k haij hbij haik hbik
    have hna : ¬ A.Adj (aa i) (bb k) := by
      intro h
      have ht := (matA i k).mpr h
      rw [haik] at ht
      cases ht
    have hnb : ¬ B.Adj (aa i) (bb j) := by
      intro h
      have ht := (matB i j).mpr h
      rw [hbij] at ht
      cases ht
    exact (GraphFactor.exclusive_endpoints_distinct G A B hfun s hbip
      (aa i) (bb j) (aa i) (bb k) (hac i) (hbc j) (hac i) (hbc k)
      ((matA i j).mp haij) hnb ((matB i k).mp hbik) hna).1 rfl
  · intro i j k haij hbij hakj hbkj
    have hna : ¬ A.Adj (aa k) (bb j) := by
      intro h
      have ht := (matA k j).mpr h
      rw [hakj] at ht
      cases ht
    have hnb : ¬ B.Adj (aa i) (bb j) := by
      intro h
      have ht := (matB i j).mpr h
      rw [hbij] at ht
      cases ht
    exact (GraphFactor.exclusive_endpoints_distinct G A B hfun s hbip
      (aa i) (bb j) (aa k) (bb j) (hac i) (hbc j) (hac k) (hbc j)
      ((matA i j).mp haij) hnb ((matB k j).mp hbkj) hna).2.1 rfl

end PEqualNP.Outside.L_meta_3566.RankTwoFactor

namespace PEqualNP.Outside.L_meta_3566.FactorBelowObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.TopForm PEqualNP.EdgeOwnership

abbrev A : SimpleGraph (Fin 8) := SimpleGraph.fromRel fun u v =>
  u.val < 4 ∧ 4 ≤ v.val ∧ u.val / 2 = (v.val - 4) / 2

abbrev B : SimpleGraph (Fin 8) := SimpleGraph.fromRel fun u v =>
  u.val < 4 ∧ 4 ≤ v.val ∧ u.val % 2 = (v.val - 4) % 2

abbrev H : SimpleGraph (Fin 8) := SimpleGraph.fromRel fun u v =>
  u.val < 4 ∧ v.val = u.val + 4

abbrev G : SimpleGraph (Fin 8) := SimpleGraph.fromRel fun u v =>
  (u.val < 4 ∧ v.val = u.val + 4) ∨
  (u = 0 ∧ v = 5) ∨ (u = 1 ∧ v = 7) ∨ (u = 3 ∧ v = 6) ∨ (u = 2 ∧ v = 4)

lemma bipartite : ∀ u v : Fin 8, G.Adj u v → decide (u.val < 4) ≠ decide (v.val < 4) := by
  decide

lemma noFourCycle : NoFourCycle G := by decide

lemma G_edges : G.edgeFinset.card = 8 := by decide

lemma H_edges : H.edgeFinset.card = 4 := by decide

lemma intersection : ∀ u v : Fin 8, H.Adj u v ↔ A.Adj u v ∧ B.Adj u v := by decide

set_option maxRecDepth 10000 in
lemma factor_A : ∀ x : Fin 8 → Bool,
    graphFun A ∅ x = (((x 0 || x 1) && (x 4 || x 5)) || ((x 2 || x 3) && (x 6 || x 7))) := by
  decide

set_option maxRecDepth 10000 in
lemma factor_B : ∀ x : Fin 8 → Bool,
    graphFun B ∅ x = (((x 0 || x 2) && (x 4 || x 6)) || ((x 1 || x 3) && (x 5 || x 7))) := by
  decide

set_option maxRecDepth 10000 in
lemma below : ∀ x : Fin 8 → Bool,
    (graphFun A ∅ x && graphFun B ∅ x) = true → graphFun G ∅ x = true := by
  decide

lemma pair_profile : ∀ u v : Fin 8,
    (graphFun A ∅ (pairInput u v) && graphFun B ∅ (pairInput u v)) =
      graphFun H ∅ (pairInput u v) := by decide

lemma not_exact_intersection : ∃ x : Fin 8 → Bool,
    (graphFun A ∅ x && graphFun B ∅ x) = true ∧ graphFun H ∅ x = false := by
  refine ⟨fun v => decide (v = 1 ∨ v = 2 ∨ v = 4), ?_⟩
  decide

set_option maxRecDepth 10000 in
lemma matching_cover_lower_bound : ∀ S : Finset (Fin 8), IsVertexCover H S → 4 ≤ S.card := by
  unfold IsVertexCover
  decide

lemma matching_cover : IsVertexCover H {0, 1, 2, 3} := by
  unfold IsVertexCover
  decide

lemma no_three_cover : ¬ ∃ S : Finset (Fin 8), IsVertexCover H S ∧ S.card ≤ 3 := by
  rintro ⟨S, hS, hcard⟩
  have := matching_cover_lower_bound S hS
  omega

end PEqualNP.Outside.L_meta_3566.FactorBelowObstruction

namespace PEqualNP.Outside.L_meta_3566.NonjunkTop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership TopFrontier

lemma gate_count_with_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (w : ℕ) (hbelow : BelowWire G C w) :
    (orN G C).card + (orT G C).card + (leaves (n := n) C w).card + (junk G C).card ≤ C.size := by
  classical
  have hNT : Disjoint (orN G C) (orT G C) := by
    apply Finset.disjoint_left.mpr
    intro j hjN hjT
    simp only [orN, orT, gatesWhere, Finset.mem_filter, Finset.mem_range] at hjN hjT
    exact hjN.2.2 hjT.2.2
  have hLA : Disjoint (orN G C ∪ orT G C) (leaves (n := n) C w) := by
    apply Finset.disjoint_left.mpr
    intro j hjO hjL
    have hand := (Finset.mem_filter.mp hjL).2.1
    have hor : (gateAt C j).op = .or := by
      rcases Finset.mem_union.mp hjO with hjN | hjT
      · simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hjN
        exact hjN.2.1
      · simp only [orT, gatesWhere, Finset.mem_filter, Finset.mem_range] at hjT
        exact hjT.2.1
    rw [hor] at hand
    cases hand
  have hsub : (orN G C ∪ orT G C) ∪ leaves (n := n) C w ⊆ Finset.range C.size := by
    intro j hj
    rcases Finset.mem_union.mp hj with hjO | hjL
    · rcases Finset.mem_union.mp hjO with hjN | hjT
      · simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hjN
        exact Finset.mem_range.mpr hjN.1
      · simp only [orT, gatesWhere, Finset.mem_filter, Finset.mem_range] at hjT
        exact Finset.mem_range.mpr hjT.1
    · exact (Finset.mem_filter.mp hjL).1
  have hJ : Disjoint ((orN G C ∪ orT G C) ∪ leaves (n := n) C w) (junk G C) := by
    apply Finset.disjoint_left.mpr
    intro j hj hjJ
    have hjD : (gateAt C j).op = .and ∧ j < C.gates.length ∧
        ∃ x, gateVal n C j x = true ∧ graphFun G ∅ x = false := by
      simpa only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range,
        PEqualNP.CleanedNonEdge.IsDirtyAnd, PEqualNP.CleanedNonEdge.IsDirty] using (Finset.mem_filter.mp hjJ).2
    rcases Finset.mem_union.mp hj with hjO | hjL
    · have hor : (gateAt C j).op = .or := by
        rcases Finset.mem_union.mp hjO with hjN | hjT
        · simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hjN
          exact hjN.2.1
        · simp only [orT, gatesWhere, Finset.mem_filter, Finset.mem_range] at hjT
          exact hjT.2.1
      rw [hor] at hjD
      cases hjD.1
    · obtain ⟨x, hx, hn⟩ := hjD.2.2
      have ht := leaf_below G C w j hbelow hjL x hx
      rw [hn] at ht
      cases ht
  have hsubJ : ((orN G C ∪ orT G C) ∪ leaves (n := n) C w) ∪ junk G C ⊆
      Finset.range C.size := by
    intro j hj
    rcases Finset.mem_union.mp hj with h | h
    · exact hsub h
    · exact (Finset.mem_filter.mp h).1
  have hc := Finset.card_le_card hsubJ
  rw [Finset.card_union_of_disjoint hJ] at hc
  rw [Finset.card_union_of_disjoint hLA, Finset.card_union_of_disjoint hNT, Finset.card_range] at hc
  exact hc

end PEqualNP.Outside.L_meta_3566.NonjunkTop

namespace PEqualNP.Outside.L_meta_3566.NonjunkStarBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OrCharge TopFrontier ConditionalStarBound

lemma exists_cover_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b) (h4 : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hne : G.edgeFinset.Nonempty) (c : ℕ → Fin n) (f : ℕ → ℕ)
    (hW : ∀ j ∈ tops G C, f j < n + C.size)
    (hpure : ∀ j ∈ tops G C, ∀ x : Fin n → Bool, wire C (f j) x =
      wire C (f j) (fun v => if s v ≠ s (c j) then x v else false))
    (hclean : ∀ j ∈ tops G C, ∀ x : Fin n → Bool, x (c j) = true →
      wire C (f j) x = true → graphFun G ∅ x = true)
    (hretain : ∀ j ∈ tops G C, ∀ a b, G.Adj a b → gateVal n C j (pairInput a b) = true →
      pairInput a b (c j) = true ∧ wire C (f j) (pairInput a b) = true) :
    ∃ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) ∧
      G.edgeFinset.card + K.card + (junk G C).card ≤ C.size + 1 := by
  classical
  let T := leaves (n := n) C C.output
  have hbelow : BelowWire G C C.output := by
    intro x hx
    change circuitFun n C x = true at hx
    simpa only [hfun] using hx
  have hTtop : ∀ j ∈ T, j ∈ tops G C := by
    intro j hj
    obtain ⟨hjlt, hjand, _⟩ := Finset.mem_filter.mp hj
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨Finset.mem_range.mp hjlt, hjand, leaf_below G C C.output j hbelow hj⟩
  have hcover : ∀ a b, G.Adj a b → ∃ j ∈ T,
      pairInput a b (c j) = true ∧ wire C (f j) (pairInput a b) = true := by
    intro a b hab
    obtain ⟨j, hjtop, hpath, hjtrue⟩ := TopFrontierCoverage.edge_reaches_top G C hAO hfun a b hab
    have hjparts : j < C.gates.length ∧ (gateAt C j).op = .and ∧ BelowF G C j := by
      simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using hjtop
    have hjT : j ∈ T :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjparts.1, hjparts.2.1, hpath⟩
    exact ⟨j, hjT, hretain j hjtop a b hab hjtrue⟩
  have hedge := StarGrouping.edge_orN_bound G s hbip h4 C hAO T c f
    (fun j hj => hW j (hTtop j hj)) (fun j hj => hpure j (hTtop j hj))
    (fun j hj => hclean j (hTtop j hj)) hcover
  have hTcard := leaves_card_le_orT G C hAO C.output (output_valid G C hfun hne) hbelow
  have hcount := NonjunkTop.gate_count_with_junk G C C.output hbelow
  refine ⟨T.image c, ?_, ?_⟩
  · intro a b hab
    obtain ⟨j, hj, hz, _⟩ := hcover a b hab
    have hz' : c j = a ∨ c j = b := by simpa [pairInput] using hz
    rcases hz' with ha | hb
    · exact Or.inl (Finset.mem_image.mpr ⟨j, hj, ha⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨j, hj, hb⟩)
  · have hK := Finset.card_image_le (s := T) (f := c)
    change T.card ≤ (orT G C).card + 1 at hTcard
    change (orN G C).card + (orT G C).card + T.card + (junk G C).card ≤ C.size at hcount
    omega


end PEqualNP.Outside.L_meta_3566.NonjunkStarBound

namespace PEqualNP.Outside.L_meta_3566.NonjunkMixedBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership SemanticPurity OrCharge

lemma exists_cover_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b) (h4 : NoFourCycle G)
    (C : Circuit) (hLeast : IsLeastAO G C) (hne : G.edgeFinset.Nonempty)
    (hOR : ∀ j, j < C.gates.length → (gateAt C j).op = .or →
      ¬ Pure s false (W n C (n + j)) → ¬ Pure s true (W n C (n + j)) →
      ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true) :
    ∃ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) ∧
      G.edgeFinset.card + K.card + (junk G C).card ≤ C.size + 1 := by
  classical
  have hn : Nonempty (Fin n) := by
    obtain ⟨e, _⟩ := hne
    induction e using Sym2.ind with
    | _ a _ => exact ⟨a⟩
  let u0 : Fin n := Classical.choice hn
  have hex : ∀ j : ℕ, ∃ (u : Fin n) (w : ℕ), j ∈ tops G C →
      w < n + C.size ∧
      (∀ x : Fin n → Bool, wire C w x =
        wire C w (fun v => if s v ≠ s u then x v else false)) ∧
      (∀ x : Fin n → Bool, x u = true → wire C w x = true → graphFun G ∅ x = true) ∧
      (∀ a b, G.Adj a b → gateVal n C j (pairInput a b) = true →
        pairInput a b u = true ∧ wire C w (pairInput a b) = true) := by
    intro j
    by_cases hjtop : j ∈ tops G C
    · have hjparts : j < C.gates.length ∧ (gateAt C j).op = .and ∧ BelowF G C j := by
        simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using hjtop
      obtain ⟨u, w, hwb, hwp, hclean, hkeep⟩ := ConeFrontier.clean_and_star_all G s hbip h4
        C hLeast hOR j hjparts.1 hjparts.2.1 hjparts.2.2
      have hwvalid : w < n + C.gates.length := by omega
      have hopp := ConeFrontier.pure_star_opposite_color G s hbip C hLeast.1 u w hwvalid hwp hclean
      refine ⟨u, w, fun _ => ⟨hwvalid, ?_, ?_, ?_⟩⟩
      · intro x
        have he := hopp x
        change wire C w x = wire C w (mask s (!(s u)) x) at he
        have hm : mask s (!(s u)) x = (fun v => if s v ≠ s u then x v else false) := by
          funext v
          cases hv : s v <;> cases hu : s u <;> simp [mask, hv, hu]
        simpa only [hm] using he
      · intro x hxu hxw
        change W n C w x = true at hxw
        exact hclean x (by rw [hxu, hxw]; rfl)
      · intro a b hab hjtrue
        have h := hkeep a b hab hjtrue
        simpa only [Bool.and_eq_true, W, wire] using h
    · exact ⟨u0, 0, fun h => False.elim (hjtop h)⟩
  choose c f hcf using hex
  apply NonjunkStarBound.exists_cover_budget G s hbip h4 C hLeast.1 hLeast.2.1 hne c f
  · intro j hj
    exact (hcf j hj).1
  · intro j hj
    exact (hcf j hj).2.1
  · intro j hj
    exact (hcf j hj).2.2.1
  · intro j hj
    exact (hcf j hj).2.2.2

lemma dirty_mixed_or_of_no_cover_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b) (h4 : NoFourCycle G)
    (C : Circuit) (hLeast : IsLeastAO G C) (hne : G.edgeFinset.Nonempty)
    (hbad : ¬ ∃ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) ∧
      G.edgeFinset.card + K.card + (junk G C).card ≤ C.size + 1) :
    ∃ j < C.gates.length, (gateAt C j).op = .or ∧
      ¬ Pure s false (W n C (n + j)) ∧ ¬ Pure s true (W n C (n + j)) ∧ ¬ BelowF G C j := by
  classical
  by_contra hnone
  apply hbad
  apply exists_cover_budget G s hbip h4 C hLeast hne
  intro j hj hop hleft hright
  by_contra hnot
  apply hnone
  exact ⟨j, hj, hop, hleft, hright, hnot⟩

lemma junk_empty_of_upper_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b) (h4 : NoFourCycle G)
    (C : Circuit) (hLeast : IsLeastAO G C) (hne : G.edgeFinset.Nonempty)
    (hOR : ∀ j, j < C.gates.length → (gateAt C j).op = .or →
      ¬ Pure s false (W n C (n + j)) → ¬ Pure s true (W n C (n + j)) →
      ∀ x, W n C (n + j) x = true → graphFun G ∅ x = true)
    (k : ℕ) (hcover : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) → k ≤ K.card)
    (hupper : C.size + 1 ≤ G.edgeFinset.card + k) : junk G C = ∅ := by
  obtain ⟨K, hK, hbudget⟩ := exists_cover_budget G s hbip h4 C hLeast hne hOR
  have hmin := hcover K hK
  apply Finset.card_eq_zero.mp
  omega

end PEqualNP.Outside.L_meta_3566.NonjunkMixedBound
