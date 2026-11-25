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
