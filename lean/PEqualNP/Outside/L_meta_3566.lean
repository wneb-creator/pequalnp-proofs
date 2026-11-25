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
