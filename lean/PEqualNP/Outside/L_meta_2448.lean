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

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_2448

lemma common_center_of_pairwise_meeting {V : Type*} (G : SimpleGraph V)
    (r : V → V → Prop)
    (hadj : ∀ {u v}, r u v → G.Adj u v)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hmeet : ∀ {a b c d}, r a b → r c d →
      a = c ∨ a = d ∨ b = c ∨ b = d) :
    (∀ u v, ¬ r u v) ∨ ∃ c, ∀ u v, r u v → u = c ∨ v = c := by
  classical
  by_cases used : ∃ a b, r a b
  · obtain ⟨a, b, hab⟩ := used
    right
    by_cases ha : ∀ u v, r u v → u = a ∨ v = a
    · exact ⟨a, ha⟩
    · simp only [not_forall, Classical.not_imp] at ha
      obtain ⟨p, q, hpq, hna⟩ := ha
      have hpa : p ≠ a := fun h => hna (Or.inl h)
      have hqa : q ≠ a := fun h => hna (Or.inr h)
      have hbpq : p = b ∨ q = b := by
        rcases hmeet hpq hab with h | h | h | h
        · exact (hpa h).elim
        · exact Or.inl h
        · exact (hqa h).elim
        · exact Or.inr h
      have hext : ∃ w, w ≠ a ∧ G.Adj b w ∧
          ∀ u v, r u v → u = b ∨ v = b ∨ u = w ∨ v = w := by
        rcases hbpq with rfl | rfl
        · refine ⟨q, hqa, hadj hpq, ?_⟩
          intro u v huv
          rcases hmeet huv hpq with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr h))
        · refine ⟨p, hpa, (hadj hpq).symm, ?_⟩
          intro u v huv
          rcases hmeet huv hpq with h | h | h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inr (Or.inl h)
      obtain ⟨w, hwa, hbw, hmeetw⟩ := hext
      refine ⟨b, ?_⟩
      intro u v huv
      by_contra hnb
      have hub : u ≠ b := fun h => hnb (Or.inl h)
      have hvb : v ≠ b := fun h => hnb (Or.inr h)
      have huva : u = a ∨ v = a := by
        rcases hmeet huv hab with h | h | h | h
        · exact Or.inl h
        · exact (hub h).elim
        · exact Or.inr h
        · exact (hvb h).elim
      have huvw : u = w ∨ v = w := by
        rcases hmeetw u v huv with h | h | h | h
        · exact (hub h).elim
        · exact (hvb h).elim
        · exact Or.inl h
        · exact Or.inr h
      have hwa_adj : G.Adj w a := by
        rcases huva with rfl | rfl
        · have hvw := huvw.resolve_left hwa.symm
          simpa only [hvw] using (hadj huv).symm
        · have huw := huvw.resolve_right hwa.symm
          simpa only [huw] using hadj huv
      exact htriangle a b w (hadj hab) hbw hwa_adj
  · left
    exact fun u v huv => used ⟨u, v, huv⟩

set_option maxHeartbeats 1000000 in
lemma owned_disjoint_edges_have_false_positive (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) (hm : Monotone2 C)
  (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
  (a b c d : Fin n)
  (ab : Owns n C j a b) (cd : Owns n C j c d)
  (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
  ∃ u ∈ ({a,b,c,d} : Finset (Fin n)), ∃ v ∈ ({a,b,c,d} : Finset (Fin n)), ¬G.Adj u v ∧ gateVal n C j (pairInput u v) = true := by
  classical
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_stepWire_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
      w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
      ∃ (pre post : List Gate) (gj : Gate),
        gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
    refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
    rw [List.cons_getElem_drop_succ, List.take_append_drop]

  let W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
    (C.wires (List.ofFn x)).getD u false

  have gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
    change C.gates.getD k _ = _
    simp [List.getD_eq_getElem?_getD, hk]

  have W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
      W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
        if i < n + k then W n C x i else false) := by
    obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
    have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
    rw [hga]
    let w0 := pre.foldl stepWire (List.ofFn x)
    have hw0_len : w0.length = n + k := by
      simp [w0, foldl_stepWire_length, hpre_len]
    have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
      simp only [W]
      rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
      rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
      simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
    rw [hCj]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    by_cases hi : i < n + k
    · simp only [hi, ↓reduceIte]
      simp only [W]
      rw [wires_eq_foldl, hgs, List.foldl_append]
      exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
    · simp only [hi, ↓reduceIte]
      exact getD_ge_length w0 i (by omega)

  have W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
      W n C x u = x ⟨u, hu⟩ := by
    simp only [W]
    rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
    simp [List.getD_eq_getElem?_getD, hu]

  have coneEq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
      coneStep n cs g = cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := rfl
  have coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [coneEq]
      omega

  have coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
      (coneStep n cs g).getD cs.length [] =
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => (w - n) :: cs.getD (w - n) []) := by
    simp [coneEq, List.getD_eq_getElem?_getD]

  have coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
      (coneStep n cs g).getD m [] = cs.getD m [] := by
    simp [coneEq, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

  have coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
      (hk : k < cs.length) :
      (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
    induction gs generalizing cs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih (coneStep n cs g) (by simp [coneEq]; omega)]
      exact coneStep_getD_lt n cs g k hk

  have inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
      InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        (i = w - n ∨ InCone n C i (w - n)) := by
    obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
    have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
    rw [hga]
    have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
      delta cones
      rw [hgs, List.foldl_append, List.foldl_cons]
    have hl0 : (pre.foldl (coneStep n) []).length = k := by
      rw [coneFold_length]; simp [hpre_len]
    have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
      simp [coneEq, hl0]
    have h1 : (cones n C).getD k [] =
        (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
          (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
      rw [hc, coneFold_getD_lt n post _ k (by omega)]
      have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
      rw [hl0] at h
      exact h
    have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
      intro m hm
      rw [hc, coneFold_getD_lt n post _ m (by omega)]
      exact coneStep_getD_lt n _ gk m (by omega)
    unfold InCone
    rw [h1]
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
      refine ⟨w, hw, hn, hlt, ?_⟩
      rcases h with h | h
      · exact Or.inl h
      · right
        rw [h2 (w - n) (by omega)]
        exact h
    · rintro ⟨w, hw, hn, hlt, h⟩
      refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
      rcases h with h | h
      · exact Or.inl h
      · right
        rw [← h2 (w - n) (by omega)]
        exact h


  have ite_true_iff (c : Prop) [Decidable c] (b : Bool) :
      (if c then b else false) = true ↔ c ∧ b = true := by
    by_cases h : c <;> simp [h]

  have W_and_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
      (hop : (gateAt C k).op = GateOp.and) :
      W n C x (n + k) = true ↔ ∀ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
    rw [W_gate n C x k hk, hop]
    have andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
    simp only [andEval, List.all_eq_true, List.mem_map, id_eq]
    constructor
    · intro h w hw
      exact (ite_true_iff _ _).mp (h _ ⟨w, hw, rfl⟩)
    · rintro h b ⟨w, hw, rfl⟩
      exact (ite_true_iff _ _).mpr (h w hw)

  have W_or_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
      (hop : (gateAt C k).op = GateOp.or) :
      W n C x (n + k) = true ↔ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
    rw [W_gate n C x k hk, hop]
    have orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
    simp only [orEval, List.any_eq_true, List.mem_map, id_eq]
    constructor
    · rintro ⟨b, ⟨w, hw, rfl⟩, h⟩
      exact ⟨w, hw, (ite_true_iff _ _).mp h⟩
    · rintro ⟨w, hw, h⟩
      exact ⟨_, ⟨w, hw, rfl⟩, (ite_true_iff _ _).mpr h⟩

  have inCone_lt (n : ℕ) (C : Circuit) :
      ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk i hi
      obtain ⟨w, _, hn, hlt, h⟩ := (inCone_iff n C i k hk).mp hi
      rcases h with h | h
      · omega
      · have := ih (w - n) (by omega) (by omega) i h
        omega

  have gate_mono2 (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
        (gateAt C k).inputs.length ≤ 2 := by
    have hg := hM (C.gates[k]) (List.getElem_mem hk)
    rw [← gateAt_eq C k hk] at hg
    have h1 := hg.1
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, hg.2⟩

  let Reach (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) : Prop :=
    ∀ P : ℕ → Prop, P t.val →
      (∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
        ∀ a ∈ (gateAt C k).inputs, a < n + k → P a → P (n + k)) → P w

  have reach_refl (n : ℕ) (C : Circuit) (t : Fin n) : Reach n C t t.val := fun _ h _ => h

  have reach_step (n : ℕ) (C : Circuit) (t : Fin n) (k : ℕ) (hk : k < C.gates.length)
      (hop : (gateAt C k).op = GateOp.or) (a : ℕ) (ha : a ∈ (gateAt C k).inputs)
      (hlt : a < n + k) (h : Reach n C t a) : Reach n C t (n + k) :=
    fun P h0 hs => hs k hk hop a ha hlt (h P h0 hs)

  have reach_val (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) (y : Fin n → Bool)
      (hy : y t = true) (h : Reach n C t w) : W n C y w = true :=
    h (fun w => W n C y w = true) (by rw [W_input n C y t.val t.isLt]; exact hy)
      (fun k hk hop a ha hlt ih => (W_or_iff n C y k hk hop).mpr ⟨a, ha, hlt, ih⟩)

  have descent (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x : Fin n → Bool) :
      ∀ k, k < C.gates.length → W n C x (n + k) = true →
        (gateAt C k).op = GateOp.and ∨
        (∃ i, InCone n C i k ∧ (gateAt C i).op = GateOp.and ∧ W n C x (n + i) = true) ∨
        (∃ u : Fin n, x u = true ∧ Reach n C u (n + k)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hx
      rcases (gate_mono2 C hM k hk).1 with hop | hop
      · exact Or.inl hop
      · obtain ⟨w, hw, hlt, hwx⟩ := (W_or_iff n C x k hk hop).mp hx
        by_cases hwn : w < n
        · right; right
          refine ⟨⟨w, hwn⟩, ?_, ?_⟩
          · rw [← W_input n C x w hwn]; exact hwx
          · exact reach_step n C ⟨w, hwn⟩ k hk hop w hw hlt (reach_refl n C ⟨w, hwn⟩)
        · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
          have he : n + k' - n = k' := by omega
          rcases ih k' (by omega) (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨u, hu, hdom⟩
          · right; left
            exact ⟨k', (inCone_iff n C k' k hk).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩,
              h, hwx⟩
          · right; left
            exact ⟨i, (inCone_iff n C i k hk).mpr
              ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩, hia, hix⟩
          · right; right
            exact ⟨u, hu, reach_step n C u k hk hop (n + k') hw hlt hdom⟩

  have owns_reach (n : ℕ) (C : Circuit) (hM : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
      (hop : (gateAt C j).op = GateOp.and) (p q : Fin n) (ho : Owns n C j p q) :
      ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Reach n C p w ∨ Reach n C q w) := by
    obtain ⟨_, _, hval, hno⟩ := ho
    intro w hw
    have hval' : W n C (pairInput p q) (n + j) = true := hval
    obtain ⟨hlt, hwx⟩ := (W_and_iff n C _ j hj hop).mp hval' w hw
    refine ⟨hlt, ?_⟩
    by_cases hwn : w < n
    · rw [W_input n C _ w hwn] at hwx
      have h' : (⟨w, hwn⟩ : Fin n) = p ∨ (⟨w, hwn⟩ : Fin n) = q := of_decide_eq_true hwx
      rcases h' with h | h
      · left
        rw [← h]; exact reach_refl n C ⟨w, hwn⟩
      · right
        rw [← h]; exact reach_refl n C ⟨w, hwn⟩
    · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
      have he : n + k' - n = k' := by omega
      have hk'j : k' < j := by omega
      have hc : InCone n C k' j :=
        (inCone_iff n C k' j hj).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩
      rcases descent n C hM (pairInput p q) k' (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨t, ht, hdom⟩
      · have hf : W n C (pairInput p q) (n + k') = false := hno k' hk'j hc h
        rw [hwx] at hf
        exact absurd hf (by simp)
      · have hc2 : InCone n C i j := (inCone_iff n C i j hj).mpr
          ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩
        have hij := inCone_lt n C j hj i hc2
        have hf : W n C (pairInput p q) (n + i) = false := hno i hij hc2 hia
        rw [hix] at hf
        exact absurd hf (by simp)
      · have h' : t = p ∨ t = q := of_decide_eq_true ht
        rcases h' with h | h
        · left; rw [← h]; exact hdom
        · right; rw [← h]; exact hdom
  let S : Finset (Fin n) := {a,b,c,d}
  change ∃ u ∈ S, ∃ v ∈ S, ¬G.Adj u v ∧ gateVal n C j (pairInput u v) = true
  have haS : a ∈ S := by simp [S]
  have hbS : b ∈ S := by simp [S]
  have hcS : c ∈ S := by simp [S]
  have hdS : d ∈ S := by simp [S]
  by_contra! clean
  have F3 (s t : Fin n) (hsS : s ∈ S) (htS : t ∈ S)
      (hr : ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Reach n C s w ∨ Reach n C t w)) :
      G.Adj s t := by
    by_contra hst
    have hs : pairInput s t s = true := decide_eq_true (Or.inl rfl : s = s ∨ s = t)
    have ht : pairInput s t t = true := decide_eq_true (Or.inr rfl : t = s ∨ t = t)
    have hval : W n C (pairInput s t) (n + j) = true :=
      (W_and_iff n C _ j ab.1 ab.2.1).mpr (fun w hw => ⟨(hr w hw).1,
        (hr w hw).2.elim (fun h => reach_val n C s w _ hs h) (fun h => reach_val n C t w _ ht h)⟩)
    have hval' : gateVal n C j (pairInput s t) = true := hval
    have hfalse := clean s hsS t htS hst
    simp [hval'] at hfalse
  have reach {s t : Fin n} (h : Owns n C j s t) := owns_reach n C hm j ab.1 ab.2.1 s t h
  have hlen := (gate_mono2 C hm j ab.1).2
  rcases hin : (gateAt C j).inputs with _ | ⟨p, _ | ⟨q, _ | ⟨t, ts⟩⟩⟩
  · exact (F3 a a haS haS (by simp [hin])).ne rfl
  · have h := reach ab p (by simp [hin])
    rcases h.2 with ha | hb
    · exact (F3 a a haS haS (by simpa [hin] using And.intro h.1 ha)).ne rfl
    · exact (F3 b b hbS hbS (by simpa [hin] using And.intro h.1 hb)).ne rfl
  · have hp := (reach ab p (by simp [hin])).1
    have hq := (reach ab q (by simp [hin])).1
    have cross (s t : Fin n) (hsS : s ∈ S) (htS : t ∈ S) (hs : Reach n C s p) (ht : Reach n C t q) : G.Adj s t := by
      apply F3 s t hsS htS
      intro w hw
      simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨hp, Or.inl hs⟩
      · exact ⟨hq, Or.inr ht⟩
    have sides {s t : Fin n} (hsS : s ∈ S) (htS : t ∈ S) (h : Owns n C j s t) :
        (Reach n C s p ∧ Reach n C t q) ∨ (Reach n C t p ∧ Reach n C s q) := by
      rcases (reach h p (by simp [hin])).2 with hs | ht <;>
        rcases (reach h q (by simp [hin])).2 with hu | hv
      · exact ((cross s s hsS hsS hs hu).ne rfl).elim
      · exact Or.inl ⟨hs, hv⟩
      · exact Or.inr ⟨ht, hu⟩
      · exact ((cross t t htS htS ht hv).ne rfl).elim
    have rectangle (s t u v : Fin n) (hsS : s ∈ S) (htS : t ∈ S) (huS : u ∈ S) (hvS : v ∈ S)
        (hs : Reach n C s p) (ht : Reach n C t q)
        (hu : Reach n C u p) (hv : Reach n C v q) : s = u ∨ t = v :=
      hfour s t u v (cross s t hsS htS hs ht) (cross u t huS htS hu ht).symm (cross u v huS hvS hu hv) (cross s v hsS hvS hs hv).symm
    rcases sides haS hbS ab with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;> rcases sides hcS hdS cd with ⟨hc, hd⟩ | ⟨hd, hc⟩
    · exact (rectangle a b c d haS hbS hcS hdS ha hb hc hd).elim hac hbd
    · exact (rectangle a b d c haS hbS hdS hcS ha hb hd hc).elim had hbc
    · exact (rectangle b a c d hbS haS hcS hdS hb ha hc hd).elim hbc had
    · exact (rectangle b a d c hbS haS hdS hcS hb ha hd hc).elim hbd hac
  · simp [hin] at hlen

lemma hasStarProfile_of_pairwise_meeting (n : ℕ) (G : SimpleGraph (Fin n))
    (C : Circuit)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hmeet : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ a b c d, G.Adj a b → G.Adj c d → Owns n C j a b → Owns n C j c d →
        a = c ∨ a = d ∨ b = c ∨ b = d) : HasStarProfile n G C := by
  intro j hj hop
  rcases common_center_of_pairwise_meeting G
      (fun u v => G.Adj u v ∧ Owns n C j u v)
      (fun h => h.1) htriangle
      (fun h₁ h₂ => hmeet j hj hop _ _ _ _ h₁.1 h₂.1 h₁.2 h₂.2) with h | ⟨c, hc⟩
  · left
    exact fun u v huv hov => h u v ⟨huv, hov⟩
  · right
    exact ⟨c, fun u v huv hov => hc u v ⟨huv, hov⟩⟩

lemma hasStarProfile_of_pair_sound (n : ℕ) (G : SimpleGraph (Fin n))
    (C : Circuit) (hm : Monotone2 C)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (hclean : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ u v, gateVal n C j (pairInput u v) = true → G.Adj u v) :
    HasStarProfile n G C := by
  apply hasStarProfile_of_pairwise_meeting n G C htriangle
  intro j hj hop a b c d _ _ hab hcd
  by_contra hmeet
  have hac : a ≠ c := fun h => hmeet (Or.inl h)
  have had : a ≠ d := fun h => hmeet (Or.inr (Or.inl h))
  have hbc : b ≠ c := fun h => hmeet (Or.inr (Or.inr (Or.inl h)))
  have hbd : b ≠ d := fun h => hmeet (Or.inr (Or.inr (Or.inr h)))
  obtain ⟨u, _, v, _, hnon, hfire⟩ :=
    owned_disjoint_edges_have_false_positive n G C j hm hfour a b c d hab hcd hac had hbc hbd
  exact hnon (hclean j hj hop u v hfire)

end PEqualNP.Outside.L_meta_2448

namespace PEqualNP.Outside.L_meta_2448_aux.StarNormal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

lemma ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


lemma mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma snoc_mono (W : List Bool) (v v' : Bool) (h : v = true → v' = true) (i : ℕ) :
    (W ++ [v]).getD i false = true → (W ++ [v']).getD i false = true := by
  rcases Nat.lt_trichotomy i W.length with hi | hi | hi
  · rw [getD_snoc_lt _ _ _ hi, getD_snoc_lt _ _ _ hi]; exact id
  · subst hi; rw [getD_snoc_eq, getD_snoc_eq]; exact h
  · rw [getD_snoc_gt _ _ _ hi]; intro hf; exact absurd hf (by simp)

lemma opmono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b a' b' : Bool)
    (ha : a = true → a' = true) (hb : b = true → b' = true) :
    op.eval [a, b] = true → op.eval [a', b'] = true := by
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval] <;> tauto

lemma core (n g : ℕ) (gates : List Gate) (hg : g < gates.length) (o w' : ℕ) (replacement : Gate)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hw' : w' < n + g) (x : Fin n → Bool)
    (hF : (wf gates (List.ofFn x)).getD w' false = true → (wf gates (List.ofFn x)).getD o false = true)
    (hsame : (wf (gates.take g) (List.ofFn x)).getD w' false = false →
      replacement.op.eval (replacement.inputs.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false)
        = gates[g].op.eval (gates[g].inputs.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false))
    (hup : gates[g].op.eval (gates[g].inputs.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false) = true →
      replacement.op.eval (replacement.inputs.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false) = true) :
    (wf (gates.set g replacement) (List.ofFn x)).getD o false
      = (wf gates (List.ofFn x)).getD o false := by
  have h2 : ∀ a : Gate, gates.set g a = gates.take g ++ a :: gates.drop (g + 1) := by
    intro a
    rw [List.set_eq_take_append_cons_drop]
    simp [hg]
  have h1 : gates = gates.take g ++ gates[g] :: gates.drop (g + 1) := by
    rw [← h2]
    exact (List.set_getElem_self _).symm
  generalize hW : wf (gates.take g) (List.ofFn x) = W at *
  have hWlen : W.length = n + g := by
    rw [← hW, wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hg)]
  have e1 : wf gates (List.ofFn x) = wf (gates.drop (g + 1))
      (W ++ [gates[g].op.eval (gates[g].inputs.map fun i => W.getD i false)]) := by
    conv_lhs => rw [h1]
    rw [wf_append, wf_cons, hW]
  have e2 : wf (gates.set g replacement) (List.ofFn x) = wf (gates.drop (g + 1))
      (W ++ [replacement.op.eval (replacement.inputs.map fun i => W.getD i false)]) := by
    rw [h2, wf_append, wf_cons, hW]
  rw [e2, e1]
  rw [e1] at hF
  cases hc : W.getD w' false
  · rw [hsame hc]
  · have hk : (wf (gates.drop (g + 1)) (W ++ [gates[g].op.eval (gates[g].inputs.map fun i => W.getD i false)])).getD w' false = true := by
      rw [wf_keep _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega)]
      exact hc
    have ht := hF hk
    rw [ht]
    exact mono2 (gates.drop (g + 1)) (fun g' hg' => hleg g' (List.mem_of_mem_drop hg')) _ _ (by simp)
      (snoc_mono W _ _ hup) o ht

lemma bypass_and (n : ℕ) (C : Circuit) (j w : ℕ)
    (hm : Monotone2 C) (hj : j < C.gates.length)
    (hop : C.gates[j].op = GateOp.and) (hw : w ∈ C.gates[j].inputs)
    (hwb : w < n + j)
    (hbelow : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD w false = true → circuitFun n C x = true) :
    let D : Circuit := ⟨C.gates.set j ⟨GateOp.or, [w]⟩, C.output⟩
    Monotone2 D ∧ circuitFun n D = circuitFun n C ∧ D.size = C.size := by
  dsimp only
  refine ⟨?_, ?_, by simp [Circuit.size]⟩
  · intro g hg
    rcases List.mem_or_eq_of_mem_set hg with hg | rfl
    · exact hm g hg
    · simp
  · funext x
    apply core n j C.gates hj C.output w ⟨GateOp.or, [w]⟩
    · intro g hg
      have h := hm g hg
      simpa using h
    · exact hwb
    · exact hbelow x
    · intro hwfalse
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false, hwfalse]
      symm
      rw [hop]
      apply Bool.eq_false_iff.mpr
      intro htrue
      have h := (List.all_eq_true.mp htrue) _ (List.mem_map_of_mem hw)
      change (wf (C.gates.take j) (List.ofFn x)).getD w false = true at h
      rw [hwfalse] at h
      contradiction
    · intro htrue
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      rw [hop] at htrue
      exact (List.all_eq_true.mp htrue) _ (List.mem_map_of_mem hw)

namespace CopyDeletion

open PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_step_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ s : List Bool, gs.foldl step w = w ++ s ∧ s.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨s, hs, hl⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: s, ?_, by simp [hl]⟩
    rw [List.foldl_cons, hs]
    simp [step]

lemma foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨s, hs, hl⟩ := foldl_step_prefix gs w
  simp [hs, hl]

lemma getD_append_left (w s : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ s).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_step_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨s, hs, _⟩ := foldl_step_prefix gs w
  rw [hs, getD_append_left w s i hi]

lemma getD_append_singleton_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · exact getD_append_left w [b] i h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega : (w ++ [b]).length ≤ i),
      List.getElem?_eq_none (by omega : w.length ≤ i)]
lemma foldl_split (gs : List Gate) (k : ℕ) (g : Gate) (hg : gs[k]? = some g) (w0 : List Bool) :
    gs.foldl step w0 = (gs.drop (k + 1)).foldl step (step ((gs.take k).foldl step w0) g) := by
  have hk : k < gs.length := by
    rcases (List.getElem?_eq_some_iff.mp hg) with ⟨hk, _⟩
    exact hk
  have hgk : gs[k] = g := (List.getElem?_eq_some_iff.mp hg).2
  conv_lhs => rw [← List.take_append_drop k gs, List.drop_eq_getElem_cons hk, hgk]
  rw [List.foldl_append, List.foldl_cons]

lemma take_fold_length (gs : List Gate) (k : ℕ) (hk : k < gs.length) (w0 : List Bool) :
    ((gs.take k).foldl step w0).length = w0.length + k := by
  rw [foldl_step_length, List.length_take]
  omega

lemma wires_copy (F : Circuit) (k u : ℕ) (hk : F.gates[k]? = some ⟨GateOp.or, [u]⟩)
    (w0 : List Bool) (hu : u < w0.length + k) :
    (F.wires w0).getD (w0.length + k) false = (F.wires w0).getD u false := by
  have hk' : k < F.gates.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [wires_eq, foldl_split F.gates k _ hk w0]
  have hl := take_fold_length F.gates k hk' w0
  set Wp := (F.gates.take k).foldl step w0
  rw [foldl_step_getD _ _ _ (by simp [step]; omega), foldl_step_getD _ _ _ (by simp [step]; omega)]
  unfold step
  rw [← hl, getD_append_singleton_last, getD_append_left _ _ _ (by omega)]
  simp [GateOp.eval]


def sig (m u : ℕ) (i : ℕ) : ℕ := if i < m then i else if i = m then u else i - 1

def rd (m u : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sig m u)⟩

def sg (k : ℕ) (j : ℕ) : ℕ := if j < k then j else j - 1

def del (n k u : ℕ) (E : Circuit) : Circuit :=
  ⟨(E.gates.eraseIdx k).map (rd (n + k) u), sig (n + k) u E.output⟩

lemma sig_gate (n k u j : ℕ) (hj : j ≠ k) : sig (n + k) u (n + j) = n + sg k j := by
  unfold sig sg
  split_ifs <;> omega

def Rel (m u : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length + 1 ∧ m < a.length ∧ ∀ i, b.getD (sig m u i) false = a.getD i false

lemma getD_oob (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma rel_step (m u : ℕ) (hu : u < m) (a b : List Bool) (g : Gate) (h : Rel m u a b) :
    Rel m u (step a g) (step b (rd m u g)) := by
  obtain ⟨hl, hm, hv⟩ := h
  have hev : (rd m u g).op.eval ((rd m u g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    simp only [rd, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hv i
  unfold step
  rw [hev]
  set v := g.op.eval (g.inputs.map fun i => a.getD i false)
  refine ⟨by simp [hl], by simp; omega, ?_⟩
  intro i
  rcases Nat.lt_trichotomy i a.length with h1 | h1 | h1
  · have hs : sig m u i < b.length := by unfold sig; split_ifs <;> omega
    rw [getD_append_left _ _ _ hs, getD_append_left _ _ _ h1, hv]
  · have hs : sig m u i = b.length := by unfold sig; split_ifs <;> omega
    rw [hs, getD_append_singleton_last, h1, getD_append_singleton_last]
  · have hs : sig m u i > b.length := by unfold sig; split_ifs <;> omega
    rw [getD_oob _ _ (by simp; omega), getD_oob _ _ (by simp; omega)]

lemma rel_fold (m u : ℕ) (hu : u < m) (gs : List Gate) : ∀ a b : List Bool, Rel m u a b →
    Rel m u (gs.foldl step a) ((gs.map (rd m u)).foldl step b) := by
  induction gs with
  | nil => intro a b h; simpa using h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons, List.map_cons]
    exact ih _ _ (rel_step m u hu a b g h)

lemma rd_id (m u : ℕ) (g : Gate) (h : ∀ i ∈ g.inputs, i < m) : rd m u g = g := by
  obtain ⟨op, ins⟩ := g
  simp only [rd, Gate.mk.injEq, true_and]
  conv_rhs => rw [← List.map_id ins]
  apply List.map_congr_left
  intro i hi
  have := h i hi
  simp [sig, this]

lemma del_fun (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) (hu : u < n + k)
    (hpre : ∀ g ∈ E.gates.take k, ∀ i ∈ g.inputs, i < n + k)
    (hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD u false) :
    circuitFun n (del n k u E) = circuitFun n E := by
  funext x
  have hc := hcopy x
  unfold circuitFun Circuit.eval
  have hgk : E.gates[k]? = some E.gates[k] := List.getElem?_eq_getElem hk
  set gk := E.gates[k]
  set w0 := List.ofFn x with hw0
  have hw0l : w0.length = n := by simp [hw0]
  have hl := take_fold_length E.gates k hk w0
  rw [hw0l] at hl
  set Wp := (E.gates.take k).foldl step w0 with hWp
  have hW : E.wires w0 = (E.gates.drop (k + 1)).foldl step (step Wp gk) := by
    rw [wires_eq, foldl_split E.gates k gk hgk w0]
  have hD : (del n k u E).wires w0 =
      ((E.gates.drop (k + 1)).map (rd (n + k) u)).foldl step Wp := by
    rw [wires_eq]
    simp only [del]
    rw [List.eraseIdx_eq_take_drop_succ, List.map_append, List.foldl_append]
    congr 1
    rw [hWp]
    congr 1
    conv_rhs => rw [← List.map_id (E.gates.take k)]
    apply List.map_congr_left
    intro g hg
    exact rd_id _ _ g (hpre g hg)
  -- the value of gate k equals that of u
  have hvk : (step Wp gk).getD (n + k) false = Wp.getD u false := by
    rw [hW, foldl_step_getD _ _ _ (by simp [step]; omega),
      foldl_step_getD _ _ _ (by simp [step]; omega)] at hc
    rw [hc]
    unfold step
    exact getD_append_left _ _ _ (by omega)
  have hrel0 : Rel (n + k) u (step Wp gk) Wp := by
    refine ⟨by simp [step], by simp [step]; omega, ?_⟩
    intro i
    rcases Nat.lt_trichotomy i (n + k) with h1 | h1 | h1
    · have : sig (n + k) u i = i := by simp [sig, h1]
      rw [this]
      unfold step
      rw [getD_append_left _ _ _ (by omega)]
    · have : sig (n + k) u i = u := by simp [sig, h1]
      rw [this, h1, hvk]
    · have : sig (n + k) u i = i - 1 := by
        unfold sig; split_ifs <;> omega
      rw [this, getD_oob _ _ (by omega), getD_oob _ _ (by simp [step]; omega)]
  have hrel := rel_fold (n + k) u hu (E.gates.drop (k + 1)) _ _ hrel0
  rw [hD, hW]
  exact hrel.2.2 E.output

lemma del_length (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) :
    (del n k u E).gates.length + 1 = E.gates.length := by
  simp only [del, List.length_map, List.length_eraseIdx, if_pos hk]
  omega
lemma del_mono (n k u : ℕ) (E : Circuit) (hE : Monotone2 E) : Monotone2 (del n k u E) := by
  intro g hg
  simp only [del, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have := hE g0 (List.mem_of_mem_eraseIdx hg0)
  simpa [rd] using this

lemma gateAt_some (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (gateAt C j) := by
  rw [List.getElem?_eq_getElem hj]
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma readsBack_get (n : ℕ) (C : Circuit) (h : ReadsBack n C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) : ∀ i ∈ g.inputs, i < n + j := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have := gateAt_some C j hj
  rw [hg] at this
  cases this
  exact h j hj

lemma readsBack_of_get (n : ℕ) (C : Circuit)
    (h : ∀ j (g : Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) : ReadsBack n C := by
  intro j hj
  exact h j _ (gateAt_some C j hj)
lemma readsBack_take (n : ℕ) (C : Circuit) (h : ReadsBack n C) (k : ℕ) :
    ∀ g ∈ C.gates.take k, ∀ i ∈ g.inputs, i < n + k := by
  intro g hg i hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  rw [List.getElem_take] at hi
  have hjl : j < k := by simp at hj; omega
  have hj' : j < C.gates.length := by simp at hj; omega
  have := readsBack_get n C h j _ (List.getElem?_eq_getElem hj') i hi
  omega

lemma least_no_and_operand_below (n : ℕ) (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hr : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and)
    (w : ℕ) (hw : w ∈ C.gates[j].inputs) :
    ¬ (∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD w false = true → circuitFun n C x = true) := by
  intro hbelow
  have hwb : w < n + j := readsBack_get n C hr j _ (List.getElem?_eq_getElem hj) w hw
  obtain ⟨hm, hf, hs⟩ := bypass_and n C j w hmin.1 hj hop hw hwb hbelow
  let E : Circuit := ⟨C.gates.set j ⟨GateOp.or, [w]⟩, C.output⟩
  have hE : E.gates[j]? = some ⟨GateOp.or, [w]⟩ := by
    simp [E, List.getElem?_set, hj]
  have hjE : j < E.gates.length := by simpa [E] using hj
  have hpre : ∀ g ∈ E.gates.take j, ∀ i ∈ g.inputs, i < n + j := by
    simpa [E, List.take_set_of_le] using readsBack_take n C hr j
  have hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + j) false = (E.wires (List.ofFn x)).getD w false := by
    intro x
    simpa using wires_copy E j w hE (List.ofFn x) (by simpa using hwb)
  have hdf := del_fun n j w E hjE hwb hpre hcopy
  have hlen := del_length n j w E hjE
  have hle := hmin.2 (del n j w E) (del_mono n j w E hm) (hdf.trans hf)
  change (del n j w E).gates.length + 1 = E.size at hlen
  change C.size ≤ (del n j w E).gates.length at hle
  change E.size = C.size at hs
  omega

end CopyDeletion

end PEqualNP.Outside.L_meta_2448_aux.StarNormal
