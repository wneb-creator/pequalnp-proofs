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

namespace PEqualNP.Outside.L_meta_2448_aux.StarSandwich

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

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

lemma circuit_mono (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  apply mono2 C.gates
  · intro g hg
    simpa using hm g hg
  · simp
  · exact ofFn_mono n x y hxy

lemma graph_sandwich (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hm : Monotone2 D)
    (hbelow : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  refine ⟨hbelow x, ?_⟩
  intro hx
  obtain ⟨u, v, huv, hu, hv⟩ : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simpa [graphFun] using hx
  apply circuit_mono n D hm (pairInput u v) x _ (hedges u v huv)
  intro w hw
  have h : w = u ∨ w = v := of_decide_eq_true hw
  rcases h with rfl | rfl
  · exact hu
  · exact hv

lemma graph_rewrite (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hm : Monotone2 D) (hC : circuitFun n C = graphFun G ∅)
    (hdown : ∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = circuitFun n C := by
  rw [hC]
  apply graph_sandwich n G D hm _ hedges
  intro x hx
  rw [← hC]
  exact hdown x hx

end PEqualNP.Outside.L_meta_2448_aux.StarSandwich

namespace PEqualNP.Outside.L_meta_2448.CoverConstruction

open PEqualNP.CircuitLowerBounds

-- A vertex cover circuit: for each cover vertex c (in increasing order) an OR chain of the
-- neighbours of c not already handled, ANDed with c; the AND gates are ORed together.

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

def V {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ fs.map (fun f => f x)

def Sem {n : ℕ} (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  ∀ x : Fin n → Bool, wf gs (List.ofFn x) = V fs x

def Val {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (i : ℕ) (F : (Fin n → Bool) → Bool) : Prop :=
  i < n + fs.length ∧ ∀ x, (V fs x).getD i false = F x

lemma V_append {n : ℕ} (fs fs' : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    V (fs ++ fs') x = V fs x ++ fs'.map (fun f => f x) := by
  simp [V]

lemma V_length {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    (V fs x).length = n + fs.length := by simp [V]

lemma V_read {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) (j : ℕ)
    (hj : j < fs.length) : (V fs x).getD (n + j) false = fs.getD j (fun _ => false) x := by
  simp only [V]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hj]

lemma val_ext {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ} {F : (Fin n → Bool) → Bool}
    (h : Val fs i F) (fs' : List ((Fin n → Bool) → Bool)) : Val (fs ++ fs') i F := by
  refine ⟨by have := h.1; simp; omega, fun x => ?_⟩
  rw [V_append, List.getD_append _ _ _ _ (by rw [V_length]; exact h.1)]
  exact h.2 x

lemma val_congr {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ}
    {F F' : (Fin n → Bool) → Bool} (h : Val fs i F) (e : ∀ x, F x = F' x) : Val fs i F' :=
  ⟨h.1, fun x => by rw [h.2 x, e x]⟩

lemma val_in {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (a : Fin n) :
    Val fs a.val (fun x => x a) := by
  refine ⟨by omega, fun x => ?_⟩
  simp only [V]
  rw [List.getD_append _ _ _ _ (by simp)]
  simp

lemma val_new {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (f : (Fin n → Bool) → Bool) :
    Val (fs ++ [f]) (n + fs.length) f := by
  refine ⟨by simp, fun x => ?_⟩
  rw [V_read _ _ _ (by simp)]
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

lemma sem_snoc {n : ℕ} {gs : List Gate} {fs : List ((Fin n → Bool) → Bool)} (h : Sem gs fs)
    (op : GateOp) (a b : ℕ) (A B : (Fin n → Bool) → Bool) (ha : Val fs a A) (hb : Val fs b B) :
    Sem (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) := by
  intro x
  rw [wf_snoc, h x, V_append]
  simp only [List.map_cons, List.map_nil, ha.2 x, hb.2 x]

def Mono (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def St {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) (gs : List Gate)
    (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  Sem gs fs ∧ fs.length = gs.length ∧ Mono gs ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ l, P l ∧ ∀ x, fs.getD j (fun _ => false) x = true → x l = true) ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ c v : Fin n, G.Adj c v ∧
      fs.getD j (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = true ∧
      ∀ i < j, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false)

lemma st_nil {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) : St G P [] [] := by
  refine ⟨fun x => by simp [wf, V], rfl, by simp [Mono], ?_, ?_⟩ <;> simp

lemma st_weak {n : ℕ} {G : SimpleGraph (Fin n)} {P Q : Fin n → Prop} {gs fs}
    (h : St G P gs fs) (hPQ : ∀ l, P l → Q l) : St G Q gs fs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, fun j hj hand => ?_, h5⟩
  obtain ⟨l, hl, hl2⟩ := h4 j hj hand
  exact ⟨l, hPQ l hl, hl2⟩

lemma push {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} {gs : List Gate}
    {fs : List ((Fin n → Bool) → Bool)} (h : St G P gs fs) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ) (A B : (Fin n → Bool) → Bool)
    (ha : Val fs a A) (hb : Val fs b B)
    (nA : op = GateOp.and → ∃ l, P l ∧ ∀ x, op.eval [A x, B x] = true → x l = true)
    (nB : op = GateOp.and → ∃ c v : Fin n, G.Adj c v ∧
      op.eval [A (PEqualNP.EdgeOwnership.pairInput c v), B (PEqualNP.EdgeOwnership.pairInput c v)]
        = true ∧
      ∀ i < gs.length, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false) :
    St G P (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) ∧
      Val (fs ++ [fun x => op.eval [A x, B x]]) (n + fs.length) (fun x => op.eval [A x, B x]) := by
  obtain ⟨hs, hl, hm, hA, hB⟩ := h
  refine ⟨⟨sem_snoc hs op a b A B ha hb, by simp [hl], ?_, ?_, ?_⟩, val_new _ _⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hm g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      rcases hop with e | e <;> simp [e]
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      obtain ⟨l, hl1, hl2⟩ := hA j hj hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rwa [List.getD_append _ _ _ _ (by omega)] at hx
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      obtain ⟨l, hl1, hl2⟩ := nA hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rw [← hl, List.getD_append_right _ _ _ _ le_rfl] at hx
      simpa using hx
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      obtain ⟨c, v, hadj, h1, h2⟩ := hB j hj hand
      refine ⟨c, v, hadj, ?_, fun i hi hand' => ?_⟩
      · rw [List.getD_append _ _ _ _ (by omega)]; exact h1
      · rw [List.getD_append _ _ _ _ (by omega)] at hand'
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 i hi hand'
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      obtain ⟨c, v, hadj, h1, h2⟩ := nB hand
      refine ⟨c, v, hadj, ?_, fun i hi hand' => ?_⟩
      · rw [← hl, List.getD_append_right _ _ _ _ le_rfl]
        simpa using h1
      · rw [List.getD_append _ _ _ _ hi] at hand'
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 i hi hand'

lemma chain {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} :
    ∀ (rest : List (Fin n)) (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (a : ℕ)
      (A : (Fin n → Bool) → Bool), St G P gs fs → Val fs a A →
      ∃ gs' fs' o, St G P gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
        gs'.length = gs.length + rest.length ∧
        Val fs' o (fun x => A x || rest.any (fun w => x w))
  | [], gs, fs, a, A, h, ha => ⟨gs, fs, a, h, ⟨[], by simp⟩, by simp, by simpa using ha⟩
  | w :: rest, gs, fs, a, A, h, ha => by
    obtain ⟨h1, h2⟩ := push h GateOp.or (Or.inr rfl) a w.val A (fun x => x w) ha (val_in fs w)
      (fun e => by simp at e) (fun e => by simp at e)
    obtain ⟨gs', fs', o, h3, ⟨fsn, hfs⟩, hlen, hv⟩ := chain rest _ _ _ _ h1 h2
    refine ⟨gs', fs', o, h3, ⟨(fun x => GateOp.or.eval [A x, x w]) :: fsn, by rw [hfs]; simp⟩, ?_, ?_⟩
    · rw [hlen]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    refine ⟨hv.1, fun x => ?_⟩
    rw [hv.2 x]
    simp [GateOp.eval, Bool.or_assoc]

def N {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun w => G.Adj c w ∧ ¬ (w ∈ C ∧ w < c))

def gad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n)
    (x : Fin n → Bool) : Bool :=
  x c && decide (∃ w ∈ N G C c, x w = true)

lemma gad_empty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {c : Fin n} (h : N G C c = ∅) (x : Fin n → Bool) : gad G C c x = false := by
  simp [gad, h]

lemma gadget {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {P : Fin n → Prop} (c : Fin n) (hP : ∀ l, P l → l ∈ C ∧ l < c) (hne : (N G C c).Nonempty)
    (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (h : St G P gs fs) :
    ∃ gs' fs' o, St G (fun l => P l ∨ l = c) gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
      gs'.length = gs.length + (N G C c).card ∧ Val fs' o (gad G C c) := by
  have hL : (N G C c).toList ≠ [] := by
    rw [Ne, Finset.toList_eq_nil]; exact hne.ne_empty
  obtain ⟨w0, rest, hL⟩ := List.exists_cons_of_ne_nil hL
  have hw0 : w0 ∈ N G C c := by
    rw [← Finset.mem_toList, hL]; exact List.mem_cons_self
  have hcard : (N G C c).card = rest.length + 1 := by
    rw [← Finset.length_toList, hL]; simp
  have key : ∀ x : Fin n → Bool,
      (x w0 || rest.any (fun w => x w)) = decide (∃ w ∈ N G C c, x w = true) := by
    intro x
    have : (x w0 || rest.any (fun w => x w)) = (N G C c).toList.any (fun w => x w) := by
      rw [hL]; simp
    rw [this, Bool.eq_iff_iff]
    simp [List.any_eq_true, Finset.mem_toList]
  obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, hv1⟩ :=
    chain rest gs fs w0.val (fun x => x w0) h (val_in fs w0)
  have hlab := h1.2.2.2.1
  have hl1 := h1.2.1
  obtain ⟨h2, hv2⟩ := push (st_weak (Q := fun l => P l ∨ l = c) h1 (fun l hl => Or.inl hl)) GateOp.and (Or.inl rfl) c.val o1
    (fun x => x c) _ (val_in fs1 c) hv1
    (fun _ => ⟨c, Or.inr rfl, fun x hx => by simp [GateOp.eval] at hx; exact hx.1⟩)
    (fun _ => ⟨c, w0, by
        simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw0; exact hw0.1, by
        simp [GateOp.eval, PEqualNP.EdgeOwnership.pairInput], by
        intro i hi hand
        obtain ⟨l, hl, hl2⟩ := hlab i hi hand
        obtain ⟨hlC, hlc⟩ := hP l hl
        cases hval : fs1.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c w0) with
        | false => rfl
        | true =>
          exfalso
          have := hl2 _ hval
          simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at this
          rcases this with rfl | rfl
          · exact lt_irrefl _ hlc
          · simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw0
            exact hw0.2 ⟨hlC, hlc⟩⟩)
  refine ⟨_, _, n + fs1.length, h2, ⟨fsn ++ [fun x => GateOp.and.eval [x c, x w0 || rest.any fun w => x w]], by rw [hfs]; simp⟩, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton, hlen1, hcard]; omega
  refine val_congr hv2 (fun x => ?_)
  simp only [GateOp.eval, gad, ← key x]
  simp

lemma build {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (S : Finset (Fin n)) : S ⊆ C →
    ∃ gs fs, St G (fun l => l ∈ S) gs fs ∧
      ((gs = [] ∧ ∀ c ∈ S, N G C c = ∅) ∨
       ∃ o, Val fs o (fun x => decide (∃ c ∈ S, gad G C c x = true)) ∧
         gs.length + 1 ≤ (∑ c ∈ S, (N G C c).card) + S.card) := by
  induction S using Finset.induction_on_max with
  | empty => intro _; exact ⟨[], [], st_nil G _, Or.inl ⟨rfl, by simp⟩⟩
  | insert c S hlt ih =>
    intro hsub
    have hcS : c ∉ S := fun hc => lt_irrefl _ (hlt c hc)
    obtain ⟨gs, fs, h, hcase⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
    have hP : ∀ l, l ∈ S → l ∈ C ∧ l < c :=
      fun l hl => ⟨hsub (Finset.mem_insert_of_mem hl), hlt l hl⟩
    by_cases hN : N G C c = ∅
    · refine ⟨gs, fs, st_weak h (fun l hl => Finset.mem_insert_of_mem hl), ?_⟩
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · left
        refine ⟨hg, ?_⟩
        intro c' hc'
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · exact hN
        · exact hall c' hc'
      · right
        refine ⟨o, val_congr hv ?_, ?_⟩
        · intro x
          simp [Finset.mem_insert, gad_empty hN]
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]; omega
    · have hne : (N G C c).Nonempty := Finset.nonempty_iff_ne_empty.2 hN
      obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, hv1⟩ := gadget c hP hne gs fs h
      have h1' : St G (fun l => l ∈ insert c S) gs1 fs1 := by
        refine st_weak h1 ?_
        intro l hl
        rcases hl with hl | rfl
        · exact Finset.mem_insert_of_mem hl
        · exact Finset.mem_insert_self _ _
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · refine ⟨gs1, fs1, h1', Or.inr ⟨o1, val_congr hv1 ?_, ?_⟩⟩
        · intro x
          have : ¬ ∃ c' ∈ S, gad G C c' x = true := by
            rintro ⟨c', hc', hg'⟩
            rw [gad_empty (hall c' hc')] at hg'
            exact Bool.false_ne_true hg'
          rw [Bool.eq_iff_iff]
          simp only [decide_eq_true_eq, Finset.mem_insert]
          constructor
          · intro hx; exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact hx
            · exact absurd ⟨c', hc', hx⟩ this
        · subst hg
          rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp at hlen1
          omega
      · obtain ⟨h2, hv2⟩ := push h1' GateOp.or (Or.inr rfl) o o1 _ _
          (by rw [hfs]; exact val_ext hv fsn) hv1 (fun e => by simp at e) (fun e => by simp at e)
        refine ⟨_, _, h2, Or.inr ⟨_, val_congr hv2 ?_, ?_⟩⟩
        · intro x
          rw [Bool.eq_iff_iff]
          simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id,
            Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
          constructor
          · rintro (⟨c', hc', hx⟩ | hx)
            · exact ⟨c', Or.inr hc', hx⟩
            · exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact Or.inr hx
            · exact Or.inl ⟨c', hc', hx⟩
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp only [List.length_append, List.length_singleton]
          omega

lemma edge_N {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) {u v : Fin n} (h : G.Adj u v) :
    ∃ c ∈ C, ∃ w ∈ N G C c, (c = u ∧ w = v) ∨ (c = v ∧ w = u) := by
  simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hC u v h with hu | hv
  · by_cases hv' : v ∈ C ∧ v < u
    · refine ⟨v, hv'.1, u, ⟨h.symm, fun hh => lt_asymm hh.2 hv'.2⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨u, hu, v, ⟨h, hv'⟩, Or.inl ⟨rfl, rfl⟩⟩
  · by_cases hu' : u ∈ C ∧ u < v
    · exact ⟨u, hu'.1, v, ⟨h, fun hh => lt_asymm hh.2 hu'.2⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, hv, u, ⟨h.symm, hu'⟩, Or.inr ⟨rfl, rfl⟩⟩

lemma any_gad {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) (x : Fin n → Bool) :
    decide (∃ c ∈ C, gad G C c x = true) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x := by
  rw [Bool.eq_iff_iff]
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, gad, decide_eq_true_eq,
    Bool.and_eq_true, Bool.or_eq_true, Finset.notMem_empty, false_and, exists_false,
    false_or]
  constructor
  · rintro ⟨c, -, hc, w, hw, hxw⟩
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨c, w, hw.1, hc, hxw⟩
  · rintro ⟨u, v, h, hu, hv⟩
    obtain ⟨c, hc, w, hw, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := edge_N hC h
    · exact ⟨c, hc, hu, w, hw, hv⟩
    · exact ⟨c, hc, hv, w, hw, hu⟩

lemma sumN_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) :
    ∑ c ∈ C, (N G C c).card ≤ G.edgeSet.ncard := by
  rw [← Finset.card_sigma]
  have : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [this]
  apply Finset.card_le_card_of_injOn (fun p => s(p.1, p.2))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hp.2.1
  · rintro ⟨c, w⟩ hp ⟨c', w'⟩ hq hpq
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; rfl
    · exfalso
      subst h1; subst h2
      have e1 : ¬ w < c := fun hl => hp.2.2 ⟨hq.1, hl⟩
      have e2 : ¬ c < w := fun hl => hq.2.2 ⟨hp.1, hl⟩
      have : c = w := le_antisymm (not_lt.1 e1) (not_lt.1 e2)
      subst this
      exact G.irrefl hp.2.1

lemma star_upper (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n))
    (hS : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      D.size ≤ G.edgeSet.ncard + S.card - 1 ∧
      PEqualNP.EdgeOwnership.HasStarProfile n G D := by
  have hS' : ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S := hS
  obtain ⟨gs, fs, ⟨hs, hl, hm, hA, _⟩, hcase⟩ := build G S S (subset_refl _)
  rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
  · subst hg
    refine ⟨⟨[], n⟩, by simp [PEqualNP.MetaComplexity.Monotone2], ?_, by simp [Circuit.size], ?_⟩
    · funext x
      rw [← any_gad hS' x]
      have : ¬ ∃ c ∈ S, gad G S c x = true := by
        rintro ⟨c', hc', hg'⟩
        rw [gad_empty (hall c' hc')] at hg'
        exact Bool.false_ne_true hg'
      simp only [this, decide_false]
      show (wf [] (List.ofFn x)).getD n false = false
      simp only [wf, List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp)
    · intro j hj
      simp at hj
  · refine ⟨⟨gs, o⟩, hm, ?_, ?_, ?_⟩
    · funext x
      show (wf gs (List.ofFn x)).getD o false = _
      rw [hs x, hv.2 x]
      exact any_gad hS' x
    · have h1 := sumN_le G S
      show gs.length ≤ _
      omega
    · intro j hj hand
      have hj' : j < gs.length := hj
      obtain ⟨c, _, hc⟩ := hA j hj' hand
      right
      refine ⟨c, ?_⟩
      intro u v _ hOwn
      have hval := hOwn.2.2.1
      have hval' : fs.getD j (fun _ => false) (PEqualNP.EdgeOwnership.pairInput u v) = true := by
        change (wf gs (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD (n + j) false = true at hval
        rw [hs _, V_read _ _ _ (by omega)] at hval
        exact hval
      have hcenter := hc _ hval'
      have hpair : c = u ∨ c = v := of_decide_eq_true hcenter
      exact hpair.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

lemma least_star_of_cover_lower (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n))
    (hS : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S)
    (lower : ∀ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      G.edgeSet.ncard + S.card - 1 ≤ C.size) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      (∀ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D →
        PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        C.size ≤ D.size) ∧ PEqualNP.EdgeOwnership.HasStarProfile n G C := by
  obtain ⟨C, hC, hf, hs, hp⟩ := star_upper n G S hS
  exact ⟨C, hC, hf, fun D hD hDf => hs.trans (lower D hD hDf), hp⟩


lemma min_cover_exists (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ S : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover G S := by
  classical
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n),
      G.IsVertexCover (S : Set (Fin n)) ∧ S.card = k := by
    refine ⟨n, Finset.univ, ?_, by simp⟩
    intro u v _
    exact Or.inl (by simp)
  obtain ⟨S, hS, hs⟩ := Nat.find_spec hex
  refine ⟨S, hS, ?_⟩
  intro T hT
  rw [hs]
  exact Nat.find_min' hex ⟨T, hT, rfl⟩

lemma posted_of_cover_lower
    (lower : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∀ S : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover G S →
      ∀ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        G.edgeSet.ncard + S.card - 1 ≤ C.size) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6.size ≤ x7.size) ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x6 := by
  intro n G _ htri hfour
  obtain ⟨S, hS⟩ := min_cover_exists n G
  exact least_star_of_cover_lower n G S (fun u v h => hS.1 h)
    (lower n G htri hfour S hS)

end PEqualNP.Outside.L_meta_2448.CoverConstruction

namespace PEqualNP.Outside.L_meta_2448_aux.CriticalRestriction

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

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma circuit_mono (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  apply mono2 C.gates
  · intro g hg
    simpa using hm g hg
  · simp
  · exact ofFn_mono n x y hxy

lemma graph_sandwich (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hm : Monotone2 D)
    (hbelow : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  refine ⟨hbelow x, ?_⟩
  intro hx
  obtain ⟨u, v, huv, hu, hv⟩ : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simpa [graphFun] using hx
  apply circuit_mono n D hm (pairInput u v) x _ (hedges u v huv)
  intro w hw
  have h : w = u ∨ w = v := of_decide_eq_true hw
  rcases h with rfl | rfl
  · exact hu
  · exact hv

lemma graph_rewrite (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hm : Monotone2 D) (hC : circuitFun n C = graphFun G ∅)
    (hdown : ∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = circuitFun n C := by
  rw [hC]
  apply graph_sandwich n G D hm _ hedges
  intro x hx
  rw [← hC]
  exact hdown x hx

lemma set_eval_mono (n j : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hj : j < C.gates.length) (r s : Gate) (x : Fin n → Bool)
    (hle : r.op.eval (r.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) = true →
      s.op.eval (s.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) = true) :
    circuitFun n ⟨C.gates.set j r, C.output⟩ x = true →
    circuitFun n ⟨C.gates.set j s, C.output⟩ x = true := by
  change (wf (C.gates.set j r) (List.ofFn x)).getD C.output false = true →
    (wf (C.gates.set j s) (List.ofFn x)).getD C.output false = true
  have hs : ∀ t : Gate, C.gates.set j t =
      C.gates.take j ++ t :: C.gates.drop (j + 1) := by
    intro t
    rw [List.set_eq_take_append_cons_drop]
    simp [hj]
  rw [hs r, hs s, wf_append, wf_append, wf_cons, wf_cons]
  apply mono2 (C.gates.drop (j + 1))
  · intro g hg
    simpa using hm g (List.mem_of_mem_drop hg)
  · simp
  · exact snoc_mono _ _ _ hle

lemma set_eval_eq (n j : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hj : j < C.gates.length) (r s : Gate) (x : Fin n → Bool)
    (heq : r.op.eval (r.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) =
      s.op.eval (s.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false)) :
    circuitFun n ⟨C.gates.set j r, C.output⟩ x =
    circuitFun n ⟨C.gates.set j s, C.output⟩ x := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨set_eval_mono n j C hm hj r s x (by rw [heq]; exact id),
    set_eval_mono n j C hm hj s r x (by rw [heq]; exact id)⟩

lemma set_gate_val (n j : ℕ) (C : Circuit) (hj : j < C.gates.length)
    (r : Gate) (x : Fin n → Bool) :
    gateVal n ⟨C.gates.set j r, C.output⟩ j x =
      r.op.eval (r.inputs.map fun i =>
        (wf (C.gates.take j) (List.ofFn x)).getD i false) := by
  change (wf (C.gates.set j r) (List.ofFn x)).getD (n + j) false = _
  rw [List.set_eq_take_append_cons_drop]
  simp only [hj, ↓reduceIte]
  rw [wf_append, wf_cons]
  have hl : (wf (C.gates.take j) (List.ofFn x)).length = n + j := by
    rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [wf_keep _ _ _ (by simp [hl]), ← hl, getD_snoc_eq]

lemma restrict_at_pivotal_star (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (hC : circuitFun n C = graphFun G ∅)
    (j a b : ℕ) (hj : j < C.gates.length)
    (hop : C.gates[j].op = GateOp.and) (hin : C.gates[j].inputs = [a,b])
    (c : Fin n)
    (hleft : ∀ x : Fin n → Bool, x c = true →
      (wf (C.gates.take j) (List.ofFn x)).getD a false = true)
    (hpiv : ∀ u v : Fin n, G.Adj u v →
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput u v) = false →
      u = c ∨ v = c) :
    let D : Circuit := ⟨C.gates.set j ⟨GateOp.and, [c.val,b]⟩, C.output⟩
    Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      ∀ u v : Fin n, gateVal n D j (pairInput u v) = true → u = c ∨ v = c := by
  classical
  dsimp only
  let r : Gate := ⟨GateOp.and, [c.val,b]⟩
  let z : Gate := ⟨GateOp.or, []⟩
  let D : Circuit := ⟨C.gates.set j r, C.output⟩
  have hDm : Monotone2 D := by
    intro g hg
    rcases List.mem_or_eq_of_mem_set hg with hg | rfl
    · exact hm g hg
    · simp [r]
  have hinval : ∀ x : Fin n → Bool,
      (wf (C.gates.take j) (List.ofFn x)).getD c.val false = x c := by
    intro x
    rw [wf_keep _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, c.isLt]
  have hsame : (⟨C.gates.set j C.gates[j], C.output⟩ : Circuit) = C := by
    simp
  have hdown : ∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true := by
    intro x
    rw [← hsame]
    apply set_eval_mono n j C hm hj r C.gates[j] x
    simp only [r, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, hinval, hop, hin, Bool.and_eq_true]
    exact fun h => ⟨hleft x h.1, h.2⟩
  have hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true := by
    intro u v huv
    let x := pairInput u v
    have hCx : circuitFun n C x = true := by
      rw [hC]
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨u, v, huv, by simp [x, pairInput], by simp [x, pairInput]⟩
    by_cases hz : circuitFun n ⟨C.gates.set j z, C.output⟩ x = false
    · have hc : x c = true := by
        rcases hpiv u v huv hz with h | h <;> simp [x, pairInput, h]
      have hgtrue : C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
          (wf (C.gates.take j) (List.ofFn x)).getD i false) = true := by
        by_contra h
        have hf := Bool.eq_false_iff.mpr h
        have he := set_eval_eq n j C hm hj C.gates[j] z x (by simpa [z, GateOp.eval] using hf)
        rw [hsame, hCx, hz] at he
        contradiction
      have hrtrue : r.op.eval (r.inputs.map fun i =>
          (wf (C.gates.take j) (List.ofFn x)).getD i false) = true := by
        simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at hgtrue
        simp only [r, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
          List.all_nil, id_eq, Bool.and_true, hinval, hc, hgtrue.2, Bool.and_self]
      have he := set_eval_eq n j C hm hj r C.gates[j] x (hrtrue.trans hgtrue.symm)
      rw [hsame, hCx] at he
      exact he
    · have hztrue : circuitFun n ⟨C.gates.set j z, C.output⟩ x = true :=
        by
          cases hb : circuitFun n ⟨C.gates.set j z, C.output⟩ x <;> simp_all
      exact set_eval_mono n j C hm hj z r x (by simp [z, GateOp.eval]) hztrue
  refine ⟨hDm, graph_sandwich n G D hDm ?_ hedges, by simp [Circuit.size], ?_⟩
  · intro x hx
    rw [← hC]
    exact hdown x hx
  · intro u v h
    rw [set_gate_val n j C hj] at h
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, hinval, Bool.and_eq_true] at h
    have hc : c = u ∨ c = v := of_decide_eq_true h.1
    exact hc.imp Eq.symm Eq.symm

end PEqualNP.Outside.L_meta_2448_aux.CriticalRestriction

namespace PEqualNP.Outside.L_meta_2448_aux.PivotalNecessary

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

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma circuit_mono (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  apply mono2 C.gates
  · intro g hg
    simpa using hm g hg
  · simp
  · exact ofFn_mono n x y hxy

lemma graph_sandwich (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hm : Monotone2 D)
    (hbelow : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  refine ⟨hbelow x, ?_⟩
  intro hx
  obtain ⟨u, v, huv, hu, hv⟩ : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simpa [graphFun] using hx
  apply circuit_mono n D hm (pairInput u v) x _ (hedges u v huv)
  intro w hw
  have h : w = u ∨ w = v := of_decide_eq_true hw
  rcases h with rfl | rfl
  · exact hu
  · exact hv

lemma graph_rewrite (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hm : Monotone2 D) (hC : circuitFun n C = graphFun G ∅)
    (hdown : ∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = circuitFun n C := by
  rw [hC]
  apply graph_sandwich n G D hm _ hedges
  intro x hx
  rw [← hC]
  exact hdown x hx

lemma set_eval_mono (n j : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hj : j < C.gates.length) (r s : Gate) (x : Fin n → Bool)
    (hle : r.op.eval (r.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) = true →
      s.op.eval (s.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) = true) :
    circuitFun n ⟨C.gates.set j r, C.output⟩ x = true →
    circuitFun n ⟨C.gates.set j s, C.output⟩ x = true := by
  change (wf (C.gates.set j r) (List.ofFn x)).getD C.output false = true →
    (wf (C.gates.set j s) (List.ofFn x)).getD C.output false = true
  have hs : ∀ t : Gate, C.gates.set j t =
      C.gates.take j ++ t :: C.gates.drop (j + 1) := by
    intro t
    rw [List.set_eq_take_append_cons_drop]
    simp [hj]
  rw [hs r, hs s, wf_append, wf_append, wf_cons, wf_cons]
  apply mono2 (C.gates.drop (j + 1))
  · intro g hg
    simpa using hm g (List.mem_of_mem_drop hg)
  · simp
  · exact snoc_mono _ _ _ hle

lemma set_eval_eq (n j : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hj : j < C.gates.length) (r s : Gate) (x : Fin n → Bool)
    (heq : r.op.eval (r.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) =
      s.op.eval (s.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false)) :
    circuitFun n ⟨C.gates.set j r, C.output⟩ x =
    circuitFun n ⟨C.gates.set j s, C.output⟩ x := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨set_eval_mono n j C hm hj r s x (by rw [heq]; exact id),
    set_eval_mono n j C hm hj s r x (by rw [heq]; exact id)⟩

lemma set_gate_val (n j : ℕ) (C : Circuit) (hj : j < C.gates.length)
    (r : Gate) (x : Fin n → Bool) :
    gateVal n ⟨C.gates.set j r, C.output⟩ j x =
      r.op.eval (r.inputs.map fun i =>
        (wf (C.gates.take j) (List.ofFn x)).getD i false) := by
  change (wf (C.gates.set j r) (List.ofFn x)).getD (n + j) false = _
  rw [List.set_eq_take_append_cons_drop]
  simp only [hj, ↓reduceIte]
  rw [wf_append, wf_cons]
  have hl : (wf (C.gates.take j) (List.ofFn x)).length = n + j := by
    rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [wf_keep _ _ _ (by simp [hl]), ← hl, getD_snoc_eq]

def shift (m t i : ℕ) : ℕ := if i < m then i else if i = m then t else i - 1

def remap (m t : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift m t)⟩

lemma getD_oob (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma shift_before (m t : ℕ) (w : List Bool) (hw : w.length ≤ m) (ht : m ≤ t) (i : ℕ) :
    w.getD (shift m t i) false = w.getD i false := by
  by_cases hi : i < m
  · simp [shift, hi]
  · by_cases he : i = m
    · subst i
      simp only [shift, lt_self_iff_false, ↓reduceIte]
      rw [getD_oob _ _ (by omega), getD_oob _ _ hw]
    · simp only [shift, hi, he, ↓reduceIte]
      rw [getD_oob _ _ (by omega), getD_oob _ _ (by omega)]

lemma remap_before (m t : ℕ) (gs : List Gate) : ∀ w : List Bool,
    w.length + gs.length ≤ m → m ≤ t → wf (gs.map (remap m t)) w = wf gs w := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro w hw ht
    simp only [List.map_cons, wf_cons]
    have hv : (remap m t g).op.eval ((remap m t g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [remap, List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => shift_before m t w (by simp at hw; omega) ht i
    rw [hv]
    exact ih _ (by simp at hw ⊢; omega) ht

def Rel (m t : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length + 1 ∧ m < a.length ∧
    ∀ i, b.getD (shift m t i) false = a.getD i false

lemma rel_snoc (m t : ℕ) (a b : List Bool) (v : Bool)
    (h : Rel m t a b) (ht : a.length ≤ t) : Rel m t (a ++ [v]) (b ++ [v]) := by
  obtain ⟨hl, hm, hv⟩ := h
  refine ⟨by simp [hl], by simp; omega, ?_⟩
  intro i
  by_cases he : i = m
  · subst i
    have hzero : a.getD m false = false := by
      have hvm := hv m
      simp only [shift, lt_self_iff_false, ↓reduceIte] at hvm
      rw [getD_oob b t (by omega)] at hvm
      exact hvm.symm
    simp only [shift, lt_self_iff_false, ↓reduceIte]
    rw [getD_oob _ _ (by simp; omega), getD_snoc_lt _ _ _ hm, hzero]
  · rcases Nat.lt_trichotomy i a.length with hi | hi | hi
    · have hs : shift m t i < b.length := by
        unfold shift
        split_ifs <;> omega
      rw [getD_snoc_lt _ _ _ hs, getD_snoc_lt _ _ _ hi, hv]
    · have hs : shift m t i = b.length := by
        unfold shift
        split_ifs <;> omega
      rw [hs, getD_snoc_eq, hi, getD_snoc_eq]
    · have hs : b.length < shift m t i := by
        unfold shift
        split_ifs <;> omega
      rw [getD_snoc_gt _ _ _ hs, getD_snoc_gt _ _ _ hi]

lemma rel_fold (m t : ℕ) (gs : List Gate) : ∀ a b : List Bool,
    Rel m t a b → a.length + gs.length ≤ t →
      Rel m t (wf gs a) (wf (gs.map (remap m t)) b) := by
  induction gs with
  | nil => intro a b h _; exact h
  | cons g gs ih =>
    intro a b h ht
    simp only [List.map_cons, wf_cons]
    have hv : (remap m t g).op.eval ((remap m t g).inputs.map fun i => b.getD i false) =
        g.op.eval (g.inputs.map fun i => a.getD i false) := by
      simp only [remap, List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => h.2.2 i
    rw [hv]
    apply ih
    · exact rel_snoc m t a b _ h (by simp at ht; omega)
    · simp at ht ⊢; omega

def eraseZero (n k : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx k).map (remap (n + k) (n + C.gates.length)),
    shift (n + k) (n + C.gates.length) C.output⟩

lemma eraseZero_fun (n k : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    circuitFun n (eraseZero n k C) =
      circuitFun n ⟨C.gates.set k ⟨GateOp.or, []⟩, C.output⟩ := by
  funext x
  let w := wf (C.gates.take k) (List.ofFn x)
  have hl : w.length = n + k := by
    simp [w, wf_len, List.length_take, Nat.min_eq_left hk.le]
  have hpre : wf ((C.gates.take k).map (remap (n + k) (n + C.gates.length)))
      (List.ofFn x) = w := by
    apply remap_before
    · simp [List.length_take, Nat.min_eq_left hk.le]
    · omega
  have hzero : Rel (n + k) (n + C.gates.length) (w ++ [false]) w := by
    refine ⟨by simp, by simp [hl], ?_⟩
    intro i
    rcases Nat.lt_trichotomy i (n + k) with hi | hi | hi
    · simp only [shift, hi, ↓reduceIte]
      exact (getD_snoc_lt w false i (by omega)).symm
    · subst i
      simp only [shift, lt_self_iff_false, ↓reduceIte]
      rw [getD_oob _ _ (by omega), ← hl, getD_snoc_eq]
    · have hs : shift (n + k) (n + C.gates.length) i = i - 1 := by
        unfold shift
        split_ifs <;> omega
      rw [hs, getD_oob _ _ (by omega), getD_snoc_gt _ _ _ (by omega)]
  have hrel := rel_fold (n + k) (n + C.gates.length) (C.gates.drop (k + 1))
    (w ++ [false]) w hzero (by simp [hl, List.length_drop]; omega)
  change (wf (eraseZero n k C).gates (List.ofFn x)).getD
      (eraseZero n k C).output false =
    (wf (C.gates.set k ⟨GateOp.or, []⟩) (List.ofFn x)).getD C.output false
  simp only [eraseZero, List.eraseIdx_eq_take_drop_succ, List.map_append, wf_append, hpre]
  rw [List.set_eq_take_append_cons_drop]
  simp only [hk, ↓reduceIte, wf_append, wf_cons, GateOp.eval, List.map_nil,
    List.any_nil]
  exact hrel.2.2 C.output

lemma eraseZero_mono (n k : ℕ) (C : Circuit) (hm : Monotone2 C) :
    Monotone2 (eraseZero n k C) := by
  intro g hg
  simp only [eraseZero, List.mem_map] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  simpa [remap] using hm h (List.mem_of_mem_eraseIdx hh)

lemma eraseZero_size (n k : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    (eraseZero n k C).size + 1 = C.size := by
  simp only [Circuit.size, eraseZero, List.length_map, List.length_eraseIdx, hk, ↓reduceIte]
  omega

lemma every_gate_has_pivotal_edge (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (hfun : circuitFun n C = graphFun G ∅)
    (hmin : ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ u v : Fin n, G.Adj u v ∧
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput u v) = false := by
  classical
  by_contra hnone
  let z : Gate := ⟨GateOp.or, []⟩
  let Z : Circuit := ⟨C.gates.set j z, C.output⟩
  have hZm : Monotone2 Z := by
    intro g hg
    rcases List.mem_or_eq_of_mem_set hg with hg | rfl
    · exact hm g hg
    · simp [z]
  have hsame : (⟨C.gates.set j C.gates[j], C.output⟩ : Circuit) = C := by simp
  have hZf : circuitFun n Z = graphFun G ∅ := by
    apply graph_sandwich n G Z hZm
    · intro x hx
      rw [← hfun]
      rw [← hsame]
      exact set_eval_mono n j C hm hj z C.gates[j] x (by simp [z, GateOp.eval]) hx
    · intro u v huv
      cases h : circuitFun n Z (pairInput u v) with
      | true => rfl
      | false => exact (hnone ⟨u, v, huv, h⟩).elim
  have hd := hmin (eraseZero n j C) (eraseZero_mono n j C hm)
    ((eraseZero_fun n j C hj).trans hZf)
  have hs := eraseZero_size n j C hj
  omega

end PEqualNP.Outside.L_meta_2448_aux.PivotalNecessary

namespace PEqualNP.Outside.L_meta_2448_aux.PivotalUnique

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

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma circuit_mono (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  apply mono2 C.gates
  · intro g hg
    simpa using hm g hg
  · simp
  · exact ofFn_mono n x y hxy

lemma graph_sandwich (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hm : Monotone2 D)
    (hbelow : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  refine ⟨hbelow x, ?_⟩
  intro hx
  obtain ⟨u, v, huv, hu, hv⟩ : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simpa [graphFun] using hx
  apply circuit_mono n D hm (pairInput u v) x _ (hedges u v huv)
  intro w hw
  have h : w = u ∨ w = v := of_decide_eq_true hw
  rcases h with rfl | rfl
  · exact hu
  · exact hv

lemma graph_rewrite (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hm : Monotone2 D) (hC : circuitFun n C = graphFun G ∅)
    (hdown : ∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = circuitFun n C := by
  rw [hC]
  apply graph_sandwich n G D hm _ hedges
  intro x hx
  rw [← hC]
  exact hdown x hx

lemma set_eval_mono (n j : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hj : j < C.gates.length) (r s : Gate) (x : Fin n → Bool)
    (hle : r.op.eval (r.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) = true →
      s.op.eval (s.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) = true) :
    circuitFun n ⟨C.gates.set j r, C.output⟩ x = true →
    circuitFun n ⟨C.gates.set j s, C.output⟩ x = true := by
  change (wf (C.gates.set j r) (List.ofFn x)).getD C.output false = true →
    (wf (C.gates.set j s) (List.ofFn x)).getD C.output false = true
  have hs : ∀ t : Gate, C.gates.set j t =
      C.gates.take j ++ t :: C.gates.drop (j + 1) := by
    intro t
    rw [List.set_eq_take_append_cons_drop]
    simp [hj]
  rw [hs r, hs s, wf_append, wf_append, wf_cons, wf_cons]
  apply mono2 (C.gates.drop (j + 1))
  · intro g hg
    simpa using hm g (List.mem_of_mem_drop hg)
  · simp
  · exact snoc_mono _ _ _ hle

lemma set_eval_eq (n j : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hj : j < C.gates.length) (r s : Gate) (x : Fin n → Bool)
    (heq : r.op.eval (r.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) =
      s.op.eval (s.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false)) :
    circuitFun n ⟨C.gates.set j r, C.output⟩ x =
    circuitFun n ⟨C.gates.set j s, C.output⟩ x := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨set_eval_mono n j C hm hj r s x (by rw [heq]; exact id),
    set_eval_mono n j C hm hj s r x (by rw [heq]; exact id)⟩

lemma set_gate_val (n j : ℕ) (C : Circuit) (hj : j < C.gates.length)
    (r : Gate) (x : Fin n → Bool) :
    gateVal n ⟨C.gates.set j r, C.output⟩ j x =
      r.op.eval (r.inputs.map fun i =>
        (wf (C.gates.take j) (List.ofFn x)).getD i false) := by
  change (wf (C.gates.set j r) (List.ofFn x)).getD (n + j) false = _
  rw [List.set_eq_take_append_cons_drop]
  simp only [hj, ↓reduceIte]
  rw [wf_append, wf_cons]
  have hl : (wf (C.gates.take j) (List.ofFn x)).length = n + j := by
    rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [wf_keep _ _ _ (by simp [hl]), ← hl, getD_snoc_eq]

lemma replace_by_pivotal_pair (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (hfun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (u v : Fin n) (huv : G.Adj u v)
    (hcritical : circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
      (pairInput u v) = false)
    (hunique : ∀ a b : Fin n, G.Adj a b →
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput a b) = false →
      (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    let D : Circuit := ⟨C.gates.set j ⟨GateOp.and, [u.val, v.val]⟩, C.output⟩
    Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      ∀ a b : Fin n, gateVal n D j (pairInput a b) = true → a = u ∨ b = u := by
  classical
  dsimp only
  let z : Gate := ⟨GateOp.or, []⟩
  let r : Gate := ⟨GateOp.and, [u.val, v.val]⟩
  let D : Circuit := ⟨C.gates.set j r, C.output⟩
  let V (x : Fin n → Bool) := C.gates[j].op.eval
    (C.gates[j].inputs.map fun i => (wf (C.gates.take j) (List.ofFn x)).getD i false)
  have hsame : (⟨C.gates.set j C.gates[j], C.output⟩ : Circuit) = C := by simp
  have hVm : ∀ x, gateVal n C j x = V x := by
    intro x
    have h := set_gate_val n j C hj C.gates[j] x
    rw [hsame] at h
    exact h
  have hinput : ∀ (x : Fin n → Bool) (t : Fin n),
      (wf (C.gates.take j) (List.ofFn x)).getD t.val false = x t := by
    intro x t
    rw [wf_keep _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, t.isLt]
  have hedge : ∀ a b : Fin n, G.Adj a b → circuitFun n C (pairInput a b) = true := by
    intro a b hab
    rw [hfun]
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
  have pivotal_value : ∀ a b : Fin n, G.Adj a b →
      circuitFun n ⟨C.gates.set j z, C.output⟩ (pairInput a b) = false →
      V (pairInput a b) = true := by
    intro a b hab hp
    by_contra hn
    have hf := Bool.eq_false_iff.mpr hn
    have he := set_eval_eq n j C hm hj C.gates[j] z (pairInput a b)
      (by change V (pairInput a b) = false; exact hf)
    rw [hsame, hedge a b hab, hp] at he
    contradiction
  have hVuv := pivotal_value u v huv hcritical
  have hdown_value : ∀ x : Fin n → Bool,
      r.op.eval (r.inputs.map fun i =>
        (wf (C.gates.take j) (List.ofFn x)).getD i false) = true → V x = true := by
    intro x hx
    simp only [r, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, hinput, Bool.and_eq_true] at hx
    have hxy : ∀ w : Fin n, pairInput u v w = true → x w = true := by
      intro w hw
      rcases of_decide_eq_true hw with h | h
      · simpa only [h] using hx.1
      · simpa only [h] using hx.2
    have hstart : circuitFun n ⟨C.gates, n + j⟩ (pairInput u v) = true := by
      change gateVal n C j (pairInput u v) = true
      rw [hVm]
      exact hVuv
    have hend := circuit_mono n ⟨C.gates, n + j⟩ hm (pairInput u v) x hxy hstart
    change gateVal n C j x = true at hend
    rwa [hVm] at hend
  have hDm : Monotone2 D := by
    intro g hg
    rcases List.mem_or_eq_of_mem_set hg with hg | rfl
    · exact hm g hg
    · simp [r]
  have hdown : ∀ x, circuitFun n D x = true → circuitFun n C x = true := by
    intro x hx
    rw [← hsame]
    exact set_eval_mono n j C hm hj r C.gates[j] x (hdown_value x) hx
  have hedges : ∀ a b : Fin n, G.Adj a b → circuitFun n D (pairInput a b) = true := by
    intro a b hab
    by_cases hp : circuitFun n ⟨C.gates.set j z, C.output⟩ (pairInput a b) = false
    · have hv := pivotal_value a b hab hp
      have hr : r.op.eval (r.inputs.map fun i =>
          (wf (C.gates.take j) (List.ofFn (pairInput a b))).getD i false) = true := by
        rcases hunique a b hab hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [r, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.and_true, hinput] <;> simp [pairInput]
      have he := set_eval_eq n j C hm hj r C.gates[j] (pairInput a b) (hr.trans hv.symm)
      rw [hsame, hedge a b hab] at he
      exact he
    · have hz : circuitFun n ⟨C.gates.set j z, C.output⟩ (pairInput a b) = true := by
        cases he : circuitFun n ⟨C.gates.set j z, C.output⟩ (pairInput a b) <;> simp_all
      exact set_eval_mono n j C hm hj z r (pairInput a b) (by simp [z, GateOp.eval]) hz
  refine ⟨hDm, graph_sandwich n G D hDm ?_ hedges, by simp [Circuit.size], ?_⟩
  · intro x hx
    rw [← hfun]
    exact hdown x hx
  · intro a b h
    rw [set_gate_val n j C hj] at h
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, hinput, Bool.and_eq_true] at h
    have hu : u = a ∨ u = b := of_decide_eq_true h.1
    exact hu.imp Eq.symm Eq.symm

end PEqualNP.Outside.L_meta_2448_aux.PivotalUnique

namespace PEqualNP.Outside.L_meta_2448_aux.TwoLeafRepair

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

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma circuit_mono (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  apply mono2 C.gates
  · intro g hg
    simpa using hm g hg
  · simp
  · exact ofFn_mono n x y hxy

lemma graph_sandwich (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hm : Monotone2 D)
    (hbelow : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  refine ⟨hbelow x, ?_⟩
  intro hx
  obtain ⟨u, v, huv, hu, hv⟩ : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simpa [graphFun] using hx
  apply circuit_mono n D hm (pairInput u v) x _ (hedges u v huv)
  intro w hw
  have h : w = u ∨ w = v := of_decide_eq_true hw
  rcases h with rfl | rfl
  · exact hu
  · exact hv

lemma graph_rewrite (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hm : Monotone2 D) (hC : circuitFun n C = graphFun G ∅)
    (hdown : ∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = circuitFun n C := by
  rw [hC]
  apply graph_sandwich n G D hm _ hedges
  intro x hx
  rw [← hC]
  exact hdown x hx

lemma set_eval_mono (n j : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hj : j < C.gates.length) (r s : Gate) (x : Fin n → Bool)
    (hle : r.op.eval (r.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) = true →
      s.op.eval (s.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) = true) :
    circuitFun n ⟨C.gates.set j r, C.output⟩ x = true →
    circuitFun n ⟨C.gates.set j s, C.output⟩ x = true := by
  change (wf (C.gates.set j r) (List.ofFn x)).getD C.output false = true →
    (wf (C.gates.set j s) (List.ofFn x)).getD C.output false = true
  have hs : ∀ t : Gate, C.gates.set j t =
      C.gates.take j ++ t :: C.gates.drop (j + 1) := by
    intro t
    rw [List.set_eq_take_append_cons_drop]
    simp [hj]
  rw [hs r, hs s, wf_append, wf_append, wf_cons, wf_cons]
  apply mono2 (C.gates.drop (j + 1))
  · intro g hg
    simpa using hm g (List.mem_of_mem_drop hg)
  · simp
  · exact snoc_mono _ _ _ hle

lemma set_eval_eq (n j : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hj : j < C.gates.length) (r s : Gate) (x : Fin n → Bool)
    (heq : r.op.eval (r.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) =
      s.op.eval (s.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false)) :
    circuitFun n ⟨C.gates.set j r, C.output⟩ x =
    circuitFun n ⟨C.gates.set j s, C.output⟩ x := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨set_eval_mono n j C hm hj r s x (by rw [heq]; exact id),
    set_eval_mono n j C hm hj s r x (by rw [heq]; exact id)⟩

lemma set_gate_val (n j : ℕ) (C : Circuit) (hj : j < C.gates.length)
    (r : Gate) (x : Fin n → Bool) :
    gateVal n ⟨C.gates.set j r, C.output⟩ j x =
      r.op.eval (r.inputs.map fun i =>
        (wf (C.gates.take j) (List.ofFn x)).getD i false) := by
  change (wf (C.gates.set j r) (List.ofFn x)).getD (n + j) false = _
  rw [List.set_eq_take_append_cons_drop]
  simp only [hj, ↓reduceIte]
  rw [wf_append, wf_cons]
  have hl : (wf (C.gates.take j) (List.ofFn x)).length = n + j := by
    rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [wf_keep _ _ _ (by simp [hl]), ← hl, getD_snoc_eq]

lemma replace_by_two_singletons (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (hC : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (u v : Fin n)
    (hu : gateVal n C j (pairInput u u) = true)
    (hv : gateVal n C j (pairInput v v) = true)
    (hpiv : ∀ a b : Fin n, G.Adj a b →
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput a b) = false →
      a = u ∨ b = u ∨ a = v ∨ b = v) :
    let D : Circuit := ⟨C.gates.set j ⟨GateOp.or, [u.val,v.val]⟩, C.output⟩
    Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      (gateAt D j).op = GateOp.or := by
  classical
  dsimp only
  let r : Gate := ⟨GateOp.or, [u.val,v.val]⟩
  let z : Gate := ⟨GateOp.or, []⟩
  let D : Circuit := ⟨C.gates.set j r, C.output⟩
  have hDm : Monotone2 D := by
    intro g hg
    rcases List.mem_or_eq_of_mem_set hg with hg | rfl
    · exact hm g hg
    · simp [r]
  have hinval : ∀ x : Fin n → Bool, ∀ c : Fin n,
      (wf (C.gates.take j) (List.ofFn x)).getD c.val false = x c := by
    intro x c
    rw [wf_keep _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, c.isLt]
  have hsame : (⟨C.gates.set j C.gates[j], C.output⟩ : Circuit) = C := by simp
  have hlocal : ∀ x : Fin n → Bool,
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        (wf (C.gates.take j) (List.ofFn x)).getD i false) = gateVal n C j x := by
    intro x
    have h := set_gate_val n j C hj C.gates[j] x
    rw [hsame] at h
    exact h.symm
  have hsingle : ∀ x : Fin n → Bool, x u = true ∨ x v = true → gateVal n C j x = true := by
    intro x hx
    rcases hx with hx | hx
    · apply circuit_mono n ⟨C.gates, n + j⟩ hm (pairInput u u) x _ hu
      intro w hw
      have hwu : w = u := by simpa [pairInput] using hw
      simpa [hwu] using hx
    · apply circuit_mono n ⟨C.gates, n + j⟩ hm (pairInput v v) x _ hv
      intro w hw
      have hwv : w = v := by simpa [pairInput] using hw
      simpa [hwv] using hx
  have hdown : ∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true := by
    intro x
    rw [← hsame]
    apply set_eval_mono n j C hm hj r C.gates[j] x
    rw [hlocal]
    simp only [r, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, id_eq, Bool.or_false, hinval, Bool.or_eq_true]
    exact hsingle x
  have hedges : ∀ a b : Fin n, G.Adj a b → circuitFun n D (pairInput a b) = true := by
    intro a b hab
    let x := pairInput a b
    have hCx : circuitFun n C x = true := by
      rw [hC]
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨a, b, hab, by simp [x, pairInput], by simp [x, pairInput]⟩
    by_cases hz : circuitFun n ⟨C.gates.set j z, C.output⟩ x = false
    · have huv : x u = true ∨ x v = true := by
        rcases hpiv a b hab hz with h | h | h | h <;> simp [x, pairInput, h]
      have hrtrue : r.op.eval (r.inputs.map fun i =>
          (wf (C.gates.take j) (List.ofFn x)).getD i false) = true := by
        simpa only [r, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
          List.any_nil, id_eq, Bool.or_false, hinval, Bool.or_eq_true] using huv
      have hgtrue : C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
          (wf (C.gates.take j) (List.ofFn x)).getD i false) = true := by
        rw [hlocal]
        exact hsingle x huv
      have he := set_eval_eq n j C hm hj r C.gates[j] x (hrtrue.trans hgtrue.symm)
      rw [hsame, hCx] at he
      exact he
    · have hztrue : circuitFun n ⟨C.gates.set j z, C.output⟩ x = true := by
        cases hb : circuitFun n ⟨C.gates.set j z, C.output⟩ x <;> simp_all
      exact set_eval_mono n j C hm hj z r x (by simp [z, GateOp.eval]) hztrue
  refine ⟨hDm, graph_sandwich n G D hDm ?_ hedges, by simp [Circuit.size], ?_⟩
  · intro x hx
    rw [← hC]
    exact hdown x hx
  · simp [gateAt, List.getD_eq_getElem?_getD, hj]

end PEqualNP.Outside.L_meta_2448_aux.TwoLeafRepair

namespace PEqualNP.Outside.L_meta_2448_aux.MatchingExchange

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

open PEqualNP.EdgeOwnership

lemma matching_identity (a b c d : Bool) :
    (((a || c) && (b || d)) && ((a || d) && (b || c))) =
      ((a && b) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

set_option maxHeartbeats 800000 in
lemma closed_pair_exchange (n : ℕ) (C D : Circuit) (g h t : ℕ)
    (a b c d : Fin n) (hlen : D.gates.length = C.gates.length)
    (hgt : g < t) (hht : h < t) (_hgh : g ≠ h) (ht : t < C.gates.length)
    (hDg : D.gates[g] = ⟨GateOp.and, [a.val,b.val]⟩)
    (hDh : D.gates[h] = ⟨GateOp.and, [c.val,d.val]⟩)
    (hDt : D.gates[t] = ⟨GateOp.or, [n+g,n+h]⟩)
    (hCt : C.gates[t] = ⟨GateOp.and, [n+g,n+h]⟩)
    (hkeep : ∀ k (hk : k < C.gates.length), k ≠ g → k ≠ h → k ≠ t →
      D.gates[k] = C.gates[k])
    (hread : ∀ k (hk : k < C.gates.length), k ≠ t →
      n + g ∉ C.gates[k].inputs ∧ n + h ∉ C.gates[k].inputs)
    (hout : D.output = C.output) (hog : C.output ≠ n+g) (hoh : C.output ≠ n+h)
    (hpair : ∀ x : Fin n → Bool,
      (gateVal n C g x && gateVal n C h x) = ((x a && x b) || (x c && x d))) :
    circuitFun n D = circuitFun n C := by
  funext x
  have hgC : g < C.gates.length := by omega
  have hhC : h < C.gates.length := by omega
  have hgD : g < D.gates.length := by omega
  have hhD : h < D.gates.length := by omega
  have htD : t < D.gates.length := by omega
  have hinput : ∀ (gs : List Gate) (i : Fin n),
      (wf gs (List.ofFn x)).getD i.val false = x i := by
    intro gs i
    rw [wf_keep _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, i.isLt]
  have hall : ∀ k, k ≤ C.gates.length →
      (∀ w, w ≠ n+g → w ≠ n+h →
        (wf (D.gates.take k) (List.ofFn x)).getD w false =
        (wf (C.gates.take k) (List.ofFn x)).getD w false) ∧
      (g < k → (wf (D.gates.take k) (List.ofFn x)).getD (n+g) false = (x a && x b)) ∧
      (h < k → (wf (D.gates.take k) (List.ofFn x)).getD (n+h) false = (x c && x d)) := by
    intro k
    induction k with
    | zero => intro hk; exact ⟨fun _ _ _ => rfl, by omega, by omega⟩
    | succ k ih =>
      intro hk
      have hkC : k < C.gates.length := by omega
      have hkD : k < D.gates.length := by omega
      obtain ⟨ihw, ihg, ihh⟩ := ih (by omega)
      have hlC : (wf (C.gates.take k) (List.ofFn x)).length = n+k := by
        simp [wf_len, List.length_take, Nat.min_eq_left hkC.le]
      have hlD : (wf (D.gates.take k) (List.ofFn x)).length = n+k := by
        simp [wf_len, List.length_take, Nat.min_eq_left hkD.le]
      have hval : k ≠ g → k ≠ h →
          D.gates[k].op.eval (D.gates[k].inputs.map fun i =>
            (wf (D.gates.take k) (List.ofFn x)).getD i false) =
          C.gates[k].op.eval (C.gates[k].inputs.map fun i =>
            (wf (C.gates.take k) (List.ofFn x)).getD i false) := by
        intro hkg hkh
        by_cases hkt : k = t
        · subst k
          rw [hDt, hCt]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
          rw [ihg hgt, ihh hht]
          have eg := wire_take C.gates (List.ofFn x) t (n+g)
            (by simp; omega) (by omega)
          have eh := wire_take C.gates (List.ofFn x) t (n+h)
            (by simp; omega) (by omega)
          rw [← eg, ← eh]
          exact (hpair x).symm
        · rw [hkeep k hkC hkg hkh hkt]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact ihw i (fun e => (hread k hkC hkt).1 (e ▸ hi))
            (fun e => (hread k hkC hkt).2 (e ▸ hi))
      rw [List.take_succ_eq_append_getElem hkD, List.take_succ_eq_append_getElem hkC,
        wf_snoc, wf_snoc]
      refine ⟨?_, ?_, ?_⟩
      · intro w hwg hwh
        rcases Nat.lt_trichotomy w (n+k) with hw | hw | hw
        · rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
          exact ihw w hwg hwh
        · rw [hw, ← hlD, getD_snoc_eq, hlD, ← hlC, getD_snoc_eq]
          exact hval (by omega) (by omega)
        · rw [getD_snoc_gt _ _ _ (by omega), getD_snoc_gt _ _ _ (by omega)]
      · intro hgk
        by_cases hg : g < k
        · rw [getD_snoc_lt _ _ _ (by omega)]
          exact ihg hg
        · have hg : g = k := by omega
          subst k
          rw [← hlD, getD_snoc_eq, hDg]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.and_true, hinput]
      · intro hhk
        by_cases hh : h < k
        · rw [getD_snoc_lt _ _ _ (by omega)]
          exact ihh hh
        · have hh : h = k := by omega
          subst k
          rw [← hlD, getD_snoc_eq, hDh]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.and_true, hinput]
  have he := (hall C.gates.length (by rfl)).1 C.output hog hoh
  rw [← hlen, List.take_length, hlen, List.take_length] at he
  change (wf D.gates (List.ofFn x)).getD D.output false = _
  rw [hout]
  exact he

lemma gate_val_eq (n j : ℕ) (C : Circuit) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    gateVal n C j x = C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) := by
  change (wf C.gates (List.ofFn x)).getD (n+j) false = _
  have hs : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by
    have hs : C.gates.set j C.gates[j] =
        C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by
      rw [List.set_eq_take_append_cons_drop]
      simp [hj]
    simpa using hs
  conv_lhs => rw [hs]
  rw [wf_append, wf_cons]
  have hl : (wf (C.gates.take j) (List.ofFn x)).length = n+j := by
    simp [wf_len, List.length_take, Nat.min_eq_left hj.le]
  rw [wf_keep _ _ _ (by simp [hl]), ← hl, getD_snoc_eq]

set_option maxHeartbeats 800000 in
lemma repair_two_rectangles (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (g h t : ℕ) (a b c d : Fin n)
    (hgt : g < t) (hht : h < t) (hgh : g ≠ h) (ht : t < C.gates.length)
    (hCt : C.gates[t] = ⟨GateOp.and, [n+g,n+h]⟩)
    (hread : ∀ k (hk : k < C.gates.length), k ≠ t →
      n + g ∉ C.gates[k].inputs ∧ n + h ∉ C.gates[k].inputs)
    (hog : C.output ≠ n+g) (hoh : C.output ≠ n+h)
    (hgfun : ∀ x : Fin n → Bool,
      gateVal n C g x = ((x a || x c) && (x b || x d)))
    (hhfun : ∀ x : Fin n → Bool,
      gateVal n C h x = ((x a || x d) && (x b || x c))) :
    let D : Circuit := ⟨((C.gates.set g ⟨GateOp.and, [a.val,b.val]⟩).set h
      ⟨GateOp.and, [c.val,d.val]⟩).set t ⟨GateOp.or, [n+g,n+h]⟩, C.output⟩
    Monotone2 D ∧ circuitFun n D = circuitFun n C ∧ D.size = C.size ∧
      (∀ u v : Fin n, gateVal n D g (pairInput u v) = true → u = a ∨ v = a) ∧
      (∀ u v : Fin n, gateVal n D h (pairInput u v) = true → u = c ∨ v = c) := by
  classical
  dsimp only
  let D : Circuit := ⟨((C.gates.set g ⟨GateOp.and, [a.val,b.val]⟩).set h
    ⟨GateOp.and, [c.val,d.val]⟩).set t ⟨GateOp.or, [n+g,n+h]⟩, C.output⟩
  have hgC : g < C.gates.length := by omega
  have hhC : h < C.gates.length := by omega
  have hlen : D.gates.length = C.gates.length := by simp [D]
  have hgD : g < D.gates.length := by omega
  have hhD : h < D.gates.length := by omega
  have htD : t < D.gates.length := by omega
  have hDg : D.gates[g] = ⟨GateOp.and, [a.val,b.val]⟩ := by
    simp [D, List.getElem_set, Ne.symm hgh, show t ≠ g by omega]
  have hDh : D.gates[h] = ⟨GateOp.and, [c.val,d.val]⟩ := by
    simp [D, List.getElem_set, show t ≠ h by omega]
  have hDt : D.gates[t] = ⟨GateOp.or, [n+g,n+h]⟩ := by simp [D]
  have hDm : Monotone2 D := by
    intro k hk
    rcases List.mem_or_eq_of_mem_set hk with hk | rfl
    · rcases List.mem_or_eq_of_mem_set hk with hk | rfl
      · rcases List.mem_or_eq_of_mem_set hk with hk | rfl
        · exact hm k hk
        · simp
      · simp
    · simp
  have hfun : circuitFun n D = circuitFun n C := by
    apply closed_pair_exchange n C D g h t a b c d hlen hgt hht hgh ht hDg hDh hDt hCt
    · intro k hk hkg hkh hkt
      simp [D, List.getElem_set, Ne.symm hkg, Ne.symm hkh, Ne.symm hkt]
    · exact hread
    · rfl
    · exact hog
    · exact hoh
    · intro x
      rw [hgfun, hhfun]
      exact matching_identity _ _ _ _
  have hinput : ∀ (x : Fin n → Bool) (gs : List Gate) (i : Fin n),
      (wf gs (List.ofFn x)).getD i.val false = x i := by
    intro x gs i
    rw [wf_keep _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, i.isLt]
  refine ⟨hDm, hfun, by simp [Circuit.size], ?_, ?_⟩
  · intro u v h
    rw [gate_val_eq n g D hgD, hDg] at h
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, hinput, Bool.and_eq_true] at h
    have ha : a = u ∨ a = v := of_decide_eq_true h.1
    exact ha.imp Eq.symm Eq.symm
  · intro u v hp
    rw [gate_val_eq n h D hhD, hDh] at hp
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, hinput, Bool.and_eq_true] at hp
    have hc : c = u ∨ c = v := of_decide_eq_true hp.1
    exact hc.imp Eq.symm Eq.symm

end PEqualNP.Outside.L_meta_2448_aux.MatchingExchange

namespace PEqualNP.Outside.L_meta_2448_aux.BackwardNormalize

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext n new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext n new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma rb_snoc {n : ℕ} {new : List Gate} {h : Gate} (hrb : RB n new)
    (hh : ∀ i ∈ h.inputs, i < n + new.length) : RB n (new ++ [h]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < new.length
  · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD, List.getElem?_append_left hlt]
    rw [e] at hi
    exact hrb j hlt i hi
  · have hj' : j = new.length := by omega
    subst hj'
    have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
    rw [e] at hi
    exact hh i hi

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ RB n new ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

lemma inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv ρ old) : Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hrb, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, _, hkb⟩
    · exact hrb
    · exact rb_snoc hrb hkb
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_pos ht]) hr
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_neg ht]) (rep_mono he _ (hrep t))

lemma inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv ρ pre → Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, (by intro j hj; simp at hj), le_refl _, rep_input ρ hρ⟩

lemma eval_eq {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = (W gs x).getD o false := rfl

lemma normalize_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin n → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ C'.size ≤ C.size := by
  intro n G inst C hm hC
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    have h := hm g hgm
    refine ⟨?_, h.2⟩
    have h1 := h.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  obtain ⟨new, hfan, hrb, hl, hrep⟩ :=
    inv_all (fun (x : Fin n → Bool) => x) (fun i => Or.inr (fun x => rfl)) C.gates hg
  have hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = (W C.gates x).getD C.output false :=
    fun x => rfl
  have hgf : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x
      = C.eval (List.ofFn x) := by
    intro x
    rw [Bool.eq_iff_iff, hC x]
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
  rcases hrep C.output with ⟨c, hc⟩ | ⟨j, _, hj⟩
  · have hc' : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = c := fun x => (hev x).trans (hc x)
    have hcf : c = false := by
      have h0 := hC (fun _ => false)
      rw [hc'] at h0
      cases c with
      | false => rfl
      | true =>
        obtain ⟨u, v, _, hu, _⟩ := h0.mp rfl
        exact absurd hu (by simp)
    subst hcf
    refine ⟨⟨[], n⟩, ⟨?_, ?_, ?_⟩, ?_, Nat.zero_le _⟩
    · intro g hgm
      simp at hgm
    · intro k hk
      simp at hk
    · intro g hgm
      simp at hgm
    · funext x
      rw [hgf x, hc' x]
      show (W ([] : List Gate) x).getD n false = false
      exact List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)
  · refine ⟨⟨new, j⟩, ⟨?_, ?_, ?_⟩, ?_, hl⟩
    · intro g hgm
      exact (hfan g hgm).1
    · exact hrb
    · intro g hgm
      exact (hfan g hgm).2
    · funext x
      rw [hgf x, hev x]
      exact hj x

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma normalize_graph (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (hfun : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size := by
  apply normalize_aux n G inferInstance C hm
  intro x
  change circuitFun n C x = true ↔ _
  rw [hfun]
  simp [graphFun]

lemma normalize_minimal (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hmin : IsMinimalMonoCircuit n C)
    (hfun : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size := by
  obtain ⟨D, hAO, hDfun, hle⟩ := normalize_graph n G C hmin.1 hfun
  have hDm : Monotone2 D := by
    intro g hg
    refine ⟨?_, (hAO.2.2 g hg).le⟩
    rcases hAO.1 g hg with h | h <;> simp [h]
  have hEq : circuitFun n D = circuitFun n C := hDfun.trans hfun.symm
  refine ⟨D, hAO, ⟨hDm, ?_⟩, hDfun, ?_⟩
  · intro E hEM hEf
    exact hle.trans (hmin.2 E hEM (hEf.trans hEq))
  · exact Nat.le_antisymm hle (hmin.2 D hDm hEq)

end PEqualNP.Outside.L_meta_2448_aux.BackwardNormalize

namespace PEqualNP.Outside.L_meta_2448_aux.ExternalRepair

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

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma gate_val_eq (n j : ℕ) (C : Circuit) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    gateVal n C j x = C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) := by
  change (wf C.gates (List.ofFn x)).getD (n+j) false = _
  have hs : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by
    have hs : C.gates.set j C.gates[j] =
        C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by
      rw [List.set_eq_take_append_cons_drop]
      simp [hj]
    simpa using hs
  conv_lhs => rw [hs]
  rw [wf_append, wf_cons]
  have hl : (wf (C.gates.take j) (List.ofFn x)).length = n+j := by
    simp [wf_len, List.length_take, Nat.min_eq_left hj.le]
  rw [wf_keep _ _ _ (by simp [hl]), ← hl, getD_snoc_eq]

lemma circuit_mono (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  apply mono2 C.gates
  · intro g hg
    simpa using hm g hg
  · simp
  · exact ofFn_mono n x y hxy

lemma graph_sandwich (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hm : Monotone2 D)
    (hbelow : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  refine ⟨hbelow x, ?_⟩
  intro hx
  obtain ⟨u, v, huv, hu, hv⟩ : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simpa [graphFun] using hx
  apply circuit_mono n D hm (pairInput u v) x _ (hedges u v huv)
  intro w hw
  have h : w = u ∨ w = v := of_decide_eq_true hw
  rcases h with rfl | rfl
  · exact hu
  · exact hv

lemma graph_rewrite (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hm : Monotone2 D) (hC : circuitFun n C = graphFun G ∅)
    (hdown : ∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = circuitFun n C := by
  rw [hC]
  apply graph_sandwich n G D hm _ hedges
  intro x hx
  rw [← hC]
  exact hdown x hx

set_option maxHeartbeats 800000 in
lemma gate_semantic_le (n : ℕ) (C D : Circuit) (hm : Monotone2 C)
    (hlen : D.gates.length = C.gates.length) (hout : D.output = C.output)
    (x : Fin n → Bool)
    (hexc : ∀ k (hk : k < C.gates.length), D.gates[k] ≠ C.gates[k] →
      gateVal n D k x = true → gateVal n C k x = true) :
    circuitFun n D x = true → circuitFun n C x = true := by
  classical
  have hall : ∀ k, k ≤ C.gates.length → ∀ w,
      (wf (D.gates.take k) (List.ofFn x)).getD w false = true →
      (wf (C.gates.take k) (List.ofFn x)).getD w false = true := by
    intro k
    induction k with
    | zero => intro _ _; exact id
    | succ k ih =>
      intro hk w
      have hkC : k < C.gates.length := by omega
      have hkD : k < D.gates.length := by omega
      have ih := ih (by omega)
      have hlC : (wf (C.gates.take k) (List.ofFn x)).length = n+k := by
        simp [wf_len, List.length_take, Nat.min_eq_left hkC.le]
      have hlD : (wf (D.gates.take k) (List.ofFn x)).length = n+k := by
        simp [wf_len, List.length_take, Nat.min_eq_left hkD.le]
      have hval : D.gates[k].op.eval (D.gates[k].inputs.map fun i =>
          (wf (D.gates.take k) (List.ofFn x)).getD i false) = true →
          C.gates[k].op.eval (C.gates[k].inputs.map fun i =>
          (wf (C.gates.take k) (List.ofFn x)).getD i false) = true := by
        by_cases heq : D.gates[k] = C.gates[k]
        · rw [heq]
          apply eval_mono
          · exact (hm C.gates[k] (List.getElem_mem _)).1
          · exact ih
        · have hh := hexc k hkC heq
          rw [gate_val_eq n k D hkD, gate_val_eq n k C hkC] at hh
          exact hh
      rw [List.take_succ_eq_append_getElem hkD, List.take_succ_eq_append_getElem hkC,
        wf_snoc, wf_snoc]
      rcases Nat.lt_trichotomy w (n+k) with hw | hw | hw
      · rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
        exact ih w
      · rw [hw, ← hlD, getD_snoc_eq, hlD, ← hlC, getD_snoc_eq]
        exact hval
      · rw [getD_snoc_gt _ _ _ (by omega)]
        simp
  have he := hall C.gates.length (by rfl) C.output
  rw [← hlen, List.take_length, hlen, List.take_length] at he
  change (wf D.gates (List.ofFn x)).getD D.output false = true → _
  rw [hout]
  exact he

lemma binary_gate_value (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (op : GateOp) (u v : ℕ) (hgate : C.gates[j] = ⟨op,[u,v]⟩)
    (hu : u < n+j) (hv : v < n+j) (x : Fin n → Bool) :
    gateVal n C j x = op.eval [(C.wires (List.ofFn x)).getD u false,
      (C.wires (List.ofFn x)).getD v false] := by
  rw [gate_val_eq n j C hj, hgate]
  simp only [List.map_cons, List.map_nil]
  rw [← wire_take C.gates (List.ofFn x) j u (by simpa using hu) hj.le,
    ← wire_take C.gates (List.ofFn x) j v (by simpa using hv) hj.le]
  rfl

set_option maxHeartbeats 800000 in
lemma outside_reader_repair (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hmC : Monotone2 C) (hmD : Monotone2 D)
    (hC : circuitFun n C = graphFun G ∅)
    (hlen : D.gates.length = C.gates.length) (hout : D.output = C.output)
    (g h t : ℕ) (hgt : g < t) (hht : h < t) (ht : t < C.gates.length)
    (hCt : C.gates[t] = ⟨GateOp.and, [n+g,n+h]⟩)
    (hDt : D.gates[t] = ⟨GateOp.or, [n+g,n+h]⟩)
    (hkeep : ∀ k (hk : k < C.gates.length), k ≠ g → k ≠ h → k ≠ t →
      D.gates[k] = C.gates[k])
    (hcleang : ∀ x : Fin n → Bool, gateVal n D g x = true → graphFun G ∅ x = true)
    (hcleanh : ∀ x : Fin n → Bool, gateVal n D h x = true → graphFun G ∅ x = true)
    (hcover : ∀ u v : Fin n, G.Adj u v →
      (gateVal n C g (pairInput u v) = true ∨ gateVal n C h (pairInput u v) = true) →
      gateVal n D g (pairInput u v) = true ∨ gateVal n D h (pairInput u v) = true)
    (hreach : ∀ x : Fin n → Bool, gateVal n D t x = true → circuitFun n D x = true) :
    circuitFun n D = graphFun G ∅ := by
  have htD : t < D.gates.length := by omega
  have evalC : ∀ x : Fin n → Bool,
      gateVal n C t x = (gateVal n C g x && gateVal n C h x) := by
    intro x
    rw [binary_gate_value n C t ht GateOp.and (n+g) (n+h) hCt (by omega) (by omega)]
    simp [GateOp.eval, gateVal]
  have evalD : ∀ x : Fin n → Bool,
      gateVal n D t x = (gateVal n D g x || gateVal n D h x) := by
    intro x
    rw [binary_gate_value n D t htD GateOp.or (n+g) (n+h) hDt (by omega) (by omega)]
    simp [GateOp.eval, gateVal]
  apply graph_sandwich n G D hmD
  · intro x hx
    by_contra hf
    have hc : circuitFun n C x = true := by
      apply gate_semantic_le n C D hmC hlen hout x ?_ hx
      intro k hk hneq hDk
      by_cases hkg : k = g
      · subst k; exact (hf (hcleang x hDk)).elim
      by_cases hkh : k = h
      · subst k; exact (hf (hcleanh x hDk)).elim
      by_cases hkt : k = t
      · subst k
        rw [evalD, Bool.or_eq_true] at hDk
        rcases hDk with hd | hd
        · exact (hf (hcleang x hd)).elim
        · exact (hf (hcleanh x hd)).elim
      · exact (hneq (hkeep k hk hkg hkh hkt)).elim
    rw [hC] at hc
    exact hf hc
  · intro u v huv
    let x := pairInput u v
    by_cases hactive : gateVal n C g x = true ∨ gateVal n C h x = true
    · apply hreach x
      rw [evalD, Bool.or_eq_true]
      exact hcover u v huv hactive
    · have hg0 : gateVal n C g x = false := Bool.eq_false_iff.mpr (fun h => hactive (Or.inl h))
      have hh0 : gateVal n C h x = false := Bool.eq_false_iff.mpr (fun h => hactive (Or.inr h))
      have ht0 : gateVal n C t x = false := by rw [evalC, hg0]; rfl
      have hCx : circuitFun n C x = true := by
        rw [hC]
        simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
          Bool.false_or, decide_eq_true_eq]
        exact ⟨u, v, huv, by simp [x, pairInput], by simp [x, pairInput]⟩
      apply gate_semantic_le n D C hmD hlen.symm hout.symm x ?_ hCx
      intro k hk hneq hCk
      have hkC : k < C.gates.length := by omega
      by_cases hkg : k = g
      · subst k; rw [hg0] at hCk; contradiction
      by_cases hkh : k = h
      · subst k; rw [hh0] at hCk; contradiction
      by_cases hkt : k = t
      · subst k; rw [ht0] at hCk; contradiction
      · exact (hneq (hkeep k hkC hkg hkh hkt).symm).elim

end PEqualNP.Outside.L_meta_2448_aux.ExternalRepair

namespace PEqualNP.Outside.L_meta_2448_aux.FourVertexGeometry

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma cross_cases {V : Type*} (G : SimpleGraph V)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (a b c d : V) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d) ∨
    (G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d) ∨
    (¬ G.Adj a d ∧ G.Adj b c ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d) ∨
    (¬ G.Adj a d ∧ ¬ G.Adj b c ∧ G.Adj a c ∧ ¬ G.Adj b d) ∨
    (¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj a c ∧ G.Adj b d) := by
  classical
  by_cases ead : G.Adj a d
  · have nbc : ¬ G.Adj b c := by
      intro ebc
      exact (hfour a d c b ead hcd.symm ebc.symm hab.symm).elim hac hbd.symm
    have nac : ¬ G.Adj a c := fun eac => htriangle a c d eac hcd ead.symm
    have nbd : ¬ G.Adj b d := fun ebd => htriangle a b d hab ebd ead.symm
    exact Or.inr (Or.inl ⟨ead, nbc, nac, nbd⟩)
  · by_cases ebc : G.Adj b c
    · have nac : ¬ G.Adj a c := fun eac => htriangle a b c hab ebc eac.symm
      have nbd : ¬ G.Adj b d := fun ebd => htriangle b c d ebc hcd ebd.symm
      exact Or.inr (Or.inr (Or.inl ⟨ead, ebc, nac, nbd⟩))
    · by_cases eac : G.Adj a c
      · have nbd : ¬ G.Adj b d := by
          intro ebd
          exact (hfour a c d b eac hcd ebd.symm hab.symm).elim had hbc.symm
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ead, ebc, eac, nbd⟩)))
      · by_cases ebd : G.Adj b d
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ead, ebc, eac, ebd⟩)))
        · exact Or.inl ⟨ead, ebc, eac, ebd⟩

def chosenEdges {V : Type*} (k : Fin 5) (a b c d : V) : List (V × V) :=
  match k.val with
  | 1 => [(a,b), (a,d), (c,d)]
  | 2 => [(a,b), (b,c), (c,d)]
  | 3 => [(a,b), (a,c), (c,d)]
  | 4 => [(a,b), (b,d), (c,d)]
  | _ => [(a,b), (c,d)]

def repairLeft (k : Fin 5) (a b c d : Bool) : Bool :=
  match k.val with
  | 1 => a && (b || d)
  | 2 => c && (b || d)
  | 3 => c && d
  | _ => a && b

def repairRight (k : Fin 5) (a b c d : Bool) : Bool :=
  match k.val with
  | 2 => a && b
  | 3 => a && (b || c)
  | 4 => d && (b || c)
  | _ => c && d

lemma repair_left_below_rectangle : ∀ (k : Fin 5) (a b c d : Bool),
    repairLeft k a b c d = true → ((a || c) && (b || d)) = true := by decide

lemma repair_right_below_rectangle : ∀ (k : Fin 5) (a b c d : Bool),
    repairRight k a b c d = true → ((a || d) && (b || c)) = true := by decide

lemma repair_output_edges {V : Type*} (k : Fin 5) (a b c d : V) (x : V → Bool) :
    (repairLeft k (x a) (x b) (x c) (x d) ||
      repairRight k (x a) (x b) (x c) (x d)) = true ↔
    ∃ u v, (u,v) ∈ chosenEdges k a b c d ∧ x u = true ∧ x v = true := by
  fin_cases k <;>
    simp [repairLeft, repairRight, chosenEdges, Bool.or_eq_true, Bool.and_eq_true,
      and_assoc, or_and_right, exists_or] <;>
    tauto

lemma chosen_edges_characterization {V : Type*} (G : SimpleGraph V)
    (a b c d : V) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (k : Fin 5)
    (ead : G.Adj a d ↔ k = 1) (ebc : G.Adj b c ↔ k = 2)
    (eac : G.Adj a c ↔ k = 3) (ebd : G.Adj b d ↔ k = 4) :
    (∀ u v, (u,v) ∈ chosenEdges k a b c d → G.Adj u v) ∧
    ∀ u v, G.Adj u v →
      (u = a ∨ u = b ∨ u = c ∨ u = d) →
      (v = a ∨ v = b ∨ v = c ∨ v = d) →
      (u,v) ∈ chosenEdges k a b c d ∨ (v,u) ∈ chosenEdges k a b c d := by
  have hba := hab.symm
  have hdc := hcd.symm
  have ead' : G.Adj d a ↔ k = 1 := ⟨fun h => ead.mp h.symm, fun h => (ead.mpr h).symm⟩
  have ebc' : G.Adj c b ↔ k = 2 := ⟨fun h => ebc.mp h.symm, fun h => (ebc.mpr h).symm⟩
  have eac' : G.Adj c a ↔ k = 3 := ⟨fun h => eac.mp h.symm, fun h => (eac.mpr h).symm⟩
  have ebd' : G.Adj d b ↔ k = 4 := ⟨fun h => ebd.mp h.symm, fun h => (ebd.mpr h).symm⟩
  constructor
  · intro u v huv
    fin_cases k <;> simp_all [chosenEdges] <;> aesop
  · intro u v huv hu hv
    rcases hu with rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl <;>
      fin_cases k <;> simp_all [chosenEdges]

lemma four_vertex_cover {V : Type*} (G : SimpleGraph V)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (a b c d : V) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∃ k : Fin 5, (∀ u v, (u,v) ∈ chosenEdges k a b c d → G.Adj u v) ∧
    ∀ u v, G.Adj u v →
      (u = a ∨ u = b ∨ u = c ∨ u = d) →
      (v = a ∨ v = b ∨ v = c ∨ v = d) →
      (u,v) ∈ chosenEdges k a b c d ∨ (v,u) ∈ chosenEdges k a b c d := by
  rcases cross_cases G htriangle hfour a b c d hab hcd hac had hbc hbd with
    h | h | h | h | h
  · refine ⟨0, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 0 ?_ ?_ ?_ ?_⟩ <;>
      simp_all
  · refine ⟨1, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 1 ?_ ?_ ?_ ?_⟩ <;>
      simp_all
  · refine ⟨2, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 2 ?_ ?_ ?_ ?_⟩ <;>
      simp_all
  · refine ⟨3, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 3 ?_ ?_ ?_ ?_⟩ <;>
      simp_all
  · refine ⟨4, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 4 ?_ ?_ ?_ ?_⟩ <;>
      simp_all

lemma pair_members {V : Type*} (Q : V → Prop) (u v p q : V)
    (hp : p = u ∨ p = v) (hq : q = u ∨ q = v) (hne : p ≠ q)
    (hpQ : Q p) (hqQ : Q q) : Q u ∧ Q v := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp_all

lemma active_pair_members (n : ℕ) (a b c d u v : Fin n)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d)
    (hactive : (((pairInput u v a || pairInput u v c) &&
      (pairInput u v b || pairInput u v d)) ||
      ((pairInput u v a || pairInput u v d) &&
      (pairInput u v b || pairInput u v c))) = true) :
    (u = a ∨ u = b ∨ u = c ∨ u = d) ∧
      (v = a ∨ v = b ∨ v = c ∨ v = d) := by
  let Q (w : Fin n) := w = a ∨ w = b ∨ w = c ∨ w = d
  have haQ : Q a := by simp [Q]
  have hbQ : Q b := by simp [Q]
  have hcQ : Q c := by simp [Q]
  have hdQ : Q d := by simp [Q]
  simp only [Bool.or_eq_true, Bool.and_eq_true, pairInput, decide_eq_true_eq] at hactive
  rcases hactive with ⟨ha | hc, hb | hd⟩ | ⟨ha | hd, hb | hc⟩
  · exact pair_members Q u v a b ha hb hab haQ hbQ
  · exact pair_members Q u v a d ha hd had haQ hdQ
  · exact pair_members Q u v c b hc hb hbc.symm hcQ hbQ
  · exact pair_members Q u v c d hc hd hcd hcQ hdQ
  · exact pair_members Q u v a b ha hb hab haQ hbQ
  · exact pair_members Q u v a c ha hc hac haQ hcQ
  · exact pair_members Q u v d b hd hb hbd.symm hdQ hbQ
  · exact pair_members Q u v d c hd hc hcd.symm hdQ hcQ

lemma repair_choice (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∃ k : Fin 5,
      (∀ x : Fin n → Bool, repairLeft k (x a) (x b) (x c) (x d) = true →
        graphFun G ∅ x = true) ∧
      (∀ x : Fin n → Bool, repairRight k (x a) (x b) (x c) (x d) = true →
        graphFun G ∅ x = true) ∧
      ∀ u v : Fin n, G.Adj u v →
        (((pairInput u v a || pairInput u v c) &&
          (pairInput u v b || pairInput u v d)) ||
          ((pairInput u v a || pairInput u v d) &&
          (pairInput u v b || pairInput u v c))) = true →
        (repairLeft k (pairInput u v a) (pairInput u v b) (pairInput u v c) (pairInput u v d) ||
          repairRight k (pairInput u v a) (pairInput u v b) (pairInput u v c) (pairInput u v d)) = true := by
  obtain ⟨k, hgood, hcover⟩ := four_vertex_cover G htriangle hfour a b c d hab hcd hac had hbc hbd
  have clean : ∀ x : Fin n → Bool,
      (repairLeft k (x a) (x b) (x c) (x d) || repairRight k (x a) (x b) (x c) (x d)) = true →
      graphFun G ∅ x = true := by
    intro x hx
    obtain ⟨u, v, huv, hu, hv⟩ := (repair_output_edges k a b c d x).mp hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, hgood u v huv, hu, hv⟩
  refine ⟨k, ?_, ?_, ?_⟩
  · intro x hx
    exact clean x (by simp only [hx, Bool.true_or])
  · intro x hx
    exact clean x (by simp only [hx, Bool.or_true])
  · intro u v huv hactive
    obtain ⟨hu, hv⟩ := active_pair_members n a b c d u v hab.ne hcd.ne hac had hbc hbd hactive
    apply (repair_output_edges k a b c d (pairInput u v)).mpr
    rcases hcover u v huv hu hv with he | he
    · exact ⟨u, v, he, by simp [pairInput], by simp [pairInput]⟩
    · exact ⟨v, u, he, by simp [pairInput], by simp [pairInput]⟩

end PEqualNP.Outside.L_meta_2448_aux.FourVertexGeometry

namespace PEqualNP.Outside.L_meta_2448_aux.DoubleStarGeometry

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma cross_edge_center {V : Type*} (G : SimpleGraph V)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (P Q : Set V) (p q : V) (hpq : G.Adj p q)
    (hpQ : ∀ b ∈ Q, G.Adj p b) (hqP : ∀ a ∈ P, G.Adj q a)
    (a b : V) (ha : a ∈ P) (hb : b ∈ Q) (hab : G.Adj a b) :
    a = p ∨ b = q := by
  rcases hfour p b a q (hpQ b hb) hab.symm (hqP a ha).symm hpq.symm with h | h
  · exact Or.inl h.symm
  · exact Or.inr h

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab.ne rfl).elim
    · exact hab
    · exact hab.symm
    · exact (hab.ne rfl).elim
  · intro huv
    exact ⟨u, v, huv, Or.inl rfl, Or.inr rfl⟩

lemma clean_context_centers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q R : Set (Fin n)) (p q : Fin n)
    (hpP : p ∈ P) (hpR : p ∈ R) (hqQ : q ∈ Q) (hqR : q ∈ R)
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ P, x a = true) → (∃ b ∈ Q, x b = true) →
      (∃ c ∈ R, x c = true) → graphFun G ∅ x = true) :
    (∀ b ∈ Q, G.Adj p b) ∧ (∀ a ∈ P, G.Adj q a) := by
  constructor
  · intro b hb
    apply (graph_pair G p b).mp
    exact hclean (pairInput p b)
      ⟨p, hpP, by simp [pairInput]⟩ ⟨b, hb, by simp [pairInput]⟩
      ⟨p, hpR, by simp [pairInput]⟩
  · intro a ha
    apply (graph_pair G q a).mp
    exact hclean (pairInput q a)
      ⟨a, ha, by simp [pairInput]⟩ ⟨q, hqQ, by simp [pairInput]⟩
      ⟨q, hqR, by simp [pairInput]⟩

def twoStars {V : Type*} (P Q : Set V) (p q : V) (x : V → Bool) : Prop :=
  (x p = true ∧ ∃ b ∈ Q, x b = true) ∨
  (x q = true ∧ ∃ a ∈ P, x a = true)

lemma clean_context_repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (P Q R : Set (Fin n)) (hdisjoint : Disjoint P Q) (p q : Fin n)
    (hpP : p ∈ P) (hpR : p ∈ R) (hqQ : q ∈ Q) (hqR : q ∈ R)
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ P, x a = true) → (∃ b ∈ Q, x b = true) →
      (∃ c ∈ R, x c = true) → graphFun G ∅ x = true) :
    (∀ x, twoStars P Q p q x → graphFun G ∅ x = true) ∧
    (∀ u v, G.Adj u v →
      (∃ a ∈ P, pairInput u v a = true) →
      (∃ b ∈ Q, pairInput u v b = true) →
      twoStars P Q p q (pairInput u v)) := by
  obtain ⟨hpQ, hqP⟩ := clean_context_centers G P Q R p q hpP hpR hqQ hqR hclean
  constructor
  · intro x hx
    rcases hx with ⟨hp, b, hb, hx⟩ | ⟨hq, a, ha, hx⟩
    · exact hclean x ⟨p, hpP, hp⟩ ⟨b, hb, hx⟩ ⟨p, hpR, hp⟩
    · exact hclean x ⟨a, ha, hx⟩ ⟨q, hqQ, hq⟩ ⟨q, hqR, hq⟩
  · rintro u v huv ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩
    have habne : a ≠ b := by
      intro h
      subst b
      exact Set.disjoint_left.mp hdisjoint ha hb
    have hab : G.Adj a b := by
      simp only [pairInput, decide_eq_true_eq] at hxa hxb
      rcases hxa with rfl | rfl <;> rcases hxb with rfl | rfl
      · exact (habne rfl).elim
      · exact huv
      · exact huv.symm
      · exact (habne rfl).elim
    rcases cross_edge_center G hfour P Q p q (hpQ q hqQ) hpQ hqP a b ha hb hab with h | h
    · exact Or.inl ⟨h ▸ hxa, b, hb, hxb⟩
    · exact Or.inr ⟨h ▸ hxb, a, ha, hxa⟩

lemma clean_context_input_edge_obstruction {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (P Q : Set (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ P, x a = true) → (∃ b ∈ Q, x b = true) → graphFun G ∅ x = true)
    (a d : Fin n) (ha : a ∈ P) (hd : d ∈ P) (had : G.Adj a d) : Q = ∅ := by
  ext v
  constructor
  · intro hv
    have hav : G.Adj a v := (graph_pair G a v).mp
      (hclean (pairInput a v) ⟨a, ha, by simp [pairInput]⟩ ⟨v, hv, by simp [pairInput]⟩)
    have hdv : G.Adj d v := (graph_pair G d v).mp
      (hclean (pairInput d v) ⟨d, hd, by simp [pairInput]⟩ ⟨v, hv, by simp [pairInput]⟩)
    exact (htriangle a d v had hdv hav.symm).elim
  · intro hv
    exact hv.elim

end PEqualNP.Outside.L_meta_2448_aux.DoubleStarGeometry

namespace PEqualNP.Outside.L_meta_2448_aux.RectangleRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2448_aux.ExternalRepair
open PEqualNP.Outside.L_meta_2448_aux.FourVertexGeometry

def leftGate (n q : ℕ) (a b c d : Fin n) (k : Fin 5) : Gate :=
  match k.val with
  | 1 => ⟨.and, [a.val,n+q]⟩
  | 2 => ⟨.and, [c.val,n+q]⟩
  | 3 => ⟨.and, [c.val,d.val]⟩
  | _ => ⟨.and, [a.val,b.val]⟩

def rightGate (n s : ℕ) (a b c d : Fin n) (k : Fin 5) : Gate :=
  match k.val with
  | 2 => ⟨.and, [a.val,b.val]⟩
  | 3 => ⟨.and, [a.val,n+s]⟩
  | 4 => ⟨.and, [d.val,n+s]⟩
  | _ => ⟨.and, [c.val,d.val]⟩

def repairCircuit (n : ℕ) (C : Circuit) (g h t q s : ℕ)
    (a b c d : Fin n) (k : Fin 5) : Circuit :=
  ⟨((C.gates.set g (leftGate n q a b c d k)).set h (rightGate n s a b c d k)).set t
    ⟨.or, [n+g,n+h]⟩, C.output⟩

lemma set_model (n : ℕ) (C : Circuit) (j : ℕ) (r : Gate)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (hrop : r.op = GateOp.and ∨ r.op = GateOp.or) (hrlen : r.inputs.length = 2)
    (hrback : ∀ w ∈ r.inputs, w < n+j) :
    PEqualNP.TopForm.IsAO2 n ⟨C.gates.set j r, C.output⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases List.mem_or_eq_of_mem_set hz with hz | rfl
    · exact hC.1 z hz
    · exact hrop
  · intro k hk w hw
    have hkC : k < C.gates.length := by simpa using hk
    have he : gateAt ⟨C.gates.set j r, C.output⟩ k =
        if j = k then r else gateAt C k := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hk, List.getElem_set,
        List.getD_eq_getElem _ _ hkC]
    rw [he] at hw
    by_cases hjk : j = k
    · subst j
      exact hrback w (by simpa using hw)
    · exact hC.2.1 k hkC w (by simpa [hjk] using hw)
  · intro z hz
    rcases List.mem_or_eq_of_mem_set hz with hz | rfl
    · exact hC.2.2 z hz
    · exact hrlen

lemma repair_model (n : ℕ) (C : Circuit) (g h t q s : ℕ)
    (a b c d : Fin n) (k : Fin 5) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hgt : g < t) (hht : h < t) (hqg : q < g) (hsh : s < h) :
    PEqualNP.TopForm.IsAO2 n (repairCircuit n C g h t q s a b c d k) := by
  have hL : (leftGate n q a b c d k).op = GateOp.and := by fin_cases k <;> rfl
  have hR : (rightGate n s a b c d k).op = GateOp.and := by fin_cases k <;> rfl
  have hl : (leftGate n q a b c d k).inputs.length = 2 := by fin_cases k <;> rfl
  have hr : (rightGate n s a b c d k).inputs.length = 2 := by fin_cases k <;> rfl
  have hlb : ∀ w ∈ (leftGate n q a b c d k).inputs, w < n+g := by
    fin_cases k <;> simp only [leftGate, List.mem_cons, List.not_mem_nil, or_false] <;>
      intro w hw <;> rcases hw with rfl | rfl
    all_goals have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt; omega
  have hrb : ∀ w ∈ (rightGate n s a b c d k).inputs, w < n+h := by
    fin_cases k <;> simp only [rightGate, List.mem_cons, List.not_mem_nil, or_false] <;>
      intro w hw <;> rcases hw with rfl | rfl
    all_goals have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt; omega
  have h1 := set_model n C g (leftGate n q a b c d k) hC (Or.inl hL) hl hlb
  have h2 := set_model n ⟨C.gates.set g (leftGate n q a b c d k), C.output⟩ h
    (rightGate n s a b c d k) h1 (Or.inl hR) hr hrb
  apply set_model n _ t ⟨GateOp.or,[n+g,n+h]⟩ h2 (Or.inr rfl) rfl
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> omega

set_option maxHeartbeats 1600000 in
lemma repair_values (n : ℕ) (C : Circuit) (g h t q s : ℕ)
    (a b c d : Fin n) (k : Fin 5) (hgh : g < h) (hht : h < t)
    (ht : t < C.gates.length) (hqg : q < g) (hsh : s < h) (hsg : s ≠ g)
    (hQ : C.gates[q] = ⟨GateOp.or, [b.val,d.val]⟩)
    (hS : C.gates[s] = ⟨GateOp.or, [b.val,c.val]⟩) :
    let D := repairCircuit n C g h t q s a b c d k
    (∀ x : Fin n → Bool, gateVal n D g x = repairLeft k (x a) (x b) (x c) (x d)) ∧
    (∀ x : Fin n → Bool, gateVal n D h x = repairRight k (x a) (x b) (x c) (x d)) := by
  let D := repairCircuit n C g h t q s a b c d k
  have hlen : D.gates.length = C.gates.length := by simp [D, repairCircuit]
  have hgD : g < D.gates.length := by omega
  have hhD : h < D.gates.length := by omega
  have hqD : q < D.gates.length := by omega
  have hsD : s < D.gates.length := by omega
  have hDg : D.gates[g] = leftGate n q a b c d k := by
    simp [D, repairCircuit, show t ≠ g by omega, show h ≠ g by omega]
  have hDh : D.gates[h] = rightGate n s a b c d k := by
    simp [D, repairCircuit, show t ≠ h by omega]
  have hDq : D.gates[q] = ⟨GateOp.or, [b.val,d.val]⟩ := by
    simp [D, repairCircuit, show t ≠ q by omega, show h ≠ q by omega,
      show g ≠ q by omega, hQ]
  have hDs : D.gates[s] = ⟨GateOp.or, [b.val,c.val]⟩ := by
    simp [D, repairCircuit, show t ≠ s by omega, show h ≠ s by omega,
      Ne.symm hsg, hS]
  have hinput : ∀ (x : Fin n → Bool) (gs : List Gate) (i : Fin n),
      (wf gs (List.ofFn x)).getD i.val false = x i := by
    intro x gs i
    rw [wf_keep _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, i.isLt]
  have evalQ : ∀ x : Fin n → Bool, gateVal n D q x = (x b || x d) := by
    intro x
    rw [gate_val_eq n q D hqD, hDq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, id_eq, Bool.or_false, hinput]
  have evalS : ∀ x : Fin n → Bool, gateVal n D s x = (x b || x c) := by
    intro x
    rw [gate_val_eq n s D hsD, hDs]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, id_eq, Bool.or_false, hinput]
  constructor
  · intro x
    have pq : (wf (D.gates.take g) (List.ofFn x)).getD (n+q) false = (x b || x d) := by
      rw [← wire_take D.gates (List.ofFn x) g (n+q) (by simp; omega) hgD.le]
      exact evalQ x
    rw [gate_val_eq n g D hgD, hDg]
    fin_cases k <;> simp only [leftGate, repairLeft, GateOp.eval, List.map_cons,
      List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hinput, pq]
  · intro x
    have ps : (wf (D.gates.take h) (List.ofFn x)).getD (n+s) false = (x b || x c) := by
      rw [← wire_take D.gates (List.ofFn x) h (n+s) (by simp; omega) hhD.le]
      exact evalS x
    rw [gate_val_eq n h D hhD, hDh]
    fin_cases k <;> simp only [rightGate, repairRight, GateOp.eval, List.map_cons,
      List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hinput, ps]

set_option maxHeartbeats 1600000 in
lemma two_rectangle_component (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (C : Circuit) (hmC : Monotone2 C) (hC : circuitFun n C = graphFun G ∅)
    (g h t q s : ℕ) (a b c d : Fin n)
    (hgh : g < h) (hht : h < t) (ht : t < C.gates.length)
    (hqg : q < g) (hsh : s < h) (hsg : s ≠ g)
    (hQ : C.gates[q] = ⟨GateOp.or, [b.val,d.val]⟩)
    (hS : C.gates[s] = ⟨GateOp.or, [b.val,c.val]⟩)
    (hCt : C.gates[t] = ⟨GateOp.and, [n+g,n+h]⟩)
    (hgfun : ∀ x : Fin n → Bool, gateVal n C g x = ((x a || x c) && (x b || x d)))
    (hhfun : ∀ x : Fin n → Bool, gateVal n C h x = ((x a || x d) && (x b || x c)))
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hreach : ∀ (k : Fin 5) (x : Fin n → Bool),
      gateVal n (repairCircuit n C g h t q s a b c d k) t x = true →
      circuitFun n (repairCircuit n C g h t q s a b c d k) x = true) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      (∀ x : Fin n → Bool, gateVal n D g x = true → graphFun G ∅ x = true) ∧
      (∀ x : Fin n → Bool, gateVal n D h x = true → graphFun G ∅ x = true) := by
  classical
  obtain ⟨k, hcleanL, hcleanR, hcover⟩ := repair_choice n G htriangle hfour a b c d
    hab hcd hac had hbc hbd
  let D := repairCircuit n C g h t q s a b c d k
  have hlen : D.gates.length = C.gates.length := by simp [D, repairCircuit]
  have htD : t < D.gates.length := by omega
  have hDm : Monotone2 D := by
    intro z hz
    rcases List.mem_or_eq_of_mem_set hz with hz | rfl
    · rcases List.mem_or_eq_of_mem_set hz with hz | rfl
      · rcases List.mem_or_eq_of_mem_set hz with hz | rfl
        · exact hmC z hz
        · fin_cases k <;> simp [leftGate]
      · fin_cases k <;> simp [rightGate]
    · simp
  obtain ⟨evalg, evalh⟩ := repair_values n C g h t q s a b c d k hgh hht ht hqg hsh hsg hQ hS
  have hcleang : ∀ x : Fin n → Bool, gateVal n D g x = true → graphFun G ∅ x = true := by
    intro x hx
    exact hcleanL x ((evalg x).symm.trans hx)
  have hcleanh : ∀ x : Fin n → Bool, gateVal n D h x = true → graphFun G ∅ x = true := by
    intro x hx
    exact hcleanR x ((evalh x).symm.trans hx)
  refine ⟨D, hDm, ?_, by simp [D, repairCircuit, Circuit.size], hcleang, hcleanh⟩
  apply outside_reader_repair n G C D hmC hDm hC hlen rfl g h t (by omega) hht ht hCt
  · simp [D, repairCircuit]
  · intro i hi hig hih hit
    simp [D, repairCircuit, Ne.symm hig, Ne.symm hih, Ne.symm hit]
  · exact hcleang
  · exact hcleanh
  · intro u v huv hvold
    rw [evalg, evalh]
    rw [hgfun, hhfun] at hvold
    have hc := hcover u v huv (by simpa only [Bool.or_eq_true] using hvold)
    simpa only [Bool.or_eq_true] using hc
  · exact hreach k

end PEqualNP.Outside.L_meta_2448_aux.RectangleRepair

namespace PEqualNP.Outside.L_meta_2448_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

abbrev cycleFiveGraph : SimpleGraph (Fin 5) :=
  edgeGraph 5 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

def cycleFiveCircuit : Circuit :=
  ⟨[⟨.or, [2, 4]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [3, 5]⟩,
    ⟨.or, [6, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [1, 9]⟩,
    ⟨.or, [8, 10]⟩], 11⟩

lemma cycleFive_mono : Monotone2 cycleFiveCircuit := by
  simp [Monotone2, cycleFiveCircuit]

lemma cycleFive_correct :
    circuitFun 5 cycleFiveCircuit = graphFun cycleFiveGraph ∅ := by decide

lemma cycleFive_profile : HasStarProfile 5 cycleFiveGraph cycleFiveCircuit := by decide

lemma cycleFive_size : cycleFiveCircuit.size = 7 := rfl

lemma cycleFive_triangle_free :
    ∀ a b c : Fin 5, cycleFiveGraph.Adj a b → cycleFiveGraph.Adj b c →
      ¬cycleFiveGraph.Adj c a := by decide

lemma cycleFive_four_cycle_free :
    ∀ a b c d : Fin 5, cycleFiveGraph.Adj a b → cycleFiveGraph.Adj b c →
      cycleFiveGraph.Adj c d → cycleFiveGraph.Adj d a → a = c ∨ b = d := by decide

end PEqualNP.Outside.L_meta_2448_aux

namespace PEqualNP.Outside.L_meta_2448_aux.PivotalExample

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

abbrev graph : SimpleGraph (Fin 5) :=
  edgeGraph 5 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

def circuit : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [1, 3]⟩,
    ⟨.or, [2, 6]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [7, 8]⟩,
    ⟨.or, [9, 10]⟩], 11⟩

lemma mono : Monotone2 circuit := by simp [Monotone2, circuit]

lemma correct : circuitFun 5 circuit = graphFun graph ∅ := by decide

lemma profile : HasStarProfile 5 graph circuit := by decide

lemma size : circuit.size = 7 := rfl

lemma owns_star_two :
    ∀ u v : Fin 5, graph.Adj u v → Owns 5 circuit 5 u v → u = 2 ∨ v = 2 := by
  decide

lemma pivotal_edges_have_no_center :
    ¬∃ c : Fin 5, ∀ u v : Fin 5, graph.Adj u v →
      circuitFun 5 ⟨circuit.gates.set 5 ⟨GateOp.or, []⟩, circuit.output⟩
        (pairInput u v) = false → u = c ∨ v = c := by
  decide

lemma left_operand_rejects_center :
    gateVal 5 circuit 2 (pairInput (2 : Fin 5) 2) = false := by decide

lemma right_operand_accepts_center :
    gateVal 5 circuit 3 (pairInput (2 : Fin 5) 2) = true := by decide

end PEqualNP.Outside.L_meta_2448_aux.PivotalExample

namespace PEqualNP.Outside.L_meta_2448_aux.PrivateSupportExample

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

abbrev graph : SimpleGraph (Fin 8) :=
  edgeGraph 8 [(0, 1), (2, 3), (4, 0), (4, 2), (5, 1),
    (5, 3), (6, 0), (6, 3), (7, 1), (7, 2)]

def circuit : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [8, 9]⟩,
    ⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [11, 12]⟩,
    ⟨.and, [10, 13]⟩, ⟨.and, [4, 8]⟩, ⟨.and, [5, 9]⟩,
    ⟨.and, [6, 11]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [14, 15]⟩,
    ⟨.or, [16, 17]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [21, 18]⟩], 22⟩

lemma model : IsAO2 8 circuit := by decide

lemma triangle_free :
    ∀ a b c : Fin 8, graph.Adj a b → graph.Adj b c → ¬graph.Adj c a := by decide

lemma no_four_cycle : NoFourCycle graph := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma correct : circuitFun 8 circuit = graphFun graph ∅ := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma top_form : TopForm graph circuit := by decide

lemma first_and : ∀ i < 2, (gateAt circuit i).op = GateOp.or := by
  letI : DecidableEq GateOp := gateOpDecEq
  decide

lemma owns_disjoint : Owns 8 circuit 2 0 1 ∧ Owns 8 circuit 2 2 3 := by decide

lemma pivotal_disjoint :
    circuitFun 8 ⟨circuit.gates.set 2 ⟨.or, []⟩, circuit.output⟩ (pairInput 0 1) = false ∧
    circuitFun 8 ⟨circuit.gates.set 2 ⟨.or, []⟩, circuit.output⟩ (pairInput 2 3) = false := by decide

lemma supports_shared :
    opnd circuit 2 0 = 8 ∧ opnd circuit 2 1 = 9 ∧
    readers 8 circuit 0 = {2, 7} ∧ readers 8 circuit 1 = {2, 8} := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma additional_readers_clean :
    (gateAt circuit 7).op = GateOp.and ∧ BelowF graph circuit 7 ∧
    (gateAt circuit 8).op = GateOp.and ∧ BelowF graph circuit 8 := by
  letI : DecidableEq GateOp := gateOpDecEq
  decide

lemma size : circuit.size = 15 := rfl

lemma or_count :
    (circuit.gates.filter fun g => match g.op with | .or => true | _ => false).length = 8 := rfl

lemma edge_count : graph.edgeFinset.card = 10 := by decide

lemma or_count_below_edges_minus_one :
    (circuit.gates.filter fun g => match g.op with | .or => true | _ => false).length + 1 <
      graph.edgeFinset.card := by rw [or_count, edge_count]; decide

end PEqualNP.Outside.L_meta_2448_aux.PrivateSupportExample
