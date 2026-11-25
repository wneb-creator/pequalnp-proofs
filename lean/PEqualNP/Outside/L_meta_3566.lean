import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_3566.AO2Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]


lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

def Good : ℕ → List Gate → Prop
  | _, [] => True
  | m, g :: gs =>
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
        ∀ i ∈ g.inputs, i < m) ∧ Good (m + 1) gs

lemma good_append (gs hs : List Gate) (m : ℕ) :
    Good m gs → Good (m + gs.length) hs → Good m (gs ++ hs) := by
  induction gs generalizing m with
  | nil => simp [Good]
  | cons g gs ih =>
    rintro ⟨hg, hgs⟩ hhs
    refine ⟨hg, ih (m + 1) hgs ?_⟩
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhs

lemma good_mem (gs : List Gate) (m : ℕ) (h : Good m gs) :
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  induction gs generalizing m with
  | nil => simp
  | cons g gs ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨h.1.1, h.1.2.1⟩
    · exact ih (m + 1) h.2 a ha

lemma good_back (gs : List Gate) (m : ℕ) (h : Good m gs) :
    ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < m + j := by
  induction gs generalizing m with
  | nil => simp
  | cons g gs ih =>
    intro j hj i hi
    cases j with
    | zero =>
      simpa using h.1.2.2 i (by simpa using hi)
    | succ j =>
      have hlt : j < gs.length := by simpa using hj
      have him : i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs := by simpa using hi
      have := ih (m + 1) h.2 j hlt i him
      omega

lemma good_ao2 (m : ℕ) (gs : List Gate) (out : ℕ) (h : Good m gs) :
    IsAO2 m ⟨gs, out⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact (good_mem gs m h g hg).1
  · exact good_back gs m h
  · intro g hg
    exact (good_mem gs m h g hg).2

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), Good m gs ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

lemma bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, good, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, good, le_trans len hs, ho, ev⟩

lemma bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, good, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, good, len, ho, fun w hw => by rw [ev w hw, e]⟩

lemma bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, True.intro, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

lemma bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, good1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, good2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · apply good_append (gs1 ++ gs2) _ m
    · exact good_append gs1 gs2 m good1 good2
    · refine ⟨⟨hop, rfl, ?_⟩, True.intro⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [List.length_append]
      rcases hi with rfl | rfl <;> omega
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

lemma bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

lemma bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2


lemma bld_circuit {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = F ∧ D.size ≤ s := by
  obtain ⟨gs, out, good, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, good_ao2 n gs out good, ?_, len⟩
  funext x
  have e := ev (List.ofFn x) (by simp)
  simp only [circuitFun, Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i


lemma bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp


lemma bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in

lemma bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var t) (bld_anyFinset S hSne)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp


lemma edge_upper_ao2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ D.size + 1 ≤ G.edgeFinset.card + T.card := by
  intro n G _ T hE hc
  obtain ⟨i0, j0, h0⟩ := hE
  have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hc a b he with h | h
    · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
  have hpos := hne.card_pos
  obtain ⟨D, h1, h3, h4⟩ := bld_circuit (bld_edges n T G.edgeFinset hne cov)
  refine ⟨D, h1, ?_, by omega⟩
  rw [h3]
  funext x
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, h⟩
    revert he h
    refine Sym2.ind (fun a b => ?_) e
    intro he h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨s(i, j), by simpa using hij, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption

lemma graphFun_upper_ao2 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (hE : G.edgeFinset.Nonempty)
    (hT : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size + 1 ≤ G.edgeFinset.card + T.card := by
  have hadj : ∃ a b : Fin n, G.Adj a b := by
    obtain ⟨e, he⟩ := hE
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    exact ⟨a, b, by simpa using he⟩
  obtain ⟨D, hD, hF, hsize⟩ := edge_upper_ao2 n G T hadj hT
  refine ⟨D, hD, ?_, hsize⟩
  rw [hF]
  funext x
  simp [graphFun]

end PEqualNP.Outside.L_meta_3566.AO2Upper


namespace PEqualNP.Outside.L_meta_3566

lemma cut_adj {n : ℕ} (G : SimpleGraph (Fin n)) (z a b : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).Adj a b ↔ G.Adj a b ∧ a ≠ z ∧ b ≠ z :=
  SimpleGraph.deleteIncidenceSet_adj

lemma cut_edge_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).edgeFinset.card + G.degree z = G.edgeFinset.card := by
  change (G.deleteIncidenceSet z).edgeFinset.card + G.degree z = _
  rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset z)

lemma cut_cover_extend {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S : Finset (Fin n))
    (hS : (G.deleteEdges (G.incidenceSet z)).IsVertexCover (S : Set (Fin n))) :
    G.IsVertexCover (insert z S : Set (Fin n)) := by
  intro a b hab
  by_cases haz : a = z
  · exact Or.inl (by simp [haz])
  by_cases hbz : b = z
  · exact Or.inr (by simp [hbz])
  rcases hS ((cut_adj G z a b).mpr ⟨hab, haz, hbz⟩) with ha | hb
  · exact Or.inl (by simp only [Set.mem_insert_iff]; exact Or.inr ha)
  · exact Or.inr (by simp only [Set.mem_insert_iff]; exact Or.inr hb)

lemma exists_min_cover {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) ∧
      ∀ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) → T.card ≤ S.card := by
  classical
  have hex : ∃ k : ℕ, ∃ T : Finset (Fin n),
      G.IsVertexCover (T : Set (Fin n)) ∧ T.card = k :=
    ⟨n, Finset.univ, by simp, by simp⟩
  obtain ⟨T, hT, hcard⟩ := Nat.find_spec hex
  refine ⟨T, hT, ?_⟩
  intro S hS
  rw [hcard]
  exact Nat.find_min' hex ⟨S, hS, rfl⟩

lemma cut_cover_bounds {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (T S : Finset (Fin n))
    (hT : G.IsVertexCover (T : Set (Fin n)))
    (hTmin : ∀ U : Finset (Fin n), G.IsVertexCover (U : Set (Fin n)) → T.card ≤ U.card)
    (hS : (G.deleteEdges (G.incidenceSet z)).IsVertexCover (S : Set (Fin n)))
    (hSmin : ∀ U : Finset (Fin n),
      (G.deleteEdges (G.incidenceSet z)).IsVertexCover (U : Set (Fin n)) → S.card ≤ U.card) :
    S.card ≤ T.card ∧ T.card ≤ S.card + 1 := by
  constructor
  · exact hSmin T (hT.mono (G.deleteEdges_le _))
  · exact (hTmin (insert z S) (by simpa using cut_cover_extend G z S hS)).trans
      (Finset.card_insert_le _ _)

lemma exists_nontrivial_cut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧ (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty := by
  classical
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp (show 1 < G.edgeFinset.card by omega)
  revert he hf hef
  refine Sym2.ind (fun a b => ?_) e
  refine Sym2.ind (fun c d => ?_) f
  intro hab hcd hne
  have hab' : G.Adj a b := by simpa using hab
  have hcd' : G.Adj c d := by simpa using hcd
  have witness (z w : Fin n) (hzw : G.Adj z w) (hzc : z ≠ c) (hzd : z ≠ d) :
      ∃ z : Fin n, 0 < G.degree z ∧ (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty := by
    refine ⟨z, hzw.degree_pos_left, s(c, d), ?_⟩
    apply SimpleGraph.mem_edgeFinset.mpr
    exact (cut_adj G z c d).mpr ⟨hcd', hzc.symm, hzd.symm⟩
  by_cases hac : a = c
  · subst c
    by_cases hbd : b = d
    · subst d; exact (hne rfl).elim
    exact witness b a hab'.symm hab'.ne.symm hbd
  by_cases had : a = d
  · subst d
    by_cases hbc : b = c
    · subst c; exact (hne (Sym2.eq_swap)).elim
    exact witness b a hab'.symm hbc hab'.ne.symm
  exact witness a b hab' hac had

lemma peel_of_lower_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : 2 ≤ G.edgeFinset.card)
    (hLower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∀ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) →
      (∀ U : Finset (Fin n), G.IsVertexCover (U : Set (Fin n)) → T.card ≤ U.card) →
      G.edgeFinset.card + T.card ≤ C.size + 1) :
    ∃ z : Fin n, 0 < G.degree z ∧
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧
        PEqualNP.MetaComplexity.circuitFun n D = (fun y : Fin n → Bool =>
          @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧
            y a = true ∧ y b = true) (Classical.propDecidable _)) ∧
        D.size + G.degree z ≤ C.size ∧
        ((∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
          (G.deleteEdges (G.incidenceSet z)) S ∧ ∀ T : Finset (Fin n),
          PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T → S.card < T.card) →
          D.size + G.degree z + 1 ≤ C.size) := by
  classical
  obtain ⟨z, hz, hH⟩ := exists_nontrivial_cut G hE
  obtain ⟨T, hT, hTmin⟩ := exists_min_cover G
  obtain ⟨S, hS, hSmin⟩ := exists_min_cover (G.deleteEdges (G.incidenceSet z))
  obtain ⟨D, hD, hFun, hSize⟩ := AO2Upper.graphFun_upper_ao2 n
    (G.deleteEdges (G.incidenceSet z)) S hH (fun a b hab => hS hab)
  have hCount := cut_edge_count G z
  have hST := (cut_cover_bounds G z T S hT hTmin hS hSmin).1
  refine ⟨z, hz, ?_⟩
  intro C hC hCF
  have hLow := hLower C hC hCF T hT hTmin
  refine ⟨D, hD, ?_, by omega, ?_⟩
  · rw [hFun]
    funext y
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
  · rintro ⟨S', hS', hDrop⟩
    have hSS' := hSmin S' (by intro a b hab; exact hS' a b hab)
    have hS'T := hDrop T (fun _ _ hab => hT hab)
    omega

lemma exists_least_ao {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C := by
  classical
  obtain ⟨D, hD, hDF, _⟩ := AO2Upper.graphFun_upper_ao2 n G Finset.univ hE
    (by intro a b _; simp)
  have hex : ∃ s : ℕ, ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 n C ∧
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      C.size = s := ⟨D.size, D, hD, hDF, rfl⟩
  obtain ⟨C, hC, hCF, hSize⟩ := Nat.find_spec hex
  refine ⟨C, hC, hCF, ?_⟩
  intro C' hC' hC'F
  rw [hSize]
  exact Nat.find_min' hex ⟨C', hC', hC'F, rfl⟩

end PEqualNP.Outside.L_meta_3566

namespace PEqualNP.Outside.L_meta_3566.FalseRestrict

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.AO2Upper

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def readOption (a : Option ℕ) (w : List Bool) : Bool :=
  a.elim false (fun i => w.getD i false)

def Bound (m : ℕ) (a : Option ℕ) : Prop :=
  ∀ i, a = some i → i < m

def reduceGate (m : ℕ) (op : GateOp) : Option ℕ → Option ℕ → List Gate × Option ℕ
  | some a, some b => ([⟨op, [a, b]⟩], some m)
  | none, none => ([], none)
  | some a, none => ([], match op with | .or => some a | _ => none)
  | none, some b => ([], match op with | .or => some b | _ => none)

lemma reduce_good (m : ℕ) (op : GateOp) (a b : Option ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (ha : Bound m a) (hb : Bound m b) :
    Good m (reduceGate m op a b).1 := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [reduceGate, Good, Bound]

lemma reduce_bound (m : ℕ) (op : GateOp) (a b : Option ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (ha : Bound m a) (hb : Bound m b) :
    Bound (m + (reduceGate m op a b).1.length) (reduceGate m op a b).2 := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [reduceGate, Bound]

lemma reduce_size (m : ℕ) (op : GateOp) (a b : Option ℕ) :
    (reduceGate m op a b).1.length + (if a.isNone || b.isNone then 1 else 0) = 1 := by
  cases a <;> cases b <;> simp [reduceGate]

lemma reduce_eval (w : List Bool) (op : GateOp) (a b : Option ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    readOption (reduceGate w.length op a b).2 (wiresFrom (reduceGate w.length op a b).1 w) =
      op.eval [readOption a w, readOption b w] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp [reduceGate, readOption, wiresFrom, GateOp.eval]

lemma readOption_preserved (a : Option ℕ) (w : List Bool) (gs : List Gate)
    (ha : Bound w.length a) : readOption a (wiresFrom gs w) = readOption a w := by
  cases a with
  | none => rfl
  | some i => exact getD_wiresFrom gs w i (ha i rfl)

def MapRel (σ : List (Option ℕ)) (s t : List Bool) : Prop :=
  σ.length = s.length ∧ (∀ i, Bound t.length (σ.getD i none)) ∧
    ∀ i, s.getD i false = readOption (σ.getD i none) t

def emit (m : ℕ) (σ : List (Option ℕ)) (g : Gate) : List Gate × Option ℕ :=
  reduceGate m g.op (σ.getD (g.inputs.getD 0 0) none) (σ.getD (g.inputs.getD 1 0) none)

lemma mapRel_step (σ : List (Option ℕ)) (s t : List Bool) (g : Gate)
    (h : MapRel σ s t) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2) :
    MapRel (σ ++ [(emit t.length σ g).2])
      (s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)])
      (wiresFrom (emit t.length σ g).1 t) := by
  have hev : readOption (emit t.length σ g).2 (wiresFrom (emit t.length σ g).1 t) =
      g.op.eval (g.inputs.map fun i => s.getD i false) := by
    obtain ⟨a, b, hg⟩ := List.length_eq_two.mp hlen
    calc
      _ = g.op.eval [readOption (σ.getD a none) t, readOption (σ.getD b none) t] := by
        simpa [emit, hg] using reduce_eval t g.op (σ.getD a none) (σ.getD b none) hop
      _ = _ := by rw [← h.2.2 a, ← h.2.2 b]; simp [hg]
  have hb : Bound (t.length + (emit t.length σ g).1.length) (emit t.length σ g).2 :=
    reduce_bound t.length g.op _ _ hop (h.2.1 _) (h.2.1 _)
  refine ⟨by simp [h.1], ?_, ?_⟩
  · intro j
    by_cases hj : j = σ.length
    · subst j
      rw [getD_snoc_eq, length_wiresFrom]
      exact hb
    · intro i hi
      rw [getD_snoc_ne _ _ _ _ hj] at hi
      have := h.2.1 j i hi
      rw [length_wiresFrom]
      omega
  · intro j
    by_cases hj : j = σ.length
    · subst j
      have hs : (s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]).getD σ.length false =
          g.op.eval (g.inputs.map fun i => s.getD i false) := by
        rw [h.1, getD_snoc_eq]
      rw [hs, getD_snoc_eq]
      exact hev.symm
    · have hjs : j ≠ s.length := by rw [← h.1]; exact hj
      rw [getD_snoc_ne _ _ _ _ hjs, getD_snoc_ne _ _ _ _ hj, h.2.2 j]
      exact (readOption_preserved _ t _ (h.2.1 j)).symm

lemma emit_good (m : ℕ) (σ : List (Option ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hbound : ∀ i, Bound m (σ.getD i none)) : Good m (emit m σ g).1 :=
  reduce_good m g.op _ _ hop (hbound _) (hbound _)

def compile (m : ℕ) (σ : List (Option ℕ)) : List Gate → List Gate × List (Option ℕ)
  | [] => ([], σ)
  | g :: gs =>
      let r := emit m σ g
      let rest := compile (m + r.1.length) (σ ++ [r.2]) gs
      (r.1 ++ rest.1, rest.2)

def saved (m : ℕ) (σ : List (Option ℕ)) : List Gate → ℕ
  | [] => 0
  | g :: gs =>
      let r := emit m σ g
      (if (σ.getD (g.inputs.getD 0 0) none).isNone ||
          (σ.getD (g.inputs.getD 1 0) none).isNone then 1 else 0) +
        saved (m + r.1.length) (σ ++ [r.2]) gs

lemma compile_size (gs : List Gate) (m : ℕ) (σ : List (Option ℕ)) :
    (compile m σ gs).1.length + saved m σ gs = gs.length := by
  induction gs generalizing m σ with
  | nil => simp [compile, saved]
  | cons g gs ih =>
    have hstep := reduce_size m g.op (σ.getD (g.inputs.getD 0 0) none)
      (σ.getD (g.inputs.getD 1 0) none)
    have hrest := ih (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2])
    simp only [compile, saved, List.length_append, List.length_cons]
    change (emit m σ g).1.length + _ + _ = gs.length + 1
    change (emit m σ g).1.length + _ = 1 at hstep
    omega

lemma compile_correct (gs : List Gate) (σ : List (Option ℕ)) (s t : List Bool)
    (h : MapRel σ s t)
    (hbasis : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    Good t.length (compile t.length σ gs).1 ∧
      MapRel (compile t.length σ gs).2 (wiresFrom gs s)
        (wiresFrom (compile t.length σ gs).1 t) := by
  induction gs generalizing σ s t with
  | nil => exact ⟨True.intro, h⟩
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hbasis g List.mem_cons_self
    have hstep := mapRel_step σ s t g h hop hlen
    have hrest := ih (σ ++ [(emit t.length σ g).2])
      (s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)])
      (wiresFrom (emit t.length σ g).1 t) hstep
      (fun g' hg' => hbasis g' (List.mem_cons_of_mem g hg'))
    rw [length_wiresFrom] at hrest
    constructor
    · exact good_append _ _ _ (emit_good _ _ _ hop h.2.1) hrest.1
    · have hcons : wiresFrom (g :: gs) s =
          wiresFrom gs (s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]) := rfl
      simpa only [compile, wiresFrom_append, hcons] using hrest.2

def initialMap (n : ℕ) (z : Fin n) : List (Option ℕ) :=
  List.ofFn fun i : Fin n => if i = z then none else some i.val

lemma initial_rel (n : ℕ) (z : Fin n) (y : Fin n → Bool) :
    MapRel (initialMap n z) (List.ofFn (Function.update y z false)) (List.ofFn y) := by
  refine ⟨by simp [initialMap], ?_, ?_⟩
  · intro j
    by_cases hj : j < n
    · have he : (initialMap n z).getD j none =
          if (⟨j, hj⟩ : Fin n) = z then none else some j := by simp [initialMap, hj]
      rw [he]
      split <;> simp_all [Bound]
    · rw [List.getD_eq_default _ _ (by simp [initialMap]; omega)]
      simp [Bound]
  · intro j
    by_cases hj : j < n
    · by_cases he : (⟨j, hj⟩ : Fin n) = z
      · simp [initialMap, hj, he, readOption]
      · simp [initialMap, hj, he, readOption]
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp [initialMap]; omega)]
      rfl

lemma read_output (a : Option ℕ) (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).getD (a.getD (w.length + gs.length)) false =
      readOption a (wiresFrom gs w) := by
  cases a <;> simp [readOption, ← length_wiresFrom gs w]

def restricted (n : ℕ) (z : Fin n) (C : Circuit) : Circuit :=
  let r := compile n (initialMap n z) C.gates
  ⟨r.1, (r.2.getD C.output none).getD (n + r.1.length)⟩

def removalCount (n : ℕ) (z : Fin n) (C : Circuit) : ℕ :=
  saved n (initialMap n z) C.gates

lemma restricted_spec (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C) :
    IsAO2 n (restricted n z C) ∧
      circuitFun n (restricted n z C) =
        (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      (restricted n z C).size + removalCount n z C = C.size := by
  have hbasis : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    exact ⟨hAO.1 g hg, hAO.2.2 g hg⟩
  have hc (y : Fin n → Bool) :
      Good n (compile n (initialMap n z) C.gates).1 ∧
        MapRel (compile n (initialMap n z) C.gates).2
          (wiresFrom C.gates (List.ofFn (Function.update y z false)))
          (wiresFrom (compile n (initialMap n z) C.gates).1 (List.ofFn y)) := by
    simpa only [List.length_ofFn] using
      compile_correct C.gates (initialMap n z) _ _ (initial_rel n z y) hbasis
  refine ⟨good_ao2 _ _ _ (hc (fun _ => false)).1, ?_, ?_⟩
  · funext y
    change (wiresFrom (compile n (initialMap n z) C.gates).1 (List.ofFn y)).getD
        (((compile n (initialMap n z) C.gates).2.getD C.output none).getD
          (n + (compile n (initialMap n z) C.gates).1.length)) false = _
    have hout := read_output ((compile n (initialMap n z) C.gates).2.getD C.output none)
      (compile n (initialMap n z) C.gates).1 (List.ofFn y)
    simp only [List.length_ofFn] at hout
    rw [hout]
    exact ((hc y).2.2.2 C.output).symm
  · exact compile_size C.gates n (initialMap n z)

lemma exists_restriction (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      D.size + removalCount n z C ≤ C.size := by
  obtain ⟨hD, hF, hsize⟩ := restricted_spec n z C hAO
  exact ⟨restricted n z C, hD, hF, hsize.le⟩

def blockStep (op : GateOp) (a b : Bool) : Bool :=
  match op with
  | .or => a && b
  | _ => a || b

lemma reduce_dead (m : ℕ) (op : GateOp) (a b : Option ℕ) :
    (reduceGate m op a b).2.isNone = blockStep op a.isNone b.isNone := by
  cases a <;> cases b <;> cases op <;> rfl

lemma getD_map_none (σ : List (Option ℕ)) (i : ℕ) :
    (σ.map Option.isNone).getD i true = (σ.getD i none).isNone := by
  induction σ generalizing i with
  | nil => simp
  | cons a σ ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

def deadRun (bs : List Bool) : List Gate → List Bool × ℕ
  | [] => (bs, 0)
  | g :: gs =>
      let a := bs.getD (g.inputs.getD 0 0) true
      let b := bs.getD (g.inputs.getD 1 0) true
      let rest := deadRun (bs ++ [blockStep g.op a b]) gs
      (rest.1, (if a || b then 1 else 0) + rest.2)

lemma compile_dead (gs : List Gate) (m : ℕ) (σ : List (Option ℕ)) :
    (compile m σ gs).2.map Option.isNone = (deadRun (σ.map Option.isNone) gs).1 ∧
      saved m σ gs = (deadRun (σ.map Option.isNone) gs).2 := by
  induction gs generalizing m σ with
  | nil => exact ⟨rfl, rfl⟩
  | cons g gs ih =>
    have hstep : (σ ++ [(emit m σ g).2]).map Option.isNone =
        σ.map Option.isNone ++ [blockStep g.op (σ.getD (g.inputs.getD 0 0) none).isNone
          (σ.getD (g.inputs.getD 1 0) none).isNone] := by
      simp [emit, reduce_dead]
    have hrest := ih (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2])
    simp only [compile, saved, deadRun, getD_map_none]
    rw [← hstep]
    exact ⟨hrest.1, congrArg (fun k => _ + k) hrest.2⟩

def initialDead (n : ℕ) (z : Fin n) : List Bool :=
  List.ofFn fun i : Fin n => decide (i = z)

lemma initial_map_dead (n : ℕ) (z : Fin n) :
    (initialMap n z).map Option.isNone = initialDead n z := by
  simp only [initialMap, initialDead, List.map_ofFn]
  congr 1
  funext i
  by_cases h : i = z <;> simp [h]

def blockedWires (n : ℕ) (z : Fin n) (C : Circuit) : List Bool :=
  (deadRun (initialDead n z) C.gates).1

def blockedCount (n : ℕ) (z : Fin n) (C : Circuit) : ℕ :=
  (deadRun (initialDead n z) C.gates).2

lemma removal_eq_blocked (n : ℕ) (z : Fin n) (C : Circuit) :
    removalCount n z C = blockedCount n z C := by
  have h := (compile_dead C.gates n (initialMap n z)).2
  rw [initial_map_dead] at h
  exact h

lemma exists_blocked_restriction (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      D.size + blockedCount n z C = C.size := by
  obtain ⟨hD, hF, hsize⟩ := restricted_spec n z C hAO
  rw [removal_eq_blocked] at hsize
  exact ⟨restricted n z C, hD, hF, hsize⟩

lemma getD_map_not (s : List Bool) (i : ℕ) :
    (s.map Bool.not).getD i true = !(s.getD i false) := by
  induction s generalizing i with
  | nil => simp
  | cons a s ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

lemma blockStep_not (op : GateOp) (a b : Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    blockStep op (!a) (!b) = !(op.eval [a, b]) := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> rfl

lemma deadRun_values (gs : List Gate) (s : List Bool)
    (hbasis : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    (deadRun (s.map Bool.not) gs).1 = (wiresFrom gs s).map Bool.not := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hbasis g List.mem_cons_self
    have hgate : blockStep g.op ((s.map Bool.not).getD (g.inputs.getD 0 0) true)
        ((s.map Bool.not).getD (g.inputs.getD 1 0) true) =
        !(g.op.eval (g.inputs.map fun i => s.getD i false)) := by
      rw [getD_map_not, getD_map_not]
      obtain ⟨a, b, hg⟩ := List.length_eq_two.mp hlen
      simpa [hg] using blockStep_not g.op (s.getD a false) (s.getD b false) hop
    have hstep : s.map Bool.not ++
        [blockStep g.op ((s.map Bool.not).getD (g.inputs.getD 0 0) true)
          ((s.map Bool.not).getD (g.inputs.getD 1 0) true)] =
        (s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]).map Bool.not := by
      simp only [List.map_append, List.map_cons, List.map_nil, hgate]
    simp only [deadRun, hstep]
    exact ih _ (fun g' hg' => hbasis g' (List.mem_cons_of_mem g hg'))

lemma initialDead_values (n : ℕ) (z : Fin n) :
    initialDead n z = (List.ofFn (fun i : Fin n => decide (i ≠ z))).map Bool.not := by
  simp only [initialDead, List.map_ofFn]
  congr 1
  funext i
  by_cases h : i = z <;> simp [h]

lemma blockedWires_eq (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C) :
    blockedWires n z C =
      (C.wires (List.ofFn (fun i : Fin n => decide (i ≠ z)))).map Bool.not := by
  unfold blockedWires
  rw [initialDead_values]
  exact deadRun_values C.gates _ (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩)

end PEqualNP.Outside.L_meta_3566.FalseRestrict


namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def CutWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (C : Circuit) : Prop :=
  ∃ D : Circuit, IsAO2 n D ∧
    circuitFun n D = (fun y : Fin n → Bool =>
      @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧
        y a = true ∧ y b = true) (Classical.propDecidable _)) ∧
    D.size + G.degree z ≤ C.size ∧
    ((∃ S : Finset (Fin n),
      CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
      ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
      D.size + G.degree z + 1 ≤ C.size)

lemma cutWitness_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (C C' : Circuit) (hsize : C.size ≤ C'.size)
    (h : CutWitness G z C) : CutWitness G z C' := by
  obtain ⟨D, hAO, hfun, hsizeD, hbonus⟩ := h
  exact ⟨D, hAO, hfun, hsizeD.trans hsize, fun hdrop => (hbonus hdrop).trans hsize⟩

lemma exists_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = NestedCover.graphFun G ∅) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size ≤ C.size := by
  classical
  let P : ℕ → Prop := fun k => ∃ D : Circuit,
    IsAO2 n D ∧ circuitFun n D = NestedCover.graphFun G ∅ ∧ D.size = k
  have hex : ∃ k, P k := ⟨C.size, C, hAO, hfun, rfl⟩
  obtain ⟨D, hD, hfunD, hsizeD⟩ := Nat.find_spec hex
  have hmin : ∀ E : Circuit, IsAO2 n E →
      circuitFun n E = NestedCover.graphFun G ∅ → D.size ≤ E.size := by
    intro E hE hfunE
    rw [hsizeD]
    exact Nat.find_min' hex ⟨E, hE, hfunE, rfl⟩
  exact ⟨D, ⟨hD, hfunD, hmin⟩, hmin C hAO hfun⟩

lemma peel_of_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hpos : ∃ z : Fin n, 0 < G.degree z)
    (h : ∀ C : Circuit, IsLeastAO G C →
      ∃ z : Fin n, 0 < G.degree z ∧ CutWitness G z C) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = NestedCover.graphFun G ∅ → CutWitness G z C := by
  classical
  by_cases hex : ∃ C : Circuit,
      IsAO2 n C ∧ circuitFun n C = NestedCover.graphFun G ∅
  · obtain ⟨C, hAO, hfun⟩ := hex
    obtain ⟨D, hD, _⟩ := exists_least G C hAO hfun
    obtain ⟨z, hz, hcut⟩ := h D hD
    exact ⟨z, hz, fun E hE hfunE =>
      cutWitness_mono G z D E (hD.2.2 E hE hfunE) hcut⟩
  · obtain ⟨z, hz⟩ := hpos
    exact ⟨z, hz, fun C hAO hfun => (hex ⟨C, hAO, hfun⟩).elim⟩

end PEqualNP.Outside.L_meta_3566


namespace PEqualNP.Outside.L_meta_3566_aux

open PEqualNP.MetaComplexity

lemma cut_adj {n : ℕ} (G : SimpleGraph (Fin n)) (z a b : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).Adj a b ↔
      G.Adj a b ∧ a ≠ z ∧ b ≠ z := by
  rw [SimpleGraph.deleteEdges_adj, SimpleGraph.mk'_mem_incidenceSet_iff]
  tauto

lemma cut_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) :
    (fun y : Fin n → Bool =>
      @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧
        y a = true ∧ y b = true) (Classical.propDecidable _)) =
    (fun y => NestedCover.graphFun G ∅ (Function.update y z false)) := by
  classical
  funext y
  simp only [NestedCover.graphFun, Finset.notMem_empty, false_and, exists_false,
    decide_false, Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hab, haz, hbz⟩ := (cut_adj G z a b).mp hab
    exact ⟨a, b, hab, by simpa [Function.update_of_ne haz] using ha,
      by simpa [Function.update_of_ne hbz] using hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    have haz : a ≠ z := by
      intro h
      subst a
      simp at ha
    have hbz : b ≠ z := by
      intro h
      subst b
      simp at hb
    exact ⟨a, b, (cut_adj G z a b).mpr ⟨hab, haz, hbz⟩,
      by simpa [Function.update_of_ne haz] using ha,
      by simpa [Function.update_of_ne hbz] using hb⟩

end PEqualNP.Outside.L_meta_3566_aux


namespace PEqualNP.Outside.L_meta_3566

abbrev heawood : SimpleGraph (Fin 14) :=
  SimpleGraph.fromRel fun u v =>
    u.val < 7 ∧ 7 ≤ v.val ∧ (v.val - 7 + 7 - u.val) % 7 ∈ ([0, 1, 3] : List ℕ)

lemma heawood_bipartite :
    ∃ c : Fin 14 → Bool, ∀ u v : Fin 14, heawood.Adj u v → c u ≠ c v := by
  refine ⟨fun u => decide (u.val < 7), ?_⟩
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
lemma heawood_no_four : PEqualNP.TopForm.NoFourCycle heawood := by
  decide

lemma heawood_degree : ∀ z : Fin 14, heawood.degree z = 3 := by
  decide

lemma heawood_edges : heawood.edgeFinset.card = 21 := by
  decide

lemma heawood_no_leaf : ¬ ∃ z : Fin 14, heawood.degree z ≤ 2 := by
  intro ⟨z, hz⟩
  have hd := heawood_degree z
  omega


abbrev heawoodLeft (i : Fin 7) : Fin 14 := ⟨i.val, by omega⟩
abbrev heawoodRight (i : Fin 7) : Fin 14 := ⟨i.val + 7, by omega⟩

lemma heawood_matching : ∀ i : Fin 7, heawood.Adj (heawoodLeft i) (heawoodRight i) := by
  decide

lemma heawood_cover_lower (S : Finset (Fin 14))
    (hS : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover heawood S) :
    7 ≤ S.card := by
  let f (i : Fin 7) : Fin 14 := if heawoodLeft i ∈ S then heawoodLeft i else heawoodRight i
  have hmem (i : Fin 7) : f i ∈ S := by
    dsimp [f]
    split_ifs with h
    · exact h
    · exact (hS _ _ (heawood_matching i)).resolve_left h
  have hfmod (i : Fin 7) : (f i).val % 7 = i.val := by
    dsimp [f]
    split_ifs <;> dsimp [heawoodLeft, heawoodRight] <;> omega
  have hinj : Function.Injective (fun i : Fin 7 => (⟨f i, hmem i⟩ : S)) := by
    intro i j hij
    have heq : f i = f j := congrArg Subtype.val hij
    have hi := hfmod i
    have hj := hfmod j
    apply Fin.ext
    rw [heq] at hi
    omega
  have hc := Fintype.card_le_of_injective _ hinj
  simpa using hc

abbrev heawoodCover : Finset (Fin 14) := Finset.univ.filter (fun z => z.val < 7)

lemma heawood_cover_valid :
    PEqualNP.MetaComplexity.CoverPromise.IsVertexCover heawood heawoodCover := by
  unfold PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
  decide

lemma heawood_cover_card : heawoodCover.card = 7 := by
  decide


abbrev heawoodCutCover (z : Fin 14) : Finset (Fin 14) :=
  Finset.univ.filter (fun v => (v.val < 7 ↔ z.val < 7) ∧ v ≠ z)

set_option synthInstance.maxSize 1000 in
lemma heawood_cut_cover_valid : ∀ z : Fin 14,
    PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
      (heawood.deleteEdges (heawood.incidenceSet z)) (heawoodCutCover z) := by
  unfold PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
  simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.mk'_mem_incidenceSet_iff]
  decide

lemma heawood_cut_cover_card : ∀ z : Fin 14, (heawoodCutCover z).card = 6 := by
  decide

lemma heawood_cut_cover_drop (z : Fin 14) :
    ∃ S : Finset (Fin 14), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
        (heawood.deleteEdges (heawood.incidenceSet z)) S ∧
      ∀ T : Finset (Fin 14), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover heawood T →
        S.card < T.card := by
  refine ⟨heawoodCutCover z, heawood_cut_cover_valid z, ?_⟩
  intro T hT
  have h := heawood_cover_lower T hT
  rw [heawood_cut_cover_card]
  omega


lemma heawood_cut_cover_lower (z : Fin 14) (S : Finset (Fin 14))
    (hS : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
      (heawood.deleteEdges (heawood.incidenceSet z)) S) :
    6 ≤ S.card := by
  have hfull : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover heawood (insert z S) := by
    intro a b hab
    by_cases hza : z = a
    · exact Or.inl (by simp [← hza])
    by_cases hzb : z = b
    · exact Or.inr (by simp [← hzb])
    have hcut : (heawood.deleteEdges (heawood.incidenceSet z)).Adj a b := by
      simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.mk'_mem_incidenceSet_iff]
      exact ⟨hab, fun h => h.2.elim hza hzb⟩
    rcases hS a b hcut with ha | hb
    · exact Or.inl (Finset.mem_insert_of_mem ha)
    · exact Or.inr (Finset.mem_insert_of_mem hb)
  have h := heawood_cover_lower (insert z S) hfull
  have hcard := Finset.card_insert_le z S
  omega


namespace Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge

abbrev Src (n : ℕ) (ι : Type) := Option (Fin n ⊕ ι)


def srcAt {n : ℕ} {ι : Type} (x : Fin n → Bool) (t : ι → Bool) (s : Src n ι) : Bool :=
  s.elim false (Sum.elim x t)


def opv (a : Bool) (p q : Bool) : Bool := if a then p && q else p || q

lemma opv_mono (a p q p' q' : Bool) (h : p = true → p' = true) (h' : q = true → q' = true) :
    opv a p q = true → opv a p' q' = true := by
  cases a <;> cases p <;> cases q <;> cases p' <;> cases q' <;> simp_all [opv]

abbrev Prog (n : ℕ) (ι : Type) := (ι → Bool) × (ι → Fin 2 → Src n ι)

def Prog.isAnd {n : ℕ} {ι : Type} (P : Prog n ι) : ι → Bool := P.1

def Prog.src {n : ℕ} {ι : Type} (P : Prog n ι) : ι → Fin 2 → Src n ι := P.2

variable {n : ℕ} {ι : Type}


def Closed (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) : Prop :=
  ∀ i ∈ K, ∀ b : Fin 2, ∀ j : ι, P.src i b = some (Sum.inr j) → j ∈ K ∧ rank j < rank i


def SolAt (P : Prog n ι) (K : Finset ι) (x : Fin n → Bool) (t : ι → Bool) : Prop :=
  ∀ i ∈ K, t i = opv (P.isAnd i) (srcAt x t (P.src i 0)) (srcAt x t (P.src i 1))


def Sol (P : Prog n ι) (K : Finset ι) (v : ι → (Fin n → Bool) → Bool) : Prop :=
  ∀ x, SolAt P K x (fun i => v i x)

lemma wires_length (gs : List Gate) (w0 : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs generalizing w0 with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

lemma wires_snoc (gs : List Gate) (g : Gate) (o : ℕ) (x : List Bool) :
    (⟨gs ++ [g], o⟩ : Circuit).wires x = (⟨gs, o⟩ : Circuit).wires x
      ++ [g.op.eval (g.inputs.map fun i => ((⟨gs, o⟩ : Circuit).wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

lemma wireVal_old (gs : List Gate) (g : Gate) (w : ℕ) (hw : w < n + gs.length) (x : Fin n → Bool) :
    wireVal n ⟨gs ++ [g], 0⟩ w x = wireVal n ⟨gs, 0⟩ w x := by
  unfold wireVal
  rw [wires_snoc, List.getD_append]
  have : ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + gs.length := by
    have h := wires_length gs (List.ofFn x)
    rw [List.length_ofFn] at h
    exact h
  omega

lemma wireVal_new (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wireVal n ⟨gs ++ [g], 0⟩ (n + gs.length) x
      = g.op.eval (g.inputs.map fun i => wireVal n ⟨gs, 0⟩ i x) := by
  unfold wireVal
  have : ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + gs.length := by
    have h := wires_length gs (List.ofFn x)
    rw [List.length_ofFn] at h
    exact h
  rw [wires_snoc, List.getD_append_right _ _ _ _ (by omega), this]
  simp

lemma wires_prefix (gs : List Gate) (w0 : List Bool) (i : ℕ) (hi : i < w0.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).getD i false
      = w0.getD i false := by
  induction gs generalizing w0 with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma wireVal_input (gs : List Gate) (i : Fin n) (x : Fin n → Bool) :
    wireVal n ⟨gs, 0⟩ (i : ℕ) x = x i := by
  unfold wireVal Circuit.wires
  rw [wires_prefix _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]


def Res (gs : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ x, f x = false) ∨ (f (fun _ => true) = true ∧ ∃ w < n + gs.length, ∀ x, wireVal n ⟨gs, 0⟩ w x = f x)

lemma res_mono (gs : List Gate) (g : Gate) (f : (Fin n → Bool) → Bool) (h : Res gs f) :
    Res (gs ++ [g]) f := by
  rcases h with h | ⟨h1, w, hw, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, w, by simp; omega, fun x => ?_⟩
    rw [wireVal_old gs g w hw x, h2 x]

lemma isAO2_snoc (gs : List Gate) (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (a b : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length) (h : IsAO2 n ⟨gs, 0⟩) :
    IsAO2 n ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h1 g hg
    · rw [List.mem_singleton.1 hg]
      exact ho
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < gs.length
    · have e : gateAt ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        exact List.getD_append _ _ _ _ hjl
      rw [e] at hi
      exact h2 j hjl i hi
    · have hj' : j = gs.length := by omega
      subst hj'
      have e : gateAt ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ gs.length = ⟨o, [a, b]⟩ := by
        simp [gateAt]
      rw [e] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h3 g hg
    · rw [List.mem_singleton.1 hg]
      rfl


def kept (P : Prog n ι) (v : ι → (Fin n → Bool) → Bool) (K : Finset ι) : Finset ι :=
  K.filter fun i => srcAt (fun _ => true) (fun j => v j fun _ => true) (P.src i 0) = true ∧
    srcAt (fun _ => true) (fun j => v j fun _ => true) (P.src i 1) = true

lemma build (P : Prog n ι) (rank : ι → ℕ) (v : ι → (Fin n → Bool) → Bool) (K : Finset ι)
    (hcl : Closed P rank K) (hv : Sol P K v) :
    ∃ gs : List Gate, IsAO2 n ⟨gs, 0⟩ ∧ gs.length ≤ (kept P v K).card ∧ ∀ i ∈ K, Res gs (v i) := by
  classical
  induction K using Finset.induction_on_max_value rank with
  | empty =>
    refine ⟨[], ⟨?_, ?_, ?_⟩, by simp, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · intro g hg; simp at hg
    · intro j hj; simp at hj
    · intro g hg; simp at hg
  | insert a s ha hmax ih =>
    have hs : Closed P rank s := by
      intro i hi b j hj
      obtain ⟨h1, h2⟩ := hcl i (Finset.mem_insert_of_mem hi) b j hj
      refine ⟨(Finset.mem_insert.1 h1).resolve_left ?_, h2⟩
      rintro rfl
      exact absurd (hmax i hi) (by omega)
    obtain ⟨gs, hAO, hlen, hres⟩ := ih hs fun x i hi => hv x i (Finset.mem_insert_of_mem hi)
    have hsrc' : ∀ b : Fin 2, Res gs (fun x => srcAt x (fun j => v j x) (P.src a b)) := by
      intro b
      rcases hb : P.src a b with _ | (c | j)
      · exact Or.inl fun x => rfl
      · exact Or.inr ⟨rfl, c, by have := c.2; omega, fun x => wireVal_input gs c x⟩
      · obtain ⟨h1, h2⟩ := hcl a (Finset.mem_insert_self a s) b j hb
        refine hres j ((Finset.mem_insert.1 h1).resolve_left ?_)
        rintro rfl
        exact absurd h2 (lt_irrefl _)
    have hsrc : ∀ b : Fin 2, (∀ x, srcAt x (fun j => v j x) (P.src a b) = false) ∨
        (srcAt (fun _ => true) (fun j => v j fun _ => true) (P.src a b) = true ∧ ∃ w < n + gs.length,
          ∀ x, wireVal n ⟨gs, 0⟩ w x = srcAt x (fun j => v j x) (P.src a b)) := hsrc'
    have hva : ∀ x, v a x = opv (P.isAnd a) (srcAt x (fun j => v j x) (P.src a 0))
        (srcAt x (fun j => v j x) (P.src a 1)) := fun x => hv x a (Finset.mem_insert_self a s)
    have hsub : kept P v s ⊆ kept P v (insert a s) :=
      Finset.filter_subset_filter _ (Finset.subset_insert a s)
    have hlen' : gs.length ≤ (kept P v (insert a s)).card := hlen.trans (Finset.card_le_card hsub)
    have same : Res gs (v a) → ∃ gs : List Gate, IsAO2 n ⟨gs, 0⟩ ∧
        gs.length ≤ (kept P v (insert a s)).card ∧ ∀ i ∈ insert a s, Res gs (v i) := by
      intro h
      refine ⟨gs, hAO, hlen', fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · exact h
      · exact hres i hi'
    rcases hsrc 0 with h0 | ⟨h0, w0, hw0, hv0⟩
    · -- first operand constant false
      refine same ?_
      cases hop : P.isAnd a
      · rcases hsrc 1 with h1 | ⟨h1, w1, hw1, hv1⟩
        · exact Or.inl fun x => by rw [hva x, h0 x, h1 x, hop]; rfl
        · refine Or.inr ⟨by rw [hva, h0, h1, hop]; rfl, w1, hw1, fun x => ?_⟩
          rw [hv1 x, hva x, h0 x, hop]; simp [opv]
      · exact Or.inl fun x => by rw [hva x, h0 x, hop]; rfl
    · rcases hsrc 1 with h1 | ⟨h1, w1, hw1, hv1⟩
      · refine same ?_
        cases hop : P.isAnd a
        · refine Or.inr ⟨by rw [hva, h0, h1, hop]; rfl, w0, hw0, fun x => ?_⟩
          rw [hv0 x, hva x, h1 x, hop]; simp [opv]
        · exact Or.inl fun x => by rw [hva x, h1 x, hop]; simp [opv]
      · -- both operands kept: append a gate
        have hak : a ∈ kept P v (insert a s) :=
          Finset.mem_filter.2 ⟨Finset.mem_insert_self a s, h0, h1⟩
        have hcard : (kept P v s).card + 1 ≤ (kept P v (insert a s)).card := by
          have hnot : a ∉ kept P v s := fun h => ha (Finset.mem_filter.1 h).1
          rw [← Finset.card_insert_of_notMem hnot]
          exact Finset.card_le_card (Finset.insert_subset hak hsub)
        let o : GateOp := if P.isAnd a then GateOp.and else GateOp.or
        have ho : o = GateOp.and ∨ o = GateOp.or := by
          by_cases h : P.isAnd a = true <;> simp [o, h]
        refine ⟨gs ++ [⟨o, [w0, w1]⟩], isAO2_snoc gs o ho w0 w1 hw0 hw1 hAO, ?_, fun i hi => ?_⟩
        · simp only [List.length_append, List.length_singleton]; omega
        · rcases Finset.mem_insert.1 hi with rfl | hi'
          · refine Or.inr ⟨?_, n + gs.length, by simp, fun x => ?_⟩
            · rw [hva]
              simp only at h0 h1
              rw [h0, h1]
              cases P.isAnd i <;> rfl
            · rw [wireVal_new, hva x]
              simp only [List.map_cons, List.map_nil, hv0 x, hv1 x]
              by_cases h : P.isAnd i = true
              · simp [o, h, opv, GateOp.eval]
              · simp [o, h, opv, GateOp.eval]
          · exact res_mono gs _ _ (hres i hi')

lemma zero_ao (n : ℕ) : IsAO2 n ⟨[], n⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg; simp at hg
  · intro j hj; simp at hj
  · intro g hg; simp at hg

lemma zero_fun (n : ℕ) : circuitFun n ⟨[], n⟩ = fun _ => false := by
  funext x
  simp [circuitFun, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]

lemma fold_total (P : Prog n ι) (rank : ι → ℕ)
    (v : ι → (Fin n → Bool) → Bool) (K : Finset ι)
    (hcl : Closed P rank K) (hv : Sol P K v) (o : Src n ι)
    (ho : ∀ j, o = some (Sum.inr j) → j ∈ K) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ (kept P v K).card ∧
      ∀ x : Fin n → Bool, circuitFun n D x = srcAt x (fun j => v j x) o := by
  obtain ⟨gs, hAO, hlen, hres⟩ := build P rank v K hcl hv
  have hR : Res gs (fun x => srcAt x (fun j => v j x) o) := by
    rcases o with _ | (c | j)
    · exact Or.inl fun x => rfl
    · exact Or.inr ⟨rfl, c, by have := c.2; omega, fun x => wireVal_input gs c x⟩
    · exact hres j (ho j rfl)
  rcases hR with h | ⟨_, w, _, hw⟩
  · refine ⟨⟨[], n⟩, zero_ao n, Nat.zero_le _, fun x => ?_⟩
    rw [zero_fun]
    exact (h x).symm
  · refine ⟨⟨gs, w⟩, ⟨hAO.1, hAO.2.1, hAO.2.2⟩, hlen, fun x => hw x⟩

open PEqualNP.EdgeOwnership (gateVal)

def srcOf (n w : ℕ) : Src n ℕ := if h : w < n then some (Sum.inl ⟨w, h⟩) else some (Sum.inr (w - n))

lemma srcOf_inr (w j : ℕ) (h : srcOf n w = some (Sum.inr j)) : w = n + j := by
  unfold srcOf at h
  split_ifs at h with hw
  · simp at h
  · simp only [Option.some.injEq, Sum.inr.injEq] at h
    omega


def isA : GateOp → Bool
  | GateOp.and => true
  | _ => false


def progOf (C : Circuit) (ρ : ℕ → Fin 2 → Src n ℕ) : Prog n ℕ :=
  ⟨fun i => isA (gateAt C i).op, ρ⟩

lemma wireVal_lt (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal Circuit.wires
  rw [wires_prefix _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma srcAt_srcOf (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    srcAt x (fun j => gateVal n C j x) (srcOf n w) = wireVal n C w x := by
  unfold srcOf
  split_ifs with hw
  · exact (wireVal_lt C w hw x).symm
  · show gateVal n C (w - n) x = _
    have : n + (w - n) = w := by omega
    unfold gateVal wireVal
    rw [this]


lemma gate_eq (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) (x : Fin n → Bool) :
    gateVal n C k x = opv (isA (gateAt C k).op) (wireVal n C (opnd C k 0) x)
      (wireVal n C (opnd C k 1) x) := by
  have hg : C.gates[k]? = some (gateAt C k) := by
    simp [gateAt, List.getD_eq_getElem?_getD, hk]
  have hmem : gateAt C k ∈ C.gates := List.mem_of_getElem? hg
  have hlen := hC.2.2 _ hmem
  have hop := hC.1 _ hmem
  have hback := hC.2.1 k hk
  have hsplit : C.gates = C.gates.take k ++ gateAt C k :: C.gates.drop (k + 1) := by
    have h := List.take_append_drop k C.gates
    rw [List.drop_eq_getElem_cons hk] at h
    have e : C.gates[k] = gateAt C k := by simp [gateAt, List.getD_eq_getElem?_getD, hk]
    rw [e] at h
    exact h.symm
  have htake : (C.gates.take k).length = k := by simp; omega
  have hold : ∀ w < n + k, wireVal n C w x = wireVal n ⟨C.gates.take k, 0⟩ w x := by
    intro w hw
    unfold wireVal Circuit.wires
    conv_lhs => rw [hsplit, List.foldl_append]
    rw [wires_prefix]
    rw [wires_length, htake]
    simpa using hw
  have hnew : gateVal n C k x = (gateAt C k).op.eval
      ((gateAt C k).inputs.map fun i => wireVal n ⟨C.gates.take k, 0⟩ i x) := by
    rw [← wireVal_new, htake]
    unfold gateVal wireVal Circuit.wires
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [wires_prefix]
    · simp [List.foldl_append]
    · rw [List.length_append, wires_length, htake, List.length_ofFn]; simp
  obtain ⟨p, q, hpq⟩ : ∃ p q, (gateAt C k).inputs = [p, q] := List.length_eq_two.1 hlen
  have hp : p < n + k := hback p (by rw [hpq]; simp)
  have hq : q < n + k := hback q (by rw [hpq]; simp)
  rw [hnew]
  simp only [opnd, hpq, List.map_cons, List.map_nil, ← hold p hp, ← hold q hq]
  rcases hop with h | h <;> simp [h, GateOp.eval, opv, isA]


lemma prune_closed (C : Circuit) (hC : IsAO2 n C) (K : Finset ℕ)
    (hK : ∀ k ∈ K, k < C.gates.length)
    (hcl : ∀ k ∈ K, ∀ w ∈ (gateAt C k).inputs, n ≤ w → w - n ∈ K)
    (ho : ∀ j, srcOf n C.output = some (Sum.inr j) → j ∈ K) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ K.card ∧ circuitFun n D = circuitFun n C := by
  let P : Prog n ℕ := progOf C fun k b => srcOf n (opnd C k b)
  let v : ℕ → (Fin n → Bool) → Bool := fun k x => gateVal n C k x
  have hback : ∀ k ∈ K, ∀ b : Fin 2, opnd C k b ∈ (gateAt C k).inputs := by
    intro k hk b
    have hm : gateAt C k ∈ C.gates := by
      exact List.mem_of_getElem? (show C.gates[k]? = some (gateAt C k) by
        simp [gateAt, List.getD_eq_getElem?_getD, hK k hk])
    have hlen := hC.2.2 _ hm
    have hb : b.val < (gateAt C k).inputs.length := by rw [hlen]; exact b.isLt
    exact List.mem_of_getElem? (show (gateAt C k).inputs[b.val]? = some (opnd C k b) by
      simp [opnd, List.getD_eq_getElem?_getD, hb])
  have hclosed : Closed P id K := by
    intro k hk b j hsrc
    change srcOf n (opnd C k b) = some (Sum.inr j) at hsrc
    have hw := srcOf_inr (opnd C k b) j hsrc
    have hlt := hC.2.1 k (hK k hk) (opnd C k b) (hback k hk b)
    refine ⟨?_, ?_⟩
    · have hmem := hcl k hk (opnd C k b) (hback k hk b) (by omega)
      simpa [hw] using hmem
    · simpa using (show j < k by omega)
  have hsol : Sol P K v := by
    intro x k hk
    change gateVal n C k x = opv (isA (gateAt C k).op)
      (srcAt x (fun j => gateVal n C j x) (srcOf n (opnd C k 0)))
      (srcAt x (fun j => gateVal n C j x) (srcOf n (opnd C k 1)))
    rw [srcAt_srcOf, srcAt_srcOf]
    exact gate_eq C hC k (hK k hk) x
  obtain ⟨D, hD, hsize, hfun⟩ := fold_total P id v K hclosed hsol (srcOf n C.output) ho
  refine ⟨D, hD, hsize.trans (Finset.card_filter_le K _), funext fun x => ?_⟩
  rw [hfun x]
  exact srcAt_srcOf C C.output x

lemma prune_complement (C : Circuit) (hC : IsAO2 n C) (J : Finset ℕ)
    (hJ : J ⊆ Finset.range C.size)
    (hcl : ∀ k < C.size, k ∉ J → ∀ w ∈ (gateAt C k).inputs,
      n ≤ w → w - n ∉ J)
    (ho : C.output < n + C.size)
    (hjout : n ≤ C.output → C.output - n ∉ J) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + J.card ≤ C.size ∧
      circuitFun n D = circuitFun n C := by
  classical
  let K := Finset.range C.size \ J
  have hK : ∀ k ∈ K, k < C.gates.length := by
    intro k hk
    exact Finset.mem_range.mp (Finset.mem_sdiff.mp hk).1
  have hclosed : ∀ k ∈ K, ∀ w ∈ (gateAt C k).inputs, n ≤ w → w - n ∈ K := by
    intro k hk w hw hwn
    obtain ⟨hkr, hkj⟩ := Finset.mem_sdiff.mp hk
    have hkl := Finset.mem_range.mp hkr
    have hwl := hC.2.1 k hkl w hw
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_range.mpr (by omega),
      hcl k hkl hkj w hw hwn⟩
  have hout : ∀ j, srcOf n C.output = some (Sum.inr j) → j ∈ K := by
    intro j hj
    have heq := srcOf_inr C.output j hj
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_range.mpr (by omega), by simpa [heq] using hjout (by omega)⟩
  obtain ⟨D, hD, hs, hf⟩ := prune_closed C hC K hK hclosed hout
  refine ⟨D, hD, ?_, hf⟩
  have hcard : K.card + J.card = C.size := by
    simpa [K] using Finset.card_sdiff_add_card_eq_card hJ
  omega

lemma erase_unread (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (hj : j < C.size)
    (hread : ∀ k < C.size, k ≠ j → n + j ∉ (gateAt C k).inputs)
    (ho : C.output < n + C.size) (hjo : C.output ≠ n + j) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 1 ≤ C.size ∧
      circuitFun n D = circuitFun n C := by
  classical
  apply prune_complement C hC {j}
  · simpa using hj
  · intro k hk hkj w hw hwn
    have hkj' : k ≠ j := by simpa using hkj
    intro hmem
    have heq : w - n = j := by simpa using hmem
    have hwj : w = n + j := by omega
    exact hread k hk hkj' (hwj ▸ hw)
  · exact ho
  · intro hn hmem
    have heq : C.output - n = j := by simpa using hmem
    exact hjo (by omega)

def WireStep (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  ∃ k < C.size, a = n + k ∧ b ∈ (gateAt C k).inputs

noncomputable def liveGates (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter fun k =>
    Relation.ReflTransGen (WireStep n C) C.output (n + k)

lemma prune_reachable (C : Circuit) (hC : IsAO2 n C)
    (ho : C.output < n + C.size) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ (liveGates n C).card ∧
      circuitFun n D = circuitFun n C := by
  classical
  apply prune_closed C hC (liveGates n C)
  · intro k hk
    exact Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  · intro k hk w hw hwn
    obtain ⟨hkr, hreach⟩ := Finset.mem_filter.mp hk
    have hkl := Finset.mem_range.mp hkr
    have hwl := hC.2.1 k hkl w hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    have hnext : WireStep n C (n + k) w := ⟨k, hkl, rfl, hw⟩
    have hfull := hreach.tail hnext
    simpa [Nat.add_sub_of_le hwn] using hfull
  · intro j hj
    have heq := srcOf_inr C.output j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [heq]

lemma least_all_live (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (ho : C.output < n + C.size) :
    liveGates n C = Finset.range C.size := by
  classical
  obtain ⟨D, hD, hs, hf⟩ := prune_reachable C hC.1 ho
  have hmin := hC.2.2 D hD (hf.trans hC.2.1)
  have hsub : liveGates n C ⊆ Finset.range C.size := Finset.filter_subset _ _
  apply Finset.eq_of_subset_of_card_le hsub
  simpa using hmin.trans hs

end Pruning

end PEqualNP.Outside.L_meta_3566


namespace PEqualNP.Outside.L_meta_3566.Equivalence

namespace Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

def Good (m : ℕ) (gs : List Gate) : Prop :=
  ∀ k g, gs[k]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
      ∀ i ∈ g.inputs, i < m + k

lemma good_append {m : ℕ} {gs₁ gs₂ : List Gate}
    (h₁ : Good m gs₁) (h₂ : Good (m + gs₁.length) gs₂) : Good m (gs₁ ++ gs₂) := by
  intro k g hk
  rw [List.getElem?_append] at hk
  split at hk
  · exact h₁ k g hk
  · obtain ⟨hop, hlen, hi⟩ := h₂ (k - gs₁.length) g hk
    exact ⟨hop, hlen, fun i h => by have := hi i h; omega⟩

lemma good_single {m o₁ o₂ : ℕ} {op : GateOp}
    (hop : op = GateOp.and ∨ op = GateOp.or) (h₁ : o₁ < m) (h₂ : o₂ < m) :
    Good m [⟨op, [o₁, o₂]⟩] := by
  intro k g hk
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst g
    refine ⟨hop, rfl, ?_⟩
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  | succ k => simp at hk

lemma good_ao2 {m : ℕ} {gs : List Gate} {out : ℕ} (h : Good m gs) :
    PEqualNP.TopForm.IsAO2 m ⟨gs, out⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg
    exact (h k g hk).1
  · intro j hj i hi
    have hj' : gs[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, out⟩ j) := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
    exact (h j _ hj').2.2 i hi
  · intro g hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg
    exact (h k g hk).2.1

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), Good m gs ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

lemma bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

lemma bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

lemma bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp [Good], le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

lemma bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · apply good_append (good_append ok1 ok2)
    apply good_single hop <;> simp only [List.length_append] <;> omega
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

lemma bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

lemma bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

lemma bld_aoCircuit {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    ∃ C : Circuit, PEqualNP.TopForm.IsAO2 n C ∧ C.size ≤ s ∧ circuitFun n C = F := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, good_ao2 ok, len, ?_⟩
  funext x
  have e := ev (List.ofFn x) (by simp)
  simp only [circuitFun, Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

lemma bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

lemma bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

lemma bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩

    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var t) (bld_anyFinset S hSne)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

lemma edge_upper : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → ∃ C : Circuit, PEqualNP.TopForm.IsAO2 n C ∧ C.size ≤ G.edgeFinset.card + T.card - 1 ∧ circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  intro n G _ T hE hc
  obtain ⟨i0, j0, h0⟩ := hE
  have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hc a b he with h | h
    · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
  apply bld_aoCircuit
  refine bld_congr (bld_edges n T G.edgeFinset hne cov) ?_
  intro x
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, h⟩
    revert he h
    refine Sym2.ind (fun a b => ?_) e
    intro he h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨s(i, j), by simpa using hij, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption

lemma graph_upper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (he : ∃ a b, G.Adj a b)
    (hc : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      D.size + 1 ≤ G.edgeFinset.card + T.card := by
  obtain ⟨D, hD, hsize, hfun⟩ := edge_upper n G T he hc
  obtain ⟨a, b, hab⟩ := he
  have hpos : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨s(a,b), by simpa using hab⟩
  refine ⟨D, hD, ?_, by omega⟩
  rw [hfun]
  funext x
  simp [PEqualNP.MetaComplexity.NestedCover.graphFun]

end Upper

open PEqualNP.MetaComplexity.CoverPromise

lemma cut_adj_iff {n : ℕ} (G : SimpleGraph (Fin n)) (z a b : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).Adj a b ↔ G.Adj a b ∧ a ≠ z ∧ b ≠ z :=
  SimpleGraph.deleteIncidenceSet_adj

lemma cut_cover_restrict {n : ℕ} (G : SimpleGraph (Fin n))
    (z : Fin n) (S : Finset (Fin n)) (hS : IsVertexCover G S) :
    IsVertexCover (G.deleteEdges (G.incidenceSet z)) S := by
  intro a b hab
  exact hS a b ((cut_adj_iff G z a b).mp hab).1

lemma cut_cover_erase {n : ℕ} (G : SimpleGraph (Fin n))
    (z : Fin n) (S : Finset (Fin n)) (hS : IsVertexCover G S) :
    IsVertexCover (G.deleteEdges (G.incidenceSet z)) (S.erase z) := by
  intro a b hab
  obtain ⟨hab, haz, hbz⟩ := (cut_adj_iff G z a b).mp hab
  rcases hS a b hab with ha | hb
  · exact Or.inl (Finset.mem_erase.mpr ⟨haz, ha⟩)
  · exact Or.inr (Finset.mem_erase.mpr ⟨hbz, hb⟩)

lemma cut_cover_insert {n : ℕ} (G : SimpleGraph (Fin n))
    (z : Fin n) (S : Finset (Fin n))
    (hS : IsVertexCover (G.deleteEdges (G.incidenceSet z)) S) :
    IsVertexCover G (insert z S) := by
  intro a b hab
  by_cases ha : a = z
  · left; simp [ha]
  by_cases hb : b = z
  · right; simp [hb]
  rcases hS a b ((cut_adj_iff G z a b).mpr ⟨hab, ha, hb⟩) with h | h
  · exact Or.inl (Finset.mem_insert_of_mem h)
  · exact Or.inr (Finset.mem_insert_of_mem h)

lemma exists_min_cover {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ T : Finset (Fin n), IsVertexCover G T ∧
      ∀ U : Finset (Fin n), IsVertexCover G U → T.card ≤ U.card := by
  classical
  have hex : ∃ k : ℕ, ∃ T : Finset (Fin n), IsVertexCover G T ∧ T.card = k := by
    exact ⟨(Finset.univ : Finset (Fin n)).card, Finset.univ,
      fun _ _ _ => Or.inl (Finset.mem_univ _), rfl⟩
  obtain ⟨T, hT, hcard⟩ := Nat.find_spec hex
  refine ⟨T, hT, ?_⟩
  intro U hU
  rw [hcard]
  exact Nat.find_min' hex ⟨U, hU, rfl⟩

lemma cover_drop_iff_min_cover_contains {n : ℕ} (G : SimpleGraph (Fin n))
    (z : Fin n) :
    (∃ S : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
      ∀ T : Finset (Fin n), IsVertexCover G T → S.card < T.card) ↔
    ∃ T : Finset (Fin n), IsVertexCover G T ∧ z ∈ T ∧
      ∀ U : Finset (Fin n), IsVertexCover G U → T.card ≤ U.card := by
  classical
  constructor
  · rintro ⟨S, hS, hdrop⟩
    obtain ⟨T, hT, hmin⟩ := exists_min_cover G
    have hins := cut_cover_insert G z S hS
    have hlt := hdrop T hT
    have hle := hmin (insert z S) hins
    have hcard := Finset.card_insert_le z S
    refine ⟨insert z S, hins, Finset.mem_insert_self z S, ?_⟩
    intro U hU
    have hTU := hmin U hU
    omega
  · rintro ⟨T, hT, hz, hmin⟩
    refine ⟨T.erase z, cut_cover_erase G z T hT, ?_⟩
    intro U hU
    have hTU := hmin U hU
    have hcard := Finset.card_erase_add_one hz
    omega

lemma exists_positive_vertex_with_residual_edge {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧
      (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty := by
  classical
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp (show 1 < G.edgeFinset.card by omega)
  induction e using Sym2.inductionOn with
  | _ a b =>
    induction f using Sym2.inductionOn with
    | _ c d =>
      have hab : G.Adj a b := G.mem_edgeFinset.mp he
      have hcd : G.Adj c d := G.mem_edgeFinset.mp hf
      have hout : (c ≠ a ∧ c ≠ b) ∨ (d ≠ a ∧ d ≠ b) := by
        by_contra h
        have hc : c = a ∨ c = b := by tauto
        have hd : d = a ∨ d = b := by tauto
        rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
        all_goals simp_all
      rcases hout with ⟨hca, hcb⟩ | ⟨hda, hdb⟩
      · refine ⟨c, (G.degree_pos_iff_exists_adj c).mpr ⟨d, hcd⟩, s(a,b), ?_⟩
        exact (G.deleteEdges (G.incidenceSet c)).mem_edgeFinset.mpr
          ((cut_adj_iff G c a b).mpr ⟨hab, hca.symm, hcb.symm⟩)
      · refine ⟨d, (G.degree_pos_iff_exists_adj d).mpr ⟨c, hcd.symm⟩, s(a,b), ?_⟩
        exact (G.deleteEdges (G.incidenceSet d)).mem_edgeFinset.mpr
          ((cut_adj_iff G d a b).mpr ⟨hab, hda.symm, hdb.symm⟩)

lemma cut_edge_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).edgeFinset.card + G.degree z =
      G.edgeFinset.card := by
  classical
  change (G.deleteIncidenceSet z).edgeFinset.card + G.degree z = G.edgeFinset.card
  rw [G.edgeFinset_deleteIncidenceSet_eq_sdiff z,
    ← SimpleGraph.card_incidenceFinset_eq_degree]
  exact Finset.card_sdiff_add_card_eq_card (G.incidenceFinset_subset z)

lemma cut_no_four_cycle {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (z : Fin n) (hG : PEqualNP.TopForm.NoFourCycle G) :
    PEqualNP.TopForm.NoFourCycle (G.deleteEdges (G.incidenceSet z)) := by
  classical
  intro a b hab
  apply le_trans (Finset.card_le_card ?_) (hG a b hab)
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  exact ⟨((cut_adj_iff G z a w).mp hw.1).1,
    ((cut_adj_iff G z b w).mp hw.2).1⟩

lemma cut_bipartition {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (hG : ∃ c : Fin n → Bool, ∀ a b, G.Adj a b → c a ≠ c b) :
    ∃ c : Fin n → Bool, ∀ a b,
      (G.deleteEdges (G.incidenceSet z)).Adj a b → c a ≠ c b := by
  obtain ⟨c, hc⟩ := hG
  exact ⟨c, fun a b hab => hc a b ((cut_adj_iff G z a b).mp hab).1⟩

lemma graph_fun_empty_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ =
      (fun y : Fin n → Bool => @decide
        (∃ a b : Fin n, G.Adj a b ∧ y a = true ∧ y b = true)
        (Classical.propDecidable _)) := by
  classical
  funext y
  simp [PEqualNP.MetaComplexity.NestedCover.graphFun]

lemma graph_fun_cut_update {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (z : Fin n) :
    (fun y : Fin n → Bool => PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
      (Function.update y z false)) =
      PEqualNP.MetaComplexity.NestedCover.graphFun (G.deleteEdges (G.incidenceSet z)) ∅ := by
  classical
  funext y
  apply Bool.eq_iff_iff.mpr
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun,
    Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty,
    false_and, exists_false, false_or]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have haz : a ≠ z := by intro h; simp [h] at ha
    have hbz : b ≠ z := by intro h; simp [h] at hb
    refine ⟨a, b, (cut_adj_iff G z a b).mpr ⟨hab, haz, hbz⟩, ?_, ?_⟩
    · simpa [Function.update_of_ne haz] using ha
    · simpa [Function.update_of_ne hbz] using hb
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hab, haz, hbz⟩ := (cut_adj_iff G z a b).mp hab
    refine ⟨a, b, hab, ?_, ?_⟩
    · simpa [Function.update_of_ne haz] using ha
    · simpa [Function.update_of_ne hbz] using hb

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.MetaComplexity.NestedCover

lemma graph_circuit_size_pos {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (he : ∃ a b, G.Adj a b)
    (hfun : circuitFun n C = graphFun G ∅) : 0 < C.size := by
  classical
  by_contra hn
  have hnil : C.gates = [] := List.length_eq_zero_iff.mp (show C.gates.length = 0 by
    change ¬ 0 < C.gates.length at hn
    omega)
  obtain ⟨a, b, hab⟩ := he
  have hon : graphFun G ∅ (fun _ => true) = true := by
    simp [graphFun, show ∃ u v, G.Adj u v from ⟨a, b, hab⟩]
  have hout : C.output < n := by
    by_contra hh
    have hval := congrFun hfun (fun _ => true)
    have hz : circuitFun n C (fun _ => true) = false := by
      simp [circuitFun, Circuit.eval, Circuit.wires, hnil,
        show n ≤ C.output by omega]
    rw [hz, hon] at hval
    contradiction
  let v : Fin n := ⟨C.output, hout⟩
  let x : Fin n → Bool := fun i => decide (i = v)
  have hval : circuitFun n C x = true := by
    simp [circuitFun, Circuit.eval, Circuit.wires, hnil,
      List.getD_eq_getElem?_getD, hout, x, v]
  have hfalse : graphFun G ∅ x = false := by
    simp [graphFun, x, SimpleGraph.irrefl]
  have hh := congrFun hfun x
  rw [hval, hfalse] at hh
  contradiction

lemma cover_lower_at_most_one_edge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hsmall : G.edgeFinset.card ≤ 1)
    (hfun : circuitFun n C = graphFun G ∅) :
    ∃ T : Finset (Fin n), IsVertexCover G T ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  by_cases he : G.edgeFinset.Nonempty
  · obtain ⟨e, he⟩ := he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab := G.mem_edgeFinset.mp he
      have hpos := graph_circuit_size_pos G C ⟨a, b, hab⟩ hfun
      refine ⟨{a}, ?_, by simpa using (show G.edgeFinset.card + 1 ≤ C.size + 1 by omega)⟩
      intro u v huv
      have heq : s(u, v) = s(a, b) :=
        Finset.card_le_one_iff.mp hsmall (G.mem_edgeFinset.mpr huv) he
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · have hempty : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    refine ⟨∅, ?_, by simp [hempty]⟩
    intro u v huv
    have hm : s(u, v) ∈ G.edgeFinset := by simpa using huv
    rw [hempty] at hm
    exact (Finset.notMem_empty _ hm).elim

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.MetaComplexity.NestedCover

lemma peeling_of_cover_lower_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hE : 2 ≤ G.edgeFinset.card)
    (lower : ∀ C : Circuit, PEqualNP.TopForm.IsAO2 n C →
      circuitFun n C = graphFun G ∅ →
      ∃ T : Finset (Fin n), IsVertexCover G T ∧
        G.edgeFinset.card + T.card ≤ C.size + 1) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit,
      PEqualNP.TopForm.IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
        circuitFun n D = (fun y : Fin n → Bool => @decide
          (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧
            y a = true ∧ y b = true) (Classical.propDecidable _)) ∧
        D.size + G.degree z ≤ C.size ∧
        ((∃ S : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
          ∀ T : Finset (Fin n), IsVertexCover G T → S.card < T.card) →
          D.size + G.degree z + 1 ≤ C.size) := by
  classical
  obtain ⟨z, hz, he⟩ := exists_positive_vertex_with_residual_edge G hE
  obtain ⟨S, hS, hmin⟩ := exists_min_cover (G.deleteEdges (G.incidenceSet z))
  have he' : ∃ a b, (G.deleteEdges (G.incidenceSet z)).Adj a b := by
    obtain ⟨e, he⟩ := he
    induction e using Sym2.inductionOn with
    | _ a b => exact ⟨a, b, (G.deleteEdges (G.incidenceSet z)).mem_edgeFinset.mp he⟩
  obtain ⟨D, hD, hfun, hsize⟩ := Upper.graph_upper
    (G.deleteEdges (G.incidenceSet z)) S he' hS
  have hedge := cut_edge_count G z
  refine ⟨z, hz, ?_⟩
  intro C hC hCF
  obtain ⟨T, hT, hbound⟩ := lower C hC hCF
  have hST := hmin T (cut_cover_restrict G z T hT)
  refine ⟨D, hD, hfun.trans (graph_fun_empty_eq _), by omega, ?_⟩
  rintro ⟨R, hR, hdrop⟩
  have hSR := hmin R hR
  have hRT := hdrop T hT
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.MetaComplexity.NestedCover

lemma cover_lower_of_peeling
    (peel : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) → PEqualNP.TopForm.NoFourCycle G → 2 ≤ G.edgeFinset.card → ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ PEqualNP.MetaComplexity.circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true) (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧ ((∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧ ∀ T : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T → S.card < T.card) → D.size + G.degree z + 1 ≤ C.size)) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∃ c : Fin n → Bool, ∀ a b, G.Adj a b → c a ≠ c b) →
      PEqualNP.TopForm.NoFourCycle G → ∀ C : Circuit,
      PEqualNP.TopForm.IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ T : Finset (Fin n), IsVertexCover G T ∧
        G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  suffices aux : ∀ m : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.card = m →
      (∃ c : Fin n → Bool, ∀ a b, G.Adj a b → c a ≠ c b) →
      PEqualNP.TopForm.NoFourCycle G → ∀ C : Circuit,
      PEqualNP.TopForm.IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ T : Finset (Fin n), IsVertexCover G T ∧
        G.edgeFinset.card + T.card ≤ C.size + 1 by
    intro n G _ hb hfour C hC hfun
    exact aux G.edgeFinset.card n G rfl hb hfour C hC hfun
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro n G _ hcard hb hfour C hC hfun
    by_cases hsmall : G.edgeFinset.card ≤ 1
    · exact cover_lower_at_most_one_edge G C hsmall hfun
    obtain ⟨z, hz, hsave⟩ := peel n G hb hfour (by omega)
    obtain ⟨D, hD, hDfun, hsize, hbonus⟩ := hsave C hC hfun
    let H := G.deleteEdges (G.incidenceSet z)
    have hedge := cut_edge_count G z
    have hless : H.edgeFinset.card < m := by
      dsimp [H]
      omega
    have hgraph : circuitFun n D = graphFun H ∅ :=
      hDfun.trans (graph_fun_empty_eq H).symm
    obtain ⟨S, hS, hbound⟩ := ih H.edgeFinset.card hless n H rfl
      (cut_bipartition G z hb) (cut_no_four_cycle G z hfour) D hD hgraph
    obtain ⟨T, hT, hmin⟩ := exists_min_cover G
    refine ⟨T, hT, ?_⟩
    by_cases hdrop : ∃ R : Finset (Fin n), IsVertexCover H R ∧
        ∀ U : Finset (Fin n), IsVertexCover G U → R.card < U.card
    · have hbns := hbonus hdrop
      have hcov := cut_cover_insert G z S hS
      have hTS := hmin (insert z S) hcov
      have hcardS := Finset.card_insert_le z S
      change H.edgeFinset.card + G.degree z = G.edgeFinset.card at hedge
      omega
    · have hTS : T.card ≤ S.card := by
        by_contra hnot
        apply hdrop
        refine ⟨S, hS, ?_⟩
        intro U hU
        have hTU := hmin U hU
        omega
      change H.edgeFinset.card + G.degree z = G.edgeFinset.card at hedge
      omega

def CoverLowerBound : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∃ c : Fin n → Bool, ∀ a b, G.Adj a b → c a ≠ c b) →
    PEqualNP.TopForm.NoFourCycle G → ∀ C : Circuit,
    PEqualNP.TopForm.IsAO2 n C → circuitFun n C = graphFun G ∅ →
    ∃ T : Finset (Fin n), IsVertexCover G T ∧
      G.edgeFinset.card + T.card ≤ C.size + 1

lemma peeling_iff_cover_lower_bound :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) → PEqualNP.TopForm.NoFourCycle G → 2 ≤ G.edgeFinset.card → ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ PEqualNP.MetaComplexity.circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true) (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧ ((∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧ ∀ T : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T → S.card < T.card) → D.size + G.degree z + 1 ≤ C.size)) ↔ CoverLowerBound := by
  constructor
  · exact cover_lower_of_peeling
  · intro lower n G _ hb hfour he
    exact peeling_of_cover_lower_bound G he (lower n G hb hfour)

lemma refutation_of_small_circuit {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (k : ℕ)
    (hb : ∃ c : Fin n → Bool, ∀ a b, G.Adj a b → c a ≠ c b)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hcover : ∀ T : Finset (Fin n), IsVertexCover G T → k ≤ T.card)
    (hsmall : C.size + 1 < G.edgeFinset.card + k) :
    ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) → PEqualNP.TopForm.NoFourCycle G → 2 ≤ G.edgeFinset.card → ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ PEqualNP.MetaComplexity.circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true) (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧ ((∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧ ∀ T : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T → S.card < T.card) → D.size + G.degree z + 1 ≤ C.size)) := by
  intro peel
  obtain ⟨T, hT, hbound⟩ := cover_lower_of_peeling peel n G hb hfour C hC hfun
  have hcard := hcover T hT
  omega

end PEqualNP.Outside.L_meta_3566.Equivalence

namespace PEqualNP.Outside.L_meta_3566.FoldPrune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

noncomputable def saving (n : ℕ) (z : Fin n) (C : Circuit) : ℕ :=
  C.size - (Pruning.liveGates n (FalseRestrict.restricted n z C)).card

lemma output_lt_of_true {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (hx : circuitFun n C x = true) : C.output < n + C.size := by
  by_contra h
  have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
    simpa [Circuit.size, AO2Upper.wires_eq] using
      AO2Upper.length_wiresFrom C.gates (List.ofFn x)
  have heq : circuitFun n C x = false := by
    unfold circuitFun Circuit.eval
    exact List.getD_eq_default _ _ (by omega)
  simp [heq] at hx

lemma restriction_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (C : Circuit) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = NestedCover.graphFun G ∅)
    (hne : (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool =>
        @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧
          y a = true ∧ y b = true) (Classical.propDecidable _)) ∧
      D.size + saving n z C ≤ C.size := by
  classical
  let E := FalseRestrict.restricted n z C
  obtain ⟨hE, hf, hs⟩ := FalseRestrict.restricted_spec n z C hAO
  have heq : circuitFun n E = (fun y : Fin n → Bool =>
      @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧
        y a = true ∧ y b = true) (Classical.propDecidable _)) := by
    rw [PEqualNP.Outside.L_meta_3566_aux.cut_semantics]
    simpa [E, hfun] using hf
  have htrue : circuitFun n E (fun _ => true) = true := by
    rw [heq]
    simp only [decide_eq_true_eq]
    obtain ⟨e, he⟩ := hne
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    exact ⟨a, b, SimpleGraph.mem_edgeFinset.mp he, trivial, trivial⟩
  obtain ⟨D, hD, hsize, hDF⟩ :=
    Pruning.prune_reachable E hE (output_lt_of_true E _ htrue)
  have hcard : (Pruning.liveGates n E).card ≤ E.size := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  refine ⟨D, hD, hDF.trans heq, ?_⟩
  change D.size + (C.size - (Pruning.liveGates n E).card) ≤ C.size
  change E.size + _ = C.size at hs
  omega

lemma cutWitness_of_saving {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (C : Circuit) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = NestedCover.graphFun G ∅)
    (hne : (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty)
    (hdeg : G.degree z ≤ saving n z C)
    (hbonus : (∃ S : Finset (Fin n),
      CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
      ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
      G.degree z + 1 ≤ saving n z C) : CutWitness G z C := by
  obtain ⟨D, hD, hf, hs⟩ := restriction_witness G z C hAO hfun hne
  refine ⟨D, hD, hf, by omega, ?_⟩
  intro hdrop
  have := hbonus hdrop
  omega

end PEqualNP.Outside.L_meta_3566.FoldPrune

namespace PEqualNP.Outside.L_meta_3566.OrRemoval
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.AO2Upper
open PEqualNP.Outside.L_meta_3566.FalseRestrict

def isOr (g : Gate) : Bool :=
  match g.op with
  | .or => true
  | _ => false

def orCount (gs : List Gate) : ℕ := (gs.filter isOr).length

def stepSaved (σ : List (Option ℕ)) (g : Gate) : ℕ :=
  if isOr g && ((σ.getD (g.inputs.getD 0 0) none).isNone ||
    (σ.getD (g.inputs.getD 1 0) none).isNone) then 1 else 0

def savedOr (m : ℕ) (σ : List (Option ℕ)) : List Gate → ℕ
  | [] => 0
  | g :: gs =>
      let r := emit m σ g
      stepSaved σ g + savedOr (m + r.1.length) (σ ++ [r.2]) gs

lemma count_append (gs hs : List Gate) : orCount (gs ++ hs) = orCount gs + orCount hs := by
  simp [orCount, List.filter_append]

lemma count_cons (g : Gate) (gs : List Gate) :
    orCount (g :: gs) = (if isOr g then 1 else 0) + orCount gs := by
  cases h : isOr g <;> simp [orCount, h, Nat.add_comm]

lemma emit_count (m : ℕ) (σ : List (Option ℕ)) (g : Gate) :
    orCount (emit m σ g).1 + stepSaved σ g = if isOr g then 1 else 0 := by
  cases hg : g.op <;>
    cases ha : σ.getD (g.inputs.getD 0 0) none <;>
    cases hb : σ.getD (g.inputs.getD 1 0) none <;>
    simp only [emit, stepSaved, isOr, hg, ha, hb, reduceGate] <;>
    rfl

lemma compile_count (gs : List Gate) (m : ℕ) (σ : List (Option ℕ)) :
    orCount (compile m σ gs).1 + savedOr m σ gs = orCount gs := by
  induction gs generalizing m σ with
  | nil => simp [compile, savedOr, orCount]
  | cons g gs ih =>
    have hs := emit_count m σ g
    have hr := ih (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2])
    simp only [compile, savedOr, count_append, count_cons]
    omega

def Retained (σ : List (Option ℕ)) (s t : List Bool) : Prop :=
  σ.length = s.length ∧ s.length = t.length ∧
    ∀ i, (σ.getD i none).isSome = true → s.getD i false = t.getD i false

lemma retained_step (m : ℕ) (σ : List (Option ℕ)) (s t : List Bool) (g : Gate)
    (h : Retained σ s t) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2) (hs : stepSaved σ g = 0) :
    Retained (σ ++ [(emit m σ g).2])
      (s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)])
      (t ++ [g.op.eval (g.inputs.map fun i => t.getD i false)]) := by
  have hev : (emit m σ g).2.isSome = true →
      g.op.eval (g.inputs.map fun i => s.getD i false) =
      g.op.eval (g.inputs.map fun i => t.getD i false) := by
    obtain ⟨a, b, hg⟩ := List.length_eq_two.mp hlen
    rcases hop with hop | hop <;>
      cases ha : σ.getD a none <;> cases hb : σ.getD b none <;>
      simp_all [emit, reduceGate, stepSaved, isOr, hg, Retained]
  refine ⟨by simp [h.1], by simp [h.2.1], ?_⟩
  intro j hj
  by_cases he : j = σ.length
  · subst j
    rw [getD_snoc_eq] at hj
    rw [h.1, getD_snoc_eq, h.2.1, getD_snoc_eq]
    exact hev hj
  · rw [getD_snoc_ne _ _ _ _ he] at hj
    have hslen : j ≠ s.length := by rw [← h.1]; exact he
    have htlen : j ≠ t.length := by rw [← h.2.1]; exact hslen
    rw [getD_snoc_ne _ _ _ _ hslen, getD_snoc_ne _ _ _ _ htlen]
    exact h.2.2 j hj

lemma compile_retained (gs : List Gate) (m : ℕ) (σ : List (Option ℕ)) (s t : List Bool)
    (h : Retained σ s t)
    (hbasis : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hs : savedOr m σ gs = 0) :
    Retained (compile m σ gs).2 (wiresFrom gs s) (wiresFrom gs t) := by
  induction gs generalizing m σ s t with
  | nil => simpa [compile, wiresFrom] using h
  | cons g gs ih =>
    have hstep : stepSaved σ g = 0 := by simp only [savedOr] at hs; omega
    have hrest : savedOr (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2]) gs = 0 := by
      simp only [savedOr] at hs
      omega
    obtain ⟨hop, hlen⟩ := hbasis g List.mem_cons_self
    exact ih _ _ _ _ (retained_step m σ s t g h hop hlen hstep)
      (fun g' hg' => hbasis g' (List.mem_cons_of_mem g hg')) hrest

lemma initial_retained_update (n : ℕ) (z : Fin n) (y : Fin n → Bool) :
    Retained (initialMap n z) (List.ofFn y) (List.ofFn (Function.update y z false)) := by
  refine ⟨by simp [initialMap], by simp, ?_⟩
  intro j hj
  by_cases hlt : j < n
  · by_cases heq : (⟨j, hlt⟩ : Fin n) = z
    · simp [initialMap, hlt, heq] at hj
    · simp [hlt, Function.update_of_ne heq]
  · simp [hlt]

lemma output_isSome_of_nonzero (n : ℕ) (z : Fin n) (C : Circuit)
    (hAO : IsAO2 n C) (x : Fin n → Bool)
    (hx : circuitFun n C (Function.update x z false) = true) :
    ((compile n (initialMap n z) C.gates).2.getD C.output none).isSome = true := by
  have hbasis : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩
  have hc := compile_correct C.gates (initialMap n z) _ _ (initial_rel n z x) hbasis
  simp only [List.length_ofFn] at hc
  have hv := hc.2.2.2 C.output
  change circuitFun n C (Function.update x z false) = _ at hv
  rw [hx] at hv
  cases h : (compile n (initialMap n z) C.gates).2.getD C.output none with
  | none =>
      rw [h] at hv
      cases hv
  | some j => rfl

lemma savedOr_pos (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C)
    (hnz : ∃ x : Fin n → Bool, circuitFun n C (Function.update x z false) = true)
    (hess : ∃ y : Fin n → Bool,
      circuitFun n C y ≠ circuitFun n C (Function.update y z false)) :
    0 < savedOr n (initialMap n z) C.gates := by
  by_contra hnot
  have hzero : savedOr n (initialMap n z) C.gates = 0 := by omega
  obtain ⟨x, hx⟩ := hnz
  obtain ⟨y, hy⟩ := hess
  have hs := output_isSome_of_nonzero n z C hAO x hx
  have hbasis : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩
  have hr := compile_retained C.gates n (initialMap n z) _ _
    (initial_retained_update n z y) hbasis hzero
  exact hy (hr.2.2 C.output hs)

lemma restriction_removes_or (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C)
    (hnz : ∃ x : Fin n → Bool, circuitFun n C (Function.update x z false) = true)
    (hess : ∃ y : Fin n → Bool,
      circuitFun n C y ≠ circuitFun n C (Function.update y z false)) :
    orCount (restricted n z C).gates + 1 ≤ orCount C.gates := by
  have hp := savedOr_pos n z C hAO hnz hess
  have hc := compile_count C.gates n (initialMap n z)
  change orCount (compile n (initialMap n z) C.gates).1 + 1 ≤ _
  omega

lemma graph_restriction_removes_or {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (z : Fin n) (C : Circuit)
    (hAO : IsAO2 n C) (hfun : circuitFun n C = NestedCover.graphFun G ∅)
    (hz : 0 < G.degree z)
    (hne : (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty) :
    orCount (restricted n z C).gates + 1 ≤ orCount C.gates := by
  classical
  apply restriction_removes_or n z C hAO
  · refine ⟨fun _ => true, ?_⟩
    rw [hfun]
    simp only [NestedCover.graphFun, Finset.notMem_empty, false_and, exists_false,
      decide_false, Bool.false_or, decide_eq_true_eq]
    obtain ⟨e, he⟩ := hne
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    have hab := (G.deleteEdges (G.incidenceSet z)).mem_edgeFinset.mp he
    obtain ⟨hab, haz, hbz⟩ := (PEqualNP.Outside.L_meta_3566.cut_adj G z a b).mp hab
    exact ⟨a, b, hab, by simp [Function.update_of_ne haz],
      by simp [Function.update_of_ne hbz]⟩
  · have hn : (G.neighborFinset z).Nonempty := Finset.card_pos.mp hz
    obtain ⟨w, hw⟩ := hn
    have hzw : G.Adj z w := (G.mem_neighborFinset z w).mp hw
    let y : Fin n → Bool := fun i => decide (i = z ∨ i = w)
    have hu : Function.update y z false = (fun i : Fin n => decide (i = w)) := by
      funext i
      by_cases hi : i = z
      · subst i
        simp [hzw.ne]
      · simp [Function.update_of_ne hi, y, hi]
    have hon : NestedCover.graphFun G ∅ y = true := by
      simp only [NestedCover.graphFun, Finset.notMem_empty, false_and, exists_false,
        decide_false, Bool.false_or, decide_eq_true_eq]
      exact ⟨z, w, hzw, by simp [y], by simp [y]⟩
    have hoff : NestedCover.graphFun G ∅ (Function.update y z false) = false := by
      rw [hu]
      simp [NestedCover.graphFun, SimpleGraph.irrefl]
    refine ⟨y, ?_⟩
    rw [hfun, hon, hoff]
    decide

end PEqualNP.Outside.L_meta_3566.OrRemoval

namespace PEqualNP.Outside.L_meta_3566.AliasRemoval
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.AO2Upper
open PEqualNP.Outside.L_meta_3566.FalseRestrict
open PEqualNP.Outside.L_meta_3566.OrRemoval

def aliasStep (m : ℕ) (σ : List (Option ℕ)) (g : Gate) : ℕ :=
  if (emit m σ g).1.length = 0 ∧ (emit m σ g).2.isSome = true then 1 else 0

def savedAlias (m : ℕ) (σ : List (Option ℕ)) : List Gate → ℕ
  | [] => 0
  | g :: gs =>
      let r := emit m σ g
      aliasStep m σ g + savedAlias (m + r.1.length) (σ ++ [r.2]) gs

def savedDead (m : ℕ) (σ : List (Option ℕ)) : List Gate → ℕ
  | [] => 0
  | g :: gs =>
      let r := emit m σ g
      (if r.2.isNone then 1 else 0) + savedDead (m + r.1.length) (σ ++ [r.2]) gs

lemma emit_partition (m : ℕ) (σ : List (Option ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (emit m σ g).1.length + (if (emit m σ g).2.isNone then 1 else 0) +
      aliasStep m σ g = 1 := by
  rcases hop with hg | hg <;>
    cases ha : σ.getD (g.inputs.getD 0 0) none <;>
    cases hb : σ.getD (g.inputs.getD 1 0) none <;>
    simp only [emit, aliasStep, hg, ha, hb, reduceGate] <;> rfl

lemma compile_partition (gs : List Gate) (m : ℕ) (σ : List (Option ℕ))
    (hbasis : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    (compile m σ gs).1.length + savedDead m σ gs + savedAlias m σ gs = gs.length := by
  induction gs generalizing m σ with
  | nil => simp [compile, savedDead, savedAlias]
  | cons g gs ih =>
    have hs := emit_partition m σ g (hbasis g List.mem_cons_self)
    have hr := ih (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2])
      (fun g' hg' => hbasis g' (List.mem_cons_of_mem g hg'))
    simp only [compile, savedDead, savedAlias, List.length_append, List.length_cons]
    omega

lemma compile_dead_count (gs : List Gate) (m : ℕ) (σ : List (Option ℕ)) :
    ((compile m σ gs).2.map Option.isNone).count true =
      (σ.map Option.isNone).count true + savedDead m σ gs := by
  induction gs generalizing m σ with
  | nil => simp [compile, savedDead]
  | cons g gs ih =>
    have hr := ih (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2])
    simp only [compile, savedDead]
    rw [hr]
    cases h : (emit m σ g).2.isNone <;>
      simp [List.count_append, h, Nat.add_assoc]

lemma savedDead_values (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C) :
    ((C.wires (List.ofFn (fun i : Fin n => decide (i ≠ z)))).map Bool.not).count true =
      (initialDead n z).count true + savedDead n (initialMap n z) C.gates := by
  have hc := compile_dead_count C.gates n (initialMap n z)
  rw [(compile_dead C.gates n (initialMap n z)).1, initial_map_dead] at hc
  change (blockedWires n z C).count true = _ at hc
  rw [blockedWires_eq n z C hAO] at hc
  exact hc

lemma initialDead_count (n : ℕ) (z : Fin n) : (initialDead n z).count true = 1 := by
  induction n with
  | zero => exact Fin.elim0 z
  | succ n ih =>
    refine Fin.cases ?_ (fun z => ?_) z
    · simp [initialDead, List.ofFn_succ, List.count_replicate]
    · have hz : (0 : Fin (n + 1)) ≠ z.succ := Ne.symm (Fin.succ_ne_zero z)
      have hc : (List.ofFn (fun i : Fin n => decide (i = z))).count true = 1 := ih z
      simpa only [initialDead, List.ofFn_succ, hz, Fin.succ_inj, decide_false,
        List.count_cons_of_ne Bool.false_ne_true] using hc

lemma count_not_true (s : List Bool) : (s.map Bool.not).count true = s.count false := by
  induction s with
  | nil => rfl
  | cons a s ih => cases a <;> simp [ih]

lemma retained_step (m : ℕ) (σ : List (Option ℕ)) (s t : List Bool) (g : Gate)
    (h : Retained σ s t) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2) (hs : aliasStep m σ g = 0) :
    Retained (σ ++ [(emit m σ g).2])
      (s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)])
      (t ++ [g.op.eval (g.inputs.map fun i => t.getD i false)]) := by
  have hev : (emit m σ g).2.isSome = true →
      g.op.eval (g.inputs.map fun i => s.getD i false) =
      g.op.eval (g.inputs.map fun i => t.getD i false) := by
    obtain ⟨a, b, hg⟩ := List.length_eq_two.mp hlen
    rcases hop with hop | hop <;>
      cases ha : σ.getD a none <;> cases hb : σ.getD b none <;>
      simp_all [emit, reduceGate, aliasStep, hg, Retained]
  refine ⟨by simp [h.1], by simp [h.2.1], ?_⟩
  intro j hj
  by_cases he : j = σ.length
  · subst j
    rw [getD_snoc_eq] at hj
    rw [h.1, getD_snoc_eq, h.2.1, getD_snoc_eq]
    exact hev hj
  · rw [getD_snoc_ne _ _ _ _ he] at hj
    have hslen : j ≠ s.length := by rw [← h.1]; exact he
    have htlen : j ≠ t.length := by rw [← h.2.1]; exact hslen
    rw [getD_snoc_ne _ _ _ _ hslen, getD_snoc_ne _ _ _ _ htlen]
    exact h.2.2 j hj

lemma compile_retained (gs : List Gate) (m : ℕ) (σ : List (Option ℕ)) (s t : List Bool)
    (h : Retained σ s t)
    (hbasis : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hs : savedAlias m σ gs = 0) :
    Retained (compile m σ gs).2 (wiresFrom gs s) (wiresFrom gs t) := by
  induction gs generalizing m σ s t with
  | nil => simpa [compile, wiresFrom] using h
  | cons g gs ih =>
    have hstep : aliasStep m σ g = 0 := by simp only [savedAlias] at hs; omega
    have hrest : savedAlias (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2]) gs = 0 := by
      simp only [savedAlias] at hs
      omega
    obtain ⟨hop, hlen⟩ := hbasis g List.mem_cons_self
    exact ih _ _ _ _ (retained_step m σ s t g h hop hlen hstep)
      (fun g' hg' => hbasis g' (List.mem_cons_of_mem g hg')) hrest

lemma savedAlias_pos (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C)
    (hnz : ∃ x : Fin n → Bool, circuitFun n C (Function.update x z false) = true)
    (hess : ∃ y : Fin n → Bool,
      circuitFun n C y ≠ circuitFun n C (Function.update y z false)) :
    0 < savedAlias n (initialMap n z) C.gates := by
  by_contra hnot
  have hzero : savedAlias n (initialMap n z) C.gates = 0 := by omega
  obtain ⟨x, hx⟩ := hnz
  obtain ⟨y, hy⟩ := hess
  have hs := output_isSome_of_nonzero n z C hAO x hx
  have hbasis : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩
  have hr := compile_retained C.gates n (initialMap n z) _ _
    (initial_retained_update n z y) hbasis hzero
  exact hy (hr.2.2 C.output hs)

lemma restriction_saves_dead_plus_one (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C)
    (hnz : ∃ x : Fin n → Bool, circuitFun n C (Function.update x z false) = true)
    (hess : ∃ y : Fin n → Bool,
      circuitFun n C y ≠ circuitFun n C (Function.update y z false)) :
    (restricted n z C).size + savedDead n (initialMap n z) C.gates + 1 ≤ C.size := by
  have hp := savedAlias_pos n z C hAO hnz hess
  have hc := compile_partition C.gates n (initialMap n z) (fun g hg => hAO.1 g hg)
  change (compile n (initialMap n z) C.gates).1.length + _ + 1 ≤ C.gates.length
  omega

lemma restriction_false_wire_bound (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C)
    (hnz : ∃ x : Fin n → Bool, circuitFun n C (Function.update x z false) = true)
    (hess : ∃ y : Fin n → Bool,
      circuitFun n C y ≠ circuitFun n C (Function.update y z false)) :
    (restricted n z C).size +
      (C.wires (List.ofFn (fun i : Fin n => decide (i ≠ z)))).count false ≤ C.size := by
  have hs := restriction_saves_dead_plus_one n z C hAO hnz hess
  have hc := savedDead_values n z C hAO
  rw [count_not_true, initialDead_count] at hc
  omega

end PEqualNP.Outside.L_meta_3566.AliasRemoval

/-!
# Helpers for L-meta-2604 (the implicant lift)

The fold inside `Circuit.wires`, run from an arbitrary wire list: it only appends, one value per
gate, so a wire that already exists keeps its value.
-/

namespace PEqualNP.Outside.L_meta_3566.HoistEval

open PEqualNP.CircuitLowerBounds

/-- One gate step of `Circuit.wires`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ s : List Bool, gs.foldl step w = w ++ s ∧ s.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨s, hs, hl⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: s, ?_, by simp [hl]⟩
    rw [List.foldl_cons, hs]
    simp [step]

theorem foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨s, hs, hl⟩ := foldl_step_prefix gs w
  simp [hs, hl]

theorem getD_append_left (w s : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ s).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_step_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨s, hs, _⟩ := foldl_step_prefix gs w
  rw [hs, getD_append_left w s i hi]

theorem getD_append_singleton_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · exact getD_append_left w [b] i h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega : (w ++ [b]).length ≤ i),
      List.getElem?_eq_none (by omega : w.length ≤ i)]

end PEqualNP.Outside.L_meta_3566.HoistEval


/-!
# Helpers for L-meta-2715 (the implicant lift iterated to a fixed point)

* `foldl_set_equiv`: replacing a gate by one with the same value on every wire list keeps the
  wires.
* `del n k u E`: delete gate `k` of `E`, redirecting every read of wire `n + k` to `u` and
  shifting every wire above it down by one. If gate `k` always equals wire `u` (`u < n + k`),
  the function is kept (`del_fun`).
-/

namespace PEqualNP.Outside.L_meta_3566.HoistBase

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3566.HoistEval
open PEqualNP.MetaComplexity.NestedCover

/-! ## Replacing a gate by an equivalent one -/

theorem foldl_set_equiv (gs : List Gate) (k : ℕ) (g g' : Gate) (hg : gs[k]? = some g)
    (heq : ∀ w : List Bool, g'.op.eval (g'.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false)) (w0 : List Bool) :
    (gs.set k g').foldl step w0 = gs.foldl step w0 := by
  induction gs generalizing k w0 with
  | nil => simp
  | cons h gs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      simp only [List.set_cons_zero, List.foldl_cons]
      congr 1
      unfold step
      rw [heq]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hg
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih k hg _

/-! ## The value of a gate -/

theorem foldl_split (gs : List Gate) (k : ℕ) (g : Gate) (hg : gs[k]? = some g) (w0 : List Bool) :
    gs.foldl step w0 = (gs.drop (k + 1)).foldl step (step ((gs.take k).foldl step w0) g) := by
  have hk : k < gs.length := by
    rcases (List.getElem?_eq_some_iff.mp hg) with ⟨hk, _⟩
    exact hk
  have hgk : gs[k] = g := (List.getElem?_eq_some_iff.mp hg).2
  conv_lhs => rw [← List.take_append_drop k gs, List.drop_eq_getElem_cons hk, hgk]
  rw [List.foldl_append, List.foldl_cons]

theorem take_fold_length (gs : List Gate) (k : ℕ) (hk : k < gs.length) (w0 : List Bool) :
    ((gs.take k).foldl step w0).length = w0.length + k := by
  rw [foldl_step_length, List.length_take]
  omega

/-- A gate `OR [u]` at position `k` has the value of wire `u`. -/
theorem wires_copy (F : Circuit) (k u : ℕ) (hk : F.gates[k]? = some ⟨GateOp.or, [u]⟩)
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

/-! ## Deleting a copy gate -/

/-- The wire renaming of a deletion of wire `m`, whose reads go to `u`. -/
def sig (m u : ℕ) (i : ℕ) : ℕ := if i < m then i else if i = m then u else i - 1

/-- A gate with its reads renamed. -/
def rd (m u : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sig m u)⟩

/-- The gate renaming of a deletion of gate `k`. -/
def sg (k : ℕ) (j : ℕ) : ℕ := if j < k then j else j - 1

/-- Delete gate `k` of `E`, redirecting its reads to `u`. -/
def del (n k u : ℕ) (E : Circuit) : Circuit :=
  ⟨(E.gates.eraseIdx k).map (rd (n + k) u), sig (n + k) u E.output⟩

theorem sig_gate (n k u j : ℕ) (hj : j ≠ k) : sig (n + k) u (n + j) = n + sg k j := by
  unfold sig sg
  split_ifs <;> omega

/-- The simulation relation between the old wire list `a` and the new one `b`. -/
def Rel (m u : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length + 1 ∧ m < a.length ∧ ∀ i, b.getD (sig m u i) false = a.getD i false

theorem getD_oob (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem rel_step (m u : ℕ) (hu : u < m) (a b : List Bool) (g : Gate) (h : Rel m u a b) :
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

theorem rel_fold (m u : ℕ) (hu : u < m) (gs : List Gate) : ∀ a b : List Bool, Rel m u a b →
    Rel m u (gs.foldl step a) ((gs.map (rd m u)).foldl step b) := by
  induction gs with
  | nil => intro a b h; simpa using h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons, List.map_cons]
    exact ih _ _ (rel_step m u hu a b g h)

theorem rd_id (m u : ℕ) (g : Gate) (h : ∀ i ∈ g.inputs, i < m) : rd m u g = g := by
  obtain ⟨op, ins⟩ := g
  simp only [rd, Gate.mk.injEq, true_and]
  conv_rhs => rw [← List.map_id ins]
  apply List.map_congr_left
  intro i hi
  have := h i hi
  simp [sig, this]

theorem del_fun (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) (hu : u < n + k)
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

theorem del_length (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) :
    (del n k u E).gates.length + 1 = E.gates.length := by
  simp only [del, List.length_map, List.length_eraseIdx, if_pos hk]
  omega

theorem del_get (n k u : ℕ) (E : Circuit) (j : ℕ) (g : Gate) (hj : j ≠ k)
    (h : E.gates[j]? = some g) : (del n k u E).gates[sg k j]? = some (rd (n + k) u g) := by
  by_cases h1 : j < k
  · simp only [del, sg, if_pos h1, List.getElem?_map, List.getElem?_eraseIdx, h]; rfl
  · have h2 : ¬ (j - 1 < k) := by omega
    have h3 : j - 1 + 1 = j := by omega
    simp only [del, sg, if_neg h1, List.getElem?_map, List.getElem?_eraseIdx, if_neg h2, h3, h]
    rfl

theorem del_get_inv (n k u : ℕ) (E : Circuit) (j : ℕ) (g : Gate)
    (h : (del n k u E).gates[j]? = some g) :
    ∃ g0, E.gates[if j < k then j else j + 1]? = some g0 ∧ g = rd (n + k) u g0 := by
  simp only [del, List.getElem?_map, List.getElem?_eraseIdx] at h
  split_ifs at h ⊢ with h1
  · cases hh : E.gates[j]? with
    | none => rw [hh] at h; simp at h
    | some g0 => rw [hh] at h; simp at h; exact ⟨g0, rfl, h.symm⟩
  · cases hh : E.gates[j + 1]? with
    | none => rw [hh] at h; simp at h
    | some g0 => rw [hh] at h; simp at h; exact ⟨g0, rfl, h.symm⟩

theorem del_mono (n k u : ℕ) (E : Circuit) (hE : Monotone2 E) : Monotone2 (del n k u E) := by
  intro g hg
  simp only [del, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have := hE g0 (List.mem_of_mem_eraseIdx hg0)
  simpa [rd] using this

theorem gateAt_some (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (gateAt C j) := by
  rw [List.getElem?_eq_getElem hj]
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem readsBack_get (n : ℕ) (C : Circuit) (h : ReadsBack n C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) : ∀ i ∈ g.inputs, i < n + j := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have := gateAt_some C j hj
  rw [hg] at this
  cases this
  exact h j hj

theorem readsBack_of_get (n : ℕ) (C : Circuit)
    (h : ∀ j (g : Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) : ReadsBack n C := by
  intro j hj
  exact h j _ (gateAt_some C j hj)

theorem del_readsBack (n k u : ℕ) (E : Circuit) (hE : ReadsBack n E) (hu : u < n + k) :
    ReadsBack n (del n k u E) := by
  apply readsBack_of_get
  intro j g hg
  obtain ⟨g0, hg0, rfl⟩ := del_get_inv n k u E j g hg
  have hr := readsBack_get n E hE _ g0 hg0
  intro i hi
  simp only [rd, List.mem_map] at hi
  obtain ⟨i0, hi0, rfl⟩ := hi
  have := hr i0 hi0
  unfold sig
  split_ifs at this ⊢ <;> omega

theorem readsBack_take (n : ℕ) (C : Circuit) (h : ReadsBack n C) (k : ℕ) :
    ∀ g ∈ C.gates.take k, ∀ i ∈ g.inputs, i < n + k := by
  intro g hg i hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  rw [List.getElem_take] at hi
  have hjl : j < k := by simp at hj; omega
  have hj' : j < C.gates.length := by simp at hj; omega
  have := readsBack_get n C h j _ (List.getElem?_eq_getElem hj') i hi
  omega

end PEqualNP.Outside.L_meta_3566.HoistBase

namespace PEqualNP.Outside.L_meta_3566.HoistNegative
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.HoistEval PEqualNP.Outside.L_meta_3566.HoistBase

lemma foldl_set_state (gs : List Gate) (k : ℕ) (g g' : Gate) (hg : gs[k]? = some g)
    (w0 : List Bool)
    (heq : g'.op.eval (g'.inputs.map fun i => ((gs.take k).foldl step w0).getD i false) =
      g.op.eval (g.inputs.map fun i => ((gs.take k).foldl step w0).getD i false)) :
    (gs.set k g').foldl step w0 = gs.foldl step w0 := by
  induction gs generalizing k w0 with
  | nil => simp at hg
  | cons h gs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst h
      simp only [List.take_zero, List.foldl_nil] at heq
      simp only [List.set_cons_zero, List.foldl_cons]
      congr 1
      unfold step
      rw [heq]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hg
      simp only [List.take_succ_cons, List.foldl_cons] at heq
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih k hg _ heq

lemma prefix_wire (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (w0 : List Bool) (i : ℕ) (hi : i < w0.length + k) :
    (gs.foldl step w0).getD i false = ((gs.take k).foldl step w0).getD i false := by
  have hl := take_fold_length gs k hk w0
  have heq : gs.foldl step w0 = (gs.drop k).foldl step ((gs.take k).foldl step w0) := by
    rw [← List.foldl_append, List.take_append_drop]
  rw [heq]
  exact foldl_step_getD _ _ _ (by omega)

lemma copy_or_wires_eq_of_false (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hkg : D.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ht : t < n + k) (x : Fin n → Bool)
    (hfalse : (D.wires (List.ofFn x)).getD t false = false) :
    (D.gates.set k ⟨GateOp.or, [u]⟩).foldl step (List.ofFn x) =
      D.gates.foldl step (List.ofFn x) := by
  have hk := (List.getElem?_eq_some_iff.mp hkg).1
  have htP : ((D.gates.take k).foldl step (List.ofFn x)).getD t false = false := by
    rw [← prefix_wire D.gates k hk (List.ofFn x) t (by simpa using ht)]
    exact hfalse
  apply foldl_set_state D.gates k _ _ hkg (List.ofFn x)
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, htP,
    id_eq, Bool.false_or, Bool.or_false]

def lifted (n : ℕ) (D : Circuit) (k u t : ℕ) : Circuit :=
  ⟨D.gates.set k ⟨GateOp.or, [u]⟩ ++ [⟨GateOp.or, [D.output,t]⟩], n+D.gates.length⟩

lemma lifted_get_ne (n : ℕ) (D : Circuit) (k u t j : ℕ)
    (hjk : j ≠ k) (hj : j < D.gates.length) :
    (lifted n D k u t).gates[j]? = D.gates[j]? := by
  simp only [lifted]
  rw [List.getElem?_append_left (by simpa using hj), List.getElem?_set_ne (Ne.symm hjk)]

lemma lifted_get_copy (n : ℕ) (D : Circuit) (k u t : ℕ) (hk : k < D.gates.length) :
    (lifted n D k u t).gates[k]? = some ⟨GateOp.or,[u]⟩ := by
  simp only [lifted]
  rw [List.getElem?_append_left (by simpa using hk)]
  simp [List.getElem?_set, hk]

lemma lifted_get_last (n : ℕ) (D : Circuit) (k u t : ℕ) :
    (lifted n D k u t).gates[D.gates.length]? = some ⟨GateOp.or,[D.output,t]⟩ := by
  simp only [lifted]
  rw [List.getElem?_append_right (by simp)]
  simp

lemma lifted_readsBack (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hR : ReadsBack n D) (hk : k < D.gates.length)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length) :
    ReadsBack n (lifted n D k u t) := by
  apply readsBack_of_get
  intro j g hg i hi
  rcases Nat.lt_trichotomy j D.gates.length with hj | hj | hj
  · by_cases hjk : j = k
    · subst j
      rw [lifted_get_copy n D k u t hk] at hg
      cases hg
      simp at hi
      omega
    · rw [lifted_get_ne n D k u t j hjk hj] at hg
      exact readsBack_get n D hR j g hg i hi
  · subst j
    rw [lifted_get_last] at hg
    cases hg
    simp at hi
    omega
  · have hlen : (lifted n D k u t).gates.length = D.gates.length+1 := by simp [lifted]
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg

lemma lifted_negative_wires (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩) (ht : t < n+k)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) :
    (lifted n D k u t).wires (List.ofFn x) = D.wires (List.ofFn x) ++ [false] := by
  have hc := copy_or_wires_eq_of_false n D k u t hkg ht x htfalse
  change (D.gates.set k _ ++ [_]).foldl step (List.ofFn x) = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hc]
  change step (D.wires (List.ofFn x)) _ = _
  change (D.wires (List.ofFn x)).getD D.output false = false at hofalse
  simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    htfalse, hofalse, id_eq, Bool.false_or]

end PEqualNP.Outside.L_meta_3566.HoistNegative

namespace PEqualNP.Outside.L_meta_3566.HoistBase
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3566.HoistEval

theorem del_wire (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) (hu : u < n + k)
    (hpre : ∀ g ∈ E.gates.take k, ∀ i ∈ g.inputs, i < n + k)
    (hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD u false) :
    ∀ (x : Fin n → Bool) (i : ℕ),
      ((del n k u E).wires (List.ofFn x)).getD (sig (n+k) u i) false =
        (E.wires (List.ofFn x)).getD i false := by
  intro x i
  have hc := hcopy x
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
  exact hrel.2.2 i


end PEqualNP.Outside.L_meta_3566.HoistBase

namespace PEqualNP.Outside.L_meta_3566.HoistNegative
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.HoistEval PEqualNP.Outside.L_meta_3566.HoistBase

def hoisted (n : ℕ) (D : Circuit) (k u t : ℕ) : Circuit :=
  del n k u (lifted n D k u t)

lemma hoisted_negative_wire (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) (i : ℕ) (hi : i < n+D.gates.length) :
    ((hoisted n D k u t).wires (List.ofFn x)).getD (sig (n+k) u i) false =
      (D.wires (List.ofFn x)).getD i false := by
  have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
  let E := lifted n D k u t
  have hER := lifted_readsBack n D k u t hR hk hu ht ho
  have hEk := lifted_get_copy n D k u t hk
  have hkE : k < E.gates.length := by simp [E, lifted]; omega
  have hcopy : ∀ y : Fin n → Bool,
      (E.wires (List.ofFn y)).getD (n+k) false = (E.wires (List.ofFn y)).getD u false := by
    intro y
    simpa using wires_copy E k u hEk (List.ofFn y) (by simpa using hu)
  have hw := del_wire n k u E hkE hu (readsBack_take n E hER k) hcopy x i
  have hl : (D.wires (List.ofFn x)).length = n+D.gates.length := by
    rw [wires_eq, foldl_step_length, List.length_ofFn]
  change ((hoisted n D k u t).wires (List.ofFn x)).getD _ false = _ at hw
  rw [lifted_negative_wires n D k u t hkg ht x htfalse hofalse,
    List.getD_append _ _ _ _ (by omega)] at hw
  exact hw

lemma hoisted_negative_gate (n : ℕ) (D : Circuit) (k u t j : ℕ)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (hj : j < D.gates.length) (hjk : j ≠ k)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) :
    ((hoisted n D k u t).wires (List.ofFn x)).getD (n+sg k j) false =
      (D.wires (List.ofFn x)).getD (n+j) false := by
  have h := hoisted_negative_wire n D k u t hR hkg hu ht ho x htfalse hofalse
    (n+j) (by omega)
  rw [sig_gate n k u j hjk] at h
  exact h

lemma hoisted_get (n : ℕ) (D : Circuit) (k u t j : ℕ) (g : Gate)
    (hjk : j ≠ k) (hj : D.gates[j]? = some g) :
    (hoisted n D k u t).gates[sg k j]? = some (rd (n+k) u g) := by
  have hjlt : j < D.gates.length := (List.getElem?_eq_some_iff.mp hj).1
  apply del_get n k u (lifted n D k u t) j g hjk
  rw [lifted_get_ne n D k u t j hjk hjlt, hj]

lemma clean_hoist_negative_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (k u t j : ℕ)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (hfun : circuitFun n D = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true)
    (hj : j < D.gates.length) (hjk : j ≠ k)
    (x : Fin n → Bool) (hx : graphFun G ∅ x = false) :
    ((hoisted n D k u t).wires (List.ofFn x)).getD (n+sg k j) false =
      (D.wires (List.ofFn x)).getD (n+j) false := by
  have htfalse : (D.wires (List.ofFn x)).getD t false = false := by
    cases h : (D.wires (List.ofFn x)).getD t false
    · rfl
    · have hc := hclean x h
      rw [hx] at hc
      cases hc
  exact hoisted_negative_gate n D k u t j hR hkg hu ht ho hj hjk x htfalse (by rw [hfun, hx])

end PEqualNP.Outside.L_meta_3566.HoistNegative

namespace PEqualNP.Outside.L_meta_3566.HoistNegative
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.HoistEval PEqualNP.Outside.L_meta_3566.HoistBase

def ordered (D : Circuit) (k u t : ℕ) : Circuit :=
  ⟨D.gates.set k ⟨GateOp.or,[u,t]⟩, D.output⟩

lemma ordered_wires_eq (D : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : D.gates[k]? = some g)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false)) (x : List Bool) :
    (ordered D k u t).wires x = D.wires x :=
  foldl_set_equiv D.gates k g ⟨GateOp.or,[u,t]⟩ hkg hequ x

lemma ordered_fun_eq (n : ℕ) (D : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : D.gates[k]? = some g)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false)) :
    circuitFun n (ordered D k u t) = circuitFun n D := by
  funext x
  change ((ordered D k u t).wires (List.ofFn x)).getD D.output false = _
  rw [ordered_wires_eq D k u t g hkg hequ]
  rfl

lemma hoisted_ordered_eq (n : ℕ) (D : Circuit) (k u t : ℕ) :
    hoisted n (ordered D k u t) k u t = hoisted n D k u t := by
  simp [hoisted, lifted, ordered, List.set_set]

lemma ordered_readsBack (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hR : ReadsBack n D) (hu : u < n+k) (ht : t < n+k) :
    ReadsBack n (ordered D k u t) := by
  apply readsBack_of_get
  intro j g hg i hi
  have hj : j < D.gates.length := by
    have h := (List.getElem?_eq_some_iff.mp hg).1
    simpa [ordered] using h
  by_cases hjk : j = k
  · subst j
    have hget : (ordered D k u t).gates[k]? = some ⟨GateOp.or,[u,t]⟩ := by
      simp [ordered, hj]
    rw [hget] at hg
    cases hg
    simp at hi
    omega
  · have hget : (ordered D k u t).gates[j]? = D.gates[j]? := by
      simp only [ordered, List.getElem?_set_ne (Ne.symm hjk)]
    rw [hget] at hg
    exact readsBack_get n D hR j g hg i hi

lemma hoisted_negative_gate_equiv (n : ℕ) (D : Circuit) (k u t j : ℕ) (g : Gate)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some g)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (hj : j < D.gates.length) (hjk : j ≠ k)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) :
    ((hoisted n D k u t).wires (List.ofFn x)).getD (n+sg k j) false =
      (D.wires (List.ofFn x)).getD (n+j) false := by
  have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
  have hkg' : (ordered D k u t).gates[k]? = some ⟨GateOp.or,[u,t]⟩ := by
    simp [ordered, hk]
  have ho' : (ordered D k u t).output < n+(ordered D k u t).gates.length := by
    simpa [ordered] using ho
  have hj' : j < (ordered D k u t).gates.length := by simpa [ordered] using hj
  have htfalse' : ((ordered D k u t).wires (List.ofFn x)).getD t false = false := by
    rw [ordered_wires_eq D k u t g hkg hequ]
    exact htfalse
  have hofalse' : circuitFun n (ordered D k u t) x = false := by
    rw [ordered_fun_eq n D k u t g hkg hequ]
    exact hofalse
  have h := hoisted_negative_gate n (ordered D k u t) k u t j
    (ordered_readsBack n D k u t hR hu ht) hkg' hu ht ho' hj' hjk x htfalse' hofalse'
  rw [hoisted_ordered_eq, ordered_wires_eq D k u t g hkg hequ] at h
  exact h

end PEqualNP.Outside.L_meta_3566.HoistNegative

namespace PEqualNP.Outside.L_meta_3566.AndIndexTransport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

noncomputable def andIndices (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j => (gateAt C j).op = .and

noncomputable def badAnds {n : ℕ} (C : Circuit) (P : (Fin n → Bool) → Prop) : Finset ℕ := by
  classical
  exact (andIndices C).filter fun j => ∃ x, P x ∧ gateVal n C j x = true

lemma mem_andIndices {C : Circuit} {j : ℕ} :
    j ∈ andIndices C ↔ j < C.gates.length ∧ (gateAt C j).op = .and := by
  classical
  simp [andIndices]

lemma mem_badAnds {n : ℕ} {C : Circuit} {P : (Fin n → Bool) → Prop} {j : ℕ} :
    j ∈ badAnds C P ↔ j ∈ andIndices C ∧ ∃ x, P x ∧ gateVal n C j x = true := by
  classical
  simp [badAnds]

lemma badAnds_image {n : ℕ} (C D : Circuit) (f : ℕ → ℕ)
    (P : (Fin n → Bool) → Prop)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hval : ∀ j ∈ andIndices C, ∀ x, P x → gateVal n D (f j) x = gateVal n C j x) :
    badAnds D P = (badAnds C P).image f := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨hkA, x, hx, hv⟩ := mem_badAnds.mp hk
    obtain ⟨j, hj, rfl⟩ := hsurj k hkA
    exact Finset.mem_image.mpr ⟨j, mem_badAnds.mpr ⟨hj, x, hx, (hval j hj x hx) ▸ hv⟩, rfl⟩
  · intro hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hjA, x, hx, hv⟩ := mem_badAnds.mp hj
    exact mem_badAnds.mpr ⟨hforward j hjA, x, hx, (hval j hjA x hx).symm ▸ hv⟩

lemma badAnds_card {n : ℕ} (C D : Circuit) (f : ℕ → ℕ)
    (P : (Fin n → Bool) → Prop)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hinj : Set.InjOn f (andIndices C : Set ℕ))
    (hval : ∀ j ∈ andIndices C, ∀ x, P x → gateVal n D (f j) x = gateVal n C j x) :
    (badAnds D P).card = (badAnds C P).card := by
  classical
  rw [badAnds_image C D f P hforward hsurj hval]
  apply Finset.card_image_of_injOn
  intro i hi j hj hij
  exact hinj (mem_badAnds.mp hi).1 (mem_badAnds.mp hj).1 hij

lemma junk_eq_badAnds {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    junk G C = badAnds C (fun x => graphFun G ∅ x = false) := by
  classical
  ext j
  have hjunk : j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
    unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
    rw [Finset.mem_filter, Finset.mem_range]
  rw [hjunk, mem_badAnds, mem_andIndices]
  change (j < C.gates.length ∧ (gateAt C j).op = .and ∧ j < C.gates.length ∧
    ∃ x, gateVal n C j x = true ∧ graphFun G ∅ x = false) ↔ _
  constructor
  · rintro ⟨hj, hop, _, x, hv, hx⟩
    exact ⟨⟨hj, hop⟩, x, hx, hv⟩
  · rintro ⟨⟨hj, hop⟩, x, hx, hv⟩
    exact ⟨hj, hop, hj, x, hv, hx⟩

lemma junk_image {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hval : ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n D (f j) x = gateVal n C j x) :
    junk G D = (junk G C).image f := by
  rw [junk_eq_badAnds, junk_eq_badAnds]
  exact badAnds_image C D f _ hforward hsurj hval

lemma junk_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hinj : Set.InjOn f (andIndices C : Set ℕ))
    (hval : ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n D (f j) x = gateVal n C j x) :
    (junk G D).card = (junk G C).card := by
  rw [junk_eq_badAnds, junk_eq_badAnds]
  exact badAnds_card C D f _ hforward hsurj hinj hval

noncomputable def pairLeakyAnds {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Finset ℕ := by
  classical
  exact (andIndices C).filter fun j =>
    ∃ a b, ¬ G.Adj a b ∧ gateVal n C j (pairInput a b) = true

lemma mem_pairLeakyAnds {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {j : ℕ} :
    j ∈ pairLeakyAnds G C ↔ j ∈ andIndices C ∧
      ∃ a b, ¬ G.Adj a b ∧ gateVal n C j (pairInput a b) = true := by
  classical
  simp [pairLeakyAnds]

lemma pairLeakyAnds_eq_badAnds {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :
    pairLeakyAnds G C = badAnds C (fun x => ∃ a b, ¬ G.Adj a b ∧ x = pairInput a b) := by
  classical
  ext j
  rw [mem_pairLeakyAnds, mem_badAnds]
  constructor
  · rintro ⟨hj, a, b, hab, hv⟩
    exact ⟨hj, pairInput a b, ⟨a, b, hab, rfl⟩, hv⟩
  · rintro ⟨hj, x, ⟨a, b, hab, rfl⟩, hv⟩
    exact ⟨hj, a, b, hab, hv⟩

lemma pairLeakyAnds_image {n : ℕ} (G : SimpleGraph (Fin n))
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hval : ∀ j ∈ andIndices C, ∀ a b, ¬ G.Adj a b →
      gateVal n D (f j) (pairInput a b) = gateVal n C j (pairInput a b)) :
    pairLeakyAnds G D = (pairLeakyAnds G C).image f := by
  rw [pairLeakyAnds_eq_badAnds, pairLeakyAnds_eq_badAnds]
  apply badAnds_image C D f _ hforward hsurj
  rintro j hj x ⟨a, b, hab, rfl⟩
  exact hval j hj a b hab

lemma pairLeakyAnds_card {n : ℕ} (G : SimpleGraph (Fin n))
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hinj : Set.InjOn f (andIndices C : Set ℕ))
    (hval : ∀ j ∈ andIndices C, ∀ a b, ¬ G.Adj a b →
      gateVal n D (f j) (pairInput a b) = gateVal n C j (pairInput a b)) :
    (pairLeakyAnds G D).card = (pairLeakyAnds G C).card := by
  rw [pairLeakyAnds_eq_badAnds, pairLeakyAnds_eq_badAnds]
  apply badAnds_card C D f _ hforward hsurj hinj
  rintro j hj x ⟨a, b, hab, rfl⟩
  exact hval j hj a b hab

end PEqualNP.Outside.L_meta_3566.AndIndexTransport

namespace PEqualNP.Outside.L_meta_3566.HoistAndIndices

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.HoistBase PEqualNP.Outside.L_meta_3566.HoistNegative
open PEqualNP.Outside.L_meta_3566.AndIndexTransport (andIndices)

lemma mem_andIndices (C : Circuit) (j : ℕ) :
    j ∈ andIndices C ↔ ∃ g, C.gates[j]? = some g ∧ g.op = .and := by
  classical
  simp only [AndIndexTransport.andIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hop⟩
    refine ⟨gateAt C j, ?_, hop⟩
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  · rintro ⟨g, hg, hop⟩
    refine ⟨(List.getElem?_eq_some_iff.mp hg).1, ?_⟩
    simpa [gateAt, List.getD_eq_getElem?_getD, hg] using hop

lemma indexShift_injOn (k : ℕ) (S : Finset ℕ) (hS : k ∉ S) :
    Set.InjOn (sg k) (S : Set ℕ) := by
  intro a ha b hb hab
  have ha' : a ≠ k := fun h => hS (h ▸ ha)
  have hb' : b ≠ k := fun h => hS (h ▸ hb)
  unfold sg at hab
  split_ifs at hab <;> omega

lemma changed_not_and (C : Circuit) (k : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or) : k ∉ andIndices C := by
  intro hk
  obtain ⟨g', hg', hand⟩ := (mem_andIndices C k).mp hk
  rw [hkg] at hg'
  cases hg'
  rw [hor] at hand
  cases hand

lemma hoisted_and_injOn (C : Circuit) (k : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or) :
    Set.InjOn (sg k) (andIndices C : Set ℕ) :=
  indexShift_injOn k (andIndices C) (changed_not_and C k g hkg hor)

lemma hoisted_and_forward (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or)
    (j : ℕ) (hj : j ∈ andIndices C) : sg k j ∈ andIndices (hoisted n C k u t) := by
  have hjk : j ≠ k := by
    intro heq
    exact changed_not_and C k g hkg hor (heq ▸ hj)
  obtain ⟨g0, hg0, hand⟩ := (mem_andIndices C j).mp hj
  apply (mem_andIndices _ _).mpr
  exact ⟨rd (n + k) u g0, HoistNegative.hoisted_get n C k u t j g0 hjk hg0, hand⟩

lemma hoisted_and_inverse (n : ℕ) (C : Circuit) (k u t j : ℕ)
    (hj : j ∈ andIndices (hoisted n C k u t)) :
    ∃ i ∈ andIndices C, sg k i = j := by
  obtain ⟨g, hg, hand⟩ := (mem_andIndices _ j).mp hj
  obtain ⟨g0, hg0, hrd⟩ := del_get_inv n k u (lifted n C k u t) j g hg
  let i := if j < k then j else j + 1
  have hik : i ≠ k := by dsimp [i]; split_ifs <;> omega
  have hi : i < (lifted n C k u t).gates.length :=
    (List.getElem?_eq_some_iff.mp hg0).1
  have hlen : (lifted n C k u t).gates.length = C.gates.length + 1 := by
    simp [lifted]
  have hiold : i < C.gates.length := by
    by_contra hn
    have heq : i = C.gates.length := by omega
    have hlast := lifted_get_last n C k u t
    change (lifted n C k u t).gates[i]? = some g0 at hg0
    rw [heq, hlast] at hg0
    cases hg0
    simp [hrd, rd] at hand
  have hOld : C.gates[i]? = some g0 := by
    rw [← lifted_get_ne n C k u t i hik hiold]
    exact hg0
  refine ⟨i, (mem_andIndices C i).mpr ⟨g0, hOld, ?_⟩, ?_⟩
  · simpa [hrd, rd] using hand
  · dsimp [i, sg]
    split_ifs <;> omega

lemma hoisted_and_image (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or) :
    andIndices (hoisted n C k u t) = (andIndices C).image (sg k) := by
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi, heq⟩ := hoisted_and_inverse n C k u t j hj
    exact Finset.mem_image.mpr ⟨i, hi, heq⟩
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact hoisted_and_forward n C k u t g hkg hor i hi

lemma hoisted_and_bijection (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or)
    (j : ℕ) (hj : j ∈ andIndices (hoisted n C k u t)) :
    ∃! i, i ∈ andIndices C ∧ sg k i = j := by
  obtain ⟨i, hi, heq⟩ := hoisted_and_inverse n C k u t j hj
  refine ⟨i, ⟨hi, heq⟩, ?_⟩
  intro i' hi'
  exact indexShift_injOn k (andIndices C) (changed_not_and C k g hkg hor)
    hi'.1 hi (hi'.2.trans heq.symm)

lemma hoisted_and_card (n : ℕ) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = .or) :
    (andIndices (hoisted n C k u t)).card = (andIndices C).card := by
  rw [hoisted_and_image n C k u t g hkg hor]
  exact Finset.card_image_of_injOn
    (indexShift_injOn k (andIndices C) (changed_not_and C k g hkg hor))

end PEqualNP.Outside.L_meta_3566.HoistAndIndices

namespace PEqualNP.Outside.L_meta_3566.HoistDirty

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.HoistBase (sg)
open PEqualNP.Outside.L_meta_3566.HoistNegative (hoisted)
open PEqualNP.Outside.L_meta_3566.AndIndexTransport (andIndices pairLeakyAnds)

lemma negative_and_profile {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n (hoisted n C k u t) (sg k j) x = gateVal n C j x := by
  have hreads := HoistBase.readsBack_get n C hR k ⟨GateOp.or, [u,t]⟩ hkg
  have hu : u < n + k := hreads u (by simp)
  have ht : t < n + k := hreads t (by simp)
  intro j hj x hx
  have hjlt := (AndIndexTransport.mem_andIndices.mp hj).1
  have hjk : j ≠ k := by
    intro h
    exact HoistAndIndices.changed_not_and C k _ hkg rfl (h ▸ hj)
  exact HoistNegative.clean_hoist_negative_gate G C k u t j hR hkg hu ht ho
    hfun hclean hjlt hjk x hx

lemma junk_image {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    junk G (hoisted n C k u t) = (junk G C).image (sg k) := by
  exact AndIndexTransport.junk_image G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t _ hkg rfl)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (negative_and_profile G C k u t hR hkg ho hfun hclean)

lemma junk_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    (junk G (hoisted n C k u t)).card = (junk G C).card := by
  exact AndIndexTransport.junk_card G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t _ hkg rfl)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (HoistAndIndices.hoisted_and_injOn C k _ hkg rfl)
    (negative_and_profile G C k u t hR hkg ho hfun hclean)

lemma graphFun_pair_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (hab : ¬ G.Adj a b) : graphFun G ∅ (pairInput a b) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hh : ∃ p q, G.Adj p q ∧ pairInput a b p = true ∧ pairInput a b q = true := by
    simpa [graphFun] using h
  obtain ⟨p, q, hpq, hp, hq⟩ := hh
  have hp' : p = a ∨ p = b := by simpa [pairInput] using hp
  have hq' : q = a ∨ q = b := by simpa [pairInput] using hq
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
  · exact G.loopless.irrefl _ hpq
  · exact hab hpq
  · exact hab hpq.symm
  · exact G.loopless.irrefl _ hpq

lemma pair_negative_and_profile {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    ∀ j ∈ andIndices C, ∀ a b, ¬ G.Adj a b →
      gateVal n (hoisted n C k u t) (sg k j) (pairInput a b) =
        gateVal n C j (pairInput a b) := by
  intro j hj a b hab
  exact negative_and_profile G C k u t hR hkg ho hfun hclean j hj
    (pairInput a b) (graphFun_pair_false G a b hab)

lemma pairLeakyAnds_image {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    pairLeakyAnds G (hoisted n C k u t) = (pairLeakyAnds G C).image (sg k) := by
  exact AndIndexTransport.pairLeakyAnds_image G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t _ hkg rfl)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (pair_negative_and_profile G C k u t hR hkg ho hfun hclean)

lemma pairLeakyAnds_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some ⟨GateOp.or, [u,t]⟩)
    (ho : C.output < n + C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    (pairLeakyAnds G (hoisted n C k u t)).card = (pairLeakyAnds G C).card := by
  exact AndIndexTransport.pairLeakyAnds_card G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t _ hkg rfl)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (HoistAndIndices.hoisted_and_injOn C k _ hkg rfl)
    (pair_negative_and_profile G C k u t hR hkg ho hfun hclean)

end PEqualNP.Outside.L_meta_3566.HoistDirty

namespace PEqualNP.Outside.L_meta_3566.HoistDirty
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.HoistBase (sg)
open PEqualNP.Outside.L_meta_3566.HoistNegative (hoisted)
open PEqualNP.Outside.L_meta_3566.AndIndexTransport (andIndices)

lemma negative_and_profile_equiv {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g) (hor : g.op = GateOp.or)
    (hu : u ∈ g.inputs) (ht : t ∈ g.inputs)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (ho : C.output < n+C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n (hoisted n C k u t) (sg k j) x = gateVal n C j x := by
  have hreads := HoistBase.readsBack_get n C hR k g hkg
  intro j hj x hx
  have hjlt := (AndIndexTransport.mem_andIndices.mp hj).1
  have hjk : j ≠ k := by
    intro h
    exact HoistAndIndices.changed_not_and C k g hkg hor (h ▸ hj)
  have htfalse : (C.wires (List.ofFn x)).getD t false = false := by
    cases h : (C.wires (List.ofFn x)).getD t false
    · rfl
    · have hc := hclean x h
      rw [hx] at hc
      cases hc
  exact HoistNegative.hoisted_negative_gate_equiv n C k u t j g hR hkg hequ
    (hreads u hu) (hreads t ht) ho hjlt hjk x htfalse (by rw [hfun,hx])

lemma junk_card_equiv {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g) (hor : g.op = GateOp.or)
    (hu : u ∈ g.inputs) (ht : t ∈ g.inputs)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (ho : C.output < n+C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    (junk G (hoisted n C k u t)).card = (junk G C).card := by
  exact AndIndexTransport.junk_card G C (hoisted n C k u t) (sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t g hkg hor)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (HoistAndIndices.hoisted_and_injOn C k g hkg hor)
    (negative_and_profile_equiv G C k u t g hR hkg hor hu ht hequ ho hfun hclean)

end PEqualNP.Outside.L_meta_3566.HoistDirty


namespace PEqualNP.Outside.L_meta_3566.NegativeMass
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_3566.AndIndexTransport

noncomputable def falseInputs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter fun x => graphFun G ∅ x = false

noncomputable def mass {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : ℕ :=
  ∑ x ∈ falseInputs G, (badAnds C (fun y => y = x)).card

lemma mem_falseInputs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : x ∈ falseInputs G ↔ graphFun G ∅ x = false := by
  classical
  simp [falseInputs]

lemma mass_congr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j ∈ andIndices C, f j ∈ andIndices D)
    (hsurj : ∀ k ∈ andIndices D, ∃ j ∈ andIndices C, f j = k)
    (hinj : Set.InjOn f (andIndices C : Set ℕ))
    (hval : ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n D (f j) x = gateVal n C j x) : mass G D = mass G C := by
  classical
  apply Finset.sum_congr rfl
  intro x hx
  apply badAnds_card C D f (fun y => y = x) hforward hsurj hinj
  intro j hj y hy
  subst y
  exact hval j hj x ((mem_falseInputs G x).mp hx)

lemma mass_strict_of_negative_decrease {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit)
    (hinds : andIndices D = andIndices C)
    (hval : ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n D j x = true → gateVal n C j x = true)
    (hstrict : ∃ j ∈ andIndices C, ∃ x : Fin n → Bool,
      graphFun G ∅ x = false ∧ gateVal n C j x = true ∧ gateVal n D j x = false) :
    mass G D < mass G C := by
  classical
  have hsub (x : Fin n → Bool) (hx : graphFun G ∅ x = false) :
      badAnds D (fun y => y = x) ⊆ badAnds C (fun y => y = x) := by
    intro j hj
    obtain ⟨hjD, y, hy, hv⟩ := mem_badAnds.mp hj
    subst y
    have hjC : j ∈ andIndices C := hinds ▸ hjD
    exact mem_badAnds.mpr ⟨hjC, x, rfl, hval j hjC x hx hv⟩
  unfold mass
  apply Finset.sum_lt_sum
  · intro x hx
    exact Finset.card_le_card (hsub x ((mem_falseInputs G x).mp hx))
  · obtain ⟨j, hj, x, hx, hc, hd⟩ := hstrict
    refine ⟨x, (mem_falseInputs G x).mpr hx, ?_⟩
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub x hx, ?_⟩
    intro heq
    have hjC : j ∈ badAnds C (fun y => y = x) := mem_badAnds.mpr ⟨hj, x, rfl, hc⟩
    have hjD : j ∈ badAnds D (fun y => y = x) := heq.symm ▸ hjC
    obtain ⟨_, y, hy, hv⟩ := mem_badAnds.mp hjD
    subst y
    rw [hd] at hv
    cases hv

lemma exists_minimum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Circuit → Prop) (hP : ∃ C, P C) :
    ∃ C, P C ∧ ∀ D, P D → mass G C ≤ mass G D := by
  classical
  have hex : ∃ m, ∃ C, P C ∧ mass G C = m := by
    obtain ⟨C, hC⟩ := hP
    exact ⟨mass G C, C, hC, rfl⟩
  obtain ⟨C, hC, hm⟩ := Nat.find_spec hex
  refine ⟨C, hC, ?_⟩
  intro D hD
  rw [hm]
  exact Nat.find_min' hex ⟨D, hD, rfl⟩

lemma no_strict_rewrite {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Circuit → Prop) (C D : Circuit)
    (hmin : ∀ E, P E → mass G C ≤ mass G E) (hD : P D)
    (hinds : andIndices D = andIndices C)
    (hval : ∀ j ∈ andIndices C, ∀ x, graphFun G ∅ x = false →
      gateVal n D j x = true → gateVal n C j x = true) :
    ¬ ∃ j ∈ andIndices C, ∃ x : Fin n → Bool,
      graphFun G ∅ x = false ∧ gateVal n C j x = true ∧ gateVal n D j x = false := by
  intro hstrict
  have hlt := mass_strict_of_negative_decrease G C D hinds hval hstrict
  have hle := hmin D hD
  omega

lemma hoist_mass {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g) (hor : g.op = GateOp.or)
    (hu : u ∈ g.inputs) (ht : t ∈ g.inputs)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (ho : C.output < n+C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    mass G (HoistNegative.hoisted n C k u t) = mass G C := by
  exact mass_congr G C (HoistNegative.hoisted n C k u t) (HoistBase.sg k)
    (HoistAndIndices.hoisted_and_forward n C k u t g hkg hor)
    (HoistAndIndices.hoisted_and_inverse n C k u t)
    (HoistAndIndices.hoisted_and_injOn C k g hkg hor)
    (HoistDirty.negative_and_profile_equiv G C k u t g hR hkg hor hu ht hequ ho hfun hclean)

end PEqualNP.Outside.L_meta_3566.NegativeMass

namespace PEqualNP.Outside.L_meta_3566.HoistTrueCount
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.HoistEval PEqualNP.Outside.L_meta_3566.HoistBase
open PEqualNP.Outside.L_meta_3566.HoistNegative

lemma del_wires_eq_erase (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length)
    (hu : u < n+k)
    (hpre : ∀ g ∈ E.gates.take k, ∀ i ∈ g.inputs, i < n+k)
    (hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n+k) false = (E.wires (List.ofFn x)).getD u false)
    (x : Fin n → Bool) :
    (del n k u E).wires (List.ofFn x) = (E.wires (List.ofFn x)).eraseIdx (n+k) := by
  have hlE : (E.wires (List.ofFn x)).length = n+E.gates.length := by
    rw [wires_eq, foldl_step_length, List.length_ofFn]
  have hlD : ((del n k u E).wires (List.ofFn x)).length = n+(del n k u E).gates.length := by
    rw [wires_eq, foldl_step_length, List.length_ofFn]
  have hm : n+k < (E.wires (List.ofFn x)).length := by rw [hlE]; omega
  have hlen : ((del n k u E).wires (List.ofFn x)).length =
      ((E.wires (List.ofFn x)).eraseIdx (n+k)).length := by
    rw [hlD, List.length_eraseIdx_of_lt hm, hlE]
    have hglen := del_length n k u E hk
    omega
  have hv (j : ℕ) :
      ((del n k u E).wires (List.ofFn x)).getD j false =
      ((E.wires (List.ofFn x)).eraseIdx (n+k)).getD j false := by
    by_cases hj : j < n+k
    · have h := del_wire n k u E hk hu hpre hcopy x j
      simpa [sig, hj, List.getD_eq_getElem?_getD, List.getElem?_eraseIdx] using h
    · have h := del_wire n k u E hk hu hpre hcopy x (j+1)
      have hj1 : ¬ j+1 < n+k := by omega
      have hj2 : j+1 ≠ n+k := by omega
      simpa [sig, hj, hj1, hj2, List.getD_eq_getElem?_getD, List.getElem?_eraseIdx] using h
  apply List.ext_getElem hlen
  intro j hj1 hj2
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1,
    List.getElem?_eq_getElem hj2, Option.getD_some] using hv j

lemma count_true_eraseIdx (w : List Bool) (m : ℕ) (hm : m < w.length) :
    (w.eraseIdx m).count true + (if w.getD m false then 1 else 0) = w.count true := by
  induction w generalizing m with
  | nil => simp at hm
  | cons b w ih =>
    cases m with
    | zero => cases b <;> simp
    | succ m =>
      have hm' : m < w.length := by simpa using hm
      have h := ih m hm'
      cases b <;>
        simp only [List.eraseIdx_cons_succ, List.getD_cons_succ, List.count_cons_self,
          List.count_cons_of_ne Bool.false_ne_true] <;> omega

lemma hoisted_negative_wires_eq_erase (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) :
    (hoisted n D k u t).wires (List.ofFn x) =
      (D.wires (List.ofFn x)).eraseIdx (n+k) ++ [false] := by
  have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
  let E := lifted n D k u t
  have hER := lifted_readsBack n D k u t hR hk hu ht ho
  have hEk := lifted_get_copy n D k u t hk
  have hkE : k < E.gates.length := by simp [E, lifted]; omega
  have hcopy : ∀ y : Fin n → Bool,
      (E.wires (List.ofFn y)).getD (n+k) false = (E.wires (List.ofFn y)).getD u false := by
    intro y
    simpa using wires_copy E k u hEk (List.ofFn y) (by simpa using hu)
  have heq := del_wires_eq_erase n k u E hkE hu (readsBack_take n E hER k) hcopy x
  have hl : (D.wires (List.ofFn x)).length = n+D.gates.length := by
    rw [wires_eq, foldl_step_length, List.length_ofFn]
  change (hoisted n D k u t).wires (List.ofFn x) = _ at heq
  rw [lifted_negative_wires n D k u t hkg ht x htfalse hofalse,
    List.eraseIdx_append_of_lt_length (by omega)] at heq
  exact heq

lemma hoisted_negative_true_count (n : ℕ) (D : Circuit) (k u t : ℕ)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some ⟨GateOp.or,[u,t]⟩)
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) :
    ((hoisted n D k u t).wires (List.ofFn x)).count true +
      (if (D.wires (List.ofFn x)).getD (n+k) false then 1 else 0) =
      (D.wires (List.ofFn x)).count true := by
  have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
  have hl : (D.wires (List.ofFn x)).length = n+D.gates.length := by
    rw [wires_eq, foldl_step_length, List.length_ofFn]
  rw [hoisted_negative_wires_eq_erase n D k u t hR hkg hu ht ho x htfalse hofalse]
  simpa using count_true_eraseIdx (D.wires (List.ofFn x)) (n+k) (by omega)

end PEqualNP.Outside.L_meta_3566.HoistTrueCount

namespace PEqualNP.Outside.L_meta_3566.WireMass
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_3566.HoistNegative

lemma hoisted_negative_true_count_equiv (n : ℕ) (D : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n D) (hkg : D.gates[k]? = some g)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (hu : u < n+k) (ht : t < n+k) (ho : D.output < n+D.gates.length)
    (x : Fin n → Bool) (htfalse : (D.wires (List.ofFn x)).getD t false = false)
    (hofalse : circuitFun n D x = false) :
    ((hoisted n D k u t).wires (List.ofFn x)).count true +
      (if (D.wires (List.ofFn x)).getD (n+k) false then 1 else 0) =
      (D.wires (List.ofFn x)).count true := by
  have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
  have hkg' : (ordered D k u t).gates[k]? = some ⟨GateOp.or,[u,t]⟩ := by
    simp [ordered, hk]
  have ho' : (ordered D k u t).output < n+(ordered D k u t).gates.length := by
    simpa [ordered] using ho
  have htfalse' : ((ordered D k u t).wires (List.ofFn x)).getD t false = false := by
    rw [ordered_wires_eq D k u t g hkg hequ]
    exact htfalse
  have hofalse' : circuitFun n (ordered D k u t) x = false := by
    rw [ordered_fun_eq n D k u t g hkg hequ]
    exact hofalse
  have h := HoistTrueCount.hoisted_negative_true_count n (ordered D k u t) k u t
    (ordered_readsBack n D k u t hR hu ht) hkg' hu ht ho' x htfalse' hofalse'
  rw [hoisted_ordered_eq, ordered_wires_eq D k u t g hkg hequ] at h
  exact h

noncomputable def mass {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : ℕ :=
  ∑ x ∈ NegativeMass.falseInputs G, (C.wires (List.ofFn x)).count true

lemma hoist_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g)
    (hu : u ∈ g.inputs) (ht : t ∈ g.inputs)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (ho : C.output < n+C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true)
    (x : Fin n → Bool) (hx : graphFun G ∅ x = false) :
    ((hoisted n C k u t).wires (List.ofFn x)).count true +
      (if gateVal n C k x then 1 else 0) = (C.wires (List.ofFn x)).count true := by
  have hreads := HoistBase.readsBack_get n C hR k g hkg
  have htfalse : (C.wires (List.ofFn x)).getD t false = false := by
    cases h : (C.wires (List.ofFn x)).getD t false
    · rfl
    · have hc := hclean x h
      rw [hx] at hc
      cases hc
  exact hoisted_negative_true_count_equiv n C k u t g hR hkg hequ
    (hreads u hu) (hreads t ht) ho x htfalse (by rw [hfun,hx])

lemma hoist_mass_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g)
    (hu : u ∈ g.inputs) (ht : t ∈ g.inputs)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (ho : C.output < n+C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) :
    mass G (hoisted n C k u t) ≤ mass G C := by
  apply Finset.sum_le_sum
  intro x hx
  have hc := hoist_count G C k u t g hR hkg hu ht hequ ho hfun hclean x
    ((NegativeMass.mem_falseInputs G x).mp hx)
  omega

lemma hoist_mass_lt_of_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k u t : ℕ) (g : Gate)
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g)
    (hu : u ∈ g.inputs) (ht : t ∈ g.inputs)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (ho : C.output < n+C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) (hdirty : ¬ BelowF G C k) :
    mass G (hoisted n C k u t) < mass G C := by
  classical
  unfold mass
  apply Finset.sum_lt_sum
  · intro x hx
    have hc := hoist_count G C k u t g hR hkg hu ht hequ ho hfun hclean x
      ((NegativeMass.mem_falseInputs G x).mp hx)
    omega
  · change ¬ ∀ x : Fin n → Bool, gateVal n C k x = true → graphFun G ∅ x = true at hdirty
    push Not at hdirty
    obtain ⟨x, hxgate, hxF⟩ := hdirty
    have hx : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hxF
    refine ⟨x, (NegativeMass.mem_falseInputs G x).mpr hx, ?_⟩
    have hc := hoist_count G C k u t g hR hkg hu ht hequ ho hfun hclean x hx
    rw [hxgate] at hc
    simp only [↓reduceIte] at hc
    omega

lemma exists_minimum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Circuit → Prop) (hP : ∃ C, P C) :
    ∃ C, P C ∧ ∀ D, P D → mass G C ≤ mass G D := by
  classical
  have hex : ∃ m, ∃ C, P C ∧ mass G C = m := by
    obtain ⟨C, hC⟩ := hP
    exact ⟨mass G C, C, hC, rfl⟩
  obtain ⟨C, hC, hm⟩ := Nat.find_spec hex
  refine ⟨C, hC, ?_⟩
  intro D hD
  rw [hm]
  exact Nat.find_min' hex ⟨D, hD, rfl⟩

lemma minimum_forces_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Circuit → Prop) (C : Circuit) (k u t : ℕ) (g : Gate)
    (hmin : ∀ D, P D → mass G C ≤ mass G D) (hP : P (hoisted n C k u t))
    (hR : ReadsBack n C) (hkg : C.gates[k]? = some g)
    (hu : u ∈ g.inputs) (ht : t ∈ g.inputs)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (ho : C.output < n+C.gates.length) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true) : BelowF G C k := by
  by_contra hdirty
  have hlt := hoist_mass_lt_of_dirty G C k u t g hR hkg hu ht hequ ho hfun hclean hdirty
  have hle := hmin _ hP
  omega

end PEqualNP.Outside.L_meta_3566.WireMass


namespace PEqualNP.Outside.L_meta_3566.WireProfile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma list_count_true (w : List Bool) :
    w.count true = ∑ j ∈ Finset.range w.length, (if w.getD j false then 1 else 0) := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    cases b <;> simp [ih]

noncomputable def trueGates {n : ℕ} (C : Circuit) (x : Fin n → Bool) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j => gateVal n C j x = true

lemma mem_trueGates {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) :
    j ∈ trueGates C x ↔ j < C.gates.length ∧ gateVal n C j x = true := by
  classical
  simp [trueGates]

lemma wire_count {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).count true = (List.ofFn x).count true + (trueGates C x).card := by
  classical
  obtain ⟨t, ht, hl⟩ := AO2Upper.wiresFrom_prefix C.gates (List.ofFn x)
  have hw : C.wires (List.ofFn x) = List.ofFn x ++ t := ht
  rw [hw, List.count_append]
  congr 1
  rw [list_count_true, hl]
  have hv (j : ℕ) : t.getD j false = gateVal n C j x := by
    change t.getD j false = (C.wires (List.ofFn x)).getD (n+j) false
    rw [hw, List.getD_append_right _ _ _ _ (by simp)]
    simp
  simp_rw [hv]
  simp [trueGates]

lemma image_trueGates_subset {n : ℕ} (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j < D.gates.length, f j < C.gates.length)
    (x : Fin n → Bool)
    (hval : ∀ j < D.gates.length, gateVal n D j x = true → gateVal n C (f j) x = true) :
    (trueGates D x).image f ⊆ trueGates C x := by
  classical
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨hj, hv⟩ := (mem_trueGates D x j).mp hj
  exact (mem_trueGates C x (f j)).mpr ⟨hforward j hj, hval j hj hv⟩

lemma card_trueGates_image {n : ℕ} (D : Circuit) (f : ℕ → ℕ)
    (hinj : Set.InjOn f (Finset.range D.gates.length : Set ℕ)) (x : Fin n → Bool) :
    ((trueGates D x).image f).card = (trueGates D x).card := by
  classical
  apply Finset.card_image_of_injOn
  intro i hi j hj heq
  exact hinj (Finset.mem_range.mpr ((mem_trueGates D x i).mp hi).1)
    (Finset.mem_range.mpr ((mem_trueGates D x j).mp hj).1) heq

lemma wire_count_le {n : ℕ} (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j < D.gates.length, f j < C.gates.length)
    (hinj : Set.InjOn f (Finset.range D.gates.length : Set ℕ))
    (x : Fin n → Bool)
    (hval : ∀ j < D.gates.length, gateVal n D j x = true → gateVal n C (f j) x = true) :
    (D.wires (List.ofFn x)).count true ≤ (C.wires (List.ofFn x)).count true := by
  have h := Finset.card_le_card (image_trueGates_subset C D f hforward x hval)
  rw [card_trueGates_image D f hinj x] at h
  rw [wire_count D x, wire_count C x]
  omega

lemma wire_count_lt {n : ℕ} (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j < D.gates.length, f j < C.gates.length)
    (hinj : Set.InjOn f (Finset.range D.gates.length : Set ℕ))
    (x : Fin n → Bool)
    (hval : ∀ j < D.gates.length, gateVal n D j x = true → gateVal n C (f j) x = true)
    (hstrict : ∃ i < C.gates.length, gateVal n C i x = true ∧
      ∀ j < D.gates.length, f j = i → gateVal n D j x = false) :
    (D.wires (List.ofFn x)).count true < (C.wires (List.ofFn x)).count true := by
  classical
  have hsub := image_trueGates_subset C D f hforward x hval
  have hne : (trueGates D x).image f ≠ trueGates C x := by
    intro heq
    obtain ⟨i, hi, hv, hm⟩ := hstrict
    have himem : i ∈ (trueGates D x).image f :=
      heq.symm ▸ (mem_trueGates C x i).mpr ⟨hi,hv⟩
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp himem
    obtain ⟨hj, hjv⟩ := (mem_trueGates D x j).mp hj
    rw [hm j hj hji] at hjv
    cases hjv
  have h := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hne⟩)
  rw [card_trueGates_image D f hinj x] at h
  rw [wire_count D x, wire_count C x]
  omega

lemma mass_le_of_injective {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j < D.gates.length, f j < C.gates.length)
    (hinj : Set.InjOn f (Finset.range D.gates.length : Set ℕ))
    (hval : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      ∀ j < D.gates.length, gateVal n D j x = true → gateVal n C (f j) x = true) :
    WireMass.mass G D ≤ WireMass.mass G C := by
  apply Finset.sum_le_sum
  intro x hx
  exact wire_count_le C D f hforward hinj x
    (hval x ((NegativeMass.mem_falseInputs G x).mp hx))

lemma mass_lt_of_injective {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j < D.gates.length, f j < C.gates.length)
    (hinj : Set.InjOn f (Finset.range D.gates.length : Set ℕ))
    (hval : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      ∀ j < D.gates.length, gateVal n D j x = true → gateVal n C (f j) x = true)
    (hstrict : ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧
      ∃ i < C.gates.length, gateVal n C i x = true ∧
        ∀ j < D.gates.length, f j = i → gateVal n D j x = false) :
    WireMass.mass G D < WireMass.mass G C := by
  unfold WireMass.mass
  apply Finset.sum_lt_sum
  · intro x hx
    exact wire_count_le C D f hforward hinj x
      (hval x ((NegativeMass.mem_falseInputs G x).mp hx))
  · obtain ⟨x, hx, hstrict⟩ := hstrict
    exact ⟨x, (NegativeMass.mem_falseInputs G x).mpr hx,
      wire_count_lt C D f hforward hinj x (hval x hx) hstrict⟩

lemma mass_lt_of_profile {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (f : ℕ → ℕ)
    (hforward : ∀ j < D.gates.length, f j < C.gates.length)
    (hinj : Set.InjOn f (Finset.range D.gates.length : Set ℕ))
    (hval : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      ∀ j < D.gates.length, gateVal n D j x = true → gateVal n C (f j) x = true)
    (hstrict : ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧
      ∃ j < D.gates.length, gateVal n C (f j) x = true ∧ gateVal n D j x = false) :
    WireMass.mass G D < WireMass.mass G C := by
  apply mass_lt_of_injective G C D f hforward hinj hval
  obtain ⟨x, hx, j, hj, hc, hd⟩ := hstrict
  refine ⟨x,hx,f j,hforward j hj,hc,?_⟩
  intro i hi hij
  have heq : i = j := hinj (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) hij
  simpa [heq] using hd

end PEqualNP.Outside.L_meta_3566.WireProfile


namespace PEqualNP.Outside.L_meta_3566.JointMinimum
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def IsJointLeast {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  IsLeastAO G C ∧
  (∀ D, IsLeastAO G D → (junk G C).card ≤ (junk G D).card) ∧
  ∀ D, IsLeastAO G D → (junk G D).card = (junk G C).card →
    WireMass.mass G C ≤ WireMass.mass G D

lemma exists_joint_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty) : ∃ C, IsJointLeast G C := by
  classical
  obtain ⟨C₀, hC₀⟩ := exists_least_ao G hE
  have hex : ∃ j, ∃ C, IsLeastAO G C ∧ (junk G C).card = j :=
    ⟨(junk G C₀).card, C₀, hC₀, rfl⟩
  obtain ⟨C, hC, hJ⟩ := Nat.find_spec hex
  have hmin : ∀ D, IsLeastAO G D → (junk G C).card ≤ (junk G D).card := by
    intro D hD
    rw [hJ]
    exact Nat.find_min' hex ⟨D,hD,rfl⟩
  obtain ⟨D, ⟨hD,hJD⟩, hW⟩ := WireMass.exists_minimum G
    (fun D => IsLeastAO G D ∧ (junk G D).card = (junk G C).card) ⟨C,hC,rfl⟩
  refine ⟨D,hD,?_,?_⟩
  · intro E hE
    rw [hJD]
    exact hmin E hE
  · intro E hE hJE
    exact hW E ⟨hE,hJE.trans hJD⟩

lemma rewrite_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hC : IsJointLeast G C)
    (hAO : IsAO2 n D) (hF : circuitFun n D = graphFun G ∅)
    (hsize : D.size ≤ C.size) (hJ : (junk G D).card ≤ (junk G C).card)
    (hW : WireMass.mass G D ≤ WireMass.mass G C) :
    D.size = C.size ∧ (junk G D).card = (junk G C).card ∧
      WireMass.mass G D = WireMass.mass G C ∧ IsJointLeast G D := by
  have hsize' : C.size ≤ D.size := hC.1.2.2 D hAO hF
  have hD : IsLeastAO G D := ⟨hAO,hF,fun E hE hEF => hsize.trans (hC.1.2.2 E hE hEF)⟩
  have hj : (junk G D).card = (junk G C).card := Nat.le_antisymm hJ (hC.2.1 D hD)
  have hw : WireMass.mass G D = WireMass.mass G C :=
    Nat.le_antisymm hW (hC.2.2 D hD hj)
  refine ⟨Nat.le_antisymm hsize hsize',hj,hw,hD,?_,?_⟩
  · intro E hE
    rw [hj]
    exact hC.2.1 E hE
  · intro E hE hJE
    rw [hw]
    exact hC.2.2 E hE (hJE.trans hj)

lemma no_strict_rewrite {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hC : IsJointLeast G C)
    (hAO : IsAO2 n D) (hF : circuitFun n D = graphFun G ∅)
    (hsize : D.size ≤ C.size) (hJ : (junk G D).card ≤ (junk G C).card)
    (hW : WireMass.mass G D ≤ WireMass.mass G C)
    (hstrict : D.size < C.size ∨ (junk G D).card < (junk G C).card ∨
      WireMass.mass G D < WireMass.mass G C) : False := by
  obtain ⟨hs,hj,hw,_⟩ := rewrite_le G C D hC hAO hF hsize hJ hW
  omega

lemma clean_or_of_admissible_hoist {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsJointLeast G C) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hor : g.op = GateOp.or)
    (hu : u ∈ g.inputs) (ht : t ∈ g.inputs)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (ho : C.output < n+C.gates.length)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true)
    (hAO : IsAO2 n (HoistNegative.hoisted n C k u t))
    (hF : circuitFun n (HoistNegative.hoisted n C k u t) = graphFun G ∅)
    (hsize : (HoistNegative.hoisted n C k u t).size ≤ C.size) : BelowF G C k := by
  have hR := hC.1.1.2.1
  have hCF := hC.1.2.1
  have hJ := HoistDirty.junk_card_equiv G C k u t g hR hkg hor hu ht hequ ho hCF hclean
  have hW := WireMass.hoist_mass_le G C k u t g hR hkg hu ht hequ ho hCF hclean
  by_contra hdirty
  have hlt := WireMass.hoist_mass_lt_of_dirty G C k u t g hR hkg hu ht hequ ho hCF hclean hdirty
  exact no_strict_rewrite G C (HoistNegative.hoisted n C k u t) hC hAO hF hsize
    hJ.le hW (Or.inr (Or.inr hlt))

end PEqualNP.Outside.L_meta_3566.JointMinimum


namespace PEqualNP.Outside.L_meta_3566.RawOrCone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

theorem cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.EdgeOwnership.coneStep]
    omega

theorem cones_length (n : ℕ) (C : Circuit) :
    (PEqualNP.EdgeOwnership.cones n C).length = C.gates.length := by
  unfold PEqualNP.EdgeOwnership.cones
  rw [cones_len]; simp

theorem cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    PEqualNP.EdgeOwnership.InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧
      n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ PEqualNP.EdgeOwnership.InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold PEqualNP.EdgeOwnership.InCone PEqualNP.EdgeOwnership.cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

theorem inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

theorem inCone_of_read (n : ℕ) (C : Circuit) (k j : ℕ) (hj : j < C.gates.length) (hk : k < j)
    (hin : n + k ∈ (gateAt C j).inputs) : PEqualNP.EdgeOwnership.InCone n C k j :=
  (inCone_iff n C k j).mpr ⟨hj, k, hk, hin, Or.inl rfl⟩

theorem inCone_trans (n : ℕ) (C : Circuit) (i k : ℕ) (hik : PEqualNP.EdgeOwnership.InCone n C i k) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C k j → PEqualNP.EdgeOwnership.InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k', hk', hin, h3⟩ := h
    rw [inCone_iff]
    refine ⟨h0, k', hk', hin, Or.inr ?_⟩
    rcases h3 with h3 | h3
    · rw [← h3]; exact hik
    · exact ih k' hk' h3

lemma first_dirty_no_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hT : PEqualNP.TopForm.TopForm G C) (j : ℕ) (hj : j < C.gates.length)
    (hjAnd : (gateAt C j).op = GateOp.and)
    (hfirst : ∀ i < j, (gateAt C i).op = GateOp.and → BelowF G C i) :
    ∀ i, InCone n C i j → (gateAt C i).op ≠ GateOp.and := by
  intro i hcone hiAnd
  have hlt := (inCone_lt n C i j hcone).1
  exact hT i (by omega) j hj hiAnd (hfirst i hlt hiAnd) hjAnd hcone

lemma first_dirty_cone_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : PEqualNP.TopForm.TopForm G C)
    (j : ℕ) (hj : j < C.gates.length) (hjAnd : (gateAt C j).op = GateOp.and)
    (hfirst : ∀ i < j, (gateAt C i).op = GateOp.and → BelowF G C i) :
    ∀ i, InCone n C i j → (gateAt C i).op = GateOp.or := by
  intro i hcone
  have hi : i < C.gates.length := by have := (inCone_lt n C i j hcone).1; omega
  have hmem : gateAt C i ∈ C.gates := by
    exact List.mem_of_getElem? (show C.gates[i]? = some (gateAt C i) by
      simp [gateAt, List.getD_eq_getElem?_getD, hi])
  exact (hAO.1 _ hmem).resolve_left (first_dirty_no_and G C hT j hj hjAnd hfirst i hcone)

lemma opnd_mem (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (k : ℕ)
    (hk : k < C.gates.length) (b : Fin 2) : opnd C k b ∈ (gateAt C k).inputs := by
  have hmem : gateAt C k ∈ C.gates := by
    exact List.mem_of_getElem? (show C.gates[k]? = some (gateAt C k) by
      simp [gateAt, List.getD_eq_getElem?_getD, hk])
  have hlen := hAO.2.2 _ hmem
  have hb : b.val < (gateAt C k).inputs.length := by rw [hlen]; exact b.isLt
  exact List.mem_of_getElem? (show (gateAt C k).inputs[b.val]? = some (opnd C k b) by
    simp [opnd, List.getD_eq_getElem?_getD, hb])

lemma wire_raw_or_of_cone (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length)
    (hor : ∀ i, InCone n C i j → (gateAt C i).op = GateOp.or) :
    ∀ w < n+j, (n ≤ w → InCone n C (w-n) j) →
      ∃ S : Finset (Fin n), ∀ x : Fin n → Bool,
        wireVal n C w x = true ↔ ∃ v ∈ S, x v = true := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hcone
    by_cases hwn : w < n
    · refine ⟨{⟨w,hwn⟩}, ?_⟩
      intro x
      rw [Pruning.wireVal_lt C w hwn x]
      simp
    · have hn : n ≤ w := by omega
      let k := w-n
      have hk : k < j := by dsimp [k]; omega
      have hkC : k < C.gates.length := by omega
      have hweq : w = n+k := by dsimp [k]; omega
      have hkj : InCone n C k j := hcone hn
      have hkOr := hor k hkj
      have hoperand (b : Fin 2) : ∃ S : Finset (Fin n), ∀ x : Fin n → Bool,
          wireVal n C (opnd C k b) x = true ↔ ∃ v ∈ S, x v = true := by
        have hm := opnd_mem n C hAO k hkC b
        have hlt := hAO.2.1 k hkC (opnd C k b) hm
        apply ih (opnd C k b) (by omega) (by omega)
        intro hnop
        have hi : opnd C k b - n < k := by omega
        have hc : InCone n C (opnd C k b-n) k := by
          apply inCone_of_read n C _ k hkC hi
          have heq : n+(opnd C k b-n) = opnd C k b := by omega
          rw [heq]
          exact hm
        exact inCone_trans n C _ k hc j hkj
      obtain ⟨S,hS⟩ := hoperand 0
      obtain ⟨T,hT⟩ := hoperand 1
      refine ⟨S ∪ T, ?_⟩
      intro x
      have heval := Pruning.gate_eq C hAO k hkC x
      change wireVal n C (n+k) x = _ at heval
      have heval' : wireVal n C (n+k) x =
          (wireVal n C (opnd C k 0) x || wireVal n C (opnd C k 1) x) := by
        simpa [hkOr, Pruning.isA, Pruning.opv] using heval
      rw [hweq, heval', Bool.or_eq_true, hS x, hT x]
      constructor
      · rintro (⟨v,hv,hx⟩ | ⟨v,hv,hx⟩)
        · exact ⟨v,Finset.mem_union_left T hv,hx⟩
        · exact ⟨v,Finset.mem_union_right S hv,hx⟩
      · rintro ⟨v,hv,hx⟩
        rcases Finset.mem_union.mp hv with hv | hv
        · exact Or.inl ⟨v,hv,hx⟩
        · exact Or.inr ⟨v,hv,hx⟩

lemma first_dirty_operands_raw_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : PEqualNP.TopForm.TopForm G C)
    (j : ℕ) (hj : j < C.gates.length) (hjAnd : (gateAt C j).op = GateOp.and)
    (hfirst : ∀ i < j, (gateAt C i).op = GateOp.and → BelowF G C i)
    (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
    ∃ S : Finset (Fin n), ∀ x : Fin n → Bool,
      wireVal n C w x = true ↔ ∃ v ∈ S, x v = true := by
  apply wire_raw_or_of_cone n C hAO j hj (first_dirty_cone_or G C hAO hT j hj hjAnd hfirst)
    w (hAO.2.1 j hj w hw)
  intro hn
  have hi : w-n < j := by have := hAO.2.1 j hj w hw; omega
  apply inCone_of_read n C (w-n) j hj hi
  have heq : n+(w-n) = w := by omega
  rw [heq]
  exact hw

lemma prior_and_below_of_least_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hmin : ∀ i ∈ junk G C, j ≤ i) :
    ∀ i < j, (gateAt C i).op = GateOp.and → BelowF G C i := by
  intro i hi hiAnd x hx
  by_contra hxF
  have hiJ : i ∈ junk G C := by
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hiAnd, by omega, x, hx, Bool.eq_false_iff.mpr hxF⟩
  have := hmin i hiJ
  omega

lemma least_junk_no_and_and_raw_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : PEqualNP.TopForm.TopForm G C)
    (j : ℕ) (hj : j ∈ junk G C) (hmin : ∀ i ∈ junk G C, j ≤ i) :
    (∀ i, InCone n C i j → (gateAt C i).op ≠ GateOp.and) ∧
    ∀ w ∈ (gateAt C j).inputs, ∃ S : Finset (Fin n), ∀ x : Fin n → Bool,
      wireVal n C w x = true ↔ ∃ v ∈ S, x v = true := by
  have hmem := hj
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hmem
  have hfirst := prior_and_below_of_least_junk G C j hmem.1 hmin
  refine ⟨first_dirty_no_and G C hT j hmem.1 hmem.2.1 hfirst, ?_⟩
  intro w hw
  exact first_dirty_operands_raw_or G C hAO hT j hmem.1 hmem.2.1 hfirst w hw

lemma exists_first_junk_raw_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : PEqualNP.TopForm.TopForm G C)
    (hJ : (junk G C).Nonempty) :
    ∃ j ∈ junk G C, (∀ i ∈ junk G C, j ≤ i) ∧
      (∀ i, InCone n C i j → (gateAt C i).op ≠ GateOp.and) ∧
      ∀ w ∈ (gateAt C j).inputs, ∃ S : Finset (Fin n), ∀ x : Fin n → Bool,
        wireVal n C w x = true ↔ ∃ v ∈ S, x v = true := by
  let j := (junk G C).min' hJ
  have hj : j ∈ junk G C := Finset.min'_mem _ hJ
  have hmin : ∀ i ∈ junk G C, j ≤ i := fun i hi => Finset.min'_le _ i hi
  exact ⟨j,hj,hmin,least_junk_no_and_and_raw_or G C hAO hT j hj hmin⟩

end PEqualNP.Outside.L_meta_3566.RawOrCone


namespace PEqualNP.Outside.L_meta_3566.WireFirst
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def IsWireLeast {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  IsLeastAO G C ∧ ∀ D, IsLeastAO G D → WireMass.mass G C ≤ WireMass.mass G D

lemma exists_wire_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty) : ∃ C, IsWireLeast G C := by
  obtain ⟨C,hC,hmin⟩ := WireMass.exists_minimum G (IsLeastAO G) (exists_least_ao G hE)
  exact ⟨C,hC,hmin⟩

lemma rewrite_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hC : IsWireLeast G C)
    (hAO : IsAO2 n D) (hF : circuitFun n D = graphFun G ∅)
    (hsize : D.size ≤ C.size) (hW : WireMass.mass G D ≤ WireMass.mass G C) :
    D.size = C.size ∧ WireMass.mass G D = WireMass.mass G C ∧ IsWireLeast G D := by
  have hsize' : C.size ≤ D.size := hC.1.2.2 D hAO hF
  have hD : IsLeastAO G D := ⟨hAO,hF,fun E hE hEF => hsize.trans (hC.1.2.2 E hE hEF)⟩
  have hw : WireMass.mass G D = WireMass.mass G C := Nat.le_antisymm hW (hC.2 D hD)
  refine ⟨Nat.le_antisymm hsize hsize',hw,hD,?_⟩
  intro E hE
  rw [hw]
  exact hC.2 E hE

lemma no_strict_rewrite {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hC : IsWireLeast G C)
    (hAO : IsAO2 n D) (hF : circuitFun n D = graphFun G ∅)
    (hsize : D.size ≤ C.size) (hW : WireMass.mass G D < WireMass.mass G C) : False := by
  obtain ⟨_,hw,_⟩ := rewrite_le G C D hC hAO hF hsize hW.le
  omega

lemma clean_or_of_admissible_hoist {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsWireLeast G C) (k u t : ℕ) (g : Gate)
    (hkg : C.gates[k]? = some g) (hu : u ∈ g.inputs) (ht : t ∈ g.inputs)
    (hequ : ∀ w : List Bool, GateOp.or.eval ([u,t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false))
    (ho : C.output < n+C.gates.length)
    (hclean : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      graphFun G ∅ x = true)
    (hAO : IsAO2 n (HoistNegative.hoisted n C k u t))
    (hF : circuitFun n (HoistNegative.hoisted n C k u t) = graphFun G ∅)
    (hsize : (HoistNegative.hoisted n C k u t).size ≤ C.size) : BelowF G C k := by
  by_contra hdirty
  have hlt := WireMass.hoist_mass_lt_of_dirty G C k u t g hC.1.1.2.1 hkg hu ht hequ
    ho hC.1.2.1 hclean hdirty
  exact no_strict_rewrite G C _ hC hAO hF hsize hlt

end PEqualNP.Outside.L_meta_3566.WireFirst


namespace PEqualNP.Outside.L_meta_3566.MixedShell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_3566.HoistEval
open PEqualNP.Outside.L_meta_3566.AO2Upper (Good)

def oldBlock (m a b c d : ℕ) : List Gate :=
  [⟨.or,[a,b]⟩,⟨.or,[c,d]⟩,⟨.and,[m,m+1]⟩]

def newBlock (m a b c d : ℕ) : List Gate :=
  [⟨.and,[a,d]⟩,⟨.and,[c,b]⟩,⟨.or,[m,m+1]⟩]

def oldCircuit (n : ℕ) (pre post : List Gate) (a b c d out : ℕ) : Circuit :=
  ⟨pre ++ oldBlock (n+pre.length) a b c d ++ post,out⟩

def newCircuit (n : ℕ) (pre post : List Gate) (a b c d out : ℕ) : Circuit :=
  ⟨pre ++ newBlock (n+pre.length) a b c d ++ post,out⟩

lemma size_eq (n : ℕ) (pre post : List Gate) (a b c d out : ℕ) :
    (newCircuit n pre post a b c d out).size = (oldCircuit n pre post a b c d out).size := by
  simp [newCircuit,oldCircuit,newBlock,oldBlock,Circuit.size]

lemma good_of_ao2 (n : ℕ) (gs : List Gate) (out : ℕ) (hAO : IsAO2 n ⟨gs,out⟩) : Good n gs := by
  induction gs generalizing n with
  | nil => trivial
  | cons g gs ih =>
    refine ⟨⟨hAO.1 g (by simp),hAO.2.2 g (by simp),?_⟩,?_⟩
    · intro i hi
      have h := hAO.2.1 0 (by simp) i (by simpa [gateAt] using hi)
      simpa using h
    · apply ih (n+1)
      refine ⟨fun g hg => hAO.1 g (by simp [hg]),?_,fun g hg => hAO.2.2 g (by simp [hg])⟩
      intro j hj i hi
      have hg : gateAt (⟨g::gs,out⟩ : Circuit) (j+1) = gateAt ⟨gs,out⟩ j := by
        simp [gateAt]
      have h := hAO.2.1 (j+1) (by simp; omega) i (by simpa [hg] using hi)
      omega

lemma good_append_iff (pre post : List Gate) (n : ℕ) :
    Good n (pre++post) ↔ Good n pre ∧ Good (n+pre.length) post := by
  induction pre generalizing n with
  | nil => simp [Good]
  | cons g gs ih =>
    simp only [List.cons_append,Good,List.length_cons]
    rw [ih]
    constructor
    · rintro ⟨h1,h2,h3⟩
      exact ⟨⟨h1,h2⟩,by convert h3 using 1; omega⟩
    · rintro ⟨⟨h1,h2⟩,h3⟩
      exact ⟨h1,h2,by convert h3 using 1; omega⟩

lemma new_ao2 (n : ℕ) (pre post : List Gate) (a b c d out : ℕ)
    (hAO : IsAO2 n (oldCircuit n pre post a b c d out))
    (ha : a < n+pre.length) (hb : b < n+pre.length)
    (hc : c < n+pre.length) (hd : d < n+pre.length) :
    IsAO2 n (newCircuit n pre post a b c d out) := by
  have hg := good_of_ao2 n _ out hAO
  change Good n (pre ++ oldBlock (n+pre.length) a b c d ++ post) at hg
  rw [good_append_iff,good_append_iff] at hg
  apply AO2Upper.good_ao2 n _ out
  rw [good_append_iff,good_append_iff]
  refine ⟨⟨hg.1.1,?_⟩,?_⟩
  · simp [newBlock,Good]
    omega
  · simpa [oldBlock,newBlock] using hg.2

lemma old_run (w : List Bool) (a b c d : ℕ)
    (_ha : a < w.length) (_hb : b < w.length) (hc : c < w.length) (hd : d < w.length) :
    (oldBlock w.length a b c d).foldl step w = w ++
      [w.getD a false || w.getD b false, w.getD c false || w.getD d false,
       (w.getD a false || w.getD b false) && (w.getD c false || w.getD d false)] := by
  simp [oldBlock,step,GateOp.eval,List.append_assoc,
    List.getElem?_append_left hc,List.getElem?_append_left hd]

lemma new_run (w : List Bool) (a b c d : ℕ)
    (_ha : a < w.length) (hb : b < w.length) (hc : c < w.length) (_hd : d < w.length) :
    (newBlock w.length a b c d).foldl step w = w ++
      [w.getD a false && w.getD d false, w.getD c false && w.getD b false,
       (w.getD a false && w.getD d false) || (w.getD c false && w.getD b false)] := by
  simp [newBlock,step,GateOp.eval,List.append_assoc,
    List.getElem?_append_left hc,List.getElem?_append_left hb]

lemma append_dom (a b s t : List Bool) (hlen : a.length = b.length)
    (hab : ∀ i, a.getD i false = true → b.getD i false = true)
    (hst : ∀ i, s.getD i false = true → t.getD i false = true) :
    ∀ i, (a++s).getD i false = true → (b++t).getD i false = true := by
  intro i hi
  by_cases hlt : i < a.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact hab i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega),←hlen]
    exact hst _ hi

lemma gate_dom (g : Gate) (hAO : g.op = .and ∨ g.op = .or) (f h : ℕ → Bool)
    (hfh : ∀ i, f i = true → h i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map h) = true := by
  rcases hAO with ho | ho <;> rw [ho]
  · simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    intro hf i hi
    exact hfh i (hf i hi)
  · simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨i,hi,hf⟩
    exact ⟨i,hi,hfh i hf⟩

lemma fold_dom (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (a b : List Bool) (hlen : a.length = b.length)
    (hab : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (gs.foldl step a).getD i false = true → (gs.foldl step b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    apply ih (fun g hg => hAO g (by simp [hg])) (step a g) (step b g)
    · simp [step,hlen]
    · apply append_dom a b _ _ hlen hab
      intro i hi
      cases i with
      | zero =>
        simp only [List.getD_cons_zero] at hi ⊢
        exact gate_dom g (hAO g (by simp)) _ _ hab hi
      | succ i => simp at hi

lemma block_dom (A B C D : Bool) :
    ∀ i, ([A && D,C && B,(A && D)||(C && B)] : List Bool).getD i false = true →
      ([A || B,C || D,(A || B)&&(C || D)] : List Bool).getD i false = true := by
  intro i
  rcases i with _ | _ | _ | i <;>
    cases A <;> cases B <;> cases C <;> cases D <;> simp

lemma wires_dom (n : ℕ) (pre post : List Gate) (a b c d out : ℕ)
    (hAO : IsAO2 n (oldCircuit n pre post a b c d out))
    (ha : a < n+pre.length) (hb : b < n+pre.length)
    (hc : c < n+pre.length) (hd : d < n+pre.length) (x : Fin n → Bool) :
    ∀ i, ((newCircuit n pre post a b c d out).wires (List.ofFn x)).getD i false = true →
      ((oldCircuit n pre post a b c d out).wires (List.ofFn x)).getD i false = true := by
  let w := pre.foldl step (List.ofFn x)
  have hl : w.length = n+pre.length := by simp [w,foldl_step_length]
  have hpost : ∀ g ∈ post, g.op = .and ∨ g.op = .or := by
    intro g hg
    apply hAO.1 g
    simp [oldCircuit,hg]
  simp only [newCircuit,oldCircuit,wires_eq,List.foldl_append]
  change ∀ i, (post.foldl step ((newBlock (n+pre.length) a b c d).foldl step w)).getD i false = true →
    (post.foldl step ((oldBlock (n+pre.length) a b c d).foldl step w)).getD i false = true
  rw [←hl,new_run w a b c d (by omega) (by omega) (by omega) (by omega),
    old_run w a b c d (by omega) (by omega) (by omega) (by omega)]
  apply fold_dom post hpost
  · simp
  · exact append_dom w w _ _ rfl (fun _ h => h) (block_dom _ _ _ _)

lemma fold_private_eq (gs : List Gate) (m : ℕ)
    (hprivate : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ≠ m ∧ i ≠ m+1)
    (a b : List Bool) (hlen : a.length = b.length)
    (hab : ∀ i, i ≠ m → i ≠ m+1 → a.getD i false = b.getD i false) :
    ∀ i, i ≠ m → i ≠ m+1 →
      (gs.foldl step a).getD i false = (gs.foldl step b).getD i false := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    apply ih (fun g hg => hprivate g (by simp [hg])) (step a g) (step b g)
    · simp [step,hlen]
    · have heval : g.op.eval (g.inputs.map fun i => a.getD i false) =
          g.op.eval (g.inputs.map fun i => b.getD i false) := by
        congr 1
        apply List.map_congr_left
        intro i hi
        obtain ⟨hi1,hi2⟩ := hprivate g (by simp) i hi
        exact hab i hi1 hi2
      intro i hi1 hi2
      by_cases hlt : i < a.length
      · change (a++[_]).getD i false = (b++[_]).getD i false
        rw [getD_append_left _ _ _ hlt,getD_append_left _ _ _ (by omega)]
        exact hab i hi1 hi2
      · change (a++[_]).getD i false = (b++[_]).getD i false
        rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega),hlen,heval]

lemma block_private_eq (w : List Bool) (A B C D : Bool)
    (hQ : ((A && D)||(C && B)) = ((A || B)&&(C || D))) :
    ∀ i, i ≠ w.length → i ≠ w.length+1 →
      (w++[A && D,C && B,(A && D)||(C && B)]).getD i false =
        (w++[A || B,C || D,(A || B)&&(C || D)]).getD i false := by
  intro i hi1 hi2
  by_cases hi : i < w.length
  · rw [getD_append_left _ _ _ hi,getD_append_left _ _ _ hi]
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
    have h0 : i-w.length ≠ 0 := by omega
    have h1 : i-w.length ≠ 1 := by omega
    generalize i-w.length = k at h0 h1 ⊢
    rcases k with _ | _ | _ | k
    · contradiction
    · contradiction
    · simpa using hQ
    · simp

lemma eval_eq_on (n : ℕ) (pre post : List Gate) (a b c d out : ℕ)
    (ha : a < n+pre.length) (hb : b < n+pre.length)
    (hc : c < n+pre.length) (hd : d < n+pre.length)
    (hprivate : ∀ g ∈ post, ∀ i ∈ g.inputs, i ≠ n+pre.length ∧ i ≠ n+pre.length+1)
    (ho1 : out ≠ n+pre.length) (ho2 : out ≠ n+pre.length+1) (x : Fin n → Bool)
    (hQ : let w := pre.foldl step (List.ofFn x)
      ((w.getD a false && w.getD d false)||(w.getD c false && w.getD b false)) =
        ((w.getD a false || w.getD b false)&&(w.getD c false || w.getD d false))) :
    circuitFun n (newCircuit n pre post a b c d out) x =
      circuitFun n (oldCircuit n pre post a b c d out) x := by
  let w := pre.foldl step (List.ofFn x)
  have hl : w.length = n+pre.length := by simp [w,foldl_step_length]
  change ((newCircuit n pre post a b c d out).wires (List.ofFn x)).getD out false =
    ((oldCircuit n pre post a b c d out).wires (List.ofFn x)).getD out false
  simp only [newCircuit,oldCircuit,wires_eq,List.foldl_append]
  change (post.foldl step ((newBlock (n+pre.length) a b c d).foldl step w)).getD out false =
    (post.foldl step ((oldBlock (n+pre.length) a b c d).foldl step w)).getD out false
  rw [←hl,new_run w a b c d (by omega) (by omega) (by omega) (by omega),
    old_run w a b c d (by omega) (by omega) (by omega) (by omega)]
  exact fold_private_eq post (n+pre.length) hprivate _ _ (by simp)
    (by simpa [hl] using block_private_eq w _ _ _ _ hQ) out ho1 ho2

lemma circuit_mono (n : ℕ) (C : Circuit) (hAO : AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  apply fold_dom C.gates hAO (List.ofFn x) (List.ofFn y) (by simp) _ C.output
  intro i hi
  by_cases h : i < n
  · have hx : (List.ofFn x).getD i false = x ⟨i,h⟩ := by simp [List.getD_eq_getElem?_getD,h]
    have hy : (List.ofFn y).getD i false = y ⟨i,h⟩ := by simp [List.getD_eq_getElem?_getD,h]
    rw [hx] at hi
    rw [hy]
    exact hxy _ hi
  · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simp; omega : (List.ofFn x).length ≤ i)] at hi

lemma graph_correct (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (a b c d out : ℕ)
    (hAO : IsAO2 n (oldCircuit n pre post a b c d out))
    (hfun : circuitFun n (oldCircuit n pre post a b c d out) = graphFun G ∅)
    (ha : a < n+pre.length) (hb : b < n+pre.length)
    (hc : c < n+pre.length) (hd : d < n+pre.length)
    (hprivate : ∀ g ∈ post, ∀ i ∈ g.inputs, i ≠ n+pre.length ∧ i ≠ n+pre.length+1)
    (ho1 : out ≠ n+pre.length) (ho2 : out ≠ n+pre.length+1)
    (hedge : ∀ u v : Fin n, G.Adj u v →
      let w := pre.foldl step (List.ofFn (pairInput u v))
      ((w.getD a false && w.getD d false)||(w.getD c false && w.getD b false)) =
        ((w.getD a false || w.getD b false)&&(w.getD c false || w.getD d false))) :
    circuitFun n (newCircuit n pre post a b c d out) = graphFun G ∅ := by
  have hD := new_ao2 n pre post a b c d out hAO ha hb hc hd
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    have h := wires_dom n pre post a b c d out hAO ha hb hc hd x out hx
    change circuitFun n (oldCircuit n pre post a b c d out) x = true at h
    rw [hfun] at h
    exact h
  · intro hx
    have hEdge : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
      simpa [graphFun] using hx
    obtain ⟨u,v,huv,hu,hv⟩ := hEdge
    have hpC : circuitFun n (oldCircuit n pre post a b c d out) (pairInput u v) = true := by
      rw [hfun]
      have hp : ∃ z t, G.Adj z t ∧ pairInput u v z = true ∧ pairInput u v t = true :=
        ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩
      simpa [graphFun] using hp
    have hpD : circuitFun n (newCircuit n pre post a b c d out) (pairInput u v) = true :=
      (eval_eq_on n pre post a b c d out ha hb hc hd hprivate ho1 ho2
        (pairInput u v) (hedge u v huv)).trans hpC
    apply circuit_mono n _ hD.1 (pairInput u v) x _ hpD
    intro z hz
    simp only [pairInput,decide_eq_true_eq] at hz
    rcases hz with rfl | rfl
    · exact hu
    · exact hv

lemma first_values (n : ℕ) (pre post : List Gate) (a b c d out : ℕ)
    (ha : a < n+pre.length) (hb : b < n+pre.length)
    (hc : c < n+pre.length) (hd : d < n+pre.length) (x : Fin n → Bool) :
    let w := pre.foldl step (List.ofFn x)
    gateVal n (oldCircuit n pre post a b c d out) pre.length x = (w.getD a false || w.getD b false) ∧
    gateVal n (newCircuit n pre post a b c d out) pre.length x = (w.getD a false && w.getD d false) := by
  let w := pre.foldl step (List.ofFn x)
  have hl : w.length = n+pre.length := by simp [w,foldl_step_length]
  change gateVal n (oldCircuit n pre post a b c d out) pre.length x = (w.getD a false || w.getD b false) ∧
    gateVal n (newCircuit n pre post a b c d out) pre.length x = (w.getD a false && w.getD d false)
  simp only [gateVal,newCircuit,oldCircuit,wires_eq,List.foldl_append]
  change (post.foldl step ((oldBlock (n+pre.length) a b c d).foldl step w)).getD (n+pre.length) false = _ ∧
    (post.foldl step ((newBlock (n+pre.length) a b c d).foldl step w)).getD (n+pre.length) false = _
  rw [←hl,old_run w a b c d (by omega) (by omega) (by omega) (by omega),
    new_run w a b c d (by omega) (by omega) (by omega) (by omega),
    foldl_step_getD post _ w.length (by simp),foldl_step_getD post _ w.length (by simp)]
  simp

lemma mass_lt (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (a b c d out : ℕ)
    (hAO : IsAO2 n (oldCircuit n pre post a b c d out))
    (ha : a < n+pre.length) (hb : b < n+pre.length)
    (hc : c < n+pre.length) (hd : d < n+pre.length)
    (hstrict : ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧
      let w := pre.foldl step (List.ofFn x)
      w.getD a false = true ∧ w.getD d false = false) :
    WireMass.mass G (newCircuit n pre post a b c d out) <
      WireMass.mass G (oldCircuit n pre post a b c d out) := by
  apply WireProfile.mass_lt_of_profile G _ _ id
  · intro j hj
    simpa [newCircuit,oldCircuit,newBlock,oldBlock] using hj
  · intro i hi j hj heq
    exact heq
  · intro x hx j hj hv
    exact wires_dom n pre post a b c d out hAO ha hb hc hd x (n+j) hv
  · obtain ⟨x,hx,hA,hD⟩ := hstrict
    refine ⟨x,hx,pre.length,by simp [newCircuit,newBlock],?_,?_⟩
    · change gateVal n (oldCircuit n pre post a b c d out) pre.length x = true
      rw [(first_values n pre post a b c d out ha hb hc hd x).1,hA]
      rfl
    · rw [(first_values n pre post a b c d out ha hb hc hd x).2,hD]
      simp

lemma no_wire_least (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (a b c d out : ℕ)
    (hLeast : WireFirst.IsWireLeast G (oldCircuit n pre post a b c d out))
    (ha : a < n+pre.length) (hb : b < n+pre.length)
    (hc : c < n+pre.length) (hd : d < n+pre.length)
    (hprivate : ∀ g ∈ post, ∀ i ∈ g.inputs, i ≠ n+pre.length ∧ i ≠ n+pre.length+1)
    (ho1 : out ≠ n+pre.length) (ho2 : out ≠ n+pre.length+1)
    (hedge : ∀ u v : Fin n, G.Adj u v →
      let w := pre.foldl step (List.ofFn (pairInput u v))
      ((w.getD a false && w.getD d false)||(w.getD c false && w.getD b false)) =
        ((w.getD a false || w.getD b false)&&(w.getD c false || w.getD d false)))
    (hstrict : ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧
      let w := pre.foldl step (List.ofFn x)
      w.getD a false = true ∧ w.getD d false = false) : False := by
  exact WireFirst.no_strict_rewrite G _ _ hLeast
    (new_ao2 n pre post a b c d out hLeast.1.1 ha hb hc hd)
    (graph_correct n G pre post a b c d out hLeast.1.1 hLeast.1.2.1 ha hb hc hd
      hprivate ho1 ho2 hedge)
    (size_eq n pre post a b c d out).le
    (mass_lt n G pre post a b c d out hLeast.1.1 ha hb hc hd hstrict)

end PEqualNP.Outside.L_meta_3566.MixedShell


namespace PEqualNP.Outside.L_meta_3566.PruningTrace
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.Pruning
variable {n : ℕ} {ι : Type}

def Trace (P : Prog n ι) (v : ι → (Fin n → Bool) → Bool) (K : Finset ι)
    (gs : List Gate) : Prop :=
  ∃ f : Fin gs.length → ι, Function.Injective f ∧ (∀ r, f r ∈ K) ∧
    (∀ r : Fin gs.length, (gateAt ⟨gs, 0⟩ r.val).op = if P.isAnd (f r) then GateOp.and else GateOp.or) ∧
    ∀ (r : Fin gs.length) x, gateVal n ⟨gs, 0⟩ r.val x = v (f r) x

lemma trace_empty (P : Prog n ι) (v : ι → (Fin n → Bool) → Bool) (K : Finset ι) :
    Trace P v K [] := by
  refine ⟨Fin.elim0, ?_, ?_, ?_, ?_⟩ <;> intro r <;> exact Fin.elim0 r

lemma trace_mono (P : Prog n ι) (v : ι → (Fin n → Bool) → Bool)
    {K L : Finset ι} {gs : List Gate} (hKL : K ⊆ L) (h : Trace P v K gs) :
    Trace P v L gs := by
  obtain ⟨f, hf, hm, ho, hv⟩ := h
  exact ⟨f, hf, fun r => hKL (hm r), ho, hv⟩

lemma trace_snoc [DecidableEq ι] (P : Prog n ι) (v : ι → (Fin n → Bool) → Bool)
    (K : Finset ι) (a : ι) (ha : a ∉ K) (gs : List Gate) (g : Gate)
    (h : Trace P v K gs)
    (hop : g.op = if P.isAnd a then GateOp.and else GateOp.or)
    (hval : ∀ x, gateVal n ⟨gs ++ [g], 0⟩ gs.length x = v a x) :
    Trace P v (insert a K) (gs ++ [g]) := by
  classical
  obtain ⟨f, hf, hm, ho, hv⟩ := h
  let f' : Fin (gs ++ [g]).length → ι := fun r =>
    if hr : r.val < gs.length then f ⟨r.val, hr⟩ else a
  have hlast (r : Fin (gs ++ [g]).length) (hr : ¬ r.val < gs.length) : r.val = gs.length := by
    have := r.isLt
    simp only [List.length_append, List.length_singleton] at this
    omega
  refine ⟨f', ?_, ?_, ?_, ?_⟩
  · intro r q he
    by_cases hr : r.val < gs.length <;> by_cases hq : q.val < gs.length
    · have he' : f ⟨r.val, hr⟩ = f ⟨q.val, hq⟩ := by simpa [f', hr, hq] using he
      have := congrArg Fin.val (hf he')
      exact Fin.ext this
    · have he' : f ⟨r.val, hr⟩ = a := by simpa [f', hr, hq] using he
      exact False.elim (ha (he' ▸ hm ⟨r.val, hr⟩))
    · have he' : a = f ⟨q.val, hq⟩ := by simpa [f', hr, hq] using he
      exact False.elim (ha (he' ▸ hm ⟨q.val, hq⟩))
    · exact Fin.ext ((hlast r hr).trans (hlast q hq).symm)
  · intro r
    by_cases hr : r.val < gs.length
    · simpa [f', hr] using Finset.mem_insert_of_mem (hm ⟨r.val, hr⟩)
    · simp [f', hr]
  · intro r
    by_cases hr : r.val < gs.length
    · have he : gateAt ⟨gs ++ [g], 0⟩ r.val = gateAt ⟨gs, 0⟩ r.val :=
        List.getD_append _ _ _ _ hr
      simpa only [he, f', dite_eq_left hr] using ho ⟨r.val, hr⟩
    · have he : gateAt ⟨gs ++ [g], 0⟩ r.val = g := by
        rw [hlast r hr]
        simp [gateAt]
      simpa only [he, f', dite_eq_right hr] using hop
  · intro r x
    by_cases hr : r.val < gs.length
    · change wireVal n ⟨gs ++ [g], 0⟩ (n + r.val) x = _
      rw [wireVal_old gs g (n + r.val) (by omega) x]
      simpa only [f', dite_eq_left hr, gateVal, wireVal] using hv ⟨r.val, hr⟩ x
    · simpa only [f', dite_eq_right hr, hlast r hr] using hval x

lemma build_with_trace (P : Prog n ι) (rank : ι → ℕ) (v : ι → (Fin n → Bool) → Bool) (K : Finset ι)
    (hcl : Closed P rank K) (hv : Sol P K v) :
    ∃ gs : List Gate, IsAO2 n ⟨gs, 0⟩ ∧ gs.length ≤ (kept P v K).card ∧ (∀ i ∈ K, Res gs (v i)) ∧ Trace P v K gs := by
  classical
  induction K using Finset.induction_on_max_value rank with
  | empty =>
    refine ⟨[], ⟨?_, ?_, ?_⟩, by simp, (fun i hi => absurd hi (Finset.notMem_empty i)), trace_empty P v ∅⟩
    · intro g hg; simp at hg
    · intro j hj; simp at hj
    · intro g hg; simp at hg
  | insert a s ha hmax ih =>
    have hs : Closed P rank s := by
      intro i hi b j hj
      obtain ⟨h1, h2⟩ := hcl i (Finset.mem_insert_of_mem hi) b j hj
      refine ⟨(Finset.mem_insert.1 h1).resolve_left ?_, h2⟩
      rintro rfl
      exact absurd (hmax i hi) (by omega)
    obtain ⟨gs, hAO, hlen, hres, htrace⟩ := ih hs fun x i hi => hv x i (Finset.mem_insert_of_mem hi)
    have hsrc' : ∀ b : Fin 2, Res gs (fun x => srcAt x (fun j => v j x) (P.src a b)) := by
      intro b
      rcases hb : P.src a b with _ | (c | j)
      · exact Or.inl fun x => rfl
      · exact Or.inr ⟨rfl, c, by have := c.2; omega, fun x => wireVal_input gs c x⟩
      · obtain ⟨h1, h2⟩ := hcl a (Finset.mem_insert_self a s) b j hb
        refine hres j ((Finset.mem_insert.1 h1).resolve_left ?_)
        rintro rfl
        exact absurd h2 (lt_irrefl _)
    have hsrc : ∀ b : Fin 2, (∀ x, srcAt x (fun j => v j x) (P.src a b) = false) ∨
        (srcAt (fun _ => true) (fun j => v j fun _ => true) (P.src a b) = true ∧ ∃ w < n + gs.length,
          ∀ x, wireVal n ⟨gs, 0⟩ w x = srcAt x (fun j => v j x) (P.src a b)) := hsrc'
    have hva : ∀ x, v a x = opv (P.isAnd a) (srcAt x (fun j => v j x) (P.src a 0))
        (srcAt x (fun j => v j x) (P.src a 1)) := fun x => hv x a (Finset.mem_insert_self a s)
    have hsub : kept P v s ⊆ kept P v (insert a s) :=
      Finset.filter_subset_filter _ (Finset.subset_insert a s)
    have hlen' : gs.length ≤ (kept P v (insert a s)).card := hlen.trans (Finset.card_le_card hsub)
    have same : Res gs (v a) → ∃ gs : List Gate, IsAO2 n ⟨gs, 0⟩ ∧
        gs.length ≤ (kept P v (insert a s)).card ∧
        (∀ i ∈ insert a s, Res gs (v i)) ∧ Trace P v (insert a s) gs := by
      intro h
      refine ⟨gs, hAO, hlen', ?_, trace_mono P v (Finset.subset_insert a s) htrace⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · exact h
      · exact hres i hi'
    rcases hsrc 0 with h0 | ⟨h0, w0, hw0, hv0⟩
    · -- first operand constant false
      refine same ?_
      cases hop : P.isAnd a
      · rcases hsrc 1 with h1 | ⟨h1, w1, hw1, hv1⟩
        · exact Or.inl fun x => by rw [hva x, h0 x, h1 x, hop]; rfl
        · refine Or.inr ⟨by rw [hva, h0, h1, hop]; rfl, w1, hw1, fun x => ?_⟩
          rw [hv1 x, hva x, h0 x, hop]; simp [opv]
      · exact Or.inl fun x => by rw [hva x, h0 x, hop]; rfl
    · rcases hsrc 1 with h1 | ⟨h1, w1, hw1, hv1⟩
      · refine same ?_
        cases hop : P.isAnd a
        · refine Or.inr ⟨by rw [hva, h0, h1, hop]; rfl, w0, hw0, fun x => ?_⟩
          rw [hv0 x, hva x, h1 x, hop]; simp [opv]
        · exact Or.inl fun x => by rw [hva x, h1 x, hop]; simp [opv]
      · -- both operands kept: append a gate
        have hak : a ∈ kept P v (insert a s) :=
          Finset.mem_filter.2 ⟨Finset.mem_insert_self a s, h0, h1⟩
        have hcard : (kept P v s).card + 1 ≤ (kept P v (insert a s)).card := by
          have hnot : a ∉ kept P v s := fun h => ha (Finset.mem_filter.1 h).1
          rw [← Finset.card_insert_of_notMem hnot]
          exact Finset.card_le_card (Finset.insert_subset hak hsub)
        let o : GateOp := if P.isAnd a then GateOp.and else GateOp.or
        have ho : o = GateOp.and ∨ o = GateOp.or := by
          by_cases h : P.isAnd a = true <;> simp [o, h]
        have hnew : ∀ x, gateVal n ⟨gs ++ [⟨o, [w0, w1]⟩], 0⟩ gs.length x = v a x := by
          intro x
          change wireVal n ⟨gs ++ [⟨o, [w0, w1]⟩], 0⟩ (n + gs.length) x = _
          rw [wireVal_new, hva x]
          simp only [List.map_cons, List.map_nil, hv0 x, hv1 x]
          by_cases h : P.isAnd a = true <;> simp [o, h, opv, GateOp.eval]
        refine ⟨gs ++ [⟨o, [w0, w1]⟩], isAO2_snoc gs o ho w0 w1 hw0 hw1 hAO, ?_, ?_,
          trace_snoc P v s a ha gs ⟨o, [w0, w1]⟩ htrace rfl hnew⟩
        · simp only [List.length_append, List.length_singleton]; omega
        · intro i hi
          rcases Finset.mem_insert.1 hi with rfl | hi'
          · refine Or.inr ⟨?_, n + gs.length, by simp, fun x => ?_⟩
            · rw [hva]
              simp only at h0 h1
              rw [h0, h1]
              cases P.isAnd i <;> rfl
            · rw [wireVal_new, hva x]
              simp only [List.map_cons, List.map_nil, hv0 x, hv1 x]
              by_cases h : P.isAnd i = true
              · simp [o, h, opv, GateOp.eval]
              · simp [o, h, opv, GateOp.eval]
          · exact res_mono gs _ _ (hres i hi')

lemma fold_total_with_trace (P : Prog n ι) (rank : ι → ℕ)
    (v : ι → (Fin n → Bool) → Bool) (K : Finset ι)
    (hcl : Closed P rank K) (hv : Sol P K v) (o : Src n ι)
    (ho : ∀ j, o = some (Sum.inr j) → j ∈ K) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ (kept P v K).card ∧
      (∀ x : Fin n → Bool, circuitFun n D x = srcAt x (fun j => v j x) o) ∧
      Trace P v K D.gates := by
  obtain ⟨gs, hAO, hlen, hres, htrace⟩ := build_with_trace P rank v K hcl hv
  have hR : Res gs (fun x => srcAt x (fun j => v j x) o) := by
    rcases o with _ | (c | j)
    · exact Or.inl fun x => rfl
    · exact Or.inr ⟨rfl, c, by have := c.2; omega, fun x => wireVal_input gs c x⟩
    · exact hres j (ho j rfl)
  rcases hR with h | ⟨_, w, _, hw⟩
  · refine ⟨⟨[], n⟩, zero_ao n, Nat.zero_le _, ?_, trace_empty P v K⟩
    intro x
    rw [zero_fun]
    exact (h x).symm
  · refine ⟨⟨gs, w⟩, ⟨hAO.1, hAO.2.1, hAO.2.2⟩, hlen, (fun x => hw x), htrace⟩

lemma prune_closed_with_embedding (C : Circuit) (hC : IsAO2 n C) (K : Finset ℕ)
    (hK : ∀ k ∈ K, k < C.gates.length)
    (hcl : ∀ k ∈ K, ∀ w ∈ (gateAt C k).inputs, n ≤ w → w - n ∈ K)
    (ho : ∀ j, srcOf n C.output = some (Sum.inr j) → j ∈ K) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ K.card ∧ circuitFun n D = circuitFun n C ∧
      ∃ f : Fin D.size → Fin C.size, Function.Injective f ∧
        (∀ r, (f r).val ∈ K) ∧ ∀ r x, gateVal n D r.val x = gateVal n C (f r).val x := by
  let P : Prog n ℕ := progOf C fun k b => srcOf n (opnd C k b)
  let v : ℕ → (Fin n → Bool) → Bool := fun k x => gateVal n C k x
  have hback : ∀ k ∈ K, ∀ b : Fin 2, opnd C k b ∈ (gateAt C k).inputs := by
    intro k hk b
    have hm : gateAt C k ∈ C.gates := by
      exact List.mem_of_getElem? (show C.gates[k]? = some (gateAt C k) by
        simp [gateAt, List.getD_eq_getElem?_getD, hK k hk])
    have hlen := hC.2.2 _ hm
    have hb : b.val < (gateAt C k).inputs.length := by rw [hlen]; exact b.isLt
    exact List.mem_of_getElem? (show (gateAt C k).inputs[b.val]? = some (opnd C k b) by
      simp [opnd, List.getD_eq_getElem?_getD, hb])
  have hclosed : Closed P id K := by
    intro k hk b j hsrc
    change srcOf n (opnd C k b) = some (Sum.inr j) at hsrc
    have hw := srcOf_inr (opnd C k b) j hsrc
    have hlt := hC.2.1 k (hK k hk) (opnd C k b) (hback k hk b)
    refine ⟨?_, ?_⟩
    · have hmem := hcl k hk (opnd C k b) (hback k hk b) (by omega)
      simpa [hw] using hmem
    · simpa using (show j < k by omega)
  have hsol : Sol P K v := by
    intro x k hk
    change gateVal n C k x = opv (isA (gateAt C k).op)
      (srcAt x (fun j => gateVal n C j x) (srcOf n (opnd C k 0)))
      (srcAt x (fun j => gateVal n C j x) (srcOf n (opnd C k 1)))
    rw [srcAt_srcOf, srcAt_srcOf]
    exact gate_eq C hC k (hK k hk) x
  obtain ⟨D,hD,hsize,hfun,htrace⟩ := fold_total_with_trace P id v K hclosed hsol (srcOf n C.output) ho
  obtain ⟨f,hf,hm,_hop,hv⟩ := htrace
  let e : Fin D.size → Fin C.size := fun r => ⟨f r,hK _ (hm r)⟩
  refine ⟨D,hD,hsize.trans (Finset.card_filter_le K _),?_,e,?_,?_,?_⟩
  · funext x
    rw [hfun x]
    exact srcAt_srcOf C C.output x
  · intro r t hrt
    exact hf (congrArg Fin.val hrt)
  · exact hm
  · exact hv

lemma prune_complement_with_embedding (C : Circuit) (hC : IsAO2 n C) (J : Finset ℕ)
    (hJ : J ⊆ Finset.range C.size)
    (hcl : ∀ k < C.size, k ∉ J → ∀ w ∈ (gateAt C k).inputs,
      n ≤ w → w-n ∉ J)
    (ho : C.output < n+C.size) (hjout : n ≤ C.output → C.output-n ∉ J) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + J.card ≤ C.size ∧ circuitFun n D = circuitFun n C ∧
      ∃ f : Fin D.size → Fin C.size, Function.Injective f ∧
        (∀ r, (f r).val ∉ J) ∧ ∀ r x, gateVal n D r.val x = gateVal n C (f r).val x := by
  classical
  let K := Finset.range C.size \ J
  have hK : ∀ k ∈ K, k < C.gates.length := by
    intro k hk
    exact Finset.mem_range.mp (Finset.mem_sdiff.mp hk).1
  have hclosed : ∀ k ∈ K, ∀ w ∈ (gateAt C k).inputs, n ≤ w → w-n ∈ K := by
    intro k hk w hw hwn
    obtain ⟨hkr,hkj⟩ := Finset.mem_sdiff.mp hk
    have hkl := Finset.mem_range.mp hkr
    have hwl := hC.2.1 k hkl w hw
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega),hcl k hkl hkj w hw hwn⟩
  have hout : ∀ j, srcOf n C.output = some (Sum.inr j) → j ∈ K := by
    intro j hj
    have heq := srcOf_inr C.output j hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega),
      by simpa [heq] using hjout (by omega)⟩
  obtain ⟨D,hD,hs,hF,f,hf,hm,hv⟩ := prune_closed_with_embedding C hC K hK hclosed hout
  have hcard : K.card + J.card = C.size := by
    simpa [K] using Finset.card_sdiff_add_card_eq_card hJ
  exact ⟨D,hD,by omega,hF,f,hf,fun r => (Finset.mem_sdiff.mp (hm r)).2,hv⟩

end PEqualNP.Outside.L_meta_3566.PruningTrace


namespace PEqualNP.Outside.L_meta_3566.ShellSemantics
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def single {n : ℕ} (u : Fin n) : Fin n → Bool := fun w => decide (w = u)

def mask {n : ℕ} (color : Fin n → Bool) (side : Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun w => if color w = side then x w else false

def Pure {n : ℕ} (color : Fin n → Bool) (side : Bool)
    (f : (Fin n → Bool) → Bool) : Prop := ∀ x, f x = f (mask color side x)

def oldFun {n : ℕ} (A B C D : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Bool :=
  (A x || B x) && (C x || D x)

def projected {n : ℕ} (A B C D : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Bool :=
  (A x && D x) || (C x && B x)

lemma mask_pair {n : ℕ} (color : Fin n → Bool) (side : Bool) (u v : Fin n)
    (hu : color u = side) (hv : color v ≠ side) :
    mask color side (pairInput u v) = mask color side (single u) := by
  funext w
  by_cases hc : color w = side <;> by_cases hwu : w = u <;> by_cases hwv : w = v <;>
    simp_all [mask,pairInput,single]

lemma pair_swap {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp [pairInput,or_comm]

lemma pure_pair {n : ℕ} (color : Fin n → Bool) (side : Bool)
    (f : (Fin n → Bool) → Bool) (hf : Pure color side f)
    (u v : Fin n) (hu : color u = side) (hv : color v ≠ side) :
    f (pairInput u v) = f (single u) := by
  rw [hf (pairInput u v),mask_pair color side u v hu hv,←hf (single u)]

lemma projection_pair_ordered {n : ℕ} (color : Fin n → Bool)
    (A B C D : (Fin n → Bool) → Bool)
    (hA : Pure color false A) (hB : Pure color true B)
    (hC : Pure color false C) (hD : Pure color true D)
    (hzero : ∀ w, oldFun A B C D (single w) = false)
    (u v : Fin n) (hu : color u = false) (hv : color v = true) :
    projected A B C D (pairInput u v) = oldFun A B C D (pairInput u v) := by
  have hAu := pure_pair color false A hA u v hu (by simp [hv])
  have hCu := pure_pair color false C hC u v hu (by simp [hv])
  have hBv : B (pairInput u v) = B (single v) := by
    rw [pair_swap]
    exact pure_pair color true B hB v u hv (by simp [hu])
  have hDv : D (pairInput u v) = D (single v) := by
    rw [pair_swap]
    exact pure_pair color true D hD v u hv (by simp [hu])
  have hAC : (A (pairInput u v) && C (pairInput u v)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hac : A (pairInput u v) = true ∧ C (pairInput u v) = true := by simpa using h
    obtain ⟨ha,hc⟩ := hac
    have haz := hAu.symm.trans ha
    have hcz := hCu.symm.trans hc
    have hz := hzero u
    simp [oldFun,haz,hcz] at hz
  have hBD : (B (pairInput u v) && D (pairInput u v)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hbd : B (pairInput u v) = true ∧ D (pairInput u v) = true := by simpa using h
    obtain ⟨hb,hd⟩ := hbd
    have hbz := hBv.symm.trans hb
    have hdz := hDv.symm.trans hd
    have hz := hzero v
    simp [oldFun,hbz,hdz] at hz
  cases ha : A (pairInput u v) <;> cases hb : B (pairInput u v) <;>
    cases hc : C (pairInput u v) <;> cases hd : D (pairInput u v) <;>
    simp_all [projected,oldFun]

lemma projection_pair {n : ℕ} (color : Fin n → Bool)
    (A B C D : (Fin n → Bool) → Bool)
    (hA : Pure color false A) (hB : Pure color true B)
    (hC : Pure color false C) (hD : Pure color true D)
    (hzero : ∀ w, oldFun A B C D (single w) = false)
    (u v : Fin n) (huv : color u ≠ color v) :
    projected A B C D (pairInput u v) = oldFun A B C D (pairInput u v) := by
  cases hu : color u <;> cases hv : color v
  · exact (huv (hu.trans hv.symm)).elim
  · exact projection_pair_ordered color A B C D hA hB hC hD hzero u v hu hv
  · rw [pair_swap]
    exact projection_pair_ordered color A B C D hA hB hC hD hzero v u hv hu
  · exact (huv (hu.trans hv.symm)).elim

lemma singleton_negative {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : graphFun G ∅ (single u) = false := by
  simp [graphFun,single]

lemma pure_single_opposite {n : ℕ} (color : Fin n → Bool)
    (f : (Fin n → Bool) → Bool) (hf : Pure color true f)
    (hfzero : f (fun _ => false) = false) (u : Fin n) (hu : color u = false) :
    f (single u) = false := by
  have hm : mask color true (single u) = (fun _ => false) := by
    funext w
    by_cases hw : w = u <;> simp_all [mask,single]
  rw [hf,hm,hfzero]

lemma strict_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (A D : (Fin n → Bool) → Bool)
    (hD : Pure color true D) (hDzero : D (fun _ => false) = false)
    (u : Fin n) (hu : color u = false) (hAu : A (single u) = true) :
    ∃ x, graphFun G ∅ x = false ∧ A x = true ∧ D x = false :=
  ⟨single u,singleton_negative G u,hAu,pure_single_opposite color D hD hDzero u hu⟩

end PEqualNP.Outside.L_meta_3566.ShellSemantics


namespace PEqualNP.Outside.L_meta_3566.WireJunkMinimum
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

def IsWireJunkLeast {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  WireFirst.IsWireLeast G C ∧
    ∀ D, WireFirst.IsWireLeast G D → (junk G C).card ≤ (junk G D).card

lemma exists_wire_junk_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty) : ∃ C, IsWireJunkLeast G C := by
  classical
  obtain ⟨C,hC⟩ := WireFirst.exists_wire_least G hE
  have hex : ∃ j, ∃ D, WireFirst.IsWireLeast G D ∧ (junk G D).card = j :=
    ⟨(junk G C).card,C,hC,rfl⟩
  obtain ⟨D,hD,hJ⟩ := Nat.find_spec hex
  refine ⟨D,hD,?_⟩
  intro E hE
  rw [hJ]
  exact Nat.find_min' hex ⟨E,hE,rfl⟩

lemma junk_le_of_mass_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hC : IsWireJunkLeast G C)
    (hAO : IsAO2 n D) (hF : circuitFun n D = graphFun G ∅)
    (hsize : D.size ≤ C.size) (hW : WireMass.mass G D ≤ WireMass.mass G C) :
    (junk G C).card ≤ (junk G D).card := by
  have hD := (WireFirst.rewrite_le G C D hC.1 hAO hF hsize hW).2.2
  exact hC.2 D hD

lemma no_strict_junk_rewrite {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hC : IsWireJunkLeast G C)
    (hAO : IsAO2 n D) (hF : circuitFun n D = graphFun G ∅)
    (hsize : D.size ≤ C.size) (hW : WireMass.mass G D ≤ WireMass.mass G C)
    (hJ : (junk G D).card < (junk G C).card) : False := by
  have h := junk_le_of_mass_le G C D hC hAO hF hsize hW
  omega

lemma rewrite_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hC : IsWireJunkLeast G C)
    (hAO : IsAO2 n D) (hF : circuitFun n D = graphFun G ∅)
    (hsize : D.size ≤ C.size) (hW : WireMass.mass G D ≤ WireMass.mass G C)
    (hJ : (junk G D).card ≤ (junk G C).card) :
    D.size = C.size ∧ WireMass.mass G D = WireMass.mass G C ∧
      (junk G D).card = (junk G C).card ∧ IsWireJunkLeast G D := by
  obtain ⟨hs,hw,hD⟩ := WireFirst.rewrite_le G C D hC.1 hAO hF hsize hW
  have hj := Nat.le_antisymm hJ (hC.2 D hD)
  refine ⟨hs,hw,hj,hD,?_⟩
  intro E hE
  rw [hj]
  exact hC.2 E hE

end PEqualNP.Outside.L_meta_3566.WireJunkMinimum


namespace PEqualNP.Outside.L_meta_3566.ShellInsert
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_3566.HoistEval

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  exact List.mem_of_getElem? (show C.gates[j]? = some (gateAt C j) by
    simp [gateAt,List.getD_eq_getElem?_getD,hj])

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs.take j = pre ∧ gs.drop (j+1) = post ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j,gs.drop (j+1),gs[j]'hj,?_,by simp; omega,rfl,rfl,rfl⟩
  rw [List.cons_getElem_drop_succ,List.take_append_drop]

lemma step_getD_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_append_left w _ i hi

lemma step_getD_len (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) :=
  getD_append_singleton_last w _

lemma gate_wire_eval {n : ℕ} (C : Circuit) (hrb : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (C.wires (List.ofFn x)).getD i false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _, _, hgj⟩ := split_gates C.gates j hj
  have hw0_len : (pre.foldl step (List.ofFn x)).length = n + j := by
    rw [foldl_step_length, List.length_ofFn, hpre_len]
  have hgate : gateAt C j = gj := by
    simpa only [gateAt, List.getD_eq_getElem _ _ hj] using hgj
  have hpre : ∀ i, i < n + j →
      (C.wires (List.ofFn x)).getD i false =
        (pre.foldl step (List.ofFn x)).getD i false := by
    intro i hi
    rw [wires_eq, hgs, List.foldl_append, List.foldl_cons,
      foldl_step_getD _ _ _ (by simp [step, hw0_len]; omega),
      step_getD_lt _ _ _ (by omega)]
  have hm : (gateAt C j).inputs.map (fun i => (C.wires (List.ofFn x)).getD i false) =
      (gateAt C j).inputs.map (fun i => (pre.foldl step (List.ofFn x)).getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact hpre i (hrb j hj i hi)
  rw [hm, hgate, wires_eq, hgs, List.foldl_append, List.foldl_cons,
    foldl_step_getD _ _ _ (by simp [step, hw0_len])]
  rw [← hw0_len, step_getD_len]

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma value_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    value C x w = x ⟨w,hw⟩ := Pruning.wireVal_lt C w hw x

lemma value_missing {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n+C.gates.length ≤ w) : value C x w = false := by
  have hl : (C.wires (List.ofFn x)).length = n+C.gates.length := by
    rw [wires_eq,foldl_step_length,List.length_ofFn]
  simp [value,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : (C.wires (List.ofFn x)).length ≤ w)]

lemma value_gate {n : ℕ} (C : Circuit) (hR : ReadsBack n C) (x : Fin n → Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    value C x (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (value C x)) :=
  gate_wire_eval C hR j hj x

def move (m w : ℕ) : ℕ := if w < m then w else w + 2

def rename (m : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (move m)⟩

def position (h j : ℕ) : ℕ := if j < h then j else j + 2

def copy (w : ℕ) : Gate := ⟨.and, [w, w]⟩

def newGate (n : ℕ) (C : Circuit) (h : ℕ) (S : Finset ℕ)
    (g₀ g₁ g₂ : Gate) (k : ℕ) : Gate :=
  if k < h then rename (n + h) (gateAt C k)
  else if k = h then g₀
  else if k = h + 1 then g₁
  else if k = h + 2 then g₂
  else if k - 2 ∈ S then copy (n + h + 2)
  else rename (n + h) (gateAt C (k - 2))

def circuit (n : ℕ) (C : Circuit) (h : ℕ) (S : Finset ℕ)
    (g₀ g₁ g₂ : Gate) : Circuit :=
  ⟨List.ofFn (fun k : Fin (C.gates.length + 2) => newGate n C h S g₀ g₁ g₂ k),
    move (n + h) C.output⟩

lemma length (n : ℕ) (C : Circuit) (h : ℕ) (S : Finset ℕ) (g₀ g₁ g₂ : Gate) :
    (circuit n C h S g₀ g₁ g₂).gates.length = C.gates.length + 2 := by
  simp [circuit]

lemma size (n : ℕ) (C : Circuit) (h : ℕ) (S : Finset ℕ) (g₀ g₁ g₂ : Gate) :
    (circuit n C h S g₀ g₁ g₂).size = C.size + 2 := by
  simp [Circuit.size, length]

lemma gate (n : ℕ) (C : Circuit) (h : ℕ) (S : Finset ℕ) (g₀ g₁ g₂ : Gate)
    (k : ℕ) (hk : k < C.gates.length + 2) :
    gateAt (circuit n C h S g₀ g₁ g₂) k = newGate n C h S g₀ g₁ g₂ k := by
  change (List.ofFn (fun k : Fin (C.gates.length + 2) => newGate n C h S g₀ g₁ g₂ k)).getD k _ = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hk), List.getElem_ofFn]

lemma move_add (n h j : ℕ) : move (n + h) (n + j) = n + position h j := by
  simp only [move, position]
  split_ifs <;> omega

lemma move_lt (m b w : ℕ) (hw : w < b) : move m w < move m b := by
  unfold move
  split_ifs <;> omega

lemma move_input (n h w : ℕ) (hw : w < n) : move (n + h) w = w := by
  simp [move, show w < n + h by omega]

lemma at_lt (C : Circuit) (h j : ℕ) (hj : j < C.gates.length) :
    position h j < C.gates.length + 2 := by
  unfold position
  split_ifs <;> omega

lemma moved_gate (n : ℕ) (C : Circuit) (h : ℕ) (S : Finset ℕ) (g₀ g₁ g₂ : Gate)
    (hS : ∀ j ∈ S, h < j) (j : ℕ) (hj : j < C.gates.length) (hjh : j ≠ h) :
    gateAt (circuit n C h S g₀ g₁ g₂) (position h j) =
      if j ∈ S then copy (n + h + 2) else rename (n + h) (gateAt C j) := by
  rw [gate _ _ _ _ _ _ _ _ (at_lt C h j hj)]
  by_cases hjl : j < h
  · have hn : j ∉ S := fun hs => by have := hS j hs; omega
    simp [newGate, position, hjl, hn]
  · have hgt : h < j := by omega
    have h0 : ¬ j + 2 < h := by omega
    have h1 : j + 2 ≠ h := by omega
    have h2 : j + 2 ≠ h + 1 := by omega
    have h3 : j + 2 ≠ h + 2 := by omega
    simp [newGate, position, hjl, h0, h1, h2, hjh]

lemma newGate_ao {n : ℕ} (C : Circuit) (h : ℕ) (S : Finset ℕ) (g₀ g₁ g₂ : Gate)
    (hC : IsAO2 n C) (hh : h < C.gates.length)
    (hg₀ : (g₀.op = .and ∨ g₀.op = .or) ∧ g₀.inputs.length = 2 ∧
      ∀ w ∈ g₀.inputs, w < n + h)
    (hg₁ : (g₁.op = .and ∨ g₁.op = .or) ∧ g₁.inputs.length = 2 ∧
      ∀ w ∈ g₁.inputs, w < n + h + 1)
    (hg₂ : (g₂.op = .and ∨ g₂.op = .or) ∧ g₂.inputs.length = 2 ∧
      ∀ w ∈ g₂.inputs, w < n + h + 2)
    (k : ℕ) (hk : k < C.gates.length + 2) :
    ((newGate n C h S g₀ g₁ g₂ k).op = .and ∨
      (newGate n C h S g₀ g₁ g₂ k).op = .or) ∧
      (newGate n C h S g₀ g₁ g₂ k).inputs.length = 2 ∧
      ∀ w ∈ (newGate n C h S g₀ g₁ g₂ k).inputs, w < n + k := by
  unfold newGate
  split_ifs with h0 h1 h2 h3 h4
  · have hkc : k < C.gates.length := by omega
    refine ⟨by simpa only [rename] using hC.1 (gateAt C _) (gateAt_mem hkc), ?_, ?_⟩
    · simpa [rename] using hC.2.2 _ (gateAt_mem hkc)
    · intro w hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      have hu' := hC.2.1 k hkc u hu
      simp only [move, ite_eq_left (show u < n + h by omega)]
      omega
  · subst k
    exact hg₀
  · subst k
    simpa [Nat.add_assoc] using hg₁
  · subst k
    simpa [Nat.add_assoc] using hg₂
  · refine ⟨Or.inl rfl, by simp [copy], ?_⟩
    intro w hw
    have hw' : w = n + h + 2 := by simpa [copy] using hw
    omega
  · have hkc : k - 2 < C.gates.length := by omega
    refine ⟨by simpa only [rename] using hC.1 (gateAt C _) (gateAt_mem hkc), ?_, ?_⟩
    · simpa [rename] using hC.2.2 _ (gateAt_mem hkc)
    · intro w hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      have hu' := hC.2.1 (k - 2) hkc u hu
      unfold move
      split_ifs <;> omega

lemma ao {n : ℕ} (C : Circuit) (h : ℕ) (S : Finset ℕ) (g₀ g₁ g₂ : Gate)
    (hC : IsAO2 n C) (hh : h < C.gates.length)
    (hg₀ : (g₀.op = .and ∨ g₀.op = .or) ∧ g₀.inputs.length = 2 ∧
      ∀ w ∈ g₀.inputs, w < n + h)
    (hg₁ : (g₁.op = .and ∨ g₁.op = .or) ∧ g₁.inputs.length = 2 ∧
      ∀ w ∈ g₁.inputs, w < n + h + 1)
    (hg₂ : (g₂.op = .and ∨ g₂.op = .or) ∧ g₂.inputs.length = 2 ∧
      ∀ w ∈ g₂.inputs, w < n + h + 2) :
    IsAO2 n (circuit n C h S g₀ g₁ g₂) := by
  have hs := newGate_ao C h S g₀ g₁ g₂ hC hh hg₀ hg₁ hg₂
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact (hs k k.isLt).1
  · intro k hk w hw
    have hk' : k < C.gates.length + 2 := by simpa only [length] using hk
    rw [gate _ _ _ _ _ _ _ _ hk'] at hw
    exact (hs k hk').2.2 w hw
  · intro g hg
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact (hs k k.isLt).2.1

lemma preserve_prefix {n : ℕ} (C : Circuit) (h : ℕ) (S : Finset ℕ) (g₀ g₁ g₂ : Gate)
    (hC : ReadsBack n C) (hh : h < C.gates.length)
    (hD : ReadsBack n (circuit n C h S g₀ g₁ g₂)) (x : Fin n → Bool) :
    ∀ w, w < n + h → value (circuit n C h S g₀ g₁ g₂) x w = value C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [value_input (circuit n C h S g₀ g₁ g₂) x w hwn, value_input C x w hwn]
    · let j := w - n
      have hjh : j < h := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      have heq : n + j = w := by dsimp [j]; omega
      have hjD : j < (circuit n C h S g₀ g₁ g₂).gates.length := by rw [length]; omega
      rw [← heq, value_gate _ hD x j hjD, value_gate C hC x j hj,
        gate _ _ _ _ _ _ _ _ (by omega)]
      simp only [newGate, ite_eq_left hjh, rename, List.map_map, Function.comp_def]
      apply congrArg (gateAt C j).op.eval
      apply List.map_congr_left
      intro i hi
      have hil := hC j hj i hi
      have him : i < n + h := by omega
      simp only [move, ite_eq_left him]
      exact ih i (by omega) him

lemma gadget_gate₀ (n : ℕ) (C : Circuit) (h : ℕ) (S : Finset ℕ) (g₀ g₁ g₂ : Gate)
    (hh : h < C.gates.length) : gateAt (circuit n C h S g₀ g₁ g₂) h = g₀ := by
  rw [gate _ _ _ _ _ _ _ _ (by omega)]
  simp [newGate]

lemma gadget_gate₁ (n : ℕ) (C : Circuit) (h : ℕ) (S : Finset ℕ) (g₀ g₁ g₂ : Gate)
    (hh : h < C.gates.length) : gateAt (circuit n C h S g₀ g₁ g₂) (h + 1) = g₁ := by
  rw [gate _ _ _ _ _ _ _ _ (by omega)]
  simp [newGate, show ¬ h + 1 < h by omega]

lemma gadget_gate₂ (n : ℕ) (C : Circuit) (h : ℕ) (S : Finset ℕ) (g₀ g₁ g₂ : Gate)
    (hh : h < C.gates.length) : gateAt (circuit n C h S g₀ g₁ g₂) (h + 2) = g₂ := by
  rw [gate _ _ _ _ _ _ _ _ (by omega)]
  simp [newGate, show ¬ h + 2 < h by omega]

def star (u p : ℕ) : Gate := ⟨.and, [u, p]⟩

def join (n h : ℕ) : Gate := ⟨.or, [n + h, n + h + 1]⟩

def stars (n : ℕ) (C : Circuit) (h : ℕ) (S : Finset ℕ) (u p v q : ℕ) : Circuit :=
  circuit n C h S (star u p) (star v q) (join n h)

lemma stars_ao {n : ℕ} (C : Circuit) (h : ℕ) (S : Finset ℕ) (u p v q : ℕ)
    (hC : IsAO2 n C) (hh : h < C.gates.length)
    (hu : u < n + h) (hp : p < n + h) (hv : v < n + h) (hq : q < n + h) :
    IsAO2 n (stars n C h S u p v q) := by
  apply ao C h S (star u p) (star v q) (join n h) hC hh
  · refine ⟨Or.inl rfl, rfl, ?_⟩
    intro w hw
    simp only [star, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> assumption
  · refine ⟨Or.inl rfl, rfl, ?_⟩
    intro w hw
    simp only [star, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> omega
  · refine ⟨Or.inr rfl, rfl, ?_⟩
    intro w hw
    simp only [join, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> omega

lemma stars_value {n : ℕ} (C : Circuit) (h : ℕ) (S : Finset ℕ) (u p v q : ℕ)
    (hC : IsAO2 n C) (hh : h < C.gates.length)
    (hu : u < n + h) (hp : p < n + h) (hv : v < n + h) (hq : q < n + h)
    (x : Fin n → Bool) :
    value (stars n C h S u p v q) x (n + h + 2) =
      ((value C x u && value C x p) || (value C x v && value C x q)) := by
  let D := stars n C h S u p v q
  have hD := stars_ao C h S u p v q hC hh hu hp hv hq
  have hpre := preserve_prefix C h S (star u p) (star v q) (join n h) hC.2.1 hh hD.2.1 x
  change ∀ w, w < n + h → value D x w = value C x w at hpre
  have hlen : D.gates.length = C.gates.length + 2 := length _ _ _ _ _ _ _
  have hg₀ : gateAt D h = star u p := gadget_gate₀ n C h S (star u p) (star v q) (join n h) hh
  have hg₁ : gateAt D (h + 1) = star v q := gadget_gate₁ n C h S (star u p) (star v q) (join n h) hh
  have hg₂ : gateAt D (h + 2) = join n h := gadget_gate₂ n C h S (star u p) (star v q) (join n h) hh
  have he₀ : value D x (n + h) = (value C x u && value C x p) := by
    rw [value_gate D hD.2.1 x h (by omega), hg₀]
    simp only [star, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    rw [hpre u hu, hpre p hp]
  have he₁ : value D x (n + (h + 1)) = (value C x v && value C x q) := by
    rw [value_gate D hD.2.1 x (h + 1) (by omega), hg₁]
    simp only [star, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    rw [hpre v hv, hpre q hq]
  change value D x (n + h + 2) = _
  rw [show n + h + 2 = n + (h + 2) by omega,
    value_gate D hD.2.1 x (h + 2) (by omega), hg₂]
  simp only [join, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    id_eq, Bool.or_false]
  rw [he₀, show n + h + 1 = n + (h + 1) by omega, he₁]

lemma relation_root {n : ℕ} (C : Circuit) (h : ℕ) (g₀ g₁ g₂ : Gate)
    (hC : ReadsBack n C) (hh : h < C.gates.length)
    (hE : ReadsBack n (circuit n C h ∅ g₀ g₁ g₂))
    (x : Fin n → Bool) (R : Bool → Bool → Prop) (hr : ∀ b, R b b)
    (hmono : ∀ j, j < C.gates.length → ∀ f g : ℕ → Bool,
      (∀ i ∈ (gateAt C j).inputs, R (f i) (g i)) →
      R ((gateAt C j).op.eval ((gateAt C j).inputs.map f))
        ((gateAt C j).op.eval ((gateAt C j).inputs.map g)))
    (hroot : R (value C x (n+h)) (value (circuit n C h ∅ g₀ g₁ g₂) x (n+h+2))) :
    ∀ w, R (value C x w) (value (circuit n C h ∅ g₀ g₁ g₂) x (move (n+h) w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [move_input n h w hwn,value_input _ x w hwn,value_input _ x w hwn]
      exact hr _
    by_cases hwc : w < n+C.gates.length
    · let j := w-n
      have hj : j < C.gates.length := by dsimp [j]; omega
      have heq : n+j = w := by dsimp [j]; omega
      by_cases hjh : j = h
      · have hw : w = n+h := by omega
        rw [hw]
        simpa [move] using hroot
      · have hjE : position h j < (circuit n C h ∅ g₀ g₁ g₂).gates.length := by
          rw [length]
          exact at_lt C h j hj
        rw [←heq,move_add,value_gate _ hE x (position h j) hjE,
          moved_gate n C h ∅ g₀ g₁ g₂ (by simp) j hj hjh,value_gate C hC x j hj]
        simp only [Finset.notMem_empty,↓reduceIte,rename,List.map_map,Function.comp_def]
        apply hmono j hj
        intro i hi
        exact ih i (by have := hC j hj i hi; omega)
    · have hge : n+C.gates.length ≤ w := by omega
      have hgm : ¬w < n+h := by omega
      rw [value_missing C x w hge]
      simp only [move,ite_eq_right hgm]
      rw [value_missing _ x (w+2) (by rw [length]; omega)]
      exact hr false

lemma stars_operands {n : ℕ} (C : Circuit) (h : ℕ) (u p v q : ℕ)
    (hC : IsAO2 n C) (hh : h < C.gates.length)
    (hu : u < n+h) (hp : p < n+h) (hv : v < n+h) (hq : q < n+h) (x : Fin n → Bool) :
    value (stars n C h ∅ u p v q) x (n+h) = (value C x u && value C x p) ∧
    value (stars n C h ∅ u p v q) x (n+h+1) = (value C x v && value C x q) := by
  let E := stars n C h ∅ u p v q
  have hE := stars_ao C h ∅ u p v q hC hh hu hp hv hq
  have hpre := preserve_prefix C h ∅ (star u p) (star v q) (join n h) hC.2.1 hh hE.2.1 x
  change ∀ w, w < n+h → value E x w = value C x w at hpre
  have hlen : E.gates.length = C.gates.length+2 := length _ _ _ _ _ _ _
  have hg₀ : gateAt E h = star u p := gadget_gate₀ n C h ∅ _ _ _ hh
  have hg₁ : gateAt E (h+1) = star v q := gadget_gate₁ n C h ∅ _ _ _ hh
  constructor
  · change value E x (n+h) = _
    rw [value_gate E hE.2.1 x h (by omega),hg₀]
    simp only [star,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true]
    rw [hpre u hu,hpre p hp]
  · change value E x (n+h+1) = _
    rw [show n+h+1 = n+(h+1) by omega,value_gate E hE.2.1 x (h+1) (by omega),hg₁]
    simp only [star,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true]
    rw [hpre v hv,hpre q hq]

lemma old_values {n : ℕ} (C : Circuit) (h i j a b c d : ℕ)
    (hC : IsAO2 n C) (hh : h < C.gates.length) (hi : i < h) (hj : j < h)
    (hgi : gateAt C i = ⟨.or,[a,b]⟩) (hgj : gateAt C j = ⟨.or,[c,d]⟩)
    (hgh : gateAt C h = ⟨.and,[n+i,n+j]⟩) (x : Fin n → Bool) :
    value C x (n+i) = (value C x a || value C x b) ∧
    value C x (n+j) = (value C x c || value C x d) ∧
    value C x (n+h) = ((value C x a || value C x b)&&(value C x c || value C x d)) := by
  have hvi : value C x (n+i) = (value C x a || value C x b) := by
    rw [value_gate C hC.2.1 x i (by omega),hgi]
    simp [GateOp.eval]
  have hvj : value C x (n+j) = (value C x c || value C x d) := by
    rw [value_gate C hC.2.1 x j (by omega),hgj]
    simp [GateOp.eval]
  refine ⟨hvi,hvj,?_⟩
  rw [value_gate C hC.2.1 x h hh,hgh]
  simp [GateOp.eval,hvi,hvj]

lemma gate_dom_on (g : Gate) (hAO : g.op = .and ∨ g.op = .or) (f q : ℕ → Bool)
    (hfq : ∀ i ∈ g.inputs, q i = true → f i = true) :
    g.op.eval (g.inputs.map q) = true → g.op.eval (g.inputs.map f) = true := by
  rcases hAO with ho | ho <;> rw [ho]
  · simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    intro hq i hi
    exact hfq i hi (hq i hi)
  · simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨i,hi,hq⟩
    exact ⟨i,hi,hfq i hi hq⟩

lemma projection_dom {n : ℕ} (C : Circuit) (h i j a b c d : ℕ)
    (hC : IsAO2 n C) (hh : h < C.gates.length) (hi : i < h) (hj : j < h)
    (hgi : gateAt C i = ⟨.or,[a,b]⟩) (hgj : gateAt C j = ⟨.or,[c,d]⟩)
    (hgh : gateAt C h = ⟨.and,[n+i,n+j]⟩)
    (ha : a < n+h) (hb : b < n+h) (hc : c < n+h) (hd : d < n+h) (x : Fin n → Bool) :
    ∀ w, value (stars n C h ∅ a d c b) x (move (n+h) w) = true → value C x w = true := by
  apply relation_root C h (star a d) (star c b) (join n h) hC.2.1 hh
    (stars_ao C h ∅ a d c b hC hh ha hd hc hb).2.1 x (fun old new => new = true → old = true)
    (fun _ ht => ht)
  · intro k hk f q hfq
    exact gate_dom_on _ (hC.1 _ (gateAt_mem hk)) f q hfq
  · change value (stars n C h ∅ a d c b) x (n+h+2) = true → value C x (n+h) = true
    rw [stars_value C h ∅ a d c b hC hh ha hd hc hb x,(old_values C h i j a b c d hC hh hi hj hgi hgj hgh x).2.2]
    cases value C x a <;> cases value C x b <;> cases value C x c <;> cases value C x d <;> simp

lemma projection_eq_on {n : ℕ} (C : Circuit) (h a b c d : ℕ)
    (hC : IsAO2 n C) (hh : h < C.gates.length)
    (ha : a < n+h) (hb : b < n+h) (hc : c < n+h) (hd : d < n+h) (x : Fin n → Bool)
    (hQ : ((value C x a && value C x d)||(value C x c && value C x b)) = value C x (n+h)) :
    ∀ w, value (stars n C h ∅ a d c b) x (move (n+h) w) = value C x w := by
  apply relation_root C h (star a d) (star c b) (join n h) hC.2.1 hh
    (stars_ao C h ∅ a d c b hC hh ha hd hc hb).2.1 x (fun old new => new = old) (fun _ => rfl)
  · intro k hk f q hfq
    congr 1
    exact List.map_congr_left hfq
  · change value (stars n C h ∅ a d c b) x (n+h+2) = value C x (n+h)
    rw [stars_value C h ∅ a d c b hC hh ha hd hc hb x]
    exact hQ

lemma projection_graph_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h i j a b c d : ℕ)
    (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hh : h < C.gates.length) (hi : i < h) (hj : j < h)
    (hgi : gateAt C i = ⟨.or,[a,b]⟩) (hgj : gateAt C j = ⟨.or,[c,d]⟩)
    (hgh : gateAt C h = ⟨.and,[n+i,n+j]⟩)
    (ha : a < n+h) (hb : b < n+h) (hc : c < n+h) (hd : d < n+h)
    (hedge : ∀ u v : Fin n, G.Adj u v →
      ((value C (pairInput u v) a && value C (pairInput u v) d)||
        (value C (pairInput u v) c && value C (pairInput u v) b)) = value C (pairInput u v) (n+h)) :
    circuitFun n (stars n C h ∅ a d c b) = graphFun G ∅ := by
  have hE := stars_ao C h ∅ a d c b hC hh ha hd hc hb
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    have hroot := projection_dom C h i j a b c d hC hh hi hj hgi hgj hgh ha hb hc hd x C.output hx
    change circuitFun n C x = true at hroot
    rw [hfun] at hroot
    exact hroot
  · intro hx
    have hEdge : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by simpa [graphFun] using hx
    obtain ⟨u,v,huv,hu,hv⟩ := hEdge
    have hpC : circuitFun n C (pairInput u v) = true := by
      rw [hfun]
      have hp : ∃ z t, G.Adj z t ∧ pairInput u v z = true ∧ pairInput u v t = true :=
        ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩
      simpa [graphFun] using hp
    have hpE : circuitFun n (stars n C h ∅ a d c b) (pairInput u v) = true :=
      (projection_eq_on C h a b c d hC hh ha hb hc hd (pairInput u v) (hedge u v huv) C.output).trans hpC
    apply MixedShell.circuit_mono n _ hE.1 (pairInput u v) x _ hpE
    intro z hz
    simp only [pairInput,decide_eq_true_eq] at hz
    rcases hz with rfl | rfl
    · exact hu
    · exact hv

def charge (h i j r : ℕ) : ℕ :=
  if r = h then i else if r = h+1 then j else if r < h then r else r-2

lemma charge_lt (C : Circuit) (h i j r : ℕ) (hh : h < C.gates.length)
    (hi : i < h) (hj : j < h) (hr : r < C.gates.length+2) : charge h i j r < C.gates.length := by
  unfold charge
  split_ifs <;> omega

lemma charge_inj (h i j r s : ℕ) (hi : i < h) (hj : j < h) (hij : i ≠ j)
    (hri : r ≠ i) (hrj : r ≠ j) (hsi : s ≠ i) (hsj : s ≠ j)
    (heq : charge h i j r = charge h i j s) : r = s := by
  unfold charge at heq
  split_ifs at heq <;> omega

lemma charge_eq_i (h i j r : ℕ) (hi : i < h) (hj : j < h) (hij : i ≠ j)
    (hri : r ≠ i) (hrj : r ≠ j) (heq : charge h i j r = i) : r = h := by
  unfold charge at heq
  split_ifs at heq <;> omega

lemma charge_position (h i j r : ℕ) (hr : r ≠ h) (hr1 : r ≠ h+1) :
    position h (charge h i j r) = r := by
  unfold charge position
  split_ifs <;> omega

lemma charge_dom {n : ℕ} (C : Circuit) (h i j a b c d r : ℕ)
    (hC : IsAO2 n C) (hh : h < C.gates.length) (hi : i < h) (hj : j < h)
    (hgi : gateAt C i = ⟨.or,[a,b]⟩) (hgj : gateAt C j = ⟨.or,[c,d]⟩)
    (hgh : gateAt C h = ⟨.and,[n+i,n+j]⟩)
    (ha : a < n+h) (hb : b < n+h) (hc : c < n+h) (hd : d < n+h) (x : Fin n → Bool) :
    gateVal n (stars n C h ∅ a d c b) r x = true → gateVal n C (charge h i j r) x = true := by
  by_cases hr : r = h
  · subst r
    change value (stars n C h ∅ a d c b) x (n+h) = true → value C x (n+charge h i j h) = true
    rw [(stars_operands C h a d c b hC hh ha hd hc hb x).1]
    simp only [charge,↓reduceIte]
    rw [(old_values C h i j a b c d hC hh hi hj hgi hgj hgh x).1]
    simp only [Bool.and_eq_true,Bool.or_eq_true]
    exact fun hx => Or.inl hx.1
  · by_cases hr1 : r = h+1
    · subst r
      change value (stars n C h ∅ a d c b) x (n+(h+1)) = true → value C x (n+charge h i j (h+1)) = true
      rw [show n+(h+1) = n+h+1 by omega,(stars_operands C h a d c b hC hh ha hd hc hb x).2]
      simp only [charge,show h+1 ≠ h by omega,↓reduceIte]
      rw [(old_values C h i j a b c d hC hh hi hj hgi hgj hgh x).2.1]
      simp only [Bool.and_eq_true,Bool.or_eq_true]
      exact fun hx => Or.inl hx.1
    · have heq := charge_position h i j r hr hr1
      have hx := projection_dom C h i j a b c d hC hh hi hj hgi hgj hgh ha hb hc hd x (n+charge h i j r)
      rw [move_add,heq] at hx
      exact hx

lemma move_ne_low (m w z : ℕ) (hz : z < m) (hw : w ≠ z) : move m w ≠ z := by
  unfold move
  split_ifs <;> omega

lemma projection_private_dead {n : ℕ} (C : Circuit) (h i j a b c d : ℕ)
    (hh : h < C.gates.length) (hi : i < h) (hj : j < h)
    (hgi : gateAt C i = ⟨.or,[a,b]⟩) (hgj : gateAt C j = ⟨.or,[c,d]⟩)
    (hprivate : ∀ k < C.gates.length, k ≠ h →
      n+i ∉ (gateAt C k).inputs ∧ n+j ∉ (gateAt C k).inputs) :
    ∀ r < (stars n C h ∅ a d c b).gates.length, ∀ w ∈ (gateAt (stars n C h ∅ a d c b) r).inputs,
      w ≠ n+i ∧ w ≠ n+j := by
  have hp (z : ℕ) (hz : z ∈ [a,b,c,d]) : z ≠ n+i ∧ z ≠ n+j := by
    have hpi := hprivate i (by omega) (by omega)
    have hpj := hprivate j (by omega) (by omega)
    rw [hgi] at hpi
    rw [hgj] at hpj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz hpi hpj
    aesop
  have hrename (k : ℕ) (hk : k < C.gates.length) (hkh : k ≠ h) :
      ∀ w ∈ (rename (n+h) (gateAt C k)).inputs, w ≠ n+i ∧ w ≠ n+j := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
    have hpr := hprivate k hk hkh
    exact ⟨move_ne_low _ _ _ (by omega) (fun heq => hpr.1 (heq ▸ hz)),
      move_ne_low _ _ _ (by omega) (fun heq => hpr.2 (heq ▸ hz))⟩
  intro r hr w hw
  have hr' : r < C.gates.length+2 := by simpa only [stars,length] using hr
  change w ∈ (gateAt (circuit n C h ∅ (star a d) (star c b) (join n h)) r).inputs at hw
  rw [gate _ _ _ _ _ _ _ _ hr'] at hw
  simp only [newGate,Finset.notMem_empty,↓reduceIte] at hw
  split_ifs at hw with h0 h1 h2 h3
  · exact hrename r (by omega) (by omega) w hw
  · simp only [star,List.mem_cons,List.not_mem_nil,or_false] at hw
    apply hp
    rcases hw with rfl | rfl <;> simp
  · simp only [star,List.mem_cons,List.not_mem_nil,or_false] at hw
    apply hp
    rcases hw with rfl | rfl <;> simp
  · simp only [join,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl <;> constructor <;> omega
  · exact hrename (r-2) (by omega) (by omega) w hw

lemma prune_projection {n : ℕ} (C : Circuit) (h i j a b c d : ℕ)
    (hC : IsAO2 n C) (hh : h < C.gates.length) (hi : i < h) (hj : j < h) (hij : i ≠ j)
    (hgi : gateAt C i = ⟨.or,[a,b]⟩) (hgj : gateAt C j = ⟨.or,[c,d]⟩)
    (ha : a < n+h) (hb : b < n+h) (hc : c < n+h) (hd : d < n+h)
    (hprivate : ∀ k < C.gates.length, k ≠ h →
      n+i ∉ (gateAt C k).inputs ∧ n+j ∉ (gateAt C k).inputs)
    (hout : C.output < n+C.size) (hoi : C.output ≠ n+i) (hoj : C.output ≠ n+j) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
      circuitFun n D = circuitFun n (stars n C h ∅ a d c b) ∧
      ∃ f : Fin D.size → Fin (stars n C h ∅ a d c b).size, Function.Injective f ∧
        (∀ r, (f r).val ≠ i ∧ (f r).val ≠ j) ∧
        ∀ r x, gateVal n D r.val x = gateVal n (stars n C h ∅ a d c b) (f r).val x := by
  classical
  let E := stars n C h ∅ a d c b
  have hE : IsAO2 n E := stars_ao C h ∅ a d c b hC hh ha hd hc hb
  have hlen : E.size = C.size+2 := size _ _ _ _ _ _ _
  have hdead := projection_private_dead C h i j a b c d hh hi hj hgi hgj hprivate
  have hJ : ({i,j} : Finset ℕ) ⊆ Finset.range E.size := by
    intro r hr
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    rw [Finset.mem_range]
    rcases hr with rfl | rfl <;> change _ < E.gates.length <;> simpa [E,stars,length] using (show _ < C.gates.length+2 by omega)
  have hclosed : ∀ r < E.size, r ∉ ({i,j} : Finset ℕ) →
      ∀ w ∈ (gateAt E r).inputs, n ≤ w → w-n ∉ ({i,j} : Finset ℕ) := by
    intro r hr _ w hw hn hm
    have hdw := hdead r hr w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact hdw.1 (by omega)
    · exact hdw.2 (by omega)
  have ho : E.output < n+E.size := by
    change move (n+h) C.output < n+E.size
    unfold move
    split_ifs <;> omega
  have hjo : n ≤ E.output → E.output-n ∉ ({i,j} : Finset ℕ) := by
    intro hn hm
    have hni : E.output ≠ n+i := move_ne_low _ _ _ (by omega) hoi
    have hnj : E.output ≠ n+j := move_ne_low _ _ _ (by omega) hoj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact hni (by omega)
    · exact hnj (by omega)
  obtain ⟨D,hD,hs,hF,f,hf,havoid,hval⟩ :=
    PruningTrace.prune_complement_with_embedding E hE {i,j} hJ hclosed ho hjo
  have hcard : ({i,j} : Finset ℕ).card = 2 := by simp [hij]
  refine ⟨D,hD,by omega,hF,f,hf,?_,hval⟩
  intro r
  simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using havoid r

lemma pruned_mass_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (h i j a b c d : ℕ)
    (hC : IsAO2 n C) (hh : h < C.gates.length) (hi : i < h) (hj : j < h) (hij : i ≠ j)
    (hgi : gateAt C i = ⟨.or,[a,b]⟩) (hgj : gateAt C j = ⟨.or,[c,d]⟩)
    (hgh : gateAt C h = ⟨.and,[n+i,n+j]⟩)
    (ha : a < n+h) (hb : b < n+h) (hc : c < n+h) (hd : d < n+h)
    (f : Fin D.size → Fin (stars n C h ∅ a d c b).size) (hf : Function.Injective f)
    (havoid : ∀ r, (f r).val ≠ i ∧ (f r).val ≠ j)
    (hval : ∀ r x, gateVal n D r.val x = gateVal n (stars n C h ∅ a d c b) (f r).val x)
    (hstrict : ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧ value C x a = true ∧ value C x d = false) :
    WireMass.mass G D < WireMass.mass G C := by
  let e : ℕ → ℕ := fun r => if hr : r < D.size then charge h i j (f ⟨r,hr⟩).val else 0
  have he (r : ℕ) (hr : r < D.size) : e r = charge h i j (f ⟨r,hr⟩).val := by simp [e,hr]
  apply WireProfile.mass_lt_of_injective G C D e
  · intro r hr
    rw [he r hr]
    apply charge_lt C h i j _ hh hi hj
    simpa only [stars,Circuit.size,length] using (f ⟨r,hr⟩).isLt
  · intro r hr s hs hrs
    have hr' : r < D.size := Finset.mem_range.mp hr
    have hs' : s < D.size := Finset.mem_range.mp hs
    rw [he r hr',he s hs'] at hrs
    have hev := charge_inj h i j _ _ hi hj hij (havoid ⟨r,hr'⟩).1 (havoid ⟨r,hr'⟩).2
      (havoid ⟨s,hs'⟩).1 (havoid ⟨s,hs'⟩).2 hrs
    exact congrArg Fin.val (hf (Fin.ext hev))
  · intro x hx r hr hv
    rw [he r hr]
    have hv' : gateVal n (stars n C h ∅ a d c b) (f ⟨r,hr⟩).val x = true :=
      (hval ⟨r,hr⟩ x).symm.trans hv
    exact charge_dom C h i j a b c d _ hC hh hi hj hgi hgj hgh ha hb hc hd x hv'
  · obtain ⟨x,hx,hA,hD⟩ := hstrict
    refine ⟨x,hx,i,by omega,?_,?_⟩
    · change value C x (n+i) = true
      rw [(old_values C h i j a b c d hC hh hi hj hgi hgj hgh x).1,hA]
      rfl
    · intro r hr her
      rw [he r hr] at her
      have hfr := charge_eq_i h i j _ hi hj hij (havoid ⟨r,hr⟩).1 (havoid ⟨r,hr⟩).2 her
      rw [hval ⟨r,hr⟩ x,hfr]
      change value (stars n C h ∅ a d c b) x (n+h) = false
      rw [(stars_operands C h a d c b hC hh ha hd hc hb x).1,hD]
      simp

lemma exists_projection {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h i j a b c d : ℕ)
    (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hh : h < C.gates.length) (hi : i < h) (hj : j < h) (hij : i ≠ j)
    (hgi : gateAt C i = ⟨.or,[a,b]⟩) (hgj : gateAt C j = ⟨.or,[c,d]⟩)
    (hgh : gateAt C h = ⟨.and,[n+i,n+j]⟩)
    (ha : a < n+h) (hb : b < n+h) (hc : c < n+h) (hd : d < n+h)
    (hprivate : ∀ k < C.gates.length, k ≠ h →
      n+i ∉ (gateAt C k).inputs ∧ n+j ∉ (gateAt C k).inputs)
    (hout : C.output < n+C.size) (hoi : C.output ≠ n+i) (hoj : C.output ≠ n+j)
    (hedge : ∀ u v : Fin n, G.Adj u v →
      ((value C (pairInput u v) a && value C (pairInput u v) d)||
        (value C (pairInput u v) c && value C (pairInput u v) b)) = value C (pairInput u v) (n+h))
    (hstrict : ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧ value C x a = true ∧ value C x d = false) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      WireMass.mass G D < WireMass.mass G C := by
  obtain ⟨D,hD,hs,hF,f,hf,havoid,hval⟩ :=
    prune_projection C h i j a b c d hC hh hi hj hij hgi hgj ha hb hc hd hprivate hout hoi hoj
  refine ⟨D,hD,hF.trans ?_,hs,?_⟩
  · exact projection_graph_correct G C h i j a b c d hC hfun hh hi hj hgi hgj hgh ha hb hc hd hedge
  · exact pruned_mass_lt G C D h i j a b c d hC hh hi hj hij hgi hgj hgh ha hb hc hd f hf havoid hval hstrict

lemma no_wire_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : WireFirst.IsWireLeast G C) (h i j a b c d : ℕ)
    (hh : h < C.gates.length) (hi : i < h) (hj : j < h) (hij : i ≠ j)
    (hgi : gateAt C i = ⟨.or,[a,b]⟩) (hgj : gateAt C j = ⟨.or,[c,d]⟩)
    (hgh : gateAt C h = ⟨.and,[n+i,n+j]⟩)
    (ha : a < n+h) (hb : b < n+h) (hc : c < n+h) (hd : d < n+h)
    (hprivate : ∀ k < C.gates.length, k ≠ h →
      n+i ∉ (gateAt C k).inputs ∧ n+j ∉ (gateAt C k).inputs)
    (hout : C.output < n+C.size) (hoi : C.output ≠ n+i) (hoj : C.output ≠ n+j)
    (hedge : ∀ u v : Fin n, G.Adj u v →
      ((value C (pairInput u v) a && value C (pairInput u v) d)||
        (value C (pairInput u v) c && value C (pairInput u v) b)) = value C (pairInput u v) (n+h))
    (hstrict : ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧ value C x a = true ∧ value C x d = false) : False := by
  obtain ⟨D,hD,hF,hs,hm⟩ := exists_projection G C h i j a b c d hLeast.1.1 hLeast.1.2.1
    hh hi hj hij hgi hgj hgh ha hb hc hd hprivate hout hoi hoj hedge hstrict
  exact WireFirst.no_strict_rewrite G C D hLeast hD hF hs hm

end PEqualNP.Outside.L_meta_3566.ShellInsert


namespace PEqualNP.Outside.L_meta_3566.ZeroWires
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.HoistEval

lemma step_false (g : Gate) (hAO : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h2 : g.inputs.length = 2) (w : List Bool) (hw : ∀ i, w.getD i false = false) :
    ∀ i, (step w g).getD i false = false := by
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp h2
  have hg : g.op.eval (g.inputs.map fun i => w.getD i false) = false := by
    rw [hab]
    simp only [List.map_cons,List.map_nil,hw]
    rcases hAO with hop | hop <;> simp [hop,GateOp.eval]
  intro i
  change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false = false
  rw [hg]
  by_cases hi : i < w.length
  · rw [getD_append_left _ _ _ hi]
    exact hw i
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    cases i-w.length <;> simp

lemma fold_false (gs : List Gate)
    (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (h2 : ∀ g ∈ gs, g.inputs.length = 2)
    (w : List Bool) (hw : ∀ i, w.getD i false = false) :
    ∀ i, (gs.foldl step w).getD i false = false := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih (fun g hg => hAO g (by simp [hg])) (fun g hg => h2 g (by simp [hg]))
      (step w g) (step_false g (hAO g (by simp)) (h2 g (by simp)) w hw)

lemma wire_false {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) :
    (C.wires (List.ofFn (fun _ : Fin n => false))).getD w false = false := by
  rw [wires_eq]
  apply fold_false C.gates hAO.1 hAO.2.2
  intro i
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_3566.ZeroWires

namespace PEqualNP.Outside.L_meta_3566.PrivateProjection
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ShellInsert ShellSemantics

lemma no_private_pure_shell {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hLeast : WireFirst.IsWireLeast G C) (h i j a b c d : ℕ)
    (hh : h < C.gates.length) (hi : i < h) (hj : j < h) (hij : i ≠ j)
    (hgi : gateAt C i = ⟨.or,[a,b]⟩) (hgj : gateAt C j = ⟨.or,[c,d]⟩)
    (hgh : gateAt C h = ⟨.and,[n+i,n+j]⟩)
    (hprivate : ∀ k < C.gates.length, k ≠ h →
      n+i ∉ (gateAt C k).inputs ∧ n+j ∉ (gateAt C k).inputs)
    (hout : C.output < n+C.size) (hoi : C.output ≠ n+i) (hoj : C.output ≠ n+j)
    (hA : Pure color false (fun x => value C x a))
    (hB : Pure color true (fun x => value C x b))
    (hC : Pure color false (fun x => value C x c))
    (hD : Pure color true (fun x => value C x d))
    (hzero : ∀ w, gateVal n C h (single w) = false)
    (u : Fin n) (hu : color u = false) (hAu : value C (single u) a = true) : False := by
  have hAO := hLeast.1.1
  have ha : a < n+h := by
    have ht := hAO.2.1 i (by omega) a (by simp [hgi])
    omega
  have hb : b < n+h := by
    have ht := hAO.2.1 i (by omega) b (by simp [hgi])
    omega
  have hc : c < n+h := by
    have ht := hAO.2.1 j (by omega) c (by simp [hgj])
    omega
  have hd : d < n+h := by
    have ht := hAO.2.1 j (by omega) d (by simp [hgj])
    omega
  have hzero' : ∀ w : Fin n, oldFun (fun x => value C x a) (fun x => value C x b)
      (fun x => value C x c) (fun x => value C x d) (single w) = false := by
    intro w
    have he := (old_values C h i j a b c d hAO hh hi hj hgi hgj hgh (single w)).2.2
    exact he.symm.trans (hzero w)
  apply ShellInsert.no_wire_least G C hLeast h i j a b c d hh hi hj hij hgi hgj hgh
    ha hb hc hd hprivate hout hoi hoj
  · intro v w hvw
    have hp := projection_pair color (fun x => value C x a) (fun x => value C x b)
      (fun x => value C x c) (fun x => value C x d) hA hB hC hD hzero' v w (hbip v w hvw)
    exact hp.trans (old_values C h i j a b c d hAO hh hi hj hgi hgj hgh (pairInput v w)).2.2.symm
  · exact strict_witness G color (fun x => value C x a) (fun x => value C x d)
      hD (ZeroWires.wire_false C hAO d) u hu hAu

end PEqualNP.Outside.L_meta_3566.PrivateProjection


namespace PEqualNP.Outside.L_meta_3566.ShellCount
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ShellInsert

lemma count_le_of_embedding {n : ℕ} (C D : Circuit) (f : Fin D.size → Fin C.size)
    (hf : Function.Injective f) (x : Fin n → Bool)
    (hval : ∀ r, gateVal n D r.val x = true → gateVal n C (f r).val x = true) :
    (D.wires (List.ofFn x)).count true ≤ (C.wires (List.ofFn x)).count true := by
  let e : ℕ → ℕ := fun r => if hr : r < D.size then (f ⟨r,hr⟩).val else 0
  have he (r : ℕ) (hr : r < D.size) : e r = (f ⟨r,hr⟩).val := by simp [e,hr]
  apply WireProfile.wire_count_le C D e
  · intro r hr
    rw [he r hr]
    exact (f ⟨r,hr⟩).isLt
  · intro r hr s hs hrs
    have hr' : r < D.size := Finset.mem_range.mp hr
    have hs' : s < D.size := Finset.mem_range.mp hs
    rw [he r hr',he s hs'] at hrs
    exact congrArg Fin.val (hf (Fin.ext hrs))
  · intro r hr hv
    rw [he r hr]
    exact hval ⟨r,hr⟩ hv

lemma count_lt_of_embedding {n : ℕ} (C D : Circuit) (f : Fin D.size → Fin C.size)
    (hf : Function.Injective f) (x : Fin n → Bool)
    (hval : ∀ r, gateVal n D r.val x = true → gateVal n C (f r).val x = true)
    (hstrict : ∃ i : Fin C.size, gateVal n C i.val x = true ∧
      ∀ r, f r = i → gateVal n D r.val x = false) :
    (D.wires (List.ofFn x)).count true < (C.wires (List.ofFn x)).count true := by
  let e : ℕ → ℕ := fun r => if hr : r < D.size then (f ⟨r,hr⟩).val else 0
  have he (r : ℕ) (hr : r < D.size) : e r = (f ⟨r,hr⟩).val := by simp [e,hr]
  apply WireProfile.wire_count_lt C D e
  · intro r hr
    rw [he r hr]
    exact (f ⟨r,hr⟩).isLt
  · intro r hr s hs hrs
    have hr' : r < D.size := Finset.mem_range.mp hr
    have hs' : s < D.size := Finset.mem_range.mp hs
    rw [he r hr',he s hs'] at hrs
    exact congrArg Fin.val (hf (Fin.ext hrs))
  · intro r hr hv
    rw [he r hr]
    exact hval ⟨r,hr⟩ hv
  · obtain ⟨i,hi,hmiss⟩ := hstrict
    refine ⟨i.val,i.isLt,hi,?_⟩
    intro r hr her
    rw [he r hr] at her
    exact hmiss ⟨r,hr⟩ (Fin.ext her)

lemma pruned_counts {n : ℕ} (C D : Circuit) (h i j a b c d : ℕ)
    (hC : IsAO2 n C) (hh : h < C.gates.length) (hi : i < h) (hj : j < h) (hij : i ≠ j)
    (hgi : gateAt C i = ⟨.or,[a,b]⟩) (hgj : gateAt C j = ⟨.or,[c,d]⟩)
    (hgh : gateAt C h = ⟨.and,[n+i,n+j]⟩)
    (ha : a < n+h) (hb : b < n+h) (hc : c < n+h) (hd : d < n+h)
    (f : Fin D.size → Fin (stars n C h ∅ a d c b).size) (hf : Function.Injective f)
    (havoid : ∀ r, (f r).val ≠ i ∧ (f r).val ≠ j)
    (hval : ∀ r x, gateVal n D r.val x = gateVal n (stars n C h ∅ a d c b) (f r).val x) :
    (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).count true ≤ (C.wires (List.ofFn x)).count true) ∧
    ∀ x : Fin n → Bool, value C x a = true → value C x d = false →
      (D.wires (List.ofFn x)).count true < (C.wires (List.ofFn x)).count true := by
  have hbound (r : Fin D.size) : charge h i j (f r).val < C.size := by
    apply charge_lt C h i j _ hh hi hj
    simpa only [stars,Circuit.size,length] using (f r).isLt
  let e : Fin D.size → Fin C.size := fun r => ⟨charge h i j (f r).val,hbound r⟩
  have heinj : Function.Injective e := by
    intro r s heq
    have hch : charge h i j (f r).val = charge h i j (f s).val := congrArg Fin.val heq
    exact hf (Fin.ext (charge_inj h i j _ _ hi hj hij (havoid r).1 (havoid r).2
      (havoid s).1 (havoid s).2 hch))
  have heval (x : Fin n → Bool) (r : Fin D.size) :
      gateVal n D r.val x = true → gateVal n C (e r).val x = true := by
    intro hv
    exact charge_dom C h i j a b c d _ hC hh hi hj hgi hgj hgh ha hb hc hd x
      ((hval r x).symm.trans hv)
  constructor
  · intro x
    exact count_le_of_embedding C D e heinj x (heval x)
  · intro x hA hD
    apply count_lt_of_embedding C D e heinj x (heval x)
    refine ⟨⟨i,by change i < C.gates.length; omega⟩,?_,?_⟩
    · change value C x (n+i) = true
      rw [(old_values C h i j a b c d hC hh hi hj hgi hgj hgh x).1,hA]
      rfl
    · intro r her
      have hch : charge h i j (f r).val = i := congrArg Fin.val her
      have hfr := charge_eq_i h i j _ hi hj hij (havoid r).1 (havoid r).2 hch
      rw [hval r x,hfr]
      change value (stars n C h ∅ a d c b) x (n+h) = false
      rw [(stars_operands C h a d c b hC hh ha hd hc hb x).1,hD]
      simp

lemma exists_projection {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h i j a b c d : ℕ)
    (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hh : h < C.gates.length) (hi : i < h) (hj : j < h) (hij : i ≠ j)
    (hgi : gateAt C i = ⟨.or,[a,b]⟩) (hgj : gateAt C j = ⟨.or,[c,d]⟩)
    (hgh : gateAt C h = ⟨.and,[n+i,n+j]⟩)
    (ha : a < n+h) (hb : b < n+h) (hc : c < n+h) (hd : d < n+h)
    (hprivate : ∀ k < C.gates.length, k ≠ h →
      n+i ∉ (gateAt C k).inputs ∧ n+j ∉ (gateAt C k).inputs)
    (hout : C.output < n+C.size) (hoi : C.output ≠ n+i) (hoj : C.output ≠ n+j)
    (hedge : ∀ u v : Fin n, G.Adj u v →
      ((value C (pairInput u v) a && value C (pairInput u v) d)||
        (value C (pairInput u v) c && value C (pairInput u v) b)) = value C (pairInput u v) (n+h)) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      (∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).count true ≤ (C.wires (List.ofFn x)).count true) ∧
      ∀ x : Fin n → Bool, value C x a = true → value C x d = false →
        (D.wires (List.ofFn x)).count true < (C.wires (List.ofFn x)).count true := by
  obtain ⟨D,hD,hs,hF,f,hf,havoid,hval⟩ :=
    prune_projection C h i j a b c d hC hh hi hj hij hgi hgj ha hb hc hd hprivate hout hoi hoj
  refine ⟨D,hD,hF.trans ?_,hs,?_⟩
  · exact projection_graph_correct G C h i j a b c d hC hfun hh hi hj hgi hgj hgh ha hb hc hd hedge
  · exact pruned_counts C D h i j a b c d hC hh hi hj hij hgi hgj hgh ha hb hc hd f hf havoid hval

def twoRowWeight {n : ℕ} (C : Circuit) (x0 x1 : Fin n → Bool) (w0 w1 : ℕ) : ℕ :=
  w0 * (C.wires (List.ofFn x0)).count true + w1 * (C.wires (List.ofFn x1)).count true

lemma twoRowWeight_le {n : ℕ} (C D : Circuit) (x0 x1 : Fin n → Bool) (w0 w1 : ℕ)
    (hle : ∀ x : Fin n → Bool,
      (D.wires (List.ofFn x)).count true ≤ (C.wires (List.ofFn x)).count true) :
    twoRowWeight D x0 x1 w0 w1 ≤ twoRowWeight C x0 x1 w0 w1 := by
  exact Nat.add_le_add (Nat.mul_le_mul_left w0 (hle x0)) (Nat.mul_le_mul_left w1 (hle x1))

lemma twoRowWeight_lt {n : ℕ} (C D : Circuit) (x0 x1 : Fin n → Bool) (w0 w1 : ℕ)
    (hle : ∀ x : Fin n → Bool,
      (D.wires (List.ofFn x)).count true ≤ (C.wires (List.ofFn x)).count true)
    (hlt : (0 < w0 ∧ (D.wires (List.ofFn x0)).count true < (C.wires (List.ofFn x0)).count true) ∨
      (0 < w1 ∧ (D.wires (List.ofFn x1)).count true < (C.wires (List.ofFn x1)).count true)) :
    twoRowWeight D x0 x1 w0 w1 < twoRowWeight C x0 x1 w0 w1 := by
  rcases hlt with ⟨hw,hx⟩ | ⟨hw,hx⟩
  · exact Nat.add_lt_add_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hx hw) (Nat.mul_le_mul_left w1 (hle x1))
  · exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left w0 (hle x0)) (Nat.mul_lt_mul_of_pos_left hx hw)

lemma twoRowWeight_lt_of_shell {n : ℕ} (C D : Circuit) (a d : ℕ)
    (hle : ∀ x : Fin n → Bool,
      (D.wires (List.ofFn x)).count true ≤ (C.wires (List.ofFn x)).count true)
    (hstrict : ∀ x : Fin n → Bool, value C x a = true → value C x d = false →
      (D.wires (List.ofFn x)).count true < (C.wires (List.ofFn x)).count true)
    (x0 x1 : Fin n → Bool) (w0 w1 : ℕ)
    (hrow : (0 < w0 ∧ value C x0 a = true ∧ value C x0 d = false) ∨
      (0 < w1 ∧ value C x1 a = true ∧ value C x1 d = false)) :
    twoRowWeight D x0 x1 w0 w1 < twoRowWeight C x0 x1 w0 w1 := by
  apply twoRowWeight_lt C D x0 x1 w0 w1 hle
  rcases hrow with ⟨hw,hA,hD⟩ | ⟨hw,hA,hD⟩
  · exact Or.inl ⟨hw,hstrict x0 hA hD⟩
  · exact Or.inr ⟨hw,hstrict x1 hA hD⟩

lemma twoRowMass_lt_of_shell {n : ℕ} (C D : Circuit) (a d : ℕ)
    (hle : ∀ x : Fin n → Bool,
      (D.wires (List.ofFn x)).count true ≤ (C.wires (List.ofFn x)).count true)
    (hstrict : ∀ x : Fin n → Bool, value C x a = true → value C x d = false →
      (D.wires (List.ofFn x)).count true < (C.wires (List.ofFn x)).count true)
    (x0 x1 : Fin n → Bool)
    (hrow : (value C x0 a = true ∧ value C x0 d = false) ∨
      (value C x1 a = true ∧ value C x1 d = false)) :
    (D.wires (List.ofFn x0)).count true + (D.wires (List.ofFn x1)).count true <
      (C.wires (List.ofFn x0)).count true + (C.wires (List.ofFn x1)).count true := by
  have h := twoRowWeight_lt_of_shell C D a d hle hstrict x0 x1 1 1
    (hrow.elim (fun hx => Or.inl ⟨by decide,hx⟩) (fun hx => Or.inr ⟨by decide,hx⟩))
  simpa only [twoRowWeight,one_mul] using h

end PEqualNP.Outside.L_meta_3566.ShellCount

namespace PEqualNP.Outside.L_meta_3566.MonoSemantics
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm ShellSemantics

def input {n : ℕ} (color : Fin n → Bool) (side : Bool) : Fin n → Bool :=
  mask color side (fun _ => true)

def mass {n : ℕ} (color : Fin n → Bool) (C : Circuit) : ℕ :=
  (C.wires (List.ofFn (input color false))).count true +
    (C.wires (List.ofFn (input color true))).count true

lemma input_true {n : ℕ} (color : Fin n → Bool) (side : Bool) (u : Fin n) :
    input color side u = true ↔ color u = side := by
  simp [input,mask]

lemma input_negative {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (side : Bool) : graphFun G ∅ (input color side) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have h' : ∃ u v, G.Adj u v ∧ input color side u = true ∧ input color side v = true := by
    simpa [graphFun] using h
  obtain ⟨u,v,huv,hu,hv⟩ := h'
  exact hbip u v huv ((input_true color side u).mp hu |>.trans ((input_true color side v).mp hv).symm)

lemma pure_opposite_false {n : ℕ} (color : Fin n → Bool)
    (f : (Fin n → Bool) → Bool) (hf : Pure color true f)
    (hfzero : f (fun _ => false) = false) : f (input color false) = false := by
  have hm : mask color true (input color false) = (fun _ => false) := by
    funext w
    cases hc : color w <;> simp [mask,input,hc]
  rw [hf,hm,hfzero]

lemma positive_single_to_input {n : ℕ} (color : Fin n → Bool)
    (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (u : Fin n) (hu : color u = false) (hfu : f (single u) = true) :
    f (input color false) = true := by
  have hle : single u ≤ input color false := by
    intro w
    by_cases hw : w = u
    · subst w
      simp [single,input,mask,hu]
    · simp [single,hw]
  have h := hf hle
  rw [hfu] at h
  apply le_antisymm
  · cases f (input color false) <;> decide
  · exact h

lemma mass_lt_of_pointwise {n : ℕ} (color : Fin n → Bool) (C D : Circuit)
    (hle : ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).count true ≤
      (C.wires (List.ofFn x)).count true)
    (hlt : (D.wires (List.ofFn (input color false))).count true <
      (C.wires (List.ofFn (input color false))).count true) : mass color D < mass color C := by
  have hright := hle (input color true)
  unfold mass
  omega

end PEqualNP.Outside.L_meta_3566.MonoSemantics

namespace PEqualNP.Outside.L_meta_3566.MonoProjection
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ShellInsert ShellSemantics

lemma exists_pure_projection {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (h i j a b c d : ℕ)
    (hh : h < C.gates.length) (hi : i < h) (hj : j < h) (hij : i ≠ j)
    (hgi : gateAt C i = ⟨.or,[a,b]⟩) (hgj : gateAt C j = ⟨.or,[c,d]⟩)
    (hgh : gateAt C h = ⟨.and,[n+i,n+j]⟩)
    (hprivate : ∀ k < C.gates.length, k ≠ h →
      n+i ∉ (gateAt C k).inputs ∧ n+j ∉ (gateAt C k).inputs)
    (hout : C.output < n+C.size) (hoi : C.output ≠ n+i) (hoj : C.output ≠ n+j)
    (hA : Pure color false (fun x => value C x a))
    (hB : Pure color true (fun x => value C x b))
    (hC : Pure color false (fun x => value C x c))
    (hD : Pure color true (fun x => value C x d))
    (hzero : ∀ w, gateVal n C h (single w) = false)
    (hAmax : value C (MonoSemantics.input color false) a = true) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      MonoSemantics.mass color D < MonoSemantics.mass color C := by
  have ha : a < n+h := by
    have ht := hAO.2.1 i (by omega) a (by simp [hgi])
    omega
  have hb : b < n+h := by
    have ht := hAO.2.1 i (by omega) b (by simp [hgi])
    omega
  have hc : c < n+h := by
    have ht := hAO.2.1 j (by omega) c (by simp [hgj])
    omega
  have hd : d < n+h := by
    have ht := hAO.2.1 j (by omega) d (by simp [hgj])
    omega
  have hzero' : ∀ w : Fin n, oldFun (fun x => value C x a) (fun x => value C x b)
      (fun x => value C x c) (fun x => value C x d) (single w) = false := by
    intro w
    have he := (old_values C h i j a b c d hAO hh hi hj hgi hgj hgh (single w)).2.2
    exact he.symm.trans (hzero w)
  have hedge : ∀ u v : Fin n, G.Adj u v →
      ((value C (pairInput u v) a && value C (pairInput u v) d)||
        (value C (pairInput u v) c && value C (pairInput u v) b)) = value C (pairInput u v) (n+h) := by
    intro u v huv
    have hp := projection_pair color (fun x => value C x a) (fun x => value C x b)
      (fun x => value C x c) (fun x => value C x d) hA hB hC hD hzero' u v (hbip u v huv)
    exact hp.trans (old_values C h i j a b c d hAO hh hi hj hgi hgj hgh (pairInput u v)).2.2.symm
  obtain ⟨D,hDao,hDF,hsize,hle,hstrict⟩ := ShellCount.exists_projection G C h i j a b c d
    hAO hfun hh hi hj hij hgi hgj hgh ha hb hc hd hprivate hout hoi hoj hedge
  refine ⟨D,hDao,hDF,hsize,MonoSemantics.mass_lt_of_pointwise color C D hle ?_⟩
  apply hstrict (MonoSemantics.input color false) hAmax
  exact MonoSemantics.pure_opposite_false color (fun x => value C x d) hD (ZeroWires.wire_false C hAO d)

lemma no_strict_competitor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (C : Circuit)
    (hmin : ∀ D : Circuit, IsAO2 n D → circuitFun n D = graphFun G ∅ → D.size ≤ C.size →
      MonoSemantics.mass color C ≤ MonoSemantics.mass color D)
    (hex : ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      MonoSemantics.mass color D < MonoSemantics.mass color C) : False := by
  obtain ⟨D,hD,hF,hs,hm⟩ := hex
  exact Nat.not_lt_of_ge (hmin D hD hF hs) hm

end PEqualNP.Outside.L_meta_3566.MonoProjection

namespace PEqualNP.Outside.L_meta_3566.RailObstruction

def rails {p k : ℕ} (support : Fin k → Finset (Fin p))
    (x : Fin p → Bool) : Fin k → Bool :=
  fun i => decide (∃ u ∈ support i, x u = true)

def edgeFun {p q : ℕ} (E : Fin p → Fin q → Prop) [DecidableRel E]
    (x : Fin p → Bool) (y : Fin q → Bool) : Bool :=
  decide (∃ u v, E u v ∧ x u = true ∧ y v = true)

lemma large_support_survives {p k : ℕ} (support : Fin k → Finset (Fin p))
    (N : Finset (Fin p)) (hlarge : ∀ i, N.card < (support i).card) :
    rails support (fun u => decide (u ∉ N)) = rails support (fun _ => true) := by
  classical
  funext i
  have hnot : ¬ support i ⊆ N := by
    intro hsub
    exact Nat.not_lt_of_ge (Finset.card_le_card hsub) (hlarge i)
  obtain ⟨u, hu, hn⟩ := Finset.not_subset.mp hnot
  have hb : rails support (fun u => decide (u ∉ N)) i = true := by
    simp only [rails, decide_eq_true_eq]
    exact ⟨u,hu,by simp [hn]⟩
  have hg : rails support (fun _ => true) i = true := by
    simp only [rails, decide_eq_true_eq]
    exact ⟨u,hu,True.intro⟩
  exact hb.trans hg.symm

lemma no_large_rail_factorization {p q k : ℕ}
    (E : Fin p → Fin q → Prop) [DecidableRel E]
    (support : Fin k → Finset (Fin p))
    (post : (Fin k → Bool) → (Fin q → Bool) → Bool)
    (v : Fin q) (hedge : ∃ u, E u v)
    (hlarge : ∀ i, (Finset.univ.filter (fun u => E u v)).card < (support i).card)
    (hcorrect : ∀ x y, post (rails support x) y = edgeFun E x y) : False := by
  classical
  let N : Finset (Fin p) := Finset.univ.filter (fun u => E u v)
  let x : Fin p → Bool := fun u => decide (u ∉ N)
  let y : Fin q → Bool := fun w => decide (w = v)
  have hsame : rails support x = rails support (fun _ => true) :=
    large_support_survives support N hlarge
  have hfalse : edgeFun E x y = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have h' : ∃ u w, E u w ∧ x u = true ∧ y w = true := by
      simpa [edgeFun] using h
    obtain ⟨u,w,he,hx,hy⟩ := h'
    have hw : w = v := by simpa [y] using hy
    subst w
    have hu : u ∉ N := by simpa [x] using hx
    exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ u,he⟩)
  have htrue : edgeFun E (fun _ => true) y = true := by
    obtain ⟨u,hu⟩ := hedge
    simp only [edgeFun, decide_eq_true_eq]
    exact ⟨u,v,hu,True.intro,by simp [y]⟩
  have heq := congrArg (fun z => post z y) hsame
  rw [hcorrect,hcorrect,hfalse,htrue] at heq
  cases heq

lemma exists_small_rail {p q k : ℕ}
    (E : Fin p → Fin q → Prop) [DecidableRel E]
    (support : Fin k → Finset (Fin p))
    (post : (Fin k → Bool) → (Fin q → Bool) → Bool)
    (hcorrect : ∀ x y, post (rails support x) y = edgeFun E x y)
    (v : Fin q) (hedge : ∃ u, E u v) :
    ∃ i, (support i).card ≤ (Finset.univ.filter (fun u => E u v)).card := by
  classical
  by_contra h
  have hlarge : ∀ i, (Finset.univ.filter (fun u => E u v)).card < (support i).card := by
    intro i
    by_contra hi
    exact h ⟨i,Nat.le_of_not_gt hi⟩
  exact no_large_rail_factorization E support post v hedge hlarge hcorrect

lemma exists_nonempty_rail_subset {p q k : ℕ}
    (E : Fin p → Fin q → Prop) [DecidableRel E]
    (support : Fin k → Finset (Fin p))
    (post : (Fin k → Bool) → (Fin q → Bool) → Bool)
    (hcorrect : ∀ x y, post (rails support x) y = edgeFun E x y)
    (v : Fin q) (hedge : ∃ u, E u v) :
    ∃ i, (support i).Nonempty ∧ support i ⊆ Finset.univ.filter (fun u => E u v) := by
  classical
  let N : Finset (Fin p) := Finset.univ.filter (fun u => E u v)
  let x : Fin p → Bool := fun u => decide (u ∉ N)
  let y : Fin q → Bool := fun w => decide (w = v)
  by_contra h
  have hsame : rails support x = rails support (fun _ => true) := by
    funext i
    by_cases hi : (support i).Nonempty
    · have hn : ¬ support i ⊆ N := fun hs => h ⟨i, hi, hs⟩
      obtain ⟨u, hu, hout⟩ := Finset.not_subset.mp hn
      have hb : rails support x i = true := by
        simp only [rails, decide_eq_true_eq]
        exact ⟨u, hu, by simp [x, hout]⟩
      have hg : rails support (fun _ => true) i = true := by
        simp only [rails, decide_eq_true_eq]
        exact ⟨u, hu, True.intro⟩
      exact hb.trans hg.symm
    · have hempty : support i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
      simp [rails, hempty]
  have hfalse : edgeFun E x y = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have he' : ∃ u w, E u w ∧ x u = true ∧ y w = true := by
      simpa [edgeFun] using he
    obtain ⟨u, w, huw, hx, hy⟩ := he'
    have hw : w = v := by simpa [y] using hy
    subst w
    have hu : u ∉ N := by simpa [x] using hx
    exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ u, huw⟩)
  have htrue : edgeFun E (fun _ => true) y = true := by
    obtain ⟨u, hu⟩ := hedge
    simp only [edgeFun, decide_eq_true_eq]
    exact ⟨u, v, hu, True.intro, by simp [y]⟩
  have heq := congrArg (fun z => post z y) hsame
  rw [hcorrect, hcorrect, hfalse, htrue] at heq
  cases heq

lemma exists_rail_for_edge_general {p q k : ℕ}
    (E : Fin p → Fin q → Prop) [DecidableRel E]
    (support : Fin k → Finset (Fin p))
    (post : (Fin k → Bool) → (Fin q → Bool) → Bool)
    (hcorrect : ∀ x y, post (rails support x) y = edgeFun E x y)
    (u : Fin p) (v : Fin q) (huv : E u v) :
    ∃ i, u ∈ support i ∧ support i ⊆ Finset.univ.filter (fun w => E w v) := by
  classical
  let N : Finset (Fin p) := Finset.univ.filter (fun w => E w v)
  let x₀ : Fin p → Bool := fun w => decide (w ∉ N)
  let x₁ : Fin p → Bool := fun w => decide (w ∉ N ∨ w = u)
  let y : Fin q → Bool := fun w => decide (w = v)
  by_contra h
  have hsame : rails support x₀ = rails support x₁ := by
    funext i
    by_cases hi : ∃ w ∈ support i, w ∉ N
    · obtain ⟨w, hw, hn⟩ := hi
      have h₀ : rails support x₀ i = true := by
        simp only [rails, decide_eq_true_eq]
        exact ⟨w, hw, by simp [x₀, hn]⟩
      have h₁ : rails support x₁ i = true := by
        simp only [rails, decide_eq_true_eq]
        exact ⟨w, hw, by simp [x₁, hn]⟩
      exact h₀.trans h₁.symm
    · have hsub : support i ⊆ N := by
        intro w hw
        by_contra hn
        exact hi ⟨w, hw, hn⟩
      have hun : u ∉ support i := fun hui => h ⟨i, hui, hsub⟩
      have h₀ : rails support x₀ i = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        have ht' : ∃ w ∈ support i, x₀ w = true := by simpa [rails] using ht
        obtain ⟨w, hw, hx⟩ := ht'
        have hn : w ∉ N := by simpa [x₀] using hx
        exact hn (hsub hw)
      have h₁ : rails support x₁ i = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        have ht' : ∃ w ∈ support i, x₁ w = true := by simpa [rails] using ht
        obtain ⟨w, hw, hx⟩ := ht'
        have hn : w ∉ N ∨ w = u := by simpa [x₁] using hx
        rcases hn with hn | rfl
        · exact hn (hsub hw)
        · exact hun hw
      exact h₀.trans h₁.symm
  have hfalse : edgeFun E x₀ y = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have ht' : ∃ a b, E a b ∧ x₀ a = true ∧ y b = true := by
      simpa [edgeFun] using ht
    obtain ⟨a, b, hab, ha, hb⟩ := ht'
    have hbv : b = v := by simpa [y] using hb
    subst b
    have han : a ∉ N := by simpa [x₀] using ha
    exact han (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hab⟩)
  have htrue : edgeFun E x₁ y = true := by
    simp only [edgeFun, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [x₁], by simp [y]⟩
  have heq := congrArg (fun z => post z y) hsame
  rw [hcorrect, hcorrect, hfalse, htrue] at heq
  cases heq

lemma neighborhood_eq_union_contained_rails {p q k : ℕ}
    (E : Fin p → Fin q → Prop) [DecidableRel E]
    (support : Fin k → Finset (Fin p))
    (post : (Fin k → Bool) → (Fin q → Bool) → Bool)
    (hcorrect : ∀ x y, post (rails support x) y = edgeFun E x y)
    (v : Fin q) :
    (Finset.univ.filter (fun i => support i ⊆
      Finset.univ.filter (fun u => E u v))).biUnion support =
      Finset.univ.filter (fun u => E u v) := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp hu
    exact (Finset.mem_filter.mp hi).2 hui
  · intro hu
    have huv : E u v := (Finset.mem_filter.mp hu).2
    obtain ⟨i, hui, hi⟩ := exists_rail_for_edge_general E support post hcorrect u v huv
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, hui⟩

lemma matching_rail_injective {p q k m : ℕ}
    (E : Fin p → Fin q → Prop) [DecidableRel E]
    (support : Fin k → Finset (Fin p))
    (left : Fin m → Fin p) (right : Fin m → Fin q)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hfour : ∀ a b v w, a ≠ b → v ≠ w →
      E a v → E a w → E b v → E b w → False)
    (choose : Fin m → Fin k)
    (hcover : ∀ t, left t ∈ support (choose t) ∧
      support (choose t) ⊆ Finset.univ.filter (fun a => E a (right t))) :
    Function.Injective choose := by
  intro s t hst
  by_contra hne
  have hls : left s ∈ support (choose s) := (hcover s).1
  have hlt : left t ∈ support (choose s) := hst ▸ (hcover t).1
  have hrs : left s ∈ support (choose t) := hst ▸ hls
  have hrt : left t ∈ support (choose t) := (hcover t).1
  have hss := Finset.mem_filter.mp ((hcover s).2 hls)
  have hst' := Finset.mem_filter.mp ((hcover t).2 hrs)
  have hts := Finset.mem_filter.mp ((hcover s).2 hlt)
  have htt := Finset.mem_filter.mp ((hcover t).2 hrt)
  exact hfour (left s) (left t) (right s) (right t)
    (fun h => hne (hl h)) (fun h => hne (hr h)) hss.2 hst'.2 hts.2 htt.2

lemma matching_bound_of_cover {p q k m : ℕ}
    (E : Fin p → Fin q → Prop) [DecidableRel E]
    (support : Fin k → Finset (Fin p))
    (left : Fin m → Fin p) (right : Fin m → Fin q)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hfour : ∀ a b v w, a ≠ b → v ≠ w →
      E a v → E a w → E b v → E b w → False)
    (hcover : ∀ t, ∃ i, left t ∈ support i ∧
      support i ⊆ Finset.univ.filter (fun a => E a (right t))) : m ≤ k := by
  classical
  choose f hf using hcover
  have hinj := matching_rail_injective E support left right hl hr hfour f hf
  simpa using Fintype.card_le_of_injective f hinj

def singletonInput {p : ℕ} (u : Fin p) : Fin p → Bool :=
  fun a => decide (a = u)

def singletonSupport {p : ℕ} (f : (Fin p → Bool) → Bool) : Finset (Fin p) :=
  Finset.univ.filter (fun u => f (singletonInput u) = true)

lemma edge_covered_monotone_frontier {p q k : ℕ}
    (E : Fin p → Fin q → Prop) [DecidableRel E]
    (pre : Fin k → (Fin p → Bool) → Bool)
    (post : (Fin k → Bool) → (Fin q → Bool) → Bool)
    (hpre : ∀ i, Monotone (pre i))
    (hpost : ∀ y, Monotone (fun z => post z y))
    (hcorrect : ∀ x y, post (fun i => pre i x) y = edgeFun E x y)
    (u : Fin p) (v : Fin q) (huv : E u v) :
    ∃ i, u ∈ singletonSupport (pre i) ∧
      singletonSupport (pre i) ⊆ Finset.univ.filter (fun a => E a v) := by
  classical
  let N : Finset (Fin p) := Finset.univ.filter (fun a => E a v)
  let bad : Fin p → Bool := fun a => decide (a ∉ N)
  let y : Fin q → Bool := fun b => decide (b = v)
  by_contra h
  have hle : (fun i => pre i (singletonInput u)) ≤ (fun i => pre i bad) := by
    intro i
    change pre i (singletonInput u) ≤ pre i bad
    cases hi : pre i (singletonInput u) with
    | false => simp
    | true =>
      have hui : u ∈ singletonSupport (pre i) := by simp [singletonSupport, hi]
      have hn : ¬ singletonSupport (pre i) ⊆ N := fun hs => h ⟨i, hui, hs⟩
      obtain ⟨a, ha, hout⟩ := Finset.not_subset.mp hn
      have hia : pre i (singletonInput a) = true := (Finset.mem_filter.mp ha).2
      have hab : singletonInput a ≤ bad := by
        intro b
        by_cases hba : b = a
        · subst b
          simp [singletonInput, bad, hout]
        · simp [singletonInput, hba]
      have hb := hpre i hab
      rw [hia] at hb
      exact hb
  have hfalse : edgeFun E bad y = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have he' : ∃ a b, E a b ∧ bad a = true ∧ y b = true := by
      simpa [edgeFun] using he
    obtain ⟨a, b, hab, hx, hy⟩ := he'
    have hb : b = v := by simpa [y] using hy
    subst b
    have ha : a ∉ N := by simpa [bad] using hx
    exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hab⟩)
  have htrue : edgeFun E (singletonInput u) y = true := by
    simp only [edgeFun, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [singletonInput], by simp [y]⟩
  have hp := hpost y hle
  change post (fun i => pre i (singletonInput u)) y ≤ post (fun i => pre i bad) y at hp
  rw [hcorrect, hcorrect, htrue, hfalse] at hp
  exact (by decide : ¬ (true : Bool) ≤ false) hp

lemma matching_bound_monotone_frontier {p q k m : ℕ}
    (E : Fin p → Fin q → Prop) [DecidableRel E]
    (pre : Fin k → (Fin p → Bool) → Bool)
    (post : (Fin k → Bool) → (Fin q → Bool) → Bool)
    (hpre : ∀ i, Monotone (pre i))
    (hpost : ∀ y, Monotone (fun z => post z y))
    (hcorrect : ∀ x y, post (fun i => pre i x) y = edgeFun E x y)
    (left : Fin m → Fin p) (right : Fin m → Fin q)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hedges : ∀ t, E (left t) (right t))
    (hfour : ∀ a b v w, a ≠ b → v ≠ w →
      E a v → E a w → E b v → E b w → False) : m ≤ k := by
  apply matching_bound_of_cover E (fun i => singletonSupport (pre i)) left right hl hr hfour
  intro t
  exact edge_covered_monotone_frontier E pre post hpre hpost hcorrect (left t) (right t) (hedges t)

lemma matching_bound_of_rail_factorization {p q k m : ℕ}
    (E : Fin p → Fin q → Prop) [DecidableRel E]
    (support : Fin k → Finset (Fin p))
    (post : (Fin k → Bool) → (Fin q → Bool) → Bool)
    (hcorrect : ∀ x y, post (rails support x) y = edgeFun E x y)
    (left : Fin m → Fin p) (right : Fin m → Fin q)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hedges : ∀ t, E (left t) (right t))
    (hfour : ∀ a b v w, a ≠ b → v ≠ w →
      E a v → E a w → E b v → E b w → False) : m ≤ k := by
  apply matching_bound_of_cover E support left right hl hr hfour
  intro t
  exact exists_rail_for_edge_general E support post hcorrect (left t) (right t) (hedges t)

end PEqualNP.Outside.L_meta_3566.RailObstruction
