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

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport

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

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.Splice

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

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.Splice

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport

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

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport

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

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.MixedColor

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
end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.MixedColor

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.WireFacts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

lemma wire_monotone {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => (C.wires (List.ofFn x)).getD w false) := by
  change Monotone (circuitFun n {C with output := w})
  exact Splice.circuitFun_monotone n {C with output := w} hAO.1

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.WireFacts

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.AndChild

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

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.AndChild

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.OrCharge

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

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.OrCharge

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.OrCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def wire {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.OrCharge

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.SemanticPurity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership

def W (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma W_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    W n C w x = x ⟨w, hw⟩ := by
  exact MixedColor.val_ofFn C x ⟨w, hw⟩

lemma W_gate {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (hab : (gateAt C j).inputs = [a, b]) (x : Fin n → Bool) :
    W n C (n + j) x = (gateAt C j).op.eval [W n C a x, W n C b x] := by
  rw [W, gate_wire_eval C hAO.2.1 j hj x, hab]
  rfl

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

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.SemanticPurity

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.TopFrontier

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

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.TopFrontier

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.TopFrontierCoverage

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

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.TopFrontierCoverage

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.ParallelRewrite

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

def rewrite (C : Circuit) (f : Fin C.gates.length → Gate) : Circuit :=
  ⟨List.ofFn f, C.output⟩

lemma rewrite_length (C : Circuit) (f : Fin C.gates.length → Gate) :
    (rewrite C f).gates.length = C.gates.length := by simp [rewrite]

lemma rewrite_size (C : Circuit) (f : Fin C.gates.length → Gate) :
    (rewrite C f).size = C.size := by simp [Circuit.size, rewrite]

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

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.ParallelRewrite

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.LeastGateLive

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm SemanticPurity ParallelRewrite

lemma output_or_later_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    C.output = n + j ∨ ∃ k, j < k ∧ k < C.gates.length ∧
      n + j ∈ (gateAt C k).inputs := by
  classical
  by_contra h
  have hout : C.output ≠ n + j := fun he => h (Or.inl he)
  have hreader : ∀ k, k < C.gates.length → n + j ∉ (gateAt C k).inputs := by
    intro k hk hin
    have hlt := hLeast.1.2.1 k hk (n + j) hin
    exact h (Or.inr ⟨k, by omega, hk, hin⟩)
  obtain ⟨a, b, hab⟩ := MixedColor.binaryInputs hLeast.1 hj
  have ha : a < n + j := hLeast.1.2.1 j hj a (by simp [hab])
  let f : Fin C.gates.length → Gate := fun k =>
    if k.val = j then ⟨.or, [a, a]⟩ else gateAt C k.val
  let D := rewrite C f
  have hlen : D.gates.length = C.gates.length := rewrite_length C f
  have hsize : D.size = C.size := rewrite_size C f
  have hgate (k : ℕ) (hk : k < C.gates.length) :
      gateAt D k = if k = j then ⟨.or, [a, a]⟩ else gateAt C k := by
    exact rewrite_gate C f k hk
  have hAO : IsAO2 n D := by
    apply rewrite_ao C f
    · intro k
      by_cases hk : k.val = j
      · simp [f, hk]
      · simpa [f, hk] using hLeast.1.1 _ (MixedColor.gateAt_mem k.isLt)
    · intro k
      by_cases hk : k.val = j
      · simp [f, hk]
      · simpa [f, hk] using hLeast.1.2.2 _ (MixedColor.gateAt_mem k.isLt)
    · intro k i hi
      by_cases hk : k.val = j
      · simp only [f, ite_eq_left hk, List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
        subst i
        simpa only [hk] using ha
      · simp only [f, ite_eq_right hk] at hi
        exact hLeast.1.2.1 k.val k.isLt i hi
  have hstable : ∀ x : Fin n → Bool, ∀ z, z ≠ n + j → value D x z = value C x z := by
    intro x
    apply wire_relation C D hlen hLeast.1.2.1 hAO.2.1 x
      (fun z old new => z ≠ n + j → new = old)
    · intro z hz _
      rfl
    · intro z hz _
      rfl
    · intro k hk ih hne
      have hkj : k ≠ j := by omega
      rw [hgate k hk, ite_eq_right hkj]
      apply congrArg (gateAt C k).op.eval
      apply List.map_congr_left
      intro i hi
      exact ih i (hLeast.1.2.1 k hk i hi) (fun he => hreader k hk (he ▸ hi))
  have hfun : circuitFun n D = graphFun G ∅ := by
    rw [← hLeast.2.1]
    funext x
    change value D x C.output = value C x C.output
    exact hstable x C.output hout
  have hLD : IsLeastAO G D := by
    refine ⟨hAO, hfun, ?_⟩
    intro E hE hEf
    rw [hsize]
    exact hLeast.2.2 E hE hEf
  apply not_equal_earlier G D hLD j a (by omega) ha
  funext x
  change value D x (n + j) = value D x a
  rw [value_gate D hAO.2.1 x j (by omega), hgate j hj, ite_eq_left rfl]
  simp [GateOp.eval]

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.LeastGateLive

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.JunkPurity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership SemanticPurity

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, _, _, hgk⟩ := Splice.split_gates C.gates k hk
  have hga : gateAt C k = gk := by simpa only [gateAt, List.getD_eq_getElem _ _ hk] using hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
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

lemma cone_step {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) {i j k : ℕ}
    (hk : k < C.gates.length) (hm : n + j ∈ (gateAt C k).inputs)
    (hi : i = j ∨ InCone n C i j) : InCone n C i k := by
  apply (inCone_iff n C i k hk).mpr
  refine ⟨n + j, hm, by omega, hAO.2.1 k hk _ hm, ?_⟩
  simpa using hi

lemma cone_trans {n : ℕ} (C : Circuit) {i j k : ℕ}
    (hk : k < C.gates.length) (hij : InCone n C i j) (hjk : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨w, hw, hn, hlt, heq | hc⟩ := (inCone_iff n C j k hk).mp hjk
    · exact (inCone_iff n C i k hk).mpr ⟨w, hw, hn, hlt, Or.inr (heq ▸ hij)⟩
    · exact (inCone_iff n C i k hk).mpr
        ⟨w, hw, hn, hlt, Or.inr (ih (w-n) (by omega) (by omega) hc)⟩

lemma reaches_and_or_output {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (hlive : ∀ j, j < C.gates.length → C.output = n+j ∨
      ∃ k, j < k ∧ k < C.gates.length ∧ n+j ∈ (gateAt C k).inputs) :
    ∀ j, j < C.gates.length →
      Relation.ReflTransGen (MixedColor.OrStep n C) C.output (n+j) ∨
      ∃ k w, k < C.gates.length ∧ (gateAt C k).op = .and ∧
        w ∈ (gateAt C k).inputs ∧ Relation.ReflTransGen (MixedColor.OrStep n C) w (n+j) := by
  intro j hj
  have haux : ∀ d j, C.gates.length-j = d → j < C.gates.length →
      Relation.ReflTransGen (MixedColor.OrStep n C) C.output (n+j) ∨
      ∃ k w, k < C.gates.length ∧ (gateAt C k).op = .and ∧
        w ∈ (gateAt C k).inputs ∧ Relation.ReflTransGen (MixedColor.OrStep n C) w (n+j) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro j hd hj
      rcases hlive j hj with hout | ⟨k,hjk,hk,hread⟩
      · left; rw [hout]
      · rcases hAO.1 _ (MixedColor.gateAt_mem hk) with ha | ho
        · exact Or.inr ⟨k,n+j,hk,ha,hread,.refl⟩
        · have hs : MixedColor.OrStep n C (n+k) (n+j) :=
            ⟨k,hk,rfl,ho,hread,by omega⟩
          rcases ih (C.gates.length-k) (by omega) k rfl hk with hp | ⟨a,w,ha,hop,hw,hp⟩
          · exact Or.inl (hp.tail hs)
          · exact Or.inr ⟨a,w,ha,hop,hw,hp.tail hs⟩
  exact haux _ j rfl hj

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.JunkPurity

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.AliasErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership Splice ParallelRewrite

lemma wire_eq {n : ℕ} (C : Circuit) (j s : ℕ) (hj : j < C.gates.length)
    (hs : s < n + j) (heq : ∀ x : Fin n → Bool, value C x (n + j) = value C x s)
    (x : Fin n → Bool) (w : ℕ) :
    value C x w = value (dropDup n C j s) x (aliasWire (n + j) s w) := by
  let Cw : Circuit := { C with output := w }
  have hmono : ∀ g ∈ Cw.gates, ∀ f h : ℕ → Bool, (∀ u, f u = h u) →
      g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map h) := by
    intro g hg f h he
    congr 1
    exact List.map_congr_left (fun u _ => he u)
  have hr := dropDup_rel (R := Eq) (fun _ => rfl) n Cw j s hj hs hmono x (heq x)
  exact hr

lemma function_eq {n : ℕ} (C : Circuit) (j s : ℕ) (hj : j < C.gates.length)
    (hs : s < n + j) (heq : ∀ x : Fin n → Bool, value C x (n + j) = value C x s) :
    circuitFun n (dropDup n C j s) = circuitFun n C := by
  funext x
  exact (wire_eq C j s hj hs heq x C.output).symm

def oldIndex (j k : ℕ) : ℕ := if k < j then k else k + 1

lemma oldIndex_injective (j : ℕ) : Function.Injective (oldIndex j) := by
  intro a b h
  unfold oldIndex at h
  split_ifs at h <;> omega

lemma gate_eq {n : ℕ} (C : Circuit) (j s : ℕ) (hj : j < C.gates.length)
    (k : ℕ) (hk : k < (dropDup n C j s).gates.length) :
    (gateAt (dropDup n C j s) k).op = (gateAt C (oldIndex j k)).op := by
  have hlen := dropDup_length n C j s hj
  by_cases hkj : k < j
  · rw [dropDup_gateAt_lt n C j s k hj hkj]
    simp [oldIndex, hkj]
  · rw [dropDup_gateAt_ge n C j s k hj (by omega) (by omega)]
    simp [aliasGate, oldIndex, hkj]

lemma mapped_wire {n : ℕ} (j s k : ℕ) :
    aliasWire (n + j) s (n + oldIndex j k) = n + k := by
  unfold oldIndex aliasWire shiftDown
  split_ifs <;> omega

lemma mem_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) :
    j ∈ junk G C ↔ (gateAt C j).op = .and ∧ j < C.gates.length ∧
      ∃ x : Fin n → Bool, value C x (n + j) = true ∧ graphFun G ∅ x = false := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr h.2.1, h⟩

lemma junk_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j s : ℕ) (hj : j < C.gates.length) (hs : s < n + j)
    (heq : ∀ x : Fin n → Bool, value C x (n + j) = value C x s) :
    (junk G (dropDup n C j s)).card ≤ (junk G C).card := by
  classical
  have hlen := dropDup_length n C j s hj
  have hm : (junk G (dropDup n C j s)).image (oldIndex j) ⊆ junk G C := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    have hkd := (mem_junk G (dropDup n C j s) k).mp hk
    have hki := hkd.2.1
    have hi : oldIndex j k < C.gates.length := by unfold oldIndex; split_ifs <;> omega
    apply (mem_junk G C (oldIndex j k)).mpr
    refine ⟨?_, hi, ?_⟩
    · rw [← gate_eq C j s hj k hki]
      exact hkd.1
    · obtain ⟨x, hx, hg⟩ := hkd.2.2
      refine ⟨x, ?_, hg⟩
      have hw := wire_eq C j s hj hs heq x (n + oldIndex j k)
      rw [mapped_wire] at hw
      exact hw.trans hx
  have hc := Finset.card_le_card hm
  rw [Finset.card_image_of_injective _ (oldIndex_injective j)] at hc
  exact hc

lemma erase_family {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (J : Finset ℕ) (C : Circuit) (hC : IsAO2 n C)
    (hJ : J ⊆ Finset.range C.size) (s : ℕ)
    (hs : ∀ j ∈ J, s < n + j)
    (heq : ∀ j ∈ J, ∀ x : Fin n → Bool, value C x (n + j) = value C x s) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + J.card ≤ C.size ∧ (junk G D).card ≤ (junk G C).card := by
  classical
  induction J using Finset.strongInductionOn generalizing C
  rename_i J ih
  by_cases hne : J.Nonempty
  · let j := J.max' hne
    have hjJ : j ∈ J := Finset.max'_mem J hne
    have hj : j < C.gates.length := Finset.mem_range.mp (hJ hjJ)
    have hsj := hs j hjJ
    let E := dropDup n C j s
    have hE : IsAO2 n E := dropDup_ao n C j s hj hsj hC
    have hlen : E.size + 1 = C.size := dropDup_length n C j s hj
    have hklt : ∀ k ∈ J.erase j, k < j := by
      intro k hk
      have hm := Finset.le_max' J k (Finset.mem_of_mem_erase hk)
      have hn := (Finset.mem_erase.mp hk).1
      omega
    have hJE : J.erase j ⊆ Finset.range E.size := by
      intro k hk
      have hkj := hklt k hk
      apply Finset.mem_range.mpr
      change j < C.size at hj
      omega
    have heqE : ∀ k ∈ J.erase j, ∀ x : Fin n → Bool, value E x (n + k) = value E x s := by
      intro k hk x
      have hkj := hklt k hk
      have hwk := wire_eq C j s hj hsj (heq j hjJ) x (n + k)
      have hws := wire_eq C j s hj hsj (heq j hjJ) x s
      have hkmap : aliasWire (n + j) s (n + k) = n + k := by unfold aliasWire shiftDown; split_ifs <;> omega
      have hsmap : aliasWire (n + j) s s = s := by unfold aliasWire shiftDown; split_ifs <;> omega
      rw [hkmap] at hwk
      rw [hsmap] at hws
      exact hwk.symm.trans ((heq k (Finset.mem_of_mem_erase hk) x).trans hws)
    obtain ⟨D, hD, hf, hsz, hjunk⟩ := ih (J.erase j) (Finset.erase_ssubset hjJ) E hE hJE
      (fun k hk => hs k (Finset.mem_of_mem_erase hk)) heqE
    refine ⟨D, hD, hf.trans (function_eq C j s hj hsj (heq j hjJ)), ?_, ?_⟩
    · have hcard := Finset.card_erase_add_one hjJ
      omega
    · exact hjunk.trans (junk_le G C j s hj hsj (heq j hjJ))
  · have hz : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst J
    exact ⟨C, hC, rfl, by simp, le_rfl⟩

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.AliasErase

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.LeastGateLiveExtras

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma last_gate_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hpos : 0 < C.size) :
    C.output = n + (C.gates.length - 1) := by
  have hp : 0 < C.gates.length := hpos
  rcases LeastGateLive.output_or_later_reader G C hLeast (C.gates.length - 1) (by omega) with
    h | ⟨k, hlt, hk, _⟩
  · exact h
  · omega

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.LeastGateLiveExtras

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.DeadSet

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

def neutralize (C : Circuit) (J : Finset ℕ) : Circuit :=
  rewrite C (fun j => if j.val ∈ J then ⟨.and, [0, 0]⟩ else gateAt C j.val)

lemma length (C : Circuit) (J : Finset ℕ) : (neutralize C J).gates.length = C.gates.length :=
  rewrite_length C _

lemma size (C : Circuit) (J : Finset ℕ) : (neutralize C J).size = C.size :=
  rewrite_size C _

lemma gate (C : Circuit) (J : Finset ℕ) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (neutralize C J) j = if j ∈ J then ⟨.and, [0, 0]⟩ else gateAt C j :=
  rewrite_gate C _ j hj

lemma ao {n : ℕ} (C : Circuit) (J : Finset ℕ) (hn : 0 < n) (hC : IsAO2 n C) :
    IsAO2 n (neutralize C J) := by
  apply rewrite_ao C _
  · intro j
    split_ifs
    · exact Or.inl rfl
    · exact hC.1 _ (MixedColor.gateAt_mem j.isLt)
  · intro j
    split_ifs
    · rfl
    · exact hC.2.2 _ (MixedColor.gateAt_mem j.isLt)
  · intro j w hw
    split_ifs at hw
    · have hw0 : w = 0 := by simpa using hw
      omega
    · exact hC.2.1 j j.isLt w hw

lemma retained {n : ℕ} (C : Circuit) (J : Finset ℕ) (hn : 0 < n) (hC : IsAO2 n C)
    (hclosed : ∀ j, j < C.gates.length → j ∉ J → ∀ k ∈ J,
      n + k ∉ (gateAt C j).inputs) :
    ∀ x : Fin n → Bool, ∀ w, (w < n ∨ w - n ∉ J) →
      value (neutralize C J) x w = value C x w := by
  apply preserve_closed_wires C (neutralize C J) (length C J) hC.2.1 (ao C J hn hC).2.1
    (fun w => w < n ∨ w - n ∉ J)
  · intro j hj hp
    have hjn : j ∉ J := by simpa using hp
    rw [gate C J j hj, ite_eq_right hjn]
  · intro j hj hp i hi
    have hjn : j ∉ J := by simpa using hp
    by_cases hin : i < n
    · exact Or.inl hin
    · right
      intro hiJ
      have he : n + (i - n) = i := by omega
      exact hclosed j hj hjn (i - n) hiJ (by simpa only [he] using hi)

lemma aliases {n : ℕ} (C : Circuit) (J : Finset ℕ) (hn : 0 < n) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hjJ : j ∈ J) (x : Fin n → Bool) :
    value (neutralize C J) x (n + j) = value (neutralize C J) x 0 := by
  have hD := ao C J hn hC
  rw [value_gate _ hD.2.1 x j (by rw [length]; exact hj), gate C J j hj, ite_eq_left hjJ]
  simp [GateOp.eval]

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.DeadSet

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.AppendFactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

def appendGate (n : ℕ) (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g], n + C.gates.length⟩

lemma appendGate_length (n : ℕ) (C : Circuit) (g : Gate) :
    (appendGate n C g).gates.length = C.gates.length + 1 := by simp [appendGate]

lemma appendGate_size (n : ℕ) (C : Circuit) (g : Gate) :
    (appendGate n C g).size = C.size + 1 := by simp [Circuit.size, appendGate]

lemma appendGate_old (n : ℕ) (C : Circuit) (g : Gate) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (appendGate n C g) j = gateAt C j := by
  simp only [appendGate, gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma appendGate_last (n : ℕ) (C : Circuit) (g : Gate) :
    gateAt (appendGate n C g) C.gates.length = g := by
  simp [appendGate, gateAt, List.getD_eq_getElem?_getD]

lemma appendGate_ao {n : ℕ} (C : Circuit) (g : Gate) (hC : IsAO2 n C)
    (hop : g.op = .and ∨ g.op = .or) (h2 : g.inputs.length = 2)
    (hback : ∀ w ∈ g.inputs, w < n + C.gates.length) : IsAO2 n (appendGate n C g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hC.1 f hf
    · have he : f = g := by simpa using hf
      subst f
      exact hop
  · intro j hj w hw
    rw [appendGate_length] at hj
    by_cases hjl : j < C.gates.length
    · rw [appendGate_old n C g j hjl] at hw
      exact hC.2.1 j hjl w hw
    · have he : j = C.gates.length := by omega
      subst j
      rw [appendGate_last] at hw
      exact hback w hw
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hC.2.2 f hf
    · have he : f = g := by simpa using hf
      subst f
      exact h2

lemma appendGate_preserves {n : ℕ} (C : Circuit) (g : Gate) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + C.gates.length) :
    value (appendGate n C g) x w = value C x w := by
  unfold value
  rw [Splice.wires_eq_foldl, Splice.wires_eq_foldl]
  change ((C.gates ++ [g]).foldl Splice.stepWire (List.ofFn x)).getD w false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply Splice.stepWire_getD_lt
  rw [Splice.foldl_stepWire_length, List.length_ofFn]
  exact hw

lemma appendGate_value {n : ℕ} (C : Circuit) (g : Gate) (x : Fin n → Bool) :
    circuitFun n (appendGate n C g) x = g.op.eval (g.inputs.map (value C x)) := by
  change ((appendGate n C g).wires (List.ofFn x)).getD (n + C.gates.length) false = _
  rw [Splice.wires_eq_foldl]
  change ((C.gates ++ [g]).foldl Splice.stepWire (List.ofFn x)).getD (n + C.gates.length) false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hl : (C.gates.foldl Splice.stepWire (List.ofFn x)).length = n + C.gates.length := by
    rw [Splice.foldl_stepWire_length, List.length_ofFn]
  rw [← hl, Splice.stepWire_getD_len]
  rfl

lemma appendGate_output_valid (n : ℕ) (C : Circuit) (g : Gate) :
    (appendGate n C g).output < n + (appendGate n C g).gates.length := by
  simp [appendGate]

def orGate (a b : ℕ) : Gate := ⟨.or, [a, b]⟩

def andGate (a b : ℕ) : Gate := ⟨.and, [a, b]⟩

def appendOrs (n : ℕ) (C : Circuit) : List ℕ → Circuit
  | [] => C
  | w :: ws => appendOrs n (appendGate n C (orGate C.output w)) ws

lemma appendOrs_size (n : ℕ) (C : Circuit) (ws : List ℕ) :
    (appendOrs n C ws).size = C.size + ws.length := by
  induction ws generalizing C with
  | nil => simp [appendOrs]
  | cons w ws ih =>
    rw [appendOrs, ih, appendGate_size]
    simp only [List.length_cons]
    omega

lemma appendOrs_preserves {n : ℕ} (C : Circuit) (ws : List ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + C.gates.length) :
    value (appendOrs n C ws) x w = value C x w := by
  induction ws generalizing C with
  | nil => rfl
  | cons a ws ih =>
    rw [appendOrs, ih _ (by rw [appendGate_length]; omega)]
    exact appendGate_preserves C _ x w hw

lemma appendOrs_ao {n : ℕ} (C : Circuit) (ws : List ℕ) (hC : IsAO2 n C)
    (hout : C.output < n + C.gates.length)
    (hws : ∀ w ∈ ws, w < n + C.gates.length) : IsAO2 n (appendOrs n C ws) := by
  induction ws generalizing C with
  | nil => exact hC
  | cons w ws ih =>
    apply ih
    · apply appendGate_ao C (orGate C.output w) hC (Or.inr rfl) rfl
      intro i hi
      simp only [orGate, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi
      · subst i
        exact hout
      · subst i
        exact hws w (by simp)
    · exact appendGate_output_valid _ _ _
    · intro i hi
      rw [appendGate_length]
      have := hws i (by simp [hi])
      omega

lemma any_congr_on {α : Type*} (l : List α) (f g : α → Bool) :
    (∀ a ∈ l, f a = g a) → l.any f = l.any g := by
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro heq
    simp only [List.any_cons]
    rw [heq a (by simp), ih (fun b hb => heq b (by simp [hb]))]

lemma appendOrs_value {n : ℕ} (C : Circuit) (ws : List ℕ)
    (hws : ∀ w ∈ ws, w < n + C.gates.length) (x : Fin n → Bool) :
    circuitFun n (appendOrs n C ws) x =
      (circuitFun n C x || ws.any (fun w => value C x w)) := by
  induction ws generalizing C with
  | nil => simp [appendOrs]
  | cons w ws ih =>
    rw [appendOrs, ih _ (by
      intro i hi
      rw [appendGate_length]
      have := hws i (by simp [hi])
      omega)]
    rw [appendGate_value]
    simp only [orGate, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
    have heq : ws.any (fun i => value (appendGate n C (orGate C.output w)) x i) =
        ws.any (fun i => value C x i) := by
      apply any_congr_on
      intro i hi
      rw [appendGate_preserves C _ x i (hws i (by simp [hi]))]
    simp only [orGate] at heq
    rw [heq]
    exact Bool.or_assoc _ _ _

def factor (n : ℕ) (C : Circuit) (h a b : ℕ) : Circuit :=
  let D := appendGate n C (orGate a b)
  appendGate n D (andGate h D.output)

def appendFactorOr (n : ℕ) (C : Circuit) (h a b : ℕ) (rest : List ℕ) : Circuit :=
  appendOrs n (factor n C h a b) rest

lemma factor_size (n : ℕ) (C : Circuit) (h a b : ℕ) :
    (factor n C h a b).size = C.size + 2 := by
  simp [factor, appendGate_size]

lemma factor_preserves {n : ℕ} (C : Circuit) (h a b : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + C.gates.length) :
    value (factor n C h a b) x w = value C x w := by
  unfold factor
  rw [appendGate_preserves _ _ x w (by rw [appendGate_length]; omega), appendGate_preserves C _ x w hw]

lemma factor_ao {n : ℕ} (C : Circuit) (h a b : ℕ) (hC : IsAO2 n C)
    (hh : h < n + C.gates.length) (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    IsAO2 n (factor n C h a b) := by
  have hD : IsAO2 n (appendGate n C (orGate a b)) := by
    apply appendGate_ao C _ hC (Or.inr rfl) rfl
    intro w hw
    simp only [orGate, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> assumption
  apply appendGate_ao _ _ hD (Or.inl rfl) rfl
  intro w hw
  simp only [andGate, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · rw [appendGate_length]
    omega
  · exact appendGate_output_valid _ _ _

lemma factor_output_valid (n : ℕ) (C : Circuit) (h a b : ℕ) :
    (factor n C h a b).output < n + (factor n C h a b).gates.length :=
  appendGate_output_valid _ _ _

lemma factor_value {n : ℕ} (C : Circuit) (h a b : ℕ)
    (hh : h < n + C.gates.length) (x : Fin n → Bool) :
    circuitFun n (factor n C h a b) x =
      (value C x h && (value C x a || value C x b)) := by
  unfold factor
  rw [appendGate_value]
  simp only [andGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true]
  rw [appendGate_preserves C _ x h hh]
  change (value C x h && circuitFun n (appendGate n C (orGate a b)) x) = _
  rw [appendGate_value]
  simp [orGate, GateOp.eval]

lemma appendFactorOr_size (n : ℕ) (C : Circuit) (h a b : ℕ) (rest : List ℕ) :
    (appendFactorOr n C h a b rest).size = C.size + 2 + rest.length := by
  rw [appendFactorOr, appendOrs_size, factor_size]

lemma appendFactorOr_preserves {n : ℕ} (C : Circuit) (h a b : ℕ) (rest : List ℕ)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + C.gates.length) :
    value (appendFactorOr n C h a b rest) x w = value C x w := by
  rw [appendFactorOr, appendOrs_preserves _ _ x w (by
    change w < n + (factor n C h a b).size
    rw [factor_size]
    change w < n + C.size at hw
    omega)]
  exact factor_preserves C h a b x w hw

lemma appendFactorOr_ao {n : ℕ} (C : Circuit) (h a b : ℕ) (rest : List ℕ) (hC : IsAO2 n C)
    (hh : h < n + C.gates.length) (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (hrest : ∀ w ∈ rest, w < n + C.gates.length) : IsAO2 n (appendFactorOr n C h a b rest) := by
  apply appendOrs_ao _ _ (factor_ao C h a b hC hh ha hb) (factor_output_valid _ _ _ _ _)
  intro w hw
  change w < n + (factor n C h a b).size
  rw [factor_size]
  have := hrest w hw
  change w < n + C.size at this
  omega

lemma appendFactorOr_value {n : ℕ} (C : Circuit) (h a b : ℕ) (rest : List ℕ)
    (hh : h < n + C.gates.length) (hrest : ∀ w ∈ rest, w < n + C.gates.length)
    (x : Fin n → Bool) :
    circuitFun n (appendFactorOr n C h a b rest) x =
      ((value C x h && (value C x a || value C x b)) || rest.any (fun w => value C x w)) := by
  rw [appendFactorOr, appendOrs_value _ _ (by
    intro w hw
    change w < n + (factor n C h a b).size
    rw [factor_size]
    have := hrest w hw
    change w < n + C.size at this
    omega), factor_value C h a b hh x]
  congr 1
  apply any_congr_on
  intro w hw
  exact factor_preserves C h a b x w (hrest w hw)

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.AppendFactor

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.AppendFactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma and_partner {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
    ∃ v, v ∈ (gateAt C j).inputs ∧ w < n + j ∧ v < n + j ∧
      ∀ x : Fin n → Bool, value C x (n + j) = (value C x w && value C x v) := by
  have hwb := hC.2.1 j hj w hw
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hC.2.2 _ (MixedColor.gateAt_mem hj))
  have hw' : w = a ∨ w = b := by simpa [hab] using hw
  rcases hw' with rfl | rfl
  · have hbm : b ∈ (gateAt C j).inputs := by simp [hab]
    refine ⟨b, hbm, hwb, hC.2.1 j hj b hbm, ?_⟩
    intro x
    rw [value_gate C hC.2.1 x j hj, hop, hab]
    simp [GateOp.eval]
  · have ham : a ∈ (gateAt C j).inputs := by simp [hab]
    refine ⟨a, ham, hwb, hC.2.1 j hj a ham, ?_⟩
    intro x
    rw [value_gate C hC.2.1 x j hj, hop, hab]
    simp [GateOp.eval, Bool.and_comm]

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.AppendFactor

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.TopFrontierIdentity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership SemanticPurity

lemma wire_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (w : ℕ)
    (hbelow : ∀ y : Fin n → Bool, W n C w y = true → graphFun G ∅ y = true)
    (x : Fin n → Bool) :
    W n C w x = true ↔ ∃ j ∈ TopFrontier.leaves (n := n) C w, gateVal n C j x = true := by
  classical
  constructor
  · intro hx
    obtain ⟨j,hj,hop,hpath,htrue⟩ := TopFrontierCoverage.true_below_reaches_and G C hAO x w hbelow hx
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hop,hpath⟩,htrue⟩
  · rintro ⟨j,hj,htrue⟩
    obtain ⟨_,_,hpath⟩ := Finset.mem_filter.mp hj
    exact MixedColor.orStep_up (by simp) hpath htrue

lemma output_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (x : Fin n → Bool) : circuitFun n C x = true ↔
      ∃ j ∈ TopFrontier.leaves (n := n) C C.output, gateVal n C j x = true := by
  apply wire_true_iff G C hAO C.output
  intro y hy
  change circuitFun n C y = true at hy
  simpa only [hfun] using hy

lemma output_eq_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (x : Fin n → Bool) : circuitFun n C x =
      (TopFrontier.leaves (n := n) C C.output).toList.any (fun j => gateVal n C j x) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [List.any_eq_true,Finset.mem_toList] using output_true_iff G C hAO hfun x

lemma clean_wire_has_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) (hw : w < n+C.gates.length)
    (hbelow : ∀ y : Fin n → Bool, W n C w y = true → graphFun G ∅ y = true) :
    ∃ j ∈ tops G C, Relation.ReflTransGen (MixedColor.OrStep n C) w (n+j) := by
  classical
  obtain ⟨j,hj,hop,hpath,_⟩ := TopFrontierCoverage.true_below_reaches_and G C hAO
    (fun _ => true) w hbelow (wire_one C hAO w hw)
  refine ⟨j,?_,hpath⟩
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range]
  exact ⟨hj,hop,TopFrontierCoverage.reached_below G C w j hbelow hpath⟩

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.TopFrontierIdentity

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.CommonTopClosure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership SemanticPurity

lemma or_path_cone {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) {w i : ℕ}
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) w (n+i)) :
    ∃ j, w = n+j ∧ (i = j ∨ InCone n C i j) := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨i,rfl,Or.inl rfl⟩
  | head hs _ ih =>
    obtain ⟨k,hk,rfl,_,hw,_⟩ := hs
    obtain ⟨j,rfl,hi⟩ := ih
    exact ⟨k,rfl,Or.inr (JunkPurity.cone_step C hAO hk hw hi)⟩

lemma top_path_not_and_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {i k w : ℕ} (hi : i < C.gates.length) (hia : (gateAt C i).op = .and)
    (hic : BelowF G C i) (hk : k < C.gates.length) (hka : (gateAt C k).op = .and)
    (hw : w ∈ (gateAt C k).inputs)
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) w (n+i)) : False := by
  obtain ⟨j,rfl,hcone⟩ := or_path_cone C hAO hp
  exact hTF i hi k hk hia hic hka (JunkPurity.cone_step C hAO hk hw hcone)

lemma above_top_reaches_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {i j : ℕ} (hi : i < C.gates.length) (hia : (gateAt C i).op = .and)
    (hic : BelowF G C i) (hj : j < C.gates.length)
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) (n+j) (n+i)) :
    Relation.ReflTransGen (MixedColor.OrStep n C) C.output (n+j) := by
  rcases JunkPurity.reaches_and_or_output C hLeast.1
      (LeastGateLive.output_or_later_reader G C hLeast) j hj with ho | ⟨k,w,hk,hka,hw,hpath⟩
  · exact ho
  · exact (top_path_not_and_input G C hLeast.1 hTF hi hia hic hk hka hw
      (hpath.trans hp)).elim

lemma top_reaches_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {i : ℕ} (hi : i ∈ tops G C) :
    Relation.ReflTransGen (MixedColor.OrStep n C) C.output (n+i) := by
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hi
  exact above_top_reaches_output G C hLeast hTF hi.1 hi.2.1 hi.2.2 hi.1 .refl

lemma tops_eq_output_frontier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C) :
    tops G C = TopFrontier.leaves (n := n) C C.output := by
  classical
  ext i
  constructor
  · intro hi
    have hp := top_reaches_output G C hLeast hTF hi
    simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi.1,hi.2.1,hp⟩
  · intro hi
    have hic := TopFrontier.leaf_below G C C.output i (by
      intro x hx
      change circuitFun n C x = true at hx
      simpa only [hLeast.2.1] using hx) hi
    obtain ⟨hib,hia,_⟩ := Finset.mem_filter.mp hi
    simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range]
    exact ⟨Finset.mem_range.mp hib,hia,hic⟩

lemma clean_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {i j : ℕ} (hi : i < C.gates.length) (hic : BelowF G C i)
    (hj : j < C.gates.length) (hread : n+i ∈ (gateAt C j).inputs) :
    (gateAt C j).op = .or ∧ BelowF G C j := by
  have hjo : (gateAt C j).op = .or := by
    rcases hLeast.1.1 _ (MixedColor.gateAt_mem hj) with ha | ho
    · exact (AndChild.not_below G C hLeast j (n+i) hj ha hread hic).elim
    · exact ho
  obtain ⟨k,hk,hp⟩ := TopFrontierIdentity.clean_wire_has_top G C hLeast.1 (n+i) (by omega) hic
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hk
  have hstep : MixedColor.OrStep n C (n+j) (n+i) :=
    ⟨j,hj,rfl,hjo,hread,hLeast.1.2.1 j hj _ hread⟩
  have hout := above_top_reaches_output G C hLeast hTF hk.1 hk.2.1 hk.2.2 hj
    (Relation.ReflTransGen.head hstep hp)
  refine ⟨hjo,?_⟩
  intro x hx
  have ho : circuitFun n C x = true := MixedColor.orStep_up (by simp) hout hx
  simpa only [hLeast.2.1] using ho

lemma clean_reader_mem_orT {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {i j : ℕ} (hi : i < C.gates.length) (hic : BelowF G C i)
    (hj : j < C.gates.length) (hread : n+i ∈ (gateAt C j).inputs) : j ∈ orT G C := by
  classical
  simp only [orT,gatesWhere,Finset.mem_filter,Finset.mem_range]
  exact ⟨hj,clean_reader G C hLeast hTF hi hic hj hread⟩

lemma clean_set_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C) (J : Finset ℕ)
    (hOR : orT G C ⊆ J) (hclean : ∀ i ∈ J, i < C.gates.length ∧ BelowF G C i)
    {j : ℕ} (hj : j < C.gates.length) (hjJ : j ∉ J) :
    ∀ i ∈ J, n+i ∉ (gateAt C j).inputs := by
  intro i hi hread
  obtain ⟨hib,hic⟩ := hclean i hi
  exact hjJ (hOR (clean_reader_mem_orT G C hLeast hTF hib hic hj hread))

lemma common_top_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {a b : ℕ} (ha : a ∈ tops G C) (hb : b ∈ tops G C)
    {j : ℕ} (hj : j < C.gates.length) (hjJ : j ∉ orT G C ∪ {a,b}) :
    ∀ i ∈ orT G C ∪ {a,b}, n+i ∉ (gateAt C j).inputs := by
  classical
  apply clean_set_closed G C hLeast hTF (orT G C ∪ {a,b}) Finset.subset_union_left _ hj hjJ
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · simp only [orT,gatesWhere,Finset.mem_filter,Finset.mem_range] at hi
    exact ⟨hi.1,hi.2.2⟩
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at ha
      exact ⟨ha.1,ha.2.2⟩
    · simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hb
      exact ⟨hb.1,hb.2.2⟩

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.CommonTopClosure

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.CommonTopSets

lemma mem_remaining (T : Finset ℕ) (a b x : ℕ) :
    x ∈ (T.erase a).erase b ↔ x ∈ T ∧ x ≠ a ∧ x ≠ b := by
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hxb, hxa, hxT⟩
    exact ⟨hxT, hxa, hxb⟩
  · rintro ⟨hxT, hxa, hxb⟩
    exact ⟨hxb, hxa, hxT⟩

lemma remaining_card (T : Finset ℕ) (a b : ℕ)
    (hab : a ≠ b) (ha : a ∈ T) (hb : b ∈ T) :
    ((T.erase a).erase b).card + 2 = T.card := by
  have hba : b ∈ T.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have h1 := Finset.card_erase_add_one ha
  have h2 := Finset.card_erase_add_one hba
  omega

lemma selected_card (T O : Finset ℕ) (a b : ℕ)
    (hab : a ≠ b) (ha : a ∈ T) (hb : b ∈ T) (hdis : Disjoint T O) :
    (O ∪ {a, b}).card = O.card + 2 := by
  have hpair : Disjoint O ({a, b} : Finset ℕ) := by
    apply Finset.disjoint_left.mpr
    intro x hxO hxab
    have hxT : x ∈ T := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxab
      rcases hxab with rfl | rfl <;> assumption
    exact Finset.disjoint_left.mp hdis hxT hxO
  rw [Finset.card_union_of_disjoint hpair]
  simp [hab]

lemma remaining_disjoint_selected (T O : Finset ℕ) (a b : ℕ) (hdis : Disjoint T O) :
    Disjoint ((T.erase a).erase b) (O ∪ {a, b}) := by
  apply Finset.disjoint_left.mpr
  intro x hxR hxJ
  obtain ⟨hxT, hxa, hxb⟩ := (mem_remaining T a b x).mp hxR
  rcases Finset.mem_union.mp hxJ with hxO | hxab
  · exact Finset.disjoint_left.mp hdis hxT hxO
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxab
    exact hxab.elim hxa hxb

lemma cardinal_budget (T O : Finset ℕ) (a b : ℕ)
    (hab : a ≠ b) (ha : a ∈ T) (hb : b ∈ T) (hdis : Disjoint T O)
    (hbound : T.card ≤ O.card + 1) :
    2 + ((T.erase a).erase b).card + 1 ≤ (O ∪ {a, b}).card := by
  have hT := remaining_card T a b hab ha hb
  have hJ := selected_card T O a b hab ha hb hdis
  omega

lemma mem_decomposition (T : Finset ℕ) (a b x : ℕ) (ha : a ∈ T) (hb : b ∈ T) :
    x ∈ T ↔ x = a ∨ x = b ∨ x ∈ (T.erase a).erase b := by
  constructor
  · intro hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr (Or.inl hxb)
    exact Or.inr (Or.inr ((mem_remaining T a b x).mpr ⟨hx, hxa, hxb⟩))
  · rintro (rfl | rfl | hx)
    · exact ha
    · exact hb
    · exact ((mem_remaining T a b x).mp hx).1

lemma exists_decomposition (T : Finset ℕ) (a b : ℕ) (ha : a ∈ T) (hb : b ∈ T)
    (P : ℕ → Prop) :
    (∃ x ∈ T, P x) ↔ P a ∨ P b ∨ ∃ x ∈ (T.erase a).erase b, P x := by
  constructor
  · rintro ⟨x, hx, hp⟩
    rcases (mem_decomposition T a b x ha hb).mp hx with rfl | rfl | hxR
    · exact Or.inl hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr ⟨x, hxR, hp⟩)
  · rintro (hp | hp | ⟨x, hxR, hp⟩)
    · exact ⟨a, ha, hp⟩
    · exact ⟨b, hb, hp⟩
    · exact ⟨x, ((mem_remaining T a b x).mp hxR).1, hp⟩

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.CommonTopSets

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.CommonTopFactorIdentity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma any_decomposition (T : Finset ℕ) (i j : ℕ) (hi : i ∈ T) (hj : j ∈ T) (f : ℕ → Bool) :
    T.toList.any f = ((f i || f j) || ((T.erase i).erase j).toList.any f) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [List.any_eq_true,Finset.mem_toList,Bool.or_eq_true,or_assoc] using
    CommonTopSets.exists_decomposition T i j hi hj (fun k => f k = true)

lemma factor_output_profiles {n : ℕ} (C : Circuit) (T : Finset ℕ) (i j H A B : ℕ)
    (hi : i ∈ T) (hj : j ∈ T)
    (houtput : ∀ x : Fin n → Bool, circuitFun n C x = T.toList.any (fun k => gateVal n C k x))
    (hival : ∀ x : Fin n → Bool, gateVal n C i x = (value C x H && value C x A))
    (hjval : ∀ x : Fin n → Bool, gateVal n C j x = (value C x H && value C x B)) :
    ∀ x : Fin n → Bool, circuitFun n C x =
      ((value C x H && (value C x A || value C x B)) ||
        (((T.erase i).erase j).toList.map (fun k => n+k)).any (value C x)) := by
  intro x
  rw [houtput,any_decomposition T i j hi hj,hival,hjval]
  simp only [List.any_map]
  change (((value C x H && value C x A) || (value C x H && value C x B)) ||
      ((T.erase i).erase j).toList.any (fun k => value C x (n+k))) =
    ((value C x H && (value C x A || value C x B)) ||
      ((T.erase i).erase j).toList.any (fun k => value C x (n+k)))
  cases value C x H <;> simp

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.CommonTopFactorIdentity

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.TopFactorCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma factor_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (J : Finset ℕ) (hn : 0 < n) (hC : IsAO2 n C)
    (hJ : J ⊆ Finset.range C.size)
    (hclosed : ∀ j, j < C.gates.length → j ∉ J → ∀ k ∈ J,
      n + k ∉ (gateAt C j).inputs)
    (h a b : ℕ) (rest : List ℕ)
    (hh : h < n + C.gates.length) (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (hrest : ∀ w ∈ rest, w < n + C.gates.length)
    (hkeep : h < n ∨ h - n ∉ J) (hkeepa : a < n ∨ a - n ∉ J)
    (hkeepb : b < n ∨ b - n ∉ J)
    (hkeepr : ∀ w ∈ rest, w < n ∨ w - n ∉ J)
    (houtput : ∀ x : Fin n → Bool, circuitFun n C x =
      ((value C x h && (value C x a || value C x b)) || rest.any (fun w => value C x w)))
    (hbudget : 2 + rest.length + 1 ≤ J.card) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧ D.size + 1 ≤ C.size := by
  classical
  let B := DeadSet.neutralize C J
  let E := AppendFactor.appendFactorOr n B h a b rest
  have hB : IsAO2 n B := DeadSet.ao C J hn hC
  have hlen : B.gates.length = C.gates.length := DeadSet.length C J
  have hE : IsAO2 n E := AppendFactor.appendFactorOr_ao B h a b rest hB
    (by simpa only [hlen] using hh) (by simpa only [hlen] using ha)
    (by simpa only [hlen] using hb) (fun w hw => by simpa only [hlen] using hrest w hw)
  have hsize : E.size = C.size + 2 + rest.length := by
    rw [AppendFactor.appendFactorOr_size, DeadSet.size]
  have hpres : ∀ x : Fin n → Bool, ∀ w, (w < n ∨ w - n ∉ J) →
      value B x w = value C x w := DeadSet.retained C J hn hC hclosed
  have hfun : circuitFun n E = circuitFun n C := by
    funext x
    rw [AppendFactor.appendFactorOr_value B h a b rest (by simpa only [hlen] using hh)
      (fun w hw => by simpa only [hlen] using hrest w hw) x]
    have hr : rest.any (fun w => value B x w) = rest.any (fun w => value C x w) := by
      have hm : rest.map (fun w => value B x w) = rest.map (fun w => value C x w) :=
        List.map_congr_left (fun w hw => hpres x w (hkeepr w hw))
      simpa only [List.any_map, Function.comp_def, id_eq] using congrArg (fun xs : List Bool => xs.any id) hm
    rw [hpres x h hkeep, hpres x a hkeepa, hpres x b hkeepb, hr]
    exact (houtput x).symm
  have hJE : J ⊆ Finset.range E.size := by
    intro j hj
    have hjC := Finset.mem_range.mp (hJ hj)
    apply Finset.mem_range.mpr
    omega
  have halias : ∀ j ∈ J, ∀ x : Fin n → Bool, value E x (n + j) = value E x 0 := by
    intro j hj x
    have hjC : j < C.gates.length := Finset.mem_range.mp (hJ hj)
    have hval := DeadSet.aliases C J hn hC j hjC hj x
    have hw : n + j < n + B.gates.length := by rw [hlen]; omega
    have hz : 0 < n + B.gates.length := by omega
    rw [AppendFactor.appendFactorOr_preserves B h a b rest x (n + j) hw,
      AppendFactor.appendFactorOr_preserves B h a b rest x 0 hz]
    exact hval
  obtain ⟨D, hD, hf, hs, _⟩ := AliasErase.erase_family G J E hE hJE 0
    (fun j _ => by omega) halias
  refine ⟨D, hD, hf.trans hfun, ?_⟩
  omega

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.TopFactorCompiler

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.CommonTopFactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma no_shared_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {i j : ℕ} (hi : i ∈ tops G C) (hj : j ∈ tops G C) (hij : i ≠ j)
    (w : ℕ) (hwi : w ∈ (gateAt C i).inputs) : w ∉ (gateAt C j).inputs := by
  classical
  intro hwj
  have hi' := hi
  have hj' := hj
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hi' hj'
  obtain ⟨a,hai,hwiB,haB,hival⟩ := AppendFactor.and_partner C hLeast.1 i hi'.1 hi'.2.1 w hwi
  obtain ⟨b,hbj,_,hbB,hjval⟩ := AppendFactor.and_partner C hLeast.1 j hj'.1 hj'.2.1 w hwj
  have hpos : 0 < C.gates.length := by omega
  have hn : 0 < n := by
    obtain ⟨u,v,huv⟩ := MixedColor.binaryInputs hLeast.1 hpos
    have hu := hLeast.1.2.1 0 hpos u (by simp [huv])
    omega
  have hout : C.output < n + C.gates.length := by
    rw [LeastGateLiveExtras.last_gate_output G C hLeast hpos]
    omega
  let J := orT G C ∪ {i,j}
  let R := ((tops G C).erase i).erase j
  let rest := R.toList.map (fun k => n+k)
  have hclean : ∀ k ∈ J, k < C.gates.length ∧ BelowF G C k := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · simp only [orT,gatesWhere,Finset.mem_filter,Finset.mem_range] at hk
      exact ⟨hk.1,hk.2.2⟩
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact ⟨hi'.1,hi'.2.2⟩
      · exact ⟨hj'.1,hj'.2.2⟩
  have hJ : J ⊆ Finset.range C.size := by
    intro k hk
    exact Finset.mem_range.mpr (hclean k hk).1
  have hclosed : ∀ k, k < C.gates.length → k ∉ J →
      ∀ l ∈ J, n+l ∉ (gateAt C k).inputs := by
    intro k hk hkJ
    exact CommonTopClosure.common_top_closed G C hLeast hTF hi hj hk hkJ
  have hkeep : ∀ k, k < C.gates.length → (gateAt C k).op = .and →
      ∀ u ∈ (gateAt C k).inputs, u < n ∨ u-n ∉ J := by
    intro k hk hka u hu
    by_cases hun : u < n
    · exact Or.inl hun
    · right
      intro huJ
      have huc := (hclean (u-n) huJ).2
      apply AndChild.not_below G C hLeast k u hk hka hu
      intro x hx
      apply huc x
      change value C x (n+(u-n)) = true
      change value C x u = true at hx
      have heq : n+(u-n) = u := by omega
      simpa only [heq] using hx
  have hdis : Disjoint (tops G C) (orT G C) := by
    apply Finset.disjoint_left.mpr
    intro k hkT hkO
    simp only [tops,orT,gatesWhere,Finset.mem_filter,Finset.mem_range] at hkT hkO
    have hf := hkT.2.1.symm.trans hkO.2.1
    cases hf
  have hRdis : Disjoint R J := CommonTopSets.remaining_disjoint_selected _ _ i j hdis
  have hrest : ∀ u ∈ rest, u < n + C.gates.length := by
    intro u hu
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hu
    have hkT := ((CommonTopSets.mem_remaining (tops G C) i j k).mp (Finset.mem_toList.mp hk)).1
    simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hkT
    omega
  have hkeepr : ∀ u ∈ rest, u < n ∨ u-n ∉ J := by
    intro u hu
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hu
    right
    simpa only [Nat.add_sub_cancel_left] using
      (Finset.disjoint_left.mp hRdis (Finset.mem_toList.mp hk))
  have houtput : ∀ x : Fin n → Bool, circuitFun n C x =
      ((value C x w && (value C x a || value C x b)) || rest.any (value C x)) := by
    apply CommonTopFactorIdentity.factor_output_profiles C (tops G C) i j w a b hi hj
    · intro x
      rw [CommonTopClosure.tops_eq_output_frontier G C hLeast hTF]
      exact TopFrontierIdentity.output_eq_or G C hLeast.1 hLeast.2.1 x
    · exact hival
    · exact hjval
  have hbound : (tops G C).card ≤ (orT G C).card + 1 := by
    rw [CommonTopClosure.tops_eq_output_frontier G C hLeast hTF]
    apply TopFrontier.leaves_card_le_orT G C hLeast.1 C.output hout
    intro x hx
    change circuitFun n C x = true at hx
    simpa only [hLeast.2.1] using hx
  have hbudget : 2 + rest.length + 1 ≤ J.card := by
    simpa only [rest,List.length_map,Finset.length_toList] using
      CommonTopSets.cardinal_budget (tops G C) (orT G C) i j hij hi hj hdis hbound
  obtain ⟨D,hD,hfun,hsize⟩ := TopFactorCompiler.factor_closed G C J hn hLeast.1 hJ hclosed
    w a b rest (by omega) (by omega) (by omega) hrest
    (hkeep i hi'.1 hi'.2.1 w hwi) (hkeep i hi'.1 hi'.2.1 a hai)
    (hkeep j hj'.1 hj'.2.1 b hbj) hkeepr houtput hbudget
  have hmin := hLeast.2.2 D hD (hfun.trans hLeast.2.1)
  omega

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.CommonTopFactor

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.MaxDirtyConsumer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma reader_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) {q : ℕ} (hdirty : ¬ BelowF G C q)
    (hmax : ∀ k, q < k → k < C.gates.length → BelowF G C k)
    {j : ℕ} (hj : j < C.gates.length) (hread : n+q ∈ (gateAt C j).inputs) :
    q < j ∧ j ∈ tops G C := by
  classical
  have hqj : q < j := by have := hAO.2.1 j hj _ hread; omega
  have hjc := hmax j hqj hj
  have hja : (gateAt C j).op = .and := by
    rcases hAO.1 _ (MixedColor.gateAt_mem hj) with ha | ho
    · exact ha
    · exfalso
      apply hdirty
      intro x hx
      apply hjc x
      exact (MixedColor.val_or (n := n) (C := C) (x := List.ofFn x) (by simp) hj ho).mpr
        ⟨n+q,hread,hAO.2.1 j hj _ hread,hx⟩
  refine ⟨hqj,?_⟩
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range]
  exact ⟨hj,hja,hjc⟩

lemma clean_reader_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) {q j : ℕ} (hdirty : ¬ BelowF G C q)
    (hj : j < C.gates.length) (hjc : BelowF G C j) (hja : (gateAt C j).op = .and)
    (hread : n+q ∈ (gateAt C j).inputs) : (gateAt C j).inputs.count (n+q) = 1 := by
  obtain ⟨a,b,hab⟩ := MixedColor.binaryInputs hAO hj
  have hmem : n+q = a ∨ n+q = b := by simpa [hab] using hread
  have hne : a ≠ b := by
    intro heq
    subst b
    have hqa : n+q = a := hmem.elim id id
    apply hdirty
    intro x hx
    apply hjc x
    change value C x (n+j) = true
    rw [value_gate C hAO.2.1 x j hj,hja,hab,← hqa]
    change value C x (n+q) = true at hx
    simp [GateOp.eval,hx]
  rw [hab]
  rcases hmem with hqa | hqb
  · rw [← hqa] at hne ⊢
    simp [hne]
  · rw [← hqb] at hne ⊢
    simp [hne,hne.symm]

lemma dirty_not_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfun : circuitFun n C = graphFun G ∅)
    {q : ℕ} (hdirty : ¬ BelowF G C q) : C.output ≠ n+q := by
  intro hout
  apply hdirty
  intro x hx
  have hc : circuitFun n C x = true := by
    change value C x C.output = true
    rw [hout]
    exact hx
  simpa only [hfun] using hc

lemma unique_consumer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {q : ℕ} (hq : q < C.gates.length) (hdirty : ¬ BelowF G C q)
    (hmax : ∀ k, q < k → k < C.gates.length → BelowF G C k) :
    ∃ j, q < j ∧ j < C.gates.length ∧ j ∈ tops G C ∧
      (gateAt C j).inputs.count (n+q) = 1 ∧
      ∀ k, k < C.gates.length → n+q ∈ (gateAt C k).inputs → k = j := by
  classical
  have hnotout := dirty_not_output G C hLeast.2.1 hdirty
  obtain ⟨j,hqj,hj,hread⟩ := (LeastGateLive.output_or_later_reader G C hLeast q hq).resolve_left hnotout
  have hjtop := (reader_top G C hLeast.1 hdirty hmax hj hread).2
  have hj' := hjtop
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hj'
  refine ⟨j,hqj,hj,hjtop,clean_reader_count G C hLeast.1 hdirty hj hj'.2.2 hj'.2.1 hread,?_⟩
  intro k hk hkr
  by_contra hkj
  have hktop := (reader_top G C hLeast.1 hdirty hmax hk hkr).2
  exact CommonTopFactor.no_shared_operand G C hLeast hTF hktop hjtop hkj (n+q) hkr hread

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.MaxDirtyConsumer

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.MaxDirtyConsumerExtras

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma earlier_partner {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) {q : ℕ} (hdirty : ¬ BelowF G C q)
    (hmax : ∀ k, q < k → k < C.gates.length → BelowF G C k)
    {j : ℕ} (hj : j < C.gates.length) (hread : n+q ∈ (gateAt C j).inputs) :
    ∃ r, r < n+q ∧ r ≠ n+q ∧ r ∈ (gateAt C j).inputs ∧
      ((gateAt C j).inputs = [n+q,r] ∨ (gateAt C j).inputs = [r,n+q]) ∧
      ∀ x : Fin n → Bool, value C x (n+j) = (value C x (n+q) && value C x r) := by
  classical
  have hjtop := (MaxDirtyConsumer.reader_top G C hLeast.1 hdirty hmax hj hread).2
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hjtop
  have hcount := MaxDirtyConsumer.clean_reader_count G C hLeast.1 hdirty hj hjtop.2.2 hjtop.2.1 hread
  obtain ⟨a,b,hab⟩ := MixedColor.binaryInputs hLeast.1 hj
  have hmem : n+q = a ∨ n+q = b := by simpa [hab] using hread
  obtain ⟨r,hshape⟩ : ∃ r, (gateAt C j).inputs = [n+q,r] ∨
      (gateAt C j).inputs = [r,n+q] := by
    rcases hmem with hqa | hqb
    · exact ⟨b,Or.inl (hqa ▸ hab)⟩
    · exact ⟨a,Or.inr (hqb ▸ hab)⟩
  have hrmem : r ∈ (gateAt C j).inputs := by
    rcases hshape with hs | hs <;> simp [hs]
  have hrne : r ≠ n+q := by
    intro heq
    subst r
    have hs : (gateAt C j).inputs = [n+q,n+q] := hshape.elim id id
    simp [hs] at hcount
  have hrl : r < n+q := by
    by_contra hrl
    have hnr : n ≤ r := by omega
    have hqr : q < r-n := by omega
    have hrback := hLeast.1.2.1 j hj r hrmem
    have hrc := hmax (r-n) hqr (by omega)
    apply AndChild.not_below G C hLeast j r hj hjtop.2.1 hrmem
    intro x hx
    apply hrc x
    change value C x (n+(r-n)) = true
    change value C x r = true at hx
    have heq : n+(r-n) = r := by omega
    simpa only [heq] using hx
  refine ⟨r,hrl,hrne,hrmem,hshape,?_⟩
  intro x
  rw [value_gate C hLeast.1.2.1 x j hj,hjtop.2.1]
  rcases hshape with hs | hs <;> simp [hs,GateOp.eval,Bool.and_comm]

lemma private_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {q : ℕ} (hq : q < C.gates.length) (hdirty : ¬ BelowF G C q)
    (hmax : ∀ k, q < k → k < C.gates.length → BelowF G C k) :
    ∃ j r, q < j ∧ j < C.gates.length ∧ j ∈ tops G C ∧ r < n+q ∧ r ≠ n+q ∧
      ((gateAt C j).inputs = [n+q,r] ∨ (gateAt C j).inputs = [r,n+q]) ∧
      (∀ x : Fin n → Bool, value C x (n+j) = (value C x (n+q) && value C x r)) ∧
      C.output ≠ n+q ∧
      (∀ k, k < C.gates.length → k ≠ j → n+q ∉ (gateAt C k).inputs) ∧
      (gateAt C j).inputs.count (n+q) = 1 := by
  obtain ⟨j,hqj,hj,hjt,hcount,hu⟩ := MaxDirtyConsumer.unique_consumer G C hLeast hTF hq hdirty hmax
  have hread : n+q ∈ (gateAt C j).inputs := by
    by_contra hnot
    have hz := List.count_eq_zero.mpr hnot
    omega
  obtain ⟨r,hr,hrne,_,hshape,hvalue⟩ := earlier_partner G C hLeast hdirty hmax hj hread
  refine ⟨j,r,hqj,hj,hjt,hr,hrne,hshape,hvalue,
    MaxDirtyConsumer.dirty_not_output G C hLeast.2.1 hdirty,?_,hcount⟩
  intro k hk hkj hkr
  exact hkj (hu k hk hkr)

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.MaxDirtyConsumerExtras

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.LastDirtyAndFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma path_true {n : ℕ} {C : Circuit} {q w : ℕ}
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) w (n+q))
    (x : Fin n → Bool) (hx : gateVal n C q x = true) : value C x w = true :=
  MixedColor.orStep_up (by simp) hp hx

lemma partner_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) {q j w r : ℕ}
    (hj : j < C.gates.length) (hja : (gateAt C j).op = .and) (hjc : BelowF G C j)
    (hinputs : (gateAt C j).inputs = [w,r] ∨ (gateAt C j).inputs = [r,w])
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) w (n+q))
    (x : Fin n → Bool) (hqx : gateVal n C q x = true) (hneg : graphFun G ∅ x = false) :
    value C x r = false := by
  by_contra hr
  have hrx : value C x r = true := by cases he : value C x r <;> simp_all
  have hwx := path_true hp x hqx
  have hjx : gateVal n C j x = true := by
    change value C x (n+j) = true
    rw [value_gate C hAO.2.1 x j hj,hja]
    rcases hinputs with hs | hs <;> simp [hs,GateOp.eval,hwx,hrx]
  have hf := hjc x hjx
  rw [hneg] at hf
  cases hf

lemma partner_not_reaches {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) {q j w r : ℕ} (hdirty : ¬ BelowF G C q)
    (hj : j < C.gates.length) (hja : (gateAt C j).op = .and) (hjc : BelowF G C j)
    (hinputs : (gateAt C j).inputs = [w,r] ∨ (gateAt C j).inputs = [r,w])
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) w (n+q)) :
    ¬ Relation.ReflTransGen (MixedColor.OrStep n C) r (n+q) := by
  intro hrp
  apply hdirty
  intro x hqx
  by_contra hneg
  have hrf := partner_false G C hAO hj hja hjc hinputs hp x hqx (Bool.eq_false_iff.mpr hneg)
  have hrt := path_true hrp x hqx
  rw [hrf] at hrt
  cases hrt

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.LastDirtyAndFrontier

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.LastDirtyAndDependency

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma cone_lt {n : ℕ} (C : Circuit) {q k : ℕ} (hk : k < C.gates.length)
    (hc : InCone n C q k) : q < k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨w,_,hn,hw,hq | hq⟩ := (JunkPurity.inCone_iff n C q k hk).mp hc
    · omega
    · have := ih (w-n) (by omega) (by omega) hq
      omega

lemma cone_to_or_path {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C) {q j : ℕ}
    (hlast : ∀ k, q < k → k < C.gates.length → (gateAt C k).op = .and → BelowF G C k)
    (hj : j < C.gates.length) (hja : (gateAt C j).op = .and)
    {k : ℕ} (hk : k < C.gates.length) (hkj : InCone n C k j)
    (hqk : q = k ∨ InCone n C q k) :
    Relation.ReflTransGen (MixedColor.OrStep n C) (n+k) (n+q) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rcases hqk with rfl | hqk
    · rfl
    have hqkl := cone_lt C hk hqk
    rcases hAO.1 _ (MixedColor.gateAt_mem hk) with ha | ho
    · exact (hTF k hk j hj ha (hlast k hqkl hk ha) hja hkj).elim
    · obtain ⟨w,hw,hn,hwk,hqw⟩ := (JunkPurity.inCone_iff n C q k hk).mp hqk
      have hwc : InCone n C (w-n) k :=
        (JunkPurity.inCone_iff n C (w-n) k hk).mpr ⟨w,hw,hn,hwk,Or.inl rfl⟩
      have hwj := JunkPurity.cone_trans C hj hwc hkj
      have hp := ih (w-n) (by omega) (by omega) hwj hqw
      apply Relation.ReflTransGen.head ⟨k,hk,rfl,ho,hw,hwk⟩
      have heq : n+(w-n) = w := by omega
      simpa only [heq] using hp

lemma partner_no_dependency {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C) {q j w r : ℕ}
    (hdirty : ¬ BelowF G C q)
    (hlast : ∀ k, q < k → k < C.gates.length → (gateAt C k).op = .and → BelowF G C k)
    (hj : j < C.gates.length) (hja : (gateAt C j).op = .and) (hjc : BelowF G C j)
    (hinputs : (gateAt C j).inputs = [w,r] ∨ (gateAt C j).inputs = [r,w])
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) w (n+q)) :
    r ≠ n+q ∧ (n ≤ r → ¬ InCone n C q (r-n)) := by
  have hnot := LastDirtyAndFrontier.partner_not_reaches G C hAO hdirty hj hja hjc hinputs hp
  constructor
  · intro heq
    rw [heq] at hnot
    exact hnot .refl
  · intro hn hc
    have hrmem : r ∈ (gateAt C j).inputs := by
      rcases hinputs with hs | hs <;> simp [hs]
    have hrj := hAO.2.1 j hj r hrmem
    have hrcone : InCone n C (r-n) j :=
      (JunkPurity.inCone_iff n C (r-n) j hj).mpr ⟨r,hrmem,hn,hrj,Or.inl rfl⟩
    have hpath := cone_to_or_path G C hAO hTF hlast hj hja (by omega) hrcone (Or.inr hc)
    have heq : n+(r-n) = r := by omega
    exact hnot (by simpa only [heq] using hpath)

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.LastDirtyAndDependency

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.PrivateInputIndependence

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma wire_eq {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (H : ℕ) (a : Fin n)
    (hsole : ∀ j, j < C.gates.length → a.val ∈ (gateAt C j).inputs → j = H)
    (x y : Fin n → Bool) (hxy : ∀ v, v ≠ a → x v = y v)
    (w : ℕ) (hwa : w ≠ a.val)
    (hno : w ≠ n+H ∧ (n ≤ w → ¬ InCone n C H (w-n))) : value C x w = value C y w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [value_input C x w hwn,value_input C y w hwn]
      apply hxy
      intro heq
      exact hwa (congrArg Fin.val heq)
    by_cases hwlen : w < n+C.gates.length
    · let k := w-n
      have hk : k < C.gates.length := by dsimp [k]; omega
      have hw : w = n+k := by dsimp [k]; omega
      have hkH : k ≠ H := by intro heq; apply hno.1; omega
      have hanc : ¬ InCone n C H k := hno.2 (by omega)
      rw [hw,value_gate C hAO.2.1 x k hk,value_gate C hAO.2.1 y k hk]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hub : u < w := by have := hAO.2.1 k hk u hu; omega
      apply ih u hub
      · intro heq
        subst u
        exact hkH (hsole k hk hu)
      · constructor
        · intro heq
          subst u
          exact hanc (JunkPurity.cone_step C hAO hk hu (Or.inl rfl))
        · intro hnu hcu
          exact hanc ((JunkPurity.inCone_iff n C H k hk).mpr
            ⟨u,hu,hnu,hAO.2.1 k hk u hu,Or.inr hcu⟩)
    · rw [value_missing C x w (by omega),value_missing C y w (by omega)]

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.PrivateInputIndependence

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.ReaderDegreeCount

open PEqualNP.TopForm

lemma neighbors_card_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (a : Fin n) {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (v : ι → Fin n)
    (hne : ∀ j ∈ J, v j ≠ a)
    (hcover : ∀ c, G.Adj a c → ∃ j ∈ J, G.Adj (v j) c) :
    (Finset.univ.filter (G.Adj a)).card ≤ J.card := by
  classical
  let S : ι → Finset (Fin n) := fun j =>
    Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj (v j) c)
  have hsub : Finset.univ.filter (G.Adj a) ⊆ J.biUnion S := by
    intro c hc
    obtain ⟨j, hj, hv⟩ := hcover c (Finset.mem_filter.mp hc).2
    exact Finset.mem_biUnion.mpr ⟨j, hj,
      Finset.mem_filter.mpr ⟨Finset.mem_univ c, (Finset.mem_filter.mp hc).2, hv⟩⟩
  calc
    (Finset.univ.filter (G.Adj a)).card ≤ (J.biUnion S).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ J, (S j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ J, 1 := Finset.sum_le_sum (fun j hj => h4 a (v j) (hne j hj).symm)
    _ = J.card := by simp

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.ReaderDegreeCount

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.PrivateReaderTransport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma edge_top_dependency {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (H : ℕ) (a : Fin n) (hdirty : ¬ BelowF G C H)
    (hsole : ∀ j, j < C.gates.length → a.val ∈ (gateAt C j).inputs → j = H)
    (c : Fin n) (hac : G.Adj a c) :
    ∃ k ∈ tops G C, gateVal n C k (pairInput a c) = true ∧ InCone n C H k := by
  classical
  obtain ⟨k,hk,_,htrue⟩ := TopFrontierCoverage.edge_reaches_top G C hAO hfun a c hac
  have hkd := MixedColor.topData hk
  have hkH : k ≠ H := by intro heq; subst k; exact hdirty hkd.2.2
  refine ⟨k,hk,htrue,?_⟩
  by_contra hno
  have he := PrivateInputIndependence.wire_eq C hAO H a hsole (pairInput a c) (pairInput c c)
    (by intro v hva; simp [pairInput,hva]) (n+k) (by have := a.isLt; omega)
    ⟨by omega,by simpa using hno⟩
  have hsingle : gateVal n C k (pairInput c c) = true := by
    change value C (pairInput c c) (n+k) = true
    rw [← he]
    exact htrue
  exact G.irrefl ((MixedColor.graphFun_pair G c c).mp (hkd.2.2 _ hsingle))

lemma leaf_ne_private {n : ℕ} (C : Circuit) (H : ℕ) (a : Fin n)
    (hHa : (gateAt C H).op = .and)
    (hsole : ∀ j, j < C.gates.length → a.val ∈ (gateAt C j).inputs → j = H)
    {j T : ℕ} (hj : j < C.gates.length) (hjo : (gateAt C j).op = .or)
    (hT : T ∈ (gateAt C j).inputs) {v : Fin n} (hv : v ∈ orIn n C T) : v ≠ a := by
  intro heq
  subst v
  simp only [orIn,Finset.mem_filter,Finset.mem_univ,true_and] at hv
  rcases hv with hv | ⟨k,hk,_,hko,hka⟩
  · have hjH := hsole j hj (hv ▸ hT)
    rw [hjH,hHa] at hjo
    cases hjo
  · have hkH := hsole k hk hka
    rw [hkH,hHa] at hko
    cases hko

lemma neighbor_transport_of_singletons {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) (hTF : TopForm G C)
    (H : ℕ) (a : Fin n) (hdirty : ¬ BelowF G C H)
    (hsole : ∀ j, j < C.gates.length → a.val ∈ (gateAt C j).inputs → j = H)
    (hlast : ∀ k, H < k → k < C.gates.length → (gateAt C k).op = .and → BelowF G C k)
    (hreadOR : ∀ j ∈ readers n C H, (gateAt C j).op = .or)
    (T : ℕ → ℕ) (v : ℕ → Fin n)
    (hleaf : ∀ j ∈ readers n C H, T j ∈ (gateAt C j).inputs ∧
      value C (pairInput (v j) (v j)) (T j) = true)
    (c : Fin n) (hac : G.Adj a c) : ∃ j ∈ readers n C H, G.Adj (v j) c := by
  classical
  obtain ⟨k,hkT,hkt,hHk⟩ := edge_top_dependency G C hAO hfun H a hdirty hsole c hac
  obtain ⟨hk,hka,hkc⟩ := MixedColor.topData hkT
  have hkH : k ≠ H := by intro heq; subst k; exact hdirty hkc
  obtain ⟨w,hwm,hnw,hwk,hHw⟩ := (JunkPurity.inCone_iff n C H k hk).mp hHk
  have hwcone : InCone n C (w-n) k :=
    (JunkPurity.inCone_iff n C (w-n) k hk).mpr ⟨w,hwm,hnw,hwk,Or.inl rfl⟩
  have hwpath := LastDirtyAndDependency.cone_to_or_path G C hAO hTF hlast hk hka
    (by omega) hwcone hHw
  have hw_eq : n+(w-n) = w := by omega
  rw [hw_eq] at hwpath
  obtain ⟨u,z,huz⟩ := MixedColor.binaryInputs hAO hk
  have hwuz : w = u ∨ w = z := by simpa [huz] using hwm
  obtain ⟨r,hshape⟩ : ∃ r, (gateAt C k).inputs = [w,r] ∨ (gateAt C k).inputs = [r,w] := by
    rcases hwuz with hwu | hwz
    · exact ⟨z,Or.inl (hwu ▸ huz)⟩
    · exact ⟨u,Or.inr (hwz ▸ huz)⟩
  have hrmem : r ∈ (gateAt C k).inputs := by rcases hshape with hs | hs <;> simp [hs]
  have hrno := LastDirtyAndDependency.partner_no_dependency G C hAO hTF hdirty hlast
    hk hka hkc hshape hwpath
  have hrna : r ≠ a.val := by
    intro heq
    subst r
    exact hkH (hsole k hk hrmem)
  have hrt : value C (pairInput a c) r = true :=
    ((MixedColor.val_and (n := n) (C := C) (x := List.ofFn (pairInput a c))
      (by simp) hk hka).mp hkt r hrmem).2
  have hre := PrivateInputIndependence.wire_eq C hAO H a hsole (pairInput a c) (pairInput c c)
    (by intro z hza; simp [pairInput,hza]) r hrna hrno
  have hrs : value C (pairInput c c) r = true := by rw [← hre]; exact hrt
  rcases Relation.ReflTransGen.cases_tail hwpath with hwH | ⟨z,hpre,hstep⟩
  · have hkr : k ∈ readers n C H := by
      simp only [readers,Finset.mem_filter,Finset.mem_range]
      exact ⟨hk,hwH ▸ hwm⟩
    have hko := hreadOR k hkr
    rw [hka] at hko
    cases hko
  · obtain ⟨j,hj,rfl,hjo,hjH,_⟩ := hstep
    have hjr : j ∈ readers n C H := by
      simp only [readers,Finset.mem_filter,Finset.mem_range]
      exact ⟨hj,hjH⟩
    obtain ⟨hTj,hvj⟩ := hleaf j hjr
    have hmT : pairInput (v j) (v j) ≤ pairInput (v j) c := by
      intro z
      by_cases hz : z = v j <;> simp [pairInput,hz]
    have hTval : value C (pairInput (v j) c) (T j) = true :=
      Bool.le_iff_imp.mp ((WireFacts.wire_monotone C hAO (T j)) hmT) hvj
    have hjval : value C (pairInput (v j) c) (n+j) = true :=
      (MixedColor.val_or (n := n) (C := C) (x := List.ofFn (pairInput (v j) c))
        (by simp) hj hjo).mpr ⟨T j,hTj,hAO.2.1 j hj _ hTj,hTval⟩
    have hwval : value C (pairInput (v j) c) w = true := MixedColor.orStep_up (by simp) hpre hjval
    have hmono : pairInput c c ≤ pairInput (v j) c := by
      intro z
      by_cases hzc : z = c <;> simp [pairInput,hzc]
    have hrval : value C (pairInput (v j) c) r = true :=
      Bool.le_iff_imp.mp ((WireFacts.wire_monotone C hAO r) hmono) hrs
    have hkval : gateVal n C k (pairInput (v j) c) = true := by
      change value C (pairInput (v j) c) (n+k) = true
      rw [value_gate C hAO.2.1 _ k hk,hka]
      rcases hshape with hs | hs <;> simp [hs,GateOp.eval,hwval,hrval]
    exact ⟨j,hjr,(MixedColor.graphFun_pair G (v j) c).mp (hkc _ hkval)⟩

lemma neighbor_transport {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) (hTF : TopForm G C)
    (H : ℕ) (a : Fin n) (hdirty : ¬ BelowF G C H)
    (hsole : ∀ j, j < C.gates.length → a.val ∈ (gateAt C j).inputs → j = H)
    (hlast : ∀ k, H < k → k < C.gates.length → (gateAt C k).op = .and → BelowF G C k)
    (hreadOR : ∀ j ∈ readers n C H, (gateAt C j).op = .or)
    (T : ℕ → ℕ) (v : ℕ → Fin n)
    (hleaf : ∀ j ∈ readers n C H, T j ∈ (gateAt C j).inputs ∧ v j ∈ orIn n C (T j))
    (c : Fin n) (hac : G.Adj a c) : ∃ j ∈ readers n C H, G.Adj (v j) c := by
  apply neighbor_transport_of_singletons G C hAO hfun hTF H a hdirty hsole hlast
    hreadOR T v ?_ c hac
  intro j hj
  exact ⟨(hleaf j hj).1, MixedColor.reach_var_val _ _ _
    (MixedColor.mem_orIn_reach (v j) (hleaf j hj).2)
    (MixedColor.pairInput_left (v j) (v j))⟩

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.PrivateReaderTransport

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.PrivateReaderDegree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma degree_le_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hTF : TopForm G C) (h4 : NoFourCycle G) (H : ℕ) (a : Fin n)
    (hHa : (gateAt C H).op = .and) (hdirty : ¬ BelowF G C H)
    (hsole : ∀ j, j < C.gates.length → a.val ∈ (gateAt C j).inputs → j = H)
    (hlast : ∀ k, H < k → k < C.gates.length → (gateAt C k).op = .and → BelowF G C k)
    (hreadOR : ∀ j ∈ readers n C H, (gateAt C j).op = .or)
    (hraw : ∀ j ∈ readers n C H, ∃ T ∈ (gateAt C j).inputs, (orIn n C T).Nonempty) :
    G.degree a ≤ (readers n C H).card := by
  classical
  have hex : ∀ j : ℕ, ∃ T : ℕ, ∃ v : Fin n, j ∈ readers n C H →
      T ∈ (gateAt C j).inputs ∧ v ∈ orIn n C T := by
    intro j
    by_cases hj : j ∈ readers n C H
    · obtain ⟨T,hT,v,hv⟩ := hraw j hj
      exact ⟨T,v,fun _ => ⟨hT,hv⟩⟩
    · exact ⟨0,a,fun h => (hj h).elim⟩
  choose T v hdata using hex
  have hne : ∀ j ∈ readers n C H, v j ≠ a := by
    intro j hj
    have hjl : j < C.gates.length := (Finset.mem_filter.mp hj).1 |> Finset.mem_range.mp
    exact PrivateReaderTransport.leaf_ne_private C H a hHa hsole hjl (hreadOR j hj)
      (hdata j hj).1 (hdata j hj).2
  have hcover := PrivateReaderTransport.neighbor_transport G C hAO hfun hTF H a hdirty
    hsole hlast hreadOR T v hdata
  rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  exact ReaderDegreeCount.neighbors_card_le G h4 a (readers n C H) v hne hcover

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.PrivateReaderDegree

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.PrivateReaderDegree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma degree_le_readers_of_singletons {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hTF : TopForm G C) (h4 : NoFourCycle G) (H : ℕ) (a : Fin n)
    (hdirty : ¬ BelowF G C H)
    (hsole : ∀ j, j < C.gates.length → a.val ∈ (gateAt C j).inputs → j = H)
    (hlast : ∀ k, H < k → k < C.gates.length → (gateAt C k).op = .and → BelowF G C k)
    (hreadOR : ∀ j ∈ readers n C H, (gateAt C j).op = .or)
    (hsingle : ∀ j ∈ readers n C H, ∃ T ∈ (gateAt C j).inputs, ∃ v : Fin n,
      v ≠ a ∧ value C (pairInput v v) T = true) :
    G.degree a ≤ (readers n C H).card := by
  classical
  have hex : ∀ j : ℕ, ∃ T : ℕ, ∃ v : Fin n, j ∈ readers n C H →
      T ∈ (gateAt C j).inputs ∧ v ≠ a ∧ value C (pairInput v v) T = true := by
    intro j
    by_cases hj : j ∈ readers n C H
    · obtain ⟨T,hT,v,hv,htrue⟩ := hsingle j hj
      exact ⟨T,v,fun _ => ⟨hT,hv,htrue⟩⟩
    · exact ⟨0,a,fun h => (hj h).elim⟩
  choose T v hdata using hex
  have hcover := PrivateReaderTransport.neighbor_transport_of_singletons G C hAO hfun hTF
    H a hdirty hsole hlast hreadOR T v (fun j hj => ⟨(hdata j hj).1,(hdata j hj).2.2⟩)
  rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  exact ReaderDegreeCount.neighbors_card_le G h4 a (readers n C H) v
    (fun j hj => (hdata j hj).2.1) hcover

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.PrivateReaderDegree

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.H4Support
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

lemma live_has_reader (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (hj : j ∈ liveGates n C) (hjo : C.output ≠ n + j) :
    ∃ k < C.size, j < k ∧ n + j ∈ (gateAt C k).inputs := by
  classical
  have hreach := (Finset.mem_filter.mp hj).2
  change Relation.ReflTransGen (WireStep n C) C.output (n + j) at hreach
  rcases hreach.cases_tail with heq | ⟨b, hpath, hstep⟩
  · exact False.elim (hjo heq.symm)
  · obtain ⟨k, hk, hbk, hread⟩ := hstep
    have hlt := hC.2.1 k hk (n + j) hread
    exact ⟨k, hk, by omega, hread⟩

lemma least_has_reader (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (ho : C.output < n + C.size)
    (j : ℕ) (hj : j < C.size) (hjo : C.output ≠ n + j) :
    ∃ k < C.size, j < k ∧ n + j ∈ (gateAt C k).inputs := by
  apply live_has_reader C hC.1 j _ hjo
  rw [least_all_live G C hC ho]
  exact Finset.mem_range.mpr hj


lemma rank_induction (rank : ι → ℕ) (p : ι → Prop)
    (h : ∀ i, (∀ j, rank j < rank i → p j) → p i) : ∀ i, p i := by
  have key : ∀ m, ∀ i, rank i = m → p i := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih => exact fun i hi => h i fun j hj => ih (rank j) (hi ▸ hj) j rfl
  exact fun i => key _ i rfl

lemma sol_le (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) (x : Fin n → Bool)
    (t u : ι → Bool) (ht : SolAt P K x t)
    (hs : ∀ i ∈ K, opv (P.isAnd i) (srcAt x u (P.src i 0)) (srcAt x u (P.src i 1)) = true → u i = true) :
    ∀ i ∈ K, t i = true → u i = true := by
  refine fun i => rank_induction rank (fun i => i ∈ K → t i = true → u i = true) ?_ i
  intro i ih hi hti
  rw [ht i hi] at hti
  refine hs i hi (opv_mono _ _ _ _ _ ?_ ?_ hti)
  all_goals
    intro h
    revert h
    generalize hb : P.src i _ = s
    rcases s with _ | (a | j)
    · exact fun h => h
    · exact fun h => h
    · intro h
      obtain ⟨hj, hr⟩ := hcl i hi _ j hb
      exact ih j hr hj h

lemma le_sol (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) (x : Fin n → Bool)
    (t u : ι → Bool) (ht : SolAt P K x t)
    (hs : ∀ i ∈ K, u i = true → opv (P.isAnd i) (srcAt x u (P.src i 0)) (srcAt x u (P.src i 1)) = true) :
    ∀ i ∈ K, u i = true → t i = true := by
  refine fun i => rank_induction rank (fun i => i ∈ K → u i = true → t i = true) ?_ i
  intro i ih hi hui
  rw [ht i hi]
  refine opv_mono _ _ _ _ _ ?_ ?_ (hs i hi hui)
  all_goals
    intro h
    revert h
    generalize hb : P.src i _ = s
    rcases s with _ | (a | j)
    · exact fun h => h
    · exact fun h => h
    · intro h
      obtain ⟨hj, hr⟩ := hcl i hi _ j hb
      exact ih j hr hj h

lemma sol_mono (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K)
    (v : ι → (Fin n → Bool) → Bool) (hv : Sol P K v) (x y : Fin n → Bool)
    (hxy : ∀ a, x a = true → y a = true) : ∀ i ∈ K, v i x = true → v i y = true := by
  refine sol_le P rank K hcl x (fun i => v i x) (fun i => v i y) (hv x) ?_
  intro i hi h
  have e := hv y i hi
  simp only at e
  rw [e]
  refine opv_mono _ _ _ _ _ ?_ ?_ h
  all_goals
    generalize P.src i _ = s
    rcases s with _ | (a | j)
    · exact fun h => h
    · exact hxy a
    · exact fun h => h

lemma sol_exists (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) :
    ∃ v : ι → (Fin n → Bool) → Bool, Sol P K v := by
  classical
  suffices h : ∀ L : Finset ι, L ⊆ K → Closed P rank L → ∃ v : ι → (Fin n → Bool) → Bool, Sol P L v from
    h K (Finset.Subset.refl K) hcl
  intro L
  induction L using Finset.induction_on_max_value rank with
  | empty => exact fun _ _ => ⟨fun _ _ => false, fun _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha hmax ih =>
    intro hsub hL
    have hs : Closed P rank s := by
      intro i hi b j hj
      obtain ⟨h1, h2⟩ := hL i (Finset.mem_insert_of_mem hi) b j hj
      refine ⟨(Finset.mem_insert.1 h1).resolve_left ?_, h2⟩
      rintro rfl
      exact absurd (hmax i hi) (by omega)
    obtain ⟨v, hv⟩ := ih ((Finset.subset_insert a s).trans hsub) hs
    let v' : ι → (Fin n → Bool) → Bool := fun i x => if i = a then
      opv (P.isAnd a) (srcAt x (fun j => v j x) (P.src a 0)) (srcAt x (fun j => v j x) (P.src a 1)) else v i x
    have hsrc : ∀ i ∈ insert a s, ∀ b x, srcAt x (fun j => v' j x) (P.src i b)
        = srcAt x (fun j => v j x) (P.src i b) := by
      intro i hi b x
      rcases hb : P.src i b with _ | (c | j)
      · rfl
      · rfl
      · obtain ⟨_, hr⟩ := hL i hi b j hb
        have hja : j ≠ a := by
          rintro rfl
          rcases Finset.mem_insert.1 hi with rfl | hi'
          · exact absurd hr (lt_irrefl _)
          · exact absurd (hmax i hi') (by omega)
        simp [srcAt, v', hja]
    refine ⟨v', fun x i hi => ?_⟩
    simp only
    rw [hsrc i hi 0 x, hsrc i hi 1 x]
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · simp [v']
    · have hia : i ≠ a := by
        rintro rfl
        exact ha hi'
      have := hv x i hi'
      simpa [v', hia] using this

open PEqualNP.EdgeOwnership (pairInput)

def dropSrc (n j w : ℕ) : Src n ℕ := if w = n + j then none else srcOf n w

lemma dropSrc_inr (j w t : ℕ) (h : dropSrc n j w = some (Sum.inr t)) :
    w = n + t ∧ t ≠ j := by
  by_cases hw : w = n + j
  · simp [dropSrc, hw] at h
  · have he := srcOf_inr w t (by simpa [dropSrc, hw] using h)
    exact ⟨he, by omega⟩

lemma opnd_mem (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.size) (b : Fin 2) :
    opnd C k b ∈ (gateAt C k).inputs := by
  have hkg : k < C.gates.length := hk
  have hm : gateAt C k ∈ C.gates := by
    exact List.mem_of_getElem? (show C.gates[k]? = some (gateAt C k) by
      simp [gateAt, List.getD_eq_getElem?_getD, hkg])
  have hlen := hC.2.2 _ hm
  have hb : b.val < (gateAt C k).inputs.length := by rw [hlen]; exact b.isLt
  exact List.mem_of_getElem? (show (gateAt C k).inputs[b.val]? = some (opnd C k b) by
    simp [opnd, List.getD_eq_getElem?_getD, hb])

lemma dropSrc_old_le (C : Circuit) (j w : ℕ) (x : Fin n → Bool) :
    srcAt x (fun k => gateVal n C k x) (dropSrc n j w) = true → wireVal n C w x = true := by
  unfold dropSrc
  split_ifs with hw
  · simp [srcAt]
  · rw [srcAt_srcOf]
    exact id

lemma dropSrc_old_eq (C : Circuit) (j w : ℕ) (x : Fin n → Bool)
    (hz : gateVal n C j x = false) :
    srcAt x (fun k => gateVal n C k x) (dropSrc n j w) = wireVal n C w x := by
  unfold dropSrc
  split_ifs with hw
  · subst w
    exact hz.symm
  · exact srcAt_srcOf C w x

lemma drop_edge_zero (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (ho : C.output < n + C.size) (j : ℕ) (hj : j < C.size)
    (hz : ∀ p q, G.Adj p q → gateVal n C j (pairInput p q) = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  let K := (Finset.range C.size).erase j
  let P : Prog n ℕ := progOf C fun k b => dropSrc n j (opnd C k b)
  let o : Src n ℕ := dropSrc n j C.output
  have hK : ∀ k ∈ K, k < C.size := fun k hk =>
    Finset.mem_range.mp (Finset.mem_of_mem_erase hk)
  have hclosed : Closed P id K := by
    intro k hk b t ht
    obtain ⟨heq, hne⟩ := dropSrc_inr j (opnd C k b) t ht
    have hkl := hK k hk
    have hback := hC.2.1 k hkl _ (opnd_mem C hC k hkl b)
    refine ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_range.mpr (by omega)⟩, ?_⟩
    simpa using (show t < k by omega)
  have hout : ∀ t, o = some (Sum.inr t) → t ∈ K := by
    intro t ht
    obtain ⟨heq, hne⟩ := dropSrc_inr j C.output t ht
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨v, hv⟩ := sol_exists P id K hclosed
  have hupper (x : Fin n → Bool) : ∀ k ∈ K, v k x = true → gateVal n C k x = true := by
    apply sol_le P id K hclosed x (fun k => v k x) (fun k => gateVal n C k x) (hv x)
    intro k hk h
    rw [gate_eq C hC k (hK k hk) x]
    exact opv_mono _ _ _ _ _ (dropSrc_old_le C j (opnd C k 0) x)
      (dropSrc_old_le C j (opnd C k 1) x) h
  have houtput_le (x : Fin n → Bool) :
      srcAt x (fun k => v k x) o = true → graphFun G ∅ x = true := by
    intro hx
    have hsource : srcAt x (fun k => gateVal n C k x) o = true := by
      rcases hs : o with _ | (a | t)
      · simp [hs, srcAt] at hx
      · simpa [hs, srcAt] using hx
      · exact hupper x t (hout t hs) (by simpa [hs, srcAt] using hx)
    have hf := dropSrc_old_le C j C.output x hsource
    change circuitFun n C x = true at hf
    rwa [hF] at hf
  have hedges (p q : Fin n) (hpq : G.Adj p q) :
      srcAt (pairInput p q) (fun k => v k (pairInput p q)) o = true := by
    let x := pairInput p q
    have hzero : gateVal n C j x = false := hz p q hpq
    have hbelow : ∀ k ∈ K, gateVal n C k x = true → v k x = true := by
      apply le_sol P id K hclosed x (fun k => v k x) (fun k => gateVal n C k x) (hv x)
      intro k hk h
      change gateVal n C k x = true at h
      change opv (isA (gateAt C k).op)
        (srcAt x (fun t => gateVal n C t x) (dropSrc n j (opnd C k 0)))
        (srcAt x (fun t => gateVal n C t x) (dropSrc n j (opnd C k 1))) = true
      rw [dropSrc_old_eq C j _ x hzero, dropSrc_old_eq C j _ x hzero, ← gate_eq C hC k (hK k hk) x]
      exact h
    have hsource : srcAt x (fun k => gateVal n C k x) o = true := by
      rw [dropSrc_old_eq C j _ x hzero]
      change circuitFun n C x = true
      rw [hF]
      apply (show graphFun G ∅ x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true by simp [graphFun]).mpr
      exact ⟨p, q, hpq, by simp [x, pairInput], by simp [x, pairInput]⟩
    rcases hs : o with _ | (a | t)
    · simp [hs, srcAt, x] at hsource
    · simpa [hs, srcAt, x] using hsource
    · exact hbelow t (hout t hs) (by simpa [hs, srcAt, x] using hsource)
  have hmono (x y : Fin n → Bool) (hxy : ∀ a, x a = true → y a = true) :
      srcAt x (fun k => v k x) o = true → srcAt y (fun k => v k y) o = true := by
    rcases hs : o with _ | (a | t)
    · exact id
    · exact hxy a
    · exact sol_mono P id K hclosed v hv x y hxy t (hout t hs)
  obtain ⟨D, hD, hsize, hfun⟩ := fold_total P id v K hclosed hv o hout
  refine ⟨D, hD, ?_, funext fun x => ?_⟩
  · have hc := hsize.trans (Finset.card_filter_le K _)
    have hcard : K.card = C.size - 1 := by
      simp [K, Finset.card_erase_of_mem (Finset.mem_range.mpr hj)]
    omega
  · rw [hfun]
    apply Bool.eq_iff_iff.mpr
    refine ⟨houtput_le x, ?_⟩
    intro hx
    have hg : ∃ p q, G.Adj p q ∧ x p = true ∧ x q = true := by
      simpa [graphFun] using hx
    obtain ⟨p, q, hpq, hp, hq⟩ := hg
    apply hmono (pairInput p q) x _ (hedges p q hpq)
    intro a ha
    simp only [pairInput, decide_eq_true_eq] at ha
    rcases ha with rfl | rfl
    · exact hp
    · exact hq

lemma least_gate_hits_edge (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hne : ∃ p q, G.Adj p q)
    (j : ℕ) (hj : j < C.size) :
    ∃ p q, G.Adj p q ∧ gateVal n C j (pairInput p q) = true := by
  classical
  have hout : C.output < n + C.size := by
    obtain ⟨p, q, hpq⟩ := hne
    have ht : circuitFun n C (pairInput p q) = true := by
      rw [hC.2.1]
      apply (show graphFun G ∅ (pairInput p q) = true ↔ ∃ a b, G.Adj a b ∧ pairInput p q a = true ∧ pairInput p q b = true by simp [graphFun]).mpr
      exact ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
    by_contra hbad
    have hlen : (C.wires (List.ofFn (pairInput p q))).length = n + C.size := by
      unfold Circuit.wires
      rw [wires_length, List.length_ofFn]
      rfl
    have hz : (C.wires (List.ofFn (pairInput p q))).getD C.output false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega :
        (C.wires (List.ofFn (pairInput p q))).length ≤ C.output)]
    change (C.wires (List.ofFn (pairInput p q))).getD C.output false = true at ht
    exact Bool.false_ne_true (hz.symm.trans ht)
  by_contra hn
  have hz : ∀ p q, G.Adj p q → gateVal n C j (pairInput p q) = false := by
    intro p q hpq
    cases he : gateVal n C j (pairInput p q)
    · rfl
    · exact False.elim (hn ⟨p, q, hpq, he⟩)
  obtain ⟨D, hD, hs, hf⟩ := drop_edge_zero G C hC.1 hC.2.1 hout j hj hz
  have hm := hC.2.2 D hD hf
  omega

lemma least_first_and_adj (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hne : ∃ p q, G.Adj p q)
    (hsize : 0 < C.size) (u v : Fin n) (huv : u ≠ v)
    (hop : (gateAt C 0).op = GateOp.and)
    (hins : (gateAt C 0).inputs = [u.val, v.val]) : G.Adj u v := by
  obtain ⟨p, q, hpq, hgate⟩ := least_gate_hits_edge G C hC hne 0 hsize
  have hval := gate_eq C hC.1 0 hsize (pairInput p q)
  have hu : wireVal n C u.val (pairInput p q) = pairInput p q u :=
    wireVal_lt C u.val u.isLt _
  have hv : wireVal n C v.val (pairInput p q) = pairInput p q v :=
    wireVal_lt C v.val v.isLt _
  simp only [opnd, hins] at hval
  simp [hop, isA, opv, hu, hv] at hval
  rw [hgate] at hval
  have hpv : pairInput p q u = true ∧ pairInput p q v = true := by
    simpa using hval.symm
  simp only [pairInput, decide_eq_true_eq] at hpv
  rcases hpv with ⟨hup | huq, hvp | hvq⟩
  · exact False.elim (huv (hup.trans hvp.symm))
  · simpa [hup, hvq] using hpq
  · simpa [huq, hvp] using hpq.symm
  · exact False.elim (huv (huq.trans hvq.symm))

open scoped BigOperators

def readList (C : Circuit) : List ℕ := C.gates.flatMap Gate.inputs

lemma readList_length (C : Circuit) (hC : IsAO2 n C) :
    (readList C).length = 2 * C.size := by
  have aux (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length = 2) :
      (gs.flatMap Gate.inputs).length = 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      rw [List.flatMap_cons, List.length_append, h g (by simp),
        ih (fun a ha => h a (by simp [ha]))]
      simp; omega
  exact aux C.gates hC.2.2

lemma readList_bound (C : Circuit) (hC : IsAO2 n C) :
    ∀ w ∈ readList C, w < n + C.size := by
  intro w hw
  obtain ⟨g, hg, hwi⟩ := List.mem_flatMap.mp hw
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hg
  have hgate : gateAt C k = g := by
    simp [gateAt, List.getD_eq_getElem?_getD, hk, heq]
  have hlt := hC.2.1 k hk w (hgate.symm ▸ hwi)
  change k < C.size at hk
  omega

lemma reader_mem (C : Circuit) (j k : ℕ) (hk : k < C.size)
    (hread : n + j ∈ (gateAt C k).inputs) : n + j ∈ readList C := by
  apply List.mem_flatMap.mpr
  refine ⟨gateAt C k, ?_, hread⟩
  have hklen : k < C.gates.length := hk
  exact List.mem_of_getElem? (show C.gates[k]? = some (gateAt C k) by
    simp [gateAt, List.getD_eq_getElem?_getD, hklen])

lemma read_twice_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (ho : n ≤ C.output) (hupper : C.output < n + C.size)
    (hreads : ∀ i : Fin n, 2 ≤ (readList C).count i.val) :
    2 * n ≤ C.size + 1 := by
  classical
  let L := readList C
  let q := C.output - n
  have hq : q < C.size := by dsimp [q]; omega
  have htotal : (∑ w ∈ Finset.range (n + C.size), L.count w) = 2 * C.size := by
    have hsum : (∑ w ∈ Finset.range (n + C.size), (L : Multiset ℕ).count w) = L.length := by
      apply Multiset.sum_count_eq_card
      intro w hw
      exact Finset.mem_range.mpr (readList_bound C hC.1 w hw)
    simpa [L, readList_length C hC.1] using hsum
  have hinputs : 2 * n ≤ ∑ w ∈ Finset.range n, L.count w := by
    have hh : (∑ w ∈ Finset.range n, 2) ≤ ∑ w ∈ Finset.range n, L.count w := by
      apply Finset.sum_le_sum
      intro w hw
      exact hreads ⟨w, Finset.mem_range.mp hw⟩
    simpa [Nat.mul_comm] using hh
  have hgate (j : ℕ) (hj : j ∈ (Finset.range C.size).erase q) :
      1 ≤ L.count (n + j) := by
    obtain ⟨hjq, hj⟩ := Finset.mem_erase.mp hj
    have hjo : C.output ≠ n + j := by
      intro heq
      apply hjq
      dsimp [q]
      omega
    obtain ⟨k, hk, _, hread⟩ := least_has_reader G C hC hupper j (Finset.mem_range.mp hj) hjo
    exact List.count_pos_iff.mpr (reader_mem C j k hk hread)
  have hgates : C.size - 1 ≤ ∑ j ∈ Finset.range C.size, L.count (n + j) := by
    have hsum := Finset.sum_le_sum hgate
    have hcard : ((Finset.range C.size).erase q).card = C.size - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hq), Finset.card_range]
    have hsub : (∑ j ∈ (Finset.range C.size).erase q, L.count (n + j)) ≤
        ∑ j ∈ Finset.range C.size, L.count (n + j) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset q _) (fun _ _ _ => Nat.zero_le _)
    have hh : C.size - 1 ≤ ∑ j ∈ (Finset.range C.size).erase q, L.count (n + j) := by
      simpa [hcard] using hsum
    exact hh.trans hsub
  rw [Finset.sum_range_add] at htotal
  omega

lemma low_read_of_small (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (ho : n ≤ C.output) (hupper : C.output < n + C.size)
    (hsmall : C.size + 1 < 2 * n) :
    ∃ i : Fin n, (readList C).count i.val ≤ 1 := by
  classical
  by_contra h
  push Not at h
  have hreads : ∀ i : Fin n, 2 ≤ (readList C).count i.val := by
    intro i
    have hi := h i
    omega
  have hbound := read_twice_bound G C hC ho hupper hreads
  omega


end Pruning

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.H4Support

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.H4Support.GateSavings

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.H4Support.Pruning

variable {n : ℕ}

def cutInput (z : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i = z then false else x i

def cutSrc (z : Fin n) (w : ℕ) : Src n ℕ := if w = z.val then none else srcOf n w

lemma cutSrc_inr (z : Fin n) (w j : ℕ) (h : cutSrc z w = some (Sum.inr j)) : w = n + j := by
  by_cases hz : w = z.val
  · simp [cutSrc, hz] at h
  · exact srcOf_inr w j (by simpa [cutSrc, hz] using h)

lemma cutSrc_value (C : Circuit) (z : Fin n) (w : ℕ) (x : Fin n → Bool) :
    srcAt x (fun k => gateVal n C k (cutInput z x)) (cutSrc z w) =
      wireVal n C w (cutInput z x) := by
  by_cases hz : w = z.val
  · subst w
    rw [wireVal_lt C z.val z.isLt]
    simp [cutSrc, srcAt, cutInput]
  · have heq : srcAt x (fun k => gateVal n C k (cutInput z x)) (cutSrc z w) =
        srcAt (cutInput z x) (fun k => gateVal n C k (cutInput z x)) (srcOf n w) := by
      simp only [cutSrc, hz, ite_false]
      unfold srcOf
      split_ifs with hw
      · have hne : (⟨w, hw⟩ : Fin n) ≠ z := by intro he; exact hz (congrArg Fin.val he)
        simp [srcAt, cutInput, hne]
      · rfl
    rw [heq, srcAt_srcOf]

lemma opnd_mem (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.size) (b : Fin 2) :
    opnd C k b ∈ (gateAt C k).inputs := by
  have hkg : k < C.gates.length := hk
  have hm : gateAt C k ∈ C.gates := by
    exact List.mem_of_getElem? (show C.gates[k]? = some (gateAt C k) by
      simp [gateAt, List.getD_eq_getElem?_getD, hkg])
  have hlen := hC.2.2 _ hm
  have hb : b.val < (gateAt C k).inputs.length := by rw [hlen]; exact b.isLt
  exact List.mem_of_getElem? (show (gateAt C k).inputs[b.val]? = some (opnd C k b) by
    simp [opnd, List.getD_eq_getElem?_getD, hb])

lemma restrict_false_saves (C : Circuit) (hC : IsAO2 n C) (ho : C.output < n + C.size)
    (z : Fin n) (E : Finset ℕ) (hE : E ⊆ Finset.range C.size)
    (hzero : ∀ k ∈ E, ∃ b : Fin 2,
      wireVal n C (opnd C k b) (cutInput z (fun _ => true)) = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + E.card ≤ C.size ∧
      circuitFun n D = fun x => circuitFun n C (cutInput z x) := by
  classical
  let K := Finset.range C.size
  let P : Prog n ℕ := progOf C fun k b => cutSrc z (opnd C k b)
  let v : ℕ → (Fin n → Bool) → Bool := fun k x => gateVal n C k (cutInput z x)
  let o : Src n ℕ := cutSrc z C.output
  have hclosed : Closed P id K := by
    intro k hk b j hj
    have he := cutSrc_inr z (opnd C k b) j hj
    have hkl : k < C.size := Finset.mem_range.mp hk
    have hb := hC.2.1 k hkl _ (opnd_mem C hC k hkl b)
    exact ⟨Finset.mem_range.mpr (by omega), by simpa using (show j < k by omega)⟩
  have hsol : Sol P K v := by
    intro x k hk
    change gateVal n C k (cutInput z x) = opv (isA (gateAt C k).op)
      (srcAt x (fun j => gateVal n C j (cutInput z x)) (cutSrc z (opnd C k 0)))
      (srcAt x (fun j => gateVal n C j (cutInput z x)) (cutSrc z (opnd C k 1)))
    rw [cutSrc_value, cutSrc_value]
    exact gate_eq C hC k (Finset.mem_range.mp hk) (cutInput z x)
  have hout : ∀ j, o = some (Sum.inr j) → j ∈ K := by
    intro j hj
    have he := cutSrc_inr z C.output j hj
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨D, hD, hs, hf⟩ := fold_total P id v K hclosed hsol o hout
  have hsub : kept P v K ⊆ K \ E := by
    intro k hk
    obtain ⟨hkK, ha, hb⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_sdiff.mpr ⟨hkK, ?_⟩
    intro hkE
    obtain ⟨b, hz⟩ := hzero k hkE
    have hboth : ∀ c : Fin 2, srcAt (fun _ => true) (fun j => v j (fun _ => true)) (P.src k c) = true := by
      intro c
      fin_cases c
      · exact ha
      · exact hb
    have hc := hboth b
    change srcAt (fun _ => true) (fun j => gateVal n C j (cutInput z (fun _ => true)))
      (cutSrc z (opnd C k b)) = true at hc
    rw [cutSrc_value, hz] at hc
    cases hc
  have hcount := Finset.card_le_card hsub
  have hcard : (K \ E).card + E.card = C.size := by
    simpa [K] using Finset.card_sdiff_add_card_eq_card hE
  refine ⟨D, hD, by omega, ?_⟩
  funext x
  rw [hf x]
  exact cutSrc_value C z C.output x

lemma exists_opnd_of_mem (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.size)
    (w : ℕ) (hw : w ∈ (gateAt C k).inputs) : ∃ b : Fin 2, opnd C k b = w := by
  have hkg : k < C.gates.length := hk
  have hm : gateAt C k ∈ C.gates := by
    exact List.mem_of_getElem? (show C.gates[k]? = some (gateAt C k) by
      simp [gateAt, List.getD_eq_getElem?_getD, hkg])
  have hlen := hC.2.2 _ hm
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hw
  let b : Fin 2 := ⟨i, by omega⟩
  refine ⟨b, ?_⟩
  simp [opnd, b, List.getD_eq_getElem?_getD, hi, he]

lemma input_zero (C : Circuit) (z : Fin n) :
    wireVal n C z.val (cutInput z (fun _ => true)) = false := by
  rw [wireVal_lt C z.val z.isLt]
  simp [cutInput]

lemma and_reader_zero (C : Circuit) (hC : IsAO2 n C) (z : Fin n) (j : ℕ)
    (hj : j < C.size) (hand : (gateAt C j).op = GateOp.and)
    (hread : z.val ∈ (gateAt C j).inputs) :
    gateVal n C j (cutInput z (fun _ => true)) = false := by
  obtain ⟨b, hb⟩ := exists_opnd_of_mem C hC j hj z.val hread
  rw [gate_eq C hC j hj, hand]
  change (wireVal n C (opnd C j 0) (cutInput z (fun _ => true)) &&
    wireVal n C (opnd C j 1) (cutInput z (fun _ => true))) = false
  have hb01 : b = 0 ∨ b = 1 := by omega
  rcases hb01 with hb0 | hb1
  · rw [hb0] at hb
    rw [hb, input_zero]
    rfl
  · rw [hb1] at hb
    rw [hb, input_zero]
    exact Bool.and_false _

lemma restrict_and_reader_saves (C : Circuit) (hC : IsAO2 n C)
    (ho : C.output < n + C.size) (z : Fin n) (j : ℕ)
    (hj : j < C.size) (hand : (gateAt C j).op = GateOp.and)
    (hread : z.val ∈ (gateAt C j).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 1 + (readers n C j).card ≤ C.size ∧
      circuitFun n D = fun x => circuitFun n C (cutInput z x) := by
  classical
  have hjnot : j ∉ readers n C j := by
    intro h
    have hr := (Finset.mem_filter.mp h).2
    have hb := hC.2.1 j hj (n + j) hr
    omega
  have hsubset : insert j (readers n C j) ⊆ Finset.range C.size := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact Finset.mem_range.mpr hj
    · exact (Finset.mem_filter.mp hk).1
  have hz : gateVal n C j (cutInput z (fun _ => true)) = false :=
    and_reader_zero C hC z j hj hand hread
  have hzero : ∀ k ∈ insert j (readers n C j), ∃ b : Fin 2,
      wireVal n C (opnd C k b) (cutInput z (fun _ => true)) = false := by
    intro k hk
    rcases Finset.mem_insert.mp hk with he | hk
    · subst k
      obtain ⟨b, hb⟩ := exists_opnd_of_mem C hC j hj z.val hread
      exact ⟨b, by rw [hb]; exact input_zero C z⟩
    · obtain ⟨hklen, hkr⟩ := Finset.mem_filter.mp hk
      obtain ⟨b, hb⟩ := exists_opnd_of_mem C hC k (Finset.mem_range.mp hklen) (n + j) hkr
      refine ⟨b, ?_⟩
      rw [hb]
      exact hz
  obtain ⟨D, hD, hs, hf⟩ := restrict_false_saves C hC ho z _ hsubset hzero
  rw [Finset.card_insert_of_notMem hjnot] at hs
  exact ⟨D, hD, by omega, hf⟩

lemma restrict_and_reader_two (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (ho : C.output < n + C.size)
    (z : Fin n) (j : ℕ) (hj : j < C.size) (hjo : C.output ≠ n + j)
    (hand : (gateAt C j).op = GateOp.and) (hread : z.val ∈ (gateAt C j).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 2 ≤ C.size ∧
      circuitFun n D = fun x => circuitFun n C (cutInput z x) := by
  obtain ⟨k, hk, _, hkr⟩ := least_has_reader G C hC ho j hj hjo
  have hmem : k ∈ readers n C j := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkr⟩
  have hpos : 0 < (readers n C j).card := Finset.card_pos.mpr ⟨k, hmem⟩
  obtain ⟨D, hD, hs, hf⟩ := restrict_and_reader_saves C hC.1 ho z j hj hand hread
  exact ⟨D, hD, by omega, hf⟩

lemma cut_adj (G : SimpleGraph (Fin n)) (z a b : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).Adj a b ↔ G.Adj a b ∧ a ≠ z ∧ b ≠ z := by
  rw [SimpleGraph.deleteEdges_adj, SimpleGraph.mk'_mem_incidenceSet_iff]
  constructor
  · rintro ⟨hab, hn⟩
    exact ⟨hab, fun h => hn ⟨hab, Or.inl h.symm⟩, fun h => hn ⟨hab, Or.inr h.symm⟩⟩
  · rintro ⟨hab, haz, hbz⟩
    exact ⟨hab, fun h => h.2.elim (fun hza => haz hza.symm) (fun hzb => hbz hzb.symm)⟩

lemma graph_cutInput (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Fin n) :
    (fun x => graphFun G ∅ (cutInput z x)) =
      (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
        (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true)
        (Classical.propDecidable _)) := by
  classical
  funext x
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  congr 1
  apply propext
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have haz : a ≠ z := by intro h; subst a; simp [cutInput] at ha
    have hbz : b ≠ z := by intro h; subst b; simp [cutInput] at hb
    refine ⟨a, b, (cut_adj G z a b).2 ⟨hab, haz, hbz⟩, ?_, ?_⟩
    · simpa [cutInput, haz] using ha
    · simpa [cutInput, hbz] using hb
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hab, haz, hbz⟩ := (cut_adj G z a b).1 hab
    exact ⟨a, b, hab, by simpa [cutInput, haz] using ha, by simpa [cutInput, hbz] using hb⟩

lemma reader_bound_peel (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (ho : C.output < n + C.size) (z : Fin n) (j : ℕ)
    (hj : j < C.size) (hand : (gateAt C j).op = GateOp.and)
    (hread : z.val ∈ (gateAt C j).inputs)
    (hbase : G.degree z ≤ 1 + (readers n C j).card)
    (hbonus : (∃ S : Finset (Fin n), CoverPromise.IsVertexCover
        (G.deleteEdges (G.incidenceSet z)) S ∧
        ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
      G.degree z ≤ (readers n C j).card) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D =
      (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
        (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true)
        (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧
      ((∃ S : Finset (Fin n), CoverPromise.IsVertexCover
        (G.deleteEdges (G.incidenceSet z)) S ∧
        ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
        D.size + G.degree z + 1 ≤ C.size) := by
  obtain ⟨D, hD, hs, hf⟩ := restrict_and_reader_saves C hC ho z j hj hand hread
  refine ⟨D, hD, ?_, by omega, ?_⟩
  · rw [hf, hfun]
    exact graph_cutInput G z
  · intro hd
    have hb := hbonus hd
    omega

lemma least_reader_peel (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C0 : Circuit) (hC0 : IsLeastAO G C0) (ho : C0.output < n + C0.size)
    (z : Fin n) (hpos : 0 < G.degree z) (j : ℕ)
    (hj : j < C0.size) (hand : (gateAt C0 j).op = GateOp.and)
    (hread : z.val ∈ (gateAt C0 j).inputs)
    (hbase : G.degree z ≤ 1 + (readers n C0 j).card)
    (hbonus : (∃ S : Finset (Fin n), CoverPromise.IsVertexCover
        (G.deleteEdges (G.incidenceSet z)) S ∧
        ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
      G.degree z ≤ (readers n C0 j).card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D =
      (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
        (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true)
        (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧
      ((∃ S : Finset (Fin n), CoverPromise.IsVertexCover
        (G.deleteEdges (G.incidenceSet z)) S ∧
        ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
        D.size + G.degree z + 1 ≤ C.size) := by
  obtain ⟨D, hD, hf, hs, hb⟩ := reader_bound_peel G C0 hC0.1 hC0.2.1 ho z j hj hand hread hbase hbonus
  refine ⟨z, hpos, fun C hC hF => ?_⟩
  have hmin := hC0.2.2 C hC hF
  exact ⟨D, hD, hf, hs.trans hmin, fun h => (hb h).trans hmin⟩

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.H4Support.GateSavings

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.H4Support.UniformSavingPeel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning GateSavings

variable {n : ℕ}

def UniformPeel (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Fin n) : Prop :=
  ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ →
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D =
      (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
        (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true)
        (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧
      ((∃ S : Finset (Fin n), CoverPromise.IsVertexCover
        (G.deleteEdges (G.incidenceSet z)) S ∧
        ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
        D.size + G.degree z + 1 ≤ C.size)

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.H4Support.UniformSavingPeel

namespace PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.SemanticPrivateReaderPeel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma uniform_peel {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (ho : C.output < n + C.size)
    (hTF : TopForm G C) (h4 : NoFourCycle G) (H : ℕ) (a : Fin n)
    (hpos : 0 < G.degree a) (hH : H < C.size)
    (hHa : (gateAt C H).op = .and) (haH : a.val ∈ (gateAt C H).inputs)
    (hdirty : ¬ BelowF G C H)
    (hsole : ∀ j, j < C.gates.length → a.val ∈ (gateAt C j).inputs → j = H)
    (hlast : ∀ k, H < k → k < C.gates.length → (gateAt C k).op = .and → BelowF G C k)
    (hreadOR : ∀ j ∈ readers n C H, (gateAt C j).op = .or)
    (hsingle : ∀ j ∈ readers n C H, ∃ T ∈ (gateAt C j).inputs, ∃ v : Fin n,
      v ≠ a ∧ ParallelRewrite.value C (pairInput v v) T = true) :
    ∃ z : Fin n, 0 < G.degree z ∧ H4Support.UniformSavingPeel.UniformPeel G z := by
  have hdeg := PrivateReaderDegree.degree_le_readers_of_singletons G C hC.1 hC.2.1 hTF h4 H a
    hdirty hsole hlast hreadOR hsingle
  exact H4Support.GateSavings.least_reader_peel G C hC ho a hpos H hH hHa haH
    (by omega) (fun _ => hdeg)

end PEqualNP.Outside.L_meta_3566.ReaderPeelSupport.SemanticPrivateReaderPeel
