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
open PEqualNP.MetaComplexity.NestedCover
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

lemma flags_or_true_of_mem (bs : List Bool) (g : Gate) (w : ℕ)
    (hlen : g.inputs.length = 2) (hmem : w ∈ g.inputs) (hflag : bs.getD w true = true) :
    (bs.getD (g.inputs.getD 0 0) true || bs.getD (g.inputs.getD 1 0) true) = true := by
  obtain ⟨a, b, hg⟩ := List.length_eq_two.mp hlen
  rw [hg] at hmem ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · change (bs.getD w true || bs.getD b true) = true
    simp only [hflag, Bool.true_or]
  · change (bs.getD a true || bs.getD w true) = true
    simp only [hflag, Bool.or_true]

lemma deadRun_pos_of_member (gs : List Gate) (bs : List Bool) (w : ℕ)
    (hw : w < bs.length) (hflag : bs.getD w true = true)
    (g : Gate) (hmem : g ∈ gs) (hlen : g.inputs.length = 2) (hread : w ∈ g.inputs) :
    1 ≤ (deadRun bs gs).2 := by
  induction gs generalizing bs with
  | nil => simp at hmem
  | cons a gs ih =>
    rcases List.mem_cons.mp hmem with rfl | hmem
    · have hk := flags_or_true_of_mem bs g w hlen hread hflag
      simp only [deadRun, hk, ↓reduceIte]
      omega
    · let v := blockStep a.op (bs.getD (a.inputs.getD 0 0) true)
        (bs.getD (a.inputs.getD 1 0) true)
      have hw' : w < (bs ++ [v]).length := by simp; omega
      have hf' : (bs ++ [v]).getD w true = true := by
        rw [List.getD_append _ _ _ _ hw]
        exact hflag
      have ht := ih (bs ++ [v]) hw' hf' hmem
      simp only [deadRun]
      change 1 ≤ _ + (deadRun (bs ++ [v]) gs).2
      omega

lemma two_count_of_and_reader (gs : List Gate) (bs : List Bool) (j w : ℕ)
    (hj : j < gs.length) (hw : w < bs.length) (hflag : bs.getD w true = true)
    (hop : (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and)
    (hlen : (gs.getD j ⟨GateOp.or, []⟩).inputs.length = 2)
    (hread : w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs)
    (g : Gate) (hmem : g ∈ gs.drop (j + 1)) (hglen : g.inputs.length = 2)
    (hreader : bs.length + j ∈ g.inputs) : 2 ≤ (deadRun bs gs).2 := by
  induction gs generalizing bs j with
  | nil => simp at hj
  | cons a gs ih =>
    cases j with
    | zero =>
      have hop' : a.op = GateOp.and := hop
      have hlen' : a.inputs.length = 2 := hlen
      have hread' : w ∈ a.inputs := hread
      have hk := flags_or_true_of_mem bs a w hlen' hread' hflag
      have hv : blockStep a.op (bs.getD (a.inputs.getD 0 0) true)
          (bs.getD (a.inputs.getD 1 0) true) = true := by
        simpa only [hop', blockStep] using hk
      have hm : g ∈ gs := by simpa using hmem
      have hr : bs.length ∈ g.inputs := by simpa using hreader
      have ht := deadRun_pos_of_member gs (bs ++ [true]) bs.length
        (by simp) (by simp) g hm hglen hr
      simp only [deadRun, hv, hk, ↓reduceIte]
      omega
    | succ j =>
      let v := blockStep a.op (bs.getD (a.inputs.getD 0 0) true)
        (bs.getD (a.inputs.getD 1 0) true)
      have hj' : j < gs.length := by simpa using hj
      have hw' : w < (bs ++ [v]).length := by simp; omega
      have hf' : (bs ++ [v]).getD w true = true := by
        rw [List.getD_append _ _ _ _ hw]
        exact hflag
      have hop' : (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and := hop
      have hlen' : (gs.getD j ⟨GateOp.or, []⟩).inputs.length = 2 := hlen
      have hread' : w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs := hread
      have hm : g ∈ gs.drop (j + 1) := by simpa using hmem
      have hr : (bs ++ [v]).length + j ∈ g.inputs := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hreader
      have ht := ih (bs ++ [v]) j hj' hw' hf' hop' hlen' hread' hm hr
      simp only [deadRun]
      change 2 ≤ _ + (deadRun (bs ++ [v]) gs).2
      omega

lemma list_getD_mem {α : Type} (gs : List α) (i : ℕ) (d : α) (hi : i < gs.length) :
    gs.getD i d ∈ gs := by
  induction gs generalizing i with
  | nil => simp at hi
  | cons a gs ih =>
    cases i with
    | zero => exact List.mem_cons_self
    | succ i => exact List.mem_cons_of_mem a (ih i (by simpa using hi))

lemma list_getD_mem_drop {α : Type} (gs : List α) (i k : ℕ) (d : α)
    (hik : i ≤ k) (hk : k < gs.length) : gs.getD k d ∈ gs.drop i := by
  induction gs generalizing i k with
  | nil => simp at hk
  | cons a gs ih =>
    cases i with
    | zero => exact list_getD_mem (a :: gs) k d hk
    | succ i =>
      cases k with
      | zero => omega
      | succ k => exact ih i k (by omega) (by simpa using hk)

lemma two_removed_of_and_reader (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C)
    (j k : ℕ) (hjk : j < k) (hk : k < C.size)
    (hop : (gateAt C j).op = GateOp.and)
    (hz : z.val ∈ (gateAt C j).inputs)
    (hr : n + j ∈ (gateAt C k).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      D.size + 2 ≤ C.size := by
  have hk' : k < C.gates.length := hk
  have hj : j < C.gates.length := by omega
  have hjmem : gateAt C j ∈ C.gates := list_getD_mem C.gates j _ hj
  have hkmem : gateAt C k ∈ C.gates := list_getD_mem C.gates k _ hk'
  have hm : gateAt C k ∈ C.gates.drop (j + 1) :=
    list_getD_mem_drop C.gates (j + 1) k _ (by omega) hk'
  have hb : (initialDead n z).length = n := by simp [initialDead]
  have hf : (initialDead n z).getD z.val true = true := by simp [initialDead]
  have hcnt : 2 ≤ blockedCount n z C :=
    two_count_of_and_reader C.gates (initialDead n z) j z.val hj
      (by rw [hb]; exact z.isLt) hf hop (hAO.2.2 _ hjmem) hz
      (gateAt C k) hm (hAO.2.2 _ hkmem) (by simpa only [hb] using hr)
  obtain ⟨D, hD, hF, hsize⟩ := exists_blocked_restriction n z C hAO
  exact ⟨D, hD, hF, by omega⟩

def directCount (w : ℕ) (gs : List Gate) : ℕ :=
  (gs.filter (fun g => decide (w ∈ g.inputs))).length

def headScore (bs : List Bool) (g : Gate) : ℕ :=
  if bs.getD (g.inputs.getD 0 0) true || bs.getD (g.inputs.getD 1 0) true then 1 else 0

def nextDead (bs : List Bool) (g : Gate) : List Bool :=
  bs ++ [blockStep g.op (bs.getD (g.inputs.getD 0 0) true)
    (bs.getD (g.inputs.getD 1 0) true)]

lemma directCount_cons (w : ℕ) (g : Gate) (gs : List Gate) :
    directCount w (g :: gs) = (if w ∈ g.inputs then 1 else 0) + directCount w gs := by
  by_cases h : w ∈ g.inputs <;> simp [directCount, h, Nat.add_comm]

lemma deadRun_cons_count (bs : List Bool) (g : Gate) (gs : List Gate) :
    (deadRun bs (g :: gs)).2 = headScore bs g + (deadRun (nextDead bs g) gs).2 := rfl

lemma nextDead_length (bs : List Bool) (g : Gate) : (nextDead bs g).length = bs.length + 1 := by
  simp [nextDead]

lemma nextDead_old (bs : List Bool) (g : Gate) (w : ℕ) (hw : w < bs.length) :
    (nextDead bs g).getD w true = bs.getD w true :=
  List.getD_append _ _ _ _ hw

lemma headScore_eq_one (bs : List Bool) (g : Gate) (w : ℕ)
    (hlen : g.inputs.length = 2) (hmem : w ∈ g.inputs) (hflag : bs.getD w true = true) :
    headScore bs g = 1 := by
  have hk := flags_or_true_of_mem bs g w hlen hmem hflag
  simp only [headScore, hk, ↓reduceIte]

lemma headScore_ge_direct (bs : List Bool) (g : Gate) (w : ℕ)
    (hlen : g.inputs.length = 2) (hflag : bs.getD w true = true) :
    (if w ∈ g.inputs then 1 else 0) ≤ headScore bs g := by
  by_cases hmem : w ∈ g.inputs
  · simp only [hmem, ↓reduceIte, headScore_eq_one bs g w hlen hmem hflag]
    exact le_rfl
  · simp only [hmem, ↓reduceIte]
    exact Nat.zero_le _

lemma direct_count_le_dead (gs : List Gate) (bs : List Bool) (w : ℕ)
    (hw : w < bs.length) (hflag : bs.getD w true = true)
    (hlen : ∀ g ∈ gs, g.inputs.length = 2) : directCount w gs ≤ (deadRun bs gs).2 := by
  induction gs generalizing bs with
  | nil => simp [directCount, deadRun]
  | cons g gs ih =>
    have hlen' : ∀ g' ∈ gs, g'.inputs.length = 2 :=
      fun g' hg' => hlen g' (List.mem_cons_of_mem g hg')
    have hw' : w < (nextDead bs g).length := by rw [nextDead_length]; omega
    have hf' : (nextDead bs g).getD w true = true := by rw [nextDead_old _ _ _ hw]; exact hflag
    have ht := ih (nextDead bs g) hw' hf' hlen'
    have hh := headScore_ge_direct bs g w (hlen g List.mem_cons_self) hflag
    rw [directCount_cons, deadRun_cons_count]
    omega

lemma direct_count_extra (gs : List Gate) (bs : List Bool) (w u : ℕ)
    (hw : w < bs.length) (hu : u < bs.length)
    (hflag : bs.getD w true = true) (huflag : bs.getD u true = true)
    (hlen : ∀ a ∈ gs, a.inputs.length = 2)
    (g : Gate) (hmem : g ∈ gs) (hread : u ∈ g.inputs) (hnot : w ∉ g.inputs) :
    directCount w gs + 1 ≤ (deadRun bs gs).2 := by
  induction gs generalizing bs with
  | nil => simp at hmem
  | cons a gs ih =>
    have hlen' : ∀ g' ∈ gs, g'.inputs.length = 2 :=
      fun g' hg' => hlen g' (List.mem_cons_of_mem a hg')
    have hw' : w < (nextDead bs a).length := by rw [nextDead_length]; omega
    have hu' : u < (nextDead bs a).length := by rw [nextDead_length]; omega
    have hf' : (nextDead bs a).getD w true = true := by rw [nextDead_old _ _ _ hw]; exact hflag
    have huf' : (nextDead bs a).getD u true = true := by rw [nextDead_old _ _ _ hu]; exact huflag
    rcases List.mem_cons.mp hmem with rfl | hmem
    · have ht := direct_count_le_dead gs (nextDead bs g) w hw' hf' hlen'
      have hh := headScore_eq_one bs g u (hlen g List.mem_cons_self) hread huflag
      rw [directCount_cons, deadRun_cons_count, hh]
      simp only [hnot, ↓reduceIte, zero_add]
      omega
    · have ht := ih (nextDead bs a) hw' hu' hf' huf' hlen' hmem
      have hh := headScore_ge_direct bs a w (hlen a List.mem_cons_self) hflag
      rw [directCount_cons, deadRun_cons_count]
      omega

lemma direct_count_extra_after_and (gs : List Gate) (bs : List Bool) (j w : ℕ)
    (hj : j < gs.length) (hw : w < bs.length) (hflag : bs.getD w true = true)
    (hlen : ∀ a ∈ gs, a.inputs.length = 2)
    (hop : (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and)
    (hread : w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs)
    (g : Gate) (hmem : g ∈ gs.drop (j + 1))
    (hreader : bs.length + j ∈ g.inputs) (hnot : w ∉ g.inputs) :
    directCount w gs + 1 ≤ (deadRun bs gs).2 := by
  induction gs generalizing bs j with
  | nil => simp at hj
  | cons a gs ih =>
    have hlen' : ∀ g' ∈ gs, g'.inputs.length = 2 :=
      fun g' hg' => hlen g' (List.mem_cons_of_mem a hg')
    have hw' : w < (nextDead bs a).length := by rw [nextDead_length]; omega
    have hf' : (nextDead bs a).getD w true = true := by rw [nextDead_old _ _ _ hw]; exact hflag
    cases j with
    | zero =>
      have hop' : a.op = GateOp.and := hop
      have hread' : w ∈ a.inputs := hread
      have hk := flags_or_true_of_mem bs a w (hlen a List.mem_cons_self) hread' hflag
      have hu : bs.length < (nextDead bs a).length := by rw [nextDead_length]; omega
      have huf : (nextDead bs a).getD bs.length true = true := by
        simp only [nextDead, getD_snoc_eq, hop', blockStep]
        exact hk
      have hm : g ∈ gs := by simpa using hmem
      have hr : bs.length ∈ g.inputs := by simpa using hreader
      have ht := direct_count_extra gs (nextDead bs a) w bs.length hw' hu hf' huf
        hlen' g hm hr hnot
      have hh := headScore_eq_one bs a w (hlen a List.mem_cons_self) hread' hflag
      rw [directCount_cons, deadRun_cons_count, hh]
      simp only [hread', ↓reduceIte]
      omega
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have hop' : (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and := hop
      have hread' : w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs := hread
      have hm : g ∈ gs.drop (j + 1) := by simpa using hmem
      have hr : (nextDead bs a).length + j ∈ g.inputs := by
        simpa only [nextDead_length, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hreader
      have ht := ih (nextDead bs a) j hj' hw' hf' hlen' hop' hread' hm hr
      have hh := headScore_ge_direct bs a w (hlen a List.mem_cons_self) hflag
      rw [directCount_cons, deadRun_cons_count]
      omega

lemma direct_readers_plus_one (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C)
    (j k : ℕ) (hjk : j < k) (hk : k < C.size)
    (hop : (gateAt C j).op = GateOp.and)
    (hz : z.val ∈ (gateAt C j).inputs)
    (hr : n + j ∈ (gateAt C k).inputs) (hnot : z.val ∉ (gateAt C k).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      D.size + (C.gates.filter (fun g => decide (z.val ∈ g.inputs))).length + 1 ≤ C.size := by
  have hk' : k < C.gates.length := hk
  have hj : j < C.gates.length := by omega
  have hm : gateAt C k ∈ C.gates.drop (j + 1) :=
    list_getD_mem_drop C.gates (j + 1) k _ (by omega) hk'
  have hb : (initialDead n z).length = n := by simp [initialDead]
  have hf : (initialDead n z).getD z.val true = true := by simp [initialDead]
  have hcnt : directCount z.val C.gates + 1 ≤ blockedCount n z C :=
    direct_count_extra_after_and C.gates (initialDead n z) j z.val hj
      (by rw [hb]; exact z.isLt) hf hAO.2.2 hop hz
      (gateAt C k) hm (by simpa only [hb] using hr) hnot
  obtain ⟨D, hD, hF, hsize⟩ := exists_blocked_restriction n z C hAO
  exact ⟨D, hD, hF, by change _ + directCount z.val C.gates + 1 ≤ _; omega⟩

end PEqualNP.Outside.L_meta_3566.FalseRestrict


namespace PEqualNP.Outside.L_meta_3566.EdgeProfile

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma eq_of_edges_and_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (F : (Fin n → Bool) → Bool)
    (hMono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      F x = true → F y = true)
    (hBelow : ∀ x, F x = true → graphFun G ∅ x = true)
    (hEdges : ∀ a b : Fin n, G.Adj a b → F (pairInput a b) = true) :
    F = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hBelow x
  · intro hx
    have hx' : ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true := by
      simpa [graphFun] using hx
    obtain ⟨a, b, hab, ha, hb⟩ := hx'
    apply hMono (pairInput a b) x _ (hEdges a b hab)
    intro i hi
    have h : i = a ∨ i = b := by simpa [pairInput] using hi
    rcases h with rfl | rfl <;> assumption

lemma narrow_first_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (z : Fin n) (hz : z ∈ A)
    (hStar : ∀ a b : Fin n, G.Adj a b →
      (∃ u ∈ A, u = a ∨ u = b) → (∃ v ∈ B, v = a ∨ v = b) → z = a ∨ z = b) :
    (∀ x : Fin n → Bool,
      (x z && decide (∃ v ∈ B, x v = true)) = true →
      (decide (∃ u ∈ A, x u = true) && decide (∃ v ∈ B, x v = true)) = true) ∧
    (∀ a b : Fin n, G.Adj a b →
      ((pairInput a b z) && decide (∃ v ∈ B, pairInput a b v = true)) =
      (decide (∃ u ∈ A, pairInput a b u = true) &&
        decide (∃ v ∈ B, pairInput a b v = true))) := by
  constructor
  · intro x hx
    have hx' : x z = true ∧ decide (∃ v ∈ B, x v = true) = true := by simpa using hx
    obtain ⟨hxz, hB⟩ := hx'
    have hA : decide (∃ u ∈ A, x u = true) = true := by
      simpa using (show ∃ u ∈ A, x u = true from ⟨z, hz, hxz⟩)
    simp [hA, hB]
  · intro a b hab
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_iff]
    constructor
    · rintro ⟨hzab, hB⟩
      exact ⟨⟨z, hz, hzab⟩, hB⟩
    · rintro ⟨hA, hB⟩
      refine ⟨?_, hB⟩
      have hA' : ∃ u ∈ A, u = a ∨ u = b := by simpa [pairInput] using hA
      have hB' : ∃ v ∈ B, v = a ∨ v = b := by simpa [pairInput] using hB
      simpa [pairInput] using hStar a b hab hA' hB'

end PEqualNP.Outside.L_meta_3566.EdgeProfile


namespace PEqualNP.Outside.L_meta_3566.LeafStep

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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.AO2Upper

lemma wiresFrom_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  conv_lhs => rw [hsplit]
  rw [wiresFrom_append]
  have hW : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [length_wiresFrom]
    simp [Nat.le_of_lt hj]
  change (wiresFrom (gs.drop (j + 1))
    (wiresFrom (gs.take j) w ++ [(gs[j]).op.eval ((gs[j]).inputs.map fun i =>
      (wiresFrom (gs.take j) w).getD i false)] )).getD _ false = _
  rw [getD_wiresFrom _ _ _ (by simp [hW])]
  rw [← hW, getD_snoc_eq]

lemma and_input_false {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.size)
    (hop : (gateAt C j).op = GateOp.and)
    (z : Fin n) (hz : z.val ∈ (gateAt C j).inputs)
    (x : Fin n → Bool) (hx : x z = false) :
    (C.wires (List.ofFn x)).getD (n + j) false = false := by
  have hj' : j < C.gates.length := hj
  have hg : gateAt C j = C.gates[j] := by simp [gateAt, List.getD, hj']
  have hop' : (C.gates[j]).op = GateOp.and := by simpa only [hg] using hop
  have hz' : z.val ∈ (C.gates[j]).inputs := by simpa only [hg] using hz
  change (wiresFrom C.gates (List.ofFn x)).getD (n + j) false = false
  have h := wiresFrom_gate C.gates (List.ofFn x) j hj'
  simp only [List.length_ofFn] at h
  rw [h, hop']
  simp only [GateOp.eval, List.all_eq_false]
  refine ⟨false, List.mem_map.mpr ⟨z.val, hz', ?_⟩, by simp⟩
  rw [getD_wiresFrom _ _ _ (by simp), getD_ofFn, hx]

lemma reader_of_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (j : ℕ) (hj : j < C.size) (ho : C.output < n + C.size)
    (hjo : C.output ≠ n + j) :
    ∃ k : ℕ, j < k ∧ k < C.size ∧ n + j ∈ (gateAt C k).inputs := by
  classical
  by_contra h
  have hread : ∀ k < C.size, k ≠ j → n + j ∉ (gateAt C k).inputs := by
    intro k hk _ hmem
    have hback := hC.1.2.1 k hk (n + j) hmem
    exact h ⟨k, by omega, hk, hmem⟩
  obtain ⟨D, hD, hs, hf⟩ := Pruning.erase_unread C hC.1 j hj hread ho hjo
  have hmin := hC.2.2 D hD (hf.trans hC.2.1)
  omega

lemma leaf_and_restriction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : 2 ≤ G.edgeFinset.card) (C : Circuit) (hC : IsLeastAO G C)
    (z : Fin n) (hdeg : G.degree z = 1)
    (j : ℕ) (hj : j < C.size) (hop : (gateAt C j).op = GateOp.and)
    (hz : z.val ∈ (gateAt C j).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      D.size + 2 ≤ C.size := by
  classical
  have hcount := PEqualNP.Outside.L_meta_3566.cut_edge_count G z
  have hnon : (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨e, he⟩ := hnon
  have hadj : ∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b := by
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    exact ⟨a, b, by simpa using he⟩
  obtain ⟨a, b, hab⟩ := hadj
  obtain ⟨hab, haz, hbz⟩ := (PEqualNP.Outside.L_meta_3566.cut_adj G z a b).mp hab
  let x : Fin n → Bool := Function.update (fun _ => true) z false
  have hx : x z = false := by simp [x]
  have hxa : x a = true := by simp [x, haz]
  have hxb : x b = true := by simp [x, hbz]
  have htrue : circuitFun n C x = true := by
    rw [hC.2.1]
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    exact ⟨a, b, hab, hxa, hxb⟩
  have hfalse := and_input_false C j hj hop z hz x hx
  have hjo : C.output ≠ n + j := by
    intro h
    change (C.wires (List.ofFn x)).getD C.output false = true at htrue
    rw [h, hfalse] at htrue
    exact Bool.false_ne_true htrue
  have ho : C.output < n + C.size := by
    by_contra h
    have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
      exact (length_wiresFrom C.gates (List.ofFn x)).trans (by simp [Circuit.size])
    change (C.wires (List.ofFn x)).getD C.output false = true at htrue
    rw [List.getD_eq_default _ _ (by omega)] at htrue
    exact Bool.false_ne_true htrue
  obtain ⟨k, hjk, hk, hr⟩ := reader_of_least G C hC j hj ho hjo
  exact PEqualNP.Outside.L_meta_3566.FalseRestrict.two_removed_of_and_reader
    n z C hC.1 j k hjk hk hop hz hr

end PEqualNP.Outside.L_meta_3566.LeafStep


namespace PEqualNP.Outside.L_meta_3566.Absorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.LeafStep.Pruning

lemma erase_equivalent (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (k r : ℕ)
    (hk : k < C.size) (hr : r < n + k) (ho : C.output < n + C.size)
    (heq : ∀ x : Fin n → Bool, wireVal n C (n + k) x = wireVal n C r x) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 1 ≤ C.size ∧
      circuitFun n D = circuitFun n C := by
  classical
  let K := Finset.range C.size \ {k}
  let red : ℕ → Src n ℕ := fun w => if w = n + k then srcOf n r else srcOf n w
  let P : Prog n ℕ := progOf C fun i b => red (opnd C i b)
  let v : ℕ → (Fin n → Bool) → Bool := fun i x => PEqualNP.EdgeOwnership.gateVal n C i x
  have hmem (i : ℕ) (hi : i < C.size) (b : Fin 2) :
      opnd C i b ∈ (gateAt C i).inputs := by
    have hg : gateAt C i ∈ C.gates :=
      PEqualNP.Outside.L_meta_3566.FalseRestrict.list_getD_mem C.gates i _ hi
    have hlen := hC.2.2 _ hg
    obtain ⟨a, d, h⟩ := List.length_eq_two.mp hlen
    fin_cases b <;> simp [opnd, h]
  have hred (w j : ℕ) (hw : w < n + C.size) (h : red w = some (Sum.inr j)) :
      j ∈ K := by
    dsimp [red] at h
    split_ifs at h with hcase
    · have hj := srcOf_inr r j h
      apply Finset.mem_sdiff.mpr
      constructor
      · apply Finset.mem_range.mpr
        omega
      · simp only [Finset.mem_singleton]
        omega
    · have hj := srcOf_inr w j h
      apply Finset.mem_sdiff.mpr
      constructor
      · apply Finset.mem_range.mpr
        omega
      · simp only [Finset.mem_singleton]
        omega
  have hcl : Closed P id K := by
    intro i hi b j h
    have hi' : i < C.size := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
    have hb := hC.2.1 i hi' (opnd C i b) (hmem i hi' b)
    change red (opnd C i b) = some (Sum.inr j) at h
    refine ⟨hred _ j (by omega) h, ?_⟩
    dsimp [red] at h
    split_ifs at h with hcase
    · have hj := srcOf_inr r j h
      change j < i
      omega
    · have hj := srcOf_inr (opnd C i b) j h
      change j < i
      omega
  have hval (w : ℕ) (x : Fin n → Bool) :
      srcAt x (fun j => v j x) (red w) = wireVal n C w x := by
    dsimp [red, v]
    split_ifs with h
    · rw [srcAt_srcOf]
      rw [h]
      exact (heq x).symm
    · exact srcAt_srcOf C w x
  have hsol : Sol P K v := by
    intro x i hi
    have hi' : i < C.size := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
    change PEqualNP.EdgeOwnership.gateVal n C i x =
      opv (isA (gateAt C i).op)
        (srcAt x (fun j => v j x) (red (opnd C i 0)))
        (srcAt x (fun j => v j x) (red (opnd C i 1)))
    rw [hval, hval]
    exact gate_eq C hC i hi' x
  have hout : ∀ j, red C.output = some (Sum.inr j) → j ∈ K :=
    fun j h => hred C.output j ho h
  obtain ⟨D, hD, hsize, hfun⟩ := fold_total P id v K hcl hsol (red C.output) hout
  have hsub : {k} ⊆ Finset.range C.size := by simpa using hk
  have hcard : K.card + 1 = C.size := by
    simpa [K] using Finset.card_sdiff_add_card_eq_card hsub
  have hkept : (kept P v K).card ≤ K.card := Finset.card_filter_le _ _
  refine ⟨D, hD, by omega, ?_⟩
  funext x
  rw [hfun x, hval]
  rfl

lemma least_no_equivalent (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (k r : ℕ)
    (hk : k < C.size) (hr : r < n + k) (ho : C.output < n + C.size) :
    ¬ (∀ x : Fin n → Bool, wireVal n C (n + k) x = wireVal n C r x) := by
  intro heq
  obtain ⟨D, hD, hsize, hfun⟩ := erase_equivalent n C hC.1 k r hk hr ho heq
  have hmin := hC.2.2 D hD (hfun.trans hC.2.1)
  omega

lemma and_gate_true_input (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.size)
    (hop : (gateAt C j).op = GateOp.and) (z : Fin n)
    (hz : z.val ∈ (gateAt C j).inputs) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = true → x z = true := by
  intro ht
  by_contra hn
  have hx : x z = false := by cases h : x z <;> simp_all
  have hf := PEqualNP.Outside.L_meta_3566.LeafStep.and_input_false C j hj hop z hz x hx
  change (C.wires (List.ofFn x)).getD (n + j) false = true at ht
  rw [hf] at ht
  exact Bool.false_ne_true ht

lemma two_inputs_of_mem (xs : List ℕ) (hlen : xs.length = 2) (a b : ℕ)
    (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) : xs = [a, b] ∨ xs = [b, a] := by
  obtain ⟨u, v, h⟩ := List.length_eq_two.mp hlen
  simp only [h, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hne rfl).elim
  · exact Or.inl h
  · exact Or.inr h
  · exact (hne rfl).elim

lemma and_eq_of_imp (p q : Bool) (h : q = true → p = true) : (p && q) = q := by
  cases p <;> cases q <;> simp_all

lemma or_eq_of_imp (p q : Bool) (h : q = true → p = true) : (p || q) = p := by
  cases p <;> cases q <;> simp_all

lemma least_reader_not_input (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (z : Fin n) (j k : ℕ)
    (hj : j < C.size) (hk : k < C.size)
    (hop : (gateAt C j).op = GateOp.and) (hz : z.val ∈ (gateAt C j).inputs)
    (hr : n + j ∈ (gateAt C k).inputs) (ho : C.output < n + C.size) :
    z.val ∉ (gateAt C k).inputs := by
  intro hzk
  have hback := hC.1.2.1 k hk (n + j) hr
  have hkmem : gateAt C k ∈ C.gates :=
    PEqualNP.Outside.L_meta_3566.FalseRestrict.list_getD_mem C.gates k _ hk
  have hkop := hC.1.1 _ hkmem
  have hlen := hC.1.2.2 _ hkmem
  have hne : z.val ≠ n + j := by have := z.isLt; omega
  have hins := two_inputs_of_mem (gateAt C k).inputs hlen z.val (n + j) hzk hr hne
  have hcomp (x : Fin n → Bool) :
      wireVal n C (n + k) x = (gateAt C k).op.eval
        [x z, PEqualNP.EdgeOwnership.gateVal n C j x] := by
    have h := gate_eq C hC.1 k hk x
    change wireVal n C (n + k) x = _ at h
    have hzv : wireVal n C z.val x = x z := wireVal_lt C z.val z.isLt x
    have hjv : wireVal n C (n + j) x = PEqualNP.EdgeOwnership.gateVal n C j x := rfl
    rcases hins with hlist | hlist <;> rcases hkop with hkand | hkor
    · simpa [opnd, hlist, hkand, isA, opv, GateOp.eval, hzv, hjv] using h
    · simpa [opnd, hlist, hkor, isA, opv, GateOp.eval, hzv, hjv] using h
    · simpa [opnd, hlist, hkand, isA, opv, GateOp.eval, hzv, hjv, Bool.and_comm] using h
    · simpa [opnd, hlist, hkor, isA, opv, GateOp.eval, hzv, hjv, Bool.or_comm] using h
  rcases hkop with hkand | hkor
  · apply least_no_equivalent n G C hC k (n + j) hk hback ho
    intro x
    change wireVal n C (n + k) x = PEqualNP.EdgeOwnership.gateVal n C j x
    rw [hcomp, hkand]
    simpa [GateOp.eval] using and_eq_of_imp (x z)
      (PEqualNP.EdgeOwnership.gateVal n C j x) (and_gate_true_input n C j hj hop z hz x)
  · apply least_no_equivalent n G C hC k z.val hk (by have := z.isLt; omega) ho
    intro x
    rw [wireVal_lt C z.val z.isLt x, hcomp, hkor]
    simpa [GateOp.eval] using or_eq_of_imp (x z)
      (PEqualNP.EdgeOwnership.gateVal n C j x) (and_gate_true_input n C j hj hop z hz x)

end PEqualNP.Outside.L_meta_3566.Absorption

namespace PEqualNP.Outside.L_meta_3566.FanoutStep

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.AO2Upper
  PEqualNP.Outside.L_meta_3566.LeafStep

lemma and_restriction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (z : Fin n)
    (hnon : (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty)
    (j : ℕ) (hj : j < C.size) (hop : (gateAt C j).op = GateOp.and)
    (hz : z.val ∈ (gateAt C j).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      D.size + (C.gates.filter (fun g => decide (z.val ∈ g.inputs))).length + 1 ≤ C.size := by
  classical
  obtain ⟨e, he⟩ := hnon
  have hadj : ∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b := by
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    exact ⟨a, b, by simpa using he⟩
  obtain ⟨a, b, hab⟩ := hadj
  obtain ⟨hab, haz, hbz⟩ := (PEqualNP.Outside.L_meta_3566.cut_adj G z a b).mp hab
  let x : Fin n → Bool := Function.update (fun _ => true) z false
  have hx : x z = false := by simp [x]
  have hxa : x a = true := by simp [x, haz]
  have hxb : x b = true := by simp [x, hbz]
  have htrue : circuitFun n C x = true := by
    rw [hC.2.1]
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    exact ⟨a, b, hab, hxa, hxb⟩
  have hfalse := and_input_false C j hj hop z hz x hx
  have hjo : C.output ≠ n + j := by
    intro h
    change (C.wires (List.ofFn x)).getD C.output false = true at htrue
    rw [h, hfalse] at htrue
    exact Bool.false_ne_true htrue
  have ho : C.output < n + C.size := by
    by_contra h
    have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
      exact (length_wiresFrom C.gates (List.ofFn x)).trans (by simp [Circuit.size])
    change (C.wires (List.ofFn x)).getD C.output false = true at htrue
    rw [List.getD_eq_default _ _ (by omega)] at htrue
    exact Bool.false_ne_true htrue
  obtain ⟨k, hjk, hk, hr⟩ := reader_of_least G C hC j hj ho hjo
  have hnot := Absorption.least_reader_not_input n G C hC z j k hj hk hop hz hr ho
  exact FalseRestrict.direct_readers_plus_one n z C hC.1 j k hjk hk hop hz hr hnot

end PEqualNP.Outside.L_meta_3566.FanoutStep


namespace PEqualNP.Outside.L_meta_3566.FanoutStep

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma graphFun_update_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) :
    (fun x : Fin n → Bool => graphFun G ∅ (Function.update x z false)) =
      (fun x : Fin n → Bool => @decide (∃ a b : Fin n,
        (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ x a = true ∧ x b = true)
          (Classical.propDecidable _)) := by
  classical
  funext x
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  congr 1
  apply propext
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have haz : a ≠ z := by rintro rfl; simp at ha
    have hbz : b ≠ z := by rintro rfl; simp at hb
    exact ⟨a, b, (cut_adj G z a b).mpr ⟨hab, haz, hbz⟩,
      by simpa [haz] using ha, by simpa [hbz] using hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hab, haz, hbz⟩ := (cut_adj G z a b).mp hab
    exact ⟨a, b, hab, by simpa [haz] using ha, by simpa [hbz] using hb⟩

lemma witness_of_direct_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (z : Fin n) (hpos : 0 < G.degree z)
    (hnon : (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty)
    (j : ℕ) (hj : j < C.size) (hop : (gateAt C j).op = GateOp.and)
    (hz : z.val ∈ (gateAt C j).inputs)
    (hcount : G.degree z ≤ (C.gates.filter (fun g => decide (z.val ∈ g.inputs))).length) :
    0 < G.degree z ∧ ∀ C' : Circuit, IsAO2 n C' → circuitFun n C' = graphFun G ∅ →
      ∃ D : Circuit, IsAO2 n D ∧
        circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
          (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true)
            (Classical.propDecidable _)) ∧
        D.size + G.degree z ≤ C'.size ∧
        ((∃ S : Finset (Fin n), CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
          ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
          D.size + G.degree z + 1 ≤ C'.size) := by
  obtain ⟨D, hD, hfun, hsize⟩ := and_restriction G C hC z hnon j hj hop hz
  have hgraph : circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
      (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true)
        (Classical.propDecidable _)) := by
    rw [hfun, hC.2.1, graphFun_update_false]
  refine ⟨hpos, ?_⟩
  intro C' hC' hfun'
  have hmin := hC.2.2 C' hC' hfun'
  exact ⟨D, hD, hgraph, by omega, fun _ => by omega⟩

end PEqualNP.Outside.L_meta_3566.FanoutStep



namespace PEqualNP.Outside.L_meta_3566.PrivateCone

open PEqualNP.EdgeOwnership

lemma input_card_le_gates_add_one (n : ℕ) (K : Finset ℕ) (r : ℕ) (hr : r ∈ K)
    (port : ℕ → Fin 2 → ℕ) (S : Finset (Fin n))
    (hInputs : ∀ v ∈ S, ∃ g ∈ K, ∃ b : Fin 2, port g b = v.val)
    (hRead : ∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, port h b = n + g) :
    S.card ≤ K.card + 1 := by
  classical
  let slots := K ×ˢ (Finset.univ : Finset (Fin 2))
  let I := slots.image (fun p => port p.1 p.2)
  have hS : S.card ≤ (I.filter (fun w => w < n)).card := by
    apply Finset.card_le_card_of_injOn (fun v : Fin n => v.val)
    · intro v hv
      obtain ⟨g, hg, b, hb⟩ := hInputs v hv
      apply Finset.mem_filter.mpr
      refine ⟨?_, v.isLt⟩
      exact Finset.mem_image.mpr ⟨(g, b), Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩, hb⟩
    · intro a _ b _ h
      exact Fin.ext h
  have hK : (K.erase r).card ≤ (I.filter (fun w => ¬ w < n)).card := by
    apply Finset.card_le_card_of_injOn (fun g : ℕ => n + g)
    · intro g hg
      obtain ⟨h, hh, b, hb⟩ := hRead g hg
      apply Finset.mem_filter.mpr
      refine ⟨?_, by change ¬ n + g < n; omega⟩
      exact Finset.mem_image.mpr ⟨(h, b), Finset.mem_product.mpr ⟨hh, Finset.mem_univ _⟩, hb⟩
    · intro a _ b _ h
      exact Nat.add_left_cancel h
  have hSplit := Finset.card_filter_add_card_filter_not (s := I) (fun w => w < n)
  have hPorts : slots.card = K.card * 2 := by simp [slots]
  have hImage : I.card ≤ slots.card := Finset.card_image_le
  have hErase := Finset.card_erase_of_mem hr
  have hPos := Finset.card_pos.mpr ⟨r, hr⟩
  omega

lemma degree_le_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (S : Finset (Fin n)) (hz : z ∉ S)
    (H : (Fin n → Bool) → Bool) (hZero : H (fun _ => false) = false)
    (hSupport : ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → H x = H y)
    (hEdges : ∀ w : Fin n, G.Adj z w → H (pairInput z w) = true) :
    G.degree z ≤ S.card := by
  change (G.neighborFinset z).card ≤ S.card
  apply Finset.card_le_card
  intro w hw
  have hzw := (G.mem_neighborFinset z w).mp hw
  by_contra hwS
  have heq : H (pairInput z w) = H (fun _ => false) := by
    apply hSupport
    intro i hi
    have hiz : i ≠ z := by rintro rfl; exact hz hi
    have hiw : i ≠ w := by rintro rfl; exact hwS hi
    simp [pairInput, hiz, hiw]
  have htrue := hEdges w hzw
  rw [heq, hZero] at htrue
  exact Bool.false_ne_true htrue

lemma degree_le_singleton_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (S : Finset (Fin n))
    (H : (Fin n → Bool) → Bool) (hZero : H (fun _ => false) = false)
    (hSupport : ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → H x = H y)
    (hEdges : ∀ w : Fin n, G.Adj z w → H (pairInput w w) = true) :
    G.degree z ≤ S.card := by
  change (G.neighborFinset z).card ≤ S.card
  apply Finset.card_le_card
  intro w hw
  have hzw := (G.mem_neighborFinset z w).mp hw
  by_contra hwS
  have heq : H (pairInput w w) = H (fun _ => false) := by
    apply hSupport
    intro i hi
    have hiw : i ≠ w := by rintro rfl; exact hwS hi
    simp [pairInput, hiw]
  have htrue := hEdges w hzw
  rw [heq, hZero] at htrue
  exact Bool.false_ne_true htrue

lemma degree_le_private_gates {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (K : Finset ℕ) (r : ℕ) (hr : r ∈ K)
    (port : ℕ → Fin 2 → ℕ) (S : Finset (Fin n)) (hz : z ∉ S)
    (hInputs : ∀ v ∈ S, ∃ g ∈ K, ∃ b : Fin 2, port g b = v.val)
    (hRead : ∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, port h b = n + g)
    (H : (Fin n → Bool) → Bool) (hZero : H (fun _ => false) = false)
    (hSupport : ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → H x = H y)
    (hEdges : ∀ w : Fin n, G.Adj z w → H (pairInput z w) = true) :
    G.degree z ≤ K.card + 1 :=
  (degree_le_support G z S hz H hZero hSupport hEdges).trans
    (input_card_le_gates_add_one n K r hr port S hInputs hRead)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.LeafStep.Pruning

lemma port_mem (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.size)
    (b : Fin 2) : opnd C j b ∈ (gateAt C j).inputs := by
  have hg : gateAt C j ∈ C.gates :=
    PEqualNP.Outside.L_meta_3566.FalseRestrict.list_getD_mem C.gates j _ hj
  obtain ⟨a, d, h⟩ := List.length_eq_two.mp (hC.2.2 _ hg)
  fin_cases b <;> simp [opnd, h]

lemma gate_zero (n : ℕ) (C : Circuit) (hC : IsAO2 n C) :
    ∀ j, j < C.size → gateVal n C j (fun _ => false) = false := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    rw [gate_eq C hC j hj]
    have hsrc (b : Fin 2) : wireVal n C (opnd C j b) (fun _ => false) = false := by
      by_cases hw : opnd C j b < n
      · rw [wireVal_lt C _ hw]
      · have hback := hC.2.1 j hj (opnd C j b) (port_mem n C hC j hj b)
        have he : n + (opnd C j b - n) = opnd C j b := by omega
        rw [← he]
        change gateVal n C (opnd C j b - n) (fun _ => false) = false
        exact ih _ (by omega) (by omega)
    rw [hsrc 0, hsrc 1]
    simp [opv]

lemma cone_agree (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (K : Finset ℕ)
    (hK : ∀ j ∈ K, j < C.size)
    (hClosed : ∀ j ∈ K, ∀ b : Fin 2, n ≤ opnd C j b → opnd C j b - n ∈ K)
    (S : Finset (Fin n))
    (hInputs : ∀ j ∈ K, ∀ b : Fin 2, ∀ hw : opnd C j b < n,
      (⟨opnd C j b, hw⟩ : Fin n) ∈ S)
    (x y : Fin n → Bool) (hxy : ∀ v ∈ S, x v = y v) :
    ∀ r ∈ K, gateVal n C r x = gateVal n C r y := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr
    have hrlt := hK r hr
    have hsrc (b : Fin 2) : wireVal n C (opnd C r b) x = wireVal n C (opnd C r b) y := by
      by_cases hw : opnd C r b < n
      · rw [wireVal_lt C _ hw x, wireVal_lt C _ hw y]
        exact hxy _ (hInputs r hr b hw)
      · have hback := hC.2.1 r hrlt (opnd C r b) (port_mem n C hC r hrlt b)
        have he : n + (opnd C r b - n) = opnd C r b := by omega
        rw [← he]
        change gateVal n C (opnd C r b - n) x = gateVal n C (opnd C r b - n) y
        exact ih _ (by omega) (hClosed r hr b (by omega))
    rw [gate_eq C hC r hrlt x, gate_eq C hC r hrlt y, hsrc 0, hsrc 1]

lemma degree_le_closed_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (C : Circuit) (hC : IsAO2 n C)
    (K : Finset ℕ) (r : ℕ) (hr : r ∈ K)
    (hK : ∀ j ∈ K, j < C.size)
    (hClosed : ∀ j ∈ K, ∀ b : Fin 2, n ≤ opnd C j b → opnd C j b - n ∈ K)
    (hRead : ∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, opnd C h b = n + g)
    (hEdges : ∀ w : Fin n, G.Adj z w → gateVal n C r (pairInput w w) = true) :
    G.degree z ≤ K.card + 1 := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun v => ∃ g ∈ K, ∃ b : Fin 2, opnd C g b = v.val
  have hInputs : ∀ v ∈ S, ∃ g ∈ K, ∃ b : Fin 2, opnd C g b = v.val := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hBare : ∀ j ∈ K, ∀ b : Fin 2, ∀ hw : opnd C j b < n,
      (⟨opnd C j b, hw⟩ : Fin n) ∈ S := by
    intro j hj b hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, b, rfl⟩
  have hDegree : G.degree z ≤ S.card :=
    degree_le_singleton_support G z S (gateVal n C r) (gate_zero n C hC r (hK r hr))
      (fun x y hxy => cone_agree n C hC K hK hClosed S hBare x y hxy r hr) hEdges
  exact hDegree.trans (input_card_le_gates_add_one n K r hr (opnd C) S hInputs hRead)

end PEqualNP.Outside.L_meta_3566.PrivateCone

namespace PEqualNP.Outside.L_meta_3566.PrivateDelete

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.LeafStep.Pruning

lemma erase_private_cone (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (z : Fin n) (j : ℕ) (hj : j < C.size)
    (hop : (gateAt C j).op = GateOp.and)
    (hz : z.val ∈ (gateAt C j).inputs)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range C.size) (_hjJ : j ∈ J)
    (hclosed : ∀ i < C.size, i ∉ J → ∀ w ∈ (gateAt C i).inputs,
      n ≤ w → w - n ∈ J → w = n + j)
    (ho : C.output < n + C.size)
    (hout : n ≤ C.output → C.output - n ∈ J → C.output = n + j)
    (k : ℕ) (hk : k < C.size) (hkJ : k ∉ J)
    (hreader : n + j ∈ (gateAt C k).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool =>
        circuitFun n C (Function.update y z false)) ∧
      D.size + J.card + 1 ≤ C.size := by
  classical
  let K := Finset.range C.size \ J
  let red : ℕ → Src n ℕ := fun w =>
    if w = z.val ∨ w = n + j then none else srcOf n w
  let P : Prog n ℕ := progOf C fun i b => red (opnd C i b)
  let v : ℕ → (Fin n → Bool) → Bool := fun i y =>
    PEqualNP.EdgeOwnership.gateVal n C i (Function.update y z false)
  have hmem (i : ℕ) (hi : i < C.size) (b : Fin 2) :
      opnd C i b ∈ (gateAt C i).inputs := by
    have hg : gateAt C i ∈ C.gates :=
      PEqualNP.Outside.L_meta_3566.FalseRestrict.list_getD_mem C.gates i _ hi
    have hlen := hC.2.2 _ hg
    obtain ⟨a, d, h⟩ := List.length_eq_two.mp hlen
    fin_cases b <;> simp [opnd, h]
  have hred (w q : ℕ) (hw : w < n + C.size)
      (hcut : n ≤ w → w - n ∈ J → w = n + j)
      (h : red w = some (Sum.inr q)) : q ∈ K := by
    have hcase : ¬ (w = z.val ∨ w = n + j) := by
      intro hc
      simp [red, hc] at h
    have hs : srcOf n w = some (Sum.inr q) := by
      simpa only [red, ite_eq_right hcase] using h
    have hq := srcOf_inr w q hs
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_range.mpr (by omega)
    · intro hqJ
      have hwJ : w - n ∈ J := by simpa [hq] using hqJ
      exact hcase (Or.inr (hcut (by omega) hwJ))
  have hcl : Closed P id K := by
    intro i hi b q h
    obtain ⟨hiRange, hiJ⟩ := Finset.mem_sdiff.mp hi
    have hi' : i < C.size := Finset.mem_range.mp hiRange
    have hb := hC.2.1 i hi' (opnd C i b) (hmem i hi' b)
    change red (opnd C i b) = some (Sum.inr q) at h
    refine ⟨hred _ q (by omega) (hclosed i hi' hiJ _ (hmem i hi' b)) h, ?_⟩
    have hcase : ¬ (opnd C i b = z.val ∨ opnd C i b = n + j) := by
      intro hc
      simp [red, hc] at h
    have hs : srcOf n (opnd C i b) = some (Sum.inr q) := by
      simpa only [red, ite_eq_right hcase] using h
    have hq := srcOf_inr (opnd C i b) q hs
    change q < i
    omega
  have hval (w : ℕ) (y : Fin n → Bool) :
      srcAt y (fun q => v q y) (red w) =
        wireVal n C w (Function.update y z false) := by
    dsimp [red]
    split_ifs with hcase
    · rcases hcase with hcase | hcase
      · subst w
        change false = wireVal n C z.val (Function.update y z false)
        rw [wireVal_lt C z.val z.isLt]
        simp
      · rw [hcase]
        change false = (C.wires (List.ofFn (Function.update y z false))).getD (n + j) false
        exact (PEqualNP.Outside.L_meta_3566.LeafStep.and_input_false
          C j hj hop z hz _ (by simp)).symm
    · unfold srcOf
      split_ifs with hw
      · rw [wireVal_lt C w hw]
        have hne : (⟨w, hw⟩ : Fin n) ≠ z := by
          intro he
          exact hcase (Or.inl (congrArg Fin.val he))
        change y ⟨w, hw⟩ = Function.update y z false ⟨w, hw⟩
        simp [hne]
      · change PEqualNP.EdgeOwnership.gateVal n C (w - n) (Function.update y z false) = _
        have hidx : n + (w - n) = w := by omega
        unfold PEqualNP.EdgeOwnership.gateVal wireVal
        rw [hidx]
  have hsol : Sol P K v := by
    intro y i hi
    have hi' : i < C.size := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
    change PEqualNP.EdgeOwnership.gateVal n C i (Function.update y z false) =
      opv (isA (gateAt C i).op)
        (srcAt y (fun q => v q y) (red (opnd C i 0)))
        (srcAt y (fun q => v q y) (red (opnd C i 1)))
    rw [hval, hval]
    exact gate_eq C hC i hi' (Function.update y z false)
  have hout' : ∀ q, red C.output = some (Sum.inr q) → q ∈ K :=
    fun q h => hred C.output q ho hout h
  obtain ⟨D, hD, hsize, hfun⟩ := fold_total P id v K hcl hsol (red C.output) hout'
  have hkK : k ∈ K := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hk, hkJ⟩
  have hpos : ∃ b : Fin 2, opnd C k b = n + j := by
    have hkmem : gateAt C k ∈ C.gates :=
      PEqualNP.Outside.L_meta_3566.FalseRestrict.list_getD_mem C.gates k _ hk
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hC.2.2 _ hkmem)
    simp only [hab, List.mem_cons, List.not_mem_nil, or_false] at hreader
    rcases hreader with hreader | hreader
    · exact ⟨0, by simp [opnd, hab, ← hreader]⟩
    · exact ⟨1, by simp [opnd, hab, ← hreader]⟩
  have hknot : k ∉ kept P v K := by
    intro hkeep
    have hp := (Finset.mem_filter.mp hkeep).2
    obtain ⟨b, hb⟩ := hpos
    have hsrc : P.src k b = none := by
      change red (opnd C k b) = none
      simp [red, hb]
    have htrue : srcAt (fun _ => true) (fun q => v q (fun _ => true)) (P.src k b) = true := by
      fin_cases b
      · exact hp.1
      · exact hp.2
    rw [hsrc] at htrue
    simp [srcAt] at htrue
  have hkept : (kept P v K).card + 1 ≤ K.card := by
    rw [← Finset.card_insert_of_notMem hknot]
    exact Finset.card_le_card (Finset.insert_subset hkK (Finset.filter_subset _ _))
  have hcard : K.card + J.card = C.size := by
    simpa [K] using Finset.card_sdiff_add_card_eq_card hJ
  refine ⟨D, hD, ?_, by omega⟩
  funext y
  rw [hfun y, hval]
  rfl

end PEqualNP.Outside.L_meta_3566.PrivateDelete

namespace PEqualNP.Outside.L_meta_3566.PrivateStep

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.AO2Upper PEqualNP.Outside.L_meta_3566.LeafStep

lemma private_and_restriction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (z : Fin n)
    (hnon : (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty)
    (j : ℕ) (hj : j < C.size) (hop : (gateAt C j).op = GateOp.and)
    (hz : z.val ∈ (gateAt C j).inputs)
    (K : Finset ℕ) (hK : K ⊆ Finset.range j) (r : ℕ) (hr : r ∈ K)
    (_hroot : n + r ∈ (gateAt C j).inputs)
    (hClosed : ∀ i ∈ K, ∀ b : Fin 2, n ≤ opnd C i b → opnd C i b - n ∈ K)
    (hRead : ∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, opnd C h b = n + g)
    (hEdges : ∀ w : Fin n, G.Adj z w → PEqualNP.EdgeOwnership.gateVal n C r
      (PEqualNP.EdgeOwnership.pairInput w w) = true)
    (hPrivate : ∀ i < C.size, i ∉ insert j K → ∀ w ∈ (gateAt C i).inputs,
      n ≤ w → w - n ∈ insert j K → w = n + j) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      D.size + G.degree z + 1 ≤ C.size := by
  classical
  obtain ⟨e, he⟩ := hnon
  have hadj : ∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b := by
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    exact ⟨a, b, by simpa using he⟩
  obtain ⟨a, b, hab⟩ := hadj
  obtain ⟨hab, haz, hbz⟩ := (cut_adj G z a b).mp hab
  let x : Fin n → Bool := Function.update (fun _ => true) z false
  have hx : x z = false := by simp [x]
  have hxa : x a = true := by simp [x, haz]
  have hxb : x b = true := by simp [x, hbz]
  have htrue : circuitFun n C x = true := by
    rw [hC.2.1]
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    exact ⟨a, b, hab, hxa, hxb⟩
  have hfalse := and_input_false C j hj hop z hz x hx
  have hjo : C.output ≠ n + j := by
    intro h
    change (C.wires (List.ofFn x)).getD C.output false = true at htrue
    rw [h, hfalse] at htrue
    exact Bool.false_ne_true htrue
  have ho : C.output < n + C.size := by
    by_contra h
    have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
      exact (length_wiresFrom C.gates (List.ofFn x)).trans (by simp [Circuit.size])
    change (C.wires (List.ofFn x)).getD C.output false = true at htrue
    rw [List.getD_eq_default _ _ (by omega)] at htrue
    exact Bool.false_ne_true htrue
  have hLast : C.output = n + (C.size - 1) := by
    by_contra h
    obtain ⟨k, hlk, hk, _⟩ := reader_of_least G C hC (C.size - 1) (by omega) ho h
    omega
  have hKlt : ∀ i ∈ K, i < j := fun i hi => Finset.mem_range.mp (hK hi)
  have hjK : j ∉ K := by intro h; have := hKlt j h; omega
  have hJ : insert j K ⊆ Finset.range C.size := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_range.mpr hj
    · exact Finset.mem_range.mpr (lt_trans (hKlt i hi) hj)
  have hout : n ≤ C.output → C.output - n ∈ insert j K → C.output = n + j := by
    intro hn hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · omega
    · have hlt := hKlt (C.output - n) hi
      omega
  obtain ⟨k, hjk, hk, hreader⟩ := reader_of_least G C hC j hj ho hjo
  have hkJ : k ∉ insert j K := by
    intro hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · omega
    · have hlt := hKlt k hi
      omega
  obtain ⟨D, hD, hFun, hSize⟩ := PrivateDelete.erase_private_cone n C hC.1 z j hj hop hz
    (insert j K) hJ (Finset.mem_insert_self _ _) hPrivate ho hout k hk hkJ hreader
  have hDegree := PrivateCone.degree_le_closed_cone G z C hC.1 K r hr
    (fun i hi => lt_trans (hKlt i hi) hj) hClosed hRead hEdges
  have hCard : (insert j K).card = K.card + 1 := Finset.card_insert_of_notMem hjK
  exact ⟨D, hD, hFun, by omega⟩

lemma witness_of_private_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (z : Fin n) (hpos : 0 < G.degree z)
    (hnon : (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty)
    (j : ℕ) (hj : j < C.size) (hop : (gateAt C j).op = GateOp.and)
    (hz : z.val ∈ (gateAt C j).inputs)
    (K : Finset ℕ) (hK : K ⊆ Finset.range j) (r : ℕ) (hr : r ∈ K)
    (hroot : n + r ∈ (gateAt C j).inputs)
    (hClosed : ∀ i ∈ K, ∀ b : Fin 2, n ≤ opnd C i b → opnd C i b - n ∈ K)
    (hRead : ∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, opnd C h b = n + g)
    (hEdges : ∀ w : Fin n, G.Adj z w → PEqualNP.EdgeOwnership.gateVal n C r
      (PEqualNP.EdgeOwnership.pairInput w w) = true)
    (hPrivate : ∀ i < C.size, i ∉ insert j K → ∀ w ∈ (gateAt C i).inputs,
      n ≤ w → w - n ∈ insert j K → w = n + j) :
    0 < G.degree z ∧ ∀ C' : Circuit, IsAO2 n C' → circuitFun n C' = graphFun G ∅ →
      ∃ D : Circuit, IsAO2 n D ∧
        circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
          (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true)
            (Classical.propDecidable _)) ∧
        D.size + G.degree z ≤ C'.size ∧
        ((∃ S : Finset (Fin n), CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
          ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
          D.size + G.degree z + 1 ≤ C'.size) := by
  obtain ⟨D, hD, hFun, hSize⟩ := private_and_restriction G C hC z hnon j hj hop hz
    K hK r hr hroot hClosed hRead hEdges hPrivate
  have hGraph : circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
      (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true)
        (Classical.propDecidable _)) := by
    rw [hFun, hC.2.1, FanoutStep.graphFun_update_false]
  refine ⟨hpos, ?_⟩
  intro C' hC' hFun'
  have hMin := hC.2.2 C' hC' hFun'
  exact ⟨D, hD, hGraph, by omega, fun _ => by omega⟩

end PEqualNP.Outside.L_meta_3566.PrivateStep


namespace PEqualNP.Outside.L_meta_3566.SharedRewrite

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  exact AO2Upper.length_wiresFrom gs w

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  exact AO2Upper.getD_wiresFrom gs w i hi

lemma stepWire_getD_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (stepWire w g).getD i false = w.getD i false := by
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma stepWire_getD_len (w : List Bool) (g : Gate) :
    (stepWire w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs.take j = pre ∧ gs.drop (j + 1) = post ∧
        gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl, rfl, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

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

def replace (C : Circuit) (j : ℕ) (g : Gate) : Circuit :=
  ⟨C.gates.set j g, C.output⟩

lemma replace_size (C : Circuit) (j : ℕ) (g : Gate) : (replace C j g).size = C.size := by
  simp [replace, Circuit.size]

lemma replace_gateAt (C : Circuit) (j : ℕ) (g : Gate) (hj : j < C.gates.length) (k : ℕ) :
    gateAt (replace C j g) k = if j = k then g else gateAt C k := by
  simp only [gateAt, replace, List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs with he
  · simp
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

lemma circuitFun_monotone (n : ℕ) (C : Circuit) (hao : AndOrOnly C) :
    Monotone (circuitFun n C) := by
  intro x y hxy
  apply foldl_rel (R := fun a b => a ≤ b) (fun _ => le_refl _) C.gates
    (fun g hg => ao_eval_mono g (hao g hg)) (List.ofFn x) (List.ofFn y) (by simp)
  intro u
  by_cases hu : u < n
  · rw [List.getD_eq_getElem _ _ (by simpa), List.getD_eq_getElem _ _ (by simpa)]
    simpa using hxy ⟨u, hu⟩
  · rw [getD_ge_length _ _ (by simpa using Nat.le_of_not_gt hu),
      getD_ge_length _ _ (by simpa using Nat.le_of_not_gt hu)]

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
  apply EdgeProfile.eq_of_edges_and_below G _
  · intro x y hxy hx
    exact Bool.le_iff_imp.mp
      (circuitFun_monotone n _ hd.1 (fun i => Bool.le_iff_imp.mpr (hxy i))) hx
  · intro x hx
    by_contra hG
    have hfalse : g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn x)).getD i false) = false := by
      apply Bool.eq_false_iff.mpr
      exact fun ht => hG (hclean x ht)
    have hle := replace_ge n C j hj g hgback hAO.1 x
      (by rw [hfalse]; exact Bool.false_le _)
    have ht := Bool.le_iff_imp.mp hle hx
    rw [hfun] at ht
    exact hG ht
  · intro u v huv
    apply Bool.le_iff_imp.mp (replace_le n C j hj g hgback hAO.1 _
      (Bool.le_iff_imp.mpr (hpos u v huv)))
    rw [hfun]
    have hp : ∃ a b, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true :=
      ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    simpa [graphFun] using hp

lemma input_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    (C.wires (List.ofFn x)).getD u.val false = x u := by
  rw [wires_eq_foldl, foldl_stepWire_getD_lt _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_3566.SharedRewrite


namespace PEqualNP.Outside.L_meta_3566.SharedExit

open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma monochrome_edge_witness {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Bool)
    (hBip : ∀ a b : Fin n, G.Adj a b → color a ≠ color b)
    (q : (Fin n → Bool) → Bool) (z w : Fin n)
    (hSame : color w = color z)
    (hPure : ∀ a b : Fin n, color a = color z → color b ≠ color z →
      q (pairInput a b) = q (pairInput b b))
    (a b : Fin n) (hab : G.Adj a b)
    (hgate : (pairInput a b w && q (pairInput a b)) = true) :
    ∃ u : Fin n, G.Adj w u ∧ q (pairInput u u) = true ∧
      pairInput a b u = true := by
  obtain ⟨hw, hq⟩ : pairInput a b w = true ∧ q (pairInput a b) = true := by
    simpa using hgate
  have hwmem : w = a ∨ w = b := by simpa [pairInput] using hw
  rcases hwmem with hwa | hwb
  · subst a
    have hOpp : color b ≠ color z := by
      intro hb
      exact hBip w b hab (hSame.trans hb.symm)
    refine ⟨b, hab, ?_, by simp [pairInput]⟩
    rw [← hPure w b hSame hOpp]
    exact hq
  · subst b
    have hOpp : color a ≠ color z := by
      intro ha
      exact hBip a w hab (ha.trans hSame.symm)
    have hswap : pairInput a w = pairInput w a := by
      funext i
      simp [pairInput, or_comm]
    refine ⟨a, hab.symm, ?_, by simp [pairInput]⟩
    rw [← hPure w a hSame hOpp, ← hswap]
    exact hq

lemma monochrome_and_narrow {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool)
    (hBip : ∀ a b : Fin n, G.Adj a b → color a ≠ color b)
    (q : (Fin n → Bool) → Bool)
    (hMono : ∀ y y' : Fin n → Bool, (∀ i, y i = true → y' i = true) →
      q y = true → q y' = true)
    (z w : Fin n) (hwz : w ≠ z) (hSame : color w = color z)
    (hFour : NoFourCycle G)
    (hSupport : ∀ u : Fin n, q (pairInput u u) = true → G.Adj z u)
    (hPure : ∀ a b : Fin n, color a = color z → color b ≠ color z →
      q (pairInput a b) = q (pairInput b b)) :
    (∀ a b : Fin n, G.Adj a b →
      (pairInput a b w && q (pairInput a b)) = false) ∨
    ∃ u : Fin n, G.Adj w u ∧ q (pairInput u u) = true ∧
      (∀ y : Fin n → Bool, (y w && y u) = true → (y w && q y) = true) ∧
      (∀ a b : Fin n, G.Adj a b →
        (pairInput a b w && q (pairInput a b)) = true →
        (pairInput a b w && pairInput a b u) = true) := by
  classical
  have unique (u v : Fin n) (hwu : G.Adj w u) (hqu : q (pairInput u u) = true)
      (hwv : G.Adj w v) (hqv : q (pairInput v v) = true) : u = v := by
    have hcard := hFour z w hwz.symm
    have hu : u ∈ Finset.univ.filter (fun t : Fin n => G.Adj z t ∧ G.Adj w t) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSupport u hqu, hwu⟩
    have hv : v ∈ Finset.univ.filter (fun t : Fin n => G.Adj z t ∧ G.Adj w t) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSupport v hqv, hwv⟩
    exact Finset.card_le_one.mp hcard u hu v hv
  by_cases hex : ∃ u : Fin n, G.Adj w u ∧ q (pairInput u u) = true
  · obtain ⟨u, hwu, hqu⟩ := hex
    refine Or.inr ⟨u, hwu, hqu, ?_, ?_⟩
    · intro y hy
      obtain ⟨hyw, hyu⟩ : y w = true ∧ y u = true := by simpa using hy
      have hqy : q y = true := hMono (pairInput u u) y (by
        intro i hi
        have hiu : i = u := by simpa [pairInput] using hi
        simpa [hiu] using hyu) hqu
      simp [hyw, hqy]
    · intro a b hab hold
      obtain ⟨v, hwv, hqv, hpv⟩ :=
        monochrome_edge_witness G color hBip q z w hSame hPure a b hab hold
      have hvu := unique v u hwv hqv hwu hqu
      have hpu : pairInput a b u = true := by simpa only [hvu] using hpv
      have hold' : pairInput a b w = true ∧ q (pairInput a b) = true := by
        simpa using hold
      simp [hold'.1, hpu]
  · refine Or.inl ?_
    intro a b hab
    cases he : (pairInput a b w && q (pairInput a b)) with
    | false => rfl
    | true =>
      obtain ⟨u, hwu, hqu, _⟩ :=
        monochrome_edge_witness G color hBip q z w hSame hPure a b hab he
      exact (hex ⟨u, hwu, hqu⟩).elim

end PEqualNP.Outside.L_meta_3566.SharedExit


namespace PEqualNP.Outside.L_meta_3566.SharedExit

open PEqualNP.EdgeOwnership

lemma opposite_color_edge_value {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Bool)
    (hBip : ∀ a b : Fin n, G.Adj a b → color a ≠ color b)
    (q : (Fin n → Bool) → Bool) (z w : Fin n)
    (hOpp : color w ≠ color z)
    (hPure : ∀ a b : Fin n, color a = color z → color b ≠ color z →
      q (pairInput a b) = q (pairInput b b))
    (a b : Fin n) (hab : G.Adj a b) (hw : pairInput a b w = true) :
    q (pairInput a b) = q (pairInput w w) := by
  have hwmem : w = a ∨ w = b := by simpa [pairInput] using hw
  rcases hwmem with hwa | hwb
  · subst a
    have hSame : color b = color z := by
      have hne := hBip w b hab
      cases hcw : color w <;> cases hcb : color b <;> cases hcz : color z <;> simp_all
    have hswap : pairInput w b = pairInput b w := by
      funext i
      simp [pairInput, or_comm]
    rw [hswap]
    exact hPure b w hSame hOpp
  · subst b
    have hSame : color a = color z := by
      have hne := hBip a w hab
      cases hcw : color w <;> cases hca : color a <;> cases hcz : color z <;> simp_all
    exact hPure a w hSame hOpp

lemma opposite_color_and_absorb {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Bool)
    (hBip : ∀ a b : Fin n, G.Adj a b → color a ≠ color b)
    (q : (Fin n → Bool) → Bool)
    (hMono : ∀ y y' : Fin n → Bool, (∀ i, y i = true → y' i = true) →
      q y = true → q y' = true)
    (z w : Fin n) (hOpp : color w ≠ color z)
    (hPure : ∀ a b : Fin n, color a = color z → color b ≠ color z →
      q (pairInput a b) = q (pairInput b b)) :
    (q (pairInput w w) = true ∧
      ∀ y : Fin n → Bool, (y w && q y) = y w) ∨
    (q (pairInput w w) = false ∧
      ∀ a b : Fin n, G.Adj a b →
        (pairInput a b w && q (pairInput a b)) = false) := by
  cases hq : q (pairInput w w) with
  | false =>
    refine Or.inr ⟨rfl, ?_⟩
    intro a b hab
    cases hw : pairInput a b w with
    | false => simp
    | true =>
      have he := opposite_color_edge_value G color hBip q z w hOpp hPure a b hab hw
      simp [he, hq]
  | true =>
    refine Or.inl ⟨rfl, ?_⟩
    intro y
    cases hy : y w with
    | false => simp
    | true =>
      have hqy : q y = true := hMono (pairInput w w) y (by
        intro i hi
        have hiw : i = w := by simpa [pairInput] using hi
        simpa [hiw] using hy) hq
      simp [hqy]

end PEqualNP.Outside.L_meta_3566.SharedExit


namespace PEqualNP.Outside.L_meta_3566.SharedExit

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma support_of_clean_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q : (Fin n → Bool) → Bool)
    (hMono : ∀ y y' : Fin n → Bool, (∀ i, y i = true → y' i = true) →
      q y = true → q y' = true)
    (z : Fin n)
    (hBelow : ∀ y : Fin n → Bool, (y z && q y) = true → graphFun G ∅ y = true) :
    ∀ u : Fin n, q (pairInput u u) = true → G.Adj z u := by
  intro u hqu
  have hqzu : q (pairInput z u) = true := hMono (pairInput u u) (pairInput z u) (by
    intro i hi
    have hiu : i = u := by simpa [pairInput] using hi
    simp [pairInput, hiu]) hqu
  have hF := hBelow (pairInput z u) (by simp [pairInput, hqzu])
  have hE : ∃ a b : Fin n, G.Adj a b ∧ (a = z ∨ a = u) ∧ (b = z ∨ b = u) := by
    simpa [graphFun, pairInput] using hF
  obtain ⟨a, b, hab, ha, hb⟩ := hE
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab.ne rfl).elim
  · exact hab
  · exact hab.symm
  · exact (hab.ne rfl).elim

end PEqualNP.Outside.L_meta_3566.SharedExit


namespace PEqualNP.Outside.L_meta_3566.JunkMinimum

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def IsJunkLeastAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  IsLeastAO G C ∧ ∀ D : Circuit, IsLeastAO G D →
    (junk G C).card ≤ (junk G D).card

lemma exists_junk_least_ao {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C0 : Circuit) (hC0 : IsLeastAO G C0) :
    ∃ C : Circuit, IsJunkLeastAO G C := by
  classical
  have hex : ∃ k : ℕ, ∃ C : Circuit,
      IsLeastAO G C ∧ (junk G C).card = k :=
    ⟨(junk G C0).card, C0, hC0, rfl⟩
  obtain ⟨C, hC, hcount⟩ := Nat.find_spec hex
  refine ⟨C, hC, ?_⟩
  intro D hD
  rw [hcount]
  exact Nat.find_min' hex ⟨D, hD, rfl⟩

end PEqualNP.Outside.L_meta_3566.JunkMinimum

namespace PEqualNP.Outside.L_meta_3566.SharedExit

open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma monochrome_and_unique_edge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hBip : ∀ a b : Fin n, G.Adj a b → color a ≠ color b)
    (q : (Fin n → Bool) → Bool) (z w : Fin n)
    (hwz : w ≠ z) (hSame : color w = color z) (hFour : NoFourCycle G)
    (hSupport : ∀ u : Fin n, q (pairInput u u) = true → G.Adj z u)
    (hPure : ∀ a b : Fin n, color a = color z → color b ≠ color z →
      q (pairInput a b) = q (pairInput b b))
    (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d)
    (habOn : (pairInput a b w && q (pairInput a b)) = true)
    (hcdOn : (pairInput c d w && q (pairInput c d)) = true) :
    s(a, b) = s(c, d) := by
  classical
  obtain ⟨u, hwu, hqu, hu⟩ :=
    monochrome_edge_witness G color hBip q z w hSame hPure a b hab habOn
  obtain ⟨v, hwv, hqv, hv⟩ :=
    monochrome_edge_witness G color hBip q z w hSame hPure c d hcd hcdOn
  have huv : u = v := by
    apply Finset.card_le_one.mp (hFour z w hwz.symm) u _ v _
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSupport u hqu, hwu⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSupport v hqv, hwv⟩
  have hwab : pairInput a b w = true := (Bool.and_eq_true_iff.mp habOn).1
  have hwcd : pairInput c d w = true := (Bool.and_eq_true_iff.mp hcdOn).1
  apply Sym2.eq_of_ne_mem hwu.ne
  · simpa [pairInput] using hwab
  · simpa [pairInput] using hu
  · simpa [pairInput] using hwcd
  · simpa [pairInput, huv] using hv

end PEqualNP.Outside.L_meta_3566.SharedExit

namespace PEqualNP.Outside.L_meta_3566.SharedExitWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma replace_with_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (hFun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (w u : Fin n) (hwu : G.Adj w u)
    (q : (Fin n → Bool) → Bool)
    (hVal : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + j) false = (x w && q x))
    (hKeep : ∀ a b : Fin n, G.Adj a b →
      (pairInput a b w && q (pairInput a b)) = true →
      (pairInput a b w && pairInput a b u) = true) :
    IsAO2 n (SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩) ∧
      circuitFun n (SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩) = graphFun G ∅ ∧
      (SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩).size = C.size := by
  have hEval : ∀ x : Fin n → Bool,
      GateOp.and.eval ([w.val, u.val].map fun i =>
        (C.wires (List.ofFn x)).getD i false) = (x w && x u) := by
    intro x
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    rw [SharedRewrite.input_val, SharedRewrite.input_val]
  apply SharedRewrite.correct_of_edge_cover G C hC hFun j hj
    ⟨GateOp.and, [w.val, u.val]⟩ (Or.inl rfl) rfl
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl <;> omega
  · intro a b hab hv
    rw [hVal] at hv
    rw [hEval]
    exact hKeep a b hab hv
  · intro x hx
    rw [hEval] at hx
    have hx' : x w = true ∧ x u = true := by simpa using hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨w, u, hwu, hx'.1, hx'.2⟩


lemma replace_with_edge_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (w u : Fin n) (hwu : G.Adj w u)
    (q : (Fin n → Bool) → Bool)
    (hVal : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + j) false = (x w && q x))
    (hKeep : ∀ a b : Fin n, G.Adj a b →
      (pairInput a b w && q (pairInput a b)) = true →
      (pairInput a b w && pairInput a b u) = true) :
    IsLeastAO G (SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩) := by
  obtain ⟨hAO, hFun, hSize⟩ := replace_with_edge G C hC.1 hC.2.1 j hj w u hwu q hVal hKeep
  exact ⟨hAO, hFun, fun D hD hFunD => hSize.trans_le (hC.2.2 D hD hFunD)⟩

end PEqualNP.Outside.L_meta_3566.SharedExitWire

namespace PEqualNP.Outside.L_meta_3566.SharedExitWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma detach_monochrome_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool)
    (hBip : ∀ a b : Fin n, G.Adj a b → color a ≠ color b)
    (hFour : NoFourCycle G)
    (C : Circuit) (hC : IsLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length)
    (q : (Fin n → Bool) → Bool)
    (hMono : ∀ y y' : Fin n → Bool, (∀ i, y i = true → y' i = true) →
      q y = true → q y' = true)
    (z w : Fin n) (hwz : w ≠ z) (hSame : color w = color z)
    (hSupport : ∀ u : Fin n, q (pairInput u u) = true → G.Adj z u)
    (hPure : ∀ a b : Fin n, color a = color z → color b ≠ color z →
      q (pairInput a b) = q (pairInput b b))
    (hVal : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + j) false = (x w && q x))
    (hAccept : ∃ a b : Fin n, G.Adj a b ∧
      (C.wires (List.ofFn (pairInput a b))).getD (n + j) false = true) :
    ∃ u : Fin n, G.Adj w u ∧ q (pairInput u u) = true ∧
      (∀ x : Fin n → Bool, (x w && x u) = true → (x w && q x) = true) ∧
      IsLeastAO G (SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩) ∧
      (SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩).size = C.size := by
  rcases SharedExit.monochrome_and_narrow G color hBip q hMono z w hwz hSame
      hFour hSupport hPure with hZero | ⟨u, hwu, hqu, hDown, hKeep⟩
  · obtain ⟨a, b, hab, hv⟩ := hAccept
    rw [hVal, hZero a b hab] at hv
    exact False.elim (Bool.false_ne_true hv)
  · exact ⟨u, hwu, hqu, hDown,
      replace_with_edge_least G C hC j hj w u hwu q hVal hKeep,
      SharedRewrite.replace_size C j _⟩

end PEqualNP.Outside.L_meta_3566.SharedExitWire

namespace PEqualNP.Outside.L_meta_3566.JunkNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma mem_junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k : ℕ) :
    k ∈ junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C k x = true ∧ graphFun G ∅ x = false := by
  change k ∈ (Finset.range C.gates.length).filter (fun i => IsDirtyAnd n G C i) ↔ _
  rw [Finset.mem_filter, Finset.mem_range]
  simp only [IsDirtyAnd, IsDirty]
  constructor
  · rintro ⟨hk, hop, _, h⟩
    exact ⟨hk, hop, h⟩
  · rintro ⟨hk, hop, h⟩
    exact ⟨hk, hop, hk, h⟩

lemma gateVal_le_of_replace (n : ℕ) (C : Circuit) (hAO : AndOrOnly C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hDown : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) ≤
        (C.wires (List.ofFn x)).getD (n + j) false)
    (k : ℕ) (x : Fin n → Bool) :
    gateVal n (SharedRewrite.replace C j g) k x ≤ gateVal n C k x := by
  exact SharedRewrite.replace_ge n ⟨C.gates, n + k⟩ j hj g hgback hAO x (hDown x)

lemma junk_subset_of_replace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : AndOrOnly C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hop : g.op = (gateAt C j).op)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hDown : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) ≤
        (C.wires (List.ofFn x)).getD (n + j) false) :
    junk G (SharedRewrite.replace C j g) ⊆ junk G C := by
  intro k hk
  obtain ⟨hk, hkop, x, hv, hFalse⟩ := (mem_junk_iff G _ k).mp hk
  have hk' : k < C.gates.length := by simpa [SharedRewrite.replace] using hk
  have hsame : (gateAt (SharedRewrite.replace C j g) k).op = (gateAt C k).op := by
    rw [SharedRewrite.replace_gateAt C j g hj k]
    split_ifs with h
    · subst k
      exact hop
    · rfl
  have hv' := Bool.le_iff_imp.mp (gateVal_le_of_replace n C hAO j hj g hgback hDown k x) hv
  exact (mem_junk_iff G C k).mpr ⟨hk', hsame ▸ hkop, x, hv', hFalse⟩

lemma junk_card_lt_of_replace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : AndOrOnly C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hop : g.op = (gateAt C j).op)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hDown : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) ≤
        (C.wires (List.ofFn x)).getD (n + j) false)
    (hDirty : j ∈ junk G C)
    (hClean : BelowF G (SharedRewrite.replace C j g) j) :
    (junk G (SharedRewrite.replace C j g)).card < (junk G C).card := by
  classical
  have hsub := junk_subset_of_replace G C hAO j hj g hop hgback hDown
  have hjnot : j ∉ junk G (SharedRewrite.replace C j g) := by
    intro hjmem
    obtain ⟨_, _, x, hv, hf⟩ := (mem_junk_iff G _ j).mp hjmem
    have ht := hClean x hv
    rw [hf] at ht
    exact Bool.false_ne_true ht
  have hstrict : junk G (SharedRewrite.replace C j g) ⊂ junk G C := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    rw [heq] at hjnot
    exact hjnot hDirty
  exact Finset.card_lt_card hstrict

lemma edge_gate_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (w u : Fin n) (hwu : G.Adj w u) :
    BelowF G (SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩) j := by
  let D := SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩
  have hD : IsAO2 n D := SharedRewrite.replace_ao C hC j hj _ (Or.inl rfl) rfl (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl <;> omega)
  have hjD : j < D.gates.length := by simpa [D, SharedRewrite.replace] using hj
  have hgate : gateAt D j = ⟨GateOp.and, [w.val, u.val]⟩ := by
    simp [D, SharedRewrite.replace_gateAt C j _ hj j]
  intro x hx
  have heq := LeafStep.Pruning.gate_eq D hD j hjD x
  simp only [hgate, LeafStep.Pruning.isA, LeafStep.Pruning.opv, opnd] at heq
  have hVal : gateVal n D j x = (x w && x u) := by
    change gateVal n D j x = ((D.wires (List.ofFn x)).getD w.val false &&
      (D.wires (List.ofFn x)).getD u.val false) at heq
    rw [SharedRewrite.input_val, SharedRewrite.input_val] at heq
    exact heq
  rw [hVal] at hx
  have hx' : x w = true ∧ x u = true := by simpa using hx
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  exact ⟨w, u, hwu, hx'.1, hx'.2⟩

end PEqualNP.Outside.L_meta_3566.JunkNormalize

namespace PEqualNP.Outside.L_meta_3566.JunkNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma monochrome_reader_not_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool)
    (hBip : ∀ a b : Fin n, G.Adj a b → color a ≠ color b)
    (hFour : NoFourCycle G)
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length)
    (q : (Fin n → Bool) → Bool)
    (hMono : ∀ y y' : Fin n → Bool, (∀ i, y i = true → y' i = true) →
      q y = true → q y' = true)
    (z w : Fin n) (hwz : w ≠ z) (hSame : color w = color z)
    (hSupport : ∀ u : Fin n, q (pairInput u u) = true → G.Adj z u)
    (hPure : ∀ a b : Fin n, color a = color z → color b ≠ color z →
      q (pairInput a b) = q (pairInput b b))
    (hVal : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + j) false = (x w && q x))
    (hAccept : ∃ a b : Fin n, G.Adj a b ∧
      (C.wires (List.ofFn (pairInput a b))).getD (n + j) false = true) :
    j ∉ junk G C := by
  obtain ⟨u, hwu, _, hDown, hLeast, _⟩ :=
    SharedExitWire.detach_monochrome_and G color hBip hFour C hC.1 j hj q hMono
      z w hwz hSame hSupport hPure hVal hAccept
  intro hDirty
  have hOldOp := ((mem_junk_iff G C j).mp hDirty).2.1
  have hEval : ∀ x : Fin n → Bool,
      GateOp.and.eval ([w.val, u.val].map fun i =>
        (C.wires (List.ofFn x)).getD i false) = (x w && x u) := by
    intro x
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    rw [SharedRewrite.input_val, SharedRewrite.input_val]
  have hDown' : ∀ x : Fin n → Bool,
      GateOp.and.eval ([w.val, u.val].map fun i =>
        (C.wires (List.ofFn x)).getD i false) ≤
          (C.wires (List.ofFn x)).getD (n + j) false := by
    intro x
    rw [hEval, hVal]
    exact Bool.le_iff_imp.mpr (hDown x)
  have hStrict := junk_card_lt_of_replace G C hC.1.1.1 j hj
    ⟨GateOp.and, [w.val, u.val]⟩ hOldOp.symm (by
      intro t ht
      simp at ht
      rcases ht with rfl | rfl <;> omega) hDown' hDirty
    (edge_gate_below G C hC.1.1 j hj w u hwu)
  have hMin := hC.2 _ hLeast
  omega

end PEqualNP.Outside.L_meta_3566.JunkNormalize

namespace PEqualNP.Outside.L_meta_3566.JunkNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma junk_subset_of_clean_replace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : AndOrOnly C) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hop : g.op = (gateAt C j).op) (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hClean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
        graphFun G ∅ x = true) :
    junk G (SharedRewrite.replace C j g) ⊆ junk G C := by
  intro k hk
  obtain ⟨hk, hkop, x, hv, hFalse⟩ := (mem_junk_iff G _ k).mp hk
  have hk' : k < C.gates.length := by simpa [SharedRewrite.replace] using hk
  have hsame : (gateAt (SharedRewrite.replace C j g) k).op = (gateAt C k).op := by
    rw [SharedRewrite.replace_gateAt C j g hj k]
    split_ifs with h
    · subst k
      exact hop
    · rfl
  have hzero : g.op.eval (g.inputs.map fun i =>
      (C.wires (List.ofFn x)).getD i false) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hF := hClean x ht
    rw [hFalse] at hF
    exact Bool.false_ne_true hF
  have hle : gateVal n (SharedRewrite.replace C j g) k x ≤ gateVal n C k x :=
    SharedRewrite.replace_ge n ⟨C.gates, n + k⟩ j hj g hgback hAO x
      (by change g.op.eval (g.inputs.map fun i =>
            (C.wires (List.ofFn x)).getD i false) ≤ _
          rw [hzero]
          exact Bool.false_le _)
  exact (mem_junk_iff G C k).mpr
    ⟨hk', hsame ▸ hkop, x, Bool.le_iff_imp.mp hle hv, hFalse⟩

lemma junk_card_lt_of_clean_replace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : AndOrOnly C) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hop : g.op = (gateAt C j).op) (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hClean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
        graphFun G ∅ x = true)
    (hDirty : j ∈ junk G C)
    (hNewClean : BelowF G (SharedRewrite.replace C j g) j) :
    (junk G (SharedRewrite.replace C j g)).card < (junk G C).card := by
  have hsub := junk_subset_of_clean_replace G C hAO j hj g hop hgback hClean
  have hjnot : j ∉ junk G (SharedRewrite.replace C j g) := by
    intro hjmem
    obtain ⟨_, _, x, hv, hf⟩ := (mem_junk_iff G _ j).mp hjmem
    have ht := hNewClean x hv
    rw [hf] at ht
    exact Bool.false_ne_true ht
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  rw [heq] at hjnot
  exact hjnot hDirty

lemma one_edge_profile_not_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (w u : Fin n) (hwu : G.Adj w u)
    (hKeep : ∀ a b : Fin n, G.Adj a b → gateVal n C j (pairInput a b) = true →
      (pairInput a b w && pairInput a b u) = true) :
    j ∉ junk G C := by
  intro hDirty
  have hOldOp := ((mem_junk_iff G C j).mp hDirty).2.1
  have hBack : ∀ i ∈ [w.val, u.val], i < n + j := by
    intro i hi
    simp at hi
    rcases hi with rfl | rfl <;> omega
  have hEval : ∀ x : Fin n → Bool,
      GateOp.and.eval ([w.val, u.val].map fun i =>
        (C.wires (List.ofFn x)).getD i false) = (x w && x u) := by
    intro x
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    rw [SharedRewrite.input_val, SharedRewrite.input_val]
  have hClean : ∀ x : Fin n → Bool,
      GateOp.and.eval ([w.val, u.val].map fun i =>
        (C.wires (List.ofFn x)).getD i false) = true → graphFun G ∅ x = true := by
    intro x hx
    rw [hEval] at hx
    have hx' : x w = true ∧ x u = true := by simpa using hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨w, u, hwu, hx'.1, hx'.2⟩
  obtain ⟨hD, hFun, hSize⟩ := SharedRewrite.correct_of_edge_cover G C hC.1.1 hC.1.2.1
    j hj ⟨GateOp.and, [w.val, u.val]⟩ (Or.inl rfl) rfl hBack
    (by intro a b hab hv; rw [hEval]; exact hKeep a b hab hv) hClean
  have hLeast : IsLeastAO G (SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩) :=
    ⟨hD, hFun, fun D hD hFunD => hSize.trans_le (hC.1.2.2 D hD hFunD)⟩
  have hStrict := junk_card_lt_of_clean_replace G C hC.1.1.1 j hj
    ⟨GateOp.and, [w.val, u.val]⟩ hOldOp.symm hBack hClean hDirty
    (edge_gate_below G C hC.1.1 j hj w u hwu)
  have hMin := hC.2 _ hLeast
  omega

lemma dirty_accepts_two_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : ∃ w u : Fin n, G.Adj w u)
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (hDirty : j ∈ junk G C) :
    ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧
      gateVal n C j (pairInput a b) = true ∧
      gateVal n C j (pairInput c d) = true ∧ s(a, b) ≠ s(c, d) := by
  classical
  have hj := ((mem_junk_iff G C j).mp hDirty).1
  by_contra hTwo
  by_cases hAccept : ∃ w u : Fin n, G.Adj w u ∧ gateVal n C j (pairInput w u) = true
  · obtain ⟨w, u, hwu, hOn⟩ := hAccept
    apply one_edge_profile_not_dirty G C hC j hj w u hwu ?_ hDirty
    intro a b hab hv
    have heq : s(a, b) = s(w, u) := by
      by_contra hne
      exact hTwo ⟨w, u, a, b, hwu, hab, hOn, hv, fun he => hne he.symm⟩
    have hw : w ∈ s(a, b) := by rw [heq]; simp
    have hu : u ∈ s(a, b) := by rw [heq]; simp
    have hw' : pairInput a b w = true := by simpa [pairInput] using hw
    have hu' : pairInput a b u = true := by simpa [pairInput] using hu
    simp [hw', hu']
  · obtain ⟨w, u, hwu⟩ := hE
    apply one_edge_profile_not_dirty G C hC j hj w u hwu ?_ hDirty
    intro a b hab hv
    exact False.elim (hAccept ⟨a, b, hab, hv⟩)

lemma monochrome_reader_not_dirty_general {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : ∃ a b : Fin n, G.Adj a b) (color : Fin n → Bool)
    (hBip : ∀ a b : Fin n, G.Adj a b → color a ≠ color b) (hFour : NoFourCycle G)
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (q : (Fin n → Bool) → Bool) (z w : Fin n)
    (hwz : w ≠ z) (hSame : color w = color z)
    (hSupport : ∀ u : Fin n, q (pairInput u u) = true → G.Adj z u)
    (hPure : ∀ a b : Fin n, color a = color z → color b ≠ color z →
      q (pairInput a b) = q (pairInput b b))
    (hVal : ∀ x : Fin n → Bool, gateVal n C j x = (x w && q x)) :
    j ∉ junk G C := by
  intro hDirty
  obtain ⟨a, b, c, d, hab, hcd, habOn, hcdOn, hne⟩ :=
    dirty_accepts_two_edges G hE C hC j hDirty
  rw [hVal] at habOn hcdOn
  exact hne (SharedExit.monochrome_and_unique_edge G color hBip q z w hwz hSame hFour
    hSupport hPure a b c d hab hcd habOn hcdOn)


lemma exists_least_dirty_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty) :
    ∃ C : Circuit, JunkMinimum.IsJunkLeastAO G C ∧
      ∀ j ∈ junk G C, ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧
        gateVal n C j (pairInput a b) = true ∧
        gateVal n C j (pairInput c d) = true ∧ s(a, b) ≠ s(c, d) := by
  obtain ⟨C0, hC0⟩ := PEqualNP.Outside.L_meta_3566.exists_least_ao G hE
  obtain ⟨C, hC⟩ := JunkMinimum.exists_junk_least_ao G C0 hC0
  have hEdges : ∃ a b : Fin n, G.Adj a b := by
    obtain ⟨e, he⟩ := hE
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    exact ⟨a, b, by simpa using he⟩
  exact ⟨C, hC, fun j hj => dirty_accepts_two_edges G hEdges C hC j hj⟩

end PEqualNP.Outside.L_meta_3566.JunkNormalize

namespace PEqualNP.Outside.L_meta_3566.InputAlias

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma least_output_bound_of_gate {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (j : ℕ) (hj : j < C.size) : C.output < n + C.size := by
  by_contra ho
  let E : Circuit := ⟨[], n⟩
  have hE : IsAO2 n E := by
    simp [E, IsAO2, AndOrOnly, ReadsBack]
  have hEFun : circuitFun n E = graphFun G ∅ := by
    rw [← hC.2.1]
    funext x
    have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
      rw [SharedRewrite.wires_eq_foldl, SharedRewrite.foldl_stepWire_length]
      simp [Circuit.size]
    change (E.wires (List.ofFn x)).getD E.output false =
      (C.wires (List.ofFn x)).getD C.output false
    rw [List.getD_eq_default _ _ (by omega : (C.wires (List.ofFn x)).length ≤ C.output)]
    simp [E, Circuit.wires]
  have hmin := hC.2.2 E hE hEFun
  have hsize : E.size = 0 := rfl
  omega

lemma least_no_input_edgeprofile {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (j : ℕ) (hj : j < C.size) (u : Fin n)
    (hDown : ∀ x : Fin n → Bool, x u = true → gateVal n C j x = true)
    (hEdge : ∀ a b : Fin n, G.Adj a b →
      gateVal n C j (pairInput a b) = pairInput a b u) : False := by
  let g : Gate := ⟨GateOp.and, [u.val, u.val]⟩
  let D := SharedRewrite.replace C j g
  have hj' : j < C.gates.length := hj
  have hback : ∀ i ∈ g.inputs, i < n + j := by
    intro i hi
    have hi' : i = u.val := by simpa [g] using hi
    subst i
    omega
  have hD : IsAO2 n D :=
    SharedRewrite.replace_ao C hC.1 j hj' g (Or.inl rfl) rfl hback
  have hsize : D.size = C.size := SharedRewrite.replace_size C j g
  have heval (x : Fin n → Bool) :
      g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn x)).getD i false) = x u := by
    simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, Bool.and_self, SharedRewrite.input_val]
  have hfun : circuitFun n D = graphFun G ∅ := by
    apply EdgeProfile.eq_of_edges_and_below G _
    · intro x y hxy hx
      exact Bool.le_iff_imp.mp
        (SharedRewrite.circuitFun_monotone n D hD.1
          (fun i => Bool.le_iff_imp.mpr (hxy i))) hx
    · intro x hx
      have hle := SharedRewrite.replace_ge n C j hj' g hback hC.1.1 x (by
        rw [heval]
        exact Bool.le_iff_imp.mpr (hDown x))
      have ht := Bool.le_iff_imp.mp hle hx
      rw [hC.2.1] at ht
      exact ht
    · intro a b hab
      apply Bool.le_iff_imp.mp
        (SharedRewrite.replace_le n C j hj' g hback hC.1.1 (pairInput a b) ?_)
      · rw [hC.2.1]
        have hp : ∃ a' b', G.Adj a' b' ∧
            pairInput a b a' = true ∧ pairInput a b b' = true :=
          ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
        simpa [graphFun] using hp
      · rw [heval]
        change gateVal n C j (pairInput a b) ≤ pairInput a b u
        rw [hEdge a b hab]
  have hLeast : IsLeastAO G D := by
    refine ⟨hD, hfun, ?_⟩
    intro E hE hEFun
    rw [hsize]
    exact hC.2.2 E hE hEFun
  have hjD : j < D.size := by omega
  have hjD' : j < D.gates.length := hjD
  have hgate : gateAt D j = g := by
    simp [D, SharedRewrite.replace_gateAt C j g hj' j]
  have ho : D.output < n + D.size :=
    least_output_bound_of_gate G D hLeast j hjD
  apply Absorption.least_no_equivalent n G D hLeast j u.val hjD
    (by have := u.isLt; omega) ho
  intro x
  have heq := LeafStep.Pruning.gate_eq D hD j hjD' x
  simp only [hgate, g, LeafStep.Pruning.isA, LeafStep.Pruning.opv, opnd] at heq
  change gateVal n D j x = (wireVal n D u.val x && wireVal n D u.val x) at heq
  have hVal : gateVal n D j x = x u := by
    simpa only [wireVal, SharedRewrite.input_val, Bool.and_self] using heq
  simpa only [wireVal, gateVal, SharedRewrite.input_val] using hVal

end PEqualNP.Outside.L_meta_3566.InputAlias

namespace PEqualNP.Outside.L_meta_3566.PureWireSupport

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma gateVal_monotone (n : ℕ) (C : Circuit) (hAO : AndOrOnly C) (j : ℕ) :
    Monotone (gateVal n C j) :=
  SharedRewrite.circuitFun_monotone n ⟨C.gates, n + j⟩ hAO

lemma singleton_support_card_ge_two {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (j : ℕ) (hj : j < C.size)
    (hHit : ∃ a b : Fin n, G.Adj a b ∧ gateVal n C j (pairInput a b) = true)
    (hWitness : ∀ a b : Fin n, G.Adj a b → gateVal n C j (pairInput a b) = true →
      ∃ u : Fin n, gateVal n C j (pairInput u u) = true ∧ pairInput a b u = true) :
    2 ≤ (Finset.univ.filter fun u : Fin n =>
      gateVal n C j (pairInput u u) = true).card := by
  classical
  let S := Finset.univ.filter fun u : Fin n => gateVal n C j (pairInput u u) = true
  change 2 ≤ S.card
  by_contra hnot
  have hcard : S.card ≤ 1 := by omega
  obtain ⟨a, b, hab, hjOn⟩ := hHit
  obtain ⟨u, hu, _⟩ := hWitness a b hab hjOn
  have huS : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
  have hDown (x : Fin n → Bool) (hxu : x u = true) : gateVal n C j x = true := by
    apply Bool.le_iff_imp.mp (gateVal_monotone n C hC.1.1 j ?_) hu
    intro i
    apply Bool.le_iff_imp.mpr
    intro hi
    have hiu : i = u := by simpa [pairInput] using hi
    simpa [hiu] using hxu
  apply InputAlias.least_no_input_edgeprofile G C hC j hj u hDown
  intro c d hcd
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hjOn'
    obtain ⟨v, hv, hvOn⟩ := hWitness c d hcd hjOn'
    have hvS : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    have hvu : v = u := Finset.card_le_one.mp hcard v hvS u huS
    simpa only [hvu] using hvOn
  · intro huOn
    exact hDown _ huOn

end PEqualNP.Outside.L_meta_3566.PureWireSupport

namespace PEqualNP.Outside.L_meta_3566.JunkPivotal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def disable (C : Circuit) (j : ℕ) : Circuit :=
  SharedRewrite.replace C j ⟨GateOp.or, []⟩

def pivotal {n : ℕ} (C : Circuit) (j : ℕ) (a b : Fin n) : Prop :=
  circuitFun n (disable C j) (pairInput a b) = false

lemma disable_andOr (C : Circuit) (hAO : AndOrOnly C) (j : ℕ) :
    AndOrOnly (disable C j) := by
  intro g hg
  change g ∈ C.gates.set j ⟨GateOp.or, []⟩ at hg
  rcases List.mem_or_eq_of_mem_set hg with hg | rfl
  · exact hAO g hg
  · exact Or.inr rfl

lemma disable_gate_false (n : ℕ) (C : Circuit) (j : ℕ)
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    gateVal n (disable C j) j x = false := by
  let w0 := (C.gates.take j).foldl SharedRewrite.stepWire (List.ofFn x)
  have hlen : w0.length = n + j := by
    rw [SharedRewrite.foldl_stepWire_length]
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  change ((C.gates.set j ⟨GateOp.or, []⟩).foldl SharedRewrite.stepWire
    (List.ofFn x)).getD (n + j) false = false
  rw [List.set_eq_take_cons_drop _ hj, List.foldl_append, List.foldl_cons]
  change ((C.gates.drop (j + 1)).foldl SharedRewrite.stepWire
    (SharedRewrite.stepWire w0 ⟨GateOp.or, []⟩)).getD (n + j) false = false
  rw [SharedRewrite.foldl_stepWire_getD_lt _ _ _ (by
    simp [SharedRewrite.stepWire, hlen])]
  rw [← hlen, SharedRewrite.stepWire_getD_len]
  rfl

lemma replace_disable (C : Circuit) (j : ℕ) (g : Gate) :
    SharedRewrite.replace (disable C j) j g = SharedRewrite.replace C j g := by
  simp only [disable, SharedRewrite.replace, List.set_set]

lemma disable_le_replace (n : ℕ) (C : Circuit) (hAO : AndOrOnly C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j) (x : Fin n → Bool) :
    circuitFun n (disable C j) x ≤ circuitFun n (SharedRewrite.replace C j g) x := by
  have hjD : j < (disable C j).gates.length := by
    simpa [disable, SharedRewrite.replace] using hj
  have hle := SharedRewrite.replace_le n (disable C j) j hjD g hgback
    (disable_andOr C hAO j) x (by
      change gateVal n (disable C j) j x ≤ _
      rw [disable_gate_false n C j hj x]
      exact Bool.false_le _)
  simpa only [replace_disable] using hle

end PEqualNP.Outside.L_meta_3566.JunkPivotal

namespace PEqualNP.Outside.L_meta_3566.JunkPivotal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma correct_of_pivotal_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hFun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgop : g.op = GateOp.and ∨ g.op = GateOp.or) (hglen : g.inputs.length = 2)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hPos : ∀ a b : Fin n, G.Adj a b → pivotal C j a b →
      g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn (pairInput a b))).getD i false) = true)
    (hClean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
        graphFun G ∅ x = true) :
    IsAO2 n (SharedRewrite.replace C j g) ∧
      circuitFun n (SharedRewrite.replace C j g) = graphFun G ∅ ∧
      (SharedRewrite.replace C j g).size = C.size := by
  classical
  have hD := SharedRewrite.replace_ao C hAO j hj g hgop hglen hgback
  refine ⟨hD, ?_, SharedRewrite.replace_size C j g⟩
  apply EdgeProfile.eq_of_edges_and_below G _
  · intro x y hxy hx
    exact Bool.le_iff_imp.mp
      (SharedRewrite.circuitFun_monotone n _ hD.1 (fun i => Bool.le_iff_imp.mpr (hxy i))) hx
  · intro x hx
    by_contra hG
    have hzero : g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn x)).getD i false) = false := by
      apply Bool.eq_false_iff.mpr
      exact fun ht => hG (hClean x ht)
    have hle := SharedRewrite.replace_ge n C j hj g hgback hAO.1 x
      (by rw [hzero]; exact Bool.false_le _)
    have ht := Bool.le_iff_imp.mp hle hx
    rw [hFun] at ht
    exact hG ht
  · intro a b hab
    by_cases hp : pivotal C j a b
    · have hnew := hPos a b hab hp
      apply Bool.le_iff_imp.mp (SharedRewrite.replace_le n C j hj g hgback hAO.1
        (pairInput a b) (by rw [hnew]; exact Bool.le_true _))
      rw [hFun]
      have he : ∃ u v : Fin n, G.Adj u v ∧ pairInput a b u = true ∧ pairInput a b v = true :=
        ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
      simpa [graphFun] using he
    · have hdisabled : circuitFun n (disable C j) (pairInput a b) = true :=
        Bool.eq_true_of_not_eq_false hp
      exact Bool.le_iff_imp.mp (disable_le_replace n C hAO.1 j hj g hgback (pairInput a b))
        hdisabled

lemma pivotal_on {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hFun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (a b : Fin n) (hab : G.Adj a b)
    (hp : pivotal C j a b) : gateVal n C j (pairInput a b) = true := by
  cases hv : gateVal n C j (pairInput a b) with
  | true => rfl
  | false =>
    have hle := SharedRewrite.replace_le n C j hj ⟨GateOp.or, []⟩ (by simp)
      hAO.1 (pairInput a b) (by
        change gateVal n C j (pairInput a b) ≤ false
        rw [hv])
    have hold : circuitFun n C (pairInput a b) = true := by
      rw [hFun]
      have he : ∃ u v : Fin n, G.Adj u v ∧ pairInput a b u = true ∧ pairInput a b v = true :=
        ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
      simpa [graphFun] using he
    have hd := Bool.le_iff_imp.mp hle hold
    change circuitFun n (disable C j) (pairInput a b) = true at hd
    rw [hp] at hd
    exact False.elim (Bool.false_ne_true hd)

lemma one_pivotal_edge_not_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (w u : Fin n) (hwu : G.Adj w u)
    (hKeep : ∀ a b : Fin n, G.Adj a b → pivotal C j a b →
      (pairInput a b w && pairInput a b u) = true) :
    j ∉ junk G C := by
  intro hDirty
  have hOldOp := ((JunkNormalize.mem_junk_iff G C j).mp hDirty).2.1
  have hBack : ∀ i ∈ [w.val, u.val], i < n + j := by
    intro i hi
    simp at hi
    rcases hi with rfl | rfl <;> omega
  have hEval : ∀ x : Fin n → Bool,
      GateOp.and.eval ([w.val, u.val].map fun i =>
        (C.wires (List.ofFn x)).getD i false) = (x w && x u) := by
    intro x
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    rw [SharedRewrite.input_val, SharedRewrite.input_val]
  have hClean : ∀ x : Fin n → Bool,
      GateOp.and.eval ([w.val, u.val].map fun i =>
        (C.wires (List.ofFn x)).getD i false) = true → graphFun G ∅ x = true := by
    intro x hx
    rw [hEval] at hx
    have hx' : x w = true ∧ x u = true := by simpa using hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨w, u, hwu, hx'.1, hx'.2⟩
  obtain ⟨hD, hFun, hSize⟩ := correct_of_pivotal_cover G C hC.1.1 hC.1.2.1
    j hj ⟨GateOp.and, [w.val, u.val]⟩ (Or.inl rfl) rfl hBack
    (by intro a b hab hp; rw [hEval]; exact hKeep a b hab hp) hClean
  have hLeast : IsLeastAO G (SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩) :=
    ⟨hD, hFun, fun D hD hFunD => hSize.trans_le (hC.1.2.2 D hD hFunD)⟩
  have hStrict := JunkNormalize.junk_card_lt_of_clean_replace G C hC.1.1.1 j hj
    ⟨GateOp.and, [w.val, u.val]⟩ hOldOp.symm hBack hClean hDirty
    (JunkNormalize.edge_gate_below G C hC.1.1 j hj w u hwu)
  have hMin := hC.2 _ hLeast
  omega

lemma dirty_has_two_pivotal_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : ∃ w u : Fin n, G.Adj w u)
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (hDirty : j ∈ junk G C) :
    ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧
      pivotal C j a b ∧ pivotal C j c d ∧ s(a, b) ≠ s(c, d) := by
  classical
  have hj := ((JunkNormalize.mem_junk_iff G C j).mp hDirty).1
  by_contra hTwo
  by_cases hPivot : ∃ w u : Fin n, G.Adj w u ∧ pivotal C j w u
  · obtain ⟨w, u, hwu, hOn⟩ := hPivot
    apply one_pivotal_edge_not_dirty G C hC j hj w u hwu ?_ hDirty
    intro a b hab hp
    have heq : s(a, b) = s(w, u) := by
      by_contra hne
      exact hTwo ⟨w, u, a, b, hwu, hab, hOn, hp, fun he => hne he.symm⟩
    have hw : w ∈ s(a, b) := by rw [heq]; simp
    have hu : u ∈ s(a, b) := by rw [heq]; simp
    have hw' : pairInput a b w = true := by simpa [pairInput] using hw
    have hu' : pairInput a b u = true := by simpa [pairInput] using hu
    simp [hw', hu']
  · obtain ⟨w, u, hwu⟩ := hE
    apply one_pivotal_edge_not_dirty G C hC j hj w u hwu ?_ hDirty
    intro a b hab hp
    exact False.elim (hPivot ⟨a, b, hab, hp⟩)

lemma exists_least_dirty_two_pivotal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty) :
    ∃ C : Circuit, JunkMinimum.IsJunkLeastAO G C ∧
      ∀ j ∈ junk G C, ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧
        pivotal C j a b ∧ pivotal C j c d ∧ s(a, b) ≠ s(c, d) := by
  obtain ⟨C0, hC0⟩ := PEqualNP.Outside.L_meta_3566.exists_least_ao G hE
  obtain ⟨C, hC⟩ := JunkMinimum.exists_junk_least_ao G C0 hC0
  have hEdges : ∃ a b : Fin n, G.Adj a b := by
    obtain ⟨e, he⟩ := hE
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    exact ⟨a, b, by simpa using he⟩
  exact ⟨C, hC, fun j hj => dirty_has_two_pivotal_edges G hEdges C hC j hj⟩

end PEqualNP.Outside.L_meta_3566.JunkPivotal


namespace PEqualNP.Outside.L_meta_3566.SharedExit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma support_has_nonneighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hFour : NoFourCycle G) (z w : Fin n) (hwz : w ≠ z)
    (S : Finset (Fin n)) (hMany : 2 ≤ S.card)
    (hSupport : ∀ u ∈ S, G.Adj z u) :
    ∃ u ∈ S, ¬ G.Adj w u := by
  classical
  by_contra h
  have hAll : ∀ u ∈ S, G.Adj w u := by
    intro u hu
    by_contra hn
    exact h ⟨u, hu, hn⟩
  have hsub : S ⊆ Finset.univ.filter (fun u => G.Adj z u ∧ G.Adj w u) := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSupport u hu, hAll u hu⟩
  have hcard := (Finset.card_le_card hsub).trans (hFour z w hwz.symm)
  omega

lemma graphFun_nonedge_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w u : Fin n) (hwu : ¬ G.Adj w u) : graphFun G ∅ (pairInput w u) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hE : ∃ a b : Fin n, G.Adj a b ∧ (a = w ∨ a = u) ∧ (b = w ∨ b = u) := by
    simpa [graphFun, pairInput] using h
  obtain ⟨a, b, hab, ha, hb⟩ := hE
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hab.ne rfl
  · exact hwu hab
  · exact hwu hab.symm
  · exact hab.ne rfl

lemma no_other_monochrome_and_reader {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hBip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hFour : NoFourCycle G)
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (hOp : (gateAt C j).op = GateOp.and)
    (q : (Fin n → Bool) → Bool) (z w : Fin n)
    (hwz : w ≠ z) (hSame : color w = color z)
    (S : Finset (Fin n)) (hMany : 2 ≤ S.card)
    (hSingleton : ∀ u ∈ S, q (pairInput u u) = true)
    (hSupport : ∀ u, q (pairInput u u) = true → G.Adj z u)
    (hPure : ∀ a b, color a = color z → color b ≠ color z →
      q (pairInput a b) = q (pairInput b b))
    (hVal : ∀ x, gateVal n C j x = (x w && q x)) : False := by
  obtain ⟨u, hu, hwu⟩ := support_has_nonneighbor G hFour z w hwz S hMany
    (fun u hu => hSupport u (hSingleton u hu))
  have hqu := hSingleton u hu
  have hzu := hSupport u hqu
  have hOpp : color u ≠ color z := (hBip z u hzu).symm
  have hpair : q (pairInput w u) = true := (hPure w u hSame hOpp).trans hqu
  have hDirty : j ∈ junk G C := (JunkNormalize.mem_junk_iff G C j).mpr
    ⟨hj, hOp, pairInput w u, by rw [hVal]; simp [pairInput, hpair],
      graphFun_nonedge_pair G w u hwu⟩
  exact JunkNormalize.monochrome_reader_not_dirty_general G ⟨z, u, hzu⟩ color hBip
    hFour C hC j q z w hwz hSame hSupport hPure hVal hDirty

lemma monochrome_wire_and_reader_center {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hBip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hFour : NoFourCycle G)
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (hOp : (gateAt C j).op = GateOp.and)
    (r : ℕ) (z w : Fin n) (hSame : color w = color z)
    (hInputs : (gateAt C j).inputs = [w.val, r] ∨ (gateAt C j).inputs = [r, w.val])
    (S : Finset (Fin n)) (hMany : 2 ≤ S.card)
    (hSingleton : ∀ u ∈ S, wireVal n C r (pairInput u u) = true)
    (hSupport : ∀ u, wireVal n C r (pairInput u u) = true → G.Adj z u)
    (hPure : ∀ a b, color a = color z → color b ≠ color z →
      wireVal n C r (pairInput a b) = wireVal n C r (pairInput b b)) :
    w = z := by
  by_contra hwz
  apply no_other_monochrome_and_reader G color hBip hFour C hC j hj hOp
    (wireVal n C r) z w hwz hSame S hMany hSingleton hSupport hPure
  intro x
  have heq := LeafStep.Pruning.gate_eq C hC.1.1 j hj x
  rcases hInputs with hInputs | hInputs
  · simp only [opnd, hInputs, hOp, LeafStep.Pruning.isA, LeafStep.Pruning.opv] at heq
    change gateVal n C j x =
      ((C.wires (List.ofFn x)).getD w.val false && wireVal n C r x) at heq
    rw [SharedRewrite.input_val] at heq
    exact heq
  · simp only [opnd, hInputs, hOp, LeafStep.Pruning.isA, LeafStep.Pruning.opv] at heq
    change gateVal n C j x =
      (wireVal n C r x && (C.wires (List.ofFn x)).getD w.val false) at heq
    rw [SharedRewrite.input_val] at heq
    simpa only [Bool.and_comm] using heq

end PEqualNP.Outside.L_meta_3566.SharedExit


namespace PEqualNP.Outside.L_meta_3566.SharedExit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma no_opposite_color_and_reader {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hBip : ∀ a b, G.Adj a b → color a ≠ color b)
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (hOp : (gateAt C j).op = GateOp.and)
    (q : (Fin n → Bool) → Bool)
    (hMono : ∀ x y, (∀ i, x i = true → y i = true) → q x = true → q y = true)
    (z w : Fin n) (hOpp : color w ≠ color z)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (hSingleton : ∀ u ∈ S, q (pairInput u u) = true)
    (hSupport : ∀ u, q (pairInput u u) = true → G.Adj z u)
    (hPure : ∀ a b, color a = color z → color b ≠ color z →
      q (pairInput a b) = q (pairInput b b))
    (hVal : ∀ x, gateVal n C j x = (x w && q x)) : False := by
  obtain ⟨u, hu⟩ := hS
  have hqu := hSingleton u hu
  have hzu := hSupport u hqu
  have hOppU : color u ≠ color z := (hBip z u hzu).symm
  have hSame : color w = color u := by
    cases hw : color w <;> cases hu' : color u <;> cases hz : color z <;> simp_all
  have hwu : ¬ G.Adj w u := fun h => hBip w u h hSame
  have hPairQ : q (pairInput w u) = true := hMono (pairInput u u) (pairInput w u) (by
    intro i hi
    have hiu : i = u := by simpa [pairInput] using hi
    simp [pairInput, hiu]) hqu
  have hDirty : j ∈ junk G C := (JunkNormalize.mem_junk_iff G C j).mpr
    ⟨hj, hOp, pairInput w u, by rw [hVal]; simp [pairInput, hPairQ],
      graphFun_nonedge_pair G w u hwu⟩
  rcases opposite_color_and_absorb G color hBip q hMono z w hOpp hPure with
    ⟨_, hAlias⟩ | ⟨_, hZero⟩
  · apply InputAlias.least_no_input_edgeprofile G C hC.1 j hj w
    · intro x hx
      rw [hVal, hAlias]
      exact hx
    · intro a b _
      rw [hVal, hAlias]
  · obtain ⟨a, b, c, d, hab, _, hOn, _, _⟩ :=
      JunkNormalize.dirty_accepts_two_edges G ⟨z, u, hzu⟩ C hC j hDirty
    rw [hVal, hZero a b hab] at hOn
    exact Bool.false_ne_true hOn

lemma wire_and_reader_center {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hBip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hFour : NoFourCycle G)
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (hOp : (gateAt C j).op = GateOp.and)
    (r : ℕ) (z w : Fin n)
    (hInputs : (gateAt C j).inputs = [w.val, r] ∨ (gateAt C j).inputs = [r, w.val])
    (S : Finset (Fin n)) (hMany : 2 ≤ S.card)
    (hSingleton : ∀ u ∈ S, wireVal n C r (pairInput u u) = true)
    (hSupport : ∀ u, wireVal n C r (pairInput u u) = true → G.Adj z u)
    (hPure : ∀ a b, color a = color z → color b ≠ color z →
      wireVal n C r (pairInput a b) = wireVal n C r (pairInput b b)) :
    w = z := by
  by_cases hSame : color w = color z
  · exact monochrome_wire_and_reader_center G color hBip hFour C hC j hj hOp r z w
      hSame hInputs S hMany hSingleton hSupport hPure
  · exfalso
    have hMono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
        wireVal n C r x = true → wireVal n C r y = true := by
      intro x y hxy hx
      exact Bool.le_iff_imp.mp
        (SharedRewrite.circuitFun_monotone n ⟨C.gates, r⟩ hC.1.1.1
          (fun i => Bool.le_iff_imp.mpr (hxy i))) hx
    apply no_opposite_color_and_reader G color hBip C hC j hj hOp (wireVal n C r)
      hMono z w hSame S (Finset.card_pos.mp (by omega)) hSingleton hSupport hPure
    intro x
    have heq := LeafStep.Pruning.gate_eq C hC.1.1 j hj x
    rcases hInputs with hInputs | hInputs
    · simp only [opnd, hInputs, hOp, LeafStep.Pruning.isA, LeafStep.Pruning.opv] at heq
      change gateVal n C j x =
        ((C.wires (List.ofFn x)).getD w.val false && wireVal n C r x) at heq
      rw [SharedRewrite.input_val] at heq
      exact heq
    · simp only [opnd, hInputs, hOp, LeafStep.Pruning.isA, LeafStep.Pruning.opv] at heq
      change gateVal n C j x =
        (wireVal n C r x && (C.wires (List.ofFn x)).getD w.val false) at heq
      rw [SharedRewrite.input_val] at heq
      simpa only [Bool.and_comm] using heq

end PEqualNP.Outside.L_meta_3566.SharedExit


namespace PEqualNP.Outside.L_meta_3566.OrCross
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

def Cross (a b c d : Bool) : Prop :=
  (a = true ∧ b = false ∧ c = false ∧ d = true) ∨
    (a = false ∧ b = true ∧ c = true ∧ d = false)

lemma gate_meet (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b c d : Bool) (hc : op = GateOp.or → ¬ Cross a b c d) :
    LeafStep.Pruning.opv (LeafStep.Pruning.isA op) (a && c) (b && d) =
      (LeafStep.Pruning.opv (LeafStep.Pruning.isA op) a b &&
        LeafStep.Pruning.opv (LeafStep.Pruning.isA op) c d) := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [LeafStep.Pruning.opv, LeafStep.Pruning.isA, Cross]

lemma no_cross_meet (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x y : Fin n → Bool)
    (hc : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ¬ Cross (wireVal n C (opnd C j 0) x) (wireVal n C (opnd C j 1) x)
        (wireVal n C (opnd C j 0) y) (wireVal n C (opnd C j 1) y)) :
    circuitFun n C (fun i => x i && y i) = (circuitFun n C x && circuitFun n C y) := by
  have hw : ∀ w, wireVal n C w (fun i => x i && y i) =
      (wireVal n C w x && wireVal n C w y) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hi : w < n
      · rw [LeafStep.Pruning.wireVal_lt C w hi, LeafStep.Pruning.wireVal_lt C w hi,
          LeafStep.Pruning.wireVal_lt C w hi]
      · by_cases hj : w < n + C.gates.length
        · let j := w - n
          have hj' : j < C.gates.length := by dsimp [j]; omega
          have heq : w = n + j := by dsimp [j]; omega
          have hmem : gateAt C j ∈ C.gates := by
            have he : C.gates[j]? = some (gateAt C j) := by
              simp [gateAt, List.getD_eq_getElem?_getD, hj']
            exact List.mem_of_getElem? he
          have hlen := hAO.2.2 _ hmem
          have hb : ∀ b : Fin 2, opnd C j b < w := by
            intro b
            obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
            have hm : opnd C j b ∈ (gateAt C j).inputs := by
              fin_cases b <;> simp [opnd, hpq]
            have hlt := hAO.2.1 j hj' _ hm
            omega
          rw [heq]
          change gateVal n C j _ = (gateVal n C j x && gateVal n C j y)
          rw [LeafStep.Pruning.gate_eq C hAO j hj', LeafStep.Pruning.gate_eq C hAO j hj',
            LeafStep.Pruning.gate_eq C hAO j hj', ih _ (hb 0), ih _ (hb 1)]
          exact gate_meet _ (hAO.1 _ hmem) _ _ _ _ (hc j hj')
        · have hz : ∀ t : Fin n → Bool, wireVal n C w t = false := by
            intro t
            apply SharedRewrite.getD_ge_length
            have hl := SharedRewrite.foldl_stepWire_length C.gates (List.ofFn t)
            change (C.gates.foldl SharedRewrite.stepWire (List.ofFn t)).length ≤ w
            rw [hl]
            simp only [List.length_ofFn]
            omega
          rw [hz, hz, hz]
          rfl
  exact hw C.output

lemma exists_or_cross (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hx : circuitFun n C x = true) (hy : circuitFun n C y = true)
    (hmeet : circuitFun n C (fun i => x i && y i) = false) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.or ∧
      Cross (wireVal n C (opnd C j 0) x) (wireVal n C (opnd C j 1) x)
        (wireVal n C (opnd C j 0) y) (wireVal n C (opnd C j 1) y) := by
  by_contra h
  have hc : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ¬ Cross (wireVal n C (opnd C j 0) x) (wireVal n C (opnd C j 1) x)
        (wireVal n C (opnd C j 0) y) (wireVal n C (opnd C j 1) y) := by
    intro j hj ho hcross
    exact h ⟨j, hj, ho, hcross⟩
  have he := no_cross_meet n C hAO x y hc
  rw [hx, hy, hmeet] at he
  contradiction

end PEqualNP.Outside.L_meta_3566.OrCross


namespace PEqualNP.Outside.L_meta_3566.OrCross

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma graph_distinct_edges_cross {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hFun : circuitFun n C = graphFun G ∅)
    (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d) (hne : s(a, b) ≠ s(c, d)) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.or ∧
      Cross (wireVal n C (opnd C j 0) (pairInput a b))
        (wireVal n C (opnd C j 1) (pairInput a b))
        (wireVal n C (opnd C j 0) (pairInput c d))
        (wireVal n C (opnd C j 1) (pairInput c d)) := by
  have edge_on (u v : Fin n) (huv : G.Adj u v) :
      circuitFun n C (pairInput u v) = true := by
    rw [hFun]
    have hE : ∃ p q : Fin n, G.Adj p q ∧ pairInput u v p = true ∧ pairInput u v q = true :=
      ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    simpa [graphFun] using hE
  apply exists_or_cross n C hAO (pairInput a b) (pairInput c d)
    (edge_on a b hab) (edge_on c d hcd)
  rw [hFun]
  apply Bool.eq_false_iff.mpr
  intro hOn
  have hE : ∃ u v : Fin n, G.Adj u v ∧
      (pairInput a b u && pairInput c d u) = true ∧
      (pairInput a b v && pairInput c d v) = true := by
    simpa [graphFun] using hOn
  obtain ⟨u, v, huv, hu, hv⟩ := hE
  have hu' : (u = a ∨ u = b) ∧ (u = c ∨ u = d) := by simpa [pairInput] using hu
  have hv' : (v = a ∨ v = b) ∧ (v = c ∨ v = d) := by simpa [pairInput] using hv
  apply hne
  apply Sym2.eq_of_ne_mem huv.ne <;> simp only [Sym2.mem_iff]
  · exact hu'.1
  · exact hv'.1
  · exact hu'.2
  · exact hv'.2

end PEqualNP.Outside.L_meta_3566.OrCross


namespace PEqualNP.Outside.L_meta_3566.JunkNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma junk_subset_of_clean_replace_any_op {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : AndOrOnly C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hClean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
        graphFun G ∅ x = true)
    (hNewClean : BelowF G (SharedRewrite.replace C j g) j) :
    junk G (SharedRewrite.replace C j g) ⊆ junk G C := by
  intro k hk
  obtain ⟨hk, hkop, x, hv, hFalse⟩ := (mem_junk_iff G _ k).mp hk
  by_cases hkj : k = j
  · subst k
    have hF := hNewClean x hv
    rw [hFalse] at hF
    exact False.elim (Bool.false_ne_true hF)
  · have hk' : k < C.gates.length := by simpa [SharedRewrite.replace] using hk
    have hsame : (gateAt (SharedRewrite.replace C j g) k).op = (gateAt C k).op := by
      rw [SharedRewrite.replace_gateAt C j g hj k, ite_eq_right (fun h => hkj h.symm)]
    have hzero : g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn x)).getD i false) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have hF := hClean x ht
      rw [hFalse] at hF
      exact Bool.false_ne_true hF
    have hle : gateVal n (SharedRewrite.replace C j g) k x ≤ gateVal n C k x :=
      SharedRewrite.replace_ge n ⟨C.gates, n + k⟩ j hj g hgback hAO x
        (by change g.op.eval (g.inputs.map fun i =>
              (C.wires (List.ofFn x)).getD i false) ≤ _
            rw [hzero]
            exact Bool.false_le _)
    exact (mem_junk_iff G C k).mpr
      ⟨hk', hsame ▸ hkop, x, Bool.le_iff_imp.mp hle hv, hFalse⟩

lemma junk_card_lt_of_clean_replace_any_op {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : AndOrOnly C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hClean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
        graphFun G ∅ x = true)
    (hDirty : j ∈ junk G C)
    (hNewClean : BelowF G (SharedRewrite.replace C j g) j) :
    (junk G (SharedRewrite.replace C j g)).card < (junk G C).card := by
  have hsub := junk_subset_of_clean_replace_any_op G C hAO j hj g hgback hClean hNewClean
  have hjnot : j ∉ junk G (SharedRewrite.replace C j g) := by
    intro hjmem
    obtain ⟨_, _, x, hv, hf⟩ := (mem_junk_iff G _ j).mp hjmem
    have ht := hNewClean x hv
    rw [hf] at ht
    exact Bool.false_ne_true ht
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  rw [heq] at hjnot
  exact hjnot hDirty

end PEqualNP.Outside.L_meta_3566.JunkNormalize

namespace PEqualNP.Outside.L_meta_3566.FalseRestrict

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

lemma three_count_of_and_chain (gs : List Gate) (bs : List Bool) (j k w : ℕ)
    (hjk : j < k) (hk : k < gs.length) (hw : w < bs.length)
    (hflag : bs.getD w true = true)
    (hjop : (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and)
    (hjlen : (gs.getD j ⟨GateOp.or, []⟩).inputs.length = 2)
    (hjread : w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs)
    (hkop : (gs.getD k ⟨GateOp.or, []⟩).op = GateOp.and)
    (hklen : (gs.getD k ⟨GateOp.or, []⟩).inputs.length = 2)
    (hkread : bs.length + j ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs)
    (g : Gate) (hmem : g ∈ gs.drop (k + 1)) (hglen : g.inputs.length = 2)
    (hreader : bs.length + k ∈ g.inputs) : 3 ≤ (deadRun bs gs).2 := by
  induction gs generalizing bs j k with
  | nil => simp at hk
  | cons a gs ih =>
    cases k with
    | zero => omega
    | succ k =>
      have hk' : k < gs.length := by simpa using hk
      have hkop' : (gs.getD k ⟨GateOp.or, []⟩).op = GateOp.and := hkop
      have hklen' : (gs.getD k ⟨GateOp.or, []⟩).inputs.length = 2 := hklen
      have hm : g ∈ gs.drop (k + 1) := by simpa using hmem
      cases j with
      | zero =>
        have hjop' : a.op = GateOp.and := hjop
        have hjlen' : a.inputs.length = 2 := hjlen
        have hjread' : w ∈ a.inputs := hjread
        have hhead := flags_or_true_of_mem bs a w hjlen' hjread' hflag
        have hv : blockStep a.op (bs.getD (a.inputs.getD 0 0) true)
            (bs.getD (a.inputs.getD 1 0) true) = true := by
          simpa only [hjop', blockStep] using hhead
        have hkread' : bs.length ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs := by
          simpa using hkread
        have hr : (bs ++ [true]).length + k ∈ g.inputs := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hreader
        have ht := two_count_of_and_reader gs (bs ++ [true]) k bs.length hk'
          (by simp) (by simp) hkop' hklen' hkread' g hm hglen hr
        simp only [deadRun, hv, hhead, ↓reduceIte]
        omega
      | succ j =>
        let v := blockStep a.op (bs.getD (a.inputs.getD 0 0) true)
          (bs.getD (a.inputs.getD 1 0) true)
        have hjk' : j < k := by omega
        have hw' : w < (bs ++ [v]).length := by simp; omega
        have hf' : (bs ++ [v]).getD w true = true := by
          rw [List.getD_append _ _ _ _ hw]
          exact hflag
        have hjop' : (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and := hjop
        have hjlen' : (gs.getD j ⟨GateOp.or, []⟩).inputs.length = 2 := hjlen
        have hjread' : w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs := hjread
        have hkread' : (bs ++ [v]).length + j ∈
            (gs.getD k ⟨GateOp.or, []⟩).inputs := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkread
        have hr : (bs ++ [v]).length + k ∈ g.inputs := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hreader
        have ht := ih (bs ++ [v]) j k hjk' hk' hw' hf' hjop' hjlen' hjread'
          hkop' hklen' hkread' hm hr
        simp only [deadRun]
        change 3 ≤ _ + (deadRun (bs ++ [v]) gs).2
        omega

lemma three_removed_of_and_chain (n : ℕ) (z : Fin n) (C : Circuit) (hAO : IsAO2 n C)
    (j k l : ℕ) (hjk : j < k) (hkl : k < l) (hl : l < C.size)
    (hjop : (gateAt C j).op = GateOp.and)
    (hz : z.val ∈ (gateAt C j).inputs)
    (hkop : (gateAt C k).op = GateOp.and)
    (hkread : n + j ∈ (gateAt C k).inputs)
    (hlread : n + k ∈ (gateAt C l).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      D.size + 3 ≤ C.size := by
  have hj : j < C.gates.length := by change j < C.size; omega
  have hk : k < C.gates.length := by change k < C.size; omega
  have hl' : l < C.gates.length := hl
  have hjmem : gateAt C j ∈ C.gates := list_getD_mem C.gates j _ hj
  have hkmem : gateAt C k ∈ C.gates := list_getD_mem C.gates k _ hk
  have hlmem : gateAt C l ∈ C.gates := list_getD_mem C.gates l _ hl'
  have hm : gateAt C l ∈ C.gates.drop (k + 1) :=
    list_getD_mem_drop C.gates (k + 1) l _ (by omega) hl'
  have hb : (initialDead n z).length = n := by simp [initialDead]
  have hf : (initialDead n z).getD z.val true = true := by simp [initialDead]
  have hcnt : 3 ≤ blockedCount n z C :=
    three_count_of_and_chain C.gates (initialDead n z) j k z.val hjk hk
      (by rw [hb]; exact z.isLt) hf hjop (hAO.2.2 _ hjmem) hz
      hkop (hAO.2.2 _ hkmem) (by simpa only [hb, gateAt] using hkread)
      (gateAt C l) hm (hAO.2.2 _ hlmem) (by simpa only [hb] using hlread)
  obtain ⟨D, hD, hF, hsize⟩ := exists_blocked_restriction n z C hAO
  exact ⟨D, hD, hF, by omega⟩

end PEqualNP.Outside.L_meta_3566.FalseRestrict

namespace PEqualNP.Outside.L_meta_3566.AndFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma and_read_false {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (k : ℕ) (hk : k < C.size) (hop : (gateAt C k).op = GateOp.and)
    (w : ℕ) (hw : w ∈ (gateAt C k).inputs) (x : Fin n → Bool)
    (hFalse : wireVal n C w x = false) : gateVal n C k x = false := by
  have hmem : gateAt C k ∈ C.gates := FalseRestrict.list_getD_mem C.gates k _ hk
  obtain ⟨a, b, hInputs⟩ := List.length_eq_two.mp (hC.2.2 _ hmem)
  have hw' : w = a ∨ w = b := by simpa [hInputs] using hw
  have heq := LeafStep.Pruning.gate_eq C hC k hk x
  simp only [hop, LeafStep.Pruning.isA, LeafStep.Pruning.opv, opnd, hInputs] at heq
  change gateVal n C k x = (wireVal n C a x && wireVal n C b x) at heq
  rcases hw' with rfl | rfl
  · rw [hFalse] at heq
    simpa using heq
  · rw [hFalse] at heq
    simpa using heq

lemma and_and_restriction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (z : Fin n)
    (hNon : (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty)
    (j k : ℕ) (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.and) (hz : z.val ∈ (gateAt C j).inputs)
    (hkop : (gateAt C k).op = GateOp.and) (hkread : n + j ∈ (gateAt C k).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      D.size + 3 ≤ C.size := by
  classical
  obtain ⟨e, he⟩ := hNon
  have hEdges : ∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b := by
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    exact ⟨a, b, by simpa using he⟩
  obtain ⟨a, b, hab⟩ := hEdges
  let x : Fin n → Bool := Function.update (fun _ => true) z false
  have hx : x z = false := by simp [x]
  have hGraph := congrFun (FanoutStep.graphFun_update_false G z) (fun _ => true)
  have hTrue : circuitFun n C x = true := by
    rw [hC.2.1]
    change graphFun G ∅ (Function.update (fun _ => true) z false) = true
    rw [hGraph]
    simp only [decide_eq_true_eq]
    exact ⟨a, b, hab, by trivial, by trivial⟩
  have hj : j < C.size := lt_trans hjk hk
  have hjFalse : wireVal n C (n + j) x = false :=
    LeafStep.and_input_false C j hj hjop z hz x hx
  have hkFalse := and_read_false C hC.1 k hk hkop (n + j) hkread x hjFalse
  have hOutput : C.output ≠ n + k := by
    intro h
    change (C.wires (List.ofFn x)).getD C.output false = true at hTrue
    rw [h] at hTrue
    change gateVal n C k x = true at hTrue
    rw [hkFalse] at hTrue
    exact Bool.false_ne_true hTrue
  have ho := InputAlias.least_output_bound_of_gate G C hC k hk
  obtain ⟨l, hkl, hl, hlread⟩ := LeafStep.reader_of_least G C hC k hk ho hOutput
  exact FalseRestrict.three_removed_of_and_chain n z C hC.1 j k l hjk hkl hl
    hjop hz hkop hkread hlread

end PEqualNP.Outside.L_meta_3566.AndFrontier
