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
