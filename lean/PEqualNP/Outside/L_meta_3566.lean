import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.MetaComplexity.CoverPromise

theorem cut_adj {n : ℕ} (G : SimpleGraph (Fin n)) (z u v : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).Adj u v ↔ G.Adj u v ∧ u ≠ z ∧ v ≠ z := by
  exact SimpleGraph.deleteIncidenceSet_adj

theorem exists_positive_cut_edge (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧
      ∃ u v : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj u v := by
  classical
  obtain ⟨e, he, f, hf, hne⟩ := Finset.one_lt_card.mp (show 1 < G.edgeFinset.card by omega)
  induction e using Sym2.inductionOn with
  | hf a b =>
    induction f using Sym2.inductionOn with
    | hf c d =>
      have hab : G.Adj a b := by simpa using he
      have hcd : G.Adj c d := by simpa using hf
      have hab' : a ≠ b := G.ne_of_adj hab
      have hout : (a ≠ c ∧ a ≠ d) ∨ (b ≠ c ∧ b ≠ d) := by
        by_cases hac : a = c <;> by_cases had : a = d <;>
          by_cases hbc : b = c <;> by_cases hbd : b = d <;>
          simp_all
      rcases hout with ⟨hac, had⟩ | ⟨hbc, hbd⟩
      · exact ⟨a, (G.degree_pos_iff_exists_adj a).mpr ⟨b, hab⟩, c, d,
          (cut_adj G a c d).mpr ⟨hcd, hac.symm, had.symm⟩⟩
      · exact ⟨b, (G.degree_pos_iff_exists_adj b).mpr ⟨a, hab.symm⟩, c, d,
          (cut_adj G b c d).mpr ⟨hcd, hbc.symm, hbd.symm⟩⟩

theorem exists_positive_cut_nonempty (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧
      (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty := by
  classical
  obtain ⟨z, hz, u, v, huv⟩ := exists_positive_cut_edge n G h
  exact ⟨z, hz, s(u, v), by simpa using huv⟩

theorem cut_edge_card (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (z : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).edgeFinset.card + G.degree z = G.edgeFinset.card := by
  classical
  change (G.deleteIncidenceSet z).edgeFinset.card + G.degree z = G.edgeFinset.card
  rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset z)

theorem exists_min_cover (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ S : Finset (Fin n), IsVertexCover G S ∧
      ∀ T : Finset (Fin n), IsVertexCover G T → S.card ≤ T.card := by
  classical
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n), IsVertexCover G S ∧ S.card = k :=
    ⟨Finset.univ.card, Finset.univ, by intro u v h; simp, rfl⟩
  obtain ⟨S, hS, hSk⟩ := Nat.find_spec hex
  refine ⟨S, hS, ?_⟩
  intro T hT
  have := Nat.find_min' hex (show ∃ S : Finset (Fin n), IsVertexCover G S ∧ S.card = T.card
    from ⟨T, hT, rfl⟩)
  omega

theorem cut_cover_of_cover {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S : Finset (Fin n)) (hS : IsVertexCover G S) :
    IsVertexCover (G.deleteEdges (G.incidenceSet z)) S := by
  intro u v h
  exact hS u v ((cut_adj G z u v).mp h).1

theorem cover_insert_of_cut_cover {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S : Finset (Fin n)) (hS : IsVertexCover (G.deleteEdges (G.incidenceSet z)) S) :
    IsVertexCover G (insert z S) := by
  intro u v h
  by_cases hu : u = z
  · exact Or.inl (by simp [hu])
  by_cases hv : v = z
  · exact Or.inr (by simp [hv])
  rcases hS u v ((cut_adj G z u v).mpr ⟨h, hu, hv⟩) with h | h
  · exact Or.inl (Finset.mem_insert_of_mem h)
  · exact Or.inr (Finset.mem_insert_of_mem h)

theorem cut_cover_erase {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S : Finset (Fin n)) (hS : IsVertexCover (G.deleteEdges (G.incidenceSet z)) S) :
    IsVertexCover (G.deleteEdges (G.incidenceSet z)) (S.erase z) := by
  intro u v h
  have hne := (cut_adj G z u v).mp h
  rcases hS u v h with hu | hv
  · exact Or.inl (Finset.mem_erase.mpr ⟨hne.2.1, hu⟩)
  · exact Or.inr (Finset.mem_erase.mpr ⟨hne.2.2, hv⟩)

theorem min_cover_cut_bounds {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S T : Finset (Fin n))
    (hS : IsVertexCover (G.deleteEdges (G.incidenceSet z)) S)
    (hSm : ∀ U : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) U →
      S.card ≤ U.card)
    (hT : IsVertexCover G T)
    (hTm : ∀ U : Finset (Fin n), IsVertexCover G U → T.card ≤ U.card) :
    S.card ≤ T.card ∧ T.card ≤ S.card + 1 := by
  refine ⟨hSm T (cut_cover_of_cover G z T hT), ?_⟩
  exact (hTm (insert z S) (cover_insert_of_cut_cover G z S hS)).trans
    (Finset.card_insert_le z S)

theorem cut_cover_drop_iff {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S T : Finset (Fin n))
    (hS : IsVertexCover (G.deleteEdges (G.incidenceSet z)) S)
    (hSm : ∀ U : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) U →
      S.card ≤ U.card)
    (hT : IsVertexCover G T)
    (hTm : ∀ U : Finset (Fin n), IsVertexCover G U → T.card ≤ U.card) :
    (∃ U : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) U ∧
      ∀ V : Finset (Fin n), IsVertexCover G V → U.card < V.card) ↔
      S.card + 1 = T.card := by
  have hb := min_cover_cut_bounds G z S T hS hSm hT hTm
  constructor
  · rintro ⟨U, hU, hUmin⟩
    have h1 := hSm U hU
    have h2 := hUmin T hT
    omega
  · intro h
    refine ⟨S, hS, ?_⟩
    intro V hV
    have := hTm V hV
    omega

end PEqualNP.Outside.L_meta_3566

namespace PEqualNP.Outside.L_meta_3566.Upper

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

lemma readsBack_append {m : ℕ} {gs1 gs2 : List Gate} {o1 o2 : ℕ}
    (h1 : ReadsBack m ⟨gs1, o1⟩) (h2 : ReadsBack (m + gs1.length) ⟨gs2, o2⟩) :
    ReadsBack m ⟨gs1 ++ gs2, 0⟩ := by
  intro j hj i hi
  change i ∈ ((gs1 ++ gs2).getD j ⟨GateOp.or, []⟩).inputs at hi
  by_cases h : j < gs1.length
  · rw [List.getD_append _ _ _ _ h] at hi
    exact h1 j h i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    have hj2 : j - gs1.length < gs2.length := by
      change j < (gs1 ++ gs2).length at hj
      simp only [List.length_append] at hj
      omega
    have hh := h2 (j - gs1.length) hj2 i hi
    omega

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧ ReadsBack m ⟨gs, out⟩ ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

lemma bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, nn, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, nn, le_trans len hs, ho, ev⟩

lemma bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, nn, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, nn, len, ho, fun w hw => by rw [ev w hw, e]⟩

lemma bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, by intro j hj; simp at hj, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

lemma bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, nn1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, nn2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [h]
  · have hpre := readsBack_append nn1 nn2
    have hlast : ReadsBack (m + (gs1 ++ gs2).length) ⟨[⟨op, [o1, o2]⟩], 0⟩ := by
      intro j hj i hi
      have hj0 : j = 0 := by simpa using hj
      subst j
      simp only [gateAt, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> simp only [List.length_append] <;> omega
    exact readsBack_append hpre hlast
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
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = F ∧ D.size ≤ s := by
  obtain ⟨gs, out, ok, rb, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ⟨(fun g hg => (ok g hg).1), rb, (fun g hg => (ok g hg).2)⟩, ?_, len⟩
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


lemma edge_upper_ao (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (hE : ∃ i j : Fin n, G.Adj i j)
    (hc : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      D.size + 1 ≤ G.edgeFinset.card + T.card := by
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

end PEqualNP.Outside.L_meta_3566.Upper
namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.CoverPromise PEqualNP.MetaComplexity.NestedCover

theorem peel_of_cover_bound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : 2 ≤ G.edgeFinset.card)
    (hbound : ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ T : Finset (Fin n), IsVertexCover G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1) :
    ∃ z : Fin n, 0 < G.degree z ∧
      ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, IsAO2 n D ∧
        circuitFun n D = (fun y : Fin n → Bool =>
          @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧
            y a = true ∧ y b = true) (Classical.propDecidable _)) ∧
        D.size + G.degree z ≤ C.size ∧
        ((∃ S : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
          ∀ T : Finset (Fin n), IsVertexCover G T → S.card < T.card) →
          D.size + G.degree z + 1 ≤ C.size) := by
  classical
  obtain ⟨z, hz, u, v, huv⟩ := exists_positive_cut_edge n G hE
  obtain ⟨S, hS, hSm⟩ := exists_min_cover n (G.deleteEdges (G.incidenceSet z))
  refine ⟨z, hz, ?_⟩
  intro C hC hF
  obtain ⟨T, hT, hTC⟩ := hbound C hC hF
  obtain ⟨D, hD, hDF, hDS⟩ := Upper.edge_upper_ao n
    (G.deleteEdges (G.incidenceSet z)) S ⟨u, v, huv⟩ hS
  have he := cut_edge_card n G z
  have hST := hSm T (cut_cover_of_cover G z T hT)
  refine ⟨D, hD, ?_, by omega, ?_⟩
  · funext y
    rw [congrFun hDF y]
    exact decide_eq_decide.mpr Iff.rfl
  · rintro ⟨U, hU, hUall⟩
    have hSU := hSm U hU
    have hUT := hUall T hT
    omega

end PEqualNP.Outside.L_meta_3566

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.MetaComplexity.CoverPromise

def PeelStatement : Prop :=
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) → PEqualNP.TopForm.NoFourCycle G → 2 ≤ G.edgeFinset.card → ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ PEqualNP.MetaComplexity.circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true) (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧ ((∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧ ∀ T : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T → S.card < T.card) → D.size + G.degree z + 1 ≤ C.size)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem graph_singleton_false {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (i : Fin n) :
    graphFun G ∅ (fun j => decide (j = i)) = false := by
  simp [graphFun]

theorem graph_circuit_size_pos {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hne : G.edgeFinset.Nonempty) (C : Circuit)
    (hfun : circuitFun n C = graphFun G ∅) : 0 < C.size := by
  classical
  by_contra hsize
  have hnil : C.gates = [] := by
    have hh : C.size = 0 := Nat.eq_zero_of_not_pos hsize
    cases he : C.gates with
    | nil => rfl
    | cons a l => simp [Circuit.size, he] at hh
  have hval (x : Fin n → Bool) : circuitFun n C x = (List.ofFn x).getD C.output false := by
    simp [circuitFun, Circuit.eval, Circuit.wires, hnil]
  by_cases ho : C.output < n
  · let i : Fin n := ⟨C.output, ho⟩
    have hh := congrFun hfun (fun j => decide (j = i))
    rw [hval, graph_singleton_false G i] at hh
    simp [List.getD_eq_getElem?_getD, ho, i] at hh
  · obtain ⟨e, he⟩ := hne
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hab : G.Adj a b := by simpa using he
      have hg : graphFun G ∅ (fun _ => true) = true := by
        simpa [graphFun] using (show ∃ u v, G.Adj u v from ⟨a, b, hab⟩)
      have hh := congrFun hfun (fun _ => true)
      rw [hval, hg] at hh
      simp [List.getD_eq_getElem?_getD, ho] at hh

theorem one_edge_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcard : G.edgeFinset.card = 1) :
    ∃ T : Finset (Fin n), IsVertexCover G T ∧ T.card = 1 := by
  classical
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  induction e using Sym2.inductionOn with
  | hf a b =>
    refine ⟨{a}, ?_, by simp⟩
    intro u v huv
    have hm : s(u, v) ∈ G.edgeFinset := by simpa using huv
    have heq : s(u, v) = s(a, b) := by simpa [he] using hm
    rcases Sym2.eq_iff.mp heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inl (by simp [hu])
    · exact Or.inr (by simp [hv])

theorem cut_bipartite {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (hb : ∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) :
    ∃ c : Fin n → Bool, ∀ u v : Fin n,
      (G.deleteEdges (G.incidenceSet z)).Adj u v → c u ≠ c v := by
  obtain ⟨c, hc⟩ := hb
  exact ⟨c, fun u v h => hc u v ((cut_adj G z u v).mp h).1⟩

theorem cut_no_four_cycle {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (h4 : PEqualNP.TopForm.NoFourCycle G) :
    PEqualNP.TopForm.NoFourCycle (G.deleteEdges (G.incidenceSet z)) := by
  classical
  intro a b hab
  apply le_trans (Finset.card_le_card ?_) (h4 a b hab)
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  exact ⟨((cut_adj G z a w).mp hw.1).1, ((cut_adj G z b w).mp hw.2).1⟩

theorem lower_bound_of_peeling (hp : PeelStatement) (n : ℕ) :
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) →
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty →
      ∀ C : Circuit, PEqualNP.TopForm.IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ T : Finset (Fin n), IsVertexCover G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  suffices h : ∀ m : ℕ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.card = m →
      (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) →
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty →
      ∀ C : Circuit, PEqualNP.TopForm.IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ T : Finset (Fin n), IsVertexCover G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 by
    intro G _ hb h4 hne C hC hfun
    exact h G.edgeFinset.card G rfl hb h4 hne C hC hfun
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro G _ hm hb h4 hne C hC hfun
    by_cases htwo : 2 ≤ G.edgeFinset.card
    · obtain ⟨z, hz, hpeel⟩ := hp n G hb h4 htwo
      obtain ⟨D, hD, hDfun, hsave, hbonus⟩ := hpeel C hC hfun
      let H := G.deleteEdges (G.incidenceSet z)
      have hDfun' : circuitFun n D = graphFun H ∅ := by
        funext x
        simpa [graphFun, H] using congrFun hDfun x
      have heq : H.edgeFinset.card + G.degree z = G.edgeFinset.card := cut_edge_card n G z
      by_cases hH : H.edgeFinset.Nonempty
      · have hlt : H.edgeFinset.card < m := by omega
        obtain ⟨S, hS, hScost⟩ := ih H.edgeFinset.card hlt H rfl
          (cut_bipartite G z hb) (cut_no_four_cycle G z h4) hH D hD hDfun'
        by_cases hex : ∃ T : Finset (Fin n), IsVertexCover G T ∧ T.card ≤ S.card
        · obtain ⟨T, hT, hTS⟩ := hex
          exact ⟨T, hT, by omega⟩
        · have hdrop : ∀ T : Finset (Fin n), IsVertexCover G T → S.card < T.card := by
            intro T hT
            by_contra hn
            exact hex ⟨T, hT, by omega⟩
          have hmore := hbonus ⟨S, hS, hdrop⟩
          refine ⟨insert z S, cover_insert_of_cut_cover G z S hS, ?_⟩
          have := Finset.card_insert_le z S
          omega
      · have hHe : H.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
        have hcover : IsVertexCover G {z} := by
          intro u v huv
          by_cases hu : u = z
          · exact Or.inl (by simp [hu])
          by_cases hv : v = z
          · exact Or.inr (by simp [hv])
          have hh : H.Adj u v := (cut_adj G z u v).mpr ⟨huv, hu, hv⟩
          have hm : s(u, v) ∈ H.edgeFinset := by simpa using hh
          simp [hHe] at hm
        refine ⟨{z}, hcover, ?_⟩
        have hzero : H.edgeFinset.card = 0 := by simp [hHe]
        simp only [Finset.card_singleton]
        omega
    · have hm1 : G.edgeFinset.card = 1 := by
        have := Finset.card_pos.mpr hne
        omega
      obtain ⟨T, hT, hTc⟩ := one_edge_cover G hm1
      have := graph_circuit_size_pos G hne C hfun
      exact ⟨T, hT, by omega⟩


theorem not_peeling_of_small_circuit (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hb : ∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v)
    (h4 : PEqualNP.TopForm.NoFourCycle G) (hne : G.edgeFinset.Nonempty)
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅)
    (k : ℕ) (hcover : ∀ T : Finset (Fin n), IsVertexCover G T → k ≤ T.card)
    (hsmall : C.size + 1 < G.edgeFinset.card + k) : ¬ PeelStatement := by
  intro hp
  obtain ⟨T, hT, hsize⟩ := lower_bound_of_peeling hp n G hb h4 hne C hC hfun
  have := hcover T hT
  omega

end PEqualNP.Outside.L_meta_3566
