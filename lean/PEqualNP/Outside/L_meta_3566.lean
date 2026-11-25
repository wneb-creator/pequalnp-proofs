import PEqualNP.Defs
import Mathlib.Algebra.Free

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

namespace PEqualNP.Outside.L_meta_3566.Absorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.LeafStep.Pruning

lemma erase_alias_family (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range C.size) (s : ℕ)
    (hs : ∀ j ∈ J, s < n + j)
    (heq : ∀ j ∈ J, ∀ x : Fin n → Bool,
      wireVal n C (n + j) x = wireVal n C s x) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + J.card ≤ C.size := by
  classical
  by_cases ho : C.output < n + C.size
  · let K := Finset.range C.size \ J
    let red : ℕ → Src n ℕ := fun w =>
      if n ≤ w ∧ w - n ∈ J then srcOf n s else srcOf n w
    let P : Prog n ℕ := progOf C fun i b => red (opnd C i b)
    let v : ℕ → (Fin n → Bool) → Bool := fun i x => gateVal n C i x
    have hmem (i : ℕ) (hi : i < C.size) (b : Fin 2) :
        opnd C i b ∈ (gateAt C i).inputs := by
      have hg : gateAt C i ∈ C.gates :=
        FalseRestrict.list_getD_mem C.gates i _ hi
      have hlen := hC.2.2 _ hg
      obtain ⟨a, d, h⟩ := List.length_eq_two.mp hlen
      fin_cases b <;> simp [opnd, h]
    have hred (w j : ℕ) (hw : w < n + C.size)
        (h : red w = some (Sum.inr j)) : j ∈ K := by
      dsimp [red] at h
      split_ifs at h with hcase
      · have hj := srcOf_inr s j h
        have hsj := hs (w - n) hcase.2
        have hwj : w - n < C.size := Finset.mem_range.mp (hJ hcase.2)
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
        intro hjJ
        have hlt := hs j hjJ
        omega
      · have hj := srcOf_inr w j h
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
        intro hjJ
        apply hcase
        refine ⟨by omega, ?_⟩
        have hsub : w - n = j := by omega
        simpa only [hsub] using hjJ
    have hcl : Closed P id K := by
      intro i hi b j h
      have hi' : i < C.size := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
      have hb := hC.2.1 i hi' (opnd C i b) (hmem i hi' b)
      change red (opnd C i b) = some (Sum.inr j) at h
      refine ⟨hred _ j (by omega) h, ?_⟩
      dsimp [red] at h
      split_ifs at h with hcase
      · have hj := srcOf_inr s j h
        have hsj := hs (opnd C i b - n) hcase.2
        change j < i
        omega
      · have hj := srcOf_inr (opnd C i b) j h
        change j < i
        omega
    have hval (w : ℕ) (x : Fin n → Bool) :
        srcAt x (fun j => v j x) (red w) = wireVal n C w x := by
      dsimp [red, v]
      split_ifs with hcase
      · rw [srcAt_srcOf]
        have hw : n + (w - n) = w := by omega
        simpa only [hw] using (heq (w - n) hcase.2 x).symm
      · exact srcAt_srcOf C w x
    have hsol : Sol P K v := by
      intro x i hi
      have hi' : i < C.size := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
      change gateVal n C i x = opv (isA (gateAt C i).op)
        (srcAt x (fun j => v j x) (red (opnd C i 0)))
        (srcAt x (fun j => v j x) (red (opnd C i 1)))
      rw [hval, hval]
      exact gate_eq C hC i hi' x
    have hout : ∀ j, red C.output = some (Sum.inr j) → j ∈ K :=
      fun j h => hred C.output j ho h
    obtain ⟨D, hD, hsize, hfun⟩ := fold_total P id v K hcl hsol (red C.output) hout
    have hcard : K.card + J.card = C.size := by
      simpa [K] using Finset.card_sdiff_add_card_eq_card hJ
    have hkept : (kept P v K).card ≤ K.card := Finset.card_filter_le _ _
    refine ⟨D, hD, ?_, by omega⟩
    funext x
    rw [hfun x, hval]
    rfl
  · refine ⟨⟨[], n⟩, zero_ao n, ?_, ?_⟩
    · funext x
      rw [zero_fun]
      have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
        rw [SharedRewrite.wires_eq_foldl, SharedRewrite.foldl_stepWire_length]
        simp [Circuit.size]
      change false = (C.wires (List.ofFn x)).getD C.output false
      rw [List.getD_eq_default _ _ (by omega)]
    · have hcard := Finset.card_le_card hJ
      simpa [Circuit.size] using hcard

end PEqualNP.Outside.L_meta_3566.Absorption

namespace PEqualNP.Outside.L_meta_3566.LeafStep.Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

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

end PEqualNP.Outside.L_meta_3566.LeafStep.Pruning

namespace PEqualNP.Outside.L_meta_3566.JunkNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma junk_card_le_sdiff_of_gate_transport {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (f : Fin D.size → Fin C.size)
    (hf : Function.Injective f)
    (hAnd : ∀ i, (gateAt D i.val).op = GateOp.and →
      (gateAt C (f i).val).op = GateOp.and)
    (hTrue : ∀ i x, graphFun G ∅ x = false → gateVal n D i.val x = true →
      gateVal n C (f i).val x = true)
    (J : Finset ℕ) (hAvoid : ∀ i, (f i).val ∉ J) :
    (junk G D).card ≤ (junk G C \ J).card := by
  classical
  let idx : {k // k ∈ junk G D} → Fin D.size :=
    fun k => ⟨k.val, ((mem_junk_iff G D k.val).mp k.property).1⟩
  let F : {k // k ∈ junk G D} → {k // k ∈ junk G C \ J} := fun k =>
    ⟨(f (idx k)).val, Finset.mem_sdiff.mpr ⟨by
      obtain ⟨_, hop, x, hv, hFalse⟩ := (mem_junk_iff G D k.val).mp k.property
      exact (mem_junk_iff G C _).mpr
        ⟨(f (idx k)).isLt, hAnd (idx k) hop, x, hTrue (idx k) x hFalse hv, hFalse⟩,
      hAvoid (idx k)⟩⟩
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    have h : f (idx a) = f (idx b) := Fin.ext (congrArg Subtype.val hab)
    exact congrArg Fin.val (hf h)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F hF

lemma junk_card_add_discarded_le_of_gate_transport {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (f : Fin D.size → Fin C.size)
    (hf : Function.Injective f)
    (hAnd : ∀ i, (gateAt D i.val).op = GateOp.and →
      (gateAt C (f i).val).op = GateOp.and)
    (hTrue : ∀ i x, graphFun G ∅ x = false → gateVal n D i.val x = true →
      gateVal n C (f i).val x = true)
    (J : Finset ℕ) (hAvoid : ∀ i, (f i).val ∉ J) :
    (junk G D).card + (junk G C ∩ J).card ≤ (junk G C).card := by
  have h := junk_card_le_sdiff_of_gate_transport G C D f hf hAnd hTrue J hAvoid
  have hcard := Finset.card_sdiff_add_card_inter (junk G C) J
  omega

lemma junk_card_le_of_gate_transport {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (f : Fin D.size → Fin C.size)
    (hf : Function.Injective f)
    (hAnd : ∀ i, (gateAt D i.val).op = GateOp.and →
      (gateAt C (f i).val).op = GateOp.and)
    (hTrue : ∀ i x, graphFun G ∅ x = false → gateVal n D i.val x = true →
      gateVal n C (f i).val x = true) :
    (junk G D).card ≤ (junk G C).card := by
  simpa using junk_card_le_sdiff_of_gate_transport G C D f hf hAnd hTrue ∅ (by simp)

lemma junk_card_le_of_gate_embedding {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (f : Fin D.size → Fin C.size)
    (hf : Function.Injective f)
    (hOp : ∀ i, (gateAt D i.val).op = (gateAt C (f i).val).op)
    (hVal : ∀ i x, gateVal n D i.val x = gateVal n C (f i).val x) :
    (junk G D).card ≤ (junk G C).card := by
  apply junk_card_le_of_gate_transport G C D f hf
  · intro i hi
    exact (hOp i).symm.trans hi
  · intro i x _ hi
    exact (hVal i x).symm.trans hi

lemma junk_card_add_discarded_le_of_gate_embedding {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (f : Fin D.size → Fin C.size)
    (hf : Function.Injective f)
    (hOp : ∀ i, (gateAt D i.val).op = (gateAt C (f i).val).op)
    (hVal : ∀ i x, gateVal n D i.val x = gateVal n C (f i).val x)
    (J : Finset ℕ) (hAvoid : ∀ i, (f i).val ∉ J) :
    (junk G D).card + (junk G C ∩ J).card ≤ (junk G C).card := by
  apply junk_card_add_discarded_le_of_gate_transport G C D f hf ?_ ?_ J hAvoid
  · intro i hi
    exact (hOp i).symm.trans hi
  · intro i x _ hi
    exact (hVal i x).symm.trans hi

end PEqualNP.Outside.L_meta_3566.JunkNormalize

namespace PEqualNP.Outside.L_meta_3566.Absorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.LeafStep.Pruning

lemma erase_alias_family_with_junk_credit (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsAO2 n C)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range C.size) (s : ℕ)
    (hs : ∀ j ∈ J, s < n + j)
    (heq : ∀ j ∈ J, ∀ x : Fin n → Bool,
      wireVal n C (n + j) x = wireVal n C s x) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + J.card ≤ C.size ∧
      (junk G D).card + (junk G C ∩ J).card ≤ (junk G C).card := by
  classical
  by_cases ho : C.output < n + C.size
  · let K := Finset.range C.size \ J
    let red : ℕ → Src n ℕ := fun w =>
      if n ≤ w ∧ w - n ∈ J then srcOf n s else srcOf n w
    let P : Prog n ℕ := progOf C fun i b => red (opnd C i b)
    let v : ℕ → (Fin n → Bool) → Bool := fun i x => gateVal n C i x
    have hmem (i : ℕ) (hi : i < C.size) (b : Fin 2) :
        opnd C i b ∈ (gateAt C i).inputs := by
      have hg : gateAt C i ∈ C.gates :=
        FalseRestrict.list_getD_mem C.gates i _ hi
      have hlen := hC.2.2 _ hg
      obtain ⟨a, d, h⟩ := List.length_eq_two.mp hlen
      fin_cases b <;> simp [opnd, h]
    have hred (w j : ℕ) (hw : w < n + C.size)
        (h : red w = some (Sum.inr j)) : j ∈ K := by
      dsimp [red] at h
      split_ifs at h with hcase
      · have hj := srcOf_inr s j h
        have hsj := hs (w - n) hcase.2
        have hwj : w - n < C.size := Finset.mem_range.mp (hJ hcase.2)
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
        intro hjJ
        have hlt := hs j hjJ
        omega
      · have hj := srcOf_inr w j h
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
        intro hjJ
        apply hcase
        refine ⟨by omega, ?_⟩
        have hsub : w - n = j := by omega
        simpa only [hsub] using hjJ
    have hcl : Closed P id K := by
      intro i hi b j h
      have hi' : i < C.size := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
      have hb := hC.2.1 i hi' (opnd C i b) (hmem i hi' b)
      change red (opnd C i b) = some (Sum.inr j) at h
      refine ⟨hred _ j (by omega) h, ?_⟩
      dsimp [red] at h
      split_ifs at h with hcase
      · have hj := srcOf_inr s j h
        have hsj := hs (opnd C i b - n) hcase.2
        change j < i
        omega
      · have hj := srcOf_inr (opnd C i b) j h
        change j < i
        omega
    have hval (w : ℕ) (x : Fin n → Bool) :
        srcAt x (fun j => v j x) (red w) = wireVal n C w x := by
      dsimp [red, v]
      split_ifs with hcase
      · rw [srcAt_srcOf]
        have hw : n + (w - n) = w := by omega
        simpa only [hw] using (heq (w - n) hcase.2 x).symm
      · exact srcAt_srcOf C w x
    have hsol : Sol P K v := by
      intro x i hi
      have hi' : i < C.size := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
      change gateVal n C i x = opv (isA (gateAt C i).op)
        (srcAt x (fun j => v j x) (red (opnd C i 0)))
        (srcAt x (fun j => v j x) (red (opnd C i 1)))
      rw [hval, hval]
      exact gate_eq C hC i hi' x
    have hout : ∀ j, red C.output = some (Sum.inr j) → j ∈ K :=
      fun j h => hred C.output j ho h
    obtain ⟨D, hD, hsize, hfun, htrace⟩ :=
      fold_total_with_trace P id v K hcl hsol (red C.output) hout
    have hcard : K.card + J.card = C.size := by
      simpa [K] using Finset.card_sdiff_add_card_eq_card hJ
    have hkept : (kept P v K).card ≤ K.card := Finset.card_filter_le _ _
    obtain ⟨f, hf, hfK, hfOp, hfVal⟩ := htrace
    let e : Fin D.size → Fin C.size := fun i =>
      ⟨f i, Finset.mem_range.mp (Finset.mem_sdiff.mp (hfK i)).1⟩
    have he : Function.Injective e := by
      intro i l hil
      exact hf (congrArg Fin.val hil)
    have heOp (i : Fin D.size) : (gateAt D i.val).op = (gateAt C (e i).val).op := by
      have hop := hfOp i
      change (gateAt D i.val).op =
        if isA (gateAt C (f i)).op then GateOp.and else GateOp.or at hop
      rw [hop]
      have hi : f i < C.size := (e i).isLt
      have hiMem : gateAt C (f i) ∈ C.gates :=
        FalseRestrict.list_getD_mem C.gates (f i) _ hi
      rcases hC.1 _ hiMem with ha | ho
      · simp [e, ha, isA]
      · simp [e, ho, isA]
    have heVal (i : Fin D.size) (x : Fin n → Bool) :
        gateVal n D i.val x = gateVal n C (e i).val x := hfVal i x
    have hAvoid (i : Fin D.size) : (e i).val ∉ J :=
      (Finset.mem_sdiff.mp (hfK i)).2
    have hJunk := JunkNormalize.junk_card_add_discarded_le_of_gate_embedding
      G C D e he heOp heVal J hAvoid
    refine ⟨D, hD, ?_, by omega, hJunk⟩
    funext x
    rw [hfun x, hval]
    rfl
  · refine ⟨⟨[], n⟩, zero_ao n, ?_, ?_, ?_⟩
    · funext x
      rw [zero_fun]
      have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
        rw [SharedRewrite.wires_eq_foldl, SharedRewrite.foldl_stepWire_length]
        simp [Circuit.size]
      change false = (C.wires (List.ofFn x)).getD C.output false
      rw [List.getD_eq_default _ _ (by omega)]
    · have hcard := Finset.card_le_card hJ
      simpa [Circuit.size] using hcard
    · have hzero : junk G (⟨[], n⟩ : Circuit) = ∅ := by
        simp [junk, gatesWhere]
      rw [hzero, Finset.card_empty, Nat.zero_add]
      exact Finset.card_le_card Finset.inter_subset_left

lemma erase_alias_family_with_junk (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsAO2 n C)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range C.size) (s : ℕ)
    (hs : ∀ j ∈ J, s < n + j)
    (heq : ∀ j ∈ J, ∀ x : Fin n → Bool,
      wireVal n C (n + j) x = wireVal n C s x) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + J.card ≤ C.size ∧ (junk G D).card ≤ (junk G C).card := by
  obtain ⟨D, hD, hfun, hsize, hJunk⟩ :=
    erase_alias_family_with_junk_credit n G C hC J hJ s hs heq
  exact ⟨D, hD, hfun, hsize, by omega⟩

end PEqualNP.Outside.L_meta_3566.Absorption

namespace PEqualNP.Outside.L_meta_3566.GateWeight

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open scoped BigOperators

lemma sum_add_discarded_le_of_gate_embedding {n : ℕ} (C D : Circuit)
    (f : Fin D.size → Fin C.size) (hf : Function.Injective f)
    (hOp : ∀ i, (gateAt D i.val).op = (gateAt C (f i).val).op)
    (hVal : ∀ i x, gateVal n D i.val x = gateVal n C (f i).val x)
    (J : Finset ℕ) (hAvoid : ∀ i, (f i).val ∉ J)
    (W : GateOp → ((Fin n → Bool) → Bool) → ℕ) :
    (∑ i : Fin D.size, W (gateAt D i.val).op (gateVal n D i.val)) +
      (∑ j : Fin C.size with j.val ∈ J,
        W (gateAt C j.val).op (gateVal n C j.val)) ≤
      ∑ k : Fin C.size, W (gateAt C k.val).op (gateVal n C k.val) := by
  classical
  let w : Fin C.size → ℕ := fun k => W (gateAt C k.val).op (gateVal n C k.val)
  let I : Finset (Fin C.size) := Finset.univ.image f
  let K : Finset (Fin C.size) := Finset.univ.filter fun k => k.val ∈ J
  have hweight (i : Fin D.size) : W (gateAt D i.val).op (gateVal n D i.val) = w (f i) := by
    have hv : gateVal n D i.val = gateVal n C (f i).val := funext (hVal i)
    dsimp [w]
    rw [hOp i, hv]
  have hsum : (∑ i : Fin D.size, W (gateAt D i.val).op (gateVal n D i.val)) =
      ∑ k ∈ I, w k := by
    simp only [hweight]
    exact (Finset.sum_image fun i _ j _ h => hf h).symm
  have hd : Disjoint I K := by
    apply Finset.disjoint_left.mpr
    intro k hk hK
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    exact hAvoid i (Finset.mem_filter.mp hK).2
  rw [hsum]
  change (∑ k ∈ I, w k) + (∑ k ∈ K, w k) ≤ ∑ k : Fin C.size, w k
  rw [← Finset.sum_union hd]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma sum_le_of_gate_embedding {n : ℕ} (C D : Circuit)
    (f : Fin D.size → Fin C.size) (hf : Function.Injective f)
    (hOp : ∀ i, (gateAt D i.val).op = (gateAt C (f i).val).op)
    (hVal : ∀ i x, gateVal n D i.val x = gateVal n C (f i).val x)
    (W : GateOp → ((Fin n → Bool) → Bool) → ℕ) :
    (∑ i : Fin D.size, W (gateAt D i.val).op (gateVal n D i.val)) ≤
      ∑ k : Fin C.size, W (gateAt C k.val).op (gateVal n C k.val) := by
  simpa using sum_add_discarded_le_of_gate_embedding C D f hf hOp hVal ∅ (by simp) W

end PEqualNP.Outside.L_meta_3566.GateWeight

namespace PEqualNP.Outside.L_meta_3566.Absorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.LeafStep.Pruning

lemma erase_alias_family_with_embedding (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range C.size) (s : ℕ)
    (hs : ∀ j ∈ J, s < n + j)
    (heq : ∀ j ∈ J, ∀ x : Fin n → Bool,
      wireVal n C (n + j) x = wireVal n C s x) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + J.card ≤ C.size ∧
      ∃ f : Fin D.size → Fin C.size, Function.Injective f ∧
        (∀ i, (f i).val ∉ J) ∧
        (∀ i, (gateAt D i.val).op = (gateAt C (f i).val).op) ∧
        ∀ i x, gateVal n D i.val x = gateVal n C (f i).val x := by
  classical
  by_cases ho : C.output < n + C.size
  · let K := Finset.range C.size \ J
    let red : ℕ → Src n ℕ := fun w =>
      if n ≤ w ∧ w - n ∈ J then srcOf n s else srcOf n w
    let P : Prog n ℕ := progOf C fun i b => red (opnd C i b)
    let v : ℕ → (Fin n → Bool) → Bool := fun i x => gateVal n C i x
    have hmem (i : ℕ) (hi : i < C.size) (b : Fin 2) :
        opnd C i b ∈ (gateAt C i).inputs := by
      have hg : gateAt C i ∈ C.gates :=
        FalseRestrict.list_getD_mem C.gates i _ hi
      have hlen := hC.2.2 _ hg
      obtain ⟨a, d, h⟩ := List.length_eq_two.mp hlen
      fin_cases b <;> simp [opnd, h]
    have hred (w j : ℕ) (hw : w < n + C.size)
        (h : red w = some (Sum.inr j)) : j ∈ K := by
      dsimp [red] at h
      split_ifs at h with hcase
      · have hj := srcOf_inr s j h
        have hsj := hs (w - n) hcase.2
        have hwj : w - n < C.size := Finset.mem_range.mp (hJ hcase.2)
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
        intro hjJ
        have hlt := hs j hjJ
        omega
      · have hj := srcOf_inr w j h
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
        intro hjJ
        apply hcase
        refine ⟨by omega, ?_⟩
        have hsub : w - n = j := by omega
        simpa only [hsub] using hjJ
    have hcl : Closed P id K := by
      intro i hi b j h
      have hi' : i < C.size := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
      have hb := hC.2.1 i hi' (opnd C i b) (hmem i hi' b)
      change red (opnd C i b) = some (Sum.inr j) at h
      refine ⟨hred _ j (by omega) h, ?_⟩
      dsimp [red] at h
      split_ifs at h with hcase
      · have hj := srcOf_inr s j h
        have hsj := hs (opnd C i b - n) hcase.2
        change j < i
        omega
      · have hj := srcOf_inr (opnd C i b) j h
        change j < i
        omega
    have hval (w : ℕ) (x : Fin n → Bool) :
        srcAt x (fun j => v j x) (red w) = wireVal n C w x := by
      dsimp [red, v]
      split_ifs with hcase
      · rw [srcAt_srcOf]
        have hw : n + (w - n) = w := by omega
        simpa only [hw] using (heq (w - n) hcase.2 x).symm
      · exact srcAt_srcOf C w x
    have hsol : Sol P K v := by
      intro x i hi
      have hi' : i < C.size := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
      change gateVal n C i x = opv (isA (gateAt C i).op)
        (srcAt x (fun j => v j x) (red (opnd C i 0)))
        (srcAt x (fun j => v j x) (red (opnd C i 1)))
      rw [hval, hval]
      exact gate_eq C hC i hi' x
    have hout : ∀ j, red C.output = some (Sum.inr j) → j ∈ K :=
      fun j h => hred C.output j ho h
    obtain ⟨D, hD, hsize, hfun, htrace⟩ :=
      fold_total_with_trace P id v K hcl hsol (red C.output) hout
    have hcard : K.card + J.card = C.size := by
      simpa [K] using Finset.card_sdiff_add_card_eq_card hJ
    have hkept : (kept P v K).card ≤ K.card := Finset.card_filter_le _ _
    obtain ⟨f, hf, hfK, hfOp, hfVal⟩ := htrace
    let e : Fin D.size → Fin C.size := fun i =>
      ⟨f i, Finset.mem_range.mp (Finset.mem_sdiff.mp (hfK i)).1⟩
    have he : Function.Injective e := by
      intro i l hil
      exact hf (congrArg Fin.val hil)
    have heOp (i : Fin D.size) : (gateAt D i.val).op = (gateAt C (e i).val).op := by
      have hop := hfOp i
      change (gateAt D i.val).op =
        if isA (gateAt C (f i)).op then GateOp.and else GateOp.or at hop
      rw [hop]
      have hi : f i < C.size := (e i).isLt
      have hiMem : gateAt C (f i) ∈ C.gates :=
        FalseRestrict.list_getD_mem C.gates (f i) _ hi
      rcases hC.1 _ hiMem with ha | ho
      · simp [e, ha, isA]
      · simp [e, ho, isA]
    have heVal (i : Fin D.size) (x : Fin n → Bool) :
        gateVal n D i.val x = gateVal n C (e i).val x := hfVal i x
    have hAvoid (i : Fin D.size) : (e i).val ∉ J :=
      (Finset.mem_sdiff.mp (hfK i)).2
    refine ⟨D, hD, ?_, by omega, e, he, hAvoid, heOp, heVal⟩
    funext x
    rw [hfun x, hval]
    rfl
  · refine ⟨⟨[], n⟩, zero_ao n, ?_, ?_, ?_⟩
    · funext x
      rw [zero_fun]
      have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
        rw [SharedRewrite.wires_eq_foldl, SharedRewrite.foldl_stepWire_length]
        simp [Circuit.size]
      change false = (C.wires (List.ofFn x)).getD C.output false
      rw [List.getD_eq_default _ _ (by omega)]
    · have hcard := Finset.card_le_card hJ
      simpa [Circuit.size] using hcard
    · refine ⟨Fin.elim0, ?_, ?_, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i

end PEqualNP.Outside.L_meta_3566.Absorption

namespace PEqualNP.Outside.L_meta_3566.Absorption

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open scoped BigOperators

lemma erase_alias_family_with_weights (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range C.size) (s : ℕ)
    (hs : ∀ j ∈ J, s < n + j)
    (heq : ∀ j ∈ J, ∀ x : Fin n → Bool,
      wireVal n C (n + j) x = wireVal n C s x) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + J.card ≤ C.size ∧
      ∀ W : GateOp → ((Fin n → Bool) → Bool) → ℕ,
        (∑ i : Fin D.size, W (gateAt D i.val).op (gateVal n D i.val)) +
          (∑ j : Fin C.size with j.val ∈ J,
            W (gateAt C j.val).op (gateVal n C j.val)) ≤
          ∑ k : Fin C.size, W (gateAt C k.val).op (gateVal n C k.val) := by
  obtain ⟨D, hD, hFun, hSize, f, hf, hAvoid, hOp, hVal⟩ :=
    erase_alias_family_with_embedding n C hC J hJ s hs heq
  exact ⟨D, hD, hFun, hSize,
    fun W => GateWeight.sum_add_discarded_le_of_gate_embedding C D f hf hOp hVal J hAvoid W⟩

end PEqualNP.Outside.L_meta_3566.Absorption

namespace PEqualNP.Outside.L_meta_3566.JunkPivotal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma correct_of_pivotal_cover_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hFun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgop : g.op = GateOp.and ∨ g.op = GateOp.or) (hglen : g.inputs.length = 2)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hPos : ∀ a b : Fin n, G.Adj a b → pivotal C j a b →
      g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn (pairInput a b))).getD i false) = true)
    (hLe : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) ≤
        (C.wires (List.ofFn x)).getD (n + j) false) :
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
    have ht := Bool.le_iff_imp.mp (SharedRewrite.replace_ge n C j hj g hgback hAO.1 x (hLe x)) hx
    rw [hFun] at ht
    exact ht
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

end PEqualNP.Outside.L_meta_3566.JunkPivotal

namespace PEqualNP.Outside.L_meta_3566.InputAlias

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma least_no_input_pivotal_cover {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (j : ℕ) (hj : j < C.size) (u : Fin n)
    (hDown : ∀ x : Fin n → Bool, x u = true → gateVal n C j x = true)
    (hPivot : ∀ a b : Fin n, G.Adj a b → JunkPivotal.pivotal C j a b →
      pairInput a b u = true) : False := by
  let g : Gate := ⟨GateOp.and, [u.val, u.val]⟩
  let D := SharedRewrite.replace C j g
  have hj' : j < C.gates.length := hj
  have hback : ∀ i ∈ g.inputs, i < n + j := by
    intro i hi
    have hi' : i = u.val := by simpa [g] using hi
    subst i
    omega
  have heval (x : Fin n → Bool) :
      g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn x)).getD i false) = x u := by
    simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, Bool.and_self, SharedRewrite.input_val]
  obtain ⟨hD, hfun, hsize⟩ := JunkPivotal.correct_of_pivotal_cover_le G C hC.1 hC.2.1
    j hj' g (Or.inl rfl) rfl hback
    (by intro a b hab hp; rw [heval]; exact hPivot a b hab hp)
    (by intro x; rw [heval]; exact Bool.le_iff_imp.mpr (hDown x))
  have hLeast : IsLeastAO G D := by
    refine ⟨hD, hfun, ?_⟩
    intro E hE hEFun
    rw [hsize]
    exact hC.2.2 E hE hEFun
  have hjD : j < D.size := by
    change j < (SharedRewrite.replace C j g).size
    omega
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


lemma exists_pivotal_edge_avoiding_input {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (j : ℕ) (hj : j < C.size) (u : Fin n)
    (hDown : ∀ x : Fin n → Bool, x u = true → gateVal n C j x = true) :
    ∃ a b : Fin n, G.Adj a b ∧ JunkPivotal.pivotal C j a b ∧
      pairInput a b u = false := by
  classical
  by_contra hnone
  apply least_no_input_pivotal_cover G C hC j hj u hDown
  intro a b hab hp
  apply Bool.eq_true_of_not_eq_false
  intro hu
  exact hnone ⟨a, b, hab, hp, hu⟩

end PEqualNP.Outside.L_meta_3566.InputAlias

namespace PEqualNP.Outside.L_meta_3566.InputAlias

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma exists_pivotal_edge_avoiding_singleton {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (j : ℕ) (hj : j < C.size) (u : Fin n)
    (hu : gateVal n C j (pairInput u u) = true) :
    ∃ a b : Fin n, G.Adj a b ∧ JunkPivotal.pivotal C j a b ∧
      pairInput a b u = false := by
  apply exists_pivotal_edge_avoiding_input G C hC j hj u
  intro x hxu
  apply Bool.le_iff_imp.mp (PureWireSupport.gateVal_monotone n C hC.1.1 j ?_) hu
  intro i
  apply Bool.le_iff_imp.mpr
  intro hi
  have hiu : i = u := by simpa [pairInput] using hi
  simpa [hiu] using hxu

end PEqualNP.Outside.L_meta_3566.InputAlias

namespace PEqualNP.Outside.L_meta_3566.OnePureFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

def orSet {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ S, x a = true)

lemma orSet_pair {n : ℕ} (S : Finset (Fin n)) (a b : Fin n) :
    orSet S (pairInput a b) = true ↔ a ∈ S ∨ b ∈ S := by
  change (decide (∃ u ∈ S, pairInput a b u = true) = true) ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨u, hu, hv⟩
    have h : u = a ∨ u = b := by simpa [pairInput] using hv
    rcases h with rfl | rfl
    · exact Or.inl hu
    · exact Or.inr hu
  · rintro (ha | hb)
    · exact ⟨a, ha, by simp [pairInput]⟩
    · exact ⟨b, hb, by simp [pairInput]⟩

lemma common_center {n : ℕ} {ι : Type*} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hFour : NoFourCycle G)
    (color : Fin n → Bool) (S T : Finset (Fin n))
    (hDisjoint : Disjoint S T) (hMany : 2 ≤ S.card)
    (hLeft : ∀ a ∈ S, color a = false)
    (Q : ι → (Fin n → Bool) → Bool)
    (hPure : ∀ i a b, color a = false → color b = true →
      Q i (pairInput a b) = Q i (pairInput b b))
    (hClean : ∀ i x, (orSet S x && orSet T x && Q i x) = true →
      graphFun G ∅ x = true)
    (E : Fin n → Fin n → Prop) (hNonempty : ∃ a b, E a b)
    (hColor : ∀ a b, E a b → color a = false ∧ color b = true)
    (hOn : ∀ a b, E a b → (orSet S (pairInput a b) && orSet T (pairInput a b)) = true)
    (hCovered : ∀ a b, E a b → ∃ i, Q i (pairInput a b) = true) :
    ∃ z, color z = true ∧ z ∈ T ∧ (∀ a ∈ S, G.Adj a z) ∧
      ∀ a b, E a b → b = z := by
  have center (a b : Fin n) (hab : E a b) : b ∈ T ∧ ∀ u ∈ S, G.Adj u b := by
    obtain ⟨haColor, hbColor⟩ := hColor a b hab
    have hBoth : orSet S (pairInput a b) = true ∧ orSet T (pairInput a b) = true := by
      simpa using hOn a b hab
    have hbNot : b ∉ S := by
      intro hbS
      have h := hLeft b hbS
      rw [hbColor] at h
      exact Bool.noConfusion h
    have haS : a ∈ S := ((orSet_pair S a b).mp hBoth.1).resolve_right hbNot
    have haNot : a ∉ T := fun haT => Finset.disjoint_left.mp hDisjoint haS haT
    have hbT : b ∈ T := ((orSet_pair T a b).mp hBoth.2).resolve_left haNot
    obtain ⟨i, hQi⟩ := hCovered a b hab
    have hQb : Q i (pairInput b b) = true := (hPure i a b haColor hbColor).symm.trans hQi
    refine ⟨hbT, fun u hu => ?_⟩
    have hSu : orSet S (pairInput u b) = true := (orSet_pair S u b).mpr (Or.inl hu)
    have hTu : orSet T (pairInput u b) = true := (orSet_pair T u b).mpr (Or.inr hbT)
    have hQu : Q i (pairInput u b) = true := (hPure i u b (hLeft u hu) hbColor).trans hQb
    have hF := hClean i (pairInput u b) (by simp [hSu, hTu, hQu])
    by_contra hAdj
    rw [SharedExit.graphFun_nonedge_pair G u b hAdj] at hF
    exact Bool.false_ne_true hF
  obtain ⟨a, z, haz⟩ := hNonempty
  obtain ⟨hzT, hzAll⟩ := center a z haz
  refine ⟨z, (hColor a z haz).2, hzT, hzAll, fun u b hub => ?_⟩
  by_contra hbz
  obtain ⟨v, hvS, hNot⟩ := SharedExit.support_has_nonneighbor G hFour z b hbz S hMany
    (fun v hv => (hzAll v hv).symm)
  exact hNot ((center u b hub).2 v hvS).symm

lemma clean_star_of_common_center {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S T : Finset (Fin n)) (z : Fin n)
    (hz : z ∈ T) (hAdj : ∀ a ∈ S, G.Adj a z)
    (E : Fin n → Fin n → Prop)
    (hOn : ∀ a b, E a b → orSet S (pairInput a b) = true)
    (hCenter : ∀ a b, E a b → b = z) :
    (∀ x, (orSet S x && x z) = true → graphFun G ∅ x = true) ∧
    (∀ x, (orSet S x && x z) = true → (orSet S x && orSet T x) = true) ∧
    (∀ a b, E a b → (orSet S (pairInput a b) && pairInput a b z) = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hS, hzOn⟩ : orSet S x = true ∧ x z = true := by simpa using hx
    obtain ⟨a, ha, haOn⟩ : ∃ a ∈ S, x a = true := of_decide_eq_true hS
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨a, z, hAdj a ha, haOn, hzOn⟩
  · intro x hx
    obtain ⟨hS, hzOn⟩ : orSet S x = true ∧ x z = true := by simpa using hx
    have hT : orSet T x = true := by
      exact decide_eq_true (show ∃ a ∈ T, x a = true from ⟨z, hz, hzOn⟩)
    simp [hS, hT]
  · intro a b hab
    have hbz := hCenter a b hab
    simp [hOn a b hab, ← hbz, pairInput]

end PEqualNP.Outside.L_meta_3566.OnePureFrontier

namespace PEqualNP.Outside.L_meta_3566.NegativeMass
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

noncomputable def falseInputs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter fun x => graphFun G ∅ x = false

lemma mem_falseInputs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : x ∈ falseInputs G ↔ graphFun G ∅ x = false := by
  classical
  simp [falseInputs]

end PEqualNP.Outside.L_meta_3566.NegativeMass

namespace PEqualNP.Outside.L_meta_3566.WireMass
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

noncomputable def mass {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : ℕ :=
  ∑ x ∈ NegativeMass.falseInputs G, (C.wires (List.ofFn x)).count true

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

namespace PEqualNP.Outside.L_meta_3566.WirePivotal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma mass_lt_of_clean_replace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : AndOrOnly C) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hClean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
        graphFun G ∅ x = true)
    (hDirty : ∃ x : Fin n → Bool, gateVal n C j x = true ∧ graphFun G ∅ x = false)
    (hNewClean : BelowF G (SharedRewrite.replace C j g) j) :
    WireMass.mass G (SharedRewrite.replace C j g) < WireMass.mass G C := by
  let D := SharedRewrite.replace C j g
  have hlen : D.gates.length = C.gates.length := by simp [D, SharedRewrite.replace]
  apply WireProfile.mass_lt_of_profile G C D id
    (by intro k hk; simpa only [id_eq, hlen] using hk)
    (by intro a ha b hb hab; exact hab)
  · intro x hFalse k hk hOn
    have hzero : g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn x)).getD i false) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have hF := hClean x ht
      rw [hFalse] at hF
      exact Bool.false_ne_true hF
    have hle : gateVal n D k x ≤ gateVal n C k x :=
      SharedRewrite.replace_ge n ⟨C.gates, n + k⟩ j hj g hgback hAO x
        (by change g.op.eval (g.inputs.map fun i =>
              (C.wires (List.ofFn x)).getD i false) ≤ _
            rw [hzero]
            exact Bool.false_le _)
    exact Bool.le_iff_imp.mp hle hOn
  · obtain ⟨x, hOld, hFalse⟩ := hDirty
    refine ⟨x, hFalse, j, by simpa only [hlen] using hj, hOld, ?_⟩
    apply Bool.eq_false_iff.mpr
    intro hNew
    have ht := hNewClean x hNew
    rw [hFalse] at ht
    exact Bool.false_ne_true ht

lemma one_pivotal_edge_not_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (hmin : ∀ D : Circuit, IsLeastAO G D → WireMass.mass G C ≤ WireMass.mass G D)
    (j : ℕ) (hj : j < C.gates.length) (w u : Fin n) (hwu : G.Adj w u)
    (hKeep : ∀ a b : Fin n, G.Adj a b → JunkPivotal.pivotal C j a b →
      (pairInput a b w && pairInput a b u) = true) :
    ¬ ∃ x : Fin n → Bool, gateVal n C j x = true ∧ graphFun G ∅ x = false := by
  intro hDirty
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
  obtain ⟨hD, hFun, hSize⟩ := JunkPivotal.correct_of_pivotal_cover G C hC.1 hC.2.1
    j hj ⟨GateOp.and, [w.val, u.val]⟩ (Or.inl rfl) rfl hBack
    (by intro a b hab hp; rw [hEval]; exact hKeep a b hab hp) hClean
  have hLeast : IsLeastAO G (SharedRewrite.replace C j ⟨GateOp.and, [w.val, u.val]⟩) :=
    ⟨hD, hFun, fun D hD hFunD => hSize.trans_le (hC.2.2 D hD hFunD)⟩
  have hStrict := mass_lt_of_clean_replace G C hC.1.1 j hj
    ⟨GateOp.and, [w.val, u.val]⟩ hBack hClean hDirty
    (JunkNormalize.edge_gate_below G C hC.1 j hj w u hwu)
  have hMin := hmin _ hLeast
  omega

lemma dirty_gate_has_two_pivotal_edges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hE : ∃ w u : Fin n, G.Adj w u)
    (C : Circuit) (hC : IsLeastAO G C)
    (hmin : ∀ D : Circuit, IsLeastAO G D → WireMass.mass G C ≤ WireMass.mass G D)
    (j : ℕ) (hj : j < C.gates.length)
    (hDirty : ∃ x : Fin n → Bool, gateVal n C j x = true ∧ graphFun G ∅ x = false) :
    ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧
      JunkPivotal.pivotal C j a b ∧ JunkPivotal.pivotal C j c d ∧ s(a, b) ≠ s(c, d) := by
  classical
  by_contra hTwo
  by_cases hPivot : ∃ w u : Fin n, G.Adj w u ∧ JunkPivotal.pivotal C j w u
  · obtain ⟨w, u, hwu, hOn⟩ := hPivot
    apply one_pivotal_edge_not_dirty G C hC hmin j hj w u hwu ?_ hDirty
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
    apply one_pivotal_edge_not_dirty G C hC hmin j hj w u hwu ?_ hDirty
    intro a b hab hp
    exact False.elim (hPivot ⟨a, b, hab, hp⟩)

end PEqualNP.Outside.L_meta_3566.WirePivotal

namespace PEqualNP.Outside.L_meta_3566.SharedRewrite

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

lemma replace_gateVal (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (g : Gate) (hgback : ∀ i ∈ g.inputs, i < n + j) (x : Fin n → Bool) :
    gateVal n (replace C j g) j x =
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
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
  rw [hm]
  change ((replace C j g).wires (List.ofFn x)).getD (n + j) false = _
  rw [wires_eq_foldl]
  change ((C.gates.set j g).foldl stepWire (List.ofFn x)).getD (n + j) false = _
  rw [List.set_eq_take_cons_drop g hj, htake, hdrop, List.foldl_append, List.foldl_cons,
    foldl_stepWire_getD_lt _ _ _ (by change n + j < (stepWire w0 g).length; simp [stepWire, hw0])]
  rw [← hw0, stepWire_getD_len]

end PEqualNP.Outside.L_meta_3566.SharedRewrite

namespace PEqualNP.Outside.L_meta_3566.JunkPivotal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma not_dirty_of_clean_pivotal_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgop : g.op = GateOp.and ∨ g.op = GateOp.or) (hglen : g.inputs.length = 2)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hPos : ∀ a b : Fin n, G.Adj a b → pivotal C j a b →
      g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn (pairInput a b))).getD i false) = true)
    (hClean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
        graphFun G ∅ x = true) : j ∉ junk G C := by
  intro hDirty
  obtain ⟨hD, hFun, hSize⟩ := correct_of_pivotal_cover G C hC.1.1 hC.1.2.1
    j hj g hgop hglen hgback hPos hClean
  have hLeast : IsLeastAO G (SharedRewrite.replace C j g) :=
    ⟨hD, hFun, fun D hD hFunD => hSize.trans_le (hC.1.2.2 D hD hFunD)⟩
  have hNewClean : BelowF G (SharedRewrite.replace C j g) j := by
    intro x hx
    rw [SharedRewrite.replace_gateVal n C j hj g hgback x] at hx
    exact hClean x hx
  have hStrict := JunkNormalize.junk_card_lt_of_clean_replace_any_op G C hC.1.1.1
    j hj g hgback hClean hDirty hNewClean
  have hMin := hC.2 _ hLeast
  omega

end PEqualNP.Outside.L_meta_3566.JunkPivotal

namespace PEqualNP.Outside.L_meta_3566.OnePureFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma wire_not_dirty {n : ℕ} {ι : Type*} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hFour : NoFourCycle G)
    (color : Fin n → Bool) (S T : Finset (Fin n))
    (hDisjoint : Disjoint S T) (hMany : 2 ≤ S.card)
    (hLeft : ∀ a ∈ S, color a = false)
    (Q : ι → (Fin n → Bool) → Bool)
    (hPure : ∀ i a b, color a = false → color b = true →
      Q i (pairInput a b) = Q i (pairInput b b))
    (hClean : ∀ i x, (orSet S x && orSet T x && Q i x) = true →
      graphFun G ∅ x = true)
    (E : Fin n → Fin n → Prop) (hNonempty : ∃ a b, E a b)
    (hColor : ∀ a b, E a b → color a = false ∧ color b = true)
    (hOn : ∀ a b, E a b → (orSet S (pairInput a b) && orSet T (pairInput a b)) = true)
    (hCovered : ∀ a b, E a b → ∃ i, Q i (pairInput a b) = true)
    (C : Circuit) (hC : JunkMinimum.IsJunkLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (r : ℕ) (hr : r < n + j)
    (hR : ∀ x, wireVal n C r x = orSet S x)
    (hPivCovered : ∀ a b, G.Adj a b → JunkPivotal.pivotal C j a b → E a b ∨ E b a) :
    j ∉ junk G C := by
  obtain ⟨z, _, hzT, hAdj, hCenter⟩ := common_center G hFour color S T hDisjoint hMany hLeft
    Q hPure hClean E hNonempty hColor hOn hCovered
  have hStar := clean_star_of_common_center G S T z hzT hAdj E
    (by
      intro a b h
      have hBoth : orSet S (pairInput a b) = true ∧ orSet T (pairInput a b) = true := by
        simpa using hOn a b h
      exact hBoth.1) hCenter
  have hBack : ∀ i ∈ [r, z.val], i < n + j := by
    intro i hi
    simp at hi
    rcases hi with rfl | rfl
    · exact hr
    · omega
  have hEval : ∀ x : Fin n → Bool,
      GateOp.and.eval ([r, z.val].map fun i =>
        (C.wires (List.ofFn x)).getD i false) = (orSet S x && x z) := by
    intro x
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    rw [SharedRewrite.input_val]
    change (wireVal n C r x && x z) = _
    rw [hR]
  apply JunkPivotal.not_dirty_of_clean_pivotal_gate G C hC j hj
    ⟨GateOp.and, [r, z.val]⟩ (Or.inl rfl) rfl hBack
  · intro a b hab hp
    rw [hEval]
    rcases hPivCovered a b hab hp with hE | hE
    · exact hStar.2.2 a b hE
    · have hSwap : pairInput a b = pairInput b a := by
        funext i
        simp [pairInput, or_comm]
      rw [hSwap]
      exact hStar.2.2 b a hE
  · intro x hx
    rw [hEval] at hx
    exact hStar.1 x hx

end PEqualNP.Outside.L_meta_3566.OnePureFrontier

namespace PEqualNP.Outside.L_meta_3566.InputAlias

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma least_no_earlier_wire_pivotal_cover {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (j : ℕ) (hj : j < C.size) (r : ℕ) (hr : r < n + j)
    (hDown : ∀ x : Fin n → Bool, wireVal n C r x = true → gateVal n C j x = true)
    (hPivot : ∀ a b : Fin n, G.Adj a b → JunkPivotal.pivotal C j a b →
      wireVal n C r (pairInput a b) = true) : False := by
  let g : Gate := ⟨GateOp.and, [r, r]⟩
  let D := SharedRewrite.replace C j g
  have hj' : j < C.gates.length := hj
  have hback : ∀ i ∈ g.inputs, i < n + j := by
    intro i hi
    have hi' : i = r := by simpa [g] using hi
    simpa only [hi'] using hr
  have heval (x : Fin n → Bool) :
      g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn x)).getD i false) = wireVal n C r x := by
    simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, Bool.and_self, wireVal]
  obtain ⟨hD, hfun, hsize⟩ := JunkPivotal.correct_of_pivotal_cover_le G C hC.1 hC.2.1
    j hj' g (Or.inl rfl) rfl hback
    (by intro a b hab hp; rw [heval]; exact hPivot a b hab hp)
    (by intro x; rw [heval]; exact Bool.le_iff_imp.mpr (hDown x))
  have hLeast : IsLeastAO G D := by
    refine ⟨hD, hfun, ?_⟩
    intro E hE hEFun
    rw [hsize]
    exact hC.2.2 E hE hEFun
  have hjD : j < D.size := by
    change j < (SharedRewrite.replace C j g).size
    omega
  have hjD' : j < D.gates.length := hjD
  have hgate : gateAt D j = g := by
    simp [D, SharedRewrite.replace_gateAt C j g hj' j]
  have ho : D.output < n + D.size :=
    least_output_bound_of_gate G D hLeast j hjD
  apply Absorption.least_no_equivalent n G D hLeast j r hjD hr ho
  intro x
  have heq := LeafStep.Pruning.gate_eq D hD j hjD' x
  simp only [hgate, g, LeafStep.Pruning.isA, LeafStep.Pruning.opv, opnd] at heq
  change gateVal n D j x = (wireVal n D r x && wireVal n D r x) at heq
  simpa only [gateVal, wireVal, Bool.and_self] using heq

lemma exists_pivotal_edge_avoiding_wire {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (j : ℕ) (hj : j < C.size) (r : ℕ) (hr : r < n + j)
    (hDown : ∀ x : Fin n → Bool, wireVal n C r x = true → gateVal n C j x = true) :
    ∃ a b : Fin n, G.Adj a b ∧ JunkPivotal.pivotal C j a b ∧
      wireVal n C r (pairInput a b) = false := by
  classical
  by_contra hnone
  apply least_no_earlier_wire_pivotal_cover G C hC j hj r hr hDown
  intro a b hab hp
  apply Bool.eq_true_of_not_eq_false
  intro hu
  exact hnone ⟨a, b, hab, hp, hu⟩

end PEqualNP.Outside.L_meta_3566.InputAlias

namespace PEqualNP.Outside.L_meta_3566.InputAlias

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma or_pivotal_opposite_operands {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (j : ℕ) (hj : j < C.size) (hOr : (gateAt C j).op = GateOp.or) :
    ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧
      JunkPivotal.pivotal C j a b ∧ JunkPivotal.pivotal C j c d ∧
      wireVal n C (opnd C j 0) (pairInput a b) = false ∧
      wireVal n C (opnd C j 1) (pairInput a b) = true ∧
      wireVal n C (opnd C j 0) (pairInput c d) = true ∧
      wireVal n C (opnd C j 1) (pairInput c d) = false := by
  have hmem (b : Fin 2) : opnd C j b ∈ (gateAt C j).inputs := by
    have hg : gateAt C j ∈ C.gates :=
      FalseRestrict.list_getD_mem C.gates j _ hj
    obtain ⟨r, s, hrs⟩ := List.length_eq_two.mp (hC.1.2.2 _ hg)
    fin_cases b <;> simp [opnd, hrs]
  have hback (b : Fin 2) : opnd C j b < n + j :=
    hC.1.2.1 j hj _ (hmem b)
  have hgate (x : Fin n → Bool) : gateVal n C j x =
      (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
    rw [LeafStep.Pruning.gate_eq C hC.1 j hj x, hOr]
    rfl
  obtain ⟨a, b, hab, hpab, h0⟩ := exists_pivotal_edge_avoiding_wire G C hC j hj
    (opnd C j 0) (hback 0) (by intro x hx; rw [hgate x, hx]; rfl)
  obtain ⟨c, d, hcd, hpcd, h1⟩ := exists_pivotal_edge_avoiding_wire G C hC j hj
    (opnd C j 1) (hback 1) (by intro x hx; rw [hgate x, hx]; exact Bool.or_true _)
  have hab1 : wireVal n C (opnd C j 1) (pairInput a b) = true := by
    have ht := JunkPivotal.pivotal_on G C hC.1 hC.2.1 j hj a b hab hpab
    rw [hgate, h0] at ht
    exact ht
  have hcd0 : wireVal n C (opnd C j 0) (pairInput c d) = true := by
    have ht := JunkPivotal.pivotal_on G C hC.1 hC.2.1 j hj c d hcd hpcd
    rw [hgate, h1, Bool.or_false] at ht
    exact ht
  exact ⟨a, b, c, d, hab, hcd, hpab, hpcd, h0, hab1, hcd0, h1⟩

lemma or_has_two_pivotal_edges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsLeastAO G C)
    (j : ℕ) (hj : j < C.size) (hOr : (gateAt C j).op = GateOp.or) :
    ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧
      JunkPivotal.pivotal C j a b ∧ JunkPivotal.pivotal C j c d ∧ s(a, b) ≠ s(c, d) := by
  obtain ⟨a, b, c, d, hab, hcd, hpab, hpcd, h0, _, hc0, _⟩ :=
    or_pivotal_opposite_operands G C hC j hj hOr
  refine ⟨a, b, c, d, hab, hcd, hpab, hpcd, ?_⟩
  intro heq
  have hpair : pairInput a b = pairInput c d := by
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · funext x
      simp [pairInput, or_comm]
  rw [hpair] at h0
  exact Bool.false_ne_true (h0.symm.trans hc0)

end PEqualNP.Outside.L_meta_3566.InputAlias

namespace PEqualNP.Outside.L_meta_3566.MonoNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

def input {n : ℕ} (color : Fin n → Bool) (b : Bool) : Fin n → Bool :=
  fun v => decide (color v = b)

def mass {n : ℕ} (color : Fin n → Bool) (C : Circuit) : ℕ :=
  (C.wires (List.ofFn (input color false))).count true +
    (C.wires (List.ofFn (input color true))).count true

def IsMonoJunkLeastAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (C : Circuit) : Prop :=
  IsLeastAO G C ∧ (∀ D : Circuit, IsLeastAO G D → mass color C ≤ mass color D) ∧
    ∀ D : Circuit, IsLeastAO G D → mass color D = mass color C →
      (junk G C).card ≤ (junk G D).card

def IsMonoJunkWireLeastAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (C : Circuit) : Prop :=
  IsMonoJunkLeastAO G color C ∧
    ∀ D : Circuit, IsLeastAO G D → mass color D = mass color C →
      (junk G D).card = (junk G C).card → WireMass.mass G C ≤ WireMass.mass G D

lemma exists_mono_junk_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (C0 : Circuit) (hC0 : IsLeastAO G C0) :
    ∃ C : Circuit, IsMonoJunkLeastAO G color C := by
  classical
  have hm : ∃ k : ℕ, ∃ C : Circuit, IsLeastAO G C ∧ mass color C = k :=
    ⟨mass color C0, C0, hC0, rfl⟩
  obtain ⟨C1, hC1, hMass1⟩ := Nat.find_spec hm
  have hMin1 : ∀ D : Circuit, IsLeastAO G D → mass color C1 ≤ mass color D := by
    intro D hD
    rw [hMass1]
    exact Nat.find_min' hm ⟨D, hD, rfl⟩
  have hj : ∃ k : ℕ, ∃ C : Circuit, IsLeastAO G C ∧ mass color C = mass color C1 ∧
      (junk G C).card = k := ⟨(junk G C1).card, C1, hC1, rfl, rfl⟩
  obtain ⟨C, hC, hMass, hJunk⟩ := Nat.find_spec hj
  refine ⟨C, hC, ?_, ?_⟩
  · intro D hD
    rw [hMass]
    exact hMin1 D hD
  · intro D hD hDMass
    rw [hJunk]
    exact Nat.find_min' hj ⟨D, hD, hDMass.trans hMass, rfl⟩

lemma exists_mono_junk_wire_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (C0 : Circuit) (hC0 : IsLeastAO G C0) :
    ∃ C : Circuit, IsMonoJunkWireLeastAO G color C := by
  classical
  obtain ⟨C1, hC1⟩ := exists_mono_junk_least G color C0 hC0
  have hw : ∃ k : ℕ, ∃ C : Circuit, IsLeastAO G C ∧ mass color C = mass color C1 ∧
      (junk G C).card = (junk G C1).card ∧ WireMass.mass G C = k :=
    ⟨WireMass.mass G C1, C1, hC1.1, rfl, rfl, rfl⟩
  obtain ⟨C, hC, hMass, hJunk, hWire⟩ := Nat.find_spec hw
  refine ⟨C, ⟨hC, ?_, ?_⟩, ?_⟩
  · intro D hD
    rw [hMass]
    exact hC1.2.1 D hD
  · intro D hD hDMass
    rw [hJunk]
    exact hC1.2.2 D hD (hDMass.trans hMass)
  · intro D hD hDMass hDJunk
    rw [hWire]
    exact Nat.find_min' hw ⟨D, hD, hDMass.trans hMass, hDJunk.trans hJunk, rfl⟩

lemma exists_mono_junk_wire_least_of_edges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool) (hE : G.edgeFinset.Nonempty) :
    ∃ C : Circuit, IsMonoJunkWireLeastAO G color C := by
  obtain ⟨C, hC⟩ := PEqualNP.Outside.L_meta_3566.exists_least_ao G hE
  exact exists_mono_junk_wire_least G color C hC

lemma input_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hBip : ∀ a b, G.Adj a b → color a ≠ color b)
    (b : Bool) : graphFun G ∅ (input color b) = false := by
  apply Bool.eq_false_iff.mpr
  intro hF
  have hEdge : ∃ u v : Fin n, G.Adj u v ∧ input color b u = true ∧
      input color b v = true := by simpa [graphFun] using hF
  obtain ⟨u, v, huv, hu, hv⟩ := hEdge
  have huColor : color u = b := of_decide_eq_true hu
  have hvColor : color v = b := of_decide_eq_true hv
  exact hBip u v huv (huColor.trans hvColor.symm)

lemma mass_le_of_clean_replace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hBip : ∀ a b, G.Adj a b → color a ≠ color b)
    (C : Circuit) (hAO : AndOrOnly C) (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hClean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
        graphFun G ∅ x = true) :
    mass color (SharedRewrite.replace C j g) ≤ mass color C := by
  let D := SharedRewrite.replace C j g
  have hlen : D.gates.length = C.gates.length := by simp [D, SharedRewrite.replace]
  have hCount (b : Bool) : (D.wires (List.ofFn (input color b))).count true ≤
      (C.wires (List.ofFn (input color b))).count true := by
    apply WireProfile.wire_count_le C D id
      (by intro k hk; simpa only [id_eq, hlen] using hk)
      (by intro a ha b hb hab; exact hab)
    intro k hk hOn
    have hzero : g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn (input color b))).getD i false) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have hF := hClean (input color b) ht
      rw [input_false G color hBip b] at hF
      exact Bool.false_ne_true hF
    have hle : gateVal n D k (input color b) ≤ gateVal n C k (input color b) :=
      SharedRewrite.replace_ge n ⟨C.gates, n + k⟩ j hj g hgback hAO (input color b)
        (by change g.op.eval (g.inputs.map fun i =>
              (C.wires (List.ofFn (input color b))).getD i false) ≤ _
            rw [hzero]
            exact Bool.false_le _)
    exact Bool.le_iff_imp.mp hle hOn
  exact Nat.add_le_add (hCount false) (hCount true)

lemma not_dirty_of_clean_pivotal_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hBip : ∀ a b, G.Adj a b → color a ≠ color b)
    (C : Circuit) (hC : IsMonoJunkLeastAO G color C)
    (j : ℕ) (hj : j < C.gates.length) (g : Gate)
    (hgop : g.op = GateOp.and ∨ g.op = GateOp.or) (hglen : g.inputs.length = 2)
    (hgback : ∀ i ∈ g.inputs, i < n + j)
    (hPos : ∀ a b : Fin n, G.Adj a b → JunkPivotal.pivotal C j a b →
      g.op.eval (g.inputs.map fun i =>
        (C.wires (List.ofFn (pairInput a b))).getD i false) = true)
    (hClean : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) = true →
        graphFun G ∅ x = true) : j ∉ junk G C := by
  intro hDirty
  obtain ⟨hD, hFun, hSize⟩ := JunkPivotal.correct_of_pivotal_cover G C hC.1.1 hC.1.2.1
    j hj g hgop hglen hgback hPos hClean
  have hLeast : IsLeastAO G (SharedRewrite.replace C j g) :=
    ⟨hD, hFun, fun D hD hFunD => hSize.trans_le (hC.1.2.2 D hD hFunD)⟩
  have hNewClean : BelowF G (SharedRewrite.replace C j g) j := by
    intro x hx
    rw [SharedRewrite.replace_gateVal n C j hj g hgback x] at hx
    exact hClean x hx
  have hMass := mass_le_of_clean_replace G color hBip C hC.1.1.1 j hj g hgback hClean
  have hMassEq : mass color (SharedRewrite.replace C j g) = mass color C :=
    Nat.le_antisymm hMass (hC.2.1 _ hLeast)
  have hStrict := JunkNormalize.junk_card_lt_of_clean_replace_any_op G C hC.1.1.1
    j hj g hgback hClean hDirty hNewClean
  have hMin := hC.2.2 _ hLeast hMassEq
  omega

lemma one_pivotal_edge_not_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hBip : ∀ a b, G.Adj a b → color a ≠ color b)
    (C : Circuit) (hC : IsMonoJunkLeastAO G color C)
    (j : ℕ) (hj : j < C.gates.length) (w u : Fin n) (hwu : G.Adj w u)
    (hKeep : ∀ a b : Fin n, G.Adj a b → JunkPivotal.pivotal C j a b →
      (pairInput a b w && pairInput a b u) = true) : j ∉ junk G C := by
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
  apply not_dirty_of_clean_pivotal_gate G color hBip C hC j hj
    ⟨GateOp.and, [w.val, u.val]⟩ (Or.inl rfl) rfl hBack
  · intro a b hab hp
    rw [hEval]
    exact hKeep a b hab hp
  · intro x hx
    rw [hEval] at hx
    have hx' : x w = true ∧ x u = true := by simpa using hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨w, u, hwu, hx'.1, hx'.2⟩

lemma dirty_has_two_pivotal_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hBip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hE : ∃ w u : Fin n, G.Adj w u)
    (C : Circuit) (hC : IsMonoJunkLeastAO G color C)
    (j : ℕ) (hDirty : j ∈ junk G C) :
    ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧
      JunkPivotal.pivotal C j a b ∧ JunkPivotal.pivotal C j c d ∧ s(a, b) ≠ s(c, d) := by
  classical
  have hj := ((JunkNormalize.mem_junk_iff G C j).mp hDirty).1
  by_contra hTwo
  by_cases hPivot : ∃ w u : Fin n, G.Adj w u ∧ JunkPivotal.pivotal C j w u
  · obtain ⟨w, u, hwu, hOn⟩ := hPivot
    apply one_pivotal_edge_not_dirty G color hBip C hC j hj w u hwu ?_ hDirty
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
    apply one_pivotal_edge_not_dirty G color hBip C hC j hj w u hwu ?_ hDirty
    intro a b hab hp
    exact False.elim (hPivot ⟨a, b, hab, hp⟩)

lemma exists_normalized_two_pivotal {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hBip : ∀ a b, G.Adj a b → color a ≠ color b) (hE : G.edgeFinset.Nonempty) :
    ∃ C : Circuit, IsMonoJunkWireLeastAO G color C ∧
      ∀ j ∈ junk G C, ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧
        JunkPivotal.pivotal C j a b ∧ JunkPivotal.pivotal C j c d ∧ s(a, b) ≠ s(c, d) := by
  obtain ⟨C, hC⟩ := exists_mono_junk_wire_least_of_edges G color hE
  have hEdges : ∃ a b : Fin n, G.Adj a b := by
    obtain ⟨e, he⟩ := hE
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    exact ⟨a, b, by simpa using he⟩
  exact ⟨C, hC, fun j hj => dirty_has_two_pivotal_edges G color hBip hEdges C hC.1 j hj⟩

end PEqualNP.Outside.L_meta_3566.MonoNormalize

namespace PEqualNP.Outside.L_meta_3566.OnePureFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma wire_not_dirty_mono {n : ℕ} {ι : Type*} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hFour : NoFourCycle G)
    (color : Fin n → Bool) (hBip : ∀ a b, G.Adj a b → color a ≠ color b)
    (S T : Finset (Fin n))
    (hDisjoint : Disjoint S T) (hMany : 2 ≤ S.card)
    (hLeft : ∀ a ∈ S, color a = false)
    (Q : ι → (Fin n → Bool) → Bool)
    (hPure : ∀ i a b, color a = false → color b = true →
      Q i (pairInput a b) = Q i (pairInput b b))
    (hClean : ∀ i x, (orSet S x && orSet T x && Q i x) = true →
      graphFun G ∅ x = true)
    (E : Fin n → Fin n → Prop) (hNonempty : ∃ a b, E a b)
    (hColor : ∀ a b, E a b → color a = false ∧ color b = true)
    (hOn : ∀ a b, E a b → (orSet S (pairInput a b) && orSet T (pairInput a b)) = true)
    (hCovered : ∀ a b, E a b → ∃ i, Q i (pairInput a b) = true)
    (C : Circuit) (hC : MonoNormalize.IsMonoJunkLeastAO G color C)
    (j : ℕ) (hj : j < C.gates.length) (r : ℕ) (hr : r < n + j)
    (hR : ∀ x, wireVal n C r x = orSet S x)
    (hPivCovered : ∀ a b, G.Adj a b → JunkPivotal.pivotal C j a b → E a b ∨ E b a) :
    j ∉ junk G C := by
  obtain ⟨z, _, hzT, hAdj, hCenter⟩ := common_center G hFour color S T hDisjoint hMany hLeft
    Q hPure hClean E hNonempty hColor hOn hCovered
  have hStar := clean_star_of_common_center G S T z hzT hAdj E
    (by
      intro a b h
      have hBoth : orSet S (pairInput a b) = true ∧ orSet T (pairInput a b) = true := by
        simpa using hOn a b h
      exact hBoth.1) hCenter
  have hBack : ∀ i ∈ [r, z.val], i < n + j := by
    intro i hi
    simp at hi
    rcases hi with rfl | rfl
    · exact hr
    · omega
  have hEval : ∀ x : Fin n → Bool,
      GateOp.and.eval ([r, z.val].map fun i =>
        (C.wires (List.ofFn x)).getD i false) = (orSet S x && x z) := by
    intro x
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    rw [SharedRewrite.input_val]
    change (wireVal n C r x && x z) = _
    rw [hR]
  apply MonoNormalize.not_dirty_of_clean_pivotal_gate G color hBip C hC j hj
    ⟨GateOp.and, [r, z.val]⟩ (Or.inl rfl) rfl hBack
  · intro a b hab hp
    rw [hEval]
    rcases hPivCovered a b hab hp with hE | hE
    · exact hStar.2.2 a b hE
    · have hSwap : pairInput a b = pairInput b a := by
        funext i
        simp [pairInput, or_comm]
      rw [hSwap]
      exact hStar.2.2 b a hE
  · intro x hx
    rw [hEval] at hx
    exact hStar.1 x hx

end PEqualNP.Outside.L_meta_3566.OnePureFrontier

namespace PEqualNP.Outside.L_meta_3566.MonoNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma mass_eq_of_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (C : Circuit) (hC : IsMonoJunkLeastAO G color C)
    (D : Circuit) (hD : IsLeastAO G D) (hMass : mass color D ≤ mass color C) :
    mass color D = mass color C := Nat.le_antisymm hMass (hC.2.1 D hD)

lemma junk_eq_of_earlier_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (C : Circuit) (hC : IsMonoJunkLeastAO G color C)
    (D : Circuit) (hD : IsLeastAO G D) (hMass : mass color D ≤ mass color C)
    (hJunk : (junk G D).card ≤ (junk G C).card) :
    (junk G D).card = (junk G C).card := by
  exact Nat.le_antisymm hJunk (hC.2.2 D hD (mass_eq_of_le G color C hC D hD hMass))

lemma wire_mass_le_of_earlier_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (C : Circuit) (hC : IsMonoJunkWireLeastAO G color C)
    (D : Circuit) (hD : IsLeastAO G D) (hMass : mass color D ≤ mass color C)
    (hJunk : (junk G D).card ≤ (junk G C).card) :
    WireMass.mass G C ≤ WireMass.mass G D :=
  hC.2 D hD (mass_eq_of_le G color C hC.1 D hD hMass)
    (junk_eq_of_earlier_le G color C hC.1 D hD hMass hJunk)

lemma of_competitor_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (C : Circuit) (hC : IsMonoJunkWireLeastAO G color C)
    (D : Circuit) (hD : IsLeastAO G D) (hMass : mass color D ≤ mass color C)
    (hJunk : (junk G D).card ≤ (junk G C).card)
    (hWire : WireMass.mass G D ≤ WireMass.mass G C) :
    IsMonoJunkWireLeastAO G color D := by
  have hm := mass_eq_of_le G color C hC.1 D hD hMass
  have hj := junk_eq_of_earlier_le G color C hC.1 D hD hMass hJunk
  refine ⟨⟨hD, ?_, ?_⟩, ?_⟩
  · intro E hE
    rw [hm]
    exact hC.1.2.1 E hE
  · intro E hE hEMass
    rw [hj]
    exact hC.1.2.2 E hE (hEMass.trans hm)
  · intro E hE hEMass hEJunk
    exact hWire.trans (hC.2 E hE (hEMass.trans hm) (hEJunk.trans hj))

end PEqualNP.Outside.L_meta_3566.MonoNormalize

namespace PEqualNP.Outside.L_meta_3566.PrivateCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma input_card_le_gates_of_extra_read (n : ℕ) (K : Finset ℕ) (r : ℕ) (hr : r ∈ K)
    (port : ℕ → Fin 2 → ℕ) (S : Finset (Fin n))
    (hInputs : ∀ v ∈ S, ∃ g ∈ K, ∃ b : Fin 2, port g b = v.val)
    (hRead : ∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, port h b = n + g)
    (w : ℕ) (hW : ∃ g ∈ K, ∃ b : Fin 2, port g b = w)
    (hWInput : ∀ v ∈ S, w ≠ v.val)
    (hWGate : ∀ g ∈ K.erase r, w ≠ n + g) : S.card ≤ K.card := by
  classical
  let slots := K ×ˢ (Finset.univ : Finset (Fin 2))
  let I := slots.image (fun p => port p.1 p.2)
  let A := S.image (fun v : Fin n => v.val)
  let B := (K.erase r).image (fun g : ℕ => n + g)
  have hA : A ⊆ I := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨g, hg, b, hb⟩ := hInputs u hu
    exact Finset.mem_image.mpr ⟨(g, b), Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩, hb⟩
  have hB : B ⊆ I := by
    intro v hv
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨h, hh, b, hb⟩ := hRead g hg
    exact Finset.mem_image.mpr ⟨(h, b), Finset.mem_product.mpr ⟨hh, Finset.mem_univ _⟩, hb⟩
  have hwI : w ∈ I := by
    obtain ⟨g, hg, b, hb⟩ := hW
    exact Finset.mem_image.mpr ⟨(g, b), Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩, hb⟩
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwB
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hwA
    obtain ⟨g, _, hg⟩ := Finset.mem_image.mp hwB
    have := v.isLt
    omega
  have hwNot : w ∉ A ∪ B := by
    intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hw
      exact hWInput v hv heq.symm
    · obtain ⟨g, hg, heq⟩ := Finset.mem_image.mp hw
      exact hWGate g hg heq.symm
  have hCount := Finset.card_le_card (Finset.insert_subset hwI (Finset.union_subset hA hB))
  rw [Finset.card_insert_of_notMem hwNot, Finset.card_union_of_disjoint hAB] at hCount
  have hAc : A.card = S.card := Finset.card_image_of_injective _ Fin.val_injective
  have hBc : B.card = (K.erase r).card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  have hPorts : slots.card = K.card * 2 := by simp [slots]
  have hImage : I.card ≤ slots.card := Finset.card_image_le
  have hErase := Finset.card_erase_of_mem hr
  have hPos := Finset.card_pos.mpr ⟨r, hr⟩
  omega

lemma or_gate_true_of_port (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.size) (hOp : (gateAt C j).op = GateOp.or)
    (x : Fin n → Bool) (b : Fin 2) (hOn : wireVal n C (opnd C j b) x = true) :
    gateVal n C j x = true := by
  rw [LeafStep.Pruning.gate_eq C hC j hj x, hOp]
  fin_cases b
  · have h : wireVal n C (opnd C j 0) x = true := hOn
    simp [LeafStep.Pruning.isA, LeafStep.Pruning.opv, h]
  · have h : wireVal n C (opnd C j 1) x = true := hOn
    simp [LeafStep.Pruning.isA, LeafStep.Pruning.opv, h]

lemma exists_active_false_port (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (K : Finset ℕ) (r : ℕ) (hK : ∀ j ∈ K, j < C.size)
    (hRead : ∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, opnd C h b = n + g)
    (x : Fin n → Bool) (hrOn : gateVal n C r x = true)
    (hOff : ∃ g ∈ K, ∃ b : Fin 2, wireVal n C (opnd C g b) x = false) :
    ∃ g ∈ K, gateVal n C g x = true ∧
      ∃ b : Fin 2, wireVal n C (opnd C g b) x = false := by
  classical
  obtain ⟨g, hg, b, hb⟩ := hOff
  by_cases hgOn : gateVal n C g x = true
  · exact ⟨g, hg, hgOn, b, hb⟩
  · let F := K.filter fun j => gateVal n C j x = false
    have hF : F.Nonempty := ⟨g, Finset.mem_filter.mpr ⟨hg, Bool.eq_false_iff.mpr hgOn⟩⟩
    let j := F.max' hF
    have hjF : j ∈ F := Finset.max'_mem F hF
    obtain ⟨hjK, hjOff⟩ := Finset.mem_filter.mp hjF
    have hjr : j ≠ r := by
      intro h
      rw [h, hrOn] at hjOff
      exact Bool.noConfusion hjOff
    obtain ⟨k, hk, c, hc⟩ := hRead j (Finset.mem_erase.mpr ⟨hjr, hjK⟩)
    have hback := hC.2.1 k (hK k hk) (opnd C k c) (port_mem n C hC k (hK k hk) c)
    have hjk : j < k := by rw [hc] at hback; omega
    have hkOn : gateVal n C k x = true := by
      apply Bool.eq_true_of_not_eq_false
      intro hkOff
      have hkF : k ∈ F := Finset.mem_filter.mpr ⟨hk, hkOff⟩
      have hle : k ≤ j := Finset.le_max' F k hkF
      omega
    refine ⟨k, hk, hkOn, c, ?_⟩
    rw [hc]
    exact hjOff

lemma input_card_le_active_or_gates (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (K : Finset ℕ) (r : ℕ) (hr : r ∈ K) (hK : ∀ j ∈ K, j < C.size)
    (hOr : ∀ j ∈ K, (gateAt C j).op = GateOp.or)
    (hRead : ∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, opnd C h b = n + g)
    (x : Fin n → Bool) (hrOn : gateVal n C r x = true)
    (S : Finset (Fin n)) (hSOn : ∀ v ∈ S, x v = true)
    (hInputs : ∀ v ∈ S, ∃ g ∈ K, ∃ b : Fin 2, opnd C g b = v.val)
    (hOff : ∃ g ∈ K, ∃ b : Fin 2, wireVal n C (opnd C g b) x = false) :
    S.card ≤ (K.filter fun j => gateVal n C j x = true).card := by
  classical
  let A := K.filter fun j => gateVal n C j x = true
  have hrA : r ∈ A := Finset.mem_filter.mpr ⟨hr, hrOn⟩
  have hInputsA : ∀ v ∈ S, ∃ g ∈ A, ∃ b : Fin 2, opnd C g b = v.val := by
    intro v hv
    obtain ⟨g, hg, b, hb⟩ := hInputs v hv
    have hOn : wireVal n C (opnd C g b) x = true := by
      rw [hb, LeafStep.Pruning.wireVal_lt C v.val v.isLt x]
      exact hSOn v hv
    exact ⟨g, Finset.mem_filter.mpr ⟨hg, or_gate_true_of_port n C hC g (hK g hg) (hOr g hg) x b hOn⟩,
      b, hb⟩
  have hReadA : ∀ g ∈ A.erase r, ∃ h ∈ A, ∃ b : Fin 2, opnd C h b = n + g := by
    intro g hg
    obtain ⟨hgr, hgA⟩ := Finset.mem_erase.mp hg
    obtain ⟨hgK, hgOn⟩ := Finset.mem_filter.mp hgA
    obtain ⟨k, hk, b, hb⟩ := hRead g (Finset.mem_erase.mpr ⟨hgr, hgK⟩)
    have hOn : wireVal n C (opnd C k b) x = true := by rw [hb]; exact hgOn
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, or_gate_true_of_port n C hC k (hK k hk) (hOr k hk) x b hOn⟩,
      b, hb⟩
  obtain ⟨g, hg, hgOn, b, hbOff⟩ := exists_active_false_port n C hC K r hK hRead x hrOn hOff
  apply input_card_le_gates_of_extra_read n A r hrA (opnd C) S hInputsA hReadA (opnd C g b)
    ⟨g, Finset.mem_filter.mpr ⟨hg, hgOn⟩, b, rfl⟩
  · intro v hv heq
    have hTrue : wireVal n C (opnd C g b) x = true := by
      rw [heq, LeafStep.Pruning.wireVal_lt C v.val v.isLt x]
      exact hSOn v hv
    rw [hbOff] at hTrue
    exact Bool.false_ne_true hTrue
  · intro k hk heq
    have hkOn := (Finset.mem_filter.mp (Finset.mem_erase.mp hk).2).2
    have hTrue : wireVal n C (opnd C g b) x = true := by rw [heq]; exact hkOn
    rw [hbOff] at hTrue
    exact Bool.false_ne_true hTrue

end PEqualNP.Outside.L_meta_3566.PrivateCone

namespace PEqualNP.Outside.L_meta_3566.PrivateCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma root_true_of_gate_true (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (K : Finset ℕ) (r : ℕ) (hK : ∀ j ∈ K, j < C.size)
    (hOr : ∀ j ∈ K, (gateAt C j).op = GateOp.or)
    (hRead : ∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, opnd C h b = n + g)
    (x : Fin n → Bool) (g : ℕ) (hg : g ∈ K) (hgOn : gateVal n C g x = true) :
    gateVal n C r x = true := by
  classical
  by_contra hrOff
  let A := K.filter fun j => gateVal n C j x = true
  have hA : A.Nonempty := ⟨g, Finset.mem_filter.mpr ⟨hg, hgOn⟩⟩
  let j := A.max' hA
  have hjA : j ∈ A := Finset.max'_mem A hA
  obtain ⟨hjK, hjOn⟩ := Finset.mem_filter.mp hjA
  have hjr : j ≠ r := by
    intro h
    exact hrOff (h ▸ hjOn)
  obtain ⟨k, hk, b, hb⟩ := hRead j (Finset.mem_erase.mpr ⟨hjr, hjK⟩)
  have hback := hC.2.1 k (hK k hk) (opnd C k b) (port_mem n C hC k (hK k hk) b)
  have hjk : j < k := by rw [hb] at hback; omega
  have hkOn : gateVal n C k x = true :=
    or_gate_true_of_port n C hC k (hK k hk) (hOr k hk) x b (by rw [hb]; exact hjOn)
  have hkA : k ∈ A := Finset.mem_filter.mpr ⟨hk, hkOn⟩
  have hle : k ≤ j := Finset.le_max' A k hkA
  omega

lemma monochrome_support_card_le_active_gates (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (K : Finset ℕ) (r : ℕ) (hr : r ∈ K) (hK : ∀ j ∈ K, j < C.size)
    (hOr : ∀ j ∈ K, (gateAt C j).op = GateOp.or)
    (hRead : ∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, opnd C h b = n + g)
    (S : Finset (Fin n))
    (hInputs : ∀ v ∈ S, ∃ g ∈ K, ∃ b : Fin 2, opnd C g b = v.val)
    (color : Fin n → Bool) (hBoth : ∀ b : Bool, ∃ v ∈ S, color v = b) (b : Bool) :
    (S.filter fun v => color v = b).card ≤
      (K.filter fun j => gateVal n C j (MonoNormalize.input color b) = true).card := by
  classical
  obtain ⟨v, hvS, hvColor⟩ := hBoth b
  obtain ⟨g, hg, c, hc⟩ := hInputs v hvS
  have hOn : wireVal n C (opnd C g c) (MonoNormalize.input color b) = true := by
    rw [hc, LeafStep.Pruning.wireVal_lt C v.val v.isLt]
    simp [MonoNormalize.input, hvColor]
  have hgOn := or_gate_true_of_port n C hC g (hK g hg) (hOr g hg) _ c hOn
  have hrOn := root_true_of_gate_true n C hC K r hK hOr hRead _ g hg hgOn
  apply input_card_le_active_or_gates n C hC K r hr hK hOr hRead
    (MonoNormalize.input color b) hrOn (S.filter fun v => color v = b)
  · intro u hu
    exact decide_eq_true (Finset.mem_filter.mp hu).2
  · intro u hu
    exact hInputs u (Finset.mem_filter.mp hu).1
  · obtain ⟨u, huS, huColor⟩ := hBoth (!b)
    obtain ⟨k, hk, d, hd⟩ := hInputs u huS
    refine ⟨k, hk, d, ?_⟩
    rw [hd, LeafStep.Pruning.wireVal_lt C u.val u.isLt]
    have hne : color u ≠ b := by rw [huColor]; cases b <;> decide
    simp [MonoNormalize.input, hne]

end PEqualNP.Outside.L_meta_3566.PrivateCone

namespace PEqualNP.Outside.L_meta_3566.PrivateCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma closed_or_cone_value (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (K : Finset ℕ) (r : ℕ) (hr : r ∈ K) (hK : ∀ j ∈ K, j < C.size)
    (hOr : ∀ j ∈ K, (gateAt C j).op = GateOp.or)
    (hClosed : ∀ j ∈ K, ∀ b : Fin 2, n ≤ opnd C j b → opnd C j b - n ∈ K)
    (hRead : ∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, opnd C h b = n + g)
    (S : Finset (Fin n))
    (hInputs : ∀ v ∈ S, ∃ g ∈ K, ∃ b : Fin 2, opnd C g b = v.val)
    (hAllInputs : ∀ j ∈ K, ∀ b : Fin 2, ∀ hw : opnd C j b < n,
      (⟨opnd C j b, hw⟩ : Fin n) ∈ S)
    (x : Fin n → Bool) : gateVal n C r x = OnePureFrontier.orSet S x := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hRoot
    by_contra hNo
    have hZero : ∀ v ∈ S, x v = false := by
      intro v hv
      apply Bool.eq_false_iff.mpr
      intro hvOn
      exact hNo (decide_eq_true (show ∃ u ∈ S, x u = true from ⟨v, hv, hvOn⟩))
    have heq := cone_agree n C hC K hK hClosed S hAllInputs x (fun _ => false) hZero r hr
    rw [heq, gate_zero n C hC r (hK r hr)] at hRoot
    exact Bool.false_ne_true hRoot
  · intro hSet
    obtain ⟨v, hv, hvOn⟩ : ∃ v ∈ S, x v = true := of_decide_eq_true hSet
    obtain ⟨g, hg, b, hb⟩ := hInputs v hv
    have hPort : wireVal n C (opnd C g b) x = true := by
      rw [hb, LeafStep.Pruning.wireVal_lt C v.val v.isLt x]
      exact hvOn
    have hgOn := or_gate_true_of_port n C hC g (hK g hg) (hOr g hg) x b hPort
    exact root_true_of_gate_true n C hC K r hK hOr hRead x g hg hgOn

end PEqualNP.Outside.L_meta_3566.PrivateCone

namespace PEqualNP.Outside.L_meta_3566.MonoNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open scoped BigOperators

def gateWeight {n : ℕ} (color : Fin n → Bool) (_op : GateOp)
    (f : (Fin n → Bool) → Bool) : ℕ :=
  (if f (input color false) then 1 else 0) + (if f (input color true) then 1 else 0)

lemma trueGates_card_eq_sum {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (WireProfile.trueGates C x).card =
      ∑ j : Fin C.size, if gateVal n C j.val x then 1 else 0 := by
  classical
  have h := Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if gateVal n C j x then (1 : ℕ) else 0) C.size
  rw [h]
  simp [WireProfile.trueGates, Circuit.size]

lemma mono_input_count {n : ℕ} (color : Fin n → Bool) :
    (List.ofFn (input color false)).count true +
      (List.ofFn (input color true)).count true = n := by
  rw [WireProfile.list_count_true, WireProfile.list_count_true]
  simp only [List.length_ofFn]
  rw [← Finset.sum_add_distrib]
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      (if (List.ofFn (input color false)).getD j false then 1 else 0) +
        (if (List.ofFn (input color true)).getD j false then 1 else 0) = 1 := by
    have hlt : j < n := Finset.mem_range.mp hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte,
      Option.getD_some, input]
    cases color ⟨j, hlt⟩ <;> decide
  simp_rw [Finset.sum_congr rfl hterm]
  simp

lemma mass_eq_input_add_gateWeight {n : ℕ} (color : Fin n → Bool) (C : Circuit) :
    mass color C = n + ∑ j : Fin C.size,
      gateWeight color (gateAt C j.val).op (gateVal n C j.val) := by
  rw [mass, WireProfile.wire_count, WireProfile.wire_count,
    trueGates_card_eq_sum, trueGates_card_eq_sum]
  simp only [gateWeight, Finset.sum_add_distrib]
  have h := mono_input_count color
  omega

lemma erase_alias_family_with_mono_mass (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range C.size) (s : ℕ)
    (hs : ∀ j ∈ J, s < n + j)
    (heq : ∀ j ∈ J, ∀ x : Fin n → Bool,
      wireVal n C (n + j) x = wireVal n C s x)
    (color : Fin n → Bool) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + J.card ≤ C.size ∧ mass color D ≤ mass color C := by
  obtain ⟨D, hD, hFun, hSize, hWeight⟩ :=
    Absorption.erase_alias_family_with_weights n C hC J hJ s hs heq
  refine ⟨D, hD, hFun, hSize, ?_⟩
  have h := hWeight (gateWeight color)
  rw [mass_eq_input_add_gateWeight, mass_eq_input_add_gateWeight]
  omega

end PEqualNP.Outside.L_meta_3566.MonoNormalize

namespace PEqualNP.Outside.L_meta_3566.AndReassociate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open LeafStep.Pruning

def rotate (n : ℕ) (C : Circuit) (q k U V R : ℕ) : Circuit :=
  SharedRewrite.replace (SharedRewrite.replace C q ⟨GateOp.and, [U, R]⟩)
    k ⟨GateOp.and, [n + q, V]⟩

lemma rotate_correct (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (q k U V R : ℕ) (hqk : q < k) (hk : k < C.size)
    (hU : U < n + q) (hV : V < n + q) (hR : R < n + q)
    (hQ : ∀ x, gateVal n C q x = (wireVal n C U x && wireVal n C V x))
    (hK : ∀ x, gateVal n C k x = (gateVal n C q x && wireVal n C R x))
    (hPrivate : ∀ j < C.size, j ≠ k → n + q ∉ (gateAt C j).inputs)
    (hOutput : C.output ≠ n + q) :
    IsAO2 n (rotate n C q k U V R) ∧ (rotate n C q k U V R).size = C.size ∧
      circuitFun n (rotate n C q k U V R) = circuitFun n C ∧
      (∀ x, gateVal n (rotate n C q k U V R) q x = (wireVal n C U x && wireVal n C R x)) ∧
      ∀ j < C.size, j ≠ q → ∀ x,
        gateVal n (rotate n C q k U V R) j x = gateVal n C j x := by
  have hq : q < C.size := by omega
  let C1 := SharedRewrite.replace C q ⟨GateOp.and, [U, R]⟩
  let D := rotate n C q k U V R
  have hSize1 : C1.size = C.size := SharedRewrite.replace_size C q _
  have hSize : D.size = C.size := by simp [D, rotate, SharedRewrite.replace_size]
  have hAO1 : IsAO2 n C1 := SharedRewrite.replace_ao C hC q hq _ (Or.inl rfl) rfl (by
    intro w hw
    simp at hw
    rcases hw with rfl | rfl <;> assumption)
  have hAO : IsAO2 n D := SharedRewrite.replace_ao C1 hAO1 k (by change k < C1.size; rw [hSize1]; exact hk)
    _ (Or.inl rfl) rfl (by
      intro w hw
      simp at hw
      rcases hw with rfl | rfl <;> omega)
  have hGate (j : ℕ) : gateAt D j =
      if k = j then ⟨GateOp.and, [n + q, V]⟩ else
      if q = j then ⟨GateOp.and, [U, R]⟩ else gateAt C j := by
    change gateAt (SharedRewrite.replace C1 k ⟨GateOp.and, [n + q, V]⟩) j = _
    rw [SharedRewrite.replace_gateAt C1 k _ (by change k < C1.size; rw [hSize1]; exact hk) j]
    dsimp only [C1]
    rw [SharedRewrite.replace_gateAt C q _ hq j]
  have hValues (x : Fin n → Bool) : ∀ j, j < C.size →
      gateVal n D j x = if j = q then (wireVal n C U x && wireVal n C R x)
        else gateVal n C j x := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj
      have hPre (w : ℕ) (hw : w < n + j) : wireVal n D w x =
          if w = n + q then (wireVal n C U x && wireVal n C R x) else wireVal n C w x := by
        by_cases hInput : w < n
        · rw [wireVal_lt D w hInput x, wireVal_lt C w hInput x]
          simp [show w ≠ n + q by omega]
        · have heq : n + (w - n) = w := by omega
          have hidx : w - n < j := by omega
          rw [← heq]
          change gateVal n D (w - n) x =
            if n + (w - n) = n + q then _ else gateVal n C (w - n) x
          simpa using ih (w - n) hidx (by omega)
      by_cases hjq : j = q
      · subst j
        rw [ite_eq_left rfl]
        have hg : gateAt D q = ⟨GateOp.and, [U, R]⟩ := by
          rw [hGate]
          simp [show k ≠ q by omega]
        have he := gate_eq D hAO q (by change q < D.size; rw [hSize]; exact hq) x
        simp only [opnd, hg, isA, opv] at he
        change gateVal n D q x = (wireVal n D U x && wireVal n D R x) at he
        rw [hPre U hU, hPre R hR] at he
        simpa [show U ≠ n + q by omega, show R ≠ n + q by omega] using he
      · rw [ite_eq_right hjq]
        by_cases hjk : j = k
        · subst j
          have hg : gateAt D k = ⟨GateOp.and, [n + q, V]⟩ := by simp [hGate]
          have he := gate_eq D hAO k (by change k < D.size; rw [hSize]; exact hk) x
          simp only [opnd, hg, isA, opv] at he
          change gateVal n D k x = (wireVal n D (n + q) x && wireVal n D V x) at he
          rw [hPre (n + q) (by omega), hPre V (by omega)] at he
          simp only [ite_true, show V ≠ n + q by omega, ite_false] at he
          rw [he, hK x, hQ x]
          simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
        · have hg : gateAt D j = gateAt C j := by simp [hGate, Ne.symm hjk, Ne.symm hjq]
          have hPort (b : Fin 2) : wireVal n D (opnd C j b) x = wireVal n C (opnd C j b) x := by
            have hmem := PrivateCone.port_mem n C hC j hj b
            have hb := hC.2.1 j hj _ hmem
            have hne : opnd C j b ≠ n + q := by
              intro heq
              exact hPrivate j hj hjk (heq ▸ hmem)
            simpa only [hne, ite_false] using hPre (opnd C j b) hb
          have he := gate_eq D hAO j (by change j < D.size; rw [hSize]; exact hj) x
          simp only [opnd, hg] at he
          change gateVal n D j x = opv (isA (gateAt C j).op)
            (wireVal n D (opnd C j 0) x) (wireVal n D (opnd C j 1) x) at he
          rw [hPort 0, hPort 1] at he
          exact he.trans (gate_eq C hC j hj x).symm
  refine ⟨hAO, hSize, ?_, ?_, ?_⟩
  · funext x
    change wireVal n D C.output x = wireVal n C C.output x
    by_cases hoInput : C.output < n
    · rw [wireVal_lt D C.output hoInput x, wireVal_lt C C.output hoInput x]
    · by_cases hoBound : C.output < n + C.size
      · have heq : n + (C.output - n) = C.output := by omega
        rw [← heq]
        change gateVal n D (C.output - n) x = gateVal n C (C.output - n) x
        simpa [show C.output - n ≠ q by omega] using hValues x (C.output - n) (by omega)
      · have hZero (E : Circuit) (hE : E.size = C.size) : wireVal n E C.output x = false := by
          apply SharedRewrite.getD_ge_length
          have hl := SharedRewrite.foldl_stepWire_length E.gates (List.ofFn x)
          change (E.gates.foldl SharedRewrite.stepWire (List.ofFn x)).length ≤ C.output
          rw [hl]
          simp only [List.length_ofFn]
          change n + E.size ≤ C.output
          omega
        rw [hZero D hSize, hZero C rfl]
  · intro x
    simpa using hValues x q hq
  · intro j hj hjq x
    simpa [hjq] using hValues x j hj

lemma clean_triple_pair (a0 b0 r0 a1 b1 r1 : Bool)
    (h0 : (a0 && b0 && r0) = false) (h1 : (a1 && b1 && r1) = false)
    (hq : (a0 && b0) = true ∨ (a1 && b1) = true) :
    ((a0 && r0) = false ∧ (a1 && r1) = false) ∨
      ((b0 && r0) = false ∧ (b1 && r1) = false) := by
  cases a0 <;> cases b0 <;> cases r0 <;> cases a1 <;> cases b1 <;> cases r1 <;> simp_all

end PEqualNP.Outside.L_meta_3566.AndReassociate

namespace PEqualNP.Outside.L_meta_3566.AndReassociate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma mass_lt_of_single_gate_drop (n : ℕ) (color : Fin n → Bool) (C D : Circuit)
    (q : ℕ) (hq : q < C.size) (hSize : D.size = C.size)
    (hEq : ∀ j < C.size, j ≠ q → ∀ x, gateVal n D j x = gateVal n C j x)
    (hZero : ∀ b : Bool, gateVal n D q (MonoNormalize.input color b) = false)
    (hOn : ∃ b : Bool, gateVal n C q (MonoNormalize.input color b) = true) :
    MonoNormalize.mass color D < MonoNormalize.mass color C := by
  have hForward : ∀ j < D.gates.length, id j < C.gates.length := by
    intro j hj
    change j < C.size
    change j < D.size at hj
    omega
  have hInj : Set.InjOn id (Finset.range D.gates.length : Set ℕ) :=
    fun a _ b _ h => h
  have hVal (b : Bool) : ∀ j < D.gates.length,
      gateVal n D j (MonoNormalize.input color b) = true →
        gateVal n C (id j) (MonoNormalize.input color b) = true := by
    intro j hj hTrue
    by_cases hjq : j = q
    · subst j
      rw [hZero b] at hTrue
      exact False.elim (Bool.false_ne_true hTrue)
    · have hjC : j < C.size := hForward j hj
      rw [hEq j hjC hjq] at hTrue
      exact hTrue
  have hCount (b : Bool) := WireProfile.wire_count_le C D id hForward hInj
    (MonoNormalize.input color b) (hVal b)
  obtain ⟨b, hb⟩ := hOn
  have hStrict := WireProfile.wire_count_lt C D id hForward hInj
    (MonoNormalize.input color b) (hVal b) ⟨q, hq, hb, by
      intro j hj hjq
      change j = q at hjq
      subst j
      exact hZero b⟩
  have hFalse := hCount false
  have hTrue := hCount true
  unfold MonoNormalize.mass
  cases b <;> omega

lemma private_product_mono_zero {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hBip : ∀ a b, G.Adj a b → color a ≠ color b)
    (C : Circuit) (hC : MonoNormalize.IsMonoJunkLeastAO G color C)
    (q k A B R : ℕ) (hqk : q < k) (hk : k < C.size)
    (hA : A < n + q) (hB : B < n + q) (hR : R < n + q)
    (hQ : ∀ x, gateVal n C q x = (wireVal n C A x && wireVal n C B x))
    (hK : ∀ x, gateVal n C k x = (gateVal n C q x && wireVal n C R x))
    (hPrivate : ∀ j < C.size, j ≠ k → n + q ∉ (gateAt C j).inputs)
    (hOutput : C.output ≠ n + q) (hClean : BelowF G C k) :
    ∀ b : Bool, gateVal n C q (MonoNormalize.input color b) = false := by
  intro b
  apply Bool.eq_false_iff.mpr
  intro hOn
  have hq : q < C.size := by omega
  have hKZero (c : Bool) : gateVal n C k (MonoNormalize.input color c) = false := by
    apply Bool.eq_false_iff.mpr
    intro hkOn
    have hF := hClean (MonoNormalize.input color c) hkOn
    rw [MonoNormalize.input_false G color hBip c] at hF
    exact Bool.false_ne_true hF
  have hTriple (c : Bool) :
      (wireVal n C A (MonoNormalize.input color c) && wireVal n C B (MonoNormalize.input color c) &&
        wireVal n C R (MonoNormalize.input color c)) = false := by
    have hz := hKZero c
    rw [hK, hQ] at hz
    simpa [Bool.and_assoc] using hz
  have hOldPair :
      (wireVal n C A (MonoNormalize.input color false) && wireVal n C B (MonoNormalize.input color false)) = true ∨
      (wireVal n C A (MonoNormalize.input color true) && wireVal n C B (MonoNormalize.input color true)) = true := by
    rw [hQ] at hOn
    cases b
    · exact Or.inl hOn
    · exact Or.inr hOn
  have hPair := clean_triple_pair
    (wireVal n C A (MonoNormalize.input color false)) (wireVal n C B (MonoNormalize.input color false))
    (wireVal n C R (MonoNormalize.input color false)) (wireVal n C A (MonoNormalize.input color true))
    (wireVal n C B (MonoNormalize.input color true)) (wireVal n C R (MonoNormalize.input color true))
    (hTriple false) (hTriple true) hOldPair
  have hNoRotation (U V : ℕ) (hU : U < n + q) (hV : V < n + q)
      (hQ' : ∀ x, gateVal n C q x = (wireVal n C U x && wireVal n C V x))
      (hZero : ∀ c : Bool,
        (wireVal n C U (MonoNormalize.input color c) && wireVal n C R (MonoNormalize.input color c)) = false) :
      False := by
    obtain ⟨hD, hSize, hFun, hNewQ, hEq⟩ :=
      rotate_correct n C hC.1.1 q k U V R hqk hk hU hV hR hQ' hK hPrivate hOutput
    have hLeast : IsLeastAO G (rotate n C q k U V R) :=
      ⟨hD, hFun.trans hC.1.2.1, fun E hE hEFun => hSize.trans_le (hC.1.2.2 E hE hEFun)⟩
    have hStrict := mass_lt_of_single_gate_drop n color C (rotate n C q k U V R) q hq hSize hEq
      (fun c => (hNewQ _).trans (hZero c)) ⟨b, hOn⟩
    have hMin := hC.2.1 _ hLeast
    omega
  rcases hPair with hAR | hBR
  · apply hNoRotation A B hA hB hQ
    intro c
    cases c
    · exact hAR.1
    · exact hAR.2
  · apply hNoRotation B A hB hA (fun x => (hQ x).trans (Bool.and_comm _ _))
    intro c
    cases c
    · exact hBR.1
    · exact hBR.2

end PEqualNP.Outside.L_meta_3566.AndReassociate

namespace PEqualNP.Outside.L_meta_3566.PrivateBudget

lemma sum_copy_add_private_le (a b : ℕ) (e : Fin (a + b) → ℕ)
    (q : Fin a → ℕ) (c : Fin b → ℕ) (J : Finset ℕ)
    (hPrefix : ∀ i : Fin a, e (Fin.castAdd b i) ≤ q i)
    (hOutside : ∀ j : Fin b, j.val ∉ J → e (Fin.natAdd a j) ≤ c j)
    (hPrivate : ∀ j : Fin b, j.val ∈ J → e (Fin.natAdd a j) = 0) :
    (∑ i, e i) + (∑ j ∈ Finset.univ.filter (fun j : Fin b => j.val ∈ J), c j) ≤
      (∑ i, q i) + ∑ j, c j := by
  classical
  rw [Fin.sum_univ_add]
  have hpre : (∑ i : Fin a, e (Fin.castAdd b i)) ≤ ∑ i, q i :=
    Finset.sum_le_sum fun i _ => hPrefix i
  have hpost : (∑ j : Fin b, e (Fin.natAdd a j)) +
      (∑ j ∈ Finset.univ.filter (fun j : Fin b => j.val ∈ J), c j) ≤ ∑ j, c j := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hJ : j.val ∈ J
    · simp [hJ, hPrivate j hJ]
    · simpa [hJ] using hOutside j hJ
  omega

end PEqualNP.Outside.L_meta_3566.PrivateBudget

namespace PEqualNP.Outside.L_meta_3566.PrivateCopy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.AO2Upper

def shift (n m w : ℕ) : ℕ := if w < n then w else w + m

def copyGate (n m q : ℕ) (J : Finset ℕ) (i : ℕ) (g : Gate) : Gate :=
  if i ∈ J then ⟨GateOp.and, [q, q]⟩ else ⟨g.op, g.inputs.map (shift n m)⟩

def code (n : ℕ) (Q C : Circuit) (J : Finset ℕ) : List Gate :=
  Q.gates ++ List.ofFn (fun i : Fin C.size => copyGate n Q.size Q.output J i.val (gateAt C i.val))

def compiled (n : ℕ) (Q C : Circuit) (J : Finset ℕ) : Circuit :=
  ⟨code n Q C J, shift n Q.size C.output⟩

lemma compiled_size (n : ℕ) (Q C : Circuit) (J : Finset ℕ) :
    (compiled n Q C J).size = Q.size + C.size := by
  simp [compiled, code, Circuit.size]

lemma gateAt_prefix (n : ℕ) (Q C : Circuit) (J : Finset ℕ)
    (i : ℕ) (hi : i < Q.size) : gateAt (compiled n Q C J) i = gateAt Q i := by
  exact List.getD_append _ _ _ _ hi

lemma gateAt_copy (n : ℕ) (Q C : Circuit) (J : Finset ℕ)
    (i : ℕ) (hi : i < C.size) :
    gateAt (compiled n Q C J) (Q.size + i) =
      copyGate n Q.size Q.output J i (gateAt C i) := by
  have hi' : i < C.gates.length := hi
  unfold gateAt compiled code
  rw [List.getD_append_right _ _ _ _ (by change Q.gates.length ≤ Q.gates.length + i; omega)]
  simp [Circuit.size, List.getD_eq_getElem?_getD, hi', gateAt]

lemma shift_lt_bound (n m i w : ℕ) (hw : w < n + i) : shift n m w < n + m + i := by
  by_cases h : w < n <;> simp only [shift, h, ↓reduceIte] <;> omega

lemma compiled_ao (n : ℕ) (Q C : Circuit) (J : Finset ℕ)
    (hQ : IsAO2 n Q) (hC : IsAO2 n C) (hq : Q.output < n + Q.size) :
    IsAO2 n (compiled n Q C J) := by
  have hmem (i : Fin C.size) : gateAt C i.val ∈ C.gates :=
    FalseRestrict.list_getD_mem C.gates i.val _ i.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    change g ∈ Q.gates ++ List.ofFn (fun i : Fin C.size =>
      copyGate n Q.size Q.output J i.val (gateAt C i.val)) at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hQ.1 g hg
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
      by_cases hi : i.val ∈ J
      · exact Or.inl (by simp [copyGate, hi])
      · simpa only [copyGate, ite_eq_right hi] using hC.1 _ (hmem i)
  · intro k hk w hw
    by_cases hkQ : k < Q.size
    · rw [gateAt_prefix n Q C J k hkQ] at hw
      exact hQ.2.1 k hkQ w hw
    · have hk' : k - Q.size < C.size := by
        have hsize := compiled_size n Q C J
        change k < (compiled n Q C J).size at hk
        omega
      have heq : k = Q.size + (k - Q.size) := by omega
      rw [heq, gateAt_copy n Q C J (k - Q.size) hk'] at hw
      by_cases hj : k - Q.size ∈ J
      · have hwq : w = Q.output := by simpa [copyGate, hj] using hw
        omega
      · simp only [copyGate, ite_eq_right hj, List.mem_map] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        have hb := hC.2.1 (k - Q.size) hk' v hv
        have hshift := shift_lt_bound n Q.size (k - Q.size) v hb
        omega
  · intro g hg
    change g ∈ Q.gates ++ List.ofFn (fun i : Fin C.size =>
      copyGate n Q.size Q.output J i.val (gateAt C i.val)) at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hQ.2.2 g hg
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
      by_cases hi : i.val ∈ J
      · simp [copyGate, hi]
      · simpa [copyGate, hi] using hC.2.2 _ (hmem i)

lemma prefix_wire (n : ℕ) (Q C : Circuit) (J : Finset ℕ)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + Q.size) :
    wireVal n (compiled n Q C J) w x = wireVal n Q w x := by
  change (wiresFrom (Q.gates ++ List.ofFn (fun i : Fin C.size =>
      copyGate n Q.size Q.output J i.val (gateAt C i.val))) (List.ofFn x)).getD w false =
    (wiresFrom Q.gates (List.ofFn x)).getD w false
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by
    rw [length_wiresFrom, List.length_ofFn]
    exact hw)]

lemma opnd_copy (n : ℕ) (Q C : Circuit) (J : Finset ℕ)
    (hC : IsAO2 n C) (i : ℕ) (hi : i < C.size) (hiJ : i ∉ J) (b : Fin 2) :
    opnd (compiled n Q C J) (Q.size + i) b = shift n Q.size (opnd C i b) := by
  have hg : gateAt C i ∈ C.gates := FalseRestrict.list_getD_mem C.gates i _ hi
  obtain ⟨a, d, hin⟩ := List.length_eq_two.mp (hC.2.2 _ hg)
  fin_cases b <;> simp [opnd, gateAt_copy n Q C J i hi, copyGate, hiJ, hin]

end PEqualNP.Outside.L_meta_3566.PrivateCopy

namespace PEqualNP.Outside.L_meta_3566.PrivateCopy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.LeafStep.Pruning

lemma shifted_internal_value (n : ℕ) (Q C : Circuit) (J : Finset ℕ) (i : ℕ)
    (x : Fin n → Bool) :
    wireVal n (compiled n Q C J) (shift n Q.size (n + i)) x =
      gateVal n (compiled n Q C J) (Q.size + i) x := by
  have hs : shift n Q.size (n + i) = n + (Q.size + i) := by
    simp only [shift, show ¬ n + i < n by omega, ite_false]
    omega
  rw [hs]
  rfl

lemma copied_alias (n : ℕ) (Q C : Circuit) (J : Finset ℕ)
    (hQ : IsAO2 n Q) (hC : IsAO2 n C) (hq : Q.output < n + Q.size)
    (i : ℕ) (hi : i < C.size) (hiJ : i ∈ J) (x : Fin n → Bool) :
    gateVal n (compiled n Q C J) (Q.size + i) x = circuitFun n Q x := by
  have hE := compiled_ao n Q C J hQ hC hq
  have hidx : Q.size + i < (compiled n Q C J).gates.length := by
    change Q.size + i < (compiled n Q C J).size
    rw [compiled_size]
    omega
  have hg : gateAt (compiled n Q C J) (Q.size + i) =
      (⟨GateOp.and, [Q.output, Q.output]⟩ : Gate) := by
    rw [gateAt_copy n Q C J i hi]
    simp [copyGate, hiJ]
  have he := gate_eq (compiled n Q C J) hE (Q.size + i) hidx x
  simp only [hg, isA, opv, opnd] at he
  change gateVal n (compiled n Q C J) (Q.size + i) x =
    (wireVal n (compiled n Q C J) Q.output x && wireVal n (compiled n Q C J) Q.output x) at he
  rw [Bool.and_self, prefix_wire n Q C J x Q.output hq] at he
  exact he

lemma copied_gate_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b)
    (hOp : ∀ o a b c d, R a c → R b d → R (opv o a b) (opv o c d))
    (n : ℕ) (Q C : Circuit) (J : Finset ℕ) (H : ℕ)
    (hQ : IsAO2 n Q) (hC : IsAO2 n C) (hq : Q.output < n + Q.size)
    (hPrivate : ∀ i < C.size, i ∉ J → ∀ j ∈ J,
      n + j ∈ (gateAt C i).inputs → j = H)
    (x : Fin n → Bool) (hBase : R (gateVal n C H x) (circuitFun n Q x)) :
    ∀ i < C.size, i ∉ J ∨ i = H →
      R (gateVal n C i x) (gateVal n (compiled n Q C J) (Q.size + i) x) := by
  have hE := compiled_ao n Q C J hQ hC hq
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi hkeep
    by_cases hiJ : i ∈ J
    · have hiH : i = H := hkeep.resolve_left (by simpa using hiJ)
      rw [copied_alias n Q C J hQ hC hq i hi hiJ x, hiH]
      exact hBase
    · have hmem (b : Fin 2) : opnd C i b ∈ (gateAt C i).inputs := by
        have hg : gateAt C i ∈ C.gates := FalseRestrict.list_getD_mem C.gates i _ hi
        obtain ⟨u, v, huv⟩ := List.length_eq_two.mp (hC.2.2 _ hg)
        fin_cases b <;> simp [opnd, huv]
      have hinput (b : Fin 2) :
          R (wireVal n C (opnd C i b) x)
            (wireVal n (compiled n Q C J) (shift n Q.size (opnd C i b)) x) := by
        have hw := hC.2.1 i hi (opnd C i b) (hmem b)
        by_cases hraw : opnd C i b < n
        · rw [show shift n Q.size (opnd C i b) = opnd C i b by simp [shift, hraw],
            wireVal_lt C (opnd C i b) hraw x,
            wireVal_lt (compiled n Q C J) (opnd C i b) hraw x]
          exact hrefl _
        · let j := opnd C i b - n
          have hj : j < i := by dsimp [j]; omega
          have hwj : n + j = opnd C i b := by dsimp [j]; omega
          have hjKeep : j ∉ J ∨ j = H := by
            by_cases hjJ : j ∈ J
            · exact Or.inr (hPrivate i hi hiJ j hjJ (hwj.symm ▸ hmem b))
            · exact Or.inl hjJ
          rw [← hwj, shifted_internal_value]
          exact ih j hj (by omega) hjKeep
      have hidx : Q.size + i < (compiled n Q C J).gates.length := by
        change Q.size + i < (compiled n Q C J).size
        rw [compiled_size]
        omega
      have hg : (gateAt (compiled n Q C J) (Q.size + i)).op = (gateAt C i).op := by
        rw [gateAt_copy n Q C J i hi]
        simp [copyGate, hiJ]
      rw [gate_eq C hC i hi x, gate_eq (compiled n Q C J) hE (Q.size + i) hidx x, hg]
      apply hOp
      · rw [opnd_copy n Q C J hC i hi hiJ 0]
        exact hinput 0
      · rw [opnd_copy n Q C J hC i hi hiJ 1]
        exact hinput 1

lemma copied_wire_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b)
    (hOp : ∀ o a b c d, R a c → R b d → R (opv o a b) (opv o c d))
    (n : ℕ) (Q C : Circuit) (J : Finset ℕ) (H : ℕ)
    (hQ : IsAO2 n Q) (hC : IsAO2 n C) (hq : Q.output < n + Q.size)
    (hPrivate : ∀ i < C.size, i ∉ J → ∀ j ∈ J,
      n + j ∈ (gateAt C i).inputs → j = H)
    (x : Fin n → Bool) (hBase : R (gateVal n C H x) (circuitFun n Q x))
    (w : ℕ) (hAllowed : ∀ j ∈ J, w = n + j → j = H) :
    R (wireVal n C w x) (wireVal n (compiled n Q C J) (shift n Q.size w) x) := by
  by_cases hw : w < n
  · rw [show shift n Q.size w = w by simp [shift, hw], wireVal_lt C w hw x,
      wireVal_lt (compiled n Q C J) w hw x]
    exact hrefl _
  · let i := w - n
    have hwi : n + i = w := by dsimp [i]; omega
    by_cases hi : i < C.size
    · have hkeep : i ∉ J ∨ i = H := by
        by_cases hiJ : i ∈ J
        · exact Or.inr (hAllowed i hiJ hwi.symm)
        · exact Or.inl hiJ
      rw [← hwi, shifted_internal_value]
      exact copied_gate_rel hrefl hOp n Q C J H hQ hC hq hPrivate x hBase i hi hkeep
    · have hlenC : (C.wires (List.ofFn x)).length = n + C.size := by
        rw [SharedRewrite.wires_eq_foldl, SharedRewrite.foldl_stepWire_length]
        simp [Circuit.size]
      have hlenE : ((compiled n Q C J).wires (List.ofFn x)).length = n + Q.size + C.size := by
        rw [SharedRewrite.wires_eq_foldl, SharedRewrite.foldl_stepWire_length]
        rw [List.length_ofFn]
        change n + (compiled n Q C J).size = _
        rw [compiled_size]
        omega
      have hshift : shift n Q.size w = w + Q.size := by simp [shift, hw]
      unfold wireVal
      rw [SharedRewrite.getD_ge_length _ w (by rw [hlenC]; dsimp [i] at hi; omega),
        SharedRewrite.getD_ge_length _ _ (by rw [hlenE, hshift]; dsimp [i] at hi; omega)]
      exact hrefl _

lemma copied_output_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b)
    (hOp : ∀ o a b c d, R a c → R b d → R (opv o a b) (opv o c d))
    (n : ℕ) (Q C : Circuit) (J : Finset ℕ) (H : ℕ)
    (hQ : IsAO2 n Q) (hC : IsAO2 n C) (hq : Q.output < n + Q.size)
    (hPrivate : ∀ i < C.size, i ∉ J → ∀ j ∈ J,
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ J, C.output = n + j → j = H)
    (x : Fin n → Bool) (hBase : R (gateVal n C H x) (circuitFun n Q x)) :
    R (circuitFun n C x) (circuitFun n (compiled n Q C J) x) := by
  exact copied_wire_rel hrefl hOp n Q C J H hQ hC hq hPrivate x hBase C.output hOutput

lemma opv_reverse_le (o a b c d : Bool) (hca : c ≤ a) (hdb : d ≤ b) :
    opv o c d ≤ opv o a b := by
  exact Bool.le_iff_imp.mpr (opv_mono o c d a b (Bool.le_iff_imp.mp hca) (Bool.le_iff_imp.mp hdb))

lemma copied_gate_le (n : ℕ) (Q C : Circuit) (J : Finset ℕ) (H : ℕ)
    (hQ : IsAO2 n Q) (hC : IsAO2 n C) (hq : Q.output < n + Q.size)
    (hPrivate : ∀ i < C.size, i ∉ J → ∀ j ∈ J,
      n + j ∈ (gateAt C i).inputs → j = H)
    (x : Fin n → Bool) (hBase : circuitFun n Q x ≤ gateVal n C H x) :
    ∀ i < C.size, i ∉ J ∨ i = H →
      gateVal n (compiled n Q C J) (Q.size + i) x ≤ gateVal n C i x :=
  copied_gate_rel (R := fun a b => b ≤ a) (fun _ => le_rfl) opv_reverse_le
    n Q C J H hQ hC hq hPrivate x hBase

lemma copied_gate_eq (n : ℕ) (Q C : Circuit) (J : Finset ℕ) (H : ℕ)
    (hQ : IsAO2 n Q) (hC : IsAO2 n C) (hq : Q.output < n + Q.size)
    (hPrivate : ∀ i < C.size, i ∉ J → ∀ j ∈ J,
      n + j ∈ (gateAt C i).inputs → j = H)
    (x : Fin n → Bool) (hBase : circuitFun n Q x = gateVal n C H x) :
    ∀ i < C.size, i ∉ J ∨ i = H →
      gateVal n (compiled n Q C J) (Q.size + i) x = gateVal n C i x := by
  intro i hi hkeep
  exact (copied_gate_rel (R := Eq) (fun _ => rfl)
    (by intro o a b c d hac hbd; rw [hac, hbd])
    n Q C J H hQ hC hq hPrivate x hBase.symm i hi hkeep).symm

lemma copied_output_le (n : ℕ) (Q C : Circuit) (J : Finset ℕ) (H : ℕ)
    (hQ : IsAO2 n Q) (hC : IsAO2 n C) (hq : Q.output < n + Q.size)
    (hPrivate : ∀ i < C.size, i ∉ J → ∀ j ∈ J,
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ J, C.output = n + j → j = H)
    (x : Fin n → Bool) (hBase : circuitFun n Q x ≤ gateVal n C H x) :
    circuitFun n (compiled n Q C J) x ≤ circuitFun n C x :=
  copied_output_rel (R := fun a b => b ≤ a) (fun _ => le_rfl) opv_reverse_le
    n Q C J H hQ hC hq hPrivate hOutput x hBase

lemma copied_output_eq (n : ℕ) (Q C : Circuit) (J : Finset ℕ) (H : ℕ)
    (hQ : IsAO2 n Q) (hC : IsAO2 n C) (hq : Q.output < n + Q.size)
    (hPrivate : ∀ i < C.size, i ∉ J → ∀ j ∈ J,
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ J, C.output = n + j → j = H)
    (x : Fin n → Bool) (hBase : circuitFun n Q x = gateVal n C H x) :
    circuitFun n (compiled n Q C J) x = circuitFun n C x := by
  exact (copied_output_rel (R := Eq) (fun _ => rfl)
    (by intro o a b c d hac hbd; rw [hac, hbd])
    n Q C J H hQ hC hq hPrivate hOutput x hBase.symm).symm

lemma compiled_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Q C : Circuit) (J : Finset ℕ) (H : ℕ)
    (hQ : IsAO2 n Q) (hC : IsAO2 n C) (hq : Q.output < n + Q.size)
    (hCFun : circuitFun n C = graphFun G ∅)
    (hPrivate : ∀ i < C.size, i ∉ J → ∀ j ∈ J,
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ J, C.output = n + j → j = H)
    (hBase : ∀ x : Fin n → Bool, circuitFun n Q x ≤ gateVal n C H x)
    (hEdges : ∀ a b : Fin n, G.Adj a b →
      circuitFun n Q (pairInput a b) = gateVal n C H (pairInput a b)) :
    circuitFun n (compiled n Q C J) = graphFun G ∅ := by
  have hE := compiled_ao n Q C J hQ hC hq
  apply EdgeProfile.eq_of_edges_and_below G _
  · intro x y hxy hx
    exact Bool.le_iff_imp.mp (SharedRewrite.circuitFun_monotone n _ hE.1
      (fun i => Bool.le_iff_imp.mpr (hxy i))) hx
  · intro x hx
    have ht := Bool.le_iff_imp.mp
      (copied_output_le n Q C J H hQ hC hq hPrivate hOutput x (hBase x)) hx
    simpa only [hCFun] using ht
  · intro a b hab
    rw [copied_output_eq n Q C J H hQ hC hq hPrivate hOutput _ (hEdges a b hab), hCFun]
    have he : ∃ u v : Fin n, G.Adj u v ∧ pairInput a b u = true ∧ pairInput a b v = true :=
      ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
    simpa [graphFun] using he

end PEqualNP.Outside.L_meta_3566.PrivateCopy

namespace PEqualNP.Outside.L_meta_3566.PrivateCopy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open MonoNormalize

noncomputable def privateMass {n : ℕ} (color : Fin n → Bool) (C : Circuit) (J : Finset ℕ) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin C.size => j.val ∈ J),
    gateWeight color (gateAt C j.val).op (gateVal n C j.val)

lemma gateWeight_le {n : ℕ} (color : Fin n → Bool) (op₁ op₂ : GateOp)
    (f g : (Fin n → Bool) → Bool)
    (h : ∀ b : Bool, f (input color b) ≤ g (input color b)) :
    gateWeight color op₁ f ≤ gateWeight color op₂ g := by
  have hF := h false
  have hT := h true
  unfold gateWeight
  cases hfF : f (input color false) <;> cases hgF : g (input color false) <;>
    cases hfT : f (input color true) <;> cases hgT : g (input color true) <;>
    simp_all [Bool.le_iff_imp]

lemma copied_mass_credit {n : ℕ} (color : Fin n → Bool) (Q C : Circuit) (J : Finset ℕ)
    (hOutside : ∀ j < C.size, j ∉ J → ∀ b : Bool,
      gateVal n (compiled n Q C J) (Q.size + j) (input color b) ≤
        gateVal n C j (input color b))
    (hPrivate : ∀ j < C.size, j ∈ J → ∀ b : Bool,
      gateVal n (compiled n Q C J) (Q.size + j) (input color b) = false) :
    mass color (compiled n Q C J) + privateMass color C J + n ≤ mass color Q + mass color C := by
  classical
  let E := compiled n Q C J
  let e : Fin (Q.size + C.size) → ℕ := fun i =>
    gateWeight color (gateAt E i.val).op (gateVal n E i.val)
  let q : Fin Q.size → ℕ := fun i =>
    gateWeight color (gateAt Q i.val).op (gateVal n Q i.val)
  let c : Fin C.size → ℕ := fun i =>
    gateWeight color (gateAt C i.val).op (gateVal n C i.val)
  have hBound := PrivateBudget.sum_copy_add_private_le Q.size C.size e q c J
    (fun i => by
      have hv : gateVal n E i.val = gateVal n Q i.val := by
        funext x
        exact prefix_wire n Q C J x (n + i.val) (by have := i.isLt; omega)
      simp only [e, q, Fin.val_castAdd, hv, gateWeight]
      exact le_rfl)
    (fun j hj => by
      exact gateWeight_le color _ _ _ _ (hOutside j.val j.isLt hj))
    (fun j hj => by
      simp only [e, Fin.val_natAdd, E, gateWeight, hPrivate j.val j.isLt hj,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero])
  have hE : mass color E = n + ∑ i : Fin (Q.size + C.size), e i := by
    rw [mass_eq_input_add_gateWeight]
    have hSize := compiled_size n Q C J
    change E.size = Q.size + C.size at hSize
    simp only [e]
    rw [hSize]
  have hQ : mass color Q = n + ∑ i, q i := mass_eq_input_add_gateWeight color Q
  have hC : mass color C = n + ∑ i, c i := mass_eq_input_add_gateWeight color C
  change (∑ i, e i) + privateMass color C J ≤ (∑ i, q i) + ∑ i, c i at hBound
  change mass color E + privateMass color C J + n ≤ mass color Q + mass color C
  omega

lemma copied_mass_gap {n : ℕ} (color : Fin n → Bool) (Q C : Circuit) (J : Finset ℕ)
    (hOutside : ∀ j < C.size, j ∉ J → ∀ b : Bool,
      gateVal n (compiled n Q C J) (Q.size + j) (input color b) ≤
        gateVal n C j (input color b))
    (hPrivate : ∀ j < C.size, j ∈ J → ∀ b : Bool,
      gateVal n (compiled n Q C J) (Q.size + j) (input color b) = false)
    (δ : ℕ) (hGap : mass color Q + δ ≤ n + privateMass color C J) :
    mass color (compiled n Q C J) + δ ≤ mass color C := by
  have h := copied_mass_credit color Q C J hOutside hPrivate
  omega

end PEqualNP.Outside.L_meta_3566.PrivateCopy

namespace PEqualNP.Outside.L_meta_3566.PrivateCopy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge MonoNormalize

lemma privateMass_eq_sum {n : ℕ} (color : Fin n → Bool) (C : Circuit) (J : Finset ℕ)
    (hJ : J ⊆ Finset.range C.size) :
    privateMass color C J = ∑ j ∈ J, gateWeight color (gateAt C j).op (gateVal n C j) := by
  classical
  unfold privateMass
  rw [Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j ∈ J then
    gateWeight color (gateAt C j).op (gateVal n C j) else 0)]
  rw [← Finset.sum_filter]
  have hf : (Finset.range C.size).filter (fun j => j ∈ J) = J := by
    ext j
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hj => ⟨hJ hj, hj⟩⟩
  rw [hf]

lemma privateMass_eq_counts {n : ℕ} (color : Fin n → Bool) (C : Circuit) (J : Finset ℕ)
    (hJ : J ⊆ Finset.range C.size) :
    privateMass color C J =
      (J.filter fun j => gateVal n C j (input color false) = true).card +
        (J.filter fun j => gateVal n C j (input color true) = true).card := by
  rw [privateMass_eq_sum color C J hJ]
  simp [gateWeight, Finset.sum_add_distrib]

end PEqualNP.Outside.L_meta_3566.PrivateCopy

namespace PEqualNP.Outside.L_meta_3566.PrivateCopy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open MonoNormalize

lemma exists_private_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (Q C : Circuit) (J : Finset ℕ) (H : ℕ)
    (hQ : IsAO2 n Q) (hC : IsAO2 n C) (hq : Q.output < n + Q.size)
    (hCFun : circuitFun n C = graphFun G ∅) (hJ : J ⊆ Finset.range C.size)
    (hPrivate : ∀ i < C.size, i ∉ J → ∀ j ∈ J,
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ J, C.output = n + j → j = H)
    (hBase : ∀ x : Fin n → Bool, circuitFun n Q x ≤ gateVal n C H x)
    (hEdges : ∀ a b : Fin n, G.Adj a b →
      circuitFun n Q (pairInput a b) = gateVal n C H (pairInput a b))
    (hMono : ∀ b : Bool, circuitFun n Q (input color b) = false)
    (hSize : Q.size ≤ J.card) (δ : ℕ)
    (hGap : mass color Q + δ ≤ n + privateMass color C J) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ mass color D + δ ≤ mass color C := by
  classical
  let E := compiled n Q C J
  let K : Finset ℕ := J.image fun i => Q.size + i
  have hE : IsAO2 n E := compiled_ao n Q C J hQ hC hq
  have hEFun : circuitFun n E = graphFun G ∅ :=
    compiled_correct G Q C J H hQ hC hq hCFun hPrivate hOutput hBase hEdges
  have hOutside : ∀ j < C.size, j ∉ J → ∀ b : Bool,
      gateVal n E (Q.size + j) (input color b) ≤ gateVal n C j (input color b) := by
    intro j hj hjJ b
    exact copied_gate_le n Q C J H hQ hC hq hPrivate _ (hBase _) j hj (Or.inl hjJ)
  have hZero : ∀ j < C.size, j ∈ J → ∀ b : Bool,
      gateVal n E (Q.size + j) (input color b) = false := by
    intro j hj hjJ b
    exact (copied_alias n Q C J hQ hC hq j hj hjJ _).trans (hMono b)
  have hMass : mass color E + δ ≤ mass color C :=
    copied_mass_gap color Q C J hOutside hZero δ hGap
  have hK : K ⊆ Finset.range E.size := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hi' : i < C.size := Finset.mem_range.mp (hJ hi)
    apply Finset.mem_range.mpr
    change Q.size + i < (compiled n Q C J).size
    rw [compiled_size]
    omega
  have hKcard : K.card = J.card := by
    dsimp [K]
    apply Finset.card_image_of_injOn
    intro i hi j hj he
    exact Nat.add_left_cancel he
  have hEarlier : ∀ k ∈ K, Q.output < n + k := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    omega
  have hAlias : ∀ k ∈ K, ∀ x : Fin n → Bool,
      wireVal n E (n + k) x = wireVal n E Q.output x := by
    intro k hk x
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hi' : i < C.size := Finset.mem_range.mp (hJ hi)
    have hv := copied_alias n Q C J hQ hC hq i hi' hi x
    have hRoot : wireVal n E Q.output x = circuitFun n Q x :=
      prefix_wire n Q C J x Q.output hq
    exact hv.trans hRoot.symm
  obtain ⟨D, hD, hFun, hSizeD, hMassD⟩ :=
    erase_alias_family_with_mono_mass n E hE K hK Q.output hEarlier hAlias color
  have hESize : E.size = Q.size + C.size := compiled_size n Q C J
  refine ⟨D, hD, hFun.trans hEFun, ?_, ?_⟩ <;> omega

lemma not_of_mono_minimum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (Q C : Circuit) (J : Finset ℕ) (H : ℕ)
    (hMin : IsMonoJunkLeastAO G color C)
    (hQ : IsAO2 n Q) (hq : Q.output < n + Q.size) (hJ : J ⊆ Finset.range C.size)
    (hPrivate : ∀ i < C.size, i ∉ J → ∀ j ∈ J,
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ J, C.output = n + j → j = H)
    (hBase : ∀ x : Fin n → Bool, circuitFun n Q x ≤ gateVal n C H x)
    (hEdges : ∀ a b : Fin n, G.Adj a b →
      circuitFun n Q (pairInput a b) = gateVal n C H (pairInput a b))
    (hMono : ∀ b : Bool, circuitFun n Q (input color b) = false)
    (hSize : Q.size ≤ J.card)
    (hGap : mass color Q + 1 ≤ n + privateMass color C J) : False := by
  obtain ⟨D, hD, hFun, hSizeD, hMassD⟩ := exists_private_replacement G color Q C J H
    hQ hMin.1.1 hq hMin.1.2.1 hJ hPrivate hOutput hBase hEdges hMono hSize 1 hGap
  have hLeastD : IsLeastAO G D := by
    refine ⟨hD, hFun, ?_⟩
    intro F hF hFFun
    exact hSizeD.trans (hMin.1.2.2 F hF hFFun)
  have hMinimalMass := hMin.2.1 D hLeastD
  omega

end PEqualNP.Outside.L_meta_3566.PrivateCopy

namespace PEqualNP.Outside.L_meta_3566.PrivateColorTree

abbrev Tree (n : ℕ) := FreeMagma (Fin n)

def size : Tree n → ℕ
  | .of _ => 0
  | .mul l r => size l + size r + 1

def eval : Tree n → (Fin n → Bool) → Bool
  | .of v, x => x v
  | .mul l r, x => eval l x || eval r x

def activeCount : Tree n → (Fin n → Bool) → ℕ
  | .of _, _ => 0
  | .mul l r, x => activeCount l x + activeCount r x + if eval (.mul l r) x then 1 else 0

def combine : Option (Tree n) → Option (Tree n) → Option (Tree n)
  | none, r => r
  | l, none => l
  | some l, some r => some (.mul l r)

def project (color : Fin n → Bool) (b : Bool) : Tree n → Option (Tree n)
  | .of v => if color v = b then some (.of v) else none
  | .mul l r => combine (project color b l) (project color b r)

def optSize : Option (Tree n) → ℕ
  | none => 0
  | some t => size t

def optEval (t : Option (Tree n)) (x : Fin n → Bool) : Bool :=
  t.elim false (fun u => eval u x)

def optActive (t : Option (Tree n)) (x : Fin n → Bool) : ℕ :=
  t.elim 0 (fun u => activeCount u x)

def present : Option (Tree n) → ℕ
  | none => 0
  | some _ => 1

lemma optSize_none : optSize (none : Option (Tree n)) = 0 := rfl
lemma optSize_some (t : Tree n) : optSize (some t) = size t := rfl
lemma present_none : present (none : Option (Tree n)) = 0 := rfl
lemma present_some (t : Tree n) : present (some t) = 1 := rfl

def Pure (color : Fin n → Bool) (b : Bool) : Tree n → Prop
  | .of v => color v = b
  | .mul l r => Pure color b l ∧ Pure color b r

lemma eval_all_false (t : Tree n) : eval t (fun _ => false) = false := by
  induction t with
  | of v => rfl
  | mul l r hl hr => simp [eval, hl, hr]

lemma eval_all_true (t : Tree n) : eval t (fun _ => true) = true := by
  induction t with
  | of v => rfl
  | mul l r hl hr => simp [eval, hl, hr]

lemma optEval_combine (l r : Option (Tree n)) (x : Fin n → Bool) :
    optEval (combine l r) x = (optEval l x || optEval r x) := by
  cases l <;> cases r <;> simp [combine, optEval, eval]

lemma project_eval_mask (color : Fin n → Bool) (b : Bool) (t : Tree n)
    (x : Fin n → Bool) :
    optEval (project color b t) x = eval t (fun v => if color v = b then x v else false) := by
  induction t with
  | of v => by_cases h : color v = b <;> simp [project, optEval, eval, h]
  | mul l r hl hr => simp only [project, optEval_combine, eval, hl, hr]

lemma project_pure (color : Fin n → Bool) (b : Bool) (t u : Tree n)
    (h : project color b t = some u) : Pure color b u := by
  induction t generalizing u with
  | of v =>
    by_cases hv : color v = b
    · simp only [project, ite_eq_left hv, Option.some.injEq] at h
      subst u
      exact hv
    · simp [project, hv] at h
  | mul l r hl hr =>
    simp only [project] at h
    cases hL : project color b l <;> cases hR : project color b r <;>
      simp only [hL, hR, combine, Option.some.injEq] at h
    · cases h
    · subst u; exact hr _ hR
    · subst u; exact hl _ hL
    · subst u; exact ⟨hl _ hL, hr _ hR⟩

lemma pure_mono (color : Fin n → Bool) (b : Bool) (t : Tree n) (h : Pure color b t) :
    eval t (fun v => decide (color v = b)) = true ∧
      activeCount t (fun v => decide (color v = b)) = size t ∧
      eval t (fun v => decide (color v = !b)) = false ∧
      activeCount t (fun v => decide (color v = !b)) = 0 := by
  induction t with
  | of v =>
    change color v = b at h
    cases b <;> simp [eval, activeCount, size, h]
  | mul l r hl hr =>
    obtain ⟨hlv, hla, hlz, hlaz⟩ := hl h.1
    obtain ⟨hrv, hra, hrz, hraz⟩ := hr h.2
    simp [eval, activeCount, size, hlv, hrv, hla, hra, hlz, hrz, hlaz, hraz]

lemma combine_leaf_count (l r : Option (Tree n)) :
    optSize (combine l r) + present (combine l r) =
      optSize l + present l + (optSize r + present r) := by
  cases l <;> cases r <;> simp [combine, optSize, present, size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma projection_leaf_count (color : Fin n → Bool) (t : Tree n) :
    optSize (project color true t) + present (project color true t) +
      (optSize (project color false t) + present (project color false t)) = size t + 1 := by
  induction t with
  | of v => cases hc : color v <;> simp [project, hc, optSize, present, size]
  | mul l r hl hr =>
    simp only [project, combine_leaf_count, size]
    omega

lemma projection_sizes (color : Fin n → Bool) (t tTrue tFalse : Tree n)
    (hTrue : project color true t = some tTrue) (hFalse : project color false t = some tFalse) :
    size tTrue + size tFalse + 1 = size t := by
  have h := projection_leaf_count color t
  simp only [hTrue, hFalse, optSize, present] at h
  omega

lemma eval_monotone (t : Tree n) (x y : Fin n → Bool) (h : ∀ v, x v ≤ y v) :
    eval t x ≤ eval t y := by
  induction t with
  | of v => exact h v
  | mul l r hl hr =>
    change (eval l x || eval r x) ≤ (eval l y || eval r y)
    cases hxL : eval l x <;> cases hxR : eval r x <;>
      cases hyL : eval l y <;> cases hyR : eval r y <;> simp_all

lemma project_eval_le (color : Fin n → Bool) (b : Bool) (t : Tree n) (x : Fin n → Bool) :
    optEval (project color b t) x ≤ eval t x := by
  rw [project_eval_mask]
  apply eval_monotone
  intro v
  split_ifs
  · exact le_refl _
  · exact Bool.false_le _

lemma optActive_combine_le (l r : Option (Tree n)) (x : Fin n → Bool) :
    optActive (combine l r) x ≤ optActive l x + optActive r x +
      (if optEval l x || optEval r x then 1 else 0) := by
  cases l <;> cases r <;> simp [combine, optActive, optEval, activeCount, eval]

lemma project_active_le (color : Fin n → Bool) (b : Bool) (t : Tree n) (x : Fin n → Bool) :
    optActive (project color b t) x ≤ activeCount t x := by
  induction t with
  | of v => by_cases hc : color v = b <;> simp [project, hc, optActive, activeCount]
  | mul l r hl hr =>
    have hcombine := optActive_combine_le (project color b l) (project color b r) x
    have he : (optEval (project color b l) x || optEval (project color b r) x) ≤
        (eval l x || eval r x) := by
      simpa only [project, optEval_combine, eval] using project_eval_le color b (.mul l r) x
    have hcount : (if optEval (project color b l) x || optEval (project color b r) x then 1 else 0) ≤
        (if eval l x || eval r x then 1 else 0) := by
      cases ha : (optEval (project color b l) x || optEval (project color b r) x) <;>
        cases hb : (eval l x || eval r x) <;> simp_all [Bool.le_iff_imp]
    change optActive (combine (project color b l) (project color b r)) x ≤
      activeCount l x + activeCount r x + (if eval l x || eval r x then 1 else 0)
    omega

lemma eval_mono_input (color : Fin n → Bool) (b : Bool) (t : Tree n) :
    eval t (fun v => decide (color v = b)) = (project color b t).isSome := by
  have hmask : (fun v => if color v = b then true else false) =
      (fun v => decide (color v = b)) := by
    funext v
    by_cases hc : color v = b <;> simp [hc]
  calc
    eval t (fun v => decide (color v = b)) = optEval (project color b t) (fun _ => true) := by
      simpa only [hmask] using (project_eval_mask color b t (fun _ => true)).symm
    _ = (project color b t).isSome := by
      cases project color b t <;> simp [optEval, eval_all_true]

lemma present_combine_le (l r : Option (Tree n)) :
    present (combine l r) ≤ present l + present r := by
  cases l <;> cases r <;> simp [combine, present]

lemma present_le_one (t : Option (Tree n)) : present t ≤ 1 := by
  cases t <;> simp [present]

lemma mono_active_bound (color : Fin n → Bool) (b : Bool) (t : Tree n) :
    optSize (project color b t) + present (project color b t) + present (project color (!b) t) ≤
      activeCount t (fun v => decide (color v = b)) + 1 := by
  induction t with
  | of v => cases b <;> cases hc : color v <;> simp [project, hc, optSize, present, activeCount, size]
  | mul l r hl hr =>
    have he := eval_mono_input color b (.mul l r)
    change eval (.mul l r) (fun v => decide (color v = b)) =
      (combine (project color b l) (project color b r)).isSome at he
    change optSize (combine (project color b l) (project color b r)) +
        present (combine (project color b l) (project color b r)) +
        present (combine (project color (!b) l) (project color (!b) r)) ≤
      activeCount (.mul l r) (fun v => decide (color v = b)) + 1
    rw [combine_leaf_count]
    have hpn := present_combine_le (project color (!b) l) (project color (!b) r)
    cases hL : project color b l <;> cases hR : project color b r
    · have hOne := present_le_one (combine (project color (!b) l) (project color (!b) r))
      simp only [optSize_none, present_none, Nat.zero_add]
      omega
    · simp only [hL, hR, combine, Option.isSome_some] at he
      simp only [activeCount, he, ite_true]
      simp only [hL, hR, optSize_none, optSize_some, present_none, present_some] at hl hr ⊢
      omega
    · simp only [hL, hR, combine, Option.isSome_some] at he
      simp only [activeCount, he, ite_true]
      simp only [hL, hR, optSize_none, optSize_some, present_none, present_some] at hl hr ⊢
      omega
    · simp only [hL, hR, combine, Option.isSome_some] at he
      simp only [activeCount, he, ite_true]
      simp only [hL, hR, optSize_some, present_some] at hl hr ⊢
      omega

lemma mono_active_strict (color : Fin n → Bool) (b : Bool) (t matching opposite : Tree n)
    (hm : project color b t = some matching) (ho : project color (!b) t = some opposite) :
    size matching + 1 ≤ activeCount t (fun v => decide (color v = b)) := by
  have h := mono_active_bound color b t
  simp only [hm, ho, optSize, present] at h
  omega

end PEqualNP.Outside.L_meta_3566.PrivateColorTree

namespace PEqualNP.Outside.L_meta_3566.PrivateColorTree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.AO2Upper

variable {n : ℕ}

def emit : Tree n → ℕ → List Gate × ℕ
  | .of i, _ => ([], i.val)
  | .mul a b, m =>
      let ea := emit a m
      let eb := emit b (m + size a)
      (ea.1 ++ eb.1 ++ [⟨GateOp.or, [ea.2, eb.2]⟩], m + size a + size b)

lemma emit_length (t : Tree n) (m : ℕ) : (emit t m).1.length = size t := by
  induction t generalizing m with
  | of i => rfl
  | mul a b ia ib => simp [emit, size, ia, ib, Nat.add_assoc]

lemma emit_all_or (t : Tree n) (m : ℕ) :
    ∀ g ∈ (emit t m).1, g.op = GateOp.or := by
  induction t generalizing m with
  | of i => simp [emit]
  | mul a b ia ib =>
    intro g hg
    simp only [emit, List.mem_append, List.mem_singleton] at hg
    rcases hg with (ha | hb) | rfl
    · exact ia m g ha
    · exact ib (m + size a) g hb
    · rfl

lemma emit_good (t : Tree n) (m : ℕ) (hm : n ≤ m) :
    Good m (emit t m).1 ∧ (emit t m).2 < m + size t := by
  induction t generalizing m with
  | of i => exact ⟨True.intro, by have := i.isLt; simpa [emit, size] using (show i.val < m by omega)⟩
  | mul a b ia ib =>
    obtain ⟨ha, hoa⟩ := ia m hm
    obtain ⟨hb, hob⟩ := ib (m + size a) (by omega)
    constructor
    · change Good m ((emit a m).1 ++ (emit b (m + size a)).1 ++
        [⟨GateOp.or, [(emit a m).2, (emit b (m + size a)).2]⟩])
      apply good_append
      · apply good_append _ _ _ ha
        simpa only [emit_length] using hb
      · refine ⟨⟨Or.inr rfl, rfl, ?_⟩, True.intro⟩
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        simp only [List.length_append, emit_length]
        rcases hi with rfl | rfl <;> omega
    · change m + size a + size b < m + (size a + size b + 1)
      omega

lemma emit_values (t : Tree n) (m : ℕ) (hm : n ≤ m) (w : List Bool) (hw : w.length = m) :
    (wiresFrom (emit t m).1 w).getD (emit t m).2 false =
      eval t (fun i => w.getD i.val false) ∧
    (wiresFrom (emit t m).1 w).count true =
      w.count true + activeCount t (fun i => w.getD i.val false) := by
  induction t generalizing m w with
  | of i => exact ⟨rfl, rfl⟩
  | mul a b ia ib =>
    let ea := emit a m
    let eb := emit b (m + size a)
    let w1 := wiresFrom ea.1 w
    let w2 := wiresFrom eb.1 w1
    let x : Fin n → Bool := fun i => w.getD i.val false
    have hlen1 : w1.length = m + size a := by
      rw [length_wiresFrom, hw, emit_length]
    have hlen2 : w2.length = m + size a + size b := by
      rw [length_wiresFrom, hlen1, emit_length]
    obtain ⟨hva, hca⟩ := ia m hm w hw
    obtain ⟨hvb, hcb⟩ := ib (m + size a) (by omega) w1 hlen1
    have hx : (fun i : Fin n => w1.getD i.val false) = x := by
      funext i
      exact getD_wiresFrom ea.1 w i.val (by rw [hw]; have := i.isLt; omega)
    rw [hx] at hvb hcb
    have hoa : ea.2 < w1.length := by
      rw [hlen1]
      exact (emit_good a m hm).2
    have hleft : w2.getD ea.2 false = eval a x := by
      rw [getD_wiresFrom eb.1 w1 ea.2 hoa]
      exact hva
    have hright : w2.getD eb.2 false = eval b x := hvb
    have hval : GateOp.or.eval ([ea.2, eb.2].map fun i => w2.getD i false) =
        eval (.mul a b) x := by
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false, hleft, hright, eval]
    have hrun : wiresFrom (emit (.mul a b) m).1 w = w2 ++ [eval (.mul a b) x] := by
      change wiresFrom (ea.1 ++ eb.1 ++ [⟨GateOp.or, [ea.2, eb.2]⟩]) w = _
      rw [wiresFrom_append, wiresFrom_append]
      change w2 ++ [GateOp.or.eval ([ea.2, eb.2].map fun i => w2.getD i false)] = _
      rw [hval]
    constructor
    · rw [hrun]
      change (w2 ++ [eval (.mul a b) x]).getD (m + size a + size b) false = _
      rw [← hlen2, getD_snoc_eq]
    · rw [hrun, List.count_append]
      change w2.count true + [eval (.mul a b) x].count true =
        w.count true + (activeCount a x + activeCount b x + if eval (.mul a b) x then 1 else 0)
      change w1.count true = w.count true + activeCount a x at hca
      change w2.count true = w1.count true + activeCount b x at hcb
      cases eval (.mul a b) x <;> simp <;> omega

lemma emit_spec (t : Tree n) (m : ℕ) (hm : n ≤ m) :
    Good m (emit t m).1 ∧ (emit t m).1.length = size t ∧
      (emit t m).2 < m + (emit t m).1.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom (emit t m).1 w).getD (emit t m).2 false =
          eval t (fun i => w.getD i.val false) ∧
        (wiresFrom (emit t m).1 w).count true =
          w.count true + activeCount t (fun i => w.getD i.val false) := by
  obtain ⟨hg, ho⟩ := emit_good t m hm
  exact ⟨hg, emit_length t m, by simpa only [emit_length] using ho,
    fun w hw => emit_values t m hm w hw⟩

def compiled (t : Tree n) : Circuit := ⟨(emit t n).1, (emit t n).2⟩

lemma compiled_spec (t : Tree n) :
    IsAO2 n (compiled t) ∧ circuitFun n (compiled t) = eval t ∧
      (compiled t).size = size t ∧
      ∀ x : Fin n → Bool, ((compiled t).wires (List.ofFn x)).count true =
        (List.ofFn x).count true + activeCount t x := by
  refine ⟨good_ao2 n _ _ (emit_good t n le_rfl).1, ?_, emit_length t n, ?_⟩
  · funext x
    have h := (emit_values t n le_rfl (List.ofFn x) (by simp)).1
    change (wiresFrom (emit t n).1 (List.ofFn x)).getD (emit t n).2 false = _
    simpa only [getD_ofFn] using h
  · intro x
    have h := (emit_values t n le_rfl (List.ofFn x) (by simp)).2
    change (wiresFrom (emit t n).1 (List.ofFn x)).count true = _
    simpa only [getD_ofFn] using h

def appendCompiled (pre : List Gate) (t : Tree n) : Circuit :=
  ⟨pre ++ (emit t (n + pre.length)).1, (emit t (n + pre.length)).2⟩

lemma append_compiled_spec (pre : List Gate) (hprefix : Good n pre) (t : Tree n) :
    IsAO2 n (appendCompiled pre t) ∧
      (appendCompiled pre t).size = pre.length + size t ∧
      circuitFun n (appendCompiled pre t) = eval t ∧
      ∀ x : Fin n → Bool, ((appendCompiled pre t).wires (List.ofFn x)).count true =
        (wiresFrom pre (List.ofFn x)).count true + activeCount t x := by
  have hm : n ≤ n + pre.length := by omega
  have hgood : Good n (pre ++ (emit t (n + pre.length)).1) :=
    good_append _ _ _ hprefix (emit_good t _ hm).1
  have hvalues (x : Fin n → Bool) :
      circuitFun n (appendCompiled pre t) x = eval t x ∧
      ((appendCompiled pre t).wires (List.ofFn x)).count true =
        (wiresFrom pre (List.ofFn x)).count true + activeCount t x := by
    have hlen : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom, List.length_ofFn]
    have hx : (fun i : Fin n => (wiresFrom pre (List.ofFn x)).getD i.val false) = x := by
      funext i
      rw [getD_wiresFrom _ _ _ (by simp)]
      exact getD_ofFn x i
    obtain ⟨hv, hc⟩ := emit_values t (n + pre.length) hm
      (wiresFrom pre (List.ofFn x)) hlen
    rw [hx] at hv hc
    constructor
    · change (wiresFrom (pre ++ (emit t (n + pre.length)).1)
        (List.ofFn x)).getD (emit t (n + pre.length)).2 false = _
      rw [wiresFrom_append]
      exact hv
    · change (wiresFrom (pre ++ (emit t (n + pre.length)).1)
        (List.ofFn x)).count true = _
      rw [wiresFrom_append]
      exact hc
  refine ⟨good_ao2 n _ _ hgood, ?_, funext fun x => (hvalues x).1,
    fun x => (hvalues x).2⟩
  simp [appendCompiled, Circuit.size, emit_length]

end PEqualNP.Outside.L_meta_3566.PrivateColorTree

namespace PEqualNP.Outside.L_meta_3566.PrivateColorShell

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm OnePureFrontier

def part {n : ℕ} (color : Fin n → Bool) (b : Bool) (S : Finset (Fin n)) :
    Finset (Fin n) := S.filter fun v => color v = b

def cross {n : ℕ} (color : Fin n → Bool) (S T : Finset (Fin n))
    (x : Fin n → Bool) : Bool :=
  (orSet (part color false S) x && orSet (part color true T) x) ||
  (orSet (part color true S) x && orSet (part color false T) x)

lemma orSet_part_le {n : ℕ} (color : Fin n → Bool) (b : Bool)
    (S : Finset (Fin n)) (x : Fin n → Bool) :
    orSet (part color b S) x ≤ orSet S x := by
  apply Bool.le_iff_imp.mpr
  simp only [orSet, decide_eq_true_eq]
  rintro ⟨v, hv, hx⟩
  exact ⟨v, (Finset.mem_filter.mp hv).1, hx⟩

lemma cross_le {n : ℕ} (color : Fin n → Bool) (S T : Finset (Fin n))
    (x : Fin n → Bool) : cross color S T x ≤ (orSet S x && orSet T x) := by
  apply Bool.le_iff_imp.mpr
  intro h
  have h' : (orSet (part color false S) x = true ∧
      orSet (part color true T) x = true) ∨
      (orSet (part color true S) x = true ∧
      orSet (part color false T) x = true) := by simpa [cross] using h
  rcases h' with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · simp [Bool.le_iff_imp.mp (orSet_part_le color false S x) hs,
      Bool.le_iff_imp.mp (orSet_part_le color true T x) ht]
  · simp [Bool.le_iff_imp.mp (orSet_part_le color true S x) hs,
      Bool.le_iff_imp.mp (orSet_part_le color false T x) ht]

lemma cross_pair_eq {n : ℕ} (color : Fin n → Bool) (S T : Finset (Fin n))
    (hDisj : Disjoint S T) (a b : Fin n) (hColor : color a ≠ color b) :
    cross color S T (pairInput a b) = (orSet S (pairInput a b) && orSet T (pairInput a b)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact Bool.le_iff_imp.mp (cross_le color S T (pairInput a b))
  · intro h
    have h' : (a ∈ S ∨ b ∈ S) ∧ (a ∈ T ∨ b ∈ T) := by
      simpa only [Bool.and_eq_true, orSet_pair] using h
    rcases h' with ⟨haS | hbS, haT | hbT⟩
    · exact False.elim ((Finset.disjoint_left.mp hDisj haS) haT)
    · cases hca : color a <;> cases hcb : color b <;>
        simp_all [cross, orSet_pair, part]
    · cases hca : color a <;> cases hcb : color b <;>
        simp_all [cross, orSet_pair, part]
    · exact False.elim ((Finset.disjoint_left.mp hDisj hbS) hbT)

lemma orSet_wrong_part {n : ℕ} (color : Fin n → Bool) (b c : Bool)
    (hbc : b ≠ c) (S : Finset (Fin n)) :
    orSet (part color b S) (fun v => decide (color v = c)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have h' : ∃ v ∈ part color b S, decide (color v = c) = true := of_decide_eq_true h
  obtain ⟨v, hv, hx⟩ := h'
  exact hbc ((Finset.mem_filter.mp hv).2.symm.trans (of_decide_eq_true hx))

lemma cross_mono_false {n : ℕ} (color : Fin n → Bool) (b : Bool)
    (S T : Finset (Fin n)) :
    cross color S T (fun v => decide (color v = b)) = false := by
  cases b
  · unfold cross
    rw [orSet_wrong_part color true false (by decide) T,
      orSet_wrong_part color true false (by decide) S]
    simp
  · unfold cross
    rw [orSet_wrong_part color false true (by decide) S,
      orSet_wrong_part color false true (by decide) T]
    simp

end PEqualNP.Outside.L_meta_3566.PrivateColorShell

namespace PEqualNP.Outside.L_meta_3566.PrivateColorTree

open PEqualNP.TopForm PEqualNP.Outside.L_meta_3566.OnePureFrontier

def vars : Tree n → Finset (Fin n)
  | .of v => {v}
  | .mul l r => vars l ∪ vars r

def optVars : Option (Tree n) → Finset (Fin n)
  | none => ∅
  | some t => vars t

lemma eval_eq_orSet (t : Tree n) (x : Fin n → Bool) : eval t x = orSet (vars t) x := by
  induction t with
  | of v => simp [eval, vars, orSet]
  | mul l r hl hr =>
    rw [eval, hl, hr]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, orSet, decide_eq_true_eq, vars, Finset.mem_union]
    aesop

lemma optVars_combine (l r : Option (Tree n)) :
    optVars (combine l r) = optVars l ∪ optVars r := by
  cases l <;> cases r <;> simp [combine, optVars, vars]

lemma optVars_project (color : Fin n → Bool) (b : Bool) (t : Tree n) :
    optVars (project color b t) = PrivateColorShell.part color b (vars t) := by
  induction t with
  | of v => by_cases h : color v = b <;>
      simp [project, optVars, vars, PrivateColorShell.part, Finset.filter_singleton, h]
  | mul l r hl hr =>
    simp only [project, optVars_combine, hl, hr, vars, PrivateColorShell.part,
      Finset.filter_union]

lemma vars_project (color : Fin n → Bool) (b : Bool) (t u : Tree n)
    (h : project color b t = some u) :
    vars u = PrivateColorShell.part color b (vars t) := by
  have heq := optVars_project color b t
  simpa only [h, optVars] using heq

lemma projected_eval_eq {n : ℕ} (color : Fin n → Bool) (b : Bool) (t u : Tree n)
    (h : project color b t = some u) (x : Fin n → Bool) :
    eval u x = orSet (PrivateColorShell.part color b (vars t)) x := by
  rw [eval_eq_orSet, vars_project color b t u h]

end PEqualNP.Outside.L_meta_3566.PrivateColorTree

namespace PEqualNP.Outside.L_meta_3566.PrivateColorShell

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Outside.L_meta_3566.OnePureFrontier
open PrivateColorTree

def oldSize (s t : PrivateColorTree.Tree n) : ℕ := size s + size t + 1

def newSize (sFalse sTrue tFalse tTrue : PrivateColorTree.Tree n) : ℕ :=
  size sFalse + size sTrue + size tFalse + size tTrue + 3

def oldValue (s t : PrivateColorTree.Tree n) (x : Fin n → Bool) : Bool := eval s x && eval t x

def newValue (sFalse sTrue tFalse tTrue : PrivateColorTree.Tree n) (x : Fin n → Bool) : Bool :=
  (eval sFalse x && eval tTrue x) || (eval sTrue x && eval tFalse x)

def oldActive (s t : PrivateColorTree.Tree n) (x : Fin n → Bool) : ℕ :=
  activeCount s x + activeCount t x + if oldValue s t x then 1 else 0

def newActive (sFalse sTrue tFalse tTrue : PrivateColorTree.Tree n) (x : Fin n → Bool) : ℕ :=
  activeCount sFalse x + activeCount sTrue x + activeCount tFalse x + activeCount tTrue x +
    (if eval sFalse x && eval tTrue x then 1 else 0) +
    (if eval sTrue x && eval tFalse x then 1 else 0) +
    (if newValue sFalse sTrue tFalse tTrue x then 1 else 0)

lemma projection_size_eq (color : Fin n → Bool) (s t sFalse sTrue tFalse tTrue : PrivateColorTree.Tree n)
    (hsF : project color false s = some sFalse) (hsT : project color true s = some sTrue)
    (htF : project color false t = some tFalse) (htT : project color true t = some tTrue) :
    newSize sFalse sTrue tFalse tTrue = oldSize s t := by
  have hs := projection_sizes color s sTrue sFalse hsT hsF
  have ht := projection_sizes color t tTrue tFalse htT htF
  simp only [newSize, oldSize]
  omega

lemma newValue_eq_cross (color : Fin n → Bool) (s t sFalse sTrue tFalse tTrue : PrivateColorTree.Tree n)
    (hsF : project color false s = some sFalse) (hsT : project color true s = some sTrue)
    (htF : project color false t = some tFalse) (htT : project color true t = some tTrue)
    (x : Fin n → Bool) :
    newValue sFalse sTrue tFalse tTrue x = cross color (vars s) (vars t) x := by
  simp only [newValue, cross, projected_eval_eq color false s sFalse hsF,
    projected_eval_eq color true s sTrue hsT, projected_eval_eq color false t tFalse htF,
    projected_eval_eq color true t tTrue htT]

lemma newValue_le_oldValue (color : Fin n → Bool) (s t sFalse sTrue tFalse tTrue : PrivateColorTree.Tree n)
    (hsF : project color false s = some sFalse) (hsT : project color true s = some sTrue)
    (htF : project color false t = some tFalse) (htT : project color true t = some tTrue)
    (x : Fin n → Bool) : newValue sFalse sTrue tFalse tTrue x ≤ oldValue s t x := by
  rw [newValue_eq_cross color s t sFalse sTrue tFalse tTrue hsF hsT htF htT]
  simpa only [oldValue, eval_eq_orSet] using cross_le color (vars s) (vars t) x

lemma newValue_pair_eq_oldValue (color : Fin n → Bool) (s t sFalse sTrue tFalse tTrue : PrivateColorTree.Tree n)
    (hsF : project color false s = some sFalse) (hsT : project color true s = some sTrue)
    (htF : project color false t = some tFalse) (htT : project color true t = some tTrue)
    (hDisj : Disjoint (vars s) (vars t)) (a b : Fin n) (hColor : color a ≠ color b) :
    newValue sFalse sTrue tFalse tTrue (pairInput a b) = oldValue s t (pairInput a b) := by
  rw [newValue_eq_cross color s t sFalse sTrue tFalse tTrue hsF hsT htF htT]
  simpa only [oldValue, eval_eq_orSet] using cross_pair_eq color (vars s) (vars t) hDisj a b hColor

lemma eval_mono_of_project (color : Fin n → Bool) (b : Bool) (t u : PrivateColorTree.Tree n)
    (hp : project color b t = some u) : eval t (fun v => decide (color v = b)) = true := by
  have hu := (pure_mono color b u (project_pure color b t u hp)).1
  rw [projected_eval_eq color b t u hp] at hu
  have ht := Bool.le_iff_imp.mp
    (orSet_part_le color b (vars t) (fun v => decide (color v = b))) hu
  simpa only [eval_eq_orSet] using ht

lemma newActive_mono (color : Fin n → Bool) (s t sFalse sTrue tFalse tTrue : PrivateColorTree.Tree n)
    (hsF : project color false s = some sFalse) (hsT : project color true s = some sTrue)
    (htF : project color false t = some tFalse) (htT : project color true t = some tTrue) :
    newActive sFalse sTrue tFalse tTrue (fun v => decide (color v = false)) =
        size sFalse + size tFalse ∧
      newActive sFalse sTrue tFalse tTrue (fun v => decide (color v = true)) =
        size sTrue + size tTrue := by
  have hSF := pure_mono color false sFalse (project_pure color false s sFalse hsF)
  have hST := pure_mono color true sTrue (project_pure color true s sTrue hsT)
  have hTF := pure_mono color false tFalse (project_pure color false t tFalse htF)
  have hTT := pure_mono color true tTrue (project_pure color true t tTrue htT)
  simp only [Bool.not_false, Bool.not_true] at hSF hST hTF hTT
  obtain ⟨hsf, hasf, hsf', hasf'⟩ := hSF
  obtain ⟨hst, hast, hst', hast'⟩ := hST
  obtain ⟨htf, hatf, htf', hatf'⟩ := hTF
  obtain ⟨htt, hatt, htt', hatt'⟩ := hTT
  constructor <;> simp only [newActive, newValue, hsf, hasf, hsf', hasf', hst, hast,
    hst', hast', htf, hatf, htf', hatf', htt, hatt, htt', hatt',
    Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte, Nat.add_zero, Nat.zero_add]

lemma newActive_mono_add_three_le (color : Fin n → Bool)
    (s t sFalse sTrue tFalse tTrue : PrivateColorTree.Tree n)
    (hsF : project color false s = some sFalse) (hsT : project color true s = some sTrue)
    (htF : project color false t = some tFalse) (htT : project color true t = some tTrue)
    (b : Bool) :
    newActive sFalse sTrue tFalse tTrue (fun v => decide (color v = b)) + 3 ≤
      oldActive s t (fun v => decide (color v = b)) := by
  obtain ⟨hNF, hNT⟩ := newActive_mono color s t sFalse sTrue tFalse tTrue hsF hsT htF htT
  cases b
  · have hs := mono_active_strict color false s sFalse sTrue hsF hsT
    have ht := mono_active_strict color false t tFalse tTrue htF htT
    rw [hNF]
    simp only [oldActive, oldValue, eval_mono_of_project color false s sFalse hsF,
      eval_mono_of_project color false t tFalse htF, Bool.true_and, ↓reduceIte]
    omega
  · have hs := mono_active_strict color true s sTrue sFalse hsT hsF
    have ht := mono_active_strict color true t tTrue tFalse htT htF
    rw [hNT]
    simp only [oldActive, oldValue, eval_mono_of_project color true s sTrue hsT,
      eval_mono_of_project color true t tTrue htT, Bool.true_and, ↓reduceIte]
    omega

lemma newActive_mono_total_add_six_le (color : Fin n → Bool)
    (s t sFalse sTrue tFalse tTrue : PrivateColorTree.Tree n)
    (hsF : project color false s = some sFalse) (hsT : project color true s = some sTrue)
    (htF : project color false t = some tFalse) (htT : project color true t = some tTrue) :
    newActive sFalse sTrue tFalse tTrue (fun v => decide (color v = false)) +
        newActive sFalse sTrue tFalse tTrue (fun v => decide (color v = true)) + 6 ≤
      oldActive s t (fun v => decide (color v = false)) +
        oldActive s t (fun v => decide (color v = true)) := by
  have hF := newActive_mono_add_three_le color s t sFalse sTrue tFalse tTrue hsF hsT htF htT false
  have hT := newActive_mono_add_three_le color s t sFalse sTrue tFalse tTrue hsF hsT htF htT true
  omega

end PEqualNP.Outside.L_meta_3566.PrivateColorShell

namespace PEqualNP.Outside.L_meta_3566.PrivateCode

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.AO2Upper

abbrev Code := ℕ × (ℕ → List Gate × ℕ)

abbrev Code.size (c : Code) : ℕ := c.1

abbrev Code.emit (c : Code) : ℕ → List Gate × ℕ := c.2

def Valid (n : ℕ) (c : Code) (F : (Fin n → Bool) → Bool)
    (A : (Fin n → Bool) → ℕ) : Prop :=
  ∀ m, n ≤ m → Good m (c.emit m).1 ∧ (c.emit m).1.length = c.size ∧
    (c.emit m).2 < m + c.size ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom (c.emit m).1 w).getD (c.emit m).2 false = F (fun i => w.getD i.val false) ∧
      (wiresFrom (c.emit m).1 w).count true = w.count true + A (fun i => w.getD i.val false)

def ofTree {n : ℕ} (t : PrivateColorTree.Tree n) : Code :=
  ⟨PrivateColorTree.size t, PrivateColorTree.emit t⟩

lemma valid_ofTree {n : ℕ} (t : PrivateColorTree.Tree n) :
    Valid n (ofTree t) (PrivateColorTree.eval t) (PrivateColorTree.activeCount t) := by
  intro m hm
  obtain ⟨hg, ho⟩ := PrivateColorTree.emit_good t m hm
  exact ⟨hg, PrivateColorTree.emit_length t m, ho,
    fun w hw => PrivateColorTree.emit_values t m hm w hw⟩

def binary (op : GateOp) (a b : Code) : Code :=
  ⟨a.size + b.size + 1, fun m =>
    let ea := a.emit m
    let eb := b.emit (m + a.size)
    (ea.1 ++ eb.1 ++ [⟨op, [ea.2, eb.2]⟩], m + a.size + b.size)⟩

lemma valid_binary {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (f : Bool → Bool → Bool) (hf : ∀ a b, op.eval [a, b] = f a b)
    (a b : Code) (F H : (Fin n → Bool) → Bool) (A B : (Fin n → Bool) → ℕ)
    (ha : Valid n a F A) (hb : Valid n b H B) :
    Valid n (binary op a b) (fun x => f (F x) (H x))
      (fun x => A x + B x + if f (F x) (H x) then 1 else 0) := by
  intro m hm
  obtain ⟨hga, hla, hoa, hva⟩ := ha m hm
  obtain ⟨hgb, hlb, hob, hvb⟩ := hb (m + a.size) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Good m ((a.emit m).1 ++ (b.emit (m + a.size)).1 ++
      [⟨op, [(a.emit m).2, (b.emit (m + a.size)).2]⟩])
    apply good_append
    · apply good_append _ _ _ hga
      simpa only [hla] using hgb
    · refine ⟨⟨hop, rfl, ?_⟩, True.intro⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [List.length_append, hla, hlb]
      rcases hi with rfl | rfl <;> omega
  · simp only [binary, List.length_append, List.length_singleton, hla, hlb]
  · change m + a.size + b.size < m + (a.size + b.size + 1)
    omega
  · intro w hw
    let ea := a.emit m
    let eb := b.emit (m + a.size)
    let w1 := wiresFrom ea.1 w
    let w2 := wiresFrom eb.1 w1
    let x : Fin n → Bool := fun i => w.getD i.val false
    have hlen1 : w1.length = m + a.size := by
      rw [length_wiresFrom, hw, hla]
    have hlen2 : w2.length = m + a.size + b.size := by
      rw [length_wiresFrom, hlen1, hlb]
    obtain ⟨hva', hca⟩ := hva w hw
    obtain ⟨hvb', hcb⟩ := hvb w1 hlen1
    have hx : (fun i : Fin n => w1.getD i.val false) = x := by
      funext i
      exact getD_wiresFrom ea.1 w i.val (by rw [hw]; have := i.isLt; omega)
    rw [hx] at hvb' hcb
    have hleft : w2.getD ea.2 false = F x := by
      rw [getD_wiresFrom eb.1 w1 ea.2 (by rw [hlen1]; exact hoa)]
      exact hva'
    have hright : w2.getD eb.2 false = H x := hvb'
    have hval : op.eval ([ea.2, eb.2].map fun i => w2.getD i false) = f (F x) (H x) := by
      simp only [List.map_cons, List.map_nil, hf, hleft, hright]
    have hrun : wiresFrom ((binary op a b).emit m).1 w = w2 ++ [f (F x) (H x)] := by
      change wiresFrom (ea.1 ++ eb.1 ++ [⟨op, [ea.2, eb.2]⟩]) w = _
      rw [wiresFrom_append, wiresFrom_append]
      change w2 ++ [op.eval ([ea.2, eb.2].map fun i => w2.getD i false)] = _
      rw [hval]
    constructor
    · rw [hrun]
      change (w2 ++ [f (F x) (H x)]).getD (m + a.size + b.size) false = _
      rw [← hlen2, getD_snoc_eq]
    · rw [hrun, List.count_append]
      change w2.count true + [f (F x) (H x)].count true =
        w.count true + (A x + B x + if f (F x) (H x) then 1 else 0)
      change w1.count true = w.count true + A x at hca
      change w2.count true = w1.count true + B x at hcb
      cases f (F x) (H x) <;> simp <;> omega

lemma valid_active_congr {n : ℕ} {c : Code} {F : (Fin n → Bool) → Bool}
    {A B : (Fin n → Bool) → ℕ} (h : Valid n c F A) (hAB : ∀ x, A x = B x) :
    Valid n c F B := by
  have heq : A = B := funext hAB
  exact heq ▸ h

def circuit (n : ℕ) (c : Code) : Circuit := ⟨(c.emit n).1, (c.emit n).2⟩

lemma circuit_spec {n : ℕ} (c : Code) (F : (Fin n → Bool) → Bool)
    (A : (Fin n → Bool) → ℕ) (h : Valid n c F A) :
    IsAO2 n (circuit n c) ∧ (circuit n c).size = c.size ∧
      circuitFun n (circuit n c) = F ∧
      ∀ x : Fin n → Bool, ((circuit n c).wires (List.ofFn x)).count true =
        (List.ofFn x).count true + A x := by
  obtain ⟨hg, hl, _, hv⟩ := h n le_rfl
  refine ⟨good_ao2 n _ _ hg, hl, ?_, ?_⟩
  · funext x
    have hx := (hv (List.ofFn x) (by simp)).1
    change (wiresFrom (c.emit n).1 (List.ofFn x)).getD (c.emit n).2 false = _
    simpa only [getD_ofFn] using hx
  · intro x
    have hx := (hv (List.ofFn x) (by simp)).2
    change (wiresFrom (c.emit n).1 (List.ofFn x)).count true = _
    simpa only [getD_ofFn] using hx

end PEqualNP.Outside.L_meta_3566.PrivateCode

namespace PEqualNP.Outside.L_meta_3566.PrivateColorShell

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PrivateColorTree PrivateCode

variable {n : ℕ}

def oldCode (s t : Tree n) : Code := binary GateOp.and (ofTree s) (ofTree t)

def newCode (sFalse sTrue tFalse tTrue : Tree n) : Code :=
  binary GateOp.or (binary GateOp.and (ofTree sFalse) (ofTree tTrue))
    (binary GateOp.and (ofTree sTrue) (ofTree tFalse))

lemma oldCode_valid (s t : Tree n) :
    Valid n (oldCode s t) (oldValue s t) (oldActive s t) :=
  valid_binary GateOp.and (Or.inl rfl) (· && ·) (by intros; simp [GateOp.eval])
    (ofTree s) (ofTree t) (eval s) (eval t) (activeCount s) (activeCount t)
    (valid_ofTree s) (valid_ofTree t)

lemma newCode_valid (sFalse sTrue tFalse tTrue : Tree n) :
    Valid n (newCode sFalse sTrue tFalse tTrue) (newValue sFalse sTrue tFalse tTrue)
      (newActive sFalse sTrue tFalse tTrue) := by
  have h1 := valid_binary GateOp.and (Or.inl rfl) (· && ·) (by intros; simp [GateOp.eval])
    (ofTree sFalse) (ofTree tTrue) (eval sFalse) (eval tTrue)
    (activeCount sFalse) (activeCount tTrue) (valid_ofTree sFalse) (valid_ofTree tTrue)
  have h2 := valid_binary GateOp.and (Or.inl rfl) (· && ·) (by intros; simp [GateOp.eval])
    (ofTree sTrue) (ofTree tFalse) (eval sTrue) (eval tFalse)
    (activeCount sTrue) (activeCount tFalse) (valid_ofTree sTrue) (valid_ofTree tFalse)
  have h := valid_binary GateOp.or (Or.inr rfl) (· || ·) (by intros; simp [GateOp.eval])
    _ _ _ _ _ _ h1 h2
  apply valid_active_congr h
  intro x
  simp only [newActive, newValue]
  ac_rfl

lemma oldCode_size (s t : Tree n) : (oldCode s t).size = oldSize s t := rfl

lemma newCode_size (sFalse sTrue tFalse tTrue : Tree n) :
    (newCode sFalse sTrue tFalse tTrue).size = newSize sFalse sTrue tFalse tTrue := by
  simp only [newCode, binary, ofTree, newSize, Code.size]
  omega

lemma oldCode_root (s t : Tree n) (m : ℕ) :
    ((oldCode s t).emit m).2 = m + oldSize s t - 1 := by
  simp only [oldCode, binary, ofTree, oldSize, Code.size]
  omega

lemma newCode_root (sFalse sTrue tFalse tTrue : Tree n) (m : ℕ) :
    ((newCode sFalse sTrue tFalse tTrue).emit m).2 =
      m + newSize sFalse sTrue tFalse tTrue - 1 := by
  simp only [newCode, binary, ofTree, newSize, Code.size]
  omega

def oldCircuit (s t : Tree n) : Circuit := circuit n (oldCode s t)

def newCircuit (sFalse sTrue tFalse tTrue : Tree n) : Circuit :=
  circuit n (newCode sFalse sTrue tFalse tTrue)

lemma oldCircuit_spec (s t : Tree n) :
    IsAO2 n (oldCircuit s t) ∧ (oldCircuit s t).size = oldSize s t ∧
      circuitFun n (oldCircuit s t) = oldValue s t ∧
      ∀ x : Fin n → Bool, ((oldCircuit s t).wires (List.ofFn x)).count true =
        (List.ofFn x).count true + oldActive s t x :=
  circuit_spec (oldCode s t) _ _ (oldCode_valid s t)

lemma newCircuit_spec (sFalse sTrue tFalse tTrue : Tree n) :
    IsAO2 n (newCircuit sFalse sTrue tFalse tTrue) ∧
      (newCircuit sFalse sTrue tFalse tTrue).size = newSize sFalse sTrue tFalse tTrue ∧
      circuitFun n (newCircuit sFalse sTrue tFalse tTrue) = newValue sFalse sTrue tFalse tTrue ∧
      ∀ x : Fin n → Bool, ((newCircuit sFalse sTrue tFalse tTrue).wires (List.ofFn x)).count true =
        (List.ofFn x).count true + newActive sFalse sTrue tFalse tTrue x := by
  simpa only [newCircuit, newCode_size] using
    circuit_spec (newCode sFalse sTrue tFalse tTrue) _ _ (newCode_valid sFalse sTrue tFalse tTrue)

end PEqualNP.Outside.L_meta_3566.PrivateColorShell

namespace PEqualNP.Outside.L_meta_3566.PrivateColorTree

lemma exists_tree_of_nonempty {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∃ t : Tree n, vars t = S ∧ size t + 1 = S.card := by
  classical
  revert hS
  induction S using Finset.induction_on with
  | empty =>
    intro hS
    exact False.elim (Finset.not_nonempty_empty hS)
  | @insert v S hv ih =>
    intro _
    by_cases hEmpty : S = ∅
    · subst S
      exact ⟨.of v, by simp [vars], by simp [size]⟩
    · obtain ⟨t, ht, hSize⟩ := ih (Finset.nonempty_iff_ne_empty.mpr hEmpty)
      refine ⟨.mul (.of v) t, ?_, ?_⟩
      · simp [vars, ht]
      · simp only [size, Nat.zero_add, Finset.card_insert_of_notMem hv]
        omega

lemma pure_of_vars {n : ℕ} (color : Fin n → Bool) (b : Bool) (t : Tree n)
    (hColor : ∀ v ∈ vars t, color v = b) : Pure color b t := by
  induction t with
  | of v => exact hColor v (by simp [vars])
  | mul l r hl hr =>
    exact ⟨hl (fun v hv => hColor v (Finset.mem_union_left _ hv)),
      hr (fun v hv => hColor v (Finset.mem_union_right _ hv))⟩

lemma exists_pure_tree_of_nonempty {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (color : Fin n → Bool) (b : Bool) (hColor : ∀ v ∈ S, color v = b) :
    ∃ t : Tree n, vars t = S ∧ size t + 1 = S.card ∧ Pure color b t := by
  obtain ⟨t, ht, hSize⟩ := exists_tree_of_nonempty S hS
  refine ⟨t, ht, hSize, pure_of_vars color b t ?_⟩
  intro v hv
  exact hColor v (ht ▸ hv)

end PEqualNP.Outside.L_meta_3566.PrivateColorTree

namespace PEqualNP.Outside.L_meta_3566.PrivateColorShell

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PrivateColorTree

lemma part_card_add {n : ℕ} (color : Fin n → Bool) (S : Finset (Fin n)) :
    (part color false S).card + (part color true S).card = S.card := by
  have hneg : S.filter (fun v => ¬color v = false) = part color true S := by
    ext v
    cases hv : color v <;> simp [part, hv]
  have h : (S.filter fun v => color v = false).card +
      (S.filter fun v => ¬color v = false).card = S.card :=
    Finset.card_filter_add_card_filter_not _
  rw [hneg] at h
  exact h

lemma exists_cross_circuit {n : ℕ} (color : Fin n → Bool) (S T : Finset (Fin n))
    (hSF : (part color false S).Nonempty) (hST : (part color true S).Nonempty)
    (hTF : (part color false T).Nonempty) (hTT : (part color true T).Nonempty) :
    ∃ Q : Circuit, IsAO2 n Q ∧ Q.size + 1 = S.card + T.card ∧
      circuitFun n Q = cross color S T ∧ Q.output < n + Q.size ∧
      ∀ b : Bool, (WireProfile.trueGates Q (MonoNormalize.input color b)).card + 2 =
        (part color b S).card + (part color b T).card := by
  obtain ⟨sf, hvSF, hsSF, hpSF⟩ := exists_pure_tree_of_nonempty
    (part color false S) hSF color false (by intro v hv; exact (Finset.mem_filter.mp hv).2)
  obtain ⟨st, hvST, hsST, hpST⟩ := exists_pure_tree_of_nonempty
    (part color true S) hST color true (by intro v hv; exact (Finset.mem_filter.mp hv).2)
  obtain ⟨tf, hvTF, hsTF, hpTF⟩ := exists_pure_tree_of_nonempty
    (part color false T) hTF color false (by intro v hv; exact (Finset.mem_filter.mp hv).2)
  obtain ⟨tt, hvTT, hsTT, hpTT⟩ := exists_pure_tree_of_nonempty
    (part color true T) hTT color true (by intro v hv; exact (Finset.mem_filter.mp hv).2)
  have hSFpure := pure_mono color false sf hpSF
  have hSTpure := pure_mono color true st hpST
  have hTFpure := pure_mono color false tf hpTF
  have hTTpure := pure_mono color true tt hpTT
  simp only [Bool.not_false, Bool.not_true] at hSFpure hSTpure hTFpure hTTpure
  obtain ⟨hsf, hasf, hsf', hasf'⟩ := hSFpure
  obtain ⟨hst, hast, hst', hast'⟩ := hSTpure
  obtain ⟨htf, hatf, htf', hatf'⟩ := hTFpure
  obtain ⟨htt, hatt, htt', hatt'⟩ := hTTpure
  have hMonos :
      newActive sf st tf tt (fun v => decide (color v = false)) = size sf + size tf ∧
      newActive sf st tf tt (fun v => decide (color v = true)) = size st + size tt := by
    constructor <;> simp only [newActive, newValue, hsf, hasf, hsf', hasf', hst, hast,
      hst', hast', htf, hatf, htf', hatf', htt, hatt, htt', hatt',
      Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_eq_true,
      ↓reduceIte, Nat.add_zero, Nat.zero_add]
  have hMonoF : newActive sf st tf tt (MonoNormalize.input color false) = size sf + size tf :=
    hMonos.1
  have hMonoT : newActive sf st tf tt (MonoNormalize.input color true) = size st + size tt :=
    hMonos.2
  have hCardS := part_card_add color S
  have hCardT := part_card_add color T
  obtain ⟨hQ, hSize, hFun, hCount⟩ := newCircuit_spec sf st tf tt
  let Q := newCircuit sf st tf tt
  refine ⟨Q, hQ, ?_, ?_, ?_, ?_⟩
  · change (newCircuit sf st tf tt).size + 1 = _
    rw [hSize]
    simp only [newSize]
    omega
  · funext x
    change circuitFun n (newCircuit sf st tf tt) x = _
    rw [hFun]
    simp only [newValue, PrivateColorTree.eval_eq_orSet, hvSF, hvST, hvTF, hvTT, cross]
  · change ((newCode sf st tf tt).emit n).2 < n + (newCircuit sf st tf tt).size
    rw [newCode_root, hSize]
    have hpos : 0 < newSize sf st tf tt := by simp [newSize]
    omega
  · intro b
    have hWire := WireProfile.wire_count Q (MonoNormalize.input color b)
    have hCode := hCount (MonoNormalize.input color b)
    dsimp only [Q] at hWire ⊢
    cases b
    · rw [hMonoF] at hCode
      omega
    · rw [hMonoT] at hCode
      omega

end PEqualNP.Outside.L_meta_3566.PrivateColorShell

namespace PEqualNP.Outside.L_meta_3566.PrivateColorShell

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PrivateColorTree

lemma actual_projection {n : ℕ} (color : Fin n → Bool)
    (s t sFalse sTrue tFalse tTrue : PrivateColorTree.Tree n)
    (hsF : project color false s = some sFalse) (hsT : project color true s = some sTrue)
    (htF : project color false t = some tFalse) (htT : project color true t = some tTrue)
    (hDisj : Disjoint (vars s) (vars t)) :
    IsAO2 n (newCircuit sFalse sTrue tFalse tTrue) ∧
      (newCircuit sFalse sTrue tFalse tTrue).size = (oldCircuit s t).size ∧
      (∀ x, circuitFun n (newCircuit sFalse sTrue tFalse tTrue) x ≤
        circuitFun n (oldCircuit s t) x) ∧
      (∀ a b : Fin n, color a ≠ color b →
        circuitFun n (newCircuit sFalse sTrue tFalse tTrue) (pairInput a b) =
          circuitFun n (oldCircuit s t) (pairInput a b)) ∧
      MonoNormalize.mass color (newCircuit sFalse sTrue tFalse tTrue) + 6 ≤
        MonoNormalize.mass color (oldCircuit s t) := by
  obtain ⟨hOld, hOldSize, hOldFun, hOldCount⟩ := oldCircuit_spec s t
  obtain ⟨hNew, hNewSize, hNewFun, hNewCount⟩ := newCircuit_spec sFalse sTrue tFalse tTrue
  refine ⟨hNew, ?_, ?_, ?_, ?_⟩
  · rw [hNewSize, hOldSize]
    exact projection_size_eq color s t sFalse sTrue tFalse tTrue hsF hsT htF htT
  · intro x
    rw [hNewFun, hOldFun]
    exact newValue_le_oldValue color s t sFalse sTrue tFalse tTrue hsF hsT htF htT x
  · intro a b hColor
    rw [hNewFun, hOldFun]
    exact newValue_pair_eq_oldValue color s t sFalse sTrue tFalse tTrue hsF hsT htF htT hDisj a b hColor
  · unfold MonoNormalize.mass
    rw [hNewCount, hNewCount, hOldCount, hOldCount]
    have h := newActive_mono_total_add_six_le color s t sFalse sTrue tFalse tTrue hsF hsT htF htT
    change newActive sFalse sTrue tFalse tTrue (MonoNormalize.input color false) +
      newActive sFalse sTrue tFalse tTrue (MonoNormalize.input color true) + 6 ≤
      oldActive s t (MonoNormalize.input color false) +
      oldActive s t (MonoNormalize.input color true) at h
    omega

end PEqualNP.Outside.L_meta_3566.PrivateColorShell

namespace PEqualNP.Outside.L_meta_3566.PrivateDagBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma root_on_mono (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (K : Finset ℕ) (r : ℕ) (hK : ∀ j ∈ K, j < C.size)
    (hOr : ∀ j ∈ K, (gateAt C j).op = GateOp.or)
    (hRead : ∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, opnd C h b = n + g)
    (S : Finset (Fin n))
    (hInputs : ∀ v ∈ S, ∃ g ∈ K, ∃ b : Fin 2, opnd C g b = v.val)
    (color : Fin n → Bool) (hBoth : ∀ b : Bool, ∃ v ∈ S, color v = b) (b : Bool) :
    gateVal n C r (MonoNormalize.input color b) = true := by
  obtain ⟨v, hvS, hvColor⟩ := hBoth b
  obtain ⟨g, hg, c, hc⟩ := hInputs v hvS
  have hOn : wireVal n C (opnd C g c) (MonoNormalize.input color b) = true := by
    rw [hc, LeafStep.Pruning.wireVal_lt C v.val v.isLt]
    simp [MonoNormalize.input, hvColor]
  have hgOn := PrivateCone.or_gate_true_of_port n C hC g (hK g hg) (hOr g hg) _ c hOn
  exact PrivateCone.root_true_of_gate_true n C hC K r hK hOr hRead _ g hg hgOn

lemma shell_budget (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (K₁ K₂ : Finset ℕ) (r₁ r₂ q : ℕ) (hr₁ : r₁ ∈ K₁) (hr₂ : r₂ ∈ K₂)
    (hK₁ : ∀ j ∈ K₁, j < C.size) (hK₂ : ∀ j ∈ K₂, j < C.size) (hq : q < C.size)
    (hOr₁ : ∀ j ∈ K₁, (gateAt C j).op = GateOp.or)
    (hOr₂ : ∀ j ∈ K₂, (gateAt C j).op = GateOp.or)
    (hRead₁ : ∀ g ∈ K₁.erase r₁, ∃ h ∈ K₁, ∃ b : Fin 2, opnd C h b = n + g)
    (hRead₂ : ∀ g ∈ K₂.erase r₂, ∃ h ∈ K₂, ∃ b : Fin 2, opnd C h b = n + g)
    (hDisj : Disjoint K₁ K₂) (hqNot : q ∉ K₁ ∪ K₂)
    (S T : Finset (Fin n))
    (hInputs₁ : ∀ v ∈ S, ∃ g ∈ K₁, ∃ b : Fin 2, opnd C g b = v.val)
    (hInputs₂ : ∀ v ∈ T, ∃ g ∈ K₂, ∃ b : Fin 2, opnd C g b = v.val)
    (color : Fin n → Bool)
    (hBothS : ∀ b : Bool, ∃ v ∈ S, color v = b)
    (hBothT : ∀ b : Bool, ∃ v ∈ T, color v = b)
    (hQValue : ∀ x, gateVal n C q x = (gateVal n C r₁ x && gateVal n C r₂ x))
    (Q : Circuit) (hSize : Q.size + 1 = S.card + T.card)
    (hActive : ∀ b : Bool, (WireProfile.trueGates Q (MonoNormalize.input color b)).card + 2 =
      (S.filter fun v => color v = b).card + (T.filter fun v => color v = b).card) :
    (insert q (K₁ ∪ K₂)) ⊆ Finset.range C.size ∧
      Q.size ≤ (insert q (K₁ ∪ K₂)).card ∧
      ∀ b : Bool, (WireProfile.trueGates Q (MonoNormalize.input color b)).card + 3 ≤
        ((insert q (K₁ ∪ K₂)).filter fun j => gateVal n C j (MonoNormalize.input color b) = true).card := by
  classical
  have hCard : (insert q (K₁ ∪ K₂)).card = K₁.card + K₂.card + 1 := by
    rw [Finset.card_insert_of_notMem hqNot, Finset.card_union_of_disjoint hDisj]
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    apply Finset.mem_range.mpr
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hq
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact hK₁ j hj
      · exact hK₂ j hj
  · have hs := PrivateCone.input_card_le_gates_add_one n K₁ r₁ hr₁ (opnd C) S hInputs₁ hRead₁
    have ht := PrivateCone.input_card_le_gates_add_one n K₂ r₂ hr₂ (opnd C) T hInputs₂ hRead₂
    omega
  · intro b
    have hs := PrivateCone.monochrome_support_card_le_active_gates n C hC K₁ r₁ hr₁ hK₁ hOr₁ hRead₁
      S hInputs₁ color hBothS b
    have ht := PrivateCone.monochrome_support_card_le_active_gates n C hC K₂ r₂ hr₂ hK₂ hOr₂ hRead₂
      T hInputs₂ color hBothT b
    have hqOn : gateVal n C q (MonoNormalize.input color b) = true := by
      rw [hQValue, root_on_mono n C hC K₁ r₁ hK₁ hOr₁ hRead₁ S hInputs₁ color hBothS b,
        root_on_mono n C hC K₂ r₂ hK₂ hOr₂ hRead₂ T hInputs₂ color hBothT b]
      rfl
    let A := K₁.filter fun j => gateVal n C j (MonoNormalize.input color b) = true
    let B := K₂.filter fun j => gateVal n C j (MonoNormalize.input color b) = true
    have hAB : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro j hjA hjB
      exact Finset.disjoint_left.mp hDisj (Finset.mem_filter.mp hjA).1 (Finset.mem_filter.mp hjB).1
    have hqAB : q ∉ A ∪ B := by
      intro hqMem
      apply hqNot
      rcases Finset.mem_union.mp hqMem with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mp h).1
      · exact Finset.mem_union_right _ (Finset.mem_filter.mp h).1
    have hFilter : ((insert q (K₁ ∪ K₂)).filter fun j =>
        gateVal n C j (MonoNormalize.input color b) = true) = insert q (A ∪ B) := by
      simp only [Finset.filter_insert, hqOn, ite_true, Finset.filter_union]
      rfl
    rw [hFilter, Finset.card_insert_of_notMem hqAB, Finset.card_union_of_disjoint hAB]
    change _ ≤ A.card + B.card + 1
    have hNew := hActive b
    change (S.filter fun v => color v = b).card ≤ A.card at hs
    change (T.filter fun v => color v = b).card ≤ B.card at ht
    omega

lemma mono_mass_gap_of_counts {n : ℕ} (color : Fin n → Bool) (C Q : Circuit) (J : Finset ℕ)
    (M : ℕ)
    (hM : M = (J.filter fun j => gateVal n C j (MonoNormalize.input color false) = true).card +
      (J.filter fun j => gateVal n C j (MonoNormalize.input color true) = true).card)
    (hGap : ∀ b : Bool, (WireProfile.trueGates Q (MonoNormalize.input color b)).card + 3 ≤
      (J.filter fun j => gateVal n C j (MonoNormalize.input color b) = true).card) :
    MonoNormalize.mass color Q + 6 ≤ n + M := by
  have hFalse := hGap false
  have hTrue := hGap true
  have hInputs := MonoNormalize.mono_input_count color
  unfold MonoNormalize.mass
  rw [WireProfile.wire_count, WireProfile.wire_count]
  omega

end PEqualNP.Outside.L_meta_3566.PrivateDagBudget

namespace PEqualNP.Outside.L_meta_3566.PrivateCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open LeafStep.Pruning

lemma gate_all_true (n : ℕ) (C : Circuit) (hC : IsAO2 n C) :
    ∀ j, j < C.size → gateVal n C j (fun _ => true) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    rw [gate_eq C hC j hj]
    have hsrc (b : Fin 2) : wireVal n C (opnd C j b) (fun _ => true) = true := by
      by_cases hw : opnd C j b < n
      · rw [wireVal_lt C _ hw]
      · have hback := hC.2.1 j hj (opnd C j b) (port_mem n C hC j hj b)
        have he : n + (opnd C j b - n) = opnd C j b := by omega
        rw [← he]
        change gateVal n C (opnd C j b - n) (fun _ => true) = true
        exact ih _ (by omega) (by omega)
    rw [hsrc 0, hsrc 1]
    simp [opv]

lemma closed_cones_disjoint_of_supports (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (K₁ K₂ : Finset ℕ)
    (hK₁ : ∀ j ∈ K₁, j < C.size) (hK₂ : ∀ j ∈ K₂, j < C.size)
    (hClosed₁ : ∀ j ∈ K₁, ∀ b : Fin 2, n ≤ opnd C j b → opnd C j b - n ∈ K₁)
    (hClosed₂ : ∀ j ∈ K₂, ∀ b : Fin 2, n ≤ opnd C j b → opnd C j b - n ∈ K₂)
    (S T : Finset (Fin n)) (hDisj : Disjoint S T)
    (hInputs₁ : ∀ j ∈ K₁, ∀ b : Fin 2, ∀ hw : opnd C j b < n,
      (⟨opnd C j b, hw⟩ : Fin n) ∈ S)
    (hInputs₂ : ∀ j ∈ K₂, ∀ b : Fin 2, ∀ hw : opnd C j b < n,
      (⟨opnd C j b, hw⟩ : Fin n) ∈ T) : Disjoint K₁ K₂ := by
  classical
  apply Finset.disjoint_left.mpr
  intro j hj₁ hj₂
  let x : Fin n → Bool := fun v => decide (v ∈ S)
  have hx₁ : ∀ v ∈ S, x v = (fun _ : Fin n => true) v := by
    intro v hv
    exact decide_eq_true hv
  have hx₂ : ∀ v ∈ T, x v = (fun _ : Fin n => false) v := by
    intro v hv
    have hn : v ∉ S := fun h => Finset.disjoint_left.mp hDisj h hv
    exact decide_eq_false hn
  have h₁ := cone_agree n C hC K₁ hK₁ hClosed₁ S hInputs₁ x (fun _ => true) hx₁ j hj₁
  have h₂ := cone_agree n C hC K₂ hK₂ hClosed₂ T hInputs₂ x (fun _ => false) hx₂ j hj₂
  rw [gate_all_true n C hC j (hK₁ j hj₁)] at h₁
  rw [gate_zero n C hC j (hK₂ j hj₂)] at h₂
  exact Bool.noConfusion (h₁.symm.trans h₂)

end PEqualNP.Outside.L_meta_3566.PrivateCone

namespace PEqualNP.Outside.L_meta_3566.PrivateMixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

def OrCone {n : ℕ} (C : Circuit) (K : Finset ℕ) (r : ℕ) (S : Finset (Fin n)) : Prop :=
  r ∈ K ∧
  (∀ j ∈ K, j < C.size) ∧
  (∀ j ∈ K, (gateAt C j).op = GateOp.or) ∧
  (∀ j ∈ K, ∀ b : Fin 2, n ≤ opnd C j b → opnd C j b - n ∈ K) ∧
  (∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, opnd C h b = n + g) ∧
  (∀ v ∈ S, ∃ g ∈ K, ∃ b : Fin 2, opnd C g b = v.val) ∧
  (∀ j ∈ K, ∀ b : Fin 2, ∀ hw : opnd C j b < n, (⟨opnd C j b, hw⟩ : Fin n) ∈ S)

lemma no_private_disjoint_mixed_or_cones {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hBip : ∀ a b : Fin n, G.Adj a b → color a ≠ color b)
    (C : Circuit) (hMin : MonoNormalize.IsMonoJunkLeastAO G color C)
    (K₁ K₂ : Finset ℕ) (r₁ r₂ H : ℕ) (S T : Finset (Fin n))
    (hCone₁ : OrCone C K₁ r₁ S) (hCone₂ : OrCone C K₂ r₂ T)
    (hH : H < C.size) (hAnd : gateAt C H = ⟨GateOp.and, [n + r₁, n + r₂]⟩)
    (hDisjS : Disjoint S T)
    (hBothS : ∀ b : Bool, ∃ v ∈ S, color v = b)
    (hBothT : ∀ b : Bool, ∃ v ∈ T, color v = b)
    (hPrivate : ∀ i < C.size, i ∉ insert H (K₁ ∪ K₂) → ∀ j ∈ insert H (K₁ ∪ K₂),
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ insert H (K₁ ∪ K₂), C.output = n + j → j = H) : False := by
  classical
  obtain ⟨hr₁, hK₁, hOr₁, hClosed₁, hRead₁, hInputs₁, hAll₁⟩ := hCone₁
  obtain ⟨hr₂, hK₂, hOr₂, hClosed₂, hRead₂, hInputs₂, hAll₂⟩ := hCone₂
  have hDisjK : Disjoint K₁ K₂ :=
    PrivateCone.closed_cones_disjoint_of_supports n C hMin.1.1 K₁ K₂ hK₁ hK₂ hClosed₁ hClosed₂
      S T hDisjS hAll₁ hAll₂
  have hHNot : H ∉ K₁ ∪ K₂ := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · have hh := hOr₁ H h
      rw [hAnd] at hh
      cases hh
    · have hh := hOr₂ H h
      rw [hAnd] at hh
      cases hh
  have hPartsS (b : Bool) : (PrivateColorShell.part color b S).Nonempty := by
    obtain ⟨v, hv, hc⟩ := hBothS b
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hc⟩⟩
  have hPartsT (b : Bool) : (PrivateColorShell.part color b T).Nonempty := by
    obtain ⟨v, hv, hc⟩ := hBothT b
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hc⟩⟩
  obtain ⟨Q, hQ, hQSize, hQFun, hq, hQActive⟩ :=
    PrivateColorShell.exists_cross_circuit color S T (hPartsS false) (hPartsS true)
      (hPartsT false) (hPartsT true)
  have hHValue (x : Fin n → Bool) :
      gateVal n C H x = (gateVal n C r₁ x && gateVal n C r₂ x) := by
    have heq := LeafStep.Pruning.gate_eq C hMin.1.1 H hH x
    simp only [hAnd, LeafStep.Pruning.isA, LeafStep.Pruning.opv, opnd] at heq
    exact heq
  have hHFun (x : Fin n → Bool) :
      gateVal n C H x = (OnePureFrontier.orSet S x && OnePureFrontier.orSet T x) := by
    rw [hHValue, PrivateCone.closed_or_cone_value n C hMin.1.1 K₁ r₁ hr₁ hK₁ hOr₁ hClosed₁
      hRead₁ S hInputs₁ hAll₁, PrivateCone.closed_or_cone_value n C hMin.1.1 K₂ r₂ hr₂ hK₂ hOr₂
      hClosed₂ hRead₂ T hInputs₂ hAll₂]
  obtain ⟨hJ, hSize, hActive⟩ := PrivateDagBudget.shell_budget n C hMin.1.1 K₁ K₂ r₁ r₂ H
    hr₁ hr₂ hK₁ hK₂ hH hOr₁ hOr₂ hRead₁ hRead₂ hDisjK hHNot S T hInputs₁ hInputs₂
    color hBothS hBothT hHValue Q hQSize hQActive
  have hGap := PrivateDagBudget.mono_mass_gap_of_counts color C Q (insert H (K₁ ∪ K₂))
    (PrivateCopy.privateMass color C (insert H (K₁ ∪ K₂)))
    (PrivateCopy.privateMass_eq_counts color C (insert H (K₁ ∪ K₂)) hJ) hActive
  apply PrivateCopy.not_of_mono_minimum G color Q C (insert H (K₁ ∪ K₂)) H hMin hQ hq hJ
    hPrivate hOutput
  · intro x
    rw [hQFun, hHFun]
    exact PrivateColorShell.cross_le color S T x
  · intro a b hab
    rw [hQFun, hHFun]
    exact PrivateColorShell.cross_pair_eq color S T hDisjS a b (hBip a b hab)
  · intro b
    rw [hQFun]
    exact PrivateColorShell.cross_mono_false color b S T
  · exact hSize
  · omega

end PEqualNP.Outside.L_meta_3566.PrivateMixed

namespace PEqualNP.Outside.L_meta_3566.PrivateCopy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma exists_private_replacement_size {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Q C : Circuit) (J : Finset ℕ) (H : ℕ)
    (hQ : IsAO2 n Q) (hC : IsAO2 n C) (hq : Q.output < n + Q.size)
    (hCFun : circuitFun n C = graphFun G ∅) (hJ : J ⊆ Finset.range C.size)
    (hPrivate : ∀ i < C.size, i ∉ J → ∀ j ∈ J,
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ J, C.output = n + j → j = H)
    (hBase : ∀ x : Fin n → Bool, circuitFun n Q x ≤ gateVal n C H x)
    (hEdges : ∀ a b : Fin n, G.Adj a b →
      circuitFun n Q (pairInput a b) = gateVal n C H (pairInput a b)) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size + J.card ≤ C.size + Q.size := by
  classical
  let E := compiled n Q C J
  let K : Finset ℕ := J.image fun i => Q.size + i
  have hE : IsAO2 n E := compiled_ao n Q C J hQ hC hq
  have hEFun : circuitFun n E = graphFun G ∅ :=
    compiled_correct G Q C J H hQ hC hq hCFun hPrivate hOutput hBase hEdges
  have hK : K ⊆ Finset.range E.size := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hi' : i < C.size := Finset.mem_range.mp (hJ hi)
    apply Finset.mem_range.mpr
    change Q.size + i < (compiled n Q C J).size
    rw [compiled_size]
    omega
  have hKcard : K.card = J.card := by
    dsimp [K]
    apply Finset.card_image_of_injOn
    intro i hi j hj he
    exact Nat.add_left_cancel he
  have hEarlier : ∀ k ∈ K, Q.output < n + k := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    omega
  have hAlias : ∀ k ∈ K, ∀ x : Fin n → Bool,
      wireVal n E (n + k) x = wireVal n E Q.output x := by
    intro k hk x
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hi' : i < C.size := Finset.mem_range.mp (hJ hi)
    have hv := copied_alias n Q C J hQ hC hq i hi' hi x
    have hRoot : wireVal n E Q.output x = circuitFun n Q x :=
      prefix_wire n Q C J x Q.output hq
    exact hv.trans hRoot.symm
  obtain ⟨D, hD, hFun, hSizeD⟩ :=
    Absorption.erase_alias_family n E hE K hK Q.output hEarlier hAlias
  have hESize : E.size = Q.size + C.size := compiled_size n Q C J
  refine ⟨D, hD, hFun.trans hEFun, ?_⟩
  omega

lemma not_of_least_size {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Q C : Circuit) (J : Finset ℕ) (H : ℕ) (hLeast : IsLeastAO G C)
    (hQ : IsAO2 n Q) (hq : Q.output < n + Q.size) (hJ : J ⊆ Finset.range C.size)
    (hPrivate : ∀ i < C.size, i ∉ J → ∀ j ∈ J,
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ J, C.output = n + j → j = H)
    (hBase : ∀ x : Fin n → Bool, circuitFun n Q x ≤ gateVal n C H x)
    (hEdges : ∀ a b : Fin n, G.Adj a b →
      circuitFun n Q (pairInput a b) = gateVal n C H (pairInput a b))
    (hSize : Q.size < J.card) : False := by
  obtain ⟨D, hD, hFun, hSizeD⟩ := exists_private_replacement_size G Q C J H hQ hLeast.1 hq
    hLeast.2.1 hJ hPrivate hOutput hBase hEdges
  have hMin := hLeast.2.2 D hD hFun
  omega

end PEqualNP.Outside.L_meta_3566.PrivateCopy

namespace PEqualNP.Outside.L_meta_3566.PrivateCone

lemma image_card_lt_of_collision {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) (p q : α) (hp : p ∈ A) (hq : q ∈ A)
    (hpq : p ≠ q) (hdup : f p = f q) : (A.image f).card < A.card := by
  have hImage : A.image f = (A.erase p).image f := by
    ext y
    constructor
    · intro hy
      obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hy
      by_cases hap : a = p
      · subst a
        exact Finset.mem_image.mpr ⟨q, Finset.mem_erase.mpr ⟨hpq.symm, hq⟩, hdup.symm.trans hfa⟩
      · exact Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨hap, ha⟩, hfa⟩
    · intro hy
      obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨a, Finset.mem_of_mem_erase ha, hfa⟩
  rw [hImage]
  have hle : ((A.erase p).image f).card ≤ (A.erase p).card := Finset.card_image_le
  have hcard := Finset.card_erase_of_mem hp
  have hpos := Finset.card_pos.mpr ⟨p, hp⟩
  omega

lemma input_card_le_gates_of_duplicate_port (n : ℕ) (K : Finset ℕ) (r : ℕ) (hr : r ∈ K)
    (port : ℕ → Fin 2 → ℕ) (S : Finset (Fin n))
    (hInputs : ∀ v ∈ S, ∃ g ∈ K, ∃ b : Fin 2, port g b = v.val)
    (hRead : ∀ g ∈ K.erase r, ∃ h ∈ K, ∃ b : Fin 2, port h b = n + g)
    (p q : ℕ × Fin 2) (hp : p.1 ∈ K) (hq : q.1 ∈ K)
    (hpq : p ≠ q) (hDup : port p.1 p.2 = port q.1 q.2) :
    S.card ≤ K.card := by
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
  have hpSlot : p ∈ slots := Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩
  have hqSlot : q ∈ slots := Finset.mem_product.mpr ⟨hq, Finset.mem_univ _⟩
  have hImage : I.card < slots.card :=
    image_card_lt_of_collision slots (fun p => port p.1 p.2) p q hpSlot hqSlot hpq hDup
  have hErase := Finset.card_erase_of_mem hr
  have hPos := Finset.card_pos.mpr ⟨r, hr⟩
  omega

lemma two_cone_input_card_le_private_of_duplicate_port (n : ℕ)
    (K₁ K₂ : Finset ℕ) (r₁ r₂ H : ℕ) (port : ℕ → Fin 2 → ℕ)
    (S T : Finset (Fin n))
    (hInputs₁ : ∀ v ∈ S, ∃ g ∈ K₁, ∃ b : Fin 2, port g b = v.val)
    (hInputs₂ : ∀ v ∈ T, ∃ g ∈ K₂, ∃ b : Fin 2, port g b = v.val)
    (hRead₁ : ∀ g ∈ K₁.erase r₁, ∃ h ∈ K₁, ∃ b : Fin 2, port h b = n + g)
    (hRead₂ : ∀ g ∈ K₂.erase r₂, ∃ h ∈ K₂, ∃ b : Fin 2, port h b = n + g)
    (hRoot₁ : port H 0 = n + r₁) (hRoot₂ : port H 1 = n + r₂)
    (p q : ℕ × Fin 2) (hp : p.1 ∈ insert H (K₁ ∪ K₂))
    (hq : q.1 ∈ insert H (K₁ ∪ K₂)) (hpq : p ≠ q)
    (hDup : port p.1 p.2 = port q.1 q.2) :
    (S ∪ T).card ≤ (insert H (K₁ ∪ K₂)).card := by
  apply input_card_le_gates_of_duplicate_port n (insert H (K₁ ∪ K₂)) H
    (Finset.mem_insert_self _ _) port (S ∪ T) ?_ ?_ p q hp hq hpq hDup
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨g, hg, b, hb⟩ := hInputs₁ v hv
      exact ⟨g, Finset.mem_insert_of_mem (Finset.mem_union_left _ hg), b, hb⟩
    · obtain ⟨g, hg, b, hb⟩ := hInputs₂ v hv
      exact ⟨g, Finset.mem_insert_of_mem (Finset.mem_union_right _ hg), b, hb⟩
  · intro g hg
    obtain ⟨hgH, hg⟩ := Finset.mem_erase.mp hg
    have hgUnion : g ∈ K₁ ∪ K₂ := (Finset.mem_insert.mp hg).resolve_left hgH
    rcases Finset.mem_union.mp hgUnion with hg₁ | hg₂
    · by_cases hgr : g = r₁
      · subst g
        exact ⟨H, Finset.mem_insert_self _ _, 0, hRoot₁⟩
      · obtain ⟨h, hh, b, hb⟩ := hRead₁ g (Finset.mem_erase.mpr ⟨hgr, hg₁⟩)
        exact ⟨h, Finset.mem_insert_of_mem (Finset.mem_union_left _ hh), b, hb⟩
    · by_cases hgr : g = r₂
      · subst g
        exact ⟨H, Finset.mem_insert_self _ _, 1, hRoot₂⟩
      · obtain ⟨h, hh, b, hb⟩ := hRead₂ g (Finset.mem_erase.mpr ⟨hgr, hg₂⟩)
        exact ⟨h, Finset.mem_insert_of_mem (Finset.mem_union_right _ hh), b, hb⟩

end PEqualNP.Outside.L_meta_3566.PrivateCone


namespace PEqualNP.Outside.L_meta_3566.PrivateOverlap

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge OnePureFrontier

lemma orSet_subset_le {n : ℕ} (S T : Finset (Fin n)) (hST : S ⊆ T) (x : Fin n → Bool) :
    orSet S x ≤ orSet T x := by
  apply Bool.le_iff_imp.mpr
  simp only [orSet, decide_eq_true_eq]
  rintro ⟨v, hv, hx⟩
  exact ⟨v, hST hv, hx⟩

lemma and_orSet_eq_left {n : ℕ} (S T : Finset (Fin n)) (hST : S ⊆ T)
    (x : Fin n → Bool) : (orSet S x && orSet T x) = orSet S x := by
  have h := orSet_subset_le S T hST x
  cases hs : orSet S x <;> cases ht : orSet T x <;> simp_all [Bool.le_iff_imp]

lemma and_roots_value (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (H r₁ r₂ : ℕ) (hH : H < C.size)
    (hAnd : gateAt C H = ⟨GateOp.and, [n + r₁, n + r₂]⟩) (x : Fin n → Bool) :
    gateVal n C H x = (gateVal n C r₁ x && gateVal n C r₂ x) := by
  have heq := LeafStep.Pruning.gate_eq C hC H hH x
  simp only [hAnd, LeafStep.Pruning.isA, LeafStep.Pruning.opv, opnd] at heq
  exact heq

lemma not_and_comparable_or_roots {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (H r₁ r₂ : ℕ) (hH : H < C.size)
    (hAnd : gateAt C H = ⟨GateOp.and, [n + r₁, n + r₂]⟩)
    (S T : Finset (Fin n))
    (hRoot₁ : ∀ x : Fin n → Bool, gateVal n C r₁ x = orSet S x)
    (hRoot₂ : ∀ x : Fin n → Bool, gateVal n C r₂ x = orSet T x)
    (hCompare : S ⊆ T ∨ T ⊆ S) : False := by
  have hOutput := InputAlias.least_output_bound_of_gate G C hLeast H hH
  have hEarlier₁ : n + r₁ < n + H :=
    hLeast.1.2.1 H hH _ (by simp [hAnd])
  have hEarlier₂ : n + r₂ < n + H :=
    hLeast.1.2.1 H hH _ (by simp [hAnd])
  have hValue (x : Fin n → Bool) : gateVal n C H x = (orSet S x && orSet T x) := by
    rw [and_roots_value n C hLeast.1 H r₁ r₂ hH hAnd, hRoot₁, hRoot₂]
  rcases hCompare with hST | hTS
  · apply Absorption.least_no_equivalent n G C hLeast H (n + r₁) hH hEarlier₁ hOutput
    intro x
    change gateVal n C H x = gateVal n C r₁ x
    rw [hValue, hRoot₁]
    exact and_orSet_eq_left S T hST x
  · apply Absorption.least_no_equivalent n G C hLeast H (n + r₂) hH hEarlier₂ hOutput
    intro x
    change gateVal n C H x = gateVal n C r₂ x
    rw [hValue, hRoot₂, Bool.and_comm]
    exact and_orSet_eq_left T S hTS x

end PEqualNP.Outside.L_meta_3566.PrivateOverlap


namespace PEqualNP.Outside.L_meta_3566.OverlapCode

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.OnePureFrontier
open PrivateColorTree PrivateCode

lemma overlap_value {n : ℕ} (S T : Finset (Fin n)) (x : Fin n → Bool) :
    (orSet (S ∩ T) x || (orSet (S \ T) x && orSet (T \ S) x)) =
      (orSet S x && orSet T x) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, orSet, decide_eq_true_eq,
    Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro (⟨v, ⟨hvS, hvT⟩, hx⟩ | ⟨⟨u, ⟨huS, _⟩, hxu⟩, ⟨v, ⟨hvT, _⟩, hxv⟩⟩)
    · exact ⟨⟨v, hvS, hx⟩, ⟨v, hvT, hx⟩⟩
    · exact ⟨⟨u, huS, hxu⟩, ⟨v, hvT, hxv⟩⟩
  · rintro ⟨⟨u, huS, hxu⟩, ⟨v, hvT, hxv⟩⟩
    by_cases huT : u ∈ T
    · exact Or.inl ⟨u, ⟨huS, huT⟩, hxu⟩
    by_cases hvS : v ∈ S
    · exact Or.inl ⟨v, ⟨hvS, hvT⟩, hxv⟩
    exact Or.inr ⟨⟨u, ⟨huS, huT⟩, hxu⟩, ⟨v, ⟨hvT, hvS⟩, hxv⟩⟩

lemma overlap_card {n : ℕ} (S T : Finset (Fin n)) :
    (S ∩ T).card + (S \ T).card + (T \ S).card = (S ∪ T).card := by
  have h₁ := Finset.card_sdiff_add_card_inter S T
  have h₂ := Finset.card_sdiff_add_card T S
  rw [Finset.union_comm T S] at h₂
  omega

lemma exists_or_circuit {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∃ Q : Circuit, IsAO2 n Q ∧ Q.size + 1 = S.card ∧
      circuitFun n Q = orSet S ∧ Q.output < n + Q.size := by
  obtain ⟨t, hVars, hSize⟩ := exists_tree_of_nonempty S hS
  obtain ⟨hQ, hFun, hLen, _⟩ := compiled_spec t
  refine ⟨PrivateColorTree.compiled t, hQ, ?_, ?_, ?_⟩
  · rw [hLen]
    exact hSize
  · rw [hFun]
    funext x
    rw [eval_eq_orSet, hVars]
  · change (emit t n).2 < n + (PrivateColorTree.compiled t).size
    rw [hLen]
    exact (emit_good t n le_rfl).2

lemma exists_overlap_circuit {n : ℕ} (S T : Finset (Fin n))
    (hA : (S ∩ T).Nonempty) (hB : (S \ T).Nonempty) (hD : (T \ S).Nonempty) :
    ∃ Q : Circuit, IsAO2 n Q ∧ Q.size + 1 = (S ∪ T).card ∧
      circuitFun n Q = (fun x => orSet S x && orSet T x) ∧ Q.output < n + Q.size := by
  obtain ⟨a, hVa, hSa⟩ := exists_tree_of_nonempty (S ∩ T) hA
  obtain ⟨b, hVb, hSb⟩ := exists_tree_of_nonempty (S \ T) hB
  obtain ⟨d, hVd, hSd⟩ := exists_tree_of_nonempty (T \ S) hD
  let bd := binary GateOp.and (ofTree b) (ofTree d)
  let code := binary GateOp.or (ofTree a) bd
  have hBD := valid_binary GateOp.and (Or.inl rfl) (· && ·) (by intros; simp [GateOp.eval])
    (ofTree b) (ofTree d) (eval b) (eval d) (activeCount b) (activeCount d)
    (valid_ofTree b) (valid_ofTree d)
  have hCode := valid_binary GateOp.or (Or.inr rfl) (· || ·) (by intros; simp [GateOp.eval])
    (ofTree a) bd (eval a) _ (activeCount a) _ (valid_ofTree a) hBD
  obtain ⟨hQ, hSize, hFun, _⟩ := circuit_spec code _ _ hCode
  refine ⟨circuit n code, hQ, ?_, ?_, ?_⟩
  · rw [hSize]
    have hCard := overlap_card S T
    simp only [code, bd, binary, ofTree, Code.size]
    omega
  · rw [hFun]
    funext x
    rw [eval_eq_orSet, eval_eq_orSet, eval_eq_orSet, hVa, hVb, hVd]
    exact overlap_value S T x
  · change (code.emit n).2 < n + (circuit n code).size
    rw [hSize]
    exact (hCode n le_rfl).2.2.1

end PEqualNP.Outside.L_meta_3566.OverlapCode


namespace PEqualNP.Outside.L_meta_3566.PrivateOverlap

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma root_not_mem_of_difference {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (K₁ K₂ : Finset ℕ) (r₁ r₂ : ℕ) (S T : Finset (Fin n))
    (hCone₁ : PrivateMixed.OrCone C K₁ r₁ S) (hCone₂ : PrivateMixed.OrCone C K₂ r₂ T)
    (hOnly : (S \ T).Nonempty) : r₁ ∉ K₂ := by
  classical
  obtain ⟨v, hv⟩ := hOnly
  obtain ⟨hvS, hvT⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨hr₁, hK₁, hOr₁, hClosed₁, hRead₁, hInputs₁, hAll₁⟩ := hCone₁
  obtain ⟨hr₂, hK₂, hOr₂, hClosed₂, hRead₂, hInputs₂, hAll₂⟩ := hCone₂
  intro hrIn
  have hOn : gateVal n C r₁ (pairInput v v) = true := by
    rw [PrivateCone.closed_or_cone_value n C hC K₁ r₁ hr₁ hK₁ hOr₁ hClosed₁ hRead₁ S hInputs₁ hAll₁]
    exact (OnePureFrontier.orSet_pair S v v).mpr (Or.inl hvS)
  have hZero : ∀ u ∈ T, pairInput v v u = (fun _ : Fin n => false) u := by
    intro u hu
    have huv : u ≠ v := by intro he; subst u; exact hvT hu
    simp [pairInput, huv]
  have hEq := PrivateCone.cone_agree n C hC K₂ hK₂ hClosed₂ T hAll₂
    (pairInput v v) (fun _ => false) hZero r₁ hrIn
  rw [PrivateCone.gate_zero n C hC r₁ (hK₂ r₁ hrIn)] at hEq
  rw [hEq] at hOn
  exact Bool.false_ne_true hOn

lemma duplicate_port_of_common_input (n : ℕ) (K₁ K₂ : Finset ℕ) (r₁ r₂ : ℕ)
    (port : ℕ → Fin 2 → ℕ)
    (hRead₁ : ∀ g ∈ K₁.erase r₁, ∃ h ∈ K₁, ∃ b : Fin 2, port h b = n + g)
    (hRead₂ : ∀ g ∈ K₂.erase r₂, ∃ h ∈ K₂, ∃ b : Fin 2, port h b = n + g)
    (hBack₁ : ∀ g ∈ K₁, ∀ b : Fin 2, port g b < n + g)
    (_hBack₂ : ∀ g ∈ K₂, ∀ b : Fin 2, port g b < n + g)
    (hr₁ : r₁ ∉ K₂) (hr₂ : r₂ ∉ K₁) (v : Fin n)
    (hv₁ : ∃ g ∈ K₁, ∃ b : Fin 2, port g b = v.val)
    (hv₂ : ∃ g ∈ K₂, ∃ b : Fin 2, port g b = v.val) :
    ∃ p q : ℕ × Fin 2, p.1 ∈ K₁ ∪ K₂ ∧ q.1 ∈ K₁ ∪ K₂ ∧ p ≠ q ∧
      port p.1 p.2 = port q.1 q.2 := by
  classical
  by_cases hInter : (K₁ ∩ K₂).Nonempty
  · let g := (K₁ ∩ K₂).max' hInter
    have hg : g ∈ K₁ ∩ K₂ := Finset.max'_mem _ _
    obtain ⟨hg₁, hg₂⟩ := Finset.mem_inter.mp hg
    have hgr₁ : g ≠ r₁ := by
      intro h
      apply hr₁
      rw [← h]
      exact hg₂
    have hgr₂ : g ≠ r₂ := by
      intro h
      apply hr₂
      rw [← h]
      exact hg₁
    obtain ⟨h₁, hh₁, b₁, hb₁⟩ := hRead₁ g (Finset.mem_erase.mpr ⟨hgr₁, hg₁⟩)
    obtain ⟨h₂, hh₂, b₂, hb₂⟩ := hRead₂ g (Finset.mem_erase.mpr ⟨hgr₂, hg₂⟩)
    have hgh₁ : g < h₁ := by have hb := hBack₁ h₁ hh₁ b₁; rw [hb₁] at hb; omega
    have hDistinct : h₁ ≠ h₂ := by
      intro h
      have hh₁₂ : h₁ ∈ K₂ := h ▸ hh₂
      have hle : h₁ ≤ g := Finset.le_max' _ h₁ (Finset.mem_inter.mpr ⟨hh₁, hh₁₂⟩)
      omega
    refine ⟨(h₁, b₁), (h₂, b₂), Finset.mem_union_left _ hh₁,
      Finset.mem_union_right _ hh₂, ?_, hb₁.trans hb₂.symm⟩
    intro he
    exact hDistinct (congrArg Prod.fst he)
  · obtain ⟨g₁, hg₁, b₁, hb₁⟩ := hv₁
    obtain ⟨g₂, hg₂, b₂, hb₂⟩ := hv₂
    have hDistinct : g₁ ≠ g₂ := by
      intro he
      exact hInter ⟨g₁, Finset.mem_inter.mpr ⟨hg₁, he ▸ hg₂⟩⟩
    refine ⟨(g₁, b₁), (g₂, b₂), Finset.mem_union_left _ hg₁,
      Finset.mem_union_right _ hg₂, ?_, hb₁.trans hb₂.symm⟩
    intro he
    exact hDistinct (congrArg Prod.fst he)

lemma overlap_support_card_le_private {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (K₁ K₂ : Finset ℕ) (r₁ r₂ H : ℕ) (S T : Finset (Fin n))
    (hCone₁ : PrivateMixed.OrCone C K₁ r₁ S) (hCone₂ : PrivateMixed.OrCone C K₂ r₂ T)
    (hAnd : gateAt C H = ⟨GateOp.and, [n + r₁, n + r₂]⟩)
    (hBoth : (S ∩ T).Nonempty) (hSOnly : (S \ T).Nonempty) (hTOnly : (T \ S).Nonempty) :
    (S ∪ T).card ≤ (insert H (K₁ ∪ K₂)).card := by
  classical
  have hr₁Not := root_not_mem_of_difference C hC K₁ K₂ r₁ r₂ S T hCone₁ hCone₂ hSOnly
  have hr₂Not := root_not_mem_of_difference C hC K₂ K₁ r₂ r₁ T S hCone₂ hCone₁ hTOnly
  obtain ⟨hr₁, hK₁, hOr₁, hClosed₁, hRead₁, hInputs₁, hAll₁⟩ := hCone₁
  obtain ⟨hr₂, hK₂, hOr₂, hClosed₂, hRead₂, hInputs₂, hAll₂⟩ := hCone₂
  have hBack₁ (g : ℕ) (hg : g ∈ K₁) (b : Fin 2) : opnd C g b < n + g :=
    hC.2.1 g (hK₁ g hg) _ (PrivateCone.port_mem n C hC g (hK₁ g hg) b)
  have hBack₂ (g : ℕ) (hg : g ∈ K₂) (b : Fin 2) : opnd C g b < n + g :=
    hC.2.1 g (hK₂ g hg) _ (PrivateCone.port_mem n C hC g (hK₂ g hg) b)
  obtain ⟨v, hv⟩ := hBoth
  obtain ⟨hvS, hvT⟩ := Finset.mem_inter.mp hv
  obtain ⟨p, q, hp, hq, hpq, hDup⟩ := duplicate_port_of_common_input n K₁ K₂ r₁ r₂ (opnd C)
    hRead₁ hRead₂ hBack₁ hBack₂ hr₁Not hr₂Not v (hInputs₁ v hvS) (hInputs₂ v hvT)
  apply PrivateCone.two_cone_input_card_le_private_of_duplicate_port n K₁ K₂ r₁ r₂ H (opnd C) S T
    hInputs₁ hInputs₂ hRead₁ hRead₂ ?_ ?_ p q (Finset.mem_insert_of_mem hp)
    (Finset.mem_insert_of_mem hq) hpq hDup
  · simp [opnd, hAnd]
  · simp [opnd, hAnd]

end PEqualNP.Outside.L_meta_3566.PrivateOverlap


namespace PEqualNP.Outside.L_meta_3566.PrivateOverlap

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge OnePureFrontier

lemma no_private_overlapping_or_cones {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C)
    (K₁ K₂ : Finset ℕ) (r₁ r₂ H : ℕ) (S T : Finset (Fin n))
    (hCone₁ : PrivateMixed.OrCone C K₁ r₁ S) (hCone₂ : PrivateMixed.OrCone C K₂ r₂ T)
    (hH : H < C.size) (hAnd : gateAt C H = ⟨GateOp.and, [n + r₁, n + r₂]⟩)
    (hOverlap : (S ∩ T).Nonempty)
    (hPrivate : ∀ i < C.size, i ∉ insert H (K₁ ∪ K₂) → ∀ j ∈ insert H (K₁ ∪ K₂),
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ insert H (K₁ ∪ K₂), C.output = n + j → j = H) : False := by
  classical
  obtain ⟨hr₁, hK₁, hOr₁, hClosed₁, hRead₁, hInputs₁, hAll₁⟩ := hCone₁
  obtain ⟨hr₂, hK₂, hOr₂, hClosed₂, hRead₂, hInputs₂, hAll₂⟩ := hCone₂
  have hRoot₁ (x : Fin n → Bool) : gateVal n C r₁ x = orSet S x :=
    PrivateCone.closed_or_cone_value n C hLeast.1 K₁ r₁ hr₁ hK₁ hOr₁ hClosed₁
      hRead₁ S hInputs₁ hAll₁ x
  have hRoot₂ (x : Fin n → Bool) : gateVal n C r₂ x = orSet T x :=
    PrivateCone.closed_or_cone_value n C hLeast.1 K₂ r₂ hr₂ hK₂ hOr₂ hClosed₂
      hRead₂ T hInputs₂ hAll₂ x
  by_cases hST : S ⊆ T
  · exact not_and_comparable_or_roots G C hLeast H r₁ r₂ hH hAnd S T hRoot₁ hRoot₂ (Or.inl hST)
  by_cases hTS : T ⊆ S
  · exact not_and_comparable_or_roots G C hLeast H r₁ r₂ hH hAnd S T hRoot₁ hRoot₂ (Or.inr hTS)
  have hSOnly : (S \ T).Nonempty := by
    by_contra hNo
    apply hST
    intro v hv
    by_contra hvT
    exact hNo ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvT⟩⟩
  have hTOnly : (T \ S).Nonempty := by
    by_contra hNo
    apply hTS
    intro v hv
    by_contra hvS
    exact hNo ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvS⟩⟩
  obtain ⟨Q, hQ, hSize, hFun, hq⟩ := OverlapCode.exists_overlap_circuit S T hOverlap hSOnly hTOnly
  have hCard := overlap_support_card_le_private C hLeast.1 K₁ K₂ r₁ r₂ H S T
    ⟨hr₁, hK₁, hOr₁, hClosed₁, hRead₁, hInputs₁, hAll₁⟩
    ⟨hr₂, hK₂, hOr₂, hClosed₂, hRead₂, hInputs₂, hAll₂⟩ hAnd hOverlap hSOnly hTOnly
  have hJ : insert H (K₁ ∪ K₂) ⊆ Finset.range C.size := by
    intro j hj
    apply Finset.mem_range.mpr
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hH
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact hK₁ j hj
      · exact hK₂ j hj
  have hValue (x : Fin n → Bool) : gateVal n C H x = (orSet S x && orSet T x) := by
    rw [and_roots_value n C hLeast.1 H r₁ r₂ hH hAnd, hRoot₁, hRoot₂]
  apply PrivateCopy.not_of_least_size G Q C (insert H (K₁ ∪ K₂)) H hLeast hQ hq hJ hPrivate hOutput
  · intro x
    rw [hFun, hValue]
  · intro a b _hab
    rw [hFun, hValue]
  · omega

end PEqualNP.Outside.L_meta_3566.PrivateOverlap


namespace PEqualNP.Outside.L_meta_3566.OnePurePrivate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PrivateColorTree PrivateCode PrivateColorShell OnePureFrontier

lemma exists_and_or_sets {n : ℕ} (S T : Finset (Fin n)) (hS : S.Nonempty) (hT : T.Nonempty) :
    ∃ Q : Circuit, IsAO2 n Q ∧ Q.size + 1 = S.card + T.card ∧
      circuitFun n Q = (fun x => orSet S x && orSet T x) ∧ Q.output < n + Q.size := by
  obtain ⟨s, hvs, hss⟩ := exists_tree_of_nonempty S hS
  obtain ⟨t, hvt, hst⟩ := exists_tree_of_nonempty T hT
  let c := binary GateOp.and (ofTree s) (ofTree t)
  have hc : Valid n c (fun x => eval s x && eval t x)
      (fun x => activeCount s x + activeCount t x + if eval s x && eval t x then 1 else 0) :=
    valid_binary GateOp.and (Or.inl rfl) (· && ·) (by intros; simp [GateOp.eval])
      (ofTree s) (ofTree t) (eval s) (eval t) (activeCount s) (activeCount t)
      (valid_ofTree s) (valid_ofTree t)
  obtain ⟨hAO, hSize, hFun, _⟩ := circuit_spec c _ _ hc
  refine ⟨circuit n c, hAO, ?_, ?_, ?_⟩
  · rw [hSize]
    simp only [c, binary, ofTree, Code.size]
    omega
  · rw [hFun]
    funext x
    simp only [eval_eq_orSet, hvs, hvt]
  · have hOut := (hc n le_rfl).2.2.1
    change (c.emit n).2 < n + (circuit n c).size
    rw [hSize]
    exact hOut

lemma cross_eq_of_pure_left {n : ℕ} (color : Fin n → Bool) (b : Bool)
    (S T : Finset (Fin n)) (hPure : ∀ v ∈ S, color v = b) (x : Fin n → Bool) :
    cross color S T x = (orSet S x && orSet (part color (!b) T) x) := by
  have hSame : part color b S = S := by
    ext v
    simp only [part, Finset.mem_filter]
    exact ⟨And.left, fun hv => ⟨hv, hPure v hv⟩⟩
  have hOther : part color (!b) S = ∅ := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvS, hc⟩ := Finset.mem_filter.mp hv
      rw [hPure v hvS] at hc
      cases b <;> cases hc
    · intro hv
      simp at hv
  cases b <;> simp only [Bool.not_false, Bool.not_true] at hOther ⊢
  · simp [cross, hSame, hOther, orSet]
  · simp [cross, hSame, hOther, orSet]

lemma part_card_lt_of_both {n : ℕ} (color : Fin n → Bool) (b : Bool)
    (T : Finset (Fin n)) (hBoth : ∀ c : Bool, ∃ v ∈ T, color v = c) :
    (part color (!b) T).card < T.card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  obtain ⟨v, hv, hc⟩ := hBoth b
  have hv' : v ∈ part color (!b) T := heq.symm ▸ hv
  have hvColor := (Finset.mem_filter.mp hv').2
  rw [hc] at hvColor
  cases b <;> cases hvColor

lemma no_private_disjoint_pure_mixed_or_cones {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hBip : ∀ a b : Fin n, G.Adj a b → color a ≠ color b)
    (C : Circuit) (hLeast : IsLeastAO G C)
    (K₁ K₂ : Finset ℕ) (r₁ r₂ H : ℕ) (S T : Finset (Fin n))
    (hCone₁ : PrivateMixed.OrCone C K₁ r₁ S) (hCone₂ : PrivateMixed.OrCone C K₂ r₂ T)
    (hH : H < C.size)
    (hAnd : gateAt C H = ⟨GateOp.and, [n + r₁, n + r₂]⟩ ∨
      gateAt C H = ⟨GateOp.and, [n + r₂, n + r₁]⟩)
    (hDisjS : Disjoint S T) (b : Bool)
    (hPureS : ∀ v ∈ S, color v = b)
    (hBothT : ∀ c : Bool, ∃ v ∈ T, color v = c)
    (hPrivate : ∀ i < C.size, i ∉ insert H (K₁ ∪ K₂) → ∀ j ∈ insert H (K₁ ∪ K₂),
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ insert H (K₁ ∪ K₂), C.output = n + j → j = H) : False := by
  classical
  obtain ⟨hr₁, hK₁, hOr₁, hClosed₁, hRead₁, hInputs₁, hAll₁⟩ := hCone₁
  obtain ⟨hr₂, hK₂, hOr₂, hClosed₂, hRead₂, hInputs₂, hAll₂⟩ := hCone₂
  have hDisjK : Disjoint K₁ K₂ :=
    PrivateCone.closed_cones_disjoint_of_supports n C hLeast.1 K₁ K₂ hK₁ hK₂ hClosed₁ hClosed₂
      S T hDisjS hAll₁ hAll₂
  have hOp : (gateAt C H).op = GateOp.and := by
    rcases hAnd with h | h <;> simp [h]
  have hHNot : H ∉ K₁ ∪ K₂ := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · have hh := hOr₁ H h
      rw [hOp] at hh
      cases hh
    · have hh := hOr₂ H h
      rw [hOp] at hh
      cases hh
  have hS : S.Nonempty := by
    have hVal := PrivateCone.closed_or_cone_value n C hLeast.1 K₁ r₁ hr₁ hK₁ hOr₁ hClosed₁
      hRead₁ S hInputs₁ hAll₁ (fun _ => true)
    have hOn := PrivateCone.gate_all_true n C hLeast.1 r₁ (hK₁ r₁ hr₁)
    have hSet : orSet S (fun _ => true) = true := hVal.symm.trans hOn
    obtain ⟨v, hv, _⟩ : ∃ v ∈ S, (fun _ : Fin n => true) v = true := of_decide_eq_true hSet
    exact ⟨v, hv⟩
  have hTPart : (part color (!b) T).Nonempty := by
    obtain ⟨v, hv, hc⟩ := hBothT (!b)
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hc⟩⟩
  obtain ⟨Q, hQ, hQSize, hQFun, hq⟩ := exists_and_or_sets S (part color (!b) T) hS hTPart
  have hQCross : circuitFun n Q = cross color S T := by
    rw [hQFun]
    funext x
    exact (cross_eq_of_pure_left color b S T hPureS x).symm
  have hHFun (x : Fin n → Bool) :
      gateVal n C H x = (orSet S x && orSet T x) := by
    have heq := LeafStep.Pruning.gate_eq C hLeast.1 H hH x
    have hr₁Fun := PrivateCone.closed_or_cone_value n C hLeast.1 K₁ r₁ hr₁ hK₁ hOr₁ hClosed₁
      hRead₁ S hInputs₁ hAll₁ x
    have hr₂Fun := PrivateCone.closed_or_cone_value n C hLeast.1 K₂ r₂ hr₂ hK₂ hOr₂ hClosed₂
      hRead₂ T hInputs₂ hAll₂ x
    rcases hAnd with h | h
    · simp only [h, LeafStep.Pruning.isA, LeafStep.Pruning.opv, opnd] at heq
      change gateVal n C H x = (gateVal n C r₁ x && gateVal n C r₂ x) at heq
      rw [heq, hr₁Fun, hr₂Fun]
    · simp only [h, LeafStep.Pruning.isA, LeafStep.Pruning.opv, opnd] at heq
      change gateVal n C H x = (gateVal n C r₂ x && gateVal n C r₁ x) at heq
      rw [heq, hr₁Fun, hr₂Fun, Bool.and_comm]
  have hJ : insert H (K₁ ∪ K₂) ⊆ Finset.range C.size := by
    intro j hj
    apply Finset.mem_range.mpr
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hH
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact hK₁ j hj
      · exact hK₂ j hj
  have hCard : (insert H (K₁ ∪ K₂)).card = K₁.card + K₂.card + 1 := by
    rw [Finset.card_insert_of_notMem hHNot, Finset.card_union_of_disjoint hDisjK]
  have hSize : Q.size < (insert H (K₁ ∪ K₂)).card := by
    have hs := PrivateCone.input_card_le_gates_add_one n K₁ r₁ hr₁ (opnd C) S hInputs₁ hRead₁
    have ht := PrivateCone.input_card_le_gates_add_one n K₂ r₂ hr₂ (opnd C) T hInputs₂ hRead₂
    have hProper := part_card_lt_of_both color b T hBothT
    omega
  apply PrivateCopy.not_of_least_size G Q C (insert H (K₁ ∪ K₂)) H hLeast hQ hq hJ
    hPrivate hOutput
  · intro x
    rw [hQCross, hHFun]
    exact cross_le color S T x
  · intro a c hac
    rw [hQCross, hHFun]
    exact cross_pair_eq color S T hDisjS a c (hBip a c hac)
  · exact hSize

end PEqualNP.Outside.L_meta_3566.OnePurePrivate


namespace PEqualNP.Outside.L_meta_3566.SameColorFactors

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm OnePureFrontier

lemma edge_false {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Bool) (hBip : ∀ a b, G.Adj a b → color a ≠ color b)
    (S T : Finset (Fin n)) (hDisjoint : Disjoint S T) (b : Bool)
    (hS : ∀ u ∈ S, color u = b) (hT : ∀ u ∈ T, color u = b)
    (u v : Fin n) (huv : G.Adj u v) :
    (orSet S (pairInput u v) && orSet T (pairInput u v)) = false := by
  apply Bool.eq_false_iff.mpr
  intro hOn
  have hBoth : orSet S (pairInput u v) = true ∧
      orSet T (pairInput u v) = true := by simpa using hOn
  rcases (orSet_pair S u v).mp hBoth.1 with huS | hvS
  · rcases (orSet_pair T u v).mp hBoth.2 with huT | hvT
    · exact Finset.disjoint_left.mp hDisjoint huS huT
    · exact hBip u v huv ((hS u huS).trans (hT v hvT).symm)
  · rcases (orSet_pair T u v).mp hBoth.2 with huT | hvT
    · exact hBip u v huv ((hT u huT).trans (hS v hvS).symm)
    · exact Finset.disjoint_left.mp hDisjoint hvS hvT

lemma not_in_mono_normalized {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hBip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hE : ∃ u v : Fin n, G.Adj u v)
    (C : Circuit) (hC : MonoNormalize.IsMonoJunkLeastAO G color C)
    (j : ℕ) (hj : j < C.gates.length) (hAnd : (gateAt C j).op = GateOp.and)
    (S T : Finset (Fin n)) (hDisjoint : Disjoint S T)
    (hSNonempty : S.Nonempty) (hTNonempty : T.Nonempty) (b : Bool)
    (hS : ∀ u ∈ S, color u = b) (hT : ∀ u ∈ T, color u = b)
    (hVal : ∀ x, gateVal n C j x = (orSet S x && orSet T x)) : False := by
  have hMonoOn : (orSet S (MonoNormalize.input color b) &&
      orSet T (MonoNormalize.input color b)) = true := by
    obtain ⟨u, hu⟩ := hSNonempty
    obtain ⟨v, hv⟩ := hTNonempty
    have hs : orSet S (MonoNormalize.input color b) = true := by
      apply decide_eq_true_eq.mpr
      exact ⟨u, hu, by simp [MonoNormalize.input, hS u hu]⟩
    have ht : orSet T (MonoNormalize.input color b) = true := by
      apply decide_eq_true_eq.mpr
      exact ⟨v, hv, by simp [MonoNormalize.input, hT v hv]⟩
    simp [hs, ht]
  have hDirty : j ∈ junk G C := by
    apply (JunkNormalize.mem_junk_iff G C j).mpr
    exact ⟨hj, hAnd, MonoNormalize.input color b, (hVal _).trans hMonoOn,
      MonoNormalize.input_false G color hBip b⟩
  obtain ⟨u, v, _, _, huv, _, hp, _, _⟩ :=
    MonoNormalize.dirty_has_two_pivotal_edges G color hBip hE C hC j hDirty
  have hOn := JunkPivotal.pivotal_on G C hC.1.1 hC.1.2.1 j hj u v huv hp
  rw [hVal, edge_false G color hBip S T hDisjoint b hS hT u v huv] at hOn
  exact Bool.false_ne_true hOn

end PEqualNP.Outside.L_meta_3566.SameColorFactors


namespace PEqualNP.Outside.L_meta_3566.PrivateClassification

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge OnePureFrontier

lemma pure_or_mixed {n : ℕ} (S : Finset (Fin n)) (color : Fin n → Bool) :
    (∃ b : Bool, ∀ v ∈ S, color v = b) ∨ (∀ b : Bool, ∃ v ∈ S, color v = b) := by
  classical
  by_cases hPure : ∃ b : Bool, ∀ v ∈ S, color v = b
  · exact Or.inl hPure
  right
  intro b
  by_contra hNo
  apply hPure
  refine ⟨!b, ?_⟩
  intro v hv
  have hne : color v ≠ b := fun hc => hNo ⟨v, hv, hc⟩
  cases hb : b <;> cases hc : color v <;> simp_all

lemma orCone_nonempty {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (K : Finset ℕ) (r : ℕ) (S : Finset (Fin n))
    (hCone : PrivateMixed.OrCone C K r S) : S.Nonempty := by
  obtain ⟨hr, hK, hOr, hClosed, hRead, hInputs, hAll⟩ := hCone
  have hVal := PrivateCone.closed_or_cone_value n C hAO K r hr hK hOr hClosed
    hRead S hInputs hAll (fun _ => true)
  have hOn := PrivateCone.gate_all_true n C hAO r (hK r hr)
  have hSet : orSet S (fun _ => true) = true := hVal.symm.trans hOn
  obtain ⟨v, hv, _⟩ : ∃ v ∈ S, (fun _ : Fin n => true) v = true := of_decide_eq_true hSet
  exact ⟨v, hv⟩

lemma private_or_factors_pure_opposite {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hBip : ∀ a b : Fin n, G.Adj a b → color a ≠ color b)
    (hE : ∃ a b : Fin n, G.Adj a b)
    (C : Circuit) (hMin : MonoNormalize.IsMonoJunkLeastAO G color C)
    (K₁ K₂ : Finset ℕ) (r₁ r₂ H : ℕ) (S T : Finset (Fin n))
    (hCone₁ : PrivateMixed.OrCone C K₁ r₁ S) (hCone₂ : PrivateMixed.OrCone C K₂ r₂ T)
    (hH : H < C.size) (hAnd : gateAt C H = ⟨GateOp.and, [n + r₁, n + r₂]⟩)
    (hPrivate : ∀ i < C.size, i ∉ insert H (K₁ ∪ K₂) → ∀ j ∈ insert H (K₁ ∪ K₂),
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ insert H (K₁ ∪ K₂), C.output = n + j → j = H) :
    Disjoint S T ∧ ∃ b : Bool, (∀ v ∈ S, color v = b) ∧ (∀ v ∈ T, color v = !b) := by
  classical
  have hDisj : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvT
    exact PrivateOverlap.no_private_overlapping_or_cones G C hMin.1 K₁ K₂ r₁ r₂ H S T
      hCone₁ hCone₂ hH hAnd ⟨v, Finset.mem_inter.mpr ⟨hvS, hvT⟩⟩ hPrivate hOutput
  refine ⟨hDisj, ?_⟩
  have hSNon := orCone_nonempty C hMin.1.1 K₁ r₁ S hCone₁
  have hTNon := orCone_nonempty C hMin.1.1 K₂ r₂ T hCone₂
  have hValue (x : Fin n → Bool) : gateVal n C H x = (orSet S x && orSet T x) := by
    obtain ⟨hr₁, hK₁, hOr₁, hClosed₁, hRead₁, hInputs₁, hAll₁⟩ := hCone₁
    obtain ⟨hr₂, hK₂, hOr₂, hClosed₂, hRead₂, hInputs₂, hAll₂⟩ := hCone₂
    rw [PrivateOverlap.and_roots_value n C hMin.1.1 H r₁ r₂ hH hAnd,
      PrivateCone.closed_or_cone_value n C hMin.1.1 K₁ r₁ hr₁ hK₁ hOr₁ hClosed₁ hRead₁ S hInputs₁ hAll₁,
      PrivateCone.closed_or_cone_value n C hMin.1.1 K₂ r₂ hr₂ hK₂ hOr₂ hClosed₂ hRead₂ T hInputs₂ hAll₂]
  rcases pure_or_mixed S color with ⟨b, hPureS⟩ | hBothS
  · rcases pure_or_mixed T color with ⟨c, hPureT⟩ | hBothT
    · by_cases hbc : b = c
      · subst c
        exact (SameColorFactors.not_in_mono_normalized G color hBip hE C hMin H hH
          (by simp [hAnd]) S T hDisj hSNon hTNon b hPureS hPureT hValue).elim
      · refine ⟨b, hPureS, ?_⟩
        intro v hv
        have hc := hPureT v hv
        cases b <;> cases c <;> simp_all
    · exact (OnePurePrivate.no_private_disjoint_pure_mixed_or_cones G color hBip C hMin.1
        K₁ K₂ r₁ r₂ H S T hCone₁ hCone₂ hH (Or.inl hAnd) hDisj b hPureS hBothT
        hPrivate hOutput).elim
  · rcases pure_or_mixed T color with ⟨c, hPureT⟩ | hBothT
    · apply (OnePurePrivate.no_private_disjoint_pure_mixed_or_cones G color hBip C hMin.1
        K₂ K₁ r₂ r₁ H T S hCone₂ hCone₁ hH (Or.inr hAnd) hDisj.symm c hPureT hBothS ?_ ?_).elim
      · simpa only [Finset.union_comm] using hPrivate
      · simpa only [Finset.union_comm] using hOutput
    · exact (PrivateMixed.no_private_disjoint_mixed_or_cones G color hBip C hMin
        K₁ K₂ r₁ r₂ H S T hCone₁ hCone₂ hH hAnd hDisj hBothS hBothT hPrivate hOutput).elim

end PEqualNP.Outside.L_meta_3566.PrivateClassification

namespace PEqualNP.Outside.L_meta_3566.PrivateClassification

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma least_output_eq_last {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (j : ℕ) (hj : j < C.size) :
    C.output = n + (C.size - 1) := by
  have ho := InputAlias.least_output_bound_of_gate G C hC j hj
  by_contra h
  obtain ⟨k, hkLast, hk, _⟩ := LeafStep.reader_of_least G C hC (C.size - 1) (by omega) ho h
  omega

lemma cone_gate_le_root {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (K : Finset ℕ) (r : ℕ) (S : Finset (Fin n))
    (hCone : PrivateMixed.OrCone C K r S) : ∀ g ∈ K, g ≤ r := by
  classical
  obtain ⟨hr, hK, hOr, hClosed, hRead, hInputs, hAll⟩ := hCone
  let m := K.max' ⟨r, hr⟩
  have hm : m ∈ K := Finset.max'_mem _ _
  have hmr : m = r := by
    by_contra hne
    obtain ⟨k, hk, b, hb⟩ := hRead m (Finset.mem_erase.mpr ⟨hne, hm⟩)
    have hBack := hC.2.1 k (hK k hk) (opnd C k b)
      (PrivateCone.port_mem n C hC k (hK k hk) b)
    rw [hb] at hBack
    have hkm : k ≤ m := Finset.le_max' K k hk
    omega
  intro g hg
  have hgm : g ≤ m := Finset.le_max' K g hg
  omega

lemma output_private_of_or_cones {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (K₁ K₂ : Finset ℕ) (r₁ r₂ H : ℕ) (S T : Finset (Fin n))
    (hCone₁ : PrivateMixed.OrCone C K₁ r₁ S) (hCone₂ : PrivateMixed.OrCone C K₂ r₂ T)
    (hH : H < C.size)
    (hAnd : gateAt C H = ⟨GateOp.and, [n + r₁, n + r₂]⟩ ∨
      gateAt C H = ⟨GateOp.and, [n + r₂, n + r₁]⟩) :
    ∀ j ∈ insert H (K₁ ∪ K₂), C.output = n + j → j = H := by
  have hLast := least_output_eq_last G C hC H hH
  have hBack₁ : n + r₁ < n + H := hC.1.2.1 H hH (n + r₁) (by
    rcases hAnd with h | h <;> simp [h])
  have hBack₂ : n + r₂ < n + H := hC.1.2.1 H hH (n + r₂) (by
    rcases hAnd with h | h <;> simp [h])
  have hK₁ := cone_gate_le_root C hC.1 K₁ r₁ S hCone₁
  have hK₂ := cone_gate_le_root C hC.1 K₂ r₂ T hCone₂
  intro j hj hOut
  rcases Finset.mem_insert.mp hj with rfl | hj
  · rfl
  · rcases Finset.mem_union.mp hj with hj | hj
    · have := hK₁ j hj
      omega
    · have := hK₂ j hj
      omega

lemma private_or_factors_pure_opposite_of_read_privacy {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hBip : ∀ a b : Fin n, G.Adj a b → color a ≠ color b)
    (hE : ∃ a b : Fin n, G.Adj a b)
    (C : Circuit) (hMin : MonoNormalize.IsMonoJunkLeastAO G color C)
    (K₁ K₂ : Finset ℕ) (r₁ r₂ H : ℕ) (S T : Finset (Fin n))
    (hCone₁ : PrivateMixed.OrCone C K₁ r₁ S) (hCone₂ : PrivateMixed.OrCone C K₂ r₂ T)
    (hH : H < C.size) (hAnd : gateAt C H = ⟨GateOp.and, [n + r₁, n + r₂]⟩)
    (hPrivate : ∀ i < C.size, i ∉ insert H (K₁ ∪ K₂) → ∀ j ∈ insert H (K₁ ∪ K₂),
      n + j ∈ (gateAt C i).inputs → j = H) :
    Disjoint S T ∧ ∃ b : Bool, (∀ v ∈ S, color v = b) ∧ (∀ v ∈ T, color v = !b) := by
  exact private_or_factors_pure_opposite G color hBip hE C hMin K₁ K₂ r₁ r₂ H S T
    hCone₁ hCone₂ hH hAnd hPrivate
    (output_private_of_or_cones G C hMin.1 K₁ K₂ r₁ r₂ H S T hCone₁ hCone₂ hH (Or.inl hAnd))

end PEqualNP.Outside.L_meta_3566.PrivateClassification

namespace PEqualNP.Outside.L_meta_3566.RawPrivate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PrivateColorShell OnePureFrontier

lemma raw_or_value {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (K : Finset ℕ) (r H : ℕ) (a : Fin n) (T : Finset (Fin n))
    (hCone : PrivateMixed.OrCone C K r T) (hH : H < C.size)
    (hAnd : gateAt C H = ⟨GateOp.and, [a.val, n + r]⟩ ∨
      gateAt C H = ⟨GateOp.and, [n + r, a.val]⟩) (x : Fin n → Bool) :
    gateVal n C H x = (x a && orSet T x) := by
  obtain ⟨hr, hK, hOr, hClosed, hRead, hInputs, hAll⟩ := hCone
  have hrFun := PrivateCone.closed_or_cone_value n C hAO K r hr hK hOr hClosed hRead
    T hInputs hAll x
  have heq := LeafStep.Pruning.gate_eq C hAO H hH x
  rcases hAnd with h | h
  · simp only [h, LeafStep.Pruning.isA, LeafStep.Pruning.opv, opnd] at heq
    change gateVal n C H x = (wireVal n C a.val x && gateVal n C r x) at heq
    rw [heq, hrFun]
    change ((C.wires (List.ofFn x)).getD a.val false && _) = _
    rw [SharedRewrite.input_val]
  · simp only [h, LeafStep.Pruning.isA, LeafStep.Pruning.opv, opnd] at heq
    change gateVal n C H x = (gateVal n C r x && wireVal n C a.val x) at heq
    rw [heq, hrFun]
    change (_ && (C.wires (List.ofFn x)).getD a.val false) = _
    rw [SharedRewrite.input_val, Bool.and_comm]

lemma raw_not_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (K : Finset ℕ) (r H : ℕ)
    (a : Fin n) (T : Finset (Fin n)) (hCone : PrivateMixed.OrCone C K r T)
    (hH : H < C.size)
    (hAnd : gateAt C H = ⟨GateOp.and, [a.val, n + r]⟩ ∨
      gateAt C H = ⟨GateOp.and, [n + r, a.val]⟩) : a ∉ T := by
  intro ha
  apply Absorption.least_no_equivalent n G C hLeast H a.val hH (by omega)
    (InputAlias.least_output_bound_of_gate G C hLeast H hH)
  intro x
  change gateVal n C H x = (C.wires (List.ofFn x)).getD a.val false
  rw [raw_or_value C hLeast.1 K r H a T hCone hH hAnd x, SharedRewrite.input_val]
  cases hx : x a
  · simp
  · have hT : orSet T x = true := by
      exact decide_eq_true ⟨a, ha, hx⟩
    simp [hT]

lemma not_mixed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hBip : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hLeast : IsLeastAO G C) (K : Finset ℕ) (r H : ℕ)
    (a : Fin n) (T : Finset (Fin n)) (hCone : PrivateMixed.OrCone C K r T)
    (hH : H < C.size)
    (hAnd : gateAt C H = ⟨GateOp.and, [a.val, n + r]⟩ ∨
      gateAt C H = ⟨GateOp.and, [n + r, a.val]⟩)
    (hSame : ∃ t ∈ T, color t = color a)
    (hOpp : ∃ t ∈ T, color t = !(color a))
    (hPrivate : ∀ i < C.size, i ∉ insert H K → ∀ j ∈ insert H K,
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ insert H K, C.output = n + j → j = H) : False := by
  classical
  have haNot := raw_not_mem G C hLeast K r H a T hCone hH hAnd
  have hDisj : Disjoint ({a} : Finset (Fin n)) T := by simpa using haNot
  have hBoth : ∀ b : Bool, ∃ t ∈ T, color t = b := by
    intro b
    by_cases hb : b = color a
    · simpa [hb] using hSame
    · have hb' : b = !(color a) := by cases b <;> cases ha : color a <;> simp_all
      simpa [hb'] using hOpp
  have hPart : (part color (!(color a)) T).Nonempty := by
    obtain ⟨t, ht, hc⟩ := hOpp
    exact ⟨t, Finset.mem_filter.mpr ⟨ht, hc⟩⟩
  obtain ⟨Q, hQ, hQSize, hQFun, hq⟩ := OnePurePrivate.exists_and_or_sets {a}
    (part color (!(color a)) T) (by simp) hPart
  have hQCross : circuitFun n Q = cross color {a} T := by
    rw [hQFun]
    funext x
    exact (OnePurePrivate.cross_eq_of_pure_left color (color a) {a} T
      (by
        intro v hv
        have he : v = a := by simpa using hv
        exact congrArg color he) x).symm
  have hHFun (x : Fin n → Bool) : gateVal n C H x =
      (orSet {a} x && orSet T x) := by
    rw [raw_or_value C hLeast.1 K r H a T hCone hH hAnd]
    simp [orSet]
  obtain ⟨hr, hK, hOr, hClosed, hRead, hInputs, hAll⟩ := hCone
  have hOp : (gateAt C H).op = GateOp.and := by rcases hAnd with h | h <;> simp [h]
  have hHNot : H ∉ K := by
    intro hm
    have ho := hOr H hm
    rw [hOp] at ho
    cases ho
  have hJ : insert H K ⊆ Finset.range C.size := by
    intro j hj
    apply Finset.mem_range.mpr
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hH
    · exact hK j hj
  have hSize : Q.size < (insert H K).card := by
    have ht := PrivateCone.input_card_le_gates_add_one n K r hr (opnd C) T hInputs hRead
    have hp := OnePurePrivate.part_card_lt_of_both color (color a) T hBoth
    have hc : (insert H K).card = K.card + 1 := Finset.card_insert_of_notMem hHNot
    simp only [Finset.card_singleton] at hQSize
    omega
  apply PrivateCopy.not_of_least_size G Q C (insert H K) H hLeast hQ hq hJ hPrivate hOutput
  · intro x
    rw [hQCross, hHFun]
    exact cross_le color {a} T x
  · intro u v huv
    rw [hQCross, hHFun]
    exact cross_pair_eq color {a} T hDisj u v (hBip u v huv)
  · exact hSize

lemma support_opposite {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hBip : ∀ u v, G.Adj u v → color u ≠ color v)
    (hE : ∃ u v : Fin n, G.Adj u v)
    (C : Circuit) (hC : MonoNormalize.IsMonoJunkLeastAO G color C)
    (K : Finset ℕ) (r H : ℕ) (a : Fin n) (T : Finset (Fin n))
    (hCone : PrivateMixed.OrCone C K r T) (hH : H < C.size)
    (hAnd : gateAt C H = ⟨GateOp.and, [a.val, n + r]⟩ ∨
      gateAt C H = ⟨GateOp.and, [n + r, a.val]⟩)
    (hPrivate : ∀ i < C.size, i ∉ insert H K → ∀ j ∈ insert H K,
      n + j ∈ (gateAt C i).inputs → j = H)
    (hOutput : ∀ j ∈ insert H K, C.output = n + j → j = H) :
    a ∉ T ∧ ∀ t ∈ T, color t = !(color a) := by
  classical
  have haNot := raw_not_mem G C hC.1 K r H a T hCone hH hAnd
  refine ⟨haNot, ?_⟩
  intro t ht
  by_contra hn
  have hc : color t = color a := by cases ha : color a <;> cases hh : color t <;> simp_all
  have hOp : (gateAt C H).op = GateOp.and := by rcases hAnd with h | h <;> simp [h]
  have hDirty : H ∈ junk G C := by
    apply (JunkNormalize.mem_junk_iff G C H).mpr
    refine ⟨hH, hOp, MonoNormalize.input color (color a), ?_,
      MonoNormalize.input_false G color hBip (color a)⟩
    rw [raw_or_value C hC.1.1 K r H a T hCone hH hAnd]
    have htOn : orSet T (MonoNormalize.input color (color a)) = true :=
      decide_eq_true ⟨t, ht, by simp [MonoNormalize.input, hc]⟩
    simp [MonoNormalize.input, htOn]
  obtain ⟨u, v, _, _, huv, _, hp, _, _⟩ :=
    MonoNormalize.dirty_has_two_pivotal_edges G color hBip hE C hC H hDirty
  have hOn := JunkPivotal.pivotal_on G C hC.1.1 hC.1.2.1 H hH u v huv hp
  rw [raw_or_value C hC.1.1 K r H a T hCone hH hAnd] at hOn
  have hOn' : pairInput u v a = true ∧ orSet T (pairInput u v) = true := by simpa using hOn
  have haEdge : a = u ∨ a = v := by simpa [pairInput] using hOn'.1
  obtain ⟨w, hw, hwOn⟩ : ∃ w ∈ T, pairInput u v w = true := of_decide_eq_true hOn'.2
  have hwEdge : w = u ∨ w = v := by simpa [pairInput] using hwOn
  have hwa : w ≠ a := by intro he; subst w; exact haNot hw
  have hNe : color w ≠ color a := by
    rcases haEdge with rfl | rfl <;> rcases hwEdge with rfl | rfl
    · exact False.elim (hwa rfl)
    · exact Ne.symm (hBip _ _ huv)
    · exact hBip _ _ huv
    · exact False.elim (hwa rfl)
  have hwColor : color w = !(color a) := by
    cases ha : color a <;> cases hh : color w <;> simp_all
  exact not_mixed G color hBip C hC.1 K r H a T hCone hH hAnd
    ⟨t, ht, hc⟩ ⟨w, hw, hwColor⟩ hPrivate hOutput

end PEqualNP.Outside.L_meta_3566.RawPrivate

namespace PEqualNP.Outside.L_meta_3566.RawPrivate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma support_opposite_of_read_privacy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hBip : ∀ u v, G.Adj u v → color u ≠ color v)
    (hE : ∃ u v : Fin n, G.Adj u v)
    (C : Circuit) (hC : MonoNormalize.IsMonoJunkLeastAO G color C)
    (K : Finset ℕ) (r H : ℕ) (a : Fin n) (T : Finset (Fin n))
    (hCone : PrivateMixed.OrCone C K r T) (hH : H < C.size)
    (hAnd : gateAt C H = ⟨GateOp.and, [a.val, n + r]⟩ ∨
      gateAt C H = ⟨GateOp.and, [n + r, a.val]⟩)
    (hPrivate : ∀ i < C.size, i ∉ insert H K → ∀ j ∈ insert H K,
      n + j ∈ (gateAt C i).inputs → j = H) :
    a ∉ T ∧ ∀ t ∈ T, color t = !(color a) := by
  have hLast := PrivateClassification.least_output_eq_last G C hC.1 H hH
  have hBack : n + r < n + H := hC.1.1.2.1 H hH (n + r) (by
    rcases hAnd with h | h <;> simp [h])
  have hK := PrivateClassification.cone_gate_le_root C hC.1.1 K r T hCone
  apply support_opposite G color hBip hE C hC K r H a T hCone hH hAnd hPrivate
  intro j hj hOut
  rcases Finset.mem_insert.mp hj with rfl | hj
  · rfl
  · have := hK j hj
    omega

end PEqualNP.Outside.L_meta_3566.RawPrivate
