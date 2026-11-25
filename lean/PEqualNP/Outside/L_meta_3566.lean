import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace PEqualNP.Outside.L_meta_3566

namespace AO2Upper

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

end AO2Upper



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


namespace FalseRestrict

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

end FalseRestrict

namespace OrLoss

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.AO2Upper
open PEqualNP.Outside.L_meta_3566.FalseRestrict

def isOr : GateOp → Bool
  | .or => true
  | _ => false

def orCount (gs : List Gate) : ℕ := gs.countP (fun g => isOr g.op)

def orFlag (σ : List (Option ℕ)) (g : Gate) : Bool :=
  isOr g.op && ((σ.getD (g.inputs.getD 0 0) none).isNone ||
    (σ.getD (g.inputs.getD 1 0) none).isNone)

def savedOr (m : ℕ) (σ : List (Option ℕ)) : List Gate → ℕ
  | [] => 0
  | g :: gs =>
      let r := emit m σ g
      (if orFlag σ g then 1 else 0) +
        savedOr (m + r.1.length) (σ ++ [r.2]) gs

lemma reduce_or_count (m : ℕ) (op : GateOp) (a b : Option ℕ) :
    orCount (reduceGate m op a b).1 +
      (if isOr op && (a.isNone || b.isNone) then 1 else 0) =
        (if isOr op then 1 else 0) := by
  cases op <;> cases a <;> cases b <;> simp [reduceGate, orCount, isOr]

lemma compile_or_count (gs : List Gate) (m : ℕ) (σ : List (Option ℕ)) :
    orCount (compile m σ gs).1 + savedOr m σ gs = orCount gs := by
  induction gs generalizing m σ with
  | nil => simp [compile, savedOr, orCount]
  | cons g gs ih =>
    have hstep := reduce_or_count m g.op (σ.getD (g.inputs.getD 0 0) none)
      (σ.getD (g.inputs.getD 1 0) none)
    have hrest := ih (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2])
    change orCount (emit m σ g).1 + (if orFlag σ g then 1 else 0) =
      (if isOr g.op then 1 else 0) at hstep
    simp only [compile, savedOr, orCount, List.countP_append, List.countP_cons]
    change orCount (emit m σ g).1 +
      orCount (compile (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2]) gs).1 +
      ((if orFlag σ g then 1 else 0) +
        savedOr (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2]) gs) =
      orCount gs + (if isOr g.op then 1 else 0)
    omega

lemma reduce_alive_parents (m : ℕ) (op : GateOp) (a b : Option ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (hflag : (isOr op && (a.isNone || b.isNone)) = false)
    (halive : (reduceGate m op a b).2.isNone = false) :
    a.isNone = false ∧ b.isNone = false := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [reduceGate, isOr]

def AliveAgree (σ : List (Option ℕ)) (s t : List Bool) : Prop :=
  s.length = σ.length ∧ t.length = σ.length ∧
    ∀ i, (σ.getD i none).isNone = false → s.getD i false = t.getD i false

lemma alive_step (m : ℕ) (σ : List (Option ℕ)) (s t : List Bool) (g : Gate)
    (h : AliveAgree σ s t) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2) (hflag : orFlag σ g = false) :
    AliveAgree (σ ++ [(emit m σ g).2])
      (s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)])
      (t ++ [g.op.eval (g.inputs.map fun i => t.getD i false)]) := by
  refine ⟨by simp [h.1], by simp [h.2.1], ?_⟩
  intro i hi
  by_cases heq : i = σ.length
  · subst i
    rw [getD_snoc_eq] at hi
    have hp := reduce_alive_parents m g.op
      (σ.getD (g.inputs.getD 0 0) none) (σ.getD (g.inputs.getD 1 0) none)
      hop hflag hi
    obtain ⟨a, b, hg⟩ := List.length_eq_two.mp hlen
    have ha : s.getD a false = t.getD a false :=
      h.2.2 a (by simpa [hg] using hp.1)
    have hb : s.getD b false = t.getD b false :=
      h.2.2 b (by simpa [hg] using hp.2)
    rw [← h.1, getD_snoc_eq, h.1, ← h.2.1, getD_snoc_eq]
    simp only [hg, List.map_cons, List.map_nil]
    rw [ha, hb]
  · rw [getD_snoc_ne _ _ _ _ heq] at hi
    have hs := h.1
    have ht := h.2.1
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    exact h.2.2 i hi

lemma compile_alive_agree (gs : List Gate) (m : ℕ) (σ : List (Option ℕ))
    (s t : List Bool) (h : AliveAgree σ s t)
    (hbasis : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hzero : savedOr m σ gs = 0) :
    AliveAgree (compile m σ gs).2 (wiresFrom gs s) (wiresFrom gs t) := by
  induction gs generalizing m σ s t with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hbasis g List.mem_cons_self
    have hflag : orFlag σ g = false := by
      cases hf : orFlag σ g
      · rfl
      · simp [savedOr, hf] at hzero
    have hrest : savedOr (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2]) gs = 0 := by
      simpa [savedOr, hflag] using hzero
    exact ih _ _ _ _ (alive_step m σ s t g h hop hlen hflag)
      (fun g' hg' => hbasis g' (List.mem_cons_of_mem g hg')) hrest

lemma initial_alive_agree (n : ℕ) (z : Fin n) (x : Fin n → Bool) :
    AliveAgree (initialMap n z) (List.ofFn x) (List.ofFn (Function.update x z false)) := by
  refine ⟨by simp [initialMap], by simp [initialMap], ?_⟩
  intro i hi
  by_cases hi' : i < n
  · have hiz : (⟨i, hi'⟩ : Fin n) ≠ z := by
      intro heq
      simp [initialMap, hi', heq] at hi
    simp [List.getD_eq_getElem?_getD, hi', hiz]
  · simp [hi']


lemma exists_restriction_or_loss (n : ℕ) (z : Fin n) (C : Circuit)
    (hAO : IsAO2 n C)
    (htrue : ∃ y : Fin n → Bool, circuitFun n C (Function.update y z false) = true)
    (hdepends : ∃ x : Fin n → Bool,
      circuitFun n C x ≠ circuitFun n C (Function.update x z false)) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => circuitFun n C (Function.update y z false)) ∧
      orCount D.gates + 1 ≤ orCount C.gates := by
  have hbasis : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    exact ⟨hAO.1 g hg, hAO.2.2 g hg⟩
  have hpos : 1 ≤ savedOr n (initialMap n z) C.gates := by
    by_contra hnot
    have hzero : savedOr n (initialMap n z) C.gates = 0 := by omega
    obtain ⟨y, hy⟩ := htrue
    have hrel := (compile_correct C.gates (initialMap n z)
      (List.ofFn (Function.update y z false)) (List.ofFn y) (initial_rel n z y) hbasis).2
    simp only [List.length_ofFn] at hrel
    have hout : ((compile n (initialMap n z) C.gates).2.getD C.output none).isNone = false := by
      cases he : (compile n (initialMap n z) C.gates).2.getD C.output none with
      | none =>
        have h := hrel.2.2 C.output
        rw [he] at h
        change circuitFun n C (Function.update y z false) = false at h
        rw [hy] at h
        contradiction
      | some a => rfl
    obtain ⟨x, hx⟩ := hdepends
    have heq := (compile_alive_agree C.gates n (initialMap n z)
      (List.ofFn x) (List.ofFn (Function.update x z false))
      (initial_alive_agree n z x) hbasis hzero).2.2 C.output hout
    exact hx heq
  obtain ⟨hD, hF, _⟩ := restricted_spec n z C hAO
  refine ⟨restricted n z C, hD, hF, ?_⟩
  have hc := compile_or_count C.gates n (initialMap n z)
  change orCount (compile n (initialMap n z) C.gates).1 + 1 ≤ orCount C.gates
  omega

lemma graphFun_false_restriction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) :
    (fun y : Fin n → Bool => graphFun G ∅ (Function.update y z false)) =
      graphFun (G.deleteEdges (G.incidenceSet z)) ∅ := by
  classical
  funext y
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false,
    decide_false, Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have haz : a ≠ z := by intro h; subst a; simp at ha
    have hbz : b ≠ z := by intro h; subst b; simp at hb
    exact ⟨a, b, (PEqualNP.Outside.L_meta_3566.cut_adj G z a b).mpr ⟨hab, haz, hbz⟩,
      by simpa [haz] using ha, by simpa [hbz] using hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hab, haz, hbz⟩ := (PEqualNP.Outside.L_meta_3566.cut_adj G z a b).mp hab
    exact ⟨a, b, hab, by simpa [haz] using ha, by simpa [hbz] using hb⟩

lemma graph_restriction_or_loss {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (hdeg : 0 < G.degree z)
    (hcut : ∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b)
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = graphFun (G.deleteEdges (G.incidenceSet z)) ∅ ∧
      orCount D.gates + 1 ≤ orCount C.gates := by
  classical
  have htrue : ∃ y : Fin n → Bool, circuitFun n C (Function.update y z false) = true := by
    obtain ⟨a, b, hab⟩ := hcut
    obtain ⟨hab, haz, hbz⟩ := (PEqualNP.Outside.L_meta_3566.cut_adj G z a b).mp hab
    refine ⟨fun _ => true, ?_⟩
    rw [hfun]
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false,
      decide_false, Bool.false_or, decide_eq_true_eq]
    exact ⟨a, b, hab, by simp [haz], by simp [hbz]⟩
  have hdepends : ∃ x : Fin n → Bool,
      circuitFun n C x ≠ circuitFun n C (Function.update x z false) := by
    obtain ⟨w, hzw⟩ := (G.degree_pos_iff_exists_adj z).mp hdeg
    let x : Fin n → Bool := fun i => decide (i = z ∨ i = w)
    have hwz : w ≠ z := hzw.ne.symm
    have hupdate : Function.update x z false = fun i => decide (i = w) := by
      funext i
      by_cases hiz : i = z
      · subst i
        simp [hwz.symm]
      · simp [x, hiz]
    have hbefore : graphFun G ∅ x = true := by
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false,
        decide_false, Bool.false_or, decide_eq_true_eq]
      exact ⟨z, w, hzw, by simp [x], by simp [x]⟩
    have hafter : graphFun G ∅ (Function.update x z false) = false := by
      rw [hupdate]
      simp [graphFun]
    refine ⟨x, ?_⟩
    rw [hfun, hbefore, hafter]
    decide
  obtain ⟨D, hD, hf, hc⟩ := exists_restriction_or_loss n z C hAO htrue hdepends
  refine ⟨D, hD, ?_, hc⟩
  rw [hfun] at hf
  exact hf.trans (graphFun_false_restriction G z)

end OrLoss

lemma monotone_graph_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (hedge : ∀ a b, G.Adj a b →
      f (fun i => decide (i = a ∨ i = b)) = true)
    (hindep : ∀ S : Set (Fin n), Maximal G.IsIndepSet S →
      f (fun i => @decide (i ∈ S) (Classical.propDecidable _)) = false) :
    f = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  classical
  funext x
  by_cases hx : ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true
  · obtain ⟨a, b, hab, ha, hb⟩ := hx
    have hle : (fun i => decide (i = a ∨ i = b)) ≤ x := by
      intro i
      apply Bool.le_iff_imp.mpr
      intro hi
      have hi' : i = a ∨ i = b := of_decide_eq_true hi
      rcases hi' with rfl | rfl
      · exact ha
      · exact hb
    have hfx : f x = true := by
      have h := hf hle
      rw [hedge a b hab] at h
      exact Bool.le_iff_imp.mp h rfl
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun, hfx,
      show ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true from ⟨a, b, hab, ha, hb⟩]
  · have hs : G.IsIndepSet {i | x i = true} := by
      intro a ha b hb hne hab
      exact hx ⟨a, b, hab, ha, hb⟩
    obtain ⟨S, hsub, hmax⟩ := Finite.exists_le_maximal hs
    have hle : x ≤ (fun i => decide (i ∈ S)) := by
      intro i
      apply Bool.le_iff_imp.mpr
      intro hi
      exact decide_eq_true (hsub hi)
    have hfx : f x = false := by
      have h := hf hle
      rw [hindep S hmax] at h
      cases heq : f x <;> simp_all [Bool.le_iff_imp]
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun, hfx, hx]

lemma positive_closure {ι α β : Type*} (P : ι → Set α) (N : ι → Set β) (J : Set ι) :
    let S := ⋂ i ∈ J, P i
    let K := {i | S ⊆ P i}
    J ⊆ K ∧ (⋂ i ∈ K, P i) = S ∧ (⋂ i ∈ K, N i) ⊆ ⋂ i ∈ J, N i := by
  dsimp only
  have hJK : J ⊆ {i | (⋂ j ∈ J, P j) ⊆ P i} := by
    intro i hi x hx
    simp only [Set.mem_iInter] at hx
    exact hx i hi
  refine ⟨hJK, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      simp only [Set.mem_iInter] at hx ⊢
      intro i hi
      exact hx i (hJK hi)
    · intro x hx
      simp only [Set.mem_iInter]
      intro i hi
      exact hi hx
  · intro x hx
    simp only [Set.mem_iInter] at hx ⊢
    intro i hi
    exact hx i (hJK hi)

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity

abbrev subdivisionK4 : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel fun a b => (a.val, b.val) ∈ ([(0, 8), (0, 9), (1, 7), (1, 9), (2, 7), (2, 8), (3, 6), (3, 9), (4, 6), (4, 8), (5, 6), (5, 7)] : List (ℕ × ℕ))

def subdivisionK4Circuit : Circuit :=
  ⟨[⟨.or, [3, 4]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.and, [6, 11]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [5, 13]⟩,
    ⟨.and, [7, 14]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [4, 16]⟩,
    ⟨.and, [8, 17]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [3, 19]⟩,
    ⟨.and, [9, 20]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [18, 22]⟩,
    ⟨.or, [21, 23]⟩], 24⟩

lemma subdivisionK4_ao2 : IsAO2 10 subdivisionK4Circuit := by decide

lemma subdivisionK4_size : subdivisionK4Circuit.size = 15 := by decide

lemma subdivisionK4_bipartite :
    ∀ a b : Fin 10, subdivisionK4.Adj a b → decide (a.val < 6) ≠ decide (b.val < 6) := by decide

lemma subdivisionK4_noFourCycle : NoFourCycle subdivisionK4 := by decide

lemma subdivisionK4_card : subdivisionK4.edgeFinset.card = 12 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma subdivisionK4_circuit : circuitFun 10 subdivisionK4Circuit = NestedCover.graphFun subdivisionK4 ∅ := by
  funext x
  revert x
  decide

lemma subdivisionK4_cover :
    PEqualNP.MetaComplexity.CoverPromise.IsVertexCover subdivisionK4
      ({6, 7, 8, 9} : Finset (Fin 10)) := by
  unfold PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma subdivisionK4_cover_minimum :
    ∀ S : Finset (Fin 10),
      PEqualNP.MetaComplexity.CoverPromise.IsVertexCover subdivisionK4 S → 4 ≤ S.card := by
  unfold PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
  decide

namespace LeafOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.OrLoss

def OrLower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ →
    G.edgeFinset.card ≤ orCount C.gates + 1

lemma or_lower_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hsmall : G.edgeFinset.card ≤ 1) : OrLower G := by
  intro C hAO hfun
  omega

lemma adjacent_of_edge_card_pos {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hpos : 0 < G.edgeFinset.card) : ∃ a b : Fin n, G.Adj a b := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  revert he
  refine Sym2.ind (fun a b => ?_) e
  intro he
  exact ⟨a, b, by simpa using he⟩

lemma leaf_step {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (hdeg : G.degree z = 1)
    (hcut : OrLower (G.deleteEdges (G.incidenceSet z))) : OrLower G := by
  classical
  have hcount := PEqualNP.Outside.L_meta_3566.cut_edge_count G z
  by_cases hzero : (G.deleteEdges (G.incidenceSet z)).edgeFinset.card = 0
  · exact or_lower_small G (by omega)
  · have hnonempty := adjacent_of_edge_card_pos (G.deleteEdges (G.incidenceSet z)) (by omega)
    intro C hAO hfun
    obtain ⟨D, hD, hF, hOr⟩ := graph_restriction_or_loss G z (by omega) hnonempty C hAO hfun
    have hbound := hcut D hD hF
    omega

lemma acyclic_has_leaf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic) (hpos : 0 < G.edgeFinset.card) :
    ∃ z : Fin n, G.degree z = 1 := by
  classical
  obtain ⟨a, b, hab⟩ := adjacent_of_edge_card_pos G hpos
  let : Nonempty (Fin n) := ⟨a⟩
  obtain ⟨u, v, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hp' := (SimpleGraph.Path.singleton hab).property
  have hlen := hmax a b (SimpleGraph.Path.singleton hab).val hp'
  have hnil : ¬p.Nil := by
    have hone : (SimpleGraph.Path.singleton hab).val.length = 1 := rfl
    grind
  refine ⟨u, ?_⟩
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  refine ⟨_, p.adj_snd hnil, fun w hadj => ?_⟩
  apply hacyclic.eq_snd_of_adj_start hp hadj
  have : ¬(p.cons hadj.symm).IsPath := by grind [SimpleGraph.Walk.length_cons]
  grind [hp.cons]

lemma forest_or_lower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic) : OrLower G := by
  classical
  have hall : ∀ m : ℕ, ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      H.edgeFinset.card = m → H.IsAcyclic → OrLower H := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro H hdec hcard hA
      by_cases hsmall : m ≤ 1
      · exact or_lower_small H (by omega)
      · obtain ⟨z, hz⟩ := acyclic_has_leaf H hA (by omega)
        apply leaf_step H z hz
        have hcount := PEqualNP.Outside.L_meta_3566.cut_edge_count H z
        exact ih (H.deleteEdges (H.incidenceSet z)).edgeFinset.card (by omega)
          (H.deleteEdges (H.incidenceSet z)) rfl
          (hA.anti (H.deleteEdges_le (H.incidenceSet z)))
  exact hall _ G rfl hacyclic

end LeafOr

namespace AndSignature

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.AO2Upper
open PEqualNP.Outside.L_meta_3566.FalseRestrict

def isAnd : GateOp → Bool
  | .and => true
  | _ => false

def andCount (gs : List Gate) : ℕ := gs.countP (fun g => isAnd g.op)

def step (g : Gate) (s : List Bool) : List Bool :=
  s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]

def sigRun : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, s =>
      (if isAnd g.op then [s.getD (g.inputs.getD 0 0) false] else []) ++
        sigRun gs (step g s)

lemma sigRun_length (gs : List Gate) (s : List Bool) :
    (sigRun gs s).length = andCount gs := by
  induction gs generalizing s with
  | nil => simp [sigRun, andCount]
  | cons g gs ih =>
    simp only [sigRun, List.length_append, ih, andCount, List.countP_cons]
    cases isAnd g.op <;> simp [Nat.add_comm]

def JoinRel (s t u : List Bool) : Prop :=
  s.length = t.length ∧ s.length = u.length ∧
    ∀ i, u.getD i false = (s.getD i false || t.getD i false)

lemma gate_join (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b c d : Bool) (hleft : op = GateOp.and → a = c) :
    op.eval [a || c, b || d] = (op.eval [a, b] || op.eval [c, d]) := by
  rcases hop with rfl | rfl <;>
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all [GateOp.eval]

lemma step_join (g : Gate) (s t u : List Bool) (h : JoinRel s t u)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2)
    (hleft : g.op = GateOp.and →
      s.getD (g.inputs.getD 0 0) false = t.getD (g.inputs.getD 0 0) false) :
    JoinRel (step g s) (step g t) (step g u) := by
  refine ⟨by simp [step, h.1], by simp [step, h.2.1], ?_⟩
  intro i
  by_cases hi : i = s.length
  · subst i
    have ht := h.1
    have hu := h.2.1
    unfold step
    rw [getD_snoc_eq, ht, getD_snoc_eq, ← ht, hu, getD_snoc_eq]
    obtain ⟨a, b, hg⟩ := List.length_eq_two.mp hlen
    have hl : g.op = GateOp.and → s.getD a false = t.getD a false := by
      simpa [hg] using hleft
    simp only [hg, List.map_cons, List.map_nil]
    rw [h.2.2 a, h.2.2 b]
    exact gate_join g.op hop _ _ _ _ hl
  · have ht := h.1
    have hu := h.2.1
    unfold step
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ hi,
      getD_snoc_ne _ _ _ _ (by omega)]
    exact h.2.2 i

lemma sigRun_join (gs : List Gate) (s t u : List Bool) (h : JoinRel s t u)
    (hbasis : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hsig : sigRun gs s = sigRun gs t) :
    JoinRel (wiresFrom gs s) (wiresFrom gs t) (wiresFrom gs u) := by
  induction gs generalizing s t u with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hbasis g List.mem_cons_self
    have htail : sigRun gs (step g s) = sigRun gs (step g t) := by
      rcases hop with hp | hp
      · have hpair :
            s.getD (g.inputs.getD 0 0) false = t.getD (g.inputs.getD 0 0) false ∧
            sigRun gs (step g s) = sigRun gs (step g t) := by
          simpa [sigRun, isAnd, hp] using hsig
        exact hpair.2
      · simpa [sigRun, isAnd, hp] using hsig
    have hleft : g.op = GateOp.and →
        s.getD (g.inputs.getD 0 0) false = t.getD (g.inputs.getD 0 0) false := by
      intro hp
      have hpair :
          s.getD (g.inputs.getD 0 0) false = t.getD (g.inputs.getD 0 0) false ∧
          sigRun gs (step g s) = sigRun gs (step g t) := by
        simpa [sigRun, isAnd, hp] using hsig
      exact hpair.1
    exact ih _ _ _ (step_join g s t u h hop hlen hleft)
      (fun g' hg' => hbasis g' (List.mem_cons_of_mem g hg')) htail

def signature (n : ℕ) (C : Circuit) (x : Fin n → Bool) : List Bool :=
  sigRun C.gates (List.ofFn x)

lemma signature_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (signature n C x).length = andCount C.gates := sigRun_length _ _

lemma same_signature_join (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hsig : signature n C x = signature n C y) :
    circuitFun n C (fun i => x i || y i) = (circuitFun n C x || circuitFun n C y) := by
  have hinit : JoinRel (List.ofFn x) (List.ofFn y) (List.ofFn fun i => x i || y i) := by
    refine ⟨by simp, by simp, ?_⟩
    intro i
    by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD, hi]
  exact (sigRun_join C.gates _ _ _ hinit
    (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩) hsig).2.2 C.output

def signatureFn (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    Fin (andCount C.gates) → Bool := fun i => (signature n C x).getD i.val false

lemma signature_eq_of_fn_eq (n : ℕ) (C : Circuit) (x y : Fin n → Bool)
    (h : signatureFn n C x = signatureFn n C y) : signature n C x = signature n C y := by
  apply List.ext_getElem
  · rw [signature_length, signature_length]
  · intro i hi hj
    have hi' : i < andCount C.gates := by simpa [signature_length] using hi
    have hv := congrFun h ⟨i, hi'⟩
    simpa [signatureFn, List.getD_eq_getElem?_getD, hi, hj] using hv

lemma false_family_card_bound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (S : Finset (Fin n → Bool))
    (hfalse : ∀ x ∈ S, circuitFun n C x = false)
    (hjoin : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → circuitFun n C (fun i => x i || y i) = true) :
    S.card ≤ 2 ^ andCount C.gates := by
  classical
  have hinj : Function.Injective (fun x : ↥S => signatureFn n C x.val) := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hsig := signature_eq_of_fn_eq n C x.val y.val hxy
    have heq := same_signature_join n C hAO x.val y.val hsig
    rw [hfalse _ x.property, hfalse _ y.property, hjoin _ x.property _ y.property hne] at heq
    contradiction
  have hcard := Fintype.card_le_of_injective _ hinj
  simpa using hcard

lemma maximal_false_family_card_bound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (S : Finset (Fin n → Bool))
    (hmax : ∀ x ∈ S, Maximal (fun y => circuitFun n C y = false) x) :
    S.card ≤ 2 ^ andCount C.gates := by
  apply false_family_card_bound n C hAO S
  · intro x hx
    exact (hmax x hx).1
  · intro x hx y hy hne
    let u : Fin n → Bool := fun i => x i || y i
    have hxu : x ≤ u := by
      intro i
      apply Bool.le_iff_imp.mpr
      intro hi
      simp [u, hi]
    have hyu : y ≤ u := by
      intro i
      apply Bool.le_iff_imp.mpr
      intro hi
      simp [u, hi]
    by_contra hf
    have huf : circuitFun n C u = false := by
      cases he : circuitFun n C u <;> simp_all [u]
    have hux : u ≤ x := (hmax x hx).2 huf hxu
    have huy : u ≤ y := (hmax y hy).2 huf hyu
    exact hne (le_antisymm (hxu.trans huy) (hyu.trans hux))

def charInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ S)

lemma charInput_injective {n : ℕ} : Function.Injective (@charInput n) := by
  intro S T h
  ext i
  have hi := Bool.eq_iff_iff.mp (congrFun h i)
  simpa [charInput] using hi

lemma independent_family_card_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (F : Finset (Finset (Fin n)))
    (hindep : ∀ S ∈ F, G.IsIndepSet (S : Set (Fin n)))
    (hpairs : ∀ S ∈ F, ∀ T ∈ F, S ≠ T →
      ∃ a ∈ S ∪ T, ∃ b ∈ S ∪ T, G.Adj a b) :
    F.card ≤ 2 ^ andCount C.gates := by
  classical
  have hbound := false_family_card_bound n C hAO (F.image charInput) ?_ ?_
  · simpa only [Finset.card_image_of_injective F charInput_injective] using hbound
  · intro x hx
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
    rw [hfun]
    have hno : ¬ ∃ a b, G.Adj a b ∧ charInput S a = true ∧ charInput S b = true := by
      rintro ⟨a, b, hab, ha, hb⟩
      exact hindep S hS (of_decide_eq_true ha) (of_decide_eq_true hb) hab.ne hab
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun, hno]
  · intro x hx y hy hne
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hy
    have hST : S ≠ T := by intro h; subst T; exact hne rfl
    obtain ⟨a, ha, b, hb, hab⟩ := hpairs S hS T hT hST
    rw [hfun]
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
      false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
    exact ⟨a, b, hab, by simpa [charInput] using ha, by simpa [charInput] using hb⟩

lemma maximal_independent_family_card_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (F : Finset (Finset (Fin n)))
    (hmax : ∀ S ∈ F, Maximal (fun T : Finset (Fin n) => G.IsIndepSet (T : Set (Fin n))) S) :
    F.card ≤ 2 ^ andCount C.gates := by
  apply independent_family_card_bound G C hAO hfun F
    (fun S hS => (hmax S hS).1)
  intro S hS T hT hne
  by_contra hno
  have hU : G.IsIndepSet ((S ∪ T : Finset (Fin n)) : Set (Fin n)) := by
    intro a ha b hb hab hAdj
    exact hno ⟨a, ha, b, hb, hAdj⟩
  have hUS : S ∪ T ⊆ S := (hmax S hS).2 hU Finset.subset_union_left
  have hUT : S ∪ T ⊆ T := (hmax T hT).2 hU Finset.subset_union_right
  exact hne (Finset.Subset.antisymm (Finset.subset_union_left.trans hUT)
    (Finset.subset_union_right.trans hUS))

end AndSignature

namespace AndPacking

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.AO2Upper
open PEqualNP.Outside.L_meta_3566.FalseRestrict
open PEqualNP.Outside.L_meta_3566.AndSignature

abbrev State := Bool × Bool

/-- Opposite unequal operand states, the only obstruction to distributing AND over join. -/
def Cross (p q : State) : Prop :=
  (p = (true, false) ∧ q = (false, true)) ∨
    (p = (false, true) ∧ q = (true, false))

/-- Equal operands leave a signature bit free; unequal operands fix it to the left value. -/
def allowed (p : State) : Finset Bool :=
  if p.1 = p.2 then Finset.univ else {p.1}

lemma not_cross_of_common (p q : State) (b : Bool)
    (hp : b ∈ allowed p) (hq : b ∈ allowed q) : ¬ Cross p q := by
  rcases p with ⟨a, c⟩
  rcases q with ⟨d, e⟩
  cases a <;> cases c <;> cases d <;> cases e <;> cases b <;>
    simp_all [allowed, Cross]

lemma gate_join_no_cross (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b c d : Bool) (h : op = GateOp.and → ¬ Cross (a, b) (c, d)) :
    op.eval [a || c, b || d] = (op.eval [a, b] || op.eval [c, d]) := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [GateOp.eval, Cross]

lemma step_join_no_cross (g : Gate) (s t u : List Bool) (h : JoinRel s t u)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2)
    (hcross : g.op = GateOp.and → ¬ Cross
      (s.getD (g.inputs.getD 0 0) false, s.getD (g.inputs.getD 1 0) false)
      (t.getD (g.inputs.getD 0 0) false, t.getD (g.inputs.getD 1 0) false)) :
    JoinRel (step g s) (step g t) (step g u) := by
  refine ⟨by simp [step, h.1], by simp [step, h.2.1], ?_⟩
  intro i
  by_cases hi : i = s.length
  · subst i
    have ht := h.1
    have hu := h.2.1
    unfold step
    rw [getD_snoc_eq, ht, getD_snoc_eq, ← ht, hu, getD_snoc_eq]
    obtain ⟨a, b, hg⟩ := List.length_eq_two.mp hlen
    have hc : g.op = GateOp.and → ¬ Cross
        (s.getD a false, s.getD b false) (t.getD a false, t.getD b false) := by
      simpa [hg] using hcross
    simp only [hg, List.map_cons, List.map_nil]
    rw [h.2.2 a, h.2.2 b]
    exact gate_join_no_cross g.op hop _ _ _ _ hc
  · have ht := h.1
    have hu := h.2.1
    unfold step
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ hi,
      getD_snoc_ne _ _ _ _ (by omega)]
    exact h.2.2 i

def traceRun : List Gate → List Bool → List State
  | [], _ => []
  | g :: gs, s =>
      (if isAnd g.op then
        [(s.getD (g.inputs.getD 0 0) false, s.getD (g.inputs.getD 1 0) false)] else []) ++
        traceRun gs (step g s)

lemma traceRun_length (gs : List Gate) (s : List Bool) :
    (traceRun gs s).length = andCount gs := by
  induction gs generalizing s with
  | nil => simp [traceRun, andCount]
  | cons g gs ih =>
    simp only [traceRun, List.length_append, ih, andCount, List.countP_cons]
    cases isAnd g.op <;> simp [Nat.add_comm]

lemma traceRun_join (gs : List Gate) (s t u : List Bool) (h : JoinRel s t u)
    (hbasis : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hcross : ∀ i < andCount gs,
      ¬ Cross ((traceRun gs s).getD i (false, false)) ((traceRun gs t).getD i (false, false))) :
    JoinRel (wiresFrom gs s) (wiresFrom gs t) (wiresFrom gs u) := by
  induction gs generalizing s t u with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hbasis g List.mem_cons_self
    have hhead : g.op = GateOp.and → ¬ Cross
        (s.getD (g.inputs.getD 0 0) false, s.getD (g.inputs.getD 1 0) false)
        (t.getD (g.inputs.getD 0 0) false, t.getD (g.inputs.getD 1 0) false) := by
      intro hp
      have hz : 0 < andCount (g :: gs) := by simp [andCount, hp, isAnd]
      simpa [traceRun, hp, isAnd] using hcross 0 hz
    have htail : ∀ i < andCount gs, ¬ Cross
        ((traceRun gs (step g s)).getD i (false, false))
        ((traceRun gs (step g t)).getD i (false, false)) := by
      intro i hi
      rcases hop with hp | hp
      · have hib : i + 1 < andCount (g :: gs) := by
          simp only [andCount, List.countP_cons, hp, isAnd, ↓reduceIte]
          exact Nat.add_lt_add_right hi 1
        simpa [traceRun, hp, isAnd] using hcross (i + 1) hib
      · have hib : i < andCount (g :: gs) := by simpa [andCount, hp, isAnd] using hi
        simpa [traceRun, hp, isAnd] using hcross i hib
    exact ih _ _ _ (step_join_no_cross g s t u h hop hlen hhead)
      (fun g' hg' => hbasis g' (List.mem_cons_of_mem g hg')) htail

def stateFn (n : ℕ) (C : Circuit) (x : Fin n → Bool) : Fin (andCount C.gates) → State :=
  fun i => (traceRun C.gates (List.ofFn x)).getD i.val (false, false)

lemma no_cross_join (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x y : Fin n → Bool)
    (hcross : ∀ i, ¬ Cross (stateFn n C x i) (stateFn n C y i)) :
    circuitFun n C (fun i => x i || y i) = (circuitFun n C x || circuitFun n C y) := by
  have hinit : JoinRel (List.ofFn x) (List.ofFn y) (List.ofFn fun i => x i || y i) := by
    refine ⟨by simp, by simp, ?_⟩
    intro i
    by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD, hi]
  exact (traceRun_join C.gates _ _ _ hinit
    (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩) (fun i hi => hcross ⟨i, hi⟩)).2.2 C.output

/-- Two false inputs with a true union have opposite unequal states at some AND gate. -/
lemma exists_and_cross (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hx : circuitFun n C x = false) (hy : circuitFun n C y = false)
    (hunion : circuitFun n C (fun i => x i || y i) = true) :
    ∃ i : Fin (andCount C.gates), Cross (stateFn n C x i) (stateFn n C y i) := by
  by_contra h
  push Not at h
  have heq := no_cross_join n C hAO x y h
  rw [hunion, hx, hy] at heq
  contradiction

def cube {k : ℕ} (p : Fin k → State) : Finset (Fin k → Bool) :=
  Fintype.piFinset fun i => allowed (p i)

def wildCount {k : ℕ} (p : Fin k → State) : ℕ :=
  (Finset.univ.filter fun i => (p i).1 = (p i).2).card

lemma cube_disjoint_of_cross {k : ℕ} (p q : Fin k → State)
    (hcross : ∃ i, Cross (p i) (q i)) : Disjoint (cube p) (cube q) := by
  apply Finset.disjoint_left.mpr
  intro f hp hq
  obtain ⟨i, hi⟩ := hcross
  exact not_cross_of_common (p i) (q i) (f i)
    (Fintype.mem_piFinset.mp hp i) (Fintype.mem_piFinset.mp hq i) hi

lemma cube_card {k : ℕ} (p : Fin k → State) : (cube p).card = 2 ^ wildCount p := by
  rw [cube, Fintype.card_piFinset]
  have hc : ∀ i, (allowed (p i)).card = if (p i).1 = (p i).2 then 2 else 1 := by
    intro i
    by_cases hi : (p i).1 = (p i).2 <;> simp [allowed, hi]
  simp_rw [hc]
  rw [← Finset.prod_filter]
  simp [wildCount]

/-- The partial AND signatures of a pairwise-union-positive false family occupy disjoint cubes. -/
lemma false_family_kraft_bound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (S : Finset (Fin n → Bool))
    (hfalse : ∀ x ∈ S, circuitFun n C x = false)
    (hjoin : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → circuitFun n C (fun i => x i || y i) = true) :
    (∑ x ∈ S, 2 ^ wildCount (stateFn n C x)) ≤ 2 ^ andCount C.gates := by
  classical
  have hdis : (S : Set (Fin n → Bool)).PairwiseDisjoint (fun x => cube (stateFn n C x)) := by
    intro x hx y hy hne
    apply cube_disjoint_of_cross
    exact exists_and_cross n C hAO x y (hfalse x hx) (hfalse y hy) (hjoin x hx y hy hne)
  calc
    _ = ∑ x ∈ S, (cube (stateFn n C x)).card := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (cube_card _).symm
    _ = (S.biUnion fun x => cube (stateFn n C x)).card := (Finset.card_biUnion hdis).symm
    _ ≤ Fintype.card (Fin (andCount C.gates) → Bool) := Finset.card_le_univ _
    _ = _ := by simp

lemma succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    omega

/-- Linear consequence of the cube packing bound, useful as a search constraint. -/
lemma false_family_linear_bound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (S : Finset (Fin n → Bool))
    (hfalse : ∀ x ∈ S, circuitFun n C x = false)
    (hjoin : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → circuitFun n C (fun i => x i || y i) = true) :
    (∑ x ∈ S, wildCount (stateFn n C x)) ≤ 2 ^ andCount C.gates - S.card := by
  have hsum : (∑ x ∈ S, (wildCount (stateFn n C x) + 1)) ≤
      ∑ x ∈ S, 2 ^ wildCount (stateFn n C x) := by
    exact Finset.sum_le_sum fun x hx => succ_le_two_pow _
  have hk := false_family_kraft_bound n C hAO S hfalse hjoin
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  omega

end AndPacking

namespace TrueAndLoss

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.AO2Upper
open PEqualNP.Outside.L_meta_3566.FalseRestrict
open PEqualNP.Outside.L_meta_3566.OrLoss
open PEqualNP.Outside.L_meta_3566.AndSignature

/-- The AND/OR dual preserves the input wire indices. -/
def dualOp : GateOp → GateOp
  | .and => .or
  | .or => .and
  | op => op

def dualGate (g : Gate) : Gate := ⟨dualOp g.op, g.inputs⟩
def dual (C : Circuit) : Circuit := ⟨C.gates.map dualGate, C.output⟩

lemma good_of_basis_back (gs : List Gate) (m : ℕ)
    (hb : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hr : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < m + j) :
    Good m gs := by
  induction gs generalizing m with
  | nil => trivial
  | cons g gs ih =>
    refine ⟨⟨(hb g List.mem_cons_self).1, (hb g List.mem_cons_self).2, ?_⟩, ?_⟩
    · intro i hi
      simpa using hr 0 (by simp) i (by simpa using hi)
    · apply ih (m + 1) (fun a ha => hb a (List.mem_cons_of_mem g ha))
      intro j hj i hi
      have h := hr (j + 1) (by simpa using hj) i (by simpa using hi)
      omega

lemma good_of_ao2 (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) : Good n C.gates :=
  good_of_basis_back _ _ (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩) hAO.2.1

lemma good_dual (gs : List Gate) (m : ℕ) (h : Good m gs) : Good m (gs.map dualGate) := by
  induction gs generalizing m with
  | nil => trivial
  | cons g gs ih =>
    refine ⟨⟨?_, h.1.2.1, h.1.2.2⟩, ih (m + 1) h.2⟩
    rcases h.1.1 with hp | hp
    · exact Or.inr (by simp [dualGate, dualOp, hp])
    · exact Or.inl (by simp [dualGate, dualOp, hp])

lemma dual_ao2 (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) : IsAO2 n (dual C) :=
  good_ao2 _ _ _ (good_dual _ _ (good_of_ao2 n C hAO))

lemma getD_map_not (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (w.map Bool.not).getD i false = !(w.getD i false) := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma dual_gate_eval (g : Gate) (w : List Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2)
    (hb : ∀ i ∈ g.inputs, i < w.length) :
    (dualGate g).op.eval ((dualGate g).inputs.map fun i =>
      (w.map Bool.not).getD i false) = !(g.op.eval (g.inputs.map fun i => w.getD i false)) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have ha : a < w.length := hb a (by simp [hab])
  have hb' : b < w.length := hb b (by simp [hab])
  simp only [dualGate, hab, List.map_cons, List.map_nil, getD_map_not w a ha,
    getD_map_not w b hb']
  rcases hop with hp | hp <;> rw [hp] <;>
    cases w.getD a false <;> cases w.getD b false <;> rfl

lemma wiresFrom_dual (gs : List Gate) (w : List Bool) (h : Good w.length gs) :
    wiresFrom (gs.map dualGate) (w.map Bool.not) = (wiresFrom gs w).map Bool.not := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have he := dual_gate_eval g w h.1.1 h.1.2.1 h.1.2.2
    have hs : w.map Bool.not ++ [(dualGate g).op.eval
        ((dualGate g).inputs.map fun i => (w.map Bool.not).getD i false)] =
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).map Bool.not := by
      rw [he]
      simp only [List.map_append, List.map_cons, List.map_nil]
    change wiresFrom (gs.map dualGate) _ = (wiresFrom gs _).map Bool.not
    dsimp only
    rw [hs]
    apply ih
    simpa using h.2

/-- Duality is asserted only for a valid output wire; out-of-range outputs default to false. -/
lemma dual_circuitFun_neg (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length) (x : Fin n → Bool) :
    circuitFun n (dual C) (fun i => !x i) = !(circuitFun n C x) := by
  change (wiresFrom (C.gates.map dualGate) (List.ofFn fun i => !x i)).getD C.output false =
    !((wiresFrom C.gates (List.ofFn x)).getD C.output false)
  have hi : List.ofFn (fun i => !x i) = (List.ofFn x).map Bool.not := by
    rw [List.map_ofFn]
    rfl
  rw [hi, wiresFrom_dual _ _ (by simpa using good_of_ao2 n C hAO)]
  exact getD_map_not _ _ (by simpa [length_wiresFrom] using hout)

lemma dual_circuitFun (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length) (x : Fin n → Bool) :
    circuitFun n (dual C) x = !(circuitFun n C (fun i => !x i)) := by
  simpa using dual_circuitFun_neg n C hAO hout (fun i => !x i)

lemma output_lt_of_true (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hx : circuitFun n C x = true) : C.output < n + C.gates.length := by
  by_contra h
  have he : circuitFun n C x = false := by
    change (wiresFrom C.gates (List.ofFn x)).getD C.output false = false
    exact List.getD_eq_default _ _ (by simpa [length_wiresFrom] using Nat.le_of_not_gt h)
  rw [hx] at he
  contradiction

lemma output_lt_of_depends (n : ℕ) (C : Circuit) (x y : Fin n → Bool)
    (h : circuitFun n C x ≠ circuitFun n C y) : C.output < n + C.gates.length := by
  cases hx : circuitFun n C x <;> cases hy : circuitFun n C y
  · exact False.elim (h (hx.trans hy.symm))
  · exact output_lt_of_true n C y hy
  · exact output_lt_of_true n C x hx
  · exact False.elim (h (hx.trans hy.symm))

lemma andCount_dual (gs : List Gate) : andCount (gs.map dualGate) = orCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, andCount, orCount, List.countP_cons] at *
    rw [ih]
    simp only [dualGate]
    cases g with
    | mk op inputs => cases op <;> rfl

lemma orCount_dual (gs : List Gate) : orCount (gs.map dualGate) = andCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, andCount, orCount, List.countP_cons] at *
    rw [ih]
    simp only [dualGate]
    cases g with
    | mk op inputs => cases op <;> rfl

lemma neg_update_true (n : ℕ) (z : Fin n) (x : Fin n → Bool) :
    (fun i => !(Function.update x z true i)) = Function.update (fun i => !x i) z false := by
  funext i
  by_cases hi : i = z <;> simp [Function.update, hi]

lemma neg_update_false (n : ℕ) (z : Fin n) (x : Fin n → Bool) :
    (fun i => !(Function.update (fun i => !x i) z false i)) = Function.update x z true := by
  funext i
  by_cases hi : i = z <;> simp [Function.update, hi]

/-- An essential true restriction whose cofactor is not constant true saves an AND gate. -/
lemma exists_restriction_and_loss (n : ℕ) (z : Fin n) (C : Circuit)
    (hAO : IsAO2 n C)
    (hfalse : ∃ y : Fin n → Bool, circuitFun n C (Function.update y z true) = false)
    (hdepends : ∃ x : Fin n → Bool,
      circuitFun n C x ≠ circuitFun n C (Function.update x z true)) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => circuitFun n C (Function.update y z true)) ∧
      andCount D.gates + 1 ≤ andCount C.gates := by
  obtain ⟨x, hx⟩ := hdepends
  have hout := output_lt_of_depends n C x (Function.update x z true) hx
  have htrue : ∃ y : Fin n → Bool,
      circuitFun n (dual C) (Function.update y z false) = true := by
    obtain ⟨y, hy⟩ := hfalse
    refine ⟨fun i => !y i, ?_⟩
    rw [← neg_update_true, dual_circuitFun_neg n C hAO hout, hy]
    rfl
  have hdep : ∃ x : Fin n → Bool,
      circuitFun n (dual C) x ≠ circuitFun n (dual C) (Function.update x z false) := by
    refine ⟨fun i => !x i, ?_⟩
    rw [← neg_update_true, dual_circuitFun_neg n C hAO hout,
      dual_circuitFun_neg n C hAO hout]
    intro he
    exact hx (by simpa using congrArg Bool.not he)
  obtain ⟨D, hD, hfun, hcount⟩ := exists_restriction_or_loss n z (dual C)
    (dual_ao2 n C hAO) htrue hdep
  have hDout : D.output < n + D.gates.length := by
    obtain ⟨y, hy⟩ := htrue
    apply output_lt_of_true n D y
    rw [hfun]
    exact hy
  refine ⟨dual D, dual_ao2 n D hD, ?_, ?_⟩
  · funext y
    rw [dual_circuitFun n D hD hDout, hfun]
    change Bool.not (circuitFun n (dual C) (Function.update (fun i => !y i) z false)) =
      circuitFun n C (Function.update y z true)
    rw [dual_circuitFun n C hAO hout, neg_update_false]
    simp
  · simpa only [dual, andCount_dual, orCount_dual] using hcount

open PEqualNP.MetaComplexity.NestedCover

lemma reduce_and_count_le (m : ℕ) (op : GateOp) (a b : Option ℕ) :
    andCount (reduceGate m op a b).1 ≤ if isAnd op then 1 else 0 := by
  cases op <;> cases a <;> cases b <;> simp [reduceGate, andCount, isAnd]

lemma compile_and_count_le (gs : List Gate) (m : ℕ) (σ : List (Option ℕ)) :
    andCount (compile m σ gs).1 ≤ andCount gs := by
  induction gs generalizing m σ with
  | nil => simp [compile, andCount]
  | cons g gs ih =>
    have hstep := reduce_and_count_le m g.op (σ.getD (g.inputs.getD 0 0) none)
      (σ.getD (g.inputs.getD 1 0) none)
    have hrest := ih (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2])
    change andCount (emit m σ g).1 ≤ if isAnd g.op then 1 else 0 at hstep
    simp only [compile, andCount, List.countP_append, List.countP_cons]
    change andCount (emit m σ g).1 +
      andCount (compile (m + (emit m σ g).1.length) (σ ++ [(emit m σ g).2]) gs).1 ≤
      andCount gs + (if isAnd g.op then 1 else 0)
    omega

lemma restricted_and_count_le (n : ℕ) (z : Fin n) (C : Circuit) :
    andCount (restricted n z C).gates ≤ andCount C.gates :=
  compile_and_count_le C.gates n (initialMap n z)

lemma graph_true_restriction_and_loss {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (z v : Fin n) (hzv : G.Adj z v)
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => graphFun G ∅ (Function.update y z true)) ∧
      andCount D.gates + 1 ≤ andCount C.gates := by
  classical
  have hfalse : ∃ y : Fin n → Bool, circuitFun n C (Function.update y z true) = false := by
    refine ⟨fun _ => false, ?_⟩
    rw [hfun]
    have he : Function.update (fun _ : Fin n => false) z true = fun i => decide (i = z) := by
      funext i
      by_cases hi : i = z <;> simp [hi]
    rw [he]
    simp [graphFun]
  have hdep : ∃ x : Fin n → Bool,
      circuitFun n C x ≠ circuitFun n C (Function.update x z true) := by
    let x : Fin n → Bool := fun i => decide (i = v)
    have hbefore : graphFun G ∅ x = false := by simp [x, graphFun]
    have hafter : graphFun G ∅ (Function.update x z true) = true := by
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false,
        decide_false, Bool.false_or, decide_eq_true_eq]
      exact ⟨z, v, hzv, by simp, by simp [x, hzv.ne.symm]⟩
    refine ⟨x, ?_⟩
    rw [hfun, hbefore, hafter]
    decide
  obtain ⟨D, hD, hf, hc⟩ := exists_restriction_and_loss n z C hAO hfalse hdep
  exact ⟨D, hD, by simpa only [hfun] using hf, hc⟩

lemma graph_leaf_true_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z v : Fin n) (hzv : G.Adj z v) (hsole : ∀ w, G.Adj z w → w = v) :
    (fun y : Fin n → Bool => graphFun G ∅ (Function.update (Function.update y v false) z true)) =
      graphFun (G.deleteEdges (G.incidenceSet v)) ∅ := by
  classical
  funext y
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false,
    decide_false, Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have hav : a ≠ v := by intro he; subst a; simp [hzv.ne.symm] at ha
    have hbv : b ≠ v := by intro he; subst b; simp [hzv.ne.symm] at hb
    have haz : a ≠ z := by intro he; subst a; exact hbv (hsole b hab)
    have hbz : b ≠ z := by intro he; subst b; exact hav (hsole a hab.symm)
    exact ⟨a, b, (PEqualNP.Outside.L_meta_3566.cut_adj G v a b).mpr ⟨hab, hav, hbv⟩,
      by simpa [haz, hav] using ha, by simpa [hbz, hbv] using hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hab, hav, hbv⟩ := (PEqualNP.Outside.L_meta_3566.cut_adj G v a b).mp hab
    have haz : a ≠ z := by intro he; subst a; exact hbv (hsole b hab)
    have hbz : b ≠ z := by intro he; subst b; exact hav (hsole a hab.symm)
    exact ⟨a, b, hab, by simpa [haz, hav] using ha, by simpa [hbz, hbv] using hb⟩

/-- Delete all edges incident to the neighbour of a leaf, saving at least one AND. -/
lemma graph_leaf_and_loss {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z v : Fin n) (hleaf : G.degree z = 1) (hzv : G.Adj z v)
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = graphFun (G.deleteEdges (G.incidenceSet v)) ∅ ∧
      andCount D.gates + 1 ≤ andCount C.gates := by
  classical
  obtain ⟨D, hD, hfunD, hcountD⟩ := graph_true_restriction_and_loss G z v hzv C hAO hfun
  obtain ⟨hE, hfunE, _⟩ := restricted_spec n v D hD
  have hc := restricted_and_count_le n v D
  refine ⟨restricted n v D, hE, ?_, by omega⟩
  rw [hfunD] at hfunE
  have hsole : ∀ w, G.Adj z w → w = v := by
    obtain ⟨u, hu, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hleaf
    intro w hw
    exact (huniq w hw).trans (huniq v hzv).symm
  exact hfunE.trans (graph_leaf_true_false G z v hzv hsole)

/-- Every minimum vertex cover is a lower bound for the number of AND gates. -/
def AndLower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ →
    ∀ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) →
      (∀ U : Finset (Fin n), G.IsVertexCover (U : Set (Fin n)) → T.card ≤ U.card) →
        T.card ≤ andCount C.gates

lemma leaf_step {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z v : Fin n) (hleaf : G.degree z = 1) (hzv : G.Adj z v)
    (hcut : AndLower (G.deleteEdges (G.incidenceSet v))) : AndLower G := by
  classical
  intro C hAO hfun T hT hTmin
  obtain ⟨D, hD, hf, hc⟩ := graph_leaf_and_loss G z v hleaf hzv C hAO hfun
  obtain ⟨S, hS, hSmin⟩ := PEqualNP.Outside.L_meta_3566.exists_min_cover
    (G.deleteEdges (G.incidenceSet v))
  have hbound := hcut D hD hf S hS hSmin
  have hcover := (PEqualNP.Outside.L_meta_3566.cut_cover_bounds G v T S hT hTmin hS hSmin).2
  omega

lemma and_lower_edgeless {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hzero : G.edgeFinset.card = 0) : AndLower G := by
  intro C hAO hfun T hT hTmin
  have hempty : G.IsVertexCover (∅ : Set (Fin n)) := by
    intro a b hab
    have he : s(a, b) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hab
    have hz := Finset.card_eq_zero.mp hzero
    simp [hz] at he
  have hTzero := hTmin ∅ (by simpa using hempty)
  simp only [Finset.card_empty] at hTzero
  omega

/-- It suffices to prove the AND lower bound for subgraphs with no degree-one vertices. -/
lemma of_leaf_free_subgraphs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcore : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      H ≤ G → (∀ z, H.degree z ≠ 1) → AndLower H) : AndLower G := by
  classical
  have hall : ∀ m : ℕ, ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      H.edgeFinset.card = m → H ≤ G → AndLower H := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro H hdec hcard hHG
      by_cases hfree : ∀ z, H.degree z ≠ 1
      · exact hcore H hHG hfree
      · push Not at hfree
        obtain ⟨z, hz⟩ := hfree
        obtain ⟨v, hv, _⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hz
        apply leaf_step H z v hz hv
        have hcount := PEqualNP.Outside.L_meta_3566.cut_edge_count H v
        have hpos := hv.degree_pos_right
        exact ih (H.deleteEdges (H.incidenceSet v)).edgeFinset.card (by omega)
          (H.deleteEdges (H.incidenceSet v)) rfl ((H.deleteEdges_le _).trans hHG)
  exact hall _ G rfl le_rfl

lemma forest_and_lower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic) : AndLower G := by
  apply of_leaf_free_subgraphs G
  intro H hdec hHG hfree
  apply and_lower_edgeless H
  by_contra hzero
  obtain ⟨z, hz⟩ := LeafOr.acyclic_has_leaf H (hacyclic.anti hHG) (by omega)
  exact hfree z hz

end TrueAndLoss

namespace OrPacking

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3566.TrueAndLoss
open PEqualNP.Outside.L_meta_3566.AndPacking
open PEqualNP.Outside.L_meta_3566.AndSignature
open PEqualNP.Outside.L_meta_3566.OrLoss

def negInput {n : ℕ} (x : Fin n → Bool) : Fin n → Bool := fun i => !x i

lemma negInput_injective {n : ℕ} : Function.Injective (@negInput n) := by
  intro x y h
  funext i
  have hi := congrFun h i
  simpa [negInput] using congrArg Bool.not hi

lemma negInput_meet {n : ℕ} (x y : Fin n → Bool) :
    (fun i => negInput x i || negInput y i) = negInput (fun i => x i && y i) := by
  funext i
  simp only [negInput]
  cases x i <;> cases y i <;> rfl

/-- Count equal-operand OR gates through the AND trace of the dual circuit.
For an AO2 circuit, `wiresFrom_dual` complements each corresponding wire value;
`dualOp` selects exactly the original OR gates, and complementing both operands
preserves whether they are equal. No output-wire validity assumption is needed
for that gate-trace interpretation. -/
def orWildCount (n : ℕ) (C : Circuit) (x : Fin n → Bool) : ℕ :=
  wildCount (stateFn n (dual C) (negInput x))

lemma dual_false_family (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length) (S : Finset (Fin n → Bool))
    (htrue : ∀ x ∈ S, circuitFun n C x = true)
    (hmeet : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → circuitFun n C (fun i => x i && y i) = false) :
    (∀ x ∈ S.image negInput, circuitFun n (dual C) x = false) ∧
      (∀ x ∈ S.image negInput, ∀ y ∈ S.image negInput, x ≠ y →
        circuitFun n (dual C) (fun i => x i || y i) = true) := by
  constructor
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    rw [show negInput a = (fun i => !a i) from rfl,
      dual_circuitFun_neg n C hAO hout, htrue a ha]
    rfl
  · intro x hx y hy hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := by intro he; subst b; exact hne rfl
    rw [negInput_meet, show negInput (fun i => a i && b i) =
      (fun i => !(a i && b i)) from rfl,
      dual_circuitFun_neg n C hAO hout, hmeet a ha b hb hab]
    rfl

/-- A true family with pairwise false meets has disjoint partial OR signatures. -/
lemma true_family_kraft_bound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (S : Finset (Fin n → Bool))
    (htrue : ∀ x ∈ S, circuitFun n C x = true)
    (hmeet : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → circuitFun n C (fun i => x i && y i) = false) :
    (∑ x ∈ S, 2 ^ orWildCount n C x) ≤ 2 ^ orCount C.gates := by
  classical
  by_cases hzero : S = ∅
  · simp [hzero]
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hzero
  have hout := output_lt_of_true n C x (htrue x hx)
  obtain ⟨hf, hj⟩ := dual_false_family n C hAO hout S htrue hmeet
  have hk := false_family_kraft_bound n (dual C) (dual_ao2 n C hAO) (S.image negInput) hf hj
  rw [Finset.sum_image (fun a _ b _ he => negInput_injective he)] at hk
  simpa only [orWildCount, dual, andCount_dual] using hk

lemma true_family_linear_bound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (S : Finset (Fin n → Bool))
    (htrue : ∀ x ∈ S, circuitFun n C x = true)
    (hmeet : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → circuitFun n C (fun i => x i && y i) = false) :
    (∑ x ∈ S, orWildCount n C x) ≤ 2 ^ orCount C.gates - S.card := by
  classical
  by_cases hzero : S = ∅
  · simp [hzero]
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hzero
  have hout := output_lt_of_true n C x (htrue x hx)
  obtain ⟨hf, hj⟩ := dual_false_family n C hAO hout S htrue hmeet
  have hk := false_family_linear_bound n (dual C) (dual_ao2 n C hAO) (S.image negInput) hf hj
  rw [Finset.sum_image (fun a _ b _ he => negInput_injective he),
    Finset.card_image_of_injective S negInput_injective] at hk
  simpa only [orWildCount, dual, andCount_dual] using hk

end OrPacking

end PEqualNP.Outside.L_meta_3566
