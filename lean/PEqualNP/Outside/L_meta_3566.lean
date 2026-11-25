import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

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

lemma cover_lower_of_matching {n k : ℕ} (G : SimpleGraph (Fin n))
    (ends : Fin k × Bool → Fin n) (hinj : Function.Injective ends)
    (hadj : ∀ i : Fin k, G.Adj (ends (i, false)) (ends (i, true)))
    (T : Finset (Fin n)) (hT : IsVertexCover G T) : k ≤ T.card := by
  classical
  let side : Fin k → Bool := fun i => if ends (i, false) ∈ T then false else true
  let pick : Fin k → Fin n := fun i => ends (i, side i)
  have hmem : ∀ i, pick i ∈ T := by
    intro i
    have h := hT _ _ (hadj i)
    dsimp [pick, side]
    split_ifs with hf
    · exact hf
    · exact h.resolve_left hf
  have hpick : Function.Injective pick := by
    intro i j heq
    exact congrArg Prod.fst (hinj heq)
  have hsub : Finset.univ.image pick ⊆ T := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i
  have hcard := Finset.card_le_card hsub
  simpa [Finset.card_image_of_injective _ hpick] using hcard

namespace BoundaryBudget

lemma weighted_union_bound {α : Type*} [DecidableEq α]
    (support : ℕ → Finset α) (cost : ℕ → ℕ) (m : ℕ)
    (step : ∀ w < m, ∃ atoms : Finset α, ∃ parents : Finset ℕ,
      parents ⊆ Finset.range w ∧
      support w ⊆ atoms ∪ parents.biUnion support ∧
      atoms.card + parents.card ≤ 1 + cost w)
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ∑ w ∈ Finset.range m, cost w := by
  classical
  induction m generalizing roots with
  | zero =>
      have hroots : roots = ∅ := by simpa using hr
      simp [hroots]
  | succ m ih =>
      have old := ih (fun w hw => step w (by omega))
      have hpre : roots.erase m ⊆ Finset.range m := by
        intro w hw
        have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
        have hlt := Finset.mem_range.mp (hr hmem)
        exact Finset.mem_range.mpr (by omega)
      rw [Finset.sum_range_succ]
      by_cases hm : m ∈ roots
      · obtain ⟨atoms, parents, hparents, hsupport, hbudget⟩ := step m (by omega)
        have hrootcard := Finset.card_erase_add_one hm
        have hnext := old ((roots.erase m) ∪ parents)
          (Finset.union_subset hpre hparents)
        have hsub : roots.biUnion support ⊆
            atoms ∪ (((roots.erase m) ∪ parents).biUnion support) := by
          intro x hx
          obtain ⟨w, hw, hxs⟩ := Finset.mem_biUnion.mp hx
          by_cases heq : w = m
          · subst w
            rcases Finset.mem_union.mp (hsupport hxs) with ha | hp
            · exact Finset.mem_union_left _ ha
            · obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hp
              exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
                ⟨p, Finset.mem_union_right _ hp, hxp⟩)
          · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), hxs⟩)
        have hcard := Finset.card_le_card hsub
        have hatoms := Finset.card_union_le atoms (((roots.erase m) ∪ parents).biUnion support)
        have hparentcard := Finset.card_union_le (roots.erase m) parents
        omega
      · rw [Finset.erase_eq_of_notMem hm] at hpre
        have hnext := old roots hpre
        omega

lemma boundary_union_bound {α : Type*} [DecidableEq α]
    (support : ℕ → Finset α) (boundary paid roots : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, w ∉ boundary → 1 < (support w).card →
      ∃ parents : Finset ℕ, parents ⊆ Finset.range w ∧
        support w ⊆ parents.biUnion support ∧
        parents.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card +
      ∑ w ∈ Finset.range m,
        ((if w ∈ paid then 1 else 0) +
          (if w ∈ boundary then (support w).card - 1 else 0)) := by
  classical
  apply weighted_union_bound support _ m ?_ roots hr
  intro w hw
  by_cases hb : w ∈ boundary
  · refine ⟨support w, ∅, by simp, by simp, ?_⟩
    simp only [Finset.card_empty, Nat.add_zero, hb, ite_true]
    omega
  · by_cases hs : 1 < (support w).card
    · obtain ⟨parents, hparents, hsupport, hbudget⟩ := step w hw hb hs
      refine ⟨∅, parents, hparents, by simpa using hsupport, ?_⟩
      simpa [hb] using hbudget
    · refine ⟨support w, ∅, by simp, by simp, ?_⟩
      simp only [Finset.card_empty, Nat.add_zero, hb, ite_false]
      omega

end BoundaryBudget

end PEqualNP.Outside.L_meta_3566
