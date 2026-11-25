import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
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

namespace WireTable

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_table (gs : List Gate) (w : List Bool) (t : ℕ → Bool)
    (hw : ∀ i < w.length, w.getD i false = t i)
    (hback : ∀ j g, gs[j]? = some g → ∀ i ∈ g.inputs, i < w.length + j)
    (hgate : ∀ j g, gs[j]? = some g → g.op.eval (g.inputs.map t) = t (w.length + j)) :
    ∀ i < w.length + gs.length, (wiresFrom gs w).getD i false = t i := by
  induction gs generalizing w with
  | nil => simpa [wiresFrom] using hw
  | cons g gs ih =>
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false) = t w.length := by
      calc
        _ = g.op.eval (g.inputs.map t) := by
          congr 1
          apply List.map_congr_left
          intro i hi
          apply hw
          have h := hback 0 g rfl i hi
          simpa using h
        _ = t w.length := by simpa using hgate 0 g rfl
    have hw' : ∀ i < (w ++ [t w.length]).length,
        (w ++ [t w.length]).getD i false = t i := by
      intro i hi
      by_cases hlt : i < w.length
      · rw [List.getD_append _ _ _ _ hlt]
        exact hw i hlt
      · have heq : i = w.length := by simp only [List.length_append, List.length_singleton] at hi; omega
        subst i
        simp
    have hb' : ∀ j q, gs[j]? = some q →
        ∀ i ∈ q.inputs, i < (w ++ [t w.length]).length + j := by
      intro j q hq i hi
      have h := hback (j + 1) q (by simpa using hq) i hi
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have hg' : ∀ j q, gs[j]? = some q →
        q.op.eval (q.inputs.map t) = t ((w ++ [t w.length]).length + j) := by
      intro j q hq
      have h := hgate (j + 1) q (by simpa using hq)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    intro i hi
    change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])).getD i false = t i
    rw [hv]
    apply ih (w ++ [t w.length]) hw' hb' hg' i
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

lemma circuit_eval_of_table {n : ℕ} (C : Circuit) (x : Fin n → Bool) (t : ℕ → Bool)
    (hinput : ∀ i : Fin n, t i.val = x i)
    (hback : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j)
    (hgate : ∀ j g, C.gates[j]? = some g → g.op.eval (g.inputs.map t) = t (n + j))
    (hout : C.output < n + C.gates.length) :
    PEqualNP.MetaComplexity.circuitFun n C x = t C.output := by
  have hw : ∀ i < (List.ofFn x).length, (List.ofFn x).getD i false = t i := by
    intro i hi
    have hin : i < n := by simpa using hi
    simpa [hin] using (hinput ⟨i, hin⟩).symm
  have h := wiresFrom_table C.gates (List.ofFn x) t hw
    (by simpa using hback) (by simpa using hgate) C.output (by simpa using hout)
  exact h

end WireTable


namespace GF8Representation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
def gates : List Gate := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [128, 2]⟩,
    ⟨GateOp.or, [129, 3]⟩,
    ⟨GateOp.or, [130, 4]⟩,
    ⟨GateOp.or, [131, 5]⟩,
    ⟨GateOp.or, [132, 6]⟩,
    ⟨GateOp.or, [133, 7]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [135, 10]⟩,
    ⟨GateOp.or, [136, 11]⟩,
    ⟨GateOp.or, [137, 12]⟩,
    ⟨GateOp.or, [138, 13]⟩,
    ⟨GateOp.or, [139, 14]⟩,
    ⟨GateOp.or, [140, 15]⟩,
    ⟨GateOp.or, [16, 17]⟩,
    ⟨GateOp.or, [142, 18]⟩,
    ⟨GateOp.or, [143, 19]⟩,
    ⟨GateOp.or, [144, 20]⟩,
    ⟨GateOp.or, [145, 21]⟩,
    ⟨GateOp.or, [146, 22]⟩,
    ⟨GateOp.or, [147, 23]⟩,
    ⟨GateOp.or, [24, 25]⟩,
    ⟨GateOp.or, [149, 26]⟩,
    ⟨GateOp.or, [150, 27]⟩,
    ⟨GateOp.or, [151, 28]⟩,
    ⟨GateOp.or, [152, 29]⟩,
    ⟨GateOp.or, [153, 30]⟩,
    ⟨GateOp.or, [154, 31]⟩,
    ⟨GateOp.or, [32, 33]⟩,
    ⟨GateOp.or, [156, 34]⟩,
    ⟨GateOp.or, [157, 35]⟩,
    ⟨GateOp.or, [158, 36]⟩,
    ⟨GateOp.or, [159, 37]⟩,
    ⟨GateOp.or, [160, 38]⟩,
    ⟨GateOp.or, [161, 39]⟩,
    ⟨GateOp.or, [40, 41]⟩,
    ⟨GateOp.or, [163, 42]⟩,
    ⟨GateOp.or, [164, 43]⟩,
    ⟨GateOp.or, [165, 44]⟩,
    ⟨GateOp.or, [166, 45]⟩,
    ⟨GateOp.or, [167, 46]⟩,
    ⟨GateOp.or, [168, 47]⟩,
    ⟨GateOp.or, [48, 49]⟩,
    ⟨GateOp.or, [170, 50]⟩,
    ⟨GateOp.or, [171, 51]⟩,
    ⟨GateOp.or, [172, 52]⟩,
    ⟨GateOp.or, [173, 53]⟩,
    ⟨GateOp.or, [174, 54]⟩,
    ⟨GateOp.or, [175, 55]⟩,
    ⟨GateOp.or, [56, 57]⟩,
    ⟨GateOp.or, [177, 58]⟩,
    ⟨GateOp.or, [178, 59]⟩,
    ⟨GateOp.or, [179, 60]⟩,
    ⟨GateOp.or, [180, 61]⟩,
    ⟨GateOp.or, [181, 62]⟩,
    ⟨GateOp.or, [182, 63]⟩,
    ⟨GateOp.or, [0, 8]⟩,
    ⟨GateOp.or, [184, 16]⟩,
    ⟨GateOp.or, [185, 24]⟩,
    ⟨GateOp.or, [186, 32]⟩,
    ⟨GateOp.or, [187, 40]⟩,
    ⟨GateOp.or, [188, 48]⟩,
    ⟨GateOp.or, [189, 56]⟩,
    ⟨GateOp.or, [1, 9]⟩,
    ⟨GateOp.or, [191, 17]⟩,
    ⟨GateOp.or, [192, 25]⟩,
    ⟨GateOp.or, [193, 33]⟩,
    ⟨GateOp.or, [194, 41]⟩,
    ⟨GateOp.or, [195, 49]⟩,
    ⟨GateOp.or, [196, 57]⟩,
    ⟨GateOp.or, [2, 10]⟩,
    ⟨GateOp.or, [198, 18]⟩,
    ⟨GateOp.or, [199, 26]⟩,
    ⟨GateOp.or, [200, 34]⟩,
    ⟨GateOp.or, [201, 42]⟩,
    ⟨GateOp.or, [202, 50]⟩,
    ⟨GateOp.or, [203, 58]⟩,
    ⟨GateOp.or, [3, 11]⟩,
    ⟨GateOp.or, [205, 19]⟩,
    ⟨GateOp.or, [206, 27]⟩,
    ⟨GateOp.or, [207, 35]⟩,
    ⟨GateOp.or, [208, 43]⟩,
    ⟨GateOp.or, [209, 51]⟩,
    ⟨GateOp.or, [210, 59]⟩,
    ⟨GateOp.or, [4, 12]⟩,
    ⟨GateOp.or, [212, 20]⟩,
    ⟨GateOp.or, [213, 28]⟩,
    ⟨GateOp.or, [214, 36]⟩,
    ⟨GateOp.or, [215, 44]⟩,
    ⟨GateOp.or, [216, 52]⟩,
    ⟨GateOp.or, [217, 60]⟩,
    ⟨GateOp.or, [5, 13]⟩,
    ⟨GateOp.or, [219, 21]⟩,
    ⟨GateOp.or, [220, 29]⟩,
    ⟨GateOp.or, [221, 37]⟩,
    ⟨GateOp.or, [222, 45]⟩,
    ⟨GateOp.or, [223, 53]⟩,
    ⟨GateOp.or, [224, 61]⟩,
    ⟨GateOp.or, [6, 14]⟩,
    ⟨GateOp.or, [226, 22]⟩,
    ⟨GateOp.or, [227, 30]⟩,
    ⟨GateOp.or, [228, 38]⟩,
    ⟨GateOp.or, [229, 46]⟩,
    ⟨GateOp.or, [230, 54]⟩,
    ⟨GateOp.or, [231, 62]⟩,
    ⟨GateOp.or, [7, 15]⟩,
    ⟨GateOp.or, [233, 23]⟩,
    ⟨GateOp.or, [234, 31]⟩,
    ⟨GateOp.or, [235, 39]⟩,
    ⟨GateOp.or, [236, 47]⟩,
    ⟨GateOp.or, [237, 55]⟩,
    ⟨GateOp.or, [238, 63]⟩,
    ⟨GateOp.or, [64, 65]⟩,
    ⟨GateOp.or, [240, 66]⟩,
    ⟨GateOp.or, [241, 67]⟩,
    ⟨GateOp.or, [242, 68]⟩,
    ⟨GateOp.or, [243, 69]⟩,
    ⟨GateOp.or, [244, 70]⟩,
    ⟨GateOp.or, [245, 71]⟩,
    ⟨GateOp.or, [72, 73]⟩,
    ⟨GateOp.or, [247, 74]⟩,
    ⟨GateOp.or, [248, 75]⟩,
    ⟨GateOp.or, [249, 76]⟩,
    ⟨GateOp.or, [250, 77]⟩,
    ⟨GateOp.or, [251, 78]⟩,
    ⟨GateOp.or, [252, 79]⟩,
    ⟨GateOp.or, [80, 81]⟩,
    ⟨GateOp.or, [254, 82]⟩,
    ⟨GateOp.or, [255, 83]⟩,
    ⟨GateOp.or, [256, 84]⟩,
    ⟨GateOp.or, [257, 85]⟩,
    ⟨GateOp.or, [258, 86]⟩,
    ⟨GateOp.or, [259, 87]⟩,
    ⟨GateOp.or, [88, 89]⟩,
    ⟨GateOp.or, [261, 90]⟩,
    ⟨GateOp.or, [262, 91]⟩,
    ⟨GateOp.or, [263, 92]⟩,
    ⟨GateOp.or, [264, 93]⟩,
    ⟨GateOp.or, [265, 94]⟩,
    ⟨GateOp.or, [266, 95]⟩,
    ⟨GateOp.or, [96, 97]⟩,
    ⟨GateOp.or, [268, 98]⟩,
    ⟨GateOp.or, [269, 99]⟩,
    ⟨GateOp.or, [270, 100]⟩,
    ⟨GateOp.or, [271, 101]⟩,
    ⟨GateOp.or, [272, 102]⟩,
    ⟨GateOp.or, [273, 103]⟩,
    ⟨GateOp.or, [104, 105]⟩,
    ⟨GateOp.or, [275, 106]⟩,
    ⟨GateOp.or, [276, 107]⟩,
    ⟨GateOp.or, [277, 108]⟩,
    ⟨GateOp.or, [278, 109]⟩,
    ⟨GateOp.or, [279, 110]⟩,
    ⟨GateOp.or, [280, 111]⟩,
    ⟨GateOp.or, [112, 113]⟩,
    ⟨GateOp.or, [282, 114]⟩,
    ⟨GateOp.or, [283, 115]⟩,
    ⟨GateOp.or, [284, 116]⟩,
    ⟨GateOp.or, [285, 117]⟩,
    ⟨GateOp.or, [286, 118]⟩,
    ⟨GateOp.or, [287, 119]⟩,
    ⟨GateOp.or, [120, 121]⟩,
    ⟨GateOp.or, [289, 122]⟩,
    ⟨GateOp.or, [290, 123]⟩,
    ⟨GateOp.or, [291, 124]⟩,
    ⟨GateOp.or, [292, 125]⟩,
    ⟨GateOp.or, [293, 126]⟩,
    ⟨GateOp.or, [294, 127]⟩,
    ⟨GateOp.or, [64, 72]⟩,
    ⟨GateOp.or, [296, 80]⟩,
    ⟨GateOp.or, [297, 88]⟩,
    ⟨GateOp.or, [298, 96]⟩,
    ⟨GateOp.or, [299, 104]⟩,
    ⟨GateOp.or, [300, 112]⟩,
    ⟨GateOp.or, [301, 120]⟩,
    ⟨GateOp.or, [65, 73]⟩,
    ⟨GateOp.or, [303, 81]⟩,
    ⟨GateOp.or, [304, 89]⟩,
    ⟨GateOp.or, [305, 97]⟩,
    ⟨GateOp.or, [306, 105]⟩,
    ⟨GateOp.or, [307, 113]⟩,
    ⟨GateOp.or, [308, 121]⟩,
    ⟨GateOp.or, [66, 74]⟩,
    ⟨GateOp.or, [310, 82]⟩,
    ⟨GateOp.or, [311, 90]⟩,
    ⟨GateOp.or, [312, 98]⟩,
    ⟨GateOp.or, [313, 106]⟩,
    ⟨GateOp.or, [314, 114]⟩,
    ⟨GateOp.or, [315, 122]⟩,
    ⟨GateOp.or, [67, 75]⟩,
    ⟨GateOp.or, [317, 83]⟩,
    ⟨GateOp.or, [318, 91]⟩,
    ⟨GateOp.or, [319, 99]⟩,
    ⟨GateOp.or, [320, 107]⟩,
    ⟨GateOp.or, [321, 115]⟩,
    ⟨GateOp.or, [322, 123]⟩,
    ⟨GateOp.or, [68, 76]⟩,
    ⟨GateOp.or, [324, 84]⟩,
    ⟨GateOp.or, [325, 92]⟩,
    ⟨GateOp.or, [326, 100]⟩,
    ⟨GateOp.or, [327, 108]⟩,
    ⟨GateOp.or, [328, 116]⟩,
    ⟨GateOp.or, [329, 124]⟩,
    ⟨GateOp.or, [69, 77]⟩,
    ⟨GateOp.or, [331, 85]⟩,
    ⟨GateOp.or, [332, 93]⟩,
    ⟨GateOp.or, [333, 101]⟩,
    ⟨GateOp.or, [334, 109]⟩,
    ⟨GateOp.or, [335, 117]⟩,
    ⟨GateOp.or, [336, 125]⟩,
    ⟨GateOp.or, [70, 78]⟩,
    ⟨GateOp.or, [338, 86]⟩,
    ⟨GateOp.or, [339, 94]⟩,
    ⟨GateOp.or, [340, 102]⟩,
    ⟨GateOp.or, [341, 110]⟩,
    ⟨GateOp.or, [342, 118]⟩,
    ⟨GateOp.or, [343, 126]⟩,
    ⟨GateOp.or, [71, 79]⟩,
    ⟨GateOp.or, [345, 87]⟩,
    ⟨GateOp.or, [346, 95]⟩,
    ⟨GateOp.or, [347, 103]⟩,
    ⟨GateOp.or, [348, 111]⟩,
    ⟨GateOp.or, [349, 119]⟩,
    ⟨GateOp.or, [350, 127]⟩,
    ⟨GateOp.or, [134, 148]⟩,
    ⟨GateOp.or, [352, 162]⟩,
    ⟨GateOp.or, [353, 176]⟩,
    ⟨GateOp.or, [141, 155]⟩,
    ⟨GateOp.or, [355, 169]⟩,
    ⟨GateOp.or, [356, 183]⟩,
    ⟨GateOp.or, [134, 141]⟩,
    ⟨GateOp.or, [358, 162]⟩,
    ⟨GateOp.or, [359, 169]⟩,
    ⟨GateOp.or, [148, 155]⟩,
    ⟨GateOp.or, [361, 176]⟩,
    ⟨GateOp.or, [362, 183]⟩,
    ⟨GateOp.or, [134, 141]⟩,
    ⟨GateOp.or, [364, 148]⟩,
    ⟨GateOp.or, [365, 155]⟩,
    ⟨GateOp.or, [162, 169]⟩,
    ⟨GateOp.or, [367, 176]⟩,
    ⟨GateOp.or, [368, 183]⟩,
    ⟨GateOp.or, [190, 204]⟩,
    ⟨GateOp.or, [370, 218]⟩,
    ⟨GateOp.or, [371, 232]⟩,
    ⟨GateOp.or, [197, 211]⟩,
    ⟨GateOp.or, [373, 225]⟩,
    ⟨GateOp.or, [374, 239]⟩,
    ⟨GateOp.or, [190, 197]⟩,
    ⟨GateOp.or, [376, 218]⟩,
    ⟨GateOp.or, [377, 225]⟩,
    ⟨GateOp.or, [204, 211]⟩,
    ⟨GateOp.or, [379, 232]⟩,
    ⟨GateOp.or, [380, 239]⟩,
    ⟨GateOp.or, [190, 197]⟩,
    ⟨GateOp.or, [382, 204]⟩,
    ⟨GateOp.or, [383, 211]⟩,
    ⟨GateOp.or, [218, 225]⟩,
    ⟨GateOp.or, [385, 232]⟩,
    ⟨GateOp.or, [386, 239]⟩,
    ⟨GateOp.or, [246, 260]⟩,
    ⟨GateOp.or, [388, 274]⟩,
    ⟨GateOp.or, [389, 288]⟩,
    ⟨GateOp.or, [253, 267]⟩,
    ⟨GateOp.or, [391, 281]⟩,
    ⟨GateOp.or, [392, 295]⟩,
    ⟨GateOp.or, [246, 253]⟩,
    ⟨GateOp.or, [394, 274]⟩,
    ⟨GateOp.or, [395, 281]⟩,
    ⟨GateOp.or, [260, 267]⟩,
    ⟨GateOp.or, [397, 288]⟩,
    ⟨GateOp.or, [398, 295]⟩,
    ⟨GateOp.or, [246, 253]⟩,
    ⟨GateOp.or, [400, 260]⟩,
    ⟨GateOp.or, [401, 267]⟩,
    ⟨GateOp.or, [274, 281]⟩,
    ⟨GateOp.or, [403, 288]⟩,
    ⟨GateOp.or, [404, 295]⟩,
    ⟨GateOp.or, [302, 316]⟩,
    ⟨GateOp.or, [406, 330]⟩,
    ⟨GateOp.or, [407, 344]⟩,
    ⟨GateOp.or, [309, 323]⟩,
    ⟨GateOp.or, [409, 337]⟩,
    ⟨GateOp.or, [410, 351]⟩,
    ⟨GateOp.or, [302, 309]⟩,
    ⟨GateOp.or, [412, 330]⟩,
    ⟨GateOp.or, [413, 337]⟩,
    ⟨GateOp.or, [316, 323]⟩,
    ⟨GateOp.or, [415, 344]⟩,
    ⟨GateOp.or, [416, 351]⟩,
    ⟨GateOp.or, [302, 309]⟩,
    ⟨GateOp.or, [418, 316]⟩,
    ⟨GateOp.or, [419, 323]⟩,
    ⟨GateOp.or, [330, 337]⟩,
    ⟨GateOp.or, [421, 344]⟩,
    ⟨GateOp.or, [422, 351]⟩,
    ⟨GateOp.or, [390, 354]⟩,
    ⟨GateOp.and, [393, 357]⟩,
    ⟨GateOp.or, [390, 360]⟩,
    ⟨GateOp.and, [393, 363]⟩,
    ⟨GateOp.or, [390, 366]⟩,
    ⟨GateOp.and, [393, 369]⟩,
    ⟨GateOp.or, [396, 354]⟩,
    ⟨GateOp.and, [399, 357]⟩,
    ⟨GateOp.or, [396, 360]⟩,
    ⟨GateOp.and, [399, 363]⟩,
    ⟨GateOp.or, [396, 366]⟩,
    ⟨GateOp.and, [399, 369]⟩,
    ⟨GateOp.or, [402, 354]⟩,
    ⟨GateOp.and, [405, 357]⟩,
    ⟨GateOp.or, [402, 360]⟩,
    ⟨GateOp.and, [405, 363]⟩,
    ⟨GateOp.or, [402, 366]⟩,
    ⟨GateOp.and, [405, 369]⟩,
    ⟨GateOp.and, [426, 430]⟩,
    ⟨GateOp.and, [427, 431]⟩,
    ⟨GateOp.or, [442, 443]⟩,
    ⟨GateOp.and, [426, 431]⟩,
    ⟨GateOp.and, [427, 430]⟩,
    ⟨GateOp.or, [445, 446]⟩,
    ⟨GateOp.and, [428, 432]⟩,
    ⟨GateOp.and, [429, 433]⟩,
    ⟨GateOp.or, [448, 449]⟩,
    ⟨GateOp.and, [428, 433]⟩,
    ⟨GateOp.and, [429, 432]⟩,
    ⟨GateOp.or, [451, 452]⟩,
    ⟨GateOp.and, [450, 436]⟩,
    ⟨GateOp.and, [453, 437]⟩,
    ⟨GateOp.or, [454, 455]⟩,
    ⟨GateOp.and, [450, 437]⟩,
    ⟨GateOp.and, [453, 436]⟩,
    ⟨GateOp.or, [457, 458]⟩,
    ⟨GateOp.and, [434, 438]⟩,
    ⟨GateOp.and, [435, 439]⟩,
    ⟨GateOp.or, [460, 461]⟩,
    ⟨GateOp.and, [434, 439]⟩,
    ⟨GateOp.and, [435, 438]⟩,
    ⟨GateOp.or, [463, 464]⟩,
    ⟨GateOp.and, [424, 462]⟩,
    ⟨GateOp.and, [425, 465]⟩,
    ⟨GateOp.or, [466, 467]⟩,
    ⟨GateOp.and, [424, 465]⟩,
    ⟨GateOp.and, [425, 462]⟩,
    ⟨GateOp.or, [469, 470]⟩,
    ⟨GateOp.and, [444, 462]⟩,
    ⟨GateOp.and, [447, 465]⟩,
    ⟨GateOp.or, [472, 473]⟩,
    ⟨GateOp.and, [444, 465]⟩,
    ⟨GateOp.and, [447, 462]⟩,
    ⟨GateOp.or, [475, 476]⟩,
    ⟨GateOp.and, [474, 440]⟩,
    ⟨GateOp.and, [477, 441]⟩,
    ⟨GateOp.or, [478, 479]⟩,
    ⟨GateOp.and, [474, 441]⟩,
    ⟨GateOp.and, [477, 440]⟩,
    ⟨GateOp.or, [481, 482]⟩,
    ⟨GateOp.and, [456, 440]⟩,
    ⟨GateOp.and, [459, 441]⟩,
    ⟨GateOp.or, [484, 485]⟩,
    ⟨GateOp.and, [456, 441]⟩,
    ⟨GateOp.and, [459, 440]⟩,
    ⟨GateOp.or, [487, 488]⟩,
    ⟨GateOp.and, [468, 408]⟩,
    ⟨GateOp.and, [471, 411]⟩,
    ⟨GateOp.or, [490, 491]⟩,
    ⟨GateOp.and, [468, 411]⟩,
    ⟨GateOp.and, [471, 408]⟩,
    ⟨GateOp.or, [493, 494]⟩,
    ⟨GateOp.and, [480, 414]⟩,
    ⟨GateOp.and, [483, 417]⟩,
    ⟨GateOp.or, [496, 497]⟩,
    ⟨GateOp.and, [480, 417]⟩,
    ⟨GateOp.and, [483, 414]⟩,
    ⟨GateOp.or, [499, 500]⟩,
    ⟨GateOp.and, [486, 420]⟩,
    ⟨GateOp.and, [489, 423]⟩,
    ⟨GateOp.or, [502, 503]⟩,
    ⟨GateOp.and, [486, 423]⟩,
    ⟨GateOp.and, [489, 420]⟩,
    ⟨GateOp.or, [505, 506]⟩,
    ⟨GateOp.and, [492, 372]⟩,
    ⟨GateOp.and, [495, 375]⟩,
    ⟨GateOp.or, [508, 509]⟩,
    ⟨GateOp.and, [498, 378]⟩,
    ⟨GateOp.and, [501, 381]⟩,
    ⟨GateOp.or, [511, 512]⟩,
    ⟨GateOp.and, [504, 384]⟩,
    ⟨GateOp.and, [507, 387]⟩,
    ⟨GateOp.or, [514, 515]⟩,
    ⟨GateOp.and, [510, 513]⟩,
    ⟨GateOp.and, [517, 516]⟩,
    ⟨GateOp.or, [354, 357]⟩,
    ⟨GateOp.or, [390, 393]⟩,
    ⟨GateOp.and, [519, 520]⟩,
    ⟨GateOp.and, [521, 518]⟩]

def circuit : Circuit := ⟨gates, 522⟩

def w128 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨0, by decide⟩), (x ⟨1, by decide⟩)]

def w129 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w128 x, (x ⟨2, by decide⟩)]

def w130 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w129 x, (x ⟨3, by decide⟩)]

def w131 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w130 x, (x ⟨4, by decide⟩)]

def w132 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w131 x, (x ⟨5, by decide⟩)]

def w133 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w132 x, (x ⟨6, by decide⟩)]

def w134 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w133 x, (x ⟨7, by decide⟩)]

def w135 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨8, by decide⟩), (x ⟨9, by decide⟩)]

def w136 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w135 x, (x ⟨10, by decide⟩)]

def w137 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w136 x, (x ⟨11, by decide⟩)]

def w138 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w137 x, (x ⟨12, by decide⟩)]

def w139 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w138 x, (x ⟨13, by decide⟩)]

def w140 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w139 x, (x ⟨14, by decide⟩)]

def w141 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w140 x, (x ⟨15, by decide⟩)]

def w142 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨16, by decide⟩), (x ⟨17, by decide⟩)]

def w143 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w142 x, (x ⟨18, by decide⟩)]

def w144 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w143 x, (x ⟨19, by decide⟩)]

def w145 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w144 x, (x ⟨20, by decide⟩)]

def w146 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w145 x, (x ⟨21, by decide⟩)]

def w147 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w146 x, (x ⟨22, by decide⟩)]

def w148 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w147 x, (x ⟨23, by decide⟩)]

def w149 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨24, by decide⟩), (x ⟨25, by decide⟩)]

def w150 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w149 x, (x ⟨26, by decide⟩)]

def w151 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w150 x, (x ⟨27, by decide⟩)]

def w152 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w151 x, (x ⟨28, by decide⟩)]

def w153 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w152 x, (x ⟨29, by decide⟩)]

def w154 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w153 x, (x ⟨30, by decide⟩)]

def w155 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w154 x, (x ⟨31, by decide⟩)]

def w156 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨32, by decide⟩), (x ⟨33, by decide⟩)]

def w157 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w156 x, (x ⟨34, by decide⟩)]

def w158 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w157 x, (x ⟨35, by decide⟩)]

def w159 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w158 x, (x ⟨36, by decide⟩)]

def w160 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w159 x, (x ⟨37, by decide⟩)]

def w161 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w160 x, (x ⟨38, by decide⟩)]

def w162 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w161 x, (x ⟨39, by decide⟩)]

def w163 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨40, by decide⟩), (x ⟨41, by decide⟩)]

def w164 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w163 x, (x ⟨42, by decide⟩)]

def w165 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w164 x, (x ⟨43, by decide⟩)]

def w166 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w165 x, (x ⟨44, by decide⟩)]

def w167 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w166 x, (x ⟨45, by decide⟩)]

def w168 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w167 x, (x ⟨46, by decide⟩)]

def w169 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w168 x, (x ⟨47, by decide⟩)]

def w170 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨48, by decide⟩), (x ⟨49, by decide⟩)]

def w171 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w170 x, (x ⟨50, by decide⟩)]

def w172 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w171 x, (x ⟨51, by decide⟩)]

def w173 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w172 x, (x ⟨52, by decide⟩)]

def w174 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w173 x, (x ⟨53, by decide⟩)]

def w175 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w174 x, (x ⟨54, by decide⟩)]

def w176 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w175 x, (x ⟨55, by decide⟩)]

def w177 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨56, by decide⟩), (x ⟨57, by decide⟩)]

def w178 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w177 x, (x ⟨58, by decide⟩)]

def w179 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w178 x, (x ⟨59, by decide⟩)]

def w180 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w179 x, (x ⟨60, by decide⟩)]

def w181 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w180 x, (x ⟨61, by decide⟩)]

def w182 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w181 x, (x ⟨62, by decide⟩)]

def w183 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w182 x, (x ⟨63, by decide⟩)]

def w184 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨0, by decide⟩), (x ⟨8, by decide⟩)]

def w185 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w184 x, (x ⟨16, by decide⟩)]

def w186 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w185 x, (x ⟨24, by decide⟩)]

def w187 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w186 x, (x ⟨32, by decide⟩)]

def w188 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w187 x, (x ⟨40, by decide⟩)]

def w189 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w188 x, (x ⟨48, by decide⟩)]

def w190 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w189 x, (x ⟨56, by decide⟩)]

def w191 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨1, by decide⟩), (x ⟨9, by decide⟩)]

def w192 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w191 x, (x ⟨17, by decide⟩)]

def w193 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w192 x, (x ⟨25, by decide⟩)]

def w194 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w193 x, (x ⟨33, by decide⟩)]

def w195 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w194 x, (x ⟨41, by decide⟩)]

def w196 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w195 x, (x ⟨49, by decide⟩)]

def w197 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w196 x, (x ⟨57, by decide⟩)]

def w198 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨2, by decide⟩), (x ⟨10, by decide⟩)]

def w199 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w198 x, (x ⟨18, by decide⟩)]

def w200 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w199 x, (x ⟨26, by decide⟩)]

def w201 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w200 x, (x ⟨34, by decide⟩)]

def w202 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w201 x, (x ⟨42, by decide⟩)]

def w203 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w202 x, (x ⟨50, by decide⟩)]

def w204 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w203 x, (x ⟨58, by decide⟩)]

def w205 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨3, by decide⟩), (x ⟨11, by decide⟩)]

def w206 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w205 x, (x ⟨19, by decide⟩)]

def w207 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w206 x, (x ⟨27, by decide⟩)]

def w208 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w207 x, (x ⟨35, by decide⟩)]

def w209 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w208 x, (x ⟨43, by decide⟩)]

def w210 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w209 x, (x ⟨51, by decide⟩)]

def w211 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w210 x, (x ⟨59, by decide⟩)]

def w212 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨4, by decide⟩), (x ⟨12, by decide⟩)]

def w213 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w212 x, (x ⟨20, by decide⟩)]

def w214 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w213 x, (x ⟨28, by decide⟩)]

def w215 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w214 x, (x ⟨36, by decide⟩)]

def w216 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w215 x, (x ⟨44, by decide⟩)]

def w217 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w216 x, (x ⟨52, by decide⟩)]

def w218 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w217 x, (x ⟨60, by decide⟩)]

def w219 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨5, by decide⟩), (x ⟨13, by decide⟩)]

def w220 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w219 x, (x ⟨21, by decide⟩)]

def w221 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w220 x, (x ⟨29, by decide⟩)]

def w222 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w221 x, (x ⟨37, by decide⟩)]

def w223 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w222 x, (x ⟨45, by decide⟩)]

def w224 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w223 x, (x ⟨53, by decide⟩)]

def w225 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w224 x, (x ⟨61, by decide⟩)]

def w226 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨6, by decide⟩), (x ⟨14, by decide⟩)]

def w227 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w226 x, (x ⟨22, by decide⟩)]

def w228 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w227 x, (x ⟨30, by decide⟩)]

def w229 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w228 x, (x ⟨38, by decide⟩)]

def w230 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w229 x, (x ⟨46, by decide⟩)]

def w231 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w230 x, (x ⟨54, by decide⟩)]

def w232 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w231 x, (x ⟨62, by decide⟩)]

def w233 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨7, by decide⟩), (x ⟨15, by decide⟩)]

def w234 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w233 x, (x ⟨23, by decide⟩)]

def w235 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w234 x, (x ⟨31, by decide⟩)]

def w236 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w235 x, (x ⟨39, by decide⟩)]

def w237 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w236 x, (x ⟨47, by decide⟩)]

def w238 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w237 x, (x ⟨55, by decide⟩)]

def w239 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w238 x, (x ⟨63, by decide⟩)]

def w240 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨64, by decide⟩), (x ⟨65, by decide⟩)]

def w241 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w240 x, (x ⟨66, by decide⟩)]

def w242 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w241 x, (x ⟨67, by decide⟩)]

def w243 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w242 x, (x ⟨68, by decide⟩)]

def w244 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w243 x, (x ⟨69, by decide⟩)]

def w245 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w244 x, (x ⟨70, by decide⟩)]

def w246 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w245 x, (x ⟨71, by decide⟩)]

def w247 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨72, by decide⟩), (x ⟨73, by decide⟩)]

def w248 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w247 x, (x ⟨74, by decide⟩)]

def w249 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w248 x, (x ⟨75, by decide⟩)]

def w250 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w249 x, (x ⟨76, by decide⟩)]

def w251 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w250 x, (x ⟨77, by decide⟩)]

def w252 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w251 x, (x ⟨78, by decide⟩)]

def w253 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w252 x, (x ⟨79, by decide⟩)]

def w254 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨80, by decide⟩), (x ⟨81, by decide⟩)]

def w255 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w254 x, (x ⟨82, by decide⟩)]

def w256 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w255 x, (x ⟨83, by decide⟩)]

def w257 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w256 x, (x ⟨84, by decide⟩)]

def w258 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w257 x, (x ⟨85, by decide⟩)]

def w259 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w258 x, (x ⟨86, by decide⟩)]

def w260 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w259 x, (x ⟨87, by decide⟩)]

def w261 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨88, by decide⟩), (x ⟨89, by decide⟩)]

def w262 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w261 x, (x ⟨90, by decide⟩)]

def w263 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w262 x, (x ⟨91, by decide⟩)]

def w264 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w263 x, (x ⟨92, by decide⟩)]

def w265 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w264 x, (x ⟨93, by decide⟩)]

def w266 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w265 x, (x ⟨94, by decide⟩)]

def w267 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w266 x, (x ⟨95, by decide⟩)]

def w268 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨96, by decide⟩), (x ⟨97, by decide⟩)]

def w269 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w268 x, (x ⟨98, by decide⟩)]

def w270 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w269 x, (x ⟨99, by decide⟩)]

def w271 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w270 x, (x ⟨100, by decide⟩)]

def w272 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w271 x, (x ⟨101, by decide⟩)]

def w273 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w272 x, (x ⟨102, by decide⟩)]

def w274 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w273 x, (x ⟨103, by decide⟩)]

def w275 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨104, by decide⟩), (x ⟨105, by decide⟩)]

def w276 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w275 x, (x ⟨106, by decide⟩)]

def w277 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w276 x, (x ⟨107, by decide⟩)]

def w278 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w277 x, (x ⟨108, by decide⟩)]

def w279 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w278 x, (x ⟨109, by decide⟩)]

def w280 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w279 x, (x ⟨110, by decide⟩)]

def w281 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w280 x, (x ⟨111, by decide⟩)]

def w282 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨112, by decide⟩), (x ⟨113, by decide⟩)]

def w283 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w282 x, (x ⟨114, by decide⟩)]

def w284 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w283 x, (x ⟨115, by decide⟩)]

def w285 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w284 x, (x ⟨116, by decide⟩)]

def w286 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w285 x, (x ⟨117, by decide⟩)]

def w287 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w286 x, (x ⟨118, by decide⟩)]

def w288 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w287 x, (x ⟨119, by decide⟩)]

def w289 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨120, by decide⟩), (x ⟨121, by decide⟩)]

def w290 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w289 x, (x ⟨122, by decide⟩)]

def w291 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w290 x, (x ⟨123, by decide⟩)]

def w292 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w291 x, (x ⟨124, by decide⟩)]

def w293 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w292 x, (x ⟨125, by decide⟩)]

def w294 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w293 x, (x ⟨126, by decide⟩)]

def w295 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w294 x, (x ⟨127, by decide⟩)]

def w296 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨64, by decide⟩), (x ⟨72, by decide⟩)]

def w297 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w296 x, (x ⟨80, by decide⟩)]

def w298 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w297 x, (x ⟨88, by decide⟩)]

def w299 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w298 x, (x ⟨96, by decide⟩)]

def w300 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w299 x, (x ⟨104, by decide⟩)]

def w301 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w300 x, (x ⟨112, by decide⟩)]

def w302 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w301 x, (x ⟨120, by decide⟩)]

def w303 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨65, by decide⟩), (x ⟨73, by decide⟩)]

def w304 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w303 x, (x ⟨81, by decide⟩)]

def w305 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w304 x, (x ⟨89, by decide⟩)]

def w306 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w305 x, (x ⟨97, by decide⟩)]

def w307 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w306 x, (x ⟨105, by decide⟩)]

def w308 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w307 x, (x ⟨113, by decide⟩)]

def w309 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w308 x, (x ⟨121, by decide⟩)]

def w310 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨66, by decide⟩), (x ⟨74, by decide⟩)]

def w311 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w310 x, (x ⟨82, by decide⟩)]

def w312 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w311 x, (x ⟨90, by decide⟩)]

def w313 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w312 x, (x ⟨98, by decide⟩)]

def w314 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w313 x, (x ⟨106, by decide⟩)]

def w315 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w314 x, (x ⟨114, by decide⟩)]

def w316 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w315 x, (x ⟨122, by decide⟩)]

def w317 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨67, by decide⟩), (x ⟨75, by decide⟩)]

def w318 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w317 x, (x ⟨83, by decide⟩)]

def w319 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w318 x, (x ⟨91, by decide⟩)]

def w320 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w319 x, (x ⟨99, by decide⟩)]

def w321 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w320 x, (x ⟨107, by decide⟩)]

def w322 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w321 x, (x ⟨115, by decide⟩)]

def w323 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w322 x, (x ⟨123, by decide⟩)]

def w324 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨68, by decide⟩), (x ⟨76, by decide⟩)]

def w325 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w324 x, (x ⟨84, by decide⟩)]

def w326 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w325 x, (x ⟨92, by decide⟩)]

def w327 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w326 x, (x ⟨100, by decide⟩)]

def w328 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w327 x, (x ⟨108, by decide⟩)]

def w329 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w328 x, (x ⟨116, by decide⟩)]

def w330 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w329 x, (x ⟨124, by decide⟩)]

def w331 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨69, by decide⟩), (x ⟨77, by decide⟩)]

def w332 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w331 x, (x ⟨85, by decide⟩)]

def w333 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w332 x, (x ⟨93, by decide⟩)]

def w334 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w333 x, (x ⟨101, by decide⟩)]

def w335 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w334 x, (x ⟨109, by decide⟩)]

def w336 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w335 x, (x ⟨117, by decide⟩)]

def w337 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w336 x, (x ⟨125, by decide⟩)]

def w338 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨70, by decide⟩), (x ⟨78, by decide⟩)]

def w339 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w338 x, (x ⟨86, by decide⟩)]

def w340 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w339 x, (x ⟨94, by decide⟩)]

def w341 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w340 x, (x ⟨102, by decide⟩)]

def w342 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w341 x, (x ⟨110, by decide⟩)]

def w343 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w342 x, (x ⟨118, by decide⟩)]

def w344 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w343 x, (x ⟨126, by decide⟩)]

def w345 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [(x ⟨71, by decide⟩), (x ⟨79, by decide⟩)]

def w346 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w345 x, (x ⟨87, by decide⟩)]

def w347 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w346 x, (x ⟨95, by decide⟩)]

def w348 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w347 x, (x ⟨103, by decide⟩)]

def w349 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w348 x, (x ⟨111, by decide⟩)]

def w350 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w349 x, (x ⟨119, by decide⟩)]

def w351 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w350 x, (x ⟨127, by decide⟩)]

def w352 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w134 x, w148 x]

def w353 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w352 x, w162 x]

def w354 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w353 x, w176 x]

def w355 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w141 x, w155 x]

def w356 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w355 x, w169 x]

def w357 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w356 x, w183 x]

def w358 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w134 x, w141 x]

def w359 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w358 x, w162 x]

def w360 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w359 x, w169 x]

def w361 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w148 x, w155 x]

def w362 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w361 x, w176 x]

def w363 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w362 x, w183 x]

def w364 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w134 x, w141 x]

def w365 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w364 x, w148 x]

def w366 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w365 x, w155 x]

def w367 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w162 x, w169 x]

def w368 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w367 x, w176 x]

def w369 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w368 x, w183 x]

def w370 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w190 x, w204 x]

def w371 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w370 x, w218 x]

def w372 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w371 x, w232 x]

def w373 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w197 x, w211 x]

def w374 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w373 x, w225 x]

def w375 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w374 x, w239 x]

def w376 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w190 x, w197 x]

def w377 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w376 x, w218 x]

def w378 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w377 x, w225 x]

def w379 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w204 x, w211 x]

def w380 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w379 x, w232 x]

def w381 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w380 x, w239 x]

def w382 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w190 x, w197 x]

def w383 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w382 x, w204 x]

def w384 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w383 x, w211 x]

def w385 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w218 x, w225 x]

def w386 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w385 x, w232 x]

def w387 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w386 x, w239 x]

def w388 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w246 x, w260 x]

def w389 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w388 x, w274 x]

def w390 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w389 x, w288 x]

def w391 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w253 x, w267 x]

def w392 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w391 x, w281 x]

def w393 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w392 x, w295 x]

def w394 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w246 x, w253 x]

def w395 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w394 x, w274 x]

def w396 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w395 x, w281 x]

def w397 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w260 x, w267 x]

def w398 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w397 x, w288 x]

def w399 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w398 x, w295 x]

def w400 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w246 x, w253 x]

def w401 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w400 x, w260 x]

def w402 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w401 x, w267 x]

def w403 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w274 x, w281 x]

def w404 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w403 x, w288 x]

def w405 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w404 x, w295 x]

def w406 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w302 x, w316 x]

def w407 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w406 x, w330 x]

def w408 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w407 x, w344 x]

def w409 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w309 x, w323 x]

def w410 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w409 x, w337 x]

def w411 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w410 x, w351 x]

def w412 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w302 x, w309 x]

def w413 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w412 x, w330 x]

def w414 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w413 x, w337 x]

def w415 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w316 x, w323 x]

def w416 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w415 x, w344 x]

def w417 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w416 x, w351 x]

def w418 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w302 x, w309 x]

def w419 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w418 x, w316 x]

def w420 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w419 x, w323 x]

def w421 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w330 x, w337 x]

def w422 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w421 x, w344 x]

def w423 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w422 x, w351 x]

def w424 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w390 x, w354 x]

def w425 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w393 x, w357 x]

def w426 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w390 x, w360 x]

def w427 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w393 x, w363 x]

def w428 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w390 x, w366 x]

def w429 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w393 x, w369 x]

def w430 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w396 x, w354 x]

def w431 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w399 x, w357 x]

def w432 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w396 x, w360 x]

def w433 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w399 x, w363 x]

def w434 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w396 x, w366 x]

def w435 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w399 x, w369 x]

def w436 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w402 x, w354 x]

def w437 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w405 x, w357 x]

def w438 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w402 x, w360 x]

def w439 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w405 x, w363 x]

def w440 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w402 x, w366 x]

def w441 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w405 x, w369 x]

def w442 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w426 x, w430 x]

def w443 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w427 x, w431 x]

def w444 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w442 x, w443 x]

def w445 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w426 x, w431 x]

def w446 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w427 x, w430 x]

def w447 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w445 x, w446 x]

def w448 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w428 x, w432 x]

def w449 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w429 x, w433 x]

def w450 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w448 x, w449 x]

def w451 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w428 x, w433 x]

def w452 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w429 x, w432 x]

def w453 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w451 x, w452 x]

def w454 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w450 x, w436 x]

def w455 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w453 x, w437 x]

def w456 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w454 x, w455 x]

def w457 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w450 x, w437 x]

def w458 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w453 x, w436 x]

def w459 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w457 x, w458 x]

def w460 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w434 x, w438 x]

def w461 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w435 x, w439 x]

def w462 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w460 x, w461 x]

def w463 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w434 x, w439 x]

def w464 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w435 x, w438 x]

def w465 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w463 x, w464 x]

def w466 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w424 x, w462 x]

def w467 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w425 x, w465 x]

def w468 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w466 x, w467 x]

def w469 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w424 x, w465 x]

def w470 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w425 x, w462 x]

def w471 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w469 x, w470 x]

def w472 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w444 x, w462 x]

def w473 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w447 x, w465 x]

def w474 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w472 x, w473 x]

def w475 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w444 x, w465 x]

def w476 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w447 x, w462 x]

def w477 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w475 x, w476 x]

def w478 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w474 x, w440 x]

def w479 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w477 x, w441 x]

def w480 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w478 x, w479 x]

def w481 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w474 x, w441 x]

def w482 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w477 x, w440 x]

def w483 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w481 x, w482 x]

def w484 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w456 x, w440 x]

def w485 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w459 x, w441 x]

def w486 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w484 x, w485 x]

def w487 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w456 x, w441 x]

def w488 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w459 x, w440 x]

def w489 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w487 x, w488 x]

def w490 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w468 x, w408 x]

def w491 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w471 x, w411 x]

def w492 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w490 x, w491 x]

def w493 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w468 x, w411 x]

def w494 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w471 x, w408 x]

def w495 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w493 x, w494 x]

def w496 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w480 x, w414 x]

def w497 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w483 x, w417 x]

def w498 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w496 x, w497 x]

def w499 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w480 x, w417 x]

def w500 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w483 x, w414 x]

def w501 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w499 x, w500 x]

def w502 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w486 x, w420 x]

def w503 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w489 x, w423 x]

def w504 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w502 x, w503 x]

def w505 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w486 x, w423 x]

def w506 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w489 x, w420 x]

def w507 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w505 x, w506 x]

def w508 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w492 x, w372 x]

def w509 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w495 x, w375 x]

def w510 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w508 x, w509 x]

def w511 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w498 x, w378 x]

def w512 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w501 x, w381 x]

def w513 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w511 x, w512 x]

def w514 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w504 x, w384 x]

def w515 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w507 x, w387 x]

def w516 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w514 x, w515 x]

def w517 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w510 x, w513 x]

def w518 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w517 x, w516 x]

def w519 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w354 x, w357 x]

def w520 (x : Fin 128 → Bool) : Bool :=
  GateOp.or.eval [w390 x, w393 x]

def w521 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w519 x, w520 x]

def w522 (x : Fin 128 → Bool) : Bool :=
  GateOp.and.eval [w521 x, w518 x]

set_option maxRecDepth 20000 in
def table (x : Fin 128 → Bool) (i : ℕ) : Bool :=
  if h : i < 128 then x ⟨i, h⟩ else
  if i < 523 then
    if i < 325 then
      if i < 226 then
        if i < 177 then
          if i < 152 then
            if i < 140 then
              if i < 134 then
                if i < 131 then
                  if i < 129 then
                    w128 x
                  else
                    if i < 130 then
                      w129 x
                    else
                      w130 x
                else
                  if i < 132 then
                    w131 x
                  else
                    if i < 133 then
                      w132 x
                    else
                      w133 x
              else
                if i < 137 then
                  if i < 135 then
                    w134 x
                  else
                    if i < 136 then
                      w135 x
                    else
                      w136 x
                else
                  if i < 138 then
                    w137 x
                  else
                    if i < 139 then
                      w138 x
                    else
                      w139 x
            else
              if i < 146 then
                if i < 143 then
                  if i < 141 then
                    w140 x
                  else
                    if i < 142 then
                      w141 x
                    else
                      w142 x
                else
                  if i < 144 then
                    w143 x
                  else
                    if i < 145 then
                      w144 x
                    else
                      w145 x
              else
                if i < 149 then
                  if i < 147 then
                    w146 x
                  else
                    if i < 148 then
                      w147 x
                    else
                      w148 x
                else
                  if i < 150 then
                    w149 x
                  else
                    if i < 151 then
                      w150 x
                    else
                      w151 x
          else
            if i < 164 then
              if i < 158 then
                if i < 155 then
                  if i < 153 then
                    w152 x
                  else
                    if i < 154 then
                      w153 x
                    else
                      w154 x
                else
                  if i < 156 then
                    w155 x
                  else
                    if i < 157 then
                      w156 x
                    else
                      w157 x
              else
                if i < 161 then
                  if i < 159 then
                    w158 x
                  else
                    if i < 160 then
                      w159 x
                    else
                      w160 x
                else
                  if i < 162 then
                    w161 x
                  else
                    if i < 163 then
                      w162 x
                    else
                      w163 x
            else
              if i < 170 then
                if i < 167 then
                  if i < 165 then
                    w164 x
                  else
                    if i < 166 then
                      w165 x
                    else
                      w166 x
                else
                  if i < 168 then
                    w167 x
                  else
                    if i < 169 then
                      w168 x
                    else
                      w169 x
              else
                if i < 173 then
                  if i < 171 then
                    w170 x
                  else
                    if i < 172 then
                      w171 x
                    else
                      w172 x
                else
                  if i < 175 then
                    if i < 174 then
                      w173 x
                    else
                      w174 x
                  else
                    if i < 176 then
                      w175 x
                    else
                      w176 x
        else
          if i < 201 then
            if i < 189 then
              if i < 183 then
                if i < 180 then
                  if i < 178 then
                    w177 x
                  else
                    if i < 179 then
                      w178 x
                    else
                      w179 x
                else
                  if i < 181 then
                    w180 x
                  else
                    if i < 182 then
                      w181 x
                    else
                      w182 x
              else
                if i < 186 then
                  if i < 184 then
                    w183 x
                  else
                    if i < 185 then
                      w184 x
                    else
                      w185 x
                else
                  if i < 187 then
                    w186 x
                  else
                    if i < 188 then
                      w187 x
                    else
                      w188 x
            else
              if i < 195 then
                if i < 192 then
                  if i < 190 then
                    w189 x
                  else
                    if i < 191 then
                      w190 x
                    else
                      w191 x
                else
                  if i < 193 then
                    w192 x
                  else
                    if i < 194 then
                      w193 x
                    else
                      w194 x
              else
                if i < 198 then
                  if i < 196 then
                    w195 x
                  else
                    if i < 197 then
                      w196 x
                    else
                      w197 x
                else
                  if i < 199 then
                    w198 x
                  else
                    if i < 200 then
                      w199 x
                    else
                      w200 x
          else
            if i < 213 then
              if i < 207 then
                if i < 204 then
                  if i < 202 then
                    w201 x
                  else
                    if i < 203 then
                      w202 x
                    else
                      w203 x
                else
                  if i < 205 then
                    w204 x
                  else
                    if i < 206 then
                      w205 x
                    else
                      w206 x
              else
                if i < 210 then
                  if i < 208 then
                    w207 x
                  else
                    if i < 209 then
                      w208 x
                    else
                      w209 x
                else
                  if i < 211 then
                    w210 x
                  else
                    if i < 212 then
                      w211 x
                    else
                      w212 x
            else
              if i < 219 then
                if i < 216 then
                  if i < 214 then
                    w213 x
                  else
                    if i < 215 then
                      w214 x
                    else
                      w215 x
                else
                  if i < 217 then
                    w216 x
                  else
                    if i < 218 then
                      w217 x
                    else
                      w218 x
              else
                if i < 222 then
                  if i < 220 then
                    w219 x
                  else
                    if i < 221 then
                      w220 x
                    else
                      w221 x
                else
                  if i < 224 then
                    if i < 223 then
                      w222 x
                    else
                      w223 x
                  else
                    if i < 225 then
                      w224 x
                    else
                      w225 x
      else
        if i < 275 then
          if i < 250 then
            if i < 238 then
              if i < 232 then
                if i < 229 then
                  if i < 227 then
                    w226 x
                  else
                    if i < 228 then
                      w227 x
                    else
                      w228 x
                else
                  if i < 230 then
                    w229 x
                  else
                    if i < 231 then
                      w230 x
                    else
                      w231 x
              else
                if i < 235 then
                  if i < 233 then
                    w232 x
                  else
                    if i < 234 then
                      w233 x
                    else
                      w234 x
                else
                  if i < 236 then
                    w235 x
                  else
                    if i < 237 then
                      w236 x
                    else
                      w237 x
            else
              if i < 244 then
                if i < 241 then
                  if i < 239 then
                    w238 x
                  else
                    if i < 240 then
                      w239 x
                    else
                      w240 x
                else
                  if i < 242 then
                    w241 x
                  else
                    if i < 243 then
                      w242 x
                    else
                      w243 x
              else
                if i < 247 then
                  if i < 245 then
                    w244 x
                  else
                    if i < 246 then
                      w245 x
                    else
                      w246 x
                else
                  if i < 248 then
                    w247 x
                  else
                    if i < 249 then
                      w248 x
                    else
                      w249 x
          else
            if i < 262 then
              if i < 256 then
                if i < 253 then
                  if i < 251 then
                    w250 x
                  else
                    if i < 252 then
                      w251 x
                    else
                      w252 x
                else
                  if i < 254 then
                    w253 x
                  else
                    if i < 255 then
                      w254 x
                    else
                      w255 x
              else
                if i < 259 then
                  if i < 257 then
                    w256 x
                  else
                    if i < 258 then
                      w257 x
                    else
                      w258 x
                else
                  if i < 260 then
                    w259 x
                  else
                    if i < 261 then
                      w260 x
                    else
                      w261 x
            else
              if i < 268 then
                if i < 265 then
                  if i < 263 then
                    w262 x
                  else
                    if i < 264 then
                      w263 x
                    else
                      w264 x
                else
                  if i < 266 then
                    w265 x
                  else
                    if i < 267 then
                      w266 x
                    else
                      w267 x
              else
                if i < 271 then
                  if i < 269 then
                    w268 x
                  else
                    if i < 270 then
                      w269 x
                    else
                      w270 x
                else
                  if i < 273 then
                    if i < 272 then
                      w271 x
                    else
                      w272 x
                  else
                    if i < 274 then
                      w273 x
                    else
                      w274 x
        else
          if i < 300 then
            if i < 287 then
              if i < 281 then
                if i < 278 then
                  if i < 276 then
                    w275 x
                  else
                    if i < 277 then
                      w276 x
                    else
                      w277 x
                else
                  if i < 279 then
                    w278 x
                  else
                    if i < 280 then
                      w279 x
                    else
                      w280 x
              else
                if i < 284 then
                  if i < 282 then
                    w281 x
                  else
                    if i < 283 then
                      w282 x
                    else
                      w283 x
                else
                  if i < 285 then
                    w284 x
                  else
                    if i < 286 then
                      w285 x
                    else
                      w286 x
            else
              if i < 293 then
                if i < 290 then
                  if i < 288 then
                    w287 x
                  else
                    if i < 289 then
                      w288 x
                    else
                      w289 x
                else
                  if i < 291 then
                    w290 x
                  else
                    if i < 292 then
                      w291 x
                    else
                      w292 x
              else
                if i < 296 then
                  if i < 294 then
                    w293 x
                  else
                    if i < 295 then
                      w294 x
                    else
                      w295 x
                else
                  if i < 298 then
                    if i < 297 then
                      w296 x
                    else
                      w297 x
                  else
                    if i < 299 then
                      w298 x
                    else
                      w299 x
          else
            if i < 312 then
              if i < 306 then
                if i < 303 then
                  if i < 301 then
                    w300 x
                  else
                    if i < 302 then
                      w301 x
                    else
                      w302 x
                else
                  if i < 304 then
                    w303 x
                  else
                    if i < 305 then
                      w304 x
                    else
                      w305 x
              else
                if i < 309 then
                  if i < 307 then
                    w306 x
                  else
                    if i < 308 then
                      w307 x
                    else
                      w308 x
                else
                  if i < 310 then
                    w309 x
                  else
                    if i < 311 then
                      w310 x
                    else
                      w311 x
            else
              if i < 318 then
                if i < 315 then
                  if i < 313 then
                    w312 x
                  else
                    if i < 314 then
                      w313 x
                    else
                      w314 x
                else
                  if i < 316 then
                    w315 x
                  else
                    if i < 317 then
                      w316 x
                    else
                      w317 x
              else
                if i < 321 then
                  if i < 319 then
                    w318 x
                  else
                    if i < 320 then
                      w319 x
                    else
                      w320 x
                else
                  if i < 323 then
                    if i < 322 then
                      w321 x
                    else
                      w322 x
                  else
                    if i < 324 then
                      w323 x
                    else
                      w324 x
    else
      if i < 424 then
        if i < 374 then
          if i < 349 then
            if i < 337 then
              if i < 331 then
                if i < 328 then
                  if i < 326 then
                    w325 x
                  else
                    if i < 327 then
                      w326 x
                    else
                      w327 x
                else
                  if i < 329 then
                    w328 x
                  else
                    if i < 330 then
                      w329 x
                    else
                      w330 x
              else
                if i < 334 then
                  if i < 332 then
                    w331 x
                  else
                    if i < 333 then
                      w332 x
                    else
                      w333 x
                else
                  if i < 335 then
                    w334 x
                  else
                    if i < 336 then
                      w335 x
                    else
                      w336 x
            else
              if i < 343 then
                if i < 340 then
                  if i < 338 then
                    w337 x
                  else
                    if i < 339 then
                      w338 x
                    else
                      w339 x
                else
                  if i < 341 then
                    w340 x
                  else
                    if i < 342 then
                      w341 x
                    else
                      w342 x
              else
                if i < 346 then
                  if i < 344 then
                    w343 x
                  else
                    if i < 345 then
                      w344 x
                    else
                      w345 x
                else
                  if i < 347 then
                    w346 x
                  else
                    if i < 348 then
                      w347 x
                    else
                      w348 x
          else
            if i < 361 then
              if i < 355 then
                if i < 352 then
                  if i < 350 then
                    w349 x
                  else
                    if i < 351 then
                      w350 x
                    else
                      w351 x
                else
                  if i < 353 then
                    w352 x
                  else
                    if i < 354 then
                      w353 x
                    else
                      w354 x
              else
                if i < 358 then
                  if i < 356 then
                    w355 x
                  else
                    if i < 357 then
                      w356 x
                    else
                      w357 x
                else
                  if i < 359 then
                    w358 x
                  else
                    if i < 360 then
                      w359 x
                    else
                      w360 x
            else
              if i < 367 then
                if i < 364 then
                  if i < 362 then
                    w361 x
                  else
                    if i < 363 then
                      w362 x
                    else
                      w363 x
                else
                  if i < 365 then
                    w364 x
                  else
                    if i < 366 then
                      w365 x
                    else
                      w366 x
              else
                if i < 370 then
                  if i < 368 then
                    w367 x
                  else
                    if i < 369 then
                      w368 x
                    else
                      w369 x
                else
                  if i < 372 then
                    if i < 371 then
                      w370 x
                    else
                      w371 x
                  else
                    if i < 373 then
                      w372 x
                    else
                      w373 x
        else
          if i < 399 then
            if i < 386 then
              if i < 380 then
                if i < 377 then
                  if i < 375 then
                    w374 x
                  else
                    if i < 376 then
                      w375 x
                    else
                      w376 x
                else
                  if i < 378 then
                    w377 x
                  else
                    if i < 379 then
                      w378 x
                    else
                      w379 x
              else
                if i < 383 then
                  if i < 381 then
                    w380 x
                  else
                    if i < 382 then
                      w381 x
                    else
                      w382 x
                else
                  if i < 384 then
                    w383 x
                  else
                    if i < 385 then
                      w384 x
                    else
                      w385 x
            else
              if i < 392 then
                if i < 389 then
                  if i < 387 then
                    w386 x
                  else
                    if i < 388 then
                      w387 x
                    else
                      w388 x
                else
                  if i < 390 then
                    w389 x
                  else
                    if i < 391 then
                      w390 x
                    else
                      w391 x
              else
                if i < 395 then
                  if i < 393 then
                    w392 x
                  else
                    if i < 394 then
                      w393 x
                    else
                      w394 x
                else
                  if i < 397 then
                    if i < 396 then
                      w395 x
                    else
                      w396 x
                  else
                    if i < 398 then
                      w397 x
                    else
                      w398 x
          else
            if i < 411 then
              if i < 405 then
                if i < 402 then
                  if i < 400 then
                    w399 x
                  else
                    if i < 401 then
                      w400 x
                    else
                      w401 x
                else
                  if i < 403 then
                    w402 x
                  else
                    if i < 404 then
                      w403 x
                    else
                      w404 x
              else
                if i < 408 then
                  if i < 406 then
                    w405 x
                  else
                    if i < 407 then
                      w406 x
                    else
                      w407 x
                else
                  if i < 409 then
                    w408 x
                  else
                    if i < 410 then
                      w409 x
                    else
                      w410 x
            else
              if i < 417 then
                if i < 414 then
                  if i < 412 then
                    w411 x
                  else
                    if i < 413 then
                      w412 x
                    else
                      w413 x
                else
                  if i < 415 then
                    w414 x
                  else
                    if i < 416 then
                      w415 x
                    else
                      w416 x
              else
                if i < 420 then
                  if i < 418 then
                    w417 x
                  else
                    if i < 419 then
                      w418 x
                    else
                      w419 x
                else
                  if i < 422 then
                    if i < 421 then
                      w420 x
                    else
                      w421 x
                  else
                    if i < 423 then
                      w422 x
                    else
                      w423 x
      else
        if i < 473 then
          if i < 448 then
            if i < 436 then
              if i < 430 then
                if i < 427 then
                  if i < 425 then
                    w424 x
                  else
                    if i < 426 then
                      w425 x
                    else
                      w426 x
                else
                  if i < 428 then
                    w427 x
                  else
                    if i < 429 then
                      w428 x
                    else
                      w429 x
              else
                if i < 433 then
                  if i < 431 then
                    w430 x
                  else
                    if i < 432 then
                      w431 x
                    else
                      w432 x
                else
                  if i < 434 then
                    w433 x
                  else
                    if i < 435 then
                      w434 x
                    else
                      w435 x
            else
              if i < 442 then
                if i < 439 then
                  if i < 437 then
                    w436 x
                  else
                    if i < 438 then
                      w437 x
                    else
                      w438 x
                else
                  if i < 440 then
                    w439 x
                  else
                    if i < 441 then
                      w440 x
                    else
                      w441 x
              else
                if i < 445 then
                  if i < 443 then
                    w442 x
                  else
                    if i < 444 then
                      w443 x
                    else
                      w444 x
                else
                  if i < 446 then
                    w445 x
                  else
                    if i < 447 then
                      w446 x
                    else
                      w447 x
          else
            if i < 460 then
              if i < 454 then
                if i < 451 then
                  if i < 449 then
                    w448 x
                  else
                    if i < 450 then
                      w449 x
                    else
                      w450 x
                else
                  if i < 452 then
                    w451 x
                  else
                    if i < 453 then
                      w452 x
                    else
                      w453 x
              else
                if i < 457 then
                  if i < 455 then
                    w454 x
                  else
                    if i < 456 then
                      w455 x
                    else
                      w456 x
                else
                  if i < 458 then
                    w457 x
                  else
                    if i < 459 then
                      w458 x
                    else
                      w459 x
            else
              if i < 466 then
                if i < 463 then
                  if i < 461 then
                    w460 x
                  else
                    if i < 462 then
                      w461 x
                    else
                      w462 x
                else
                  if i < 464 then
                    w463 x
                  else
                    if i < 465 then
                      w464 x
                    else
                      w465 x
              else
                if i < 469 then
                  if i < 467 then
                    w466 x
                  else
                    if i < 468 then
                      w467 x
                    else
                      w468 x
                else
                  if i < 471 then
                    if i < 470 then
                      w469 x
                    else
                      w470 x
                  else
                    if i < 472 then
                      w471 x
                    else
                      w472 x
        else
          if i < 498 then
            if i < 485 then
              if i < 479 then
                if i < 476 then
                  if i < 474 then
                    w473 x
                  else
                    if i < 475 then
                      w474 x
                    else
                      w475 x
                else
                  if i < 477 then
                    w476 x
                  else
                    if i < 478 then
                      w477 x
                    else
                      w478 x
              else
                if i < 482 then
                  if i < 480 then
                    w479 x
                  else
                    if i < 481 then
                      w480 x
                    else
                      w481 x
                else
                  if i < 483 then
                    w482 x
                  else
                    if i < 484 then
                      w483 x
                    else
                      w484 x
            else
              if i < 491 then
                if i < 488 then
                  if i < 486 then
                    w485 x
                  else
                    if i < 487 then
                      w486 x
                    else
                      w487 x
                else
                  if i < 489 then
                    w488 x
                  else
                    if i < 490 then
                      w489 x
                    else
                      w490 x
              else
                if i < 494 then
                  if i < 492 then
                    w491 x
                  else
                    if i < 493 then
                      w492 x
                    else
                      w493 x
                else
                  if i < 496 then
                    if i < 495 then
                      w494 x
                    else
                      w495 x
                  else
                    if i < 497 then
                      w496 x
                    else
                      w497 x
          else
            if i < 510 then
              if i < 504 then
                if i < 501 then
                  if i < 499 then
                    w498 x
                  else
                    if i < 500 then
                      w499 x
                    else
                      w500 x
                else
                  if i < 502 then
                    w501 x
                  else
                    if i < 503 then
                      w502 x
                    else
                      w503 x
              else
                if i < 507 then
                  if i < 505 then
                    w504 x
                  else
                    if i < 506 then
                      w505 x
                    else
                      w506 x
                else
                  if i < 508 then
                    w507 x
                  else
                    if i < 509 then
                      w508 x
                    else
                      w509 x
            else
              if i < 516 then
                if i < 513 then
                  if i < 511 then
                    w510 x
                  else
                    if i < 512 then
                      w511 x
                    else
                      w512 x
                else
                  if i < 514 then
                    w513 x
                  else
                    if i < 515 then
                      w514 x
                    else
                      w515 x
              else
                if i < 519 then
                  if i < 517 then
                    w516 x
                  else
                    if i < 518 then
                      w517 x
                    else
                      w518 x
                else
                  if i < 521 then
                    if i < 520 then
                      w519 x
                    else
                      w520 x
                  else
                    if i < 522 then
                      w521 x
                    else
                      w522 x
  else false

lemma table_inputs (x : Fin 128 → Bool) (i : Fin 128) : table x i.val = x i := by
  simp only [table, dif_pos i.isLt]

set_option maxRecDepth 20000 in
lemma table_lookup_128 (x : Fin 128 → Bool) : table x 128 = w128 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_129 (x : Fin 128 → Bool) : table x 129 = w129 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_130 (x : Fin 128 → Bool) : table x 130 = w130 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_131 (x : Fin 128 → Bool) : table x 131 = w131 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_132 (x : Fin 128 → Bool) : table x 132 = w132 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_133 (x : Fin 128 → Bool) : table x 133 = w133 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_134 (x : Fin 128 → Bool) : table x 134 = w134 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_135 (x : Fin 128 → Bool) : table x 135 = w135 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_136 (x : Fin 128 → Bool) : table x 136 = w136 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_137 (x : Fin 128 → Bool) : table x 137 = w137 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_138 (x : Fin 128 → Bool) : table x 138 = w138 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_139 (x : Fin 128 → Bool) : table x 139 = w139 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_140 (x : Fin 128 → Bool) : table x 140 = w140 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_141 (x : Fin 128 → Bool) : table x 141 = w141 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_142 (x : Fin 128 → Bool) : table x 142 = w142 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_143 (x : Fin 128 → Bool) : table x 143 = w143 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_144 (x : Fin 128 → Bool) : table x 144 = w144 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_145 (x : Fin 128 → Bool) : table x 145 = w145 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_146 (x : Fin 128 → Bool) : table x 146 = w146 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_147 (x : Fin 128 → Bool) : table x 147 = w147 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_148 (x : Fin 128 → Bool) : table x 148 = w148 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_149 (x : Fin 128 → Bool) : table x 149 = w149 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_150 (x : Fin 128 → Bool) : table x 150 = w150 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_151 (x : Fin 128 → Bool) : table x 151 = w151 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_152 (x : Fin 128 → Bool) : table x 152 = w152 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_153 (x : Fin 128 → Bool) : table x 153 = w153 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_154 (x : Fin 128 → Bool) : table x 154 = w154 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_155 (x : Fin 128 → Bool) : table x 155 = w155 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_156 (x : Fin 128 → Bool) : table x 156 = w156 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_157 (x : Fin 128 → Bool) : table x 157 = w157 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_158 (x : Fin 128 → Bool) : table x 158 = w158 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_159 (x : Fin 128 → Bool) : table x 159 = w159 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_160 (x : Fin 128 → Bool) : table x 160 = w160 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_161 (x : Fin 128 → Bool) : table x 161 = w161 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_162 (x : Fin 128 → Bool) : table x 162 = w162 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_163 (x : Fin 128 → Bool) : table x 163 = w163 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_164 (x : Fin 128 → Bool) : table x 164 = w164 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_165 (x : Fin 128 → Bool) : table x 165 = w165 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_166 (x : Fin 128 → Bool) : table x 166 = w166 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_167 (x : Fin 128 → Bool) : table x 167 = w167 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_168 (x : Fin 128 → Bool) : table x 168 = w168 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_169 (x : Fin 128 → Bool) : table x 169 = w169 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_170 (x : Fin 128 → Bool) : table x 170 = w170 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_171 (x : Fin 128 → Bool) : table x 171 = w171 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_172 (x : Fin 128 → Bool) : table x 172 = w172 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_173 (x : Fin 128 → Bool) : table x 173 = w173 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_174 (x : Fin 128 → Bool) : table x 174 = w174 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_175 (x : Fin 128 → Bool) : table x 175 = w175 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_176 (x : Fin 128 → Bool) : table x 176 = w176 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_177 (x : Fin 128 → Bool) : table x 177 = w177 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_178 (x : Fin 128 → Bool) : table x 178 = w178 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_179 (x : Fin 128 → Bool) : table x 179 = w179 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_180 (x : Fin 128 → Bool) : table x 180 = w180 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_181 (x : Fin 128 → Bool) : table x 181 = w181 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_182 (x : Fin 128 → Bool) : table x 182 = w182 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_183 (x : Fin 128 → Bool) : table x 183 = w183 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_184 (x : Fin 128 → Bool) : table x 184 = w184 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_185 (x : Fin 128 → Bool) : table x 185 = w185 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_186 (x : Fin 128 → Bool) : table x 186 = w186 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_187 (x : Fin 128 → Bool) : table x 187 = w187 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_188 (x : Fin 128 → Bool) : table x 188 = w188 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_189 (x : Fin 128 → Bool) : table x 189 = w189 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_190 (x : Fin 128 → Bool) : table x 190 = w190 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_191 (x : Fin 128 → Bool) : table x 191 = w191 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_192 (x : Fin 128 → Bool) : table x 192 = w192 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_193 (x : Fin 128 → Bool) : table x 193 = w193 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_194 (x : Fin 128 → Bool) : table x 194 = w194 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_195 (x : Fin 128 → Bool) : table x 195 = w195 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_196 (x : Fin 128 → Bool) : table x 196 = w196 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_197 (x : Fin 128 → Bool) : table x 197 = w197 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_198 (x : Fin 128 → Bool) : table x 198 = w198 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_199 (x : Fin 128 → Bool) : table x 199 = w199 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_200 (x : Fin 128 → Bool) : table x 200 = w200 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_201 (x : Fin 128 → Bool) : table x 201 = w201 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_202 (x : Fin 128 → Bool) : table x 202 = w202 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_203 (x : Fin 128 → Bool) : table x 203 = w203 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_204 (x : Fin 128 → Bool) : table x 204 = w204 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_205 (x : Fin 128 → Bool) : table x 205 = w205 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_206 (x : Fin 128 → Bool) : table x 206 = w206 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_207 (x : Fin 128 → Bool) : table x 207 = w207 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_208 (x : Fin 128 → Bool) : table x 208 = w208 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_209 (x : Fin 128 → Bool) : table x 209 = w209 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_210 (x : Fin 128 → Bool) : table x 210 = w210 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_211 (x : Fin 128 → Bool) : table x 211 = w211 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_212 (x : Fin 128 → Bool) : table x 212 = w212 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_213 (x : Fin 128 → Bool) : table x 213 = w213 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_214 (x : Fin 128 → Bool) : table x 214 = w214 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_215 (x : Fin 128 → Bool) : table x 215 = w215 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_216 (x : Fin 128 → Bool) : table x 216 = w216 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_217 (x : Fin 128 → Bool) : table x 217 = w217 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_218 (x : Fin 128 → Bool) : table x 218 = w218 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_219 (x : Fin 128 → Bool) : table x 219 = w219 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_220 (x : Fin 128 → Bool) : table x 220 = w220 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_221 (x : Fin 128 → Bool) : table x 221 = w221 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_222 (x : Fin 128 → Bool) : table x 222 = w222 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_223 (x : Fin 128 → Bool) : table x 223 = w223 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_224 (x : Fin 128 → Bool) : table x 224 = w224 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_225 (x : Fin 128 → Bool) : table x 225 = w225 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_226 (x : Fin 128 → Bool) : table x 226 = w226 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_227 (x : Fin 128 → Bool) : table x 227 = w227 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_228 (x : Fin 128 → Bool) : table x 228 = w228 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_229 (x : Fin 128 → Bool) : table x 229 = w229 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_230 (x : Fin 128 → Bool) : table x 230 = w230 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_231 (x : Fin 128 → Bool) : table x 231 = w231 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_232 (x : Fin 128 → Bool) : table x 232 = w232 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_233 (x : Fin 128 → Bool) : table x 233 = w233 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_234 (x : Fin 128 → Bool) : table x 234 = w234 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_235 (x : Fin 128 → Bool) : table x 235 = w235 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_236 (x : Fin 128 → Bool) : table x 236 = w236 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_237 (x : Fin 128 → Bool) : table x 237 = w237 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_238 (x : Fin 128 → Bool) : table x 238 = w238 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_239 (x : Fin 128 → Bool) : table x 239 = w239 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_240 (x : Fin 128 → Bool) : table x 240 = w240 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_241 (x : Fin 128 → Bool) : table x 241 = w241 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_242 (x : Fin 128 → Bool) : table x 242 = w242 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_243 (x : Fin 128 → Bool) : table x 243 = w243 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_244 (x : Fin 128 → Bool) : table x 244 = w244 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_245 (x : Fin 128 → Bool) : table x 245 = w245 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_246 (x : Fin 128 → Bool) : table x 246 = w246 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_247 (x : Fin 128 → Bool) : table x 247 = w247 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_248 (x : Fin 128 → Bool) : table x 248 = w248 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_249 (x : Fin 128 → Bool) : table x 249 = w249 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_250 (x : Fin 128 → Bool) : table x 250 = w250 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_251 (x : Fin 128 → Bool) : table x 251 = w251 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_252 (x : Fin 128 → Bool) : table x 252 = w252 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_253 (x : Fin 128 → Bool) : table x 253 = w253 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_254 (x : Fin 128 → Bool) : table x 254 = w254 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_255 (x : Fin 128 → Bool) : table x 255 = w255 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_256 (x : Fin 128 → Bool) : table x 256 = w256 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_257 (x : Fin 128 → Bool) : table x 257 = w257 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_258 (x : Fin 128 → Bool) : table x 258 = w258 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_259 (x : Fin 128 → Bool) : table x 259 = w259 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_260 (x : Fin 128 → Bool) : table x 260 = w260 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_261 (x : Fin 128 → Bool) : table x 261 = w261 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_262 (x : Fin 128 → Bool) : table x 262 = w262 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_263 (x : Fin 128 → Bool) : table x 263 = w263 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_264 (x : Fin 128 → Bool) : table x 264 = w264 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_265 (x : Fin 128 → Bool) : table x 265 = w265 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_266 (x : Fin 128 → Bool) : table x 266 = w266 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_267 (x : Fin 128 → Bool) : table x 267 = w267 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_268 (x : Fin 128 → Bool) : table x 268 = w268 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_269 (x : Fin 128 → Bool) : table x 269 = w269 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_270 (x : Fin 128 → Bool) : table x 270 = w270 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_271 (x : Fin 128 → Bool) : table x 271 = w271 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_272 (x : Fin 128 → Bool) : table x 272 = w272 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_273 (x : Fin 128 → Bool) : table x 273 = w273 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_274 (x : Fin 128 → Bool) : table x 274 = w274 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_275 (x : Fin 128 → Bool) : table x 275 = w275 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_276 (x : Fin 128 → Bool) : table x 276 = w276 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_277 (x : Fin 128 → Bool) : table x 277 = w277 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_278 (x : Fin 128 → Bool) : table x 278 = w278 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_279 (x : Fin 128 → Bool) : table x 279 = w279 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_280 (x : Fin 128 → Bool) : table x 280 = w280 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_281 (x : Fin 128 → Bool) : table x 281 = w281 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_282 (x : Fin 128 → Bool) : table x 282 = w282 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_283 (x : Fin 128 → Bool) : table x 283 = w283 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_284 (x : Fin 128 → Bool) : table x 284 = w284 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_285 (x : Fin 128 → Bool) : table x 285 = w285 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_286 (x : Fin 128 → Bool) : table x 286 = w286 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_287 (x : Fin 128 → Bool) : table x 287 = w287 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_288 (x : Fin 128 → Bool) : table x 288 = w288 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_289 (x : Fin 128 → Bool) : table x 289 = w289 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_290 (x : Fin 128 → Bool) : table x 290 = w290 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_291 (x : Fin 128 → Bool) : table x 291 = w291 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_292 (x : Fin 128 → Bool) : table x 292 = w292 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_293 (x : Fin 128 → Bool) : table x 293 = w293 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_294 (x : Fin 128 → Bool) : table x 294 = w294 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_295 (x : Fin 128 → Bool) : table x 295 = w295 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_296 (x : Fin 128 → Bool) : table x 296 = w296 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_297 (x : Fin 128 → Bool) : table x 297 = w297 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_298 (x : Fin 128 → Bool) : table x 298 = w298 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_299 (x : Fin 128 → Bool) : table x 299 = w299 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_300 (x : Fin 128 → Bool) : table x 300 = w300 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_301 (x : Fin 128 → Bool) : table x 301 = w301 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_302 (x : Fin 128 → Bool) : table x 302 = w302 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_303 (x : Fin 128 → Bool) : table x 303 = w303 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_304 (x : Fin 128 → Bool) : table x 304 = w304 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_305 (x : Fin 128 → Bool) : table x 305 = w305 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_306 (x : Fin 128 → Bool) : table x 306 = w306 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_307 (x : Fin 128 → Bool) : table x 307 = w307 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_308 (x : Fin 128 → Bool) : table x 308 = w308 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_309 (x : Fin 128 → Bool) : table x 309 = w309 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_310 (x : Fin 128 → Bool) : table x 310 = w310 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_311 (x : Fin 128 → Bool) : table x 311 = w311 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_312 (x : Fin 128 → Bool) : table x 312 = w312 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_313 (x : Fin 128 → Bool) : table x 313 = w313 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_314 (x : Fin 128 → Bool) : table x 314 = w314 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_315 (x : Fin 128 → Bool) : table x 315 = w315 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_316 (x : Fin 128 → Bool) : table x 316 = w316 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_317 (x : Fin 128 → Bool) : table x 317 = w317 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_318 (x : Fin 128 → Bool) : table x 318 = w318 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_319 (x : Fin 128 → Bool) : table x 319 = w319 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_320 (x : Fin 128 → Bool) : table x 320 = w320 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_321 (x : Fin 128 → Bool) : table x 321 = w321 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_322 (x : Fin 128 → Bool) : table x 322 = w322 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_323 (x : Fin 128 → Bool) : table x 323 = w323 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_324 (x : Fin 128 → Bool) : table x 324 = w324 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_325 (x : Fin 128 → Bool) : table x 325 = w325 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_326 (x : Fin 128 → Bool) : table x 326 = w326 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_327 (x : Fin 128 → Bool) : table x 327 = w327 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_328 (x : Fin 128 → Bool) : table x 328 = w328 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_329 (x : Fin 128 → Bool) : table x 329 = w329 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_330 (x : Fin 128 → Bool) : table x 330 = w330 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_331 (x : Fin 128 → Bool) : table x 331 = w331 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_332 (x : Fin 128 → Bool) : table x 332 = w332 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_333 (x : Fin 128 → Bool) : table x 333 = w333 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_334 (x : Fin 128 → Bool) : table x 334 = w334 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_335 (x : Fin 128 → Bool) : table x 335 = w335 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_336 (x : Fin 128 → Bool) : table x 336 = w336 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_337 (x : Fin 128 → Bool) : table x 337 = w337 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_338 (x : Fin 128 → Bool) : table x 338 = w338 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_339 (x : Fin 128 → Bool) : table x 339 = w339 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_340 (x : Fin 128 → Bool) : table x 340 = w340 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_341 (x : Fin 128 → Bool) : table x 341 = w341 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_342 (x : Fin 128 → Bool) : table x 342 = w342 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_343 (x : Fin 128 → Bool) : table x 343 = w343 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_344 (x : Fin 128 → Bool) : table x 344 = w344 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_345 (x : Fin 128 → Bool) : table x 345 = w345 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_346 (x : Fin 128 → Bool) : table x 346 = w346 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_347 (x : Fin 128 → Bool) : table x 347 = w347 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_348 (x : Fin 128 → Bool) : table x 348 = w348 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_349 (x : Fin 128 → Bool) : table x 349 = w349 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_350 (x : Fin 128 → Bool) : table x 350 = w350 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_351 (x : Fin 128 → Bool) : table x 351 = w351 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_352 (x : Fin 128 → Bool) : table x 352 = w352 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_353 (x : Fin 128 → Bool) : table x 353 = w353 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_354 (x : Fin 128 → Bool) : table x 354 = w354 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_355 (x : Fin 128 → Bool) : table x 355 = w355 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_356 (x : Fin 128 → Bool) : table x 356 = w356 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_357 (x : Fin 128 → Bool) : table x 357 = w357 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_358 (x : Fin 128 → Bool) : table x 358 = w358 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_359 (x : Fin 128 → Bool) : table x 359 = w359 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_360 (x : Fin 128 → Bool) : table x 360 = w360 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_361 (x : Fin 128 → Bool) : table x 361 = w361 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_362 (x : Fin 128 → Bool) : table x 362 = w362 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_363 (x : Fin 128 → Bool) : table x 363 = w363 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_364 (x : Fin 128 → Bool) : table x 364 = w364 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_365 (x : Fin 128 → Bool) : table x 365 = w365 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_366 (x : Fin 128 → Bool) : table x 366 = w366 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_367 (x : Fin 128 → Bool) : table x 367 = w367 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_368 (x : Fin 128 → Bool) : table x 368 = w368 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_369 (x : Fin 128 → Bool) : table x 369 = w369 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_370 (x : Fin 128 → Bool) : table x 370 = w370 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_371 (x : Fin 128 → Bool) : table x 371 = w371 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_372 (x : Fin 128 → Bool) : table x 372 = w372 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_373 (x : Fin 128 → Bool) : table x 373 = w373 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_374 (x : Fin 128 → Bool) : table x 374 = w374 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_375 (x : Fin 128 → Bool) : table x 375 = w375 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_376 (x : Fin 128 → Bool) : table x 376 = w376 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_377 (x : Fin 128 → Bool) : table x 377 = w377 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_378 (x : Fin 128 → Bool) : table x 378 = w378 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_379 (x : Fin 128 → Bool) : table x 379 = w379 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_380 (x : Fin 128 → Bool) : table x 380 = w380 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_381 (x : Fin 128 → Bool) : table x 381 = w381 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_382 (x : Fin 128 → Bool) : table x 382 = w382 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_383 (x : Fin 128 → Bool) : table x 383 = w383 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_384 (x : Fin 128 → Bool) : table x 384 = w384 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_385 (x : Fin 128 → Bool) : table x 385 = w385 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_386 (x : Fin 128 → Bool) : table x 386 = w386 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_387 (x : Fin 128 → Bool) : table x 387 = w387 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_388 (x : Fin 128 → Bool) : table x 388 = w388 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_389 (x : Fin 128 → Bool) : table x 389 = w389 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_390 (x : Fin 128 → Bool) : table x 390 = w390 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_391 (x : Fin 128 → Bool) : table x 391 = w391 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_392 (x : Fin 128 → Bool) : table x 392 = w392 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_393 (x : Fin 128 → Bool) : table x 393 = w393 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_394 (x : Fin 128 → Bool) : table x 394 = w394 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_395 (x : Fin 128 → Bool) : table x 395 = w395 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_396 (x : Fin 128 → Bool) : table x 396 = w396 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_397 (x : Fin 128 → Bool) : table x 397 = w397 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_398 (x : Fin 128 → Bool) : table x 398 = w398 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_399 (x : Fin 128 → Bool) : table x 399 = w399 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_400 (x : Fin 128 → Bool) : table x 400 = w400 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_401 (x : Fin 128 → Bool) : table x 401 = w401 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_402 (x : Fin 128 → Bool) : table x 402 = w402 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_403 (x : Fin 128 → Bool) : table x 403 = w403 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_404 (x : Fin 128 → Bool) : table x 404 = w404 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_405 (x : Fin 128 → Bool) : table x 405 = w405 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_406 (x : Fin 128 → Bool) : table x 406 = w406 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_407 (x : Fin 128 → Bool) : table x 407 = w407 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_408 (x : Fin 128 → Bool) : table x 408 = w408 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_409 (x : Fin 128 → Bool) : table x 409 = w409 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_410 (x : Fin 128 → Bool) : table x 410 = w410 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_411 (x : Fin 128 → Bool) : table x 411 = w411 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_412 (x : Fin 128 → Bool) : table x 412 = w412 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_413 (x : Fin 128 → Bool) : table x 413 = w413 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_414 (x : Fin 128 → Bool) : table x 414 = w414 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_415 (x : Fin 128 → Bool) : table x 415 = w415 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_416 (x : Fin 128 → Bool) : table x 416 = w416 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_417 (x : Fin 128 → Bool) : table x 417 = w417 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_418 (x : Fin 128 → Bool) : table x 418 = w418 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_419 (x : Fin 128 → Bool) : table x 419 = w419 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_420 (x : Fin 128 → Bool) : table x 420 = w420 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_421 (x : Fin 128 → Bool) : table x 421 = w421 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_422 (x : Fin 128 → Bool) : table x 422 = w422 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_423 (x : Fin 128 → Bool) : table x 423 = w423 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_424 (x : Fin 128 → Bool) : table x 424 = w424 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_425 (x : Fin 128 → Bool) : table x 425 = w425 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_426 (x : Fin 128 → Bool) : table x 426 = w426 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_427 (x : Fin 128 → Bool) : table x 427 = w427 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_428 (x : Fin 128 → Bool) : table x 428 = w428 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_429 (x : Fin 128 → Bool) : table x 429 = w429 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_430 (x : Fin 128 → Bool) : table x 430 = w430 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_431 (x : Fin 128 → Bool) : table x 431 = w431 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_432 (x : Fin 128 → Bool) : table x 432 = w432 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_433 (x : Fin 128 → Bool) : table x 433 = w433 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_434 (x : Fin 128 → Bool) : table x 434 = w434 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_435 (x : Fin 128 → Bool) : table x 435 = w435 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_436 (x : Fin 128 → Bool) : table x 436 = w436 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_437 (x : Fin 128 → Bool) : table x 437 = w437 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_438 (x : Fin 128 → Bool) : table x 438 = w438 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_439 (x : Fin 128 → Bool) : table x 439 = w439 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_440 (x : Fin 128 → Bool) : table x 440 = w440 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_441 (x : Fin 128 → Bool) : table x 441 = w441 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_442 (x : Fin 128 → Bool) : table x 442 = w442 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_443 (x : Fin 128 → Bool) : table x 443 = w443 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_444 (x : Fin 128 → Bool) : table x 444 = w444 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_445 (x : Fin 128 → Bool) : table x 445 = w445 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_446 (x : Fin 128 → Bool) : table x 446 = w446 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_447 (x : Fin 128 → Bool) : table x 447 = w447 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_448 (x : Fin 128 → Bool) : table x 448 = w448 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_449 (x : Fin 128 → Bool) : table x 449 = w449 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_450 (x : Fin 128 → Bool) : table x 450 = w450 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_451 (x : Fin 128 → Bool) : table x 451 = w451 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_452 (x : Fin 128 → Bool) : table x 452 = w452 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_453 (x : Fin 128 → Bool) : table x 453 = w453 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_454 (x : Fin 128 → Bool) : table x 454 = w454 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_455 (x : Fin 128 → Bool) : table x 455 = w455 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_456 (x : Fin 128 → Bool) : table x 456 = w456 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_457 (x : Fin 128 → Bool) : table x 457 = w457 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_458 (x : Fin 128 → Bool) : table x 458 = w458 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_459 (x : Fin 128 → Bool) : table x 459 = w459 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_460 (x : Fin 128 → Bool) : table x 460 = w460 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_461 (x : Fin 128 → Bool) : table x 461 = w461 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_462 (x : Fin 128 → Bool) : table x 462 = w462 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_463 (x : Fin 128 → Bool) : table x 463 = w463 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_464 (x : Fin 128 → Bool) : table x 464 = w464 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_465 (x : Fin 128 → Bool) : table x 465 = w465 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_466 (x : Fin 128 → Bool) : table x 466 = w466 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_467 (x : Fin 128 → Bool) : table x 467 = w467 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_468 (x : Fin 128 → Bool) : table x 468 = w468 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_469 (x : Fin 128 → Bool) : table x 469 = w469 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_470 (x : Fin 128 → Bool) : table x 470 = w470 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_471 (x : Fin 128 → Bool) : table x 471 = w471 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_472 (x : Fin 128 → Bool) : table x 472 = w472 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_473 (x : Fin 128 → Bool) : table x 473 = w473 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_474 (x : Fin 128 → Bool) : table x 474 = w474 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_475 (x : Fin 128 → Bool) : table x 475 = w475 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_476 (x : Fin 128 → Bool) : table x 476 = w476 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_477 (x : Fin 128 → Bool) : table x 477 = w477 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_478 (x : Fin 128 → Bool) : table x 478 = w478 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_479 (x : Fin 128 → Bool) : table x 479 = w479 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_480 (x : Fin 128 → Bool) : table x 480 = w480 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_481 (x : Fin 128 → Bool) : table x 481 = w481 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_482 (x : Fin 128 → Bool) : table x 482 = w482 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_483 (x : Fin 128 → Bool) : table x 483 = w483 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_484 (x : Fin 128 → Bool) : table x 484 = w484 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_485 (x : Fin 128 → Bool) : table x 485 = w485 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_486 (x : Fin 128 → Bool) : table x 486 = w486 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_487 (x : Fin 128 → Bool) : table x 487 = w487 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_488 (x : Fin 128 → Bool) : table x 488 = w488 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_489 (x : Fin 128 → Bool) : table x 489 = w489 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_490 (x : Fin 128 → Bool) : table x 490 = w490 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_491 (x : Fin 128 → Bool) : table x 491 = w491 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_492 (x : Fin 128 → Bool) : table x 492 = w492 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_493 (x : Fin 128 → Bool) : table x 493 = w493 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_494 (x : Fin 128 → Bool) : table x 494 = w494 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_495 (x : Fin 128 → Bool) : table x 495 = w495 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_496 (x : Fin 128 → Bool) : table x 496 = w496 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_497 (x : Fin 128 → Bool) : table x 497 = w497 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_498 (x : Fin 128 → Bool) : table x 498 = w498 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_499 (x : Fin 128 → Bool) : table x 499 = w499 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_500 (x : Fin 128 → Bool) : table x 500 = w500 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_501 (x : Fin 128 → Bool) : table x 501 = w501 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_502 (x : Fin 128 → Bool) : table x 502 = w502 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_503 (x : Fin 128 → Bool) : table x 503 = w503 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_504 (x : Fin 128 → Bool) : table x 504 = w504 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_505 (x : Fin 128 → Bool) : table x 505 = w505 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_506 (x : Fin 128 → Bool) : table x 506 = w506 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_507 (x : Fin 128 → Bool) : table x 507 = w507 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_508 (x : Fin 128 → Bool) : table x 508 = w508 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_509 (x : Fin 128 → Bool) : table x 509 = w509 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_510 (x : Fin 128 → Bool) : table x 510 = w510 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_511 (x : Fin 128 → Bool) : table x 511 = w511 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_512 (x : Fin 128 → Bool) : table x 512 = w512 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_513 (x : Fin 128 → Bool) : table x 513 = w513 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_514 (x : Fin 128 → Bool) : table x 514 = w514 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_515 (x : Fin 128 → Bool) : table x 515 = w515 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_516 (x : Fin 128 → Bool) : table x 516 = w516 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_517 (x : Fin 128 → Bool) : table x 517 = w517 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_518 (x : Fin 128 → Bool) : table x 518 = w518 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_519 (x : Fin 128 → Bool) : table x 519 = w519 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_520 (x : Fin 128 → Bool) : table x 520 = w520 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_521 (x : Fin 128 → Bool) : table x 521 = w521 x := by
  rfl

set_option maxRecDepth 20000 in
lemma table_lookup_522 (x : Fin 128 → Bool) : table x 522 = w522 x := by
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_0 (x : Fin 128 → Bool) :
    (gates.getD 0 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 0 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 128 := by
  have h : gates.getD 0 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [0, 1]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨0, by decide⟩, table_inputs x ⟨1, by decide⟩, table_lookup_128]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_1 (x : Fin 128 → Bool) :
    (gates.getD 1 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 1 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 129 := by
  have h : gates.getD 1 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [128, 2]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_128, table_inputs x ⟨2, by decide⟩, table_lookup_129]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_2 (x : Fin 128 → Bool) :
    (gates.getD 2 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 2 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 130 := by
  have h : gates.getD 2 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [129, 3]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_129, table_inputs x ⟨3, by decide⟩, table_lookup_130]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_3 (x : Fin 128 → Bool) :
    (gates.getD 3 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 3 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 131 := by
  have h : gates.getD 3 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [130, 4]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_130, table_inputs x ⟨4, by decide⟩, table_lookup_131]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_4 (x : Fin 128 → Bool) :
    (gates.getD 4 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 4 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 132 := by
  have h : gates.getD 4 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [131, 5]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_131, table_inputs x ⟨5, by decide⟩, table_lookup_132]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_5 (x : Fin 128 → Bool) :
    (gates.getD 5 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 5 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 133 := by
  have h : gates.getD 5 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [132, 6]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_132, table_inputs x ⟨6, by decide⟩, table_lookup_133]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_6 (x : Fin 128 → Bool) :
    (gates.getD 6 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 6 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 134 := by
  have h : gates.getD 6 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [133, 7]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_133, table_inputs x ⟨7, by decide⟩, table_lookup_134]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_7 (x : Fin 128 → Bool) :
    (gates.getD 7 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 7 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 135 := by
  have h : gates.getD 7 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [8, 9]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨8, by decide⟩, table_inputs x ⟨9, by decide⟩, table_lookup_135]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_8 (x : Fin 128 → Bool) :
    (gates.getD 8 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 8 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 136 := by
  have h : gates.getD 8 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [135, 10]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_135, table_inputs x ⟨10, by decide⟩, table_lookup_136]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_9 (x : Fin 128 → Bool) :
    (gates.getD 9 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 9 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 137 := by
  have h : gates.getD 9 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [136, 11]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_136, table_inputs x ⟨11, by decide⟩, table_lookup_137]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_10 (x : Fin 128 → Bool) :
    (gates.getD 10 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 10 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 138 := by
  have h : gates.getD 10 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [137, 12]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_137, table_inputs x ⟨12, by decide⟩, table_lookup_138]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_11 (x : Fin 128 → Bool) :
    (gates.getD 11 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 11 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 139 := by
  have h : gates.getD 11 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [138, 13]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_138, table_inputs x ⟨13, by decide⟩, table_lookup_139]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_12 (x : Fin 128 → Bool) :
    (gates.getD 12 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 12 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 140 := by
  have h : gates.getD 12 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [139, 14]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_139, table_inputs x ⟨14, by decide⟩, table_lookup_140]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_13 (x : Fin 128 → Bool) :
    (gates.getD 13 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 13 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 141 := by
  have h : gates.getD 13 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [140, 15]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_140, table_inputs x ⟨15, by decide⟩, table_lookup_141]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_14 (x : Fin 128 → Bool) :
    (gates.getD 14 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 14 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 142 := by
  have h : gates.getD 14 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [16, 17]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨16, by decide⟩, table_inputs x ⟨17, by decide⟩, table_lookup_142]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_15 (x : Fin 128 → Bool) :
    (gates.getD 15 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 15 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 143 := by
  have h : gates.getD 15 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [142, 18]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_142, table_inputs x ⟨18, by decide⟩, table_lookup_143]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_16 (x : Fin 128 → Bool) :
    (gates.getD 16 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 16 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 144 := by
  have h : gates.getD 16 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [143, 19]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_143, table_inputs x ⟨19, by decide⟩, table_lookup_144]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_17 (x : Fin 128 → Bool) :
    (gates.getD 17 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 17 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 145 := by
  have h : gates.getD 17 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [144, 20]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_144, table_inputs x ⟨20, by decide⟩, table_lookup_145]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_18 (x : Fin 128 → Bool) :
    (gates.getD 18 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 18 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 146 := by
  have h : gates.getD 18 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [145, 21]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_145, table_inputs x ⟨21, by decide⟩, table_lookup_146]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_19 (x : Fin 128 → Bool) :
    (gates.getD 19 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 19 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 147 := by
  have h : gates.getD 19 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [146, 22]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_146, table_inputs x ⟨22, by decide⟩, table_lookup_147]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_20 (x : Fin 128 → Bool) :
    (gates.getD 20 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 20 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 148 := by
  have h : gates.getD 20 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [147, 23]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_147, table_inputs x ⟨23, by decide⟩, table_lookup_148]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_21 (x : Fin 128 → Bool) :
    (gates.getD 21 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 21 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 149 := by
  have h : gates.getD 21 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [24, 25]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨24, by decide⟩, table_inputs x ⟨25, by decide⟩, table_lookup_149]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_22 (x : Fin 128 → Bool) :
    (gates.getD 22 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 22 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 150 := by
  have h : gates.getD 22 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [149, 26]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_149, table_inputs x ⟨26, by decide⟩, table_lookup_150]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_23 (x : Fin 128 → Bool) :
    (gates.getD 23 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 23 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 151 := by
  have h : gates.getD 23 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [150, 27]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_150, table_inputs x ⟨27, by decide⟩, table_lookup_151]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_24 (x : Fin 128 → Bool) :
    (gates.getD 24 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 24 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 152 := by
  have h : gates.getD 24 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [151, 28]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_151, table_inputs x ⟨28, by decide⟩, table_lookup_152]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_25 (x : Fin 128 → Bool) :
    (gates.getD 25 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 25 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 153 := by
  have h : gates.getD 25 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [152, 29]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_152, table_inputs x ⟨29, by decide⟩, table_lookup_153]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_26 (x : Fin 128 → Bool) :
    (gates.getD 26 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 26 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 154 := by
  have h : gates.getD 26 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [153, 30]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_153, table_inputs x ⟨30, by decide⟩, table_lookup_154]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_27 (x : Fin 128 → Bool) :
    (gates.getD 27 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 27 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 155 := by
  have h : gates.getD 27 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [154, 31]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_154, table_inputs x ⟨31, by decide⟩, table_lookup_155]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_28 (x : Fin 128 → Bool) :
    (gates.getD 28 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 28 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 156 := by
  have h : gates.getD 28 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [32, 33]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨32, by decide⟩, table_inputs x ⟨33, by decide⟩, table_lookup_156]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_29 (x : Fin 128 → Bool) :
    (gates.getD 29 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 29 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 157 := by
  have h : gates.getD 29 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [156, 34]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_156, table_inputs x ⟨34, by decide⟩, table_lookup_157]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_30 (x : Fin 128 → Bool) :
    (gates.getD 30 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 30 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 158 := by
  have h : gates.getD 30 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [157, 35]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_157, table_inputs x ⟨35, by decide⟩, table_lookup_158]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_31 (x : Fin 128 → Bool) :
    (gates.getD 31 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 31 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 159 := by
  have h : gates.getD 31 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [158, 36]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_158, table_inputs x ⟨36, by decide⟩, table_lookup_159]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_32 (x : Fin 128 → Bool) :
    (gates.getD 32 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 32 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 160 := by
  have h : gates.getD 32 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [159, 37]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_159, table_inputs x ⟨37, by decide⟩, table_lookup_160]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_33 (x : Fin 128 → Bool) :
    (gates.getD 33 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 33 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 161 := by
  have h : gates.getD 33 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [160, 38]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_160, table_inputs x ⟨38, by decide⟩, table_lookup_161]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_34 (x : Fin 128 → Bool) :
    (gates.getD 34 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 34 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 162 := by
  have h : gates.getD 34 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [161, 39]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_161, table_inputs x ⟨39, by decide⟩, table_lookup_162]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_35 (x : Fin 128 → Bool) :
    (gates.getD 35 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 35 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 163 := by
  have h : gates.getD 35 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [40, 41]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨40, by decide⟩, table_inputs x ⟨41, by decide⟩, table_lookup_163]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_36 (x : Fin 128 → Bool) :
    (gates.getD 36 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 36 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 164 := by
  have h : gates.getD 36 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [163, 42]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_163, table_inputs x ⟨42, by decide⟩, table_lookup_164]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_37 (x : Fin 128 → Bool) :
    (gates.getD 37 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 37 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 165 := by
  have h : gates.getD 37 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [164, 43]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_164, table_inputs x ⟨43, by decide⟩, table_lookup_165]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_38 (x : Fin 128 → Bool) :
    (gates.getD 38 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 38 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 166 := by
  have h : gates.getD 38 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [165, 44]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_165, table_inputs x ⟨44, by decide⟩, table_lookup_166]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_39 (x : Fin 128 → Bool) :
    (gates.getD 39 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 39 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 167 := by
  have h : gates.getD 39 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [166, 45]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_166, table_inputs x ⟨45, by decide⟩, table_lookup_167]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_40 (x : Fin 128 → Bool) :
    (gates.getD 40 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 40 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 168 := by
  have h : gates.getD 40 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [167, 46]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_167, table_inputs x ⟨46, by decide⟩, table_lookup_168]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_41 (x : Fin 128 → Bool) :
    (gates.getD 41 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 41 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 169 := by
  have h : gates.getD 41 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [168, 47]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_168, table_inputs x ⟨47, by decide⟩, table_lookup_169]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_42 (x : Fin 128 → Bool) :
    (gates.getD 42 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 42 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 170 := by
  have h : gates.getD 42 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [48, 49]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨48, by decide⟩, table_inputs x ⟨49, by decide⟩, table_lookup_170]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_43 (x : Fin 128 → Bool) :
    (gates.getD 43 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 43 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 171 := by
  have h : gates.getD 43 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [170, 50]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_170, table_inputs x ⟨50, by decide⟩, table_lookup_171]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_44 (x : Fin 128 → Bool) :
    (gates.getD 44 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 44 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 172 := by
  have h : gates.getD 44 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [171, 51]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_171, table_inputs x ⟨51, by decide⟩, table_lookup_172]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_45 (x : Fin 128 → Bool) :
    (gates.getD 45 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 45 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 173 := by
  have h : gates.getD 45 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [172, 52]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_172, table_inputs x ⟨52, by decide⟩, table_lookup_173]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_46 (x : Fin 128 → Bool) :
    (gates.getD 46 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 46 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 174 := by
  have h : gates.getD 46 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [173, 53]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_173, table_inputs x ⟨53, by decide⟩, table_lookup_174]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_47 (x : Fin 128 → Bool) :
    (gates.getD 47 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 47 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 175 := by
  have h : gates.getD 47 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [174, 54]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_174, table_inputs x ⟨54, by decide⟩, table_lookup_175]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_48 (x : Fin 128 → Bool) :
    (gates.getD 48 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 48 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 176 := by
  have h : gates.getD 48 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [175, 55]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_175, table_inputs x ⟨55, by decide⟩, table_lookup_176]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_49 (x : Fin 128 → Bool) :
    (gates.getD 49 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 49 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 177 := by
  have h : gates.getD 49 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [56, 57]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨56, by decide⟩, table_inputs x ⟨57, by decide⟩, table_lookup_177]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_50 (x : Fin 128 → Bool) :
    (gates.getD 50 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 50 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 178 := by
  have h : gates.getD 50 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [177, 58]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_177, table_inputs x ⟨58, by decide⟩, table_lookup_178]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_51 (x : Fin 128 → Bool) :
    (gates.getD 51 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 51 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 179 := by
  have h : gates.getD 51 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [178, 59]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_178, table_inputs x ⟨59, by decide⟩, table_lookup_179]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_52 (x : Fin 128 → Bool) :
    (gates.getD 52 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 52 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 180 := by
  have h : gates.getD 52 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [179, 60]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_179, table_inputs x ⟨60, by decide⟩, table_lookup_180]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_53 (x : Fin 128 → Bool) :
    (gates.getD 53 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 53 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 181 := by
  have h : gates.getD 53 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [180, 61]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_180, table_inputs x ⟨61, by decide⟩, table_lookup_181]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_54 (x : Fin 128 → Bool) :
    (gates.getD 54 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 54 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 182 := by
  have h : gates.getD 54 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [181, 62]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_181, table_inputs x ⟨62, by decide⟩, table_lookup_182]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_55 (x : Fin 128 → Bool) :
    (gates.getD 55 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 55 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 183 := by
  have h : gates.getD 55 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [182, 63]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_182, table_inputs x ⟨63, by decide⟩, table_lookup_183]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_56 (x : Fin 128 → Bool) :
    (gates.getD 56 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 56 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 184 := by
  have h : gates.getD 56 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [0, 8]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨0, by decide⟩, table_inputs x ⟨8, by decide⟩, table_lookup_184]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_57 (x : Fin 128 → Bool) :
    (gates.getD 57 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 57 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 185 := by
  have h : gates.getD 57 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [184, 16]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_184, table_inputs x ⟨16, by decide⟩, table_lookup_185]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_58 (x : Fin 128 → Bool) :
    (gates.getD 58 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 58 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 186 := by
  have h : gates.getD 58 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [185, 24]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_185, table_inputs x ⟨24, by decide⟩, table_lookup_186]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_59 (x : Fin 128 → Bool) :
    (gates.getD 59 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 59 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 187 := by
  have h : gates.getD 59 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [186, 32]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_186, table_inputs x ⟨32, by decide⟩, table_lookup_187]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_60 (x : Fin 128 → Bool) :
    (gates.getD 60 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 60 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 188 := by
  have h : gates.getD 60 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [187, 40]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_187, table_inputs x ⟨40, by decide⟩, table_lookup_188]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_61 (x : Fin 128 → Bool) :
    (gates.getD 61 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 61 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 189 := by
  have h : gates.getD 61 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [188, 48]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_188, table_inputs x ⟨48, by decide⟩, table_lookup_189]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_62 (x : Fin 128 → Bool) :
    (gates.getD 62 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 62 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 190 := by
  have h : gates.getD 62 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [189, 56]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_189, table_inputs x ⟨56, by decide⟩, table_lookup_190]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_63 (x : Fin 128 → Bool) :
    (gates.getD 63 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 63 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 191 := by
  have h : gates.getD 63 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [1, 9]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨1, by decide⟩, table_inputs x ⟨9, by decide⟩, table_lookup_191]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_64 (x : Fin 128 → Bool) :
    (gates.getD 64 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 64 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 192 := by
  have h : gates.getD 64 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [191, 17]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_191, table_inputs x ⟨17, by decide⟩, table_lookup_192]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_65 (x : Fin 128 → Bool) :
    (gates.getD 65 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 65 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 193 := by
  have h : gates.getD 65 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [192, 25]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_192, table_inputs x ⟨25, by decide⟩, table_lookup_193]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_66 (x : Fin 128 → Bool) :
    (gates.getD 66 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 66 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 194 := by
  have h : gates.getD 66 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [193, 33]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_193, table_inputs x ⟨33, by decide⟩, table_lookup_194]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_67 (x : Fin 128 → Bool) :
    (gates.getD 67 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 67 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 195 := by
  have h : gates.getD 67 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [194, 41]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_194, table_inputs x ⟨41, by decide⟩, table_lookup_195]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_68 (x : Fin 128 → Bool) :
    (gates.getD 68 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 68 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 196 := by
  have h : gates.getD 68 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [195, 49]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_195, table_inputs x ⟨49, by decide⟩, table_lookup_196]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_69 (x : Fin 128 → Bool) :
    (gates.getD 69 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 69 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 197 := by
  have h : gates.getD 69 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [196, 57]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_196, table_inputs x ⟨57, by decide⟩, table_lookup_197]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_70 (x : Fin 128 → Bool) :
    (gates.getD 70 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 70 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 198 := by
  have h : gates.getD 70 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [2, 10]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨2, by decide⟩, table_inputs x ⟨10, by decide⟩, table_lookup_198]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_71 (x : Fin 128 → Bool) :
    (gates.getD 71 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 71 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 199 := by
  have h : gates.getD 71 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [198, 18]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_198, table_inputs x ⟨18, by decide⟩, table_lookup_199]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_72 (x : Fin 128 → Bool) :
    (gates.getD 72 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 72 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 200 := by
  have h : gates.getD 72 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [199, 26]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_199, table_inputs x ⟨26, by decide⟩, table_lookup_200]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_73 (x : Fin 128 → Bool) :
    (gates.getD 73 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 73 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 201 := by
  have h : gates.getD 73 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [200, 34]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_200, table_inputs x ⟨34, by decide⟩, table_lookup_201]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_74 (x : Fin 128 → Bool) :
    (gates.getD 74 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 74 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 202 := by
  have h : gates.getD 74 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [201, 42]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_201, table_inputs x ⟨42, by decide⟩, table_lookup_202]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_75 (x : Fin 128 → Bool) :
    (gates.getD 75 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 75 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 203 := by
  have h : gates.getD 75 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [202, 50]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_202, table_inputs x ⟨50, by decide⟩, table_lookup_203]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_76 (x : Fin 128 → Bool) :
    (gates.getD 76 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 76 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 204 := by
  have h : gates.getD 76 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [203, 58]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_203, table_inputs x ⟨58, by decide⟩, table_lookup_204]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_77 (x : Fin 128 → Bool) :
    (gates.getD 77 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 77 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 205 := by
  have h : gates.getD 77 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [3, 11]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨3, by decide⟩, table_inputs x ⟨11, by decide⟩, table_lookup_205]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_78 (x : Fin 128 → Bool) :
    (gates.getD 78 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 78 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 206 := by
  have h : gates.getD 78 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [205, 19]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_205, table_inputs x ⟨19, by decide⟩, table_lookup_206]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_79 (x : Fin 128 → Bool) :
    (gates.getD 79 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 79 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 207 := by
  have h : gates.getD 79 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [206, 27]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_206, table_inputs x ⟨27, by decide⟩, table_lookup_207]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_80 (x : Fin 128 → Bool) :
    (gates.getD 80 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 80 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 208 := by
  have h : gates.getD 80 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [207, 35]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_207, table_inputs x ⟨35, by decide⟩, table_lookup_208]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_81 (x : Fin 128 → Bool) :
    (gates.getD 81 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 81 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 209 := by
  have h : gates.getD 81 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [208, 43]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_208, table_inputs x ⟨43, by decide⟩, table_lookup_209]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_82 (x : Fin 128 → Bool) :
    (gates.getD 82 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 82 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 210 := by
  have h : gates.getD 82 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [209, 51]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_209, table_inputs x ⟨51, by decide⟩, table_lookup_210]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_83 (x : Fin 128 → Bool) :
    (gates.getD 83 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 83 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 211 := by
  have h : gates.getD 83 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [210, 59]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_210, table_inputs x ⟨59, by decide⟩, table_lookup_211]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_84 (x : Fin 128 → Bool) :
    (gates.getD 84 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 84 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 212 := by
  have h : gates.getD 84 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [4, 12]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨4, by decide⟩, table_inputs x ⟨12, by decide⟩, table_lookup_212]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_85 (x : Fin 128 → Bool) :
    (gates.getD 85 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 85 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 213 := by
  have h : gates.getD 85 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [212, 20]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_212, table_inputs x ⟨20, by decide⟩, table_lookup_213]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_86 (x : Fin 128 → Bool) :
    (gates.getD 86 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 86 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 214 := by
  have h : gates.getD 86 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [213, 28]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_213, table_inputs x ⟨28, by decide⟩, table_lookup_214]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_87 (x : Fin 128 → Bool) :
    (gates.getD 87 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 87 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 215 := by
  have h : gates.getD 87 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [214, 36]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_214, table_inputs x ⟨36, by decide⟩, table_lookup_215]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_88 (x : Fin 128 → Bool) :
    (gates.getD 88 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 88 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 216 := by
  have h : gates.getD 88 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [215, 44]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_215, table_inputs x ⟨44, by decide⟩, table_lookup_216]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_89 (x : Fin 128 → Bool) :
    (gates.getD 89 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 89 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 217 := by
  have h : gates.getD 89 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [216, 52]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_216, table_inputs x ⟨52, by decide⟩, table_lookup_217]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_90 (x : Fin 128 → Bool) :
    (gates.getD 90 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 90 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 218 := by
  have h : gates.getD 90 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [217, 60]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_217, table_inputs x ⟨60, by decide⟩, table_lookup_218]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_91 (x : Fin 128 → Bool) :
    (gates.getD 91 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 91 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 219 := by
  have h : gates.getD 91 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [5, 13]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨5, by decide⟩, table_inputs x ⟨13, by decide⟩, table_lookup_219]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_92 (x : Fin 128 → Bool) :
    (gates.getD 92 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 92 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 220 := by
  have h : gates.getD 92 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [219, 21]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_219, table_inputs x ⟨21, by decide⟩, table_lookup_220]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_93 (x : Fin 128 → Bool) :
    (gates.getD 93 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 93 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 221 := by
  have h : gates.getD 93 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [220, 29]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_220, table_inputs x ⟨29, by decide⟩, table_lookup_221]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_94 (x : Fin 128 → Bool) :
    (gates.getD 94 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 94 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 222 := by
  have h : gates.getD 94 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [221, 37]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_221, table_inputs x ⟨37, by decide⟩, table_lookup_222]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_95 (x : Fin 128 → Bool) :
    (gates.getD 95 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 95 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 223 := by
  have h : gates.getD 95 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [222, 45]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_222, table_inputs x ⟨45, by decide⟩, table_lookup_223]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_96 (x : Fin 128 → Bool) :
    (gates.getD 96 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 96 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 224 := by
  have h : gates.getD 96 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [223, 53]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_223, table_inputs x ⟨53, by decide⟩, table_lookup_224]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_97 (x : Fin 128 → Bool) :
    (gates.getD 97 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 97 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 225 := by
  have h : gates.getD 97 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [224, 61]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_224, table_inputs x ⟨61, by decide⟩, table_lookup_225]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_98 (x : Fin 128 → Bool) :
    (gates.getD 98 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 98 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 226 := by
  have h : gates.getD 98 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [6, 14]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨6, by decide⟩, table_inputs x ⟨14, by decide⟩, table_lookup_226]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_99 (x : Fin 128 → Bool) :
    (gates.getD 99 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 99 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 227 := by
  have h : gates.getD 99 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [226, 22]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_226, table_inputs x ⟨22, by decide⟩, table_lookup_227]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_100 (x : Fin 128 → Bool) :
    (gates.getD 100 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 100 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 228 := by
  have h : gates.getD 100 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [227, 30]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_227, table_inputs x ⟨30, by decide⟩, table_lookup_228]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_101 (x : Fin 128 → Bool) :
    (gates.getD 101 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 101 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 229 := by
  have h : gates.getD 101 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [228, 38]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_228, table_inputs x ⟨38, by decide⟩, table_lookup_229]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_102 (x : Fin 128 → Bool) :
    (gates.getD 102 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 102 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 230 := by
  have h : gates.getD 102 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [229, 46]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_229, table_inputs x ⟨46, by decide⟩, table_lookup_230]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_103 (x : Fin 128 → Bool) :
    (gates.getD 103 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 103 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 231 := by
  have h : gates.getD 103 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [230, 54]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_230, table_inputs x ⟨54, by decide⟩, table_lookup_231]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_104 (x : Fin 128 → Bool) :
    (gates.getD 104 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 104 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 232 := by
  have h : gates.getD 104 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [231, 62]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_231, table_inputs x ⟨62, by decide⟩, table_lookup_232]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_105 (x : Fin 128 → Bool) :
    (gates.getD 105 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 105 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 233 := by
  have h : gates.getD 105 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [7, 15]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨7, by decide⟩, table_inputs x ⟨15, by decide⟩, table_lookup_233]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_106 (x : Fin 128 → Bool) :
    (gates.getD 106 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 106 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 234 := by
  have h : gates.getD 106 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [233, 23]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_233, table_inputs x ⟨23, by decide⟩, table_lookup_234]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_107 (x : Fin 128 → Bool) :
    (gates.getD 107 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 107 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 235 := by
  have h : gates.getD 107 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [234, 31]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_234, table_inputs x ⟨31, by decide⟩, table_lookup_235]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_108 (x : Fin 128 → Bool) :
    (gates.getD 108 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 108 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 236 := by
  have h : gates.getD 108 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [235, 39]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_235, table_inputs x ⟨39, by decide⟩, table_lookup_236]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_109 (x : Fin 128 → Bool) :
    (gates.getD 109 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 109 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 237 := by
  have h : gates.getD 109 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [236, 47]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_236, table_inputs x ⟨47, by decide⟩, table_lookup_237]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_110 (x : Fin 128 → Bool) :
    (gates.getD 110 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 110 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 238 := by
  have h : gates.getD 110 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [237, 55]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_237, table_inputs x ⟨55, by decide⟩, table_lookup_238]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_111 (x : Fin 128 → Bool) :
    (gates.getD 111 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 111 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 239 := by
  have h : gates.getD 111 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [238, 63]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_238, table_inputs x ⟨63, by decide⟩, table_lookup_239]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_112 (x : Fin 128 → Bool) :
    (gates.getD 112 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 112 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 240 := by
  have h : gates.getD 112 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [64, 65]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨64, by decide⟩, table_inputs x ⟨65, by decide⟩, table_lookup_240]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_113 (x : Fin 128 → Bool) :
    (gates.getD 113 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 113 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 241 := by
  have h : gates.getD 113 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [240, 66]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_240, table_inputs x ⟨66, by decide⟩, table_lookup_241]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_114 (x : Fin 128 → Bool) :
    (gates.getD 114 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 114 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 242 := by
  have h : gates.getD 114 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [241, 67]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_241, table_inputs x ⟨67, by decide⟩, table_lookup_242]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_115 (x : Fin 128 → Bool) :
    (gates.getD 115 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 115 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 243 := by
  have h : gates.getD 115 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [242, 68]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_242, table_inputs x ⟨68, by decide⟩, table_lookup_243]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_116 (x : Fin 128 → Bool) :
    (gates.getD 116 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 116 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 244 := by
  have h : gates.getD 116 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [243, 69]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_243, table_inputs x ⟨69, by decide⟩, table_lookup_244]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_117 (x : Fin 128 → Bool) :
    (gates.getD 117 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 117 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 245 := by
  have h : gates.getD 117 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [244, 70]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_244, table_inputs x ⟨70, by decide⟩, table_lookup_245]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_118 (x : Fin 128 → Bool) :
    (gates.getD 118 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 118 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 246 := by
  have h : gates.getD 118 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [245, 71]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_245, table_inputs x ⟨71, by decide⟩, table_lookup_246]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_119 (x : Fin 128 → Bool) :
    (gates.getD 119 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 119 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 247 := by
  have h : gates.getD 119 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [72, 73]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨72, by decide⟩, table_inputs x ⟨73, by decide⟩, table_lookup_247]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_120 (x : Fin 128 → Bool) :
    (gates.getD 120 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 120 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 248 := by
  have h : gates.getD 120 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [247, 74]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_247, table_inputs x ⟨74, by decide⟩, table_lookup_248]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_121 (x : Fin 128 → Bool) :
    (gates.getD 121 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 121 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 249 := by
  have h : gates.getD 121 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [248, 75]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_248, table_inputs x ⟨75, by decide⟩, table_lookup_249]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_122 (x : Fin 128 → Bool) :
    (gates.getD 122 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 122 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 250 := by
  have h : gates.getD 122 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [249, 76]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_249, table_inputs x ⟨76, by decide⟩, table_lookup_250]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_123 (x : Fin 128 → Bool) :
    (gates.getD 123 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 123 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 251 := by
  have h : gates.getD 123 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [250, 77]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_250, table_inputs x ⟨77, by decide⟩, table_lookup_251]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_124 (x : Fin 128 → Bool) :
    (gates.getD 124 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 124 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 252 := by
  have h : gates.getD 124 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [251, 78]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_251, table_inputs x ⟨78, by decide⟩, table_lookup_252]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_125 (x : Fin 128 → Bool) :
    (gates.getD 125 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 125 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 253 := by
  have h : gates.getD 125 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [252, 79]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_252, table_inputs x ⟨79, by decide⟩, table_lookup_253]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_126 (x : Fin 128 → Bool) :
    (gates.getD 126 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 126 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 254 := by
  have h : gates.getD 126 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [80, 81]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨80, by decide⟩, table_inputs x ⟨81, by decide⟩, table_lookup_254]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_127 (x : Fin 128 → Bool) :
    (gates.getD 127 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 127 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 255 := by
  have h : gates.getD 127 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [254, 82]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_254, table_inputs x ⟨82, by decide⟩, table_lookup_255]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_128 (x : Fin 128 → Bool) :
    (gates.getD 128 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 128 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 256 := by
  have h : gates.getD 128 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [255, 83]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_255, table_inputs x ⟨83, by decide⟩, table_lookup_256]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_129 (x : Fin 128 → Bool) :
    (gates.getD 129 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 129 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 257 := by
  have h : gates.getD 129 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [256, 84]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_256, table_inputs x ⟨84, by decide⟩, table_lookup_257]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_130 (x : Fin 128 → Bool) :
    (gates.getD 130 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 130 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 258 := by
  have h : gates.getD 130 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [257, 85]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_257, table_inputs x ⟨85, by decide⟩, table_lookup_258]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_131 (x : Fin 128 → Bool) :
    (gates.getD 131 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 131 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 259 := by
  have h : gates.getD 131 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [258, 86]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_258, table_inputs x ⟨86, by decide⟩, table_lookup_259]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_132 (x : Fin 128 → Bool) :
    (gates.getD 132 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 132 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 260 := by
  have h : gates.getD 132 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [259, 87]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_259, table_inputs x ⟨87, by decide⟩, table_lookup_260]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_133 (x : Fin 128 → Bool) :
    (gates.getD 133 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 133 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 261 := by
  have h : gates.getD 133 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [88, 89]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨88, by decide⟩, table_inputs x ⟨89, by decide⟩, table_lookup_261]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_134 (x : Fin 128 → Bool) :
    (gates.getD 134 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 134 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 262 := by
  have h : gates.getD 134 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [261, 90]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_261, table_inputs x ⟨90, by decide⟩, table_lookup_262]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_135 (x : Fin 128 → Bool) :
    (gates.getD 135 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 135 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 263 := by
  have h : gates.getD 135 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [262, 91]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_262, table_inputs x ⟨91, by decide⟩, table_lookup_263]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_136 (x : Fin 128 → Bool) :
    (gates.getD 136 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 136 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 264 := by
  have h : gates.getD 136 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [263, 92]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_263, table_inputs x ⟨92, by decide⟩, table_lookup_264]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_137 (x : Fin 128 → Bool) :
    (gates.getD 137 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 137 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 265 := by
  have h : gates.getD 137 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [264, 93]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_264, table_inputs x ⟨93, by decide⟩, table_lookup_265]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_138 (x : Fin 128 → Bool) :
    (gates.getD 138 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 138 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 266 := by
  have h : gates.getD 138 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [265, 94]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_265, table_inputs x ⟨94, by decide⟩, table_lookup_266]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_139 (x : Fin 128 → Bool) :
    (gates.getD 139 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 139 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 267 := by
  have h : gates.getD 139 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [266, 95]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_266, table_inputs x ⟨95, by decide⟩, table_lookup_267]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_140 (x : Fin 128 → Bool) :
    (gates.getD 140 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 140 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 268 := by
  have h : gates.getD 140 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [96, 97]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨96, by decide⟩, table_inputs x ⟨97, by decide⟩, table_lookup_268]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_141 (x : Fin 128 → Bool) :
    (gates.getD 141 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 141 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 269 := by
  have h : gates.getD 141 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [268, 98]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_268, table_inputs x ⟨98, by decide⟩, table_lookup_269]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_142 (x : Fin 128 → Bool) :
    (gates.getD 142 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 142 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 270 := by
  have h : gates.getD 142 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [269, 99]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_269, table_inputs x ⟨99, by decide⟩, table_lookup_270]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_143 (x : Fin 128 → Bool) :
    (gates.getD 143 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 143 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 271 := by
  have h : gates.getD 143 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [270, 100]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_270, table_inputs x ⟨100, by decide⟩, table_lookup_271]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_144 (x : Fin 128 → Bool) :
    (gates.getD 144 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 144 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 272 := by
  have h : gates.getD 144 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [271, 101]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_271, table_inputs x ⟨101, by decide⟩, table_lookup_272]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_145 (x : Fin 128 → Bool) :
    (gates.getD 145 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 145 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 273 := by
  have h : gates.getD 145 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [272, 102]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_272, table_inputs x ⟨102, by decide⟩, table_lookup_273]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_146 (x : Fin 128 → Bool) :
    (gates.getD 146 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 146 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 274 := by
  have h : gates.getD 146 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [273, 103]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_273, table_inputs x ⟨103, by decide⟩, table_lookup_274]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_147 (x : Fin 128 → Bool) :
    (gates.getD 147 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 147 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 275 := by
  have h : gates.getD 147 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [104, 105]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨104, by decide⟩, table_inputs x ⟨105, by decide⟩, table_lookup_275]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_148 (x : Fin 128 → Bool) :
    (gates.getD 148 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 148 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 276 := by
  have h : gates.getD 148 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [275, 106]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_275, table_inputs x ⟨106, by decide⟩, table_lookup_276]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_149 (x : Fin 128 → Bool) :
    (gates.getD 149 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 149 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 277 := by
  have h : gates.getD 149 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [276, 107]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_276, table_inputs x ⟨107, by decide⟩, table_lookup_277]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_150 (x : Fin 128 → Bool) :
    (gates.getD 150 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 150 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 278 := by
  have h : gates.getD 150 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [277, 108]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_277, table_inputs x ⟨108, by decide⟩, table_lookup_278]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_151 (x : Fin 128 → Bool) :
    (gates.getD 151 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 151 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 279 := by
  have h : gates.getD 151 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [278, 109]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_278, table_inputs x ⟨109, by decide⟩, table_lookup_279]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_152 (x : Fin 128 → Bool) :
    (gates.getD 152 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 152 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 280 := by
  have h : gates.getD 152 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [279, 110]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_279, table_inputs x ⟨110, by decide⟩, table_lookup_280]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_153 (x : Fin 128 → Bool) :
    (gates.getD 153 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 153 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 281 := by
  have h : gates.getD 153 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [280, 111]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_280, table_inputs x ⟨111, by decide⟩, table_lookup_281]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_154 (x : Fin 128 → Bool) :
    (gates.getD 154 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 154 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 282 := by
  have h : gates.getD 154 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [112, 113]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨112, by decide⟩, table_inputs x ⟨113, by decide⟩, table_lookup_282]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_155 (x : Fin 128 → Bool) :
    (gates.getD 155 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 155 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 283 := by
  have h : gates.getD 155 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [282, 114]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_282, table_inputs x ⟨114, by decide⟩, table_lookup_283]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_156 (x : Fin 128 → Bool) :
    (gates.getD 156 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 156 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 284 := by
  have h : gates.getD 156 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [283, 115]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_283, table_inputs x ⟨115, by decide⟩, table_lookup_284]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_157 (x : Fin 128 → Bool) :
    (gates.getD 157 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 157 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 285 := by
  have h : gates.getD 157 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [284, 116]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_284, table_inputs x ⟨116, by decide⟩, table_lookup_285]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_158 (x : Fin 128 → Bool) :
    (gates.getD 158 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 158 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 286 := by
  have h : gates.getD 158 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [285, 117]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_285, table_inputs x ⟨117, by decide⟩, table_lookup_286]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_159 (x : Fin 128 → Bool) :
    (gates.getD 159 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 159 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 287 := by
  have h : gates.getD 159 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [286, 118]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_286, table_inputs x ⟨118, by decide⟩, table_lookup_287]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_160 (x : Fin 128 → Bool) :
    (gates.getD 160 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 160 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 288 := by
  have h : gates.getD 160 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [287, 119]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_287, table_inputs x ⟨119, by decide⟩, table_lookup_288]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_161 (x : Fin 128 → Bool) :
    (gates.getD 161 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 161 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 289 := by
  have h : gates.getD 161 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [120, 121]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨120, by decide⟩, table_inputs x ⟨121, by decide⟩, table_lookup_289]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_162 (x : Fin 128 → Bool) :
    (gates.getD 162 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 162 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 290 := by
  have h : gates.getD 162 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [289, 122]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_289, table_inputs x ⟨122, by decide⟩, table_lookup_290]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_163 (x : Fin 128 → Bool) :
    (gates.getD 163 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 163 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 291 := by
  have h : gates.getD 163 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [290, 123]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_290, table_inputs x ⟨123, by decide⟩, table_lookup_291]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_164 (x : Fin 128 → Bool) :
    (gates.getD 164 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 164 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 292 := by
  have h : gates.getD 164 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [291, 124]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_291, table_inputs x ⟨124, by decide⟩, table_lookup_292]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_165 (x : Fin 128 → Bool) :
    (gates.getD 165 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 165 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 293 := by
  have h : gates.getD 165 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [292, 125]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_292, table_inputs x ⟨125, by decide⟩, table_lookup_293]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_166 (x : Fin 128 → Bool) :
    (gates.getD 166 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 166 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 294 := by
  have h : gates.getD 166 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [293, 126]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_293, table_inputs x ⟨126, by decide⟩, table_lookup_294]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_167 (x : Fin 128 → Bool) :
    (gates.getD 167 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 167 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 295 := by
  have h : gates.getD 167 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [294, 127]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_294, table_inputs x ⟨127, by decide⟩, table_lookup_295]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_168 (x : Fin 128 → Bool) :
    (gates.getD 168 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 168 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 296 := by
  have h : gates.getD 168 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [64, 72]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨64, by decide⟩, table_inputs x ⟨72, by decide⟩, table_lookup_296]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_169 (x : Fin 128 → Bool) :
    (gates.getD 169 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 169 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 297 := by
  have h : gates.getD 169 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [296, 80]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_296, table_inputs x ⟨80, by decide⟩, table_lookup_297]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_170 (x : Fin 128 → Bool) :
    (gates.getD 170 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 170 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 298 := by
  have h : gates.getD 170 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [297, 88]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_297, table_inputs x ⟨88, by decide⟩, table_lookup_298]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_171 (x : Fin 128 → Bool) :
    (gates.getD 171 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 171 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 299 := by
  have h : gates.getD 171 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [298, 96]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_298, table_inputs x ⟨96, by decide⟩, table_lookup_299]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_172 (x : Fin 128 → Bool) :
    (gates.getD 172 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 172 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 300 := by
  have h : gates.getD 172 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [299, 104]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_299, table_inputs x ⟨104, by decide⟩, table_lookup_300]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_173 (x : Fin 128 → Bool) :
    (gates.getD 173 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 173 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 301 := by
  have h : gates.getD 173 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [300, 112]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_300, table_inputs x ⟨112, by decide⟩, table_lookup_301]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_174 (x : Fin 128 → Bool) :
    (gates.getD 174 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 174 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 302 := by
  have h : gates.getD 174 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [301, 120]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_301, table_inputs x ⟨120, by decide⟩, table_lookup_302]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_175 (x : Fin 128 → Bool) :
    (gates.getD 175 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 175 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 303 := by
  have h : gates.getD 175 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [65, 73]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨65, by decide⟩, table_inputs x ⟨73, by decide⟩, table_lookup_303]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_176 (x : Fin 128 → Bool) :
    (gates.getD 176 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 176 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 304 := by
  have h : gates.getD 176 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [303, 81]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_303, table_inputs x ⟨81, by decide⟩, table_lookup_304]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_177 (x : Fin 128 → Bool) :
    (gates.getD 177 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 177 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 305 := by
  have h : gates.getD 177 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [304, 89]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_304, table_inputs x ⟨89, by decide⟩, table_lookup_305]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_178 (x : Fin 128 → Bool) :
    (gates.getD 178 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 178 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 306 := by
  have h : gates.getD 178 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [305, 97]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_305, table_inputs x ⟨97, by decide⟩, table_lookup_306]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_179 (x : Fin 128 → Bool) :
    (gates.getD 179 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 179 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 307 := by
  have h : gates.getD 179 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [306, 105]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_306, table_inputs x ⟨105, by decide⟩, table_lookup_307]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_180 (x : Fin 128 → Bool) :
    (gates.getD 180 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 180 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 308 := by
  have h : gates.getD 180 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [307, 113]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_307, table_inputs x ⟨113, by decide⟩, table_lookup_308]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_181 (x : Fin 128 → Bool) :
    (gates.getD 181 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 181 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 309 := by
  have h : gates.getD 181 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [308, 121]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_308, table_inputs x ⟨121, by decide⟩, table_lookup_309]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_182 (x : Fin 128 → Bool) :
    (gates.getD 182 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 182 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 310 := by
  have h : gates.getD 182 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [66, 74]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨66, by decide⟩, table_inputs x ⟨74, by decide⟩, table_lookup_310]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_183 (x : Fin 128 → Bool) :
    (gates.getD 183 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 183 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 311 := by
  have h : gates.getD 183 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [310, 82]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_310, table_inputs x ⟨82, by decide⟩, table_lookup_311]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_184 (x : Fin 128 → Bool) :
    (gates.getD 184 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 184 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 312 := by
  have h : gates.getD 184 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [311, 90]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_311, table_inputs x ⟨90, by decide⟩, table_lookup_312]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_185 (x : Fin 128 → Bool) :
    (gates.getD 185 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 185 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 313 := by
  have h : gates.getD 185 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [312, 98]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_312, table_inputs x ⟨98, by decide⟩, table_lookup_313]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_186 (x : Fin 128 → Bool) :
    (gates.getD 186 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 186 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 314 := by
  have h : gates.getD 186 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [313, 106]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_313, table_inputs x ⟨106, by decide⟩, table_lookup_314]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_187 (x : Fin 128 → Bool) :
    (gates.getD 187 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 187 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 315 := by
  have h : gates.getD 187 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [314, 114]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_314, table_inputs x ⟨114, by decide⟩, table_lookup_315]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_188 (x : Fin 128 → Bool) :
    (gates.getD 188 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 188 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 316 := by
  have h : gates.getD 188 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [315, 122]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_315, table_inputs x ⟨122, by decide⟩, table_lookup_316]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_189 (x : Fin 128 → Bool) :
    (gates.getD 189 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 189 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 317 := by
  have h : gates.getD 189 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [67, 75]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨67, by decide⟩, table_inputs x ⟨75, by decide⟩, table_lookup_317]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_190 (x : Fin 128 → Bool) :
    (gates.getD 190 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 190 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 318 := by
  have h : gates.getD 190 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [317, 83]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_317, table_inputs x ⟨83, by decide⟩, table_lookup_318]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_191 (x : Fin 128 → Bool) :
    (gates.getD 191 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 191 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 319 := by
  have h : gates.getD 191 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [318, 91]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_318, table_inputs x ⟨91, by decide⟩, table_lookup_319]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_192 (x : Fin 128 → Bool) :
    (gates.getD 192 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 192 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 320 := by
  have h : gates.getD 192 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [319, 99]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_319, table_inputs x ⟨99, by decide⟩, table_lookup_320]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_193 (x : Fin 128 → Bool) :
    (gates.getD 193 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 193 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 321 := by
  have h : gates.getD 193 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [320, 107]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_320, table_inputs x ⟨107, by decide⟩, table_lookup_321]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_194 (x : Fin 128 → Bool) :
    (gates.getD 194 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 194 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 322 := by
  have h : gates.getD 194 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [321, 115]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_321, table_inputs x ⟨115, by decide⟩, table_lookup_322]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_195 (x : Fin 128 → Bool) :
    (gates.getD 195 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 195 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 323 := by
  have h : gates.getD 195 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [322, 123]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_322, table_inputs x ⟨123, by decide⟩, table_lookup_323]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_196 (x : Fin 128 → Bool) :
    (gates.getD 196 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 196 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 324 := by
  have h : gates.getD 196 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [68, 76]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨68, by decide⟩, table_inputs x ⟨76, by decide⟩, table_lookup_324]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_197 (x : Fin 128 → Bool) :
    (gates.getD 197 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 197 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 325 := by
  have h : gates.getD 197 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [324, 84]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_324, table_inputs x ⟨84, by decide⟩, table_lookup_325]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_198 (x : Fin 128 → Bool) :
    (gates.getD 198 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 198 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 326 := by
  have h : gates.getD 198 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [325, 92]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_325, table_inputs x ⟨92, by decide⟩, table_lookup_326]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_199 (x : Fin 128 → Bool) :
    (gates.getD 199 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 199 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 327 := by
  have h : gates.getD 199 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [326, 100]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_326, table_inputs x ⟨100, by decide⟩, table_lookup_327]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_200 (x : Fin 128 → Bool) :
    (gates.getD 200 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 200 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 328 := by
  have h : gates.getD 200 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [327, 108]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_327, table_inputs x ⟨108, by decide⟩, table_lookup_328]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_201 (x : Fin 128 → Bool) :
    (gates.getD 201 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 201 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 329 := by
  have h : gates.getD 201 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [328, 116]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_328, table_inputs x ⟨116, by decide⟩, table_lookup_329]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_202 (x : Fin 128 → Bool) :
    (gates.getD 202 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 202 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 330 := by
  have h : gates.getD 202 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [329, 124]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_329, table_inputs x ⟨124, by decide⟩, table_lookup_330]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_203 (x : Fin 128 → Bool) :
    (gates.getD 203 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 203 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 331 := by
  have h : gates.getD 203 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [69, 77]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨69, by decide⟩, table_inputs x ⟨77, by decide⟩, table_lookup_331]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_204 (x : Fin 128 → Bool) :
    (gates.getD 204 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 204 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 332 := by
  have h : gates.getD 204 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [331, 85]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_331, table_inputs x ⟨85, by decide⟩, table_lookup_332]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_205 (x : Fin 128 → Bool) :
    (gates.getD 205 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 205 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 333 := by
  have h : gates.getD 205 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [332, 93]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_332, table_inputs x ⟨93, by decide⟩, table_lookup_333]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_206 (x : Fin 128 → Bool) :
    (gates.getD 206 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 206 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 334 := by
  have h : gates.getD 206 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [333, 101]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_333, table_inputs x ⟨101, by decide⟩, table_lookup_334]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_207 (x : Fin 128 → Bool) :
    (gates.getD 207 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 207 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 335 := by
  have h : gates.getD 207 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [334, 109]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_334, table_inputs x ⟨109, by decide⟩, table_lookup_335]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_208 (x : Fin 128 → Bool) :
    (gates.getD 208 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 208 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 336 := by
  have h : gates.getD 208 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [335, 117]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_335, table_inputs x ⟨117, by decide⟩, table_lookup_336]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_209 (x : Fin 128 → Bool) :
    (gates.getD 209 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 209 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 337 := by
  have h : gates.getD 209 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [336, 125]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_336, table_inputs x ⟨125, by decide⟩, table_lookup_337]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_210 (x : Fin 128 → Bool) :
    (gates.getD 210 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 210 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 338 := by
  have h : gates.getD 210 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [70, 78]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨70, by decide⟩, table_inputs x ⟨78, by decide⟩, table_lookup_338]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_211 (x : Fin 128 → Bool) :
    (gates.getD 211 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 211 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 339 := by
  have h : gates.getD 211 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [338, 86]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_338, table_inputs x ⟨86, by decide⟩, table_lookup_339]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_212 (x : Fin 128 → Bool) :
    (gates.getD 212 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 212 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 340 := by
  have h : gates.getD 212 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [339, 94]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_339, table_inputs x ⟨94, by decide⟩, table_lookup_340]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_213 (x : Fin 128 → Bool) :
    (gates.getD 213 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 213 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 341 := by
  have h : gates.getD 213 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [340, 102]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_340, table_inputs x ⟨102, by decide⟩, table_lookup_341]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_214 (x : Fin 128 → Bool) :
    (gates.getD 214 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 214 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 342 := by
  have h : gates.getD 214 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [341, 110]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_341, table_inputs x ⟨110, by decide⟩, table_lookup_342]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_215 (x : Fin 128 → Bool) :
    (gates.getD 215 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 215 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 343 := by
  have h : gates.getD 215 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [342, 118]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_342, table_inputs x ⟨118, by decide⟩, table_lookup_343]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_216 (x : Fin 128 → Bool) :
    (gates.getD 216 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 216 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 344 := by
  have h : gates.getD 216 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [343, 126]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_343, table_inputs x ⟨126, by decide⟩, table_lookup_344]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_217 (x : Fin 128 → Bool) :
    (gates.getD 217 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 217 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 345 := by
  have h : gates.getD 217 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [71, 79]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_inputs x ⟨71, by decide⟩, table_inputs x ⟨79, by decide⟩, table_lookup_345]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_218 (x : Fin 128 → Bool) :
    (gates.getD 218 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 218 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 346 := by
  have h : gates.getD 218 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [345, 87]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_345, table_inputs x ⟨87, by decide⟩, table_lookup_346]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_219 (x : Fin 128 → Bool) :
    (gates.getD 219 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 219 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 347 := by
  have h : gates.getD 219 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [346, 95]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_346, table_inputs x ⟨95, by decide⟩, table_lookup_347]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_220 (x : Fin 128 → Bool) :
    (gates.getD 220 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 220 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 348 := by
  have h : gates.getD 220 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [347, 103]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_347, table_inputs x ⟨103, by decide⟩, table_lookup_348]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_221 (x : Fin 128 → Bool) :
    (gates.getD 221 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 221 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 349 := by
  have h : gates.getD 221 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [348, 111]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_348, table_inputs x ⟨111, by decide⟩, table_lookup_349]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_222 (x : Fin 128 → Bool) :
    (gates.getD 222 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 222 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 350 := by
  have h : gates.getD 222 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [349, 119]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_349, table_inputs x ⟨119, by decide⟩, table_lookup_350]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_223 (x : Fin 128 → Bool) :
    (gates.getD 223 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 223 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 351 := by
  have h : gates.getD 223 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [350, 127]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_350, table_inputs x ⟨127, by decide⟩, table_lookup_351]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_224 (x : Fin 128 → Bool) :
    (gates.getD 224 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 224 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 352 := by
  have h : gates.getD 224 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [134, 148]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_134, table_lookup_148, table_lookup_352]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_225 (x : Fin 128 → Bool) :
    (gates.getD 225 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 225 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 353 := by
  have h : gates.getD 225 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [352, 162]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_352, table_lookup_162, table_lookup_353]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_226 (x : Fin 128 → Bool) :
    (gates.getD 226 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 226 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 354 := by
  have h : gates.getD 226 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [353, 176]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_353, table_lookup_176, table_lookup_354]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_227 (x : Fin 128 → Bool) :
    (gates.getD 227 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 227 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 355 := by
  have h : gates.getD 227 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [141, 155]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_141, table_lookup_155, table_lookup_355]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_228 (x : Fin 128 → Bool) :
    (gates.getD 228 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 228 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 356 := by
  have h : gates.getD 228 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [355, 169]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_355, table_lookup_169, table_lookup_356]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_229 (x : Fin 128 → Bool) :
    (gates.getD 229 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 229 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 357 := by
  have h : gates.getD 229 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [356, 183]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_356, table_lookup_183, table_lookup_357]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_230 (x : Fin 128 → Bool) :
    (gates.getD 230 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 230 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 358 := by
  have h : gates.getD 230 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [134, 141]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_134, table_lookup_141, table_lookup_358]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_231 (x : Fin 128 → Bool) :
    (gates.getD 231 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 231 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 359 := by
  have h : gates.getD 231 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [358, 162]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_358, table_lookup_162, table_lookup_359]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_232 (x : Fin 128 → Bool) :
    (gates.getD 232 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 232 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 360 := by
  have h : gates.getD 232 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [359, 169]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_359, table_lookup_169, table_lookup_360]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_233 (x : Fin 128 → Bool) :
    (gates.getD 233 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 233 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 361 := by
  have h : gates.getD 233 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [148, 155]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_148, table_lookup_155, table_lookup_361]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_234 (x : Fin 128 → Bool) :
    (gates.getD 234 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 234 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 362 := by
  have h : gates.getD 234 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [361, 176]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_361, table_lookup_176, table_lookup_362]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_235 (x : Fin 128 → Bool) :
    (gates.getD 235 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 235 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 363 := by
  have h : gates.getD 235 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [362, 183]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_362, table_lookup_183, table_lookup_363]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_236 (x : Fin 128 → Bool) :
    (gates.getD 236 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 236 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 364 := by
  have h : gates.getD 236 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [134, 141]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_134, table_lookup_141, table_lookup_364]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_237 (x : Fin 128 → Bool) :
    (gates.getD 237 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 237 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 365 := by
  have h : gates.getD 237 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [364, 148]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_364, table_lookup_148, table_lookup_365]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_238 (x : Fin 128 → Bool) :
    (gates.getD 238 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 238 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 366 := by
  have h : gates.getD 238 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [365, 155]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_365, table_lookup_155, table_lookup_366]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_239 (x : Fin 128 → Bool) :
    (gates.getD 239 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 239 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 367 := by
  have h : gates.getD 239 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [162, 169]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_162, table_lookup_169, table_lookup_367]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_240 (x : Fin 128 → Bool) :
    (gates.getD 240 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 240 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 368 := by
  have h : gates.getD 240 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [367, 176]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_367, table_lookup_176, table_lookup_368]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_241 (x : Fin 128 → Bool) :
    (gates.getD 241 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 241 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 369 := by
  have h : gates.getD 241 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [368, 183]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_368, table_lookup_183, table_lookup_369]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_242 (x : Fin 128 → Bool) :
    (gates.getD 242 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 242 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 370 := by
  have h : gates.getD 242 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [190, 204]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_190, table_lookup_204, table_lookup_370]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_243 (x : Fin 128 → Bool) :
    (gates.getD 243 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 243 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 371 := by
  have h : gates.getD 243 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [370, 218]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_370, table_lookup_218, table_lookup_371]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_244 (x : Fin 128 → Bool) :
    (gates.getD 244 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 244 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 372 := by
  have h : gates.getD 244 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [371, 232]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_371, table_lookup_232, table_lookup_372]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_245 (x : Fin 128 → Bool) :
    (gates.getD 245 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 245 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 373 := by
  have h : gates.getD 245 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [197, 211]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_197, table_lookup_211, table_lookup_373]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_246 (x : Fin 128 → Bool) :
    (gates.getD 246 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 246 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 374 := by
  have h : gates.getD 246 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [373, 225]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_373, table_lookup_225, table_lookup_374]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_247 (x : Fin 128 → Bool) :
    (gates.getD 247 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 247 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 375 := by
  have h : gates.getD 247 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [374, 239]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_374, table_lookup_239, table_lookup_375]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_248 (x : Fin 128 → Bool) :
    (gates.getD 248 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 248 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 376 := by
  have h : gates.getD 248 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [190, 197]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_190, table_lookup_197, table_lookup_376]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_249 (x : Fin 128 → Bool) :
    (gates.getD 249 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 249 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 377 := by
  have h : gates.getD 249 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [376, 218]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_376, table_lookup_218, table_lookup_377]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_250 (x : Fin 128 → Bool) :
    (gates.getD 250 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 250 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 378 := by
  have h : gates.getD 250 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [377, 225]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_377, table_lookup_225, table_lookup_378]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_251 (x : Fin 128 → Bool) :
    (gates.getD 251 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 251 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 379 := by
  have h : gates.getD 251 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [204, 211]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_204, table_lookup_211, table_lookup_379]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_252 (x : Fin 128 → Bool) :
    (gates.getD 252 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 252 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 380 := by
  have h : gates.getD 252 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [379, 232]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_379, table_lookup_232, table_lookup_380]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_253 (x : Fin 128 → Bool) :
    (gates.getD 253 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 253 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 381 := by
  have h : gates.getD 253 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [380, 239]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_380, table_lookup_239, table_lookup_381]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_254 (x : Fin 128 → Bool) :
    (gates.getD 254 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 254 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 382 := by
  have h : gates.getD 254 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [190, 197]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_190, table_lookup_197, table_lookup_382]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_255 (x : Fin 128 → Bool) :
    (gates.getD 255 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 255 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 383 := by
  have h : gates.getD 255 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [382, 204]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_382, table_lookup_204, table_lookup_383]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_256 (x : Fin 128 → Bool) :
    (gates.getD 256 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 256 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 384 := by
  have h : gates.getD 256 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [383, 211]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_383, table_lookup_211, table_lookup_384]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_257 (x : Fin 128 → Bool) :
    (gates.getD 257 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 257 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 385 := by
  have h : gates.getD 257 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [218, 225]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_218, table_lookup_225, table_lookup_385]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_258 (x : Fin 128 → Bool) :
    (gates.getD 258 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 258 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 386 := by
  have h : gates.getD 258 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [385, 232]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_385, table_lookup_232, table_lookup_386]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_259 (x : Fin 128 → Bool) :
    (gates.getD 259 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 259 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 387 := by
  have h : gates.getD 259 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [386, 239]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_386, table_lookup_239, table_lookup_387]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_260 (x : Fin 128 → Bool) :
    (gates.getD 260 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 260 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 388 := by
  have h : gates.getD 260 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [246, 260]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_246, table_lookup_260, table_lookup_388]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_261 (x : Fin 128 → Bool) :
    (gates.getD 261 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 261 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 389 := by
  have h : gates.getD 261 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [388, 274]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_388, table_lookup_274, table_lookup_389]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_262 (x : Fin 128 → Bool) :
    (gates.getD 262 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 262 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 390 := by
  have h : gates.getD 262 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [389, 288]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_389, table_lookup_288, table_lookup_390]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_263 (x : Fin 128 → Bool) :
    (gates.getD 263 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 263 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 391 := by
  have h : gates.getD 263 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [253, 267]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_253, table_lookup_267, table_lookup_391]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_264 (x : Fin 128 → Bool) :
    (gates.getD 264 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 264 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 392 := by
  have h : gates.getD 264 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [391, 281]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_391, table_lookup_281, table_lookup_392]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_265 (x : Fin 128 → Bool) :
    (gates.getD 265 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 265 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 393 := by
  have h : gates.getD 265 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [392, 295]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_392, table_lookup_295, table_lookup_393]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_266 (x : Fin 128 → Bool) :
    (gates.getD 266 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 266 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 394 := by
  have h : gates.getD 266 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [246, 253]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_246, table_lookup_253, table_lookup_394]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_267 (x : Fin 128 → Bool) :
    (gates.getD 267 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 267 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 395 := by
  have h : gates.getD 267 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [394, 274]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_394, table_lookup_274, table_lookup_395]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_268 (x : Fin 128 → Bool) :
    (gates.getD 268 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 268 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 396 := by
  have h : gates.getD 268 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [395, 281]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_395, table_lookup_281, table_lookup_396]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_269 (x : Fin 128 → Bool) :
    (gates.getD 269 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 269 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 397 := by
  have h : gates.getD 269 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [260, 267]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_260, table_lookup_267, table_lookup_397]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_270 (x : Fin 128 → Bool) :
    (gates.getD 270 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 270 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 398 := by
  have h : gates.getD 270 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [397, 288]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_397, table_lookup_288, table_lookup_398]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_271 (x : Fin 128 → Bool) :
    (gates.getD 271 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 271 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 399 := by
  have h : gates.getD 271 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [398, 295]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_398, table_lookup_295, table_lookup_399]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_272 (x : Fin 128 → Bool) :
    (gates.getD 272 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 272 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 400 := by
  have h : gates.getD 272 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [246, 253]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_246, table_lookup_253, table_lookup_400]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_273 (x : Fin 128 → Bool) :
    (gates.getD 273 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 273 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 401 := by
  have h : gates.getD 273 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [400, 260]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_400, table_lookup_260, table_lookup_401]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_274 (x : Fin 128 → Bool) :
    (gates.getD 274 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 274 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 402 := by
  have h : gates.getD 274 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [401, 267]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_401, table_lookup_267, table_lookup_402]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_275 (x : Fin 128 → Bool) :
    (gates.getD 275 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 275 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 403 := by
  have h : gates.getD 275 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [274, 281]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_274, table_lookup_281, table_lookup_403]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_276 (x : Fin 128 → Bool) :
    (gates.getD 276 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 276 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 404 := by
  have h : gates.getD 276 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [403, 288]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_403, table_lookup_288, table_lookup_404]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_277 (x : Fin 128 → Bool) :
    (gates.getD 277 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 277 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 405 := by
  have h : gates.getD 277 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [404, 295]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_404, table_lookup_295, table_lookup_405]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_278 (x : Fin 128 → Bool) :
    (gates.getD 278 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 278 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 406 := by
  have h : gates.getD 278 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [302, 316]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_302, table_lookup_316, table_lookup_406]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_279 (x : Fin 128 → Bool) :
    (gates.getD 279 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 279 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 407 := by
  have h : gates.getD 279 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [406, 330]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_406, table_lookup_330, table_lookup_407]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_280 (x : Fin 128 → Bool) :
    (gates.getD 280 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 280 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 408 := by
  have h : gates.getD 280 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [407, 344]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_407, table_lookup_344, table_lookup_408]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_281 (x : Fin 128 → Bool) :
    (gates.getD 281 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 281 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 409 := by
  have h : gates.getD 281 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [309, 323]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_309, table_lookup_323, table_lookup_409]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_282 (x : Fin 128 → Bool) :
    (gates.getD 282 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 282 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 410 := by
  have h : gates.getD 282 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [409, 337]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_409, table_lookup_337, table_lookup_410]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_283 (x : Fin 128 → Bool) :
    (gates.getD 283 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 283 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 411 := by
  have h : gates.getD 283 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [410, 351]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_410, table_lookup_351, table_lookup_411]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_284 (x : Fin 128 → Bool) :
    (gates.getD 284 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 284 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 412 := by
  have h : gates.getD 284 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [302, 309]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_302, table_lookup_309, table_lookup_412]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_285 (x : Fin 128 → Bool) :
    (gates.getD 285 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 285 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 413 := by
  have h : gates.getD 285 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [412, 330]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_412, table_lookup_330, table_lookup_413]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_286 (x : Fin 128 → Bool) :
    (gates.getD 286 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 286 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 414 := by
  have h : gates.getD 286 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [413, 337]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_413, table_lookup_337, table_lookup_414]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_287 (x : Fin 128 → Bool) :
    (gates.getD 287 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 287 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 415 := by
  have h : gates.getD 287 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [316, 323]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_316, table_lookup_323, table_lookup_415]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_288 (x : Fin 128 → Bool) :
    (gates.getD 288 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 288 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 416 := by
  have h : gates.getD 288 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [415, 344]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_415, table_lookup_344, table_lookup_416]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_289 (x : Fin 128 → Bool) :
    (gates.getD 289 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 289 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 417 := by
  have h : gates.getD 289 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [416, 351]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_416, table_lookup_351, table_lookup_417]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_290 (x : Fin 128 → Bool) :
    (gates.getD 290 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 290 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 418 := by
  have h : gates.getD 290 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [302, 309]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_302, table_lookup_309, table_lookup_418]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_291 (x : Fin 128 → Bool) :
    (gates.getD 291 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 291 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 419 := by
  have h : gates.getD 291 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [418, 316]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_418, table_lookup_316, table_lookup_419]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_292 (x : Fin 128 → Bool) :
    (gates.getD 292 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 292 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 420 := by
  have h : gates.getD 292 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [419, 323]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_419, table_lookup_323, table_lookup_420]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_293 (x : Fin 128 → Bool) :
    (gates.getD 293 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 293 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 421 := by
  have h : gates.getD 293 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [330, 337]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_330, table_lookup_337, table_lookup_421]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_294 (x : Fin 128 → Bool) :
    (gates.getD 294 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 294 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 422 := by
  have h : gates.getD 294 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [421, 344]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_421, table_lookup_344, table_lookup_422]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_295 (x : Fin 128 → Bool) :
    (gates.getD 295 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 295 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 423 := by
  have h : gates.getD 295 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [422, 351]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_422, table_lookup_351, table_lookup_423]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_296 (x : Fin 128 → Bool) :
    (gates.getD 296 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 296 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 424 := by
  have h : gates.getD 296 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [390, 354]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_390, table_lookup_354, table_lookup_424]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_297 (x : Fin 128 → Bool) :
    (gates.getD 297 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 297 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 425 := by
  have h : gates.getD 297 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [393, 357]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_393, table_lookup_357, table_lookup_425]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_298 (x : Fin 128 → Bool) :
    (gates.getD 298 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 298 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 426 := by
  have h : gates.getD 298 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [390, 360]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_390, table_lookup_360, table_lookup_426]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_299 (x : Fin 128 → Bool) :
    (gates.getD 299 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 299 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 427 := by
  have h : gates.getD 299 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [393, 363]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_393, table_lookup_363, table_lookup_427]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_300 (x : Fin 128 → Bool) :
    (gates.getD 300 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 300 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 428 := by
  have h : gates.getD 300 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [390, 366]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_390, table_lookup_366, table_lookup_428]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_301 (x : Fin 128 → Bool) :
    (gates.getD 301 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 301 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 429 := by
  have h : gates.getD 301 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [393, 369]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_393, table_lookup_369, table_lookup_429]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_302 (x : Fin 128 → Bool) :
    (gates.getD 302 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 302 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 430 := by
  have h : gates.getD 302 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [396, 354]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_396, table_lookup_354, table_lookup_430]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_303 (x : Fin 128 → Bool) :
    (gates.getD 303 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 303 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 431 := by
  have h : gates.getD 303 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [399, 357]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_399, table_lookup_357, table_lookup_431]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_304 (x : Fin 128 → Bool) :
    (gates.getD 304 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 304 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 432 := by
  have h : gates.getD 304 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [396, 360]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_396, table_lookup_360, table_lookup_432]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_305 (x : Fin 128 → Bool) :
    (gates.getD 305 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 305 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 433 := by
  have h : gates.getD 305 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [399, 363]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_399, table_lookup_363, table_lookup_433]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_306 (x : Fin 128 → Bool) :
    (gates.getD 306 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 306 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 434 := by
  have h : gates.getD 306 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [396, 366]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_396, table_lookup_366, table_lookup_434]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_307 (x : Fin 128 → Bool) :
    (gates.getD 307 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 307 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 435 := by
  have h : gates.getD 307 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [399, 369]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_399, table_lookup_369, table_lookup_435]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_308 (x : Fin 128 → Bool) :
    (gates.getD 308 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 308 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 436 := by
  have h : gates.getD 308 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [402, 354]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_402, table_lookup_354, table_lookup_436]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_309 (x : Fin 128 → Bool) :
    (gates.getD 309 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 309 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 437 := by
  have h : gates.getD 309 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [405, 357]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_405, table_lookup_357, table_lookup_437]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_310 (x : Fin 128 → Bool) :
    (gates.getD 310 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 310 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 438 := by
  have h : gates.getD 310 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [402, 360]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_402, table_lookup_360, table_lookup_438]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_311 (x : Fin 128 → Bool) :
    (gates.getD 311 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 311 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 439 := by
  have h : gates.getD 311 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [405, 363]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_405, table_lookup_363, table_lookup_439]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_312 (x : Fin 128 → Bool) :
    (gates.getD 312 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 312 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 440 := by
  have h : gates.getD 312 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [402, 366]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_402, table_lookup_366, table_lookup_440]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_313 (x : Fin 128 → Bool) :
    (gates.getD 313 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 313 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 441 := by
  have h : gates.getD 313 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [405, 369]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_405, table_lookup_369, table_lookup_441]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_314 (x : Fin 128 → Bool) :
    (gates.getD 314 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 314 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 442 := by
  have h : gates.getD 314 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [426, 430]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_426, table_lookup_430, table_lookup_442]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_315 (x : Fin 128 → Bool) :
    (gates.getD 315 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 315 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 443 := by
  have h : gates.getD 315 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [427, 431]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_427, table_lookup_431, table_lookup_443]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_316 (x : Fin 128 → Bool) :
    (gates.getD 316 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 316 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 444 := by
  have h : gates.getD 316 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [442, 443]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_442, table_lookup_443, table_lookup_444]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_317 (x : Fin 128 → Bool) :
    (gates.getD 317 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 317 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 445 := by
  have h : gates.getD 317 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [426, 431]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_426, table_lookup_431, table_lookup_445]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_318 (x : Fin 128 → Bool) :
    (gates.getD 318 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 318 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 446 := by
  have h : gates.getD 318 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [427, 430]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_427, table_lookup_430, table_lookup_446]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_319 (x : Fin 128 → Bool) :
    (gates.getD 319 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 319 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 447 := by
  have h : gates.getD 319 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [445, 446]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_445, table_lookup_446, table_lookup_447]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_320 (x : Fin 128 → Bool) :
    (gates.getD 320 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 320 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 448 := by
  have h : gates.getD 320 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [428, 432]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_428, table_lookup_432, table_lookup_448]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_321 (x : Fin 128 → Bool) :
    (gates.getD 321 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 321 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 449 := by
  have h : gates.getD 321 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [429, 433]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_429, table_lookup_433, table_lookup_449]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_322 (x : Fin 128 → Bool) :
    (gates.getD 322 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 322 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 450 := by
  have h : gates.getD 322 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [448, 449]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_448, table_lookup_449, table_lookup_450]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_323 (x : Fin 128 → Bool) :
    (gates.getD 323 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 323 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 451 := by
  have h : gates.getD 323 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [428, 433]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_428, table_lookup_433, table_lookup_451]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_324 (x : Fin 128 → Bool) :
    (gates.getD 324 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 324 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 452 := by
  have h : gates.getD 324 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [429, 432]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_429, table_lookup_432, table_lookup_452]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_325 (x : Fin 128 → Bool) :
    (gates.getD 325 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 325 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 453 := by
  have h : gates.getD 325 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [451, 452]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_451, table_lookup_452, table_lookup_453]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_326 (x : Fin 128 → Bool) :
    (gates.getD 326 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 326 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 454 := by
  have h : gates.getD 326 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [450, 436]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_450, table_lookup_436, table_lookup_454]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_327 (x : Fin 128 → Bool) :
    (gates.getD 327 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 327 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 455 := by
  have h : gates.getD 327 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [453, 437]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_453, table_lookup_437, table_lookup_455]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_328 (x : Fin 128 → Bool) :
    (gates.getD 328 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 328 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 456 := by
  have h : gates.getD 328 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [454, 455]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_454, table_lookup_455, table_lookup_456]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_329 (x : Fin 128 → Bool) :
    (gates.getD 329 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 329 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 457 := by
  have h : gates.getD 329 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [450, 437]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_450, table_lookup_437, table_lookup_457]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_330 (x : Fin 128 → Bool) :
    (gates.getD 330 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 330 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 458 := by
  have h : gates.getD 330 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [453, 436]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_453, table_lookup_436, table_lookup_458]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_331 (x : Fin 128 → Bool) :
    (gates.getD 331 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 331 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 459 := by
  have h : gates.getD 331 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [457, 458]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_457, table_lookup_458, table_lookup_459]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_332 (x : Fin 128 → Bool) :
    (gates.getD 332 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 332 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 460 := by
  have h : gates.getD 332 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [434, 438]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_434, table_lookup_438, table_lookup_460]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_333 (x : Fin 128 → Bool) :
    (gates.getD 333 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 333 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 461 := by
  have h : gates.getD 333 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [435, 439]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_435, table_lookup_439, table_lookup_461]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_334 (x : Fin 128 → Bool) :
    (gates.getD 334 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 334 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 462 := by
  have h : gates.getD 334 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [460, 461]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_460, table_lookup_461, table_lookup_462]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_335 (x : Fin 128 → Bool) :
    (gates.getD 335 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 335 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 463 := by
  have h : gates.getD 335 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [434, 439]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_434, table_lookup_439, table_lookup_463]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_336 (x : Fin 128 → Bool) :
    (gates.getD 336 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 336 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 464 := by
  have h : gates.getD 336 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [435, 438]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_435, table_lookup_438, table_lookup_464]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_337 (x : Fin 128 → Bool) :
    (gates.getD 337 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 337 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 465 := by
  have h : gates.getD 337 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [463, 464]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_463, table_lookup_464, table_lookup_465]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_338 (x : Fin 128 → Bool) :
    (gates.getD 338 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 338 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 466 := by
  have h : gates.getD 338 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [424, 462]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_424, table_lookup_462, table_lookup_466]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_339 (x : Fin 128 → Bool) :
    (gates.getD 339 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 339 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 467 := by
  have h : gates.getD 339 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [425, 465]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_425, table_lookup_465, table_lookup_467]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_340 (x : Fin 128 → Bool) :
    (gates.getD 340 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 340 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 468 := by
  have h : gates.getD 340 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [466, 467]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_466, table_lookup_467, table_lookup_468]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_341 (x : Fin 128 → Bool) :
    (gates.getD 341 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 341 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 469 := by
  have h : gates.getD 341 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [424, 465]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_424, table_lookup_465, table_lookup_469]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_342 (x : Fin 128 → Bool) :
    (gates.getD 342 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 342 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 470 := by
  have h : gates.getD 342 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [425, 462]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_425, table_lookup_462, table_lookup_470]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_343 (x : Fin 128 → Bool) :
    (gates.getD 343 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 343 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 471 := by
  have h : gates.getD 343 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [469, 470]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_469, table_lookup_470, table_lookup_471]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_344 (x : Fin 128 → Bool) :
    (gates.getD 344 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 344 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 472 := by
  have h : gates.getD 344 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [444, 462]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_444, table_lookup_462, table_lookup_472]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_345 (x : Fin 128 → Bool) :
    (gates.getD 345 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 345 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 473 := by
  have h : gates.getD 345 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [447, 465]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_447, table_lookup_465, table_lookup_473]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_346 (x : Fin 128 → Bool) :
    (gates.getD 346 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 346 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 474 := by
  have h : gates.getD 346 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [472, 473]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_472, table_lookup_473, table_lookup_474]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_347 (x : Fin 128 → Bool) :
    (gates.getD 347 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 347 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 475 := by
  have h : gates.getD 347 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [444, 465]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_444, table_lookup_465, table_lookup_475]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_348 (x : Fin 128 → Bool) :
    (gates.getD 348 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 348 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 476 := by
  have h : gates.getD 348 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [447, 462]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_447, table_lookup_462, table_lookup_476]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_349 (x : Fin 128 → Bool) :
    (gates.getD 349 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 349 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 477 := by
  have h : gates.getD 349 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [475, 476]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_475, table_lookup_476, table_lookup_477]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_350 (x : Fin 128 → Bool) :
    (gates.getD 350 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 350 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 478 := by
  have h : gates.getD 350 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [474, 440]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_474, table_lookup_440, table_lookup_478]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_351 (x : Fin 128 → Bool) :
    (gates.getD 351 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 351 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 479 := by
  have h : gates.getD 351 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [477, 441]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_477, table_lookup_441, table_lookup_479]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_352 (x : Fin 128 → Bool) :
    (gates.getD 352 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 352 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 480 := by
  have h : gates.getD 352 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [478, 479]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_478, table_lookup_479, table_lookup_480]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_353 (x : Fin 128 → Bool) :
    (gates.getD 353 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 353 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 481 := by
  have h : gates.getD 353 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [474, 441]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_474, table_lookup_441, table_lookup_481]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_354 (x : Fin 128 → Bool) :
    (gates.getD 354 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 354 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 482 := by
  have h : gates.getD 354 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [477, 440]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_477, table_lookup_440, table_lookup_482]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_355 (x : Fin 128 → Bool) :
    (gates.getD 355 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 355 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 483 := by
  have h : gates.getD 355 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [481, 482]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_481, table_lookup_482, table_lookup_483]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_356 (x : Fin 128 → Bool) :
    (gates.getD 356 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 356 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 484 := by
  have h : gates.getD 356 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [456, 440]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_456, table_lookup_440, table_lookup_484]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_357 (x : Fin 128 → Bool) :
    (gates.getD 357 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 357 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 485 := by
  have h : gates.getD 357 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [459, 441]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_459, table_lookup_441, table_lookup_485]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_358 (x : Fin 128 → Bool) :
    (gates.getD 358 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 358 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 486 := by
  have h : gates.getD 358 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [484, 485]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_484, table_lookup_485, table_lookup_486]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_359 (x : Fin 128 → Bool) :
    (gates.getD 359 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 359 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 487 := by
  have h : gates.getD 359 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [456, 441]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_456, table_lookup_441, table_lookup_487]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_360 (x : Fin 128 → Bool) :
    (gates.getD 360 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 360 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 488 := by
  have h : gates.getD 360 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [459, 440]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_459, table_lookup_440, table_lookup_488]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_361 (x : Fin 128 → Bool) :
    (gates.getD 361 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 361 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 489 := by
  have h : gates.getD 361 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [487, 488]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_487, table_lookup_488, table_lookup_489]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_362 (x : Fin 128 → Bool) :
    (gates.getD 362 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 362 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 490 := by
  have h : gates.getD 362 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [468, 408]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_468, table_lookup_408, table_lookup_490]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_363 (x : Fin 128 → Bool) :
    (gates.getD 363 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 363 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 491 := by
  have h : gates.getD 363 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [471, 411]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_471, table_lookup_411, table_lookup_491]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_364 (x : Fin 128 → Bool) :
    (gates.getD 364 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 364 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 492 := by
  have h : gates.getD 364 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [490, 491]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_490, table_lookup_491, table_lookup_492]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_365 (x : Fin 128 → Bool) :
    (gates.getD 365 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 365 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 493 := by
  have h : gates.getD 365 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [468, 411]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_468, table_lookup_411, table_lookup_493]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_366 (x : Fin 128 → Bool) :
    (gates.getD 366 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 366 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 494 := by
  have h : gates.getD 366 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [471, 408]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_471, table_lookup_408, table_lookup_494]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_367 (x : Fin 128 → Bool) :
    (gates.getD 367 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 367 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 495 := by
  have h : gates.getD 367 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [493, 494]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_493, table_lookup_494, table_lookup_495]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_368 (x : Fin 128 → Bool) :
    (gates.getD 368 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 368 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 496 := by
  have h : gates.getD 368 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [480, 414]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_480, table_lookup_414, table_lookup_496]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_369 (x : Fin 128 → Bool) :
    (gates.getD 369 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 369 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 497 := by
  have h : gates.getD 369 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [483, 417]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_483, table_lookup_417, table_lookup_497]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_370 (x : Fin 128 → Bool) :
    (gates.getD 370 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 370 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 498 := by
  have h : gates.getD 370 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [496, 497]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_496, table_lookup_497, table_lookup_498]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_371 (x : Fin 128 → Bool) :
    (gates.getD 371 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 371 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 499 := by
  have h : gates.getD 371 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [480, 417]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_480, table_lookup_417, table_lookup_499]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_372 (x : Fin 128 → Bool) :
    (gates.getD 372 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 372 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 500 := by
  have h : gates.getD 372 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [483, 414]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_483, table_lookup_414, table_lookup_500]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_373 (x : Fin 128 → Bool) :
    (gates.getD 373 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 373 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 501 := by
  have h : gates.getD 373 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [499, 500]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_499, table_lookup_500, table_lookup_501]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_374 (x : Fin 128 → Bool) :
    (gates.getD 374 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 374 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 502 := by
  have h : gates.getD 374 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [486, 420]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_486, table_lookup_420, table_lookup_502]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_375 (x : Fin 128 → Bool) :
    (gates.getD 375 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 375 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 503 := by
  have h : gates.getD 375 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [489, 423]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_489, table_lookup_423, table_lookup_503]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_376 (x : Fin 128 → Bool) :
    (gates.getD 376 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 376 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 504 := by
  have h : gates.getD 376 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [502, 503]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_502, table_lookup_503, table_lookup_504]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_377 (x : Fin 128 → Bool) :
    (gates.getD 377 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 377 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 505 := by
  have h : gates.getD 377 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [486, 423]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_486, table_lookup_423, table_lookup_505]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_378 (x : Fin 128 → Bool) :
    (gates.getD 378 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 378 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 506 := by
  have h : gates.getD 378 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [489, 420]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_489, table_lookup_420, table_lookup_506]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_379 (x : Fin 128 → Bool) :
    (gates.getD 379 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 379 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 507 := by
  have h : gates.getD 379 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [505, 506]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_505, table_lookup_506, table_lookup_507]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_380 (x : Fin 128 → Bool) :
    (gates.getD 380 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 380 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 508 := by
  have h : gates.getD 380 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [492, 372]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_492, table_lookup_372, table_lookup_508]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_381 (x : Fin 128 → Bool) :
    (gates.getD 381 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 381 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 509 := by
  have h : gates.getD 381 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [495, 375]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_495, table_lookup_375, table_lookup_509]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_382 (x : Fin 128 → Bool) :
    (gates.getD 382 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 382 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 510 := by
  have h : gates.getD 382 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [508, 509]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_508, table_lookup_509, table_lookup_510]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_383 (x : Fin 128 → Bool) :
    (gates.getD 383 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 383 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 511 := by
  have h : gates.getD 383 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [498, 378]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_498, table_lookup_378, table_lookup_511]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_384 (x : Fin 128 → Bool) :
    (gates.getD 384 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 384 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 512 := by
  have h : gates.getD 384 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [501, 381]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_501, table_lookup_381, table_lookup_512]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_385 (x : Fin 128 → Bool) :
    (gates.getD 385 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 385 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 513 := by
  have h : gates.getD 385 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [511, 512]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_511, table_lookup_512, table_lookup_513]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_386 (x : Fin 128 → Bool) :
    (gates.getD 386 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 386 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 514 := by
  have h : gates.getD 386 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [504, 384]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_504, table_lookup_384, table_lookup_514]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_387 (x : Fin 128 → Bool) :
    (gates.getD 387 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 387 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 515 := by
  have h : gates.getD 387 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [507, 387]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_507, table_lookup_387, table_lookup_515]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_388 (x : Fin 128 → Bool) :
    (gates.getD 388 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 388 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 516 := by
  have h : gates.getD 388 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [514, 515]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_514, table_lookup_515, table_lookup_516]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_389 (x : Fin 128 → Bool) :
    (gates.getD 389 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 389 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 517 := by
  have h : gates.getD 389 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [510, 513]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_510, table_lookup_513, table_lookup_517]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_390 (x : Fin 128 → Bool) :
    (gates.getD 390 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 390 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 518 := by
  have h : gates.getD 390 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [517, 516]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_517, table_lookup_516, table_lookup_518]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_391 (x : Fin 128 → Bool) :
    (gates.getD 391 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 391 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 519 := by
  have h : gates.getD 391 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [354, 357]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_354, table_lookup_357, table_lookup_519]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_392 (x : Fin 128 → Bool) :
    (gates.getD 392 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 392 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 520 := by
  have h : gates.getD 392 ⟨GateOp.or, []⟩ = ⟨GateOp.or, [390, 393]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_390, table_lookup_393, table_lookup_520]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_393 (x : Fin 128 → Bool) :
    (gates.getD 393 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 393 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 521 := by
  have h : gates.getD 393 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [519, 520]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_519, table_lookup_520, table_lookup_521]
  rfl

set_option maxRecDepth 20000 in
lemma local_eq_394 (x : Fin 128 → Bool) :
    (gates.getD 394 ⟨GateOp.or, []⟩).op.eval
      ((gates.getD 394 ⟨GateOp.or, []⟩).inputs.map (table x)) = table x 522 := by
  have h : gates.getD 394 ⟨GateOp.or, []⟩ = ⟨GateOp.and, [521, 518]⟩ := by rfl
  rw [h]
  simp only [List.map_cons, List.map_nil]
  rw [table_lookup_521, table_lookup_518, table_lookup_522]
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma local_gate_equations (x : Fin 128 → Bool) : ∀ j : Fin 395,
    (gates.getD j.val ⟨GateOp.or, []⟩).op.eval
      ((gates.getD j.val ⟨GateOp.or, []⟩).inputs.map (table x)) = table x (128 + j.val) := by
  intro j
  fin_cases j
  · exact local_eq_0 x
  · exact local_eq_1 x
  · exact local_eq_2 x
  · exact local_eq_3 x
  · exact local_eq_4 x
  · exact local_eq_5 x
  · exact local_eq_6 x
  · exact local_eq_7 x
  · exact local_eq_8 x
  · exact local_eq_9 x
  · exact local_eq_10 x
  · exact local_eq_11 x
  · exact local_eq_12 x
  · exact local_eq_13 x
  · exact local_eq_14 x
  · exact local_eq_15 x
  · exact local_eq_16 x
  · exact local_eq_17 x
  · exact local_eq_18 x
  · exact local_eq_19 x
  · exact local_eq_20 x
  · exact local_eq_21 x
  · exact local_eq_22 x
  · exact local_eq_23 x
  · exact local_eq_24 x
  · exact local_eq_25 x
  · exact local_eq_26 x
  · exact local_eq_27 x
  · exact local_eq_28 x
  · exact local_eq_29 x
  · exact local_eq_30 x
  · exact local_eq_31 x
  · exact local_eq_32 x
  · exact local_eq_33 x
  · exact local_eq_34 x
  · exact local_eq_35 x
  · exact local_eq_36 x
  · exact local_eq_37 x
  · exact local_eq_38 x
  · exact local_eq_39 x
  · exact local_eq_40 x
  · exact local_eq_41 x
  · exact local_eq_42 x
  · exact local_eq_43 x
  · exact local_eq_44 x
  · exact local_eq_45 x
  · exact local_eq_46 x
  · exact local_eq_47 x
  · exact local_eq_48 x
  · exact local_eq_49 x
  · exact local_eq_50 x
  · exact local_eq_51 x
  · exact local_eq_52 x
  · exact local_eq_53 x
  · exact local_eq_54 x
  · exact local_eq_55 x
  · exact local_eq_56 x
  · exact local_eq_57 x
  · exact local_eq_58 x
  · exact local_eq_59 x
  · exact local_eq_60 x
  · exact local_eq_61 x
  · exact local_eq_62 x
  · exact local_eq_63 x
  · exact local_eq_64 x
  · exact local_eq_65 x
  · exact local_eq_66 x
  · exact local_eq_67 x
  · exact local_eq_68 x
  · exact local_eq_69 x
  · exact local_eq_70 x
  · exact local_eq_71 x
  · exact local_eq_72 x
  · exact local_eq_73 x
  · exact local_eq_74 x
  · exact local_eq_75 x
  · exact local_eq_76 x
  · exact local_eq_77 x
  · exact local_eq_78 x
  · exact local_eq_79 x
  · exact local_eq_80 x
  · exact local_eq_81 x
  · exact local_eq_82 x
  · exact local_eq_83 x
  · exact local_eq_84 x
  · exact local_eq_85 x
  · exact local_eq_86 x
  · exact local_eq_87 x
  · exact local_eq_88 x
  · exact local_eq_89 x
  · exact local_eq_90 x
  · exact local_eq_91 x
  · exact local_eq_92 x
  · exact local_eq_93 x
  · exact local_eq_94 x
  · exact local_eq_95 x
  · exact local_eq_96 x
  · exact local_eq_97 x
  · exact local_eq_98 x
  · exact local_eq_99 x
  · exact local_eq_100 x
  · exact local_eq_101 x
  · exact local_eq_102 x
  · exact local_eq_103 x
  · exact local_eq_104 x
  · exact local_eq_105 x
  · exact local_eq_106 x
  · exact local_eq_107 x
  · exact local_eq_108 x
  · exact local_eq_109 x
  · exact local_eq_110 x
  · exact local_eq_111 x
  · exact local_eq_112 x
  · exact local_eq_113 x
  · exact local_eq_114 x
  · exact local_eq_115 x
  · exact local_eq_116 x
  · exact local_eq_117 x
  · exact local_eq_118 x
  · exact local_eq_119 x
  · exact local_eq_120 x
  · exact local_eq_121 x
  · exact local_eq_122 x
  · exact local_eq_123 x
  · exact local_eq_124 x
  · exact local_eq_125 x
  · exact local_eq_126 x
  · exact local_eq_127 x
  · exact local_eq_128 x
  · exact local_eq_129 x
  · exact local_eq_130 x
  · exact local_eq_131 x
  · exact local_eq_132 x
  · exact local_eq_133 x
  · exact local_eq_134 x
  · exact local_eq_135 x
  · exact local_eq_136 x
  · exact local_eq_137 x
  · exact local_eq_138 x
  · exact local_eq_139 x
  · exact local_eq_140 x
  · exact local_eq_141 x
  · exact local_eq_142 x
  · exact local_eq_143 x
  · exact local_eq_144 x
  · exact local_eq_145 x
  · exact local_eq_146 x
  · exact local_eq_147 x
  · exact local_eq_148 x
  · exact local_eq_149 x
  · exact local_eq_150 x
  · exact local_eq_151 x
  · exact local_eq_152 x
  · exact local_eq_153 x
  · exact local_eq_154 x
  · exact local_eq_155 x
  · exact local_eq_156 x
  · exact local_eq_157 x
  · exact local_eq_158 x
  · exact local_eq_159 x
  · exact local_eq_160 x
  · exact local_eq_161 x
  · exact local_eq_162 x
  · exact local_eq_163 x
  · exact local_eq_164 x
  · exact local_eq_165 x
  · exact local_eq_166 x
  · exact local_eq_167 x
  · exact local_eq_168 x
  · exact local_eq_169 x
  · exact local_eq_170 x
  · exact local_eq_171 x
  · exact local_eq_172 x
  · exact local_eq_173 x
  · exact local_eq_174 x
  · exact local_eq_175 x
  · exact local_eq_176 x
  · exact local_eq_177 x
  · exact local_eq_178 x
  · exact local_eq_179 x
  · exact local_eq_180 x
  · exact local_eq_181 x
  · exact local_eq_182 x
  · exact local_eq_183 x
  · exact local_eq_184 x
  · exact local_eq_185 x
  · exact local_eq_186 x
  · exact local_eq_187 x
  · exact local_eq_188 x
  · exact local_eq_189 x
  · exact local_eq_190 x
  · exact local_eq_191 x
  · exact local_eq_192 x
  · exact local_eq_193 x
  · exact local_eq_194 x
  · exact local_eq_195 x
  · exact local_eq_196 x
  · exact local_eq_197 x
  · exact local_eq_198 x
  · exact local_eq_199 x
  · exact local_eq_200 x
  · exact local_eq_201 x
  · exact local_eq_202 x
  · exact local_eq_203 x
  · exact local_eq_204 x
  · exact local_eq_205 x
  · exact local_eq_206 x
  · exact local_eq_207 x
  · exact local_eq_208 x
  · exact local_eq_209 x
  · exact local_eq_210 x
  · exact local_eq_211 x
  · exact local_eq_212 x
  · exact local_eq_213 x
  · exact local_eq_214 x
  · exact local_eq_215 x
  · exact local_eq_216 x
  · exact local_eq_217 x
  · exact local_eq_218 x
  · exact local_eq_219 x
  · exact local_eq_220 x
  · exact local_eq_221 x
  · exact local_eq_222 x
  · exact local_eq_223 x
  · exact local_eq_224 x
  · exact local_eq_225 x
  · exact local_eq_226 x
  · exact local_eq_227 x
  · exact local_eq_228 x
  · exact local_eq_229 x
  · exact local_eq_230 x
  · exact local_eq_231 x
  · exact local_eq_232 x
  · exact local_eq_233 x
  · exact local_eq_234 x
  · exact local_eq_235 x
  · exact local_eq_236 x
  · exact local_eq_237 x
  · exact local_eq_238 x
  · exact local_eq_239 x
  · exact local_eq_240 x
  · exact local_eq_241 x
  · exact local_eq_242 x
  · exact local_eq_243 x
  · exact local_eq_244 x
  · exact local_eq_245 x
  · exact local_eq_246 x
  · exact local_eq_247 x
  · exact local_eq_248 x
  · exact local_eq_249 x
  · exact local_eq_250 x
  · exact local_eq_251 x
  · exact local_eq_252 x
  · exact local_eq_253 x
  · exact local_eq_254 x
  · exact local_eq_255 x
  · exact local_eq_256 x
  · exact local_eq_257 x
  · exact local_eq_258 x
  · exact local_eq_259 x
  · exact local_eq_260 x
  · exact local_eq_261 x
  · exact local_eq_262 x
  · exact local_eq_263 x
  · exact local_eq_264 x
  · exact local_eq_265 x
  · exact local_eq_266 x
  · exact local_eq_267 x
  · exact local_eq_268 x
  · exact local_eq_269 x
  · exact local_eq_270 x
  · exact local_eq_271 x
  · exact local_eq_272 x
  · exact local_eq_273 x
  · exact local_eq_274 x
  · exact local_eq_275 x
  · exact local_eq_276 x
  · exact local_eq_277 x
  · exact local_eq_278 x
  · exact local_eq_279 x
  · exact local_eq_280 x
  · exact local_eq_281 x
  · exact local_eq_282 x
  · exact local_eq_283 x
  · exact local_eq_284 x
  · exact local_eq_285 x
  · exact local_eq_286 x
  · exact local_eq_287 x
  · exact local_eq_288 x
  · exact local_eq_289 x
  · exact local_eq_290 x
  · exact local_eq_291 x
  · exact local_eq_292 x
  · exact local_eq_293 x
  · exact local_eq_294 x
  · exact local_eq_295 x
  · exact local_eq_296 x
  · exact local_eq_297 x
  · exact local_eq_298 x
  · exact local_eq_299 x
  · exact local_eq_300 x
  · exact local_eq_301 x
  · exact local_eq_302 x
  · exact local_eq_303 x
  · exact local_eq_304 x
  · exact local_eq_305 x
  · exact local_eq_306 x
  · exact local_eq_307 x
  · exact local_eq_308 x
  · exact local_eq_309 x
  · exact local_eq_310 x
  · exact local_eq_311 x
  · exact local_eq_312 x
  · exact local_eq_313 x
  · exact local_eq_314 x
  · exact local_eq_315 x
  · exact local_eq_316 x
  · exact local_eq_317 x
  · exact local_eq_318 x
  · exact local_eq_319 x
  · exact local_eq_320 x
  · exact local_eq_321 x
  · exact local_eq_322 x
  · exact local_eq_323 x
  · exact local_eq_324 x
  · exact local_eq_325 x
  · exact local_eq_326 x
  · exact local_eq_327 x
  · exact local_eq_328 x
  · exact local_eq_329 x
  · exact local_eq_330 x
  · exact local_eq_331 x
  · exact local_eq_332 x
  · exact local_eq_333 x
  · exact local_eq_334 x
  · exact local_eq_335 x
  · exact local_eq_336 x
  · exact local_eq_337 x
  · exact local_eq_338 x
  · exact local_eq_339 x
  · exact local_eq_340 x
  · exact local_eq_341 x
  · exact local_eq_342 x
  · exact local_eq_343 x
  · exact local_eq_344 x
  · exact local_eq_345 x
  · exact local_eq_346 x
  · exact local_eq_347 x
  · exact local_eq_348 x
  · exact local_eq_349 x
  · exact local_eq_350 x
  · exact local_eq_351 x
  · exact local_eq_352 x
  · exact local_eq_353 x
  · exact local_eq_354 x
  · exact local_eq_355 x
  · exact local_eq_356 x
  · exact local_eq_357 x
  · exact local_eq_358 x
  · exact local_eq_359 x
  · exact local_eq_360 x
  · exact local_eq_361 x
  · exact local_eq_362 x
  · exact local_eq_363 x
  · exact local_eq_364 x
  · exact local_eq_365 x
  · exact local_eq_366 x
  · exact local_eq_367 x
  · exact local_eq_368 x
  · exact local_eq_369 x
  · exact local_eq_370 x
  · exact local_eq_371 x
  · exact local_eq_372 x
  · exact local_eq_373 x
  · exact local_eq_374 x
  · exact local_eq_375 x
  · exact local_eq_376 x
  · exact local_eq_377 x
  · exact local_eq_378 x
  · exact local_eq_379 x
  · exact local_eq_380 x
  · exact local_eq_381 x
  · exact local_eq_382 x
  · exact local_eq_383 x
  · exact local_eq_384 x
  · exact local_eq_385 x
  · exact local_eq_386 x
  · exact local_eq_387 x
  · exact local_eq_388 x
  · exact local_eq_389 x
  · exact local_eq_390 x
  · exact local_eq_391 x
  · exact local_eq_392 x
  · exact local_eq_393 x
  · exact local_eq_394 x

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma local_reads_back : ∀ j : Fin 395,
    ∀ i ∈ (gates.getD j.val ⟨GateOp.or, []⟩).inputs, i < 128 + j.val := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma circuit_eval_eq_named_table (x : Fin 128 → Bool) :
    circuitFun 128 circuit x = table x 522 := by
  apply PEqualNP.Outside.L_meta_3566.WireTable.circuit_eval_of_table circuit x (table x)
  · exact table_inputs x
  · intro j g hget i hi
    change gates[j]? = some g at hget
    obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp hget
    have hj' : j < 395 := hj
    have heq : gates.getD j ⟨GateOp.or, []⟩ = g := by
      simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some]
    have hb := local_reads_back ⟨j, hj'⟩
    rw [heq] at hb
    exact hb i hi
  · intro j g hget
    change gates[j]? = some g at hget
    obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp hget
    have hj' : j < 395 := hj
    have heq : gates.getD j ⟨GateOp.or, []⟩ = g := by
      simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some]
    have hg := local_gate_equations x ⟨j, hj'⟩
    rw [heq] at hg
    exact hg
  · decide

set_option maxRecDepth 20000 in
lemma table_output (x : Fin 128 → Bool) : table x 522 = w522 x := by
  rfl

end GF8Representation

namespace GF8Rails

def timesX (a : BitVec 3) : BitVec 3 :=
  (a <<< 1) ^^^ (if a.getLsbD 2 then 3 else 0)

def mul (a b : BitVec 3) : BitVec 3 :=
  (if b.getLsbD 0 then a else 0) ^^^
  (if b.getLsbD 1 then timesX a else 0) ^^^
  (if b.getLsbD 2 then timesX (timesX a) else 0)

def rail (b : Bool) : Bool × Bool := (!b, b)

def dualAnd (p q : Bool × Bool) : Bool × Bool :=
  (p.1 || q.1, p.2 && q.2)

def dualXor (p q : Bool × Bool) : Bool × Bool :=
  ((p.1 && q.1) || (p.2 && q.2), (p.1 && q.2) || (p.2 && q.1))

def mulRails (a x : Fin 3 → Bool × Bool) (i : Fin 3) : Bool × Bool :=
  let terms := fun j k : Fin 3 => dualAnd (a j) (x k)
  let cross := dualXor (terms 1 2) (terms 2 1)
  if i = 0 then dualXor (terms 0 0) cross
  else if i = 1 then
    dualXor (dualXor (dualXor (terms 0 1) (terms 1 0)) cross) (terms 2 2)
  else dualXor (dualXor (dualXor (terms 0 2) (terms 1 1)) (terms 2 0)) (terms 2 2)

def bits (a : BitVec 3) (i : Fin 3) : Bool × Bool := rail (a.getLsbD i.val)

def agree (p q : Bool × Bool) : Bool :=
  (p.1 && q.1) || (p.2 && q.2)

def endpointTest (x y a b : BitVec 3) : Bool :=
  let product := mulRails (bits a) (bits x)
  let eq := fun i : Fin 3 => agree (bits y i) (dualXor (product i) (bits b i))
  (eq 0 && eq 1) && eq 2

lemma dualAnd_rail (p q : Bool) : dualAnd (rail p) (rail q) = rail (p && q) := by
  cases p <;> cases q <;> rfl

lemma dualXor_rail (p q : Bool) : dualXor (rail p) (rail q) = rail (xor p q) := by
  cases p <;> cases q <;> rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma multiplication_rails : ∀ a x : BitVec 3, ∀ i : Fin 3,
    mulRails (bits a) (bits x) i = bits (mul a x) i := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma endpoint_test_correct : ∀ x y a b : BitVec 3,
    endpointTest x y a b = (y == (mul a x ^^^ b)) := by
  decide

end GF8Rails

namespace GF8Coordinates

open PEqualNP.Outside.L_meta_3566.GF8Rails

def point (x y : Fin 8) : Fin 128 := ⟨8 * x.val + y.val, by omega⟩

def line (a b : Fin 8) : Fin 128 := ⟨64 + 8 * a.val + b.val, by omega⟩

def crossInput (x y a b : Fin 8) (v : Fin 128) : Bool :=
  decide (v = point x y ∨ v = line a b)

def or4 (a b c d : Bool) : Bool := ((a || b) || c) || d

def or8 (f : Fin 8 → Bool) : Bool :=
  ((((((f 0 || f 1) || f 2) || f 3) || f 4) || f 5) || f 6) || f 7

def pointX (x : Fin 128 → Bool) (u : Fin 8) : Bool :=
  or8 (fun v => x (point u v))

def pointY (x : Fin 128 → Bool) (v : Fin 8) : Bool :=
  or8 (fun u => x (point u v))

def lineA (x : Fin 128 → Bool) (a : Fin 8) : Bool :=
  or8 (fun b => x (line a b))

def lineB (x : Fin 128 → Bool) (b : Fin 8) : Bool :=
  or8 (fun a => x (line a b))

def groupRails (g : Fin 8 → Bool) (i : Fin 3) : Bool × Bool :=
  if i = 0 then (or4 (g 0) (g 2) (g 4) (g 6), or4 (g 1) (g 3) (g 5) (g 7))
  else if i = 1 then (or4 (g 0) (g 1) (g 4) (g 5), or4 (g 2) (g 3) (g 6) (g 7))
  else (or4 (g 0) (g 1) (g 2) (g 3), or4 (g 4) (g 5) (g 6) (g 7))

def structuredEval (x : Fin 128 → Bool) : Bool :=
  let xr := groupRails (pointX x)
  let yr := groupRails (pointY x)
  let ar := groupRails (lineA x)
  let br := groupRails (lineB x)
  let product := mulRails ar xr
  let eq := fun i : Fin 3 => agree (yr i) (dualXor (product i) (br i))
  (((xr 0).1 || (xr 0).2) && ((ar 0).1 || (ar 0).2)) && ((eq 0 && eq 1) && eq 2)

lemma point_eq_iff (x y u v : Fin 8) : point x y = point u v ↔ x = u ∧ y = v := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [point] at hv
    have hx : x.val = u.val := by omega
    have hy : y.val = v.val := by omega
    exact ⟨Fin.ext hx, Fin.ext hy⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma line_eq_iff (a b u v : Fin 8) : line a b = line u v ↔ a = u ∧ b = v := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [line] at hv
    have ha : a.val = u.val := by omega
    have hb : b.val = v.val := by omega
    exact ⟨Fin.ext ha, Fin.ext hb⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma point_ne_line (x y a b : Fin 8) : point x y ≠ line a b := by
  intro h
  have hv := congrArg Fin.val h
  simp only [point, line] at hv
  omega

lemma line_ne_point (a b x y : Fin 8) : line a b ≠ point x y :=
  (point_ne_line x y a b).symm

set_option maxRecDepth 10000 in
lemma or8_eq_decide : ∀ f : Fin 8 → Bool, or8 f = decide (∃ i : Fin 8, f i = true) := by
  decide

lemma pointX_cross (x y a b : Fin 8) :
    pointX (crossInput x y a b) = (fun u : Fin 8 => decide (u = x)) := by
  funext u
  simp [pointX, or8_eq_decide, crossInput, point_eq_iff, point_ne_line]

lemma pointY_cross (x y a b : Fin 8) :
    pointY (crossInput x y a b) = (fun v : Fin 8 => decide (v = y)) := by
  funext v
  simp [pointY, or8_eq_decide, crossInput, point_eq_iff, point_ne_line]

lemma lineA_cross (x y a b : Fin 8) :
    lineA (crossInput x y a b) = (fun u : Fin 8 => decide (u = a)) := by
  funext u
  simp [lineA, or8_eq_decide, crossInput, line_eq_iff, line_ne_point]

lemma lineB_cross (x y a b : Fin 8) :
    lineB (crossInput x y a b) = (fun v : Fin 8 => decide (v = b)) := by
  funext v
  simp [lineB, or8_eq_decide, crossInput, line_eq_iff, line_ne_point]

set_option maxRecDepth 10000 in
lemma groupRails_onehot_at : ∀ k : Fin 8, ∀ i : Fin 3,
    groupRails (fun j : Fin 8 => decide (j = k)) i = bits (BitVec.ofNat 3 k.val) i := by
  decide

lemma groupRails_onehot (k : Fin 8) :
    groupRails (fun j : Fin 8 => decide (j = k)) = bits (BitVec.ofNat 3 k.val) := by
  funext i
  exact groupRails_onehot_at k i

lemma bits_present (b : BitVec 3) (i : Fin 3) : ((bits b i).1 || (bits b i).2) = true := by
  simp [bits, rail]

lemma structured_on_cross (x y a b : Fin 8) :
    structuredEval (crossInput x y a b) = endpointTest
      (BitVec.ofNat 3 x.val) (BitVec.ofNat 3 y.val)
      (BitVec.ofNat 3 a.val) (BitVec.ofNat 3 b.val) := by
  simp only [structuredEval, pointX_cross, pointY_cross, lineA_cross, lineB_cross,
    groupRails_onehot, bits_present, Bool.true_and]
  rfl

lemma structured_no_points (x : Fin 128 → Bool)
    (hx : ∀ u v : Fin 8, x (point u v) = false) : structuredEval x = false := by
  simp [structuredEval, pointX, or8, groupRails, or4, hx]

lemma structured_no_lines (x : Fin 128 → Bool)
    (hx : ∀ a b : Fin 8, x (line a b) = false) : structuredEval x = false := by
  simp [structuredEval, lineA, or8, groupRails, or4, hx]

lemma structured_cross_correct (x y a b : Fin 8) :
    structuredEval (crossInput x y a b) =
      ((BitVec.ofNat 3 y.val) ==
        (mul (BitVec.ofNat 3 a.val) (BitVec.ofNat 3 x.val) ^^^ BitVec.ofNat 3 b.val)) := by
  rw [structured_on_cross, endpoint_test_correct]

lemma vertex_cases (v : Fin 128) :
    (∃ x y : Fin 8, v = point x y) ∨ (∃ a b : Fin 8, v = line a b) := by
  by_cases h : v.val < 64
  · left
    refine ⟨⟨v.val / 8, by omega⟩, ⟨v.val % 8, by omega⟩, ?_⟩
    apply Fin.ext
    dsimp [point]
    omega
  · right
    refine ⟨⟨(v.val - 64) / 8, by omega⟩, ⟨(v.val - 64) % 8, by omega⟩, ?_⟩
    apply Fin.ext
    dsimp [line]
    omega

def pairInput (u v w : Fin 128) : Bool := decide (w = u ∨ w = v)

lemma pairInput_comm (u v : Fin 128) : pairInput u v = pairInput v u := by
  funext w
  simp [pairInput, or_comm]

lemma structured_pair_points (x y u v : Fin 8) :
    structuredEval (pairInput (point x y) (point u v)) = false := by
  apply structured_no_lines
  intro a b
  simp [pairInput, line_ne_point]

lemma structured_pair_lines (a b u v : Fin 8) :
    structuredEval (pairInput (line a b) (line u v)) = false := by
  apply structured_no_points
  intro x y
  simp [pairInput, point_ne_line]

lemma structured_singleton (u : Fin 128) :
    structuredEval (fun w => decide (w = u)) = false := by
  have hpair : (fun w => decide (w = u)) = pairInput u u := by
    funext w
    simp [pairInput]
  rw [hpair]
  rcases vertex_cases u with ⟨x, y, rfl⟩ | ⟨a, b, rfl⟩
  · exact structured_pair_points x y x y
  · exact structured_pair_lines a b a b

lemma structured_empty : structuredEval (fun _ => false) = false := by
  apply structured_no_points
  intros
  rfl

abbrev incidence (p l : Fin 128) : Prop :=
  p.val < 64 ∧ 64 ≤ l.val ∧
    BitVec.ofNat 3 (p.val % 8) =
      (mul (BitVec.ofNat 3 ((l.val - 64) / 8)) (BitVec.ofNat 3 (p.val / 8)) ^^^
        BitVec.ofNat 3 ((l.val - 64) % 8))

abbrev adjacent (u v : Fin 128) : Prop := incidence u v ∨ incidence v u

lemma incidence_point_line (x y a b : Fin 8) :
    incidence (point x y) (line a b) ↔
      BitVec.ofNat 3 y.val =
        (mul (BitVec.ofNat 3 a.val) (BitVec.ofNat 3 x.val) ^^^ BitVec.ofNat 3 b.val) := by
  have hp : (point x y).val < 64 := by simp only [point]; omega
  have hl : 64 ≤ (line a b).val := by simp only [line]; omega
  have hpx : (point x y).val / 8 = x.val := by simp only [point]; omega
  have hpy : (point x y).val % 8 = y.val := by simp only [point]; omega
  have hla : ((line a b).val - 64) / 8 = a.val := by simp only [line]; omega
  have hlb : ((line a b).val - 64) % 8 = b.val := by simp only [line]; omega
  simp [incidence, hp, hl, hpx, hpy, hla, hlb]

lemma not_incidence_point (u : Fin 128) (x y : Fin 8) :
    ¬ incidence u (point x y) := by
  intro h
  have hl := h.2.1
  simp only [point] at hl
  omega

lemma not_incidence_line (a b : Fin 8) (u : Fin 128) :
    ¬ incidence (line a b) u := by
  intro h
  have hp := h.1
  simp only [line] at hp
  omega

lemma adjacent_point_line (x y a b : Fin 8) :
    adjacent (point x y) (line a b) ↔
      BitVec.ofNat 3 y.val =
        (mul (BitVec.ofNat 3 a.val) (BitVec.ofNat 3 x.val) ^^^ BitVec.ofNat 3 b.val) := by
  simp [adjacent, incidence_point_line, not_incidence_line]

lemma structured_pair_correct (u v : Fin 128) :
    structuredEval (pairInput u v) = decide (adjacent u v) := by
  rcases vertex_cases u with ⟨x, y, rfl⟩ | ⟨a, b, rfl⟩ <;>
    rcases vertex_cases v with ⟨x', y', rfl⟩ | ⟨a', b', rfl⟩
  · simp [structured_pair_points, adjacent, not_incidence_point]
  · change structuredEval (crossInput x y a' b') = _
    rw [structured_cross_correct]
    simp only [adjacent_point_line]
    exact beq_eq_decide _ _
  · rw [pairInput_comm]
    change structuredEval (crossInput x' y' a b) = _
    rw [structured_cross_correct]
    simp only [adjacent, not_incidence_line, false_or, incidence_point_line]
    exact beq_eq_decide _ _
  · simp [structured_pair_lines, adjacent, not_incidence_line]

end GF8Coordinates

namespace GF8Representation
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_3566.GF8Coordinates
open PEqualNP.Outside.L_meta_3566.GF8Rails

lemma group_134 (x : Fin 128 → Bool) : w134 x = pointX x 0 := by
  simp only [w128, w129, w130, w131, w132, w133, w134, pointX, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_141 (x : Fin 128 → Bool) : w141 x = pointX x 1 := by
  simp only [w135, w136, w137, w138, w139, w140, w141, pointX, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_148 (x : Fin 128 → Bool) : w148 x = pointX x 2 := by
  simp only [w142, w143, w144, w145, w146, w147, w148, pointX, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_155 (x : Fin 128 → Bool) : w155 x = pointX x 3 := by
  simp only [w149, w150, w151, w152, w153, w154, w155, pointX, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_162 (x : Fin 128 → Bool) : w162 x = pointX x 4 := by
  simp only [w156, w157, w158, w159, w160, w161, w162, pointX, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_169 (x : Fin 128 → Bool) : w169 x = pointX x 5 := by
  simp only [w163, w164, w165, w166, w167, w168, w169, pointX, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_176 (x : Fin 128 → Bool) : w176 x = pointX x 6 := by
  simp only [w170, w171, w172, w173, w174, w175, w176, pointX, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_183 (x : Fin 128 → Bool) : w183 x = pointX x 7 := by
  simp only [w177, w178, w179, w180, w181, w182, w183, pointX, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_190 (x : Fin 128 → Bool) : w190 x = pointY x 0 := by
  simp only [w184, w185, w186, w187, w188, w189, w190, pointY, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_197 (x : Fin 128 → Bool) : w197 x = pointY x 1 := by
  simp only [w191, w192, w193, w194, w195, w196, w197, pointY, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_204 (x : Fin 128 → Bool) : w204 x = pointY x 2 := by
  simp only [w198, w199, w200, w201, w202, w203, w204, pointY, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_211 (x : Fin 128 → Bool) : w211 x = pointY x 3 := by
  simp only [w205, w206, w207, w208, w209, w210, w211, pointY, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_218 (x : Fin 128 → Bool) : w218 x = pointY x 4 := by
  simp only [w212, w213, w214, w215, w216, w217, w218, pointY, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_225 (x : Fin 128 → Bool) : w225 x = pointY x 5 := by
  simp only [w219, w220, w221, w222, w223, w224, w225, pointY, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_232 (x : Fin 128 → Bool) : w232 x = pointY x 6 := by
  simp only [w226, w227, w228, w229, w230, w231, w232, pointY, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_239 (x : Fin 128 → Bool) : w239 x = pointY x 7 := by
  simp only [w233, w234, w235, w236, w237, w238, w239, pointY, or8, point, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_246 (x : Fin 128 → Bool) : w246 x = lineA x 0 := by
  simp only [w240, w241, w242, w243, w244, w245, w246, lineA, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_253 (x : Fin 128 → Bool) : w253 x = lineA x 1 := by
  simp only [w247, w248, w249, w250, w251, w252, w253, lineA, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_260 (x : Fin 128 → Bool) : w260 x = lineA x 2 := by
  simp only [w254, w255, w256, w257, w258, w259, w260, lineA, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_267 (x : Fin 128 → Bool) : w267 x = lineA x 3 := by
  simp only [w261, w262, w263, w264, w265, w266, w267, lineA, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_274 (x : Fin 128 → Bool) : w274 x = lineA x 4 := by
  simp only [w268, w269, w270, w271, w272, w273, w274, lineA, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_281 (x : Fin 128 → Bool) : w281 x = lineA x 5 := by
  simp only [w275, w276, w277, w278, w279, w280, w281, lineA, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_288 (x : Fin 128 → Bool) : w288 x = lineA x 6 := by
  simp only [w282, w283, w284, w285, w286, w287, w288, lineA, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_295 (x : Fin 128 → Bool) : w295 x = lineA x 7 := by
  simp only [w289, w290, w291, w292, w293, w294, w295, lineA, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_302 (x : Fin 128 → Bool) : w302 x = lineB x 0 := by
  simp only [w296, w297, w298, w299, w300, w301, w302, lineB, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_309 (x : Fin 128 → Bool) : w309 x = lineB x 1 := by
  simp only [w303, w304, w305, w306, w307, w308, w309, lineB, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_316 (x : Fin 128 → Bool) : w316 x = lineB x 2 := by
  simp only [w310, w311, w312, w313, w314, w315, w316, lineB, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_323 (x : Fin 128 → Bool) : w323 x = lineB x 3 := by
  simp only [w317, w318, w319, w320, w321, w322, w323, lineB, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_330 (x : Fin 128 → Bool) : w330 x = lineB x 4 := by
  simp only [w324, w325, w326, w327, w328, w329, w330, lineB, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_337 (x : Fin 128 → Bool) : w337 x = lineB x 5 := by
  simp only [w331, w332, w333, w334, w335, w336, w337, lineB, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_344 (x : Fin 128 → Bool) : w344 x = lineB x 6 := by
  simp only [w338, w339, w340, w341, w342, w343, w344, lineB, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma group_351 (x : Fin 128 → Bool) : w351 x = lineB x 7 := by
  simp only [w345, w346, w347, w348, w349, w350, w351, lineB, or8, line, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

def s354 (x : Fin 128 → Bool) : Bool × Bool := groupRails (pointX x) 0
lemma rail_354 (x : Fin 128 → Bool) : (w354 x, w357 x) = s354 x := by
  simp only [w352, w353, w354, w355, w356, w357, group_134, group_141, group_148, group_155, group_162, group_169, group_176, group_183, s354, groupRails, or4, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma rail_354_fst (x : Fin 128 → Bool) : w354 x = (s354 x).1 := congrArg Prod.fst (rail_354 x)
lemma rail_354_snd (x : Fin 128 → Bool) : w357 x = (s354 x).2 := congrArg Prod.snd (rail_354 x)

def s360 (x : Fin 128 → Bool) : Bool × Bool := groupRails (pointX x) 1
lemma rail_360 (x : Fin 128 → Bool) : (w360 x, w363 x) = s360 x := by
  simp only [w358, w359, w360, w361, w362, w363, group_134, group_141, group_148, group_155, group_162, group_169, group_176, group_183, s360, groupRails, or4, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma rail_360_fst (x : Fin 128 → Bool) : w360 x = (s360 x).1 := congrArg Prod.fst (rail_360 x)
lemma rail_360_snd (x : Fin 128 → Bool) : w363 x = (s360 x).2 := congrArg Prod.snd (rail_360 x)

def s366 (x : Fin 128 → Bool) : Bool × Bool := groupRails (pointX x) 2
lemma rail_366 (x : Fin 128 → Bool) : (w366 x, w369 x) = s366 x := by
  simp only [w364, w365, w366, w367, w368, w369, group_134, group_141, group_148, group_155, group_162, group_169, group_176, group_183, s366, groupRails, or4, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma rail_366_fst (x : Fin 128 → Bool) : w366 x = (s366 x).1 := congrArg Prod.fst (rail_366 x)
lemma rail_366_snd (x : Fin 128 → Bool) : w369 x = (s366 x).2 := congrArg Prod.snd (rail_366 x)

def s372 (x : Fin 128 → Bool) : Bool × Bool := groupRails (pointY x) 0
lemma rail_372 (x : Fin 128 → Bool) : (w372 x, w375 x) = s372 x := by
  simp only [w370, w371, w372, w373, w374, w375, group_190, group_197, group_204, group_211, group_218, group_225, group_232, group_239, s372, groupRails, or4, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma rail_372_fst (x : Fin 128 → Bool) : w372 x = (s372 x).1 := congrArg Prod.fst (rail_372 x)
lemma rail_372_snd (x : Fin 128 → Bool) : w375 x = (s372 x).2 := congrArg Prod.snd (rail_372 x)

def s378 (x : Fin 128 → Bool) : Bool × Bool := groupRails (pointY x) 1
lemma rail_378 (x : Fin 128 → Bool) : (w378 x, w381 x) = s378 x := by
  simp only [w376, w377, w378, w379, w380, w381, group_190, group_197, group_204, group_211, group_218, group_225, group_232, group_239, s378, groupRails, or4, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma rail_378_fst (x : Fin 128 → Bool) : w378 x = (s378 x).1 := congrArg Prod.fst (rail_378 x)
lemma rail_378_snd (x : Fin 128 → Bool) : w381 x = (s378 x).2 := congrArg Prod.snd (rail_378 x)

def s384 (x : Fin 128 → Bool) : Bool × Bool := groupRails (pointY x) 2
lemma rail_384 (x : Fin 128 → Bool) : (w384 x, w387 x) = s384 x := by
  simp only [w382, w383, w384, w385, w386, w387, group_190, group_197, group_204, group_211, group_218, group_225, group_232, group_239, s384, groupRails, or4, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma rail_384_fst (x : Fin 128 → Bool) : w384 x = (s384 x).1 := congrArg Prod.fst (rail_384 x)
lemma rail_384_snd (x : Fin 128 → Bool) : w387 x = (s384 x).2 := congrArg Prod.snd (rail_384 x)

def s390 (x : Fin 128 → Bool) : Bool × Bool := groupRails (lineA x) 0
lemma rail_390 (x : Fin 128 → Bool) : (w390 x, w393 x) = s390 x := by
  simp only [w388, w389, w390, w391, w392, w393, group_246, group_253, group_260, group_267, group_274, group_281, group_288, group_295, s390, groupRails, or4, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma rail_390_fst (x : Fin 128 → Bool) : w390 x = (s390 x).1 := congrArg Prod.fst (rail_390 x)
lemma rail_390_snd (x : Fin 128 → Bool) : w393 x = (s390 x).2 := congrArg Prod.snd (rail_390 x)

def s396 (x : Fin 128 → Bool) : Bool × Bool := groupRails (lineA x) 1
lemma rail_396 (x : Fin 128 → Bool) : (w396 x, w399 x) = s396 x := by
  simp only [w394, w395, w396, w397, w398, w399, group_246, group_253, group_260, group_267, group_274, group_281, group_288, group_295, s396, groupRails, or4, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma rail_396_fst (x : Fin 128 → Bool) : w396 x = (s396 x).1 := congrArg Prod.fst (rail_396 x)
lemma rail_396_snd (x : Fin 128 → Bool) : w399 x = (s396 x).2 := congrArg Prod.snd (rail_396 x)

def s402 (x : Fin 128 → Bool) : Bool × Bool := groupRails (lineA x) 2
lemma rail_402 (x : Fin 128 → Bool) : (w402 x, w405 x) = s402 x := by
  simp only [w400, w401, w402, w403, w404, w405, group_246, group_253, group_260, group_267, group_274, group_281, group_288, group_295, s402, groupRails, or4, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma rail_402_fst (x : Fin 128 → Bool) : w402 x = (s402 x).1 := congrArg Prod.fst (rail_402 x)
lemma rail_402_snd (x : Fin 128 → Bool) : w405 x = (s402 x).2 := congrArg Prod.snd (rail_402 x)

def s408 (x : Fin 128 → Bool) : Bool × Bool := groupRails (lineB x) 0
lemma rail_408 (x : Fin 128 → Bool) : (w408 x, w411 x) = s408 x := by
  simp only [w406, w407, w408, w409, w410, w411, group_302, group_309, group_316, group_323, group_330, group_337, group_344, group_351, s408, groupRails, or4, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma rail_408_fst (x : Fin 128 → Bool) : w408 x = (s408 x).1 := congrArg Prod.fst (rail_408 x)
lemma rail_408_snd (x : Fin 128 → Bool) : w411 x = (s408 x).2 := congrArg Prod.snd (rail_408 x)

def s414 (x : Fin 128 → Bool) : Bool × Bool := groupRails (lineB x) 1
lemma rail_414 (x : Fin 128 → Bool) : (w414 x, w417 x) = s414 x := by
  simp only [w412, w413, w414, w415, w416, w417, group_302, group_309, group_316, group_323, group_330, group_337, group_344, group_351, s414, groupRails, or4, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma rail_414_fst (x : Fin 128 → Bool) : w414 x = (s414 x).1 := congrArg Prod.fst (rail_414 x)
lemma rail_414_snd (x : Fin 128 → Bool) : w417 x = (s414 x).2 := congrArg Prod.snd (rail_414 x)

def s420 (x : Fin 128 → Bool) : Bool × Bool := groupRails (lineB x) 2
lemma rail_420 (x : Fin 128 → Bool) : (w420 x, w423 x) = s420 x := by
  simp only [w418, w419, w420, w421, w422, w423, group_302, group_309, group_316, group_323, group_330, group_337, group_344, group_351, s420, groupRails, or4, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rfl

lemma rail_420_fst (x : Fin 128 → Bool) : w420 x = (s420 x).1 := congrArg Prod.fst (rail_420 x)
lemma rail_420_snd (x : Fin 128 → Bool) : w423 x = (s420 x).2 := congrArg Prod.snd (rail_420 x)

def s424 (x : Fin 128 → Bool) : Bool × Bool := dualAnd (s390 x) (s354 x)
lemma term_424 (x : Fin 128 → Bool) : (w424 x, w425 x) = s424 x := by
  simp only [w424, w425, s424, dualAnd, rail_390_fst, rail_354_fst, rail_390_snd, rail_354_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma term_424_fst (x : Fin 128 → Bool) : w424 x = (s424 x).1 := congrArg Prod.fst (term_424 x)
lemma term_424_snd (x : Fin 128 → Bool) : w425 x = (s424 x).2 := congrArg Prod.snd (term_424 x)

def s426 (x : Fin 128 → Bool) : Bool × Bool := dualAnd (s390 x) (s360 x)
lemma term_426 (x : Fin 128 → Bool) : (w426 x, w427 x) = s426 x := by
  simp only [w426, w427, s426, dualAnd, rail_390_fst, rail_360_fst, rail_390_snd, rail_360_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma term_426_fst (x : Fin 128 → Bool) : w426 x = (s426 x).1 := congrArg Prod.fst (term_426 x)
lemma term_426_snd (x : Fin 128 → Bool) : w427 x = (s426 x).2 := congrArg Prod.snd (term_426 x)

def s428 (x : Fin 128 → Bool) : Bool × Bool := dualAnd (s390 x) (s366 x)
lemma term_428 (x : Fin 128 → Bool) : (w428 x, w429 x) = s428 x := by
  simp only [w428, w429, s428, dualAnd, rail_390_fst, rail_366_fst, rail_390_snd, rail_366_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma term_428_fst (x : Fin 128 → Bool) : w428 x = (s428 x).1 := congrArg Prod.fst (term_428 x)
lemma term_428_snd (x : Fin 128 → Bool) : w429 x = (s428 x).2 := congrArg Prod.snd (term_428 x)

def s430 (x : Fin 128 → Bool) : Bool × Bool := dualAnd (s396 x) (s354 x)
lemma term_430 (x : Fin 128 → Bool) : (w430 x, w431 x) = s430 x := by
  simp only [w430, w431, s430, dualAnd, rail_396_fst, rail_354_fst, rail_396_snd, rail_354_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma term_430_fst (x : Fin 128 → Bool) : w430 x = (s430 x).1 := congrArg Prod.fst (term_430 x)
lemma term_430_snd (x : Fin 128 → Bool) : w431 x = (s430 x).2 := congrArg Prod.snd (term_430 x)

def s432 (x : Fin 128 → Bool) : Bool × Bool := dualAnd (s396 x) (s360 x)
lemma term_432 (x : Fin 128 → Bool) : (w432 x, w433 x) = s432 x := by
  simp only [w432, w433, s432, dualAnd, rail_396_fst, rail_360_fst, rail_396_snd, rail_360_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma term_432_fst (x : Fin 128 → Bool) : w432 x = (s432 x).1 := congrArg Prod.fst (term_432 x)
lemma term_432_snd (x : Fin 128 → Bool) : w433 x = (s432 x).2 := congrArg Prod.snd (term_432 x)

def s434 (x : Fin 128 → Bool) : Bool × Bool := dualAnd (s396 x) (s366 x)
lemma term_434 (x : Fin 128 → Bool) : (w434 x, w435 x) = s434 x := by
  simp only [w434, w435, s434, dualAnd, rail_396_fst, rail_366_fst, rail_396_snd, rail_366_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma term_434_fst (x : Fin 128 → Bool) : w434 x = (s434 x).1 := congrArg Prod.fst (term_434 x)
lemma term_434_snd (x : Fin 128 → Bool) : w435 x = (s434 x).2 := congrArg Prod.snd (term_434 x)

def s436 (x : Fin 128 → Bool) : Bool × Bool := dualAnd (s402 x) (s354 x)
lemma term_436 (x : Fin 128 → Bool) : (w436 x, w437 x) = s436 x := by
  simp only [w436, w437, s436, dualAnd, rail_402_fst, rail_354_fst, rail_402_snd, rail_354_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma term_436_fst (x : Fin 128 → Bool) : w436 x = (s436 x).1 := congrArg Prod.fst (term_436 x)
lemma term_436_snd (x : Fin 128 → Bool) : w437 x = (s436 x).2 := congrArg Prod.snd (term_436 x)

def s438 (x : Fin 128 → Bool) : Bool × Bool := dualAnd (s402 x) (s360 x)
lemma term_438 (x : Fin 128 → Bool) : (w438 x, w439 x) = s438 x := by
  simp only [w438, w439, s438, dualAnd, rail_402_fst, rail_360_fst, rail_402_snd, rail_360_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma term_438_fst (x : Fin 128 → Bool) : w438 x = (s438 x).1 := congrArg Prod.fst (term_438 x)
lemma term_438_snd (x : Fin 128 → Bool) : w439 x = (s438 x).2 := congrArg Prod.snd (term_438 x)

def s440 (x : Fin 128 → Bool) : Bool × Bool := dualAnd (s402 x) (s366 x)
lemma term_440 (x : Fin 128 → Bool) : (w440 x, w441 x) = s440 x := by
  simp only [w440, w441, s440, dualAnd, rail_402_fst, rail_366_fst, rail_402_snd, rail_366_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma term_440_fst (x : Fin 128 → Bool) : w440 x = (s440 x).1 := congrArg Prod.fst (term_440 x)
lemma term_440_snd (x : Fin 128 → Bool) : w441 x = (s440 x).2 := congrArg Prod.snd (term_440 x)

def s444 (x : Fin 128 → Bool) : Bool × Bool := dualXor (s426 x) (s430 x)
lemma xor_444 (x : Fin 128 → Bool) : (w444 x, w447 x) = s444 x := by
  simp only [w442, w443, w444, w445, w446, w447, s444, dualXor, term_426_fst, term_430_fst, term_426_snd, term_430_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma xor_444_fst (x : Fin 128 → Bool) : w444 x = (s444 x).1 := congrArg Prod.fst (xor_444 x)
lemma xor_444_snd (x : Fin 128 → Bool) : w447 x = (s444 x).2 := congrArg Prod.snd (xor_444 x)

def s450 (x : Fin 128 → Bool) : Bool × Bool := dualXor (s428 x) (s432 x)
lemma xor_450 (x : Fin 128 → Bool) : (w450 x, w453 x) = s450 x := by
  simp only [w448, w449, w450, w451, w452, w453, s450, dualXor, term_428_fst, term_432_fst, term_428_snd, term_432_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma xor_450_fst (x : Fin 128 → Bool) : w450 x = (s450 x).1 := congrArg Prod.fst (xor_450 x)
lemma xor_450_snd (x : Fin 128 → Bool) : w453 x = (s450 x).2 := congrArg Prod.snd (xor_450 x)

def s456 (x : Fin 128 → Bool) : Bool × Bool := dualXor (s450 x) (s436 x)
lemma xor_456 (x : Fin 128 → Bool) : (w456 x, w459 x) = s456 x := by
  simp only [w454, w455, w456, w457, w458, w459, s456, dualXor, xor_450_fst, term_436_fst, xor_450_snd, term_436_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma xor_456_fst (x : Fin 128 → Bool) : w456 x = (s456 x).1 := congrArg Prod.fst (xor_456 x)
lemma xor_456_snd (x : Fin 128 → Bool) : w459 x = (s456 x).2 := congrArg Prod.snd (xor_456 x)

def s462 (x : Fin 128 → Bool) : Bool × Bool := dualXor (s434 x) (s438 x)
lemma xor_462 (x : Fin 128 → Bool) : (w462 x, w465 x) = s462 x := by
  simp only [w460, w461, w462, w463, w464, w465, s462, dualXor, term_434_fst, term_438_fst, term_434_snd, term_438_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma xor_462_fst (x : Fin 128 → Bool) : w462 x = (s462 x).1 := congrArg Prod.fst (xor_462 x)
lemma xor_462_snd (x : Fin 128 → Bool) : w465 x = (s462 x).2 := congrArg Prod.snd (xor_462 x)

def s468 (x : Fin 128 → Bool) : Bool × Bool := dualXor (s424 x) (s462 x)
lemma xor_468 (x : Fin 128 → Bool) : (w468 x, w471 x) = s468 x := by
  simp only [w466, w467, w468, w469, w470, w471, s468, dualXor, term_424_fst, xor_462_fst, term_424_snd, xor_462_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma xor_468_fst (x : Fin 128 → Bool) : w468 x = (s468 x).1 := congrArg Prod.fst (xor_468 x)
lemma xor_468_snd (x : Fin 128 → Bool) : w471 x = (s468 x).2 := congrArg Prod.snd (xor_468 x)

def s474 (x : Fin 128 → Bool) : Bool × Bool := dualXor (s444 x) (s462 x)
lemma xor_474 (x : Fin 128 → Bool) : (w474 x, w477 x) = s474 x := by
  simp only [w472, w473, w474, w475, w476, w477, s474, dualXor, xor_444_fst, xor_462_fst, xor_444_snd, xor_462_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma xor_474_fst (x : Fin 128 → Bool) : w474 x = (s474 x).1 := congrArg Prod.fst (xor_474 x)
lemma xor_474_snd (x : Fin 128 → Bool) : w477 x = (s474 x).2 := congrArg Prod.snd (xor_474 x)

def s480 (x : Fin 128 → Bool) : Bool × Bool := dualXor (s474 x) (s440 x)
lemma xor_480 (x : Fin 128 → Bool) : (w480 x, w483 x) = s480 x := by
  simp only [w478, w479, w480, w481, w482, w483, s480, dualXor, xor_474_fst, term_440_fst, xor_474_snd, term_440_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma xor_480_fst (x : Fin 128 → Bool) : w480 x = (s480 x).1 := congrArg Prod.fst (xor_480 x)
lemma xor_480_snd (x : Fin 128 → Bool) : w483 x = (s480 x).2 := congrArg Prod.snd (xor_480 x)

def s486 (x : Fin 128 → Bool) : Bool × Bool := dualXor (s456 x) (s440 x)
lemma xor_486 (x : Fin 128 → Bool) : (w486 x, w489 x) = s486 x := by
  simp only [w484, w485, w486, w487, w488, w489, s486, dualXor, xor_456_fst, term_440_fst, xor_456_snd, term_440_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma xor_486_fst (x : Fin 128 → Bool) : w486 x = (s486 x).1 := congrArg Prod.fst (xor_486 x)
lemma xor_486_snd (x : Fin 128 → Bool) : w489 x = (s486 x).2 := congrArg Prod.snd (xor_486 x)

def s492 (x : Fin 128 → Bool) : Bool × Bool := dualXor (s468 x) (s408 x)
lemma xor_492 (x : Fin 128 → Bool) : (w492 x, w495 x) = s492 x := by
  simp only [w490, w491, w492, w493, w494, w495, s492, dualXor, xor_468_fst, rail_408_fst, xor_468_snd, rail_408_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma xor_492_fst (x : Fin 128 → Bool) : w492 x = (s492 x).1 := congrArg Prod.fst (xor_492 x)
lemma xor_492_snd (x : Fin 128 → Bool) : w495 x = (s492 x).2 := congrArg Prod.snd (xor_492 x)

def s498 (x : Fin 128 → Bool) : Bool × Bool := dualXor (s480 x) (s414 x)
lemma xor_498 (x : Fin 128 → Bool) : (w498 x, w501 x) = s498 x := by
  simp only [w496, w497, w498, w499, w500, w501, s498, dualXor, xor_480_fst, rail_414_fst, xor_480_snd, rail_414_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma xor_498_fst (x : Fin 128 → Bool) : w498 x = (s498 x).1 := congrArg Prod.fst (xor_498 x)
lemma xor_498_snd (x : Fin 128 → Bool) : w501 x = (s498 x).2 := congrArg Prod.snd (xor_498 x)

def s504 (x : Fin 128 → Bool) : Bool × Bool := dualXor (s486 x) (s420 x)
lemma xor_504 (x : Fin 128 → Bool) : (w504 x, w507 x) = s504 x := by
  simp only [w502, w503, w504, w505, w506, w507, s504, dualXor, xor_486_fst, rail_420_fst, xor_486_snd, rail_420_snd, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

lemma xor_504_fst (x : Fin 128 → Bool) : w504 x = (s504 x).1 := congrArg Prod.fst (xor_504 x)
lemma xor_504_snd (x : Fin 128 → Bool) : w507 x = (s504 x).2 := congrArg Prod.snd (xor_504 x)

lemma product_0 (x : Fin 128 → Bool) : s468 x =
    mulRails (groupRails (lineA x)) (groupRails (pointX x)) 0 := by
  rfl

lemma product_1 (x : Fin 128 → Bool) : s480 x =
    mulRails (groupRails (lineA x)) (groupRails (pointX x)) 1 := by
  rfl

lemma product_2 (x : Fin 128 → Bool) : s486 x =
    mulRails (groupRails (lineA x)) (groupRails (pointX x)) 2 := by
  rfl

lemma eq_0 (x : Fin 128 → Bool) : w510 x =
    agree (groupRails (pointY x) 0)
      (dualXor (mulRails (groupRails (lineA x)) (groupRails (pointX x)) 0)
        (groupRails (lineB x) 0)) := by
  simp only [w508, w509, w510, xor_492_fst, rail_372_fst, xor_492_snd, rail_372_snd, s492, s372, s408, product_0, agree, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
  simp only [Bool.and_comm]

lemma eq_1 (x : Fin 128 → Bool) : w513 x =
    agree (groupRails (pointY x) 1)
      (dualXor (mulRails (groupRails (lineA x)) (groupRails (pointX x)) 1)
        (groupRails (lineB x) 1)) := by
  simp only [w511, w512, w513, xor_498_fst, rail_378_fst, xor_498_snd, rail_378_snd, s498, s378, s414, product_1, agree, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
  simp only [Bool.and_comm]

lemma eq_2 (x : Fin 128 → Bool) : w516 x =
    agree (groupRails (pointY x) 2)
      (dualXor (mulRails (groupRails (lineA x)) (groupRails (pointX x)) 2)
        (groupRails (lineB x) 2)) := by
  simp only [w514, w515, w516, xor_504_fst, rail_384_fst, xor_504_snd, rail_384_snd, s504, s384, s420, product_2, agree, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
  simp only [Bool.and_comm]

lemma named_output_eq_structured (x : Fin 128 → Bool) : w522 x = structuredEval x := by
  simp only [w517, w518, w519, w520, w521, w522, eq_0, eq_1, eq_2, rail_354_fst, rail_354_snd, rail_390_fst, rail_390_snd, s354, s390, structuredEval, GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]

end GF8Representation

namespace GF8Representation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def witness : Fin 128 → Bool := fun v => decide (v.val = 0 ∨ v.val = 9 ∨ v.val = 73)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma isAO2 : IsAO2 128 circuit := by decide

set_option maxRecDepth 20000 in
lemma size_eq : circuit.size = 395 := by decide

set_option maxRecDepth 20000 in
lemma and_count_eq :
    (circuit.gates.filter fun g => match g.op with | GateOp.and => true | _ => false).length = 63 := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma accepted_witness : circuitFun 128 circuit witness = true := by decide

def gfTimesX (a : BitVec 3) : BitVec 3 :=
  (a <<< 1) ^^^ (if a.getLsbD 2 then 3 else 0)

def gfMul (a b : BitVec 3) : BitVec 3 :=
  (if b.getLsbD 0 then a else 0) ^^^
  (if b.getLsbD 1 then gfTimesX a else 0) ^^^
  (if b.getLsbD 2 then gfTimesX (gfTimesX a) else 0)

def incidence (p l : Fin 128) : Prop :=
  p.val < 64 ∧ 64 ≤ l.val ∧
    BitVec.ofNat 3 (p.val % 8) =
      (gfMul (BitVec.ofNat 3 ((l.val - 64) / 8)) (BitVec.ofNat 3 (p.val / 8)) ^^^
        BitVec.ofNat 3 ((l.val - 64) % 8))

def adjacent (u v : Fin 128) : Prop := incidence u v ∨ incidence v u

lemma no_edge_on_witness : ∀ u v : Fin 128,
    witness u = true → witness v = true → ¬ adjacent u v := by
  intro u v hu hv
  have hu' : u.val = 0 ∨ u.val = 9 ∨ u.val = 73 := of_decide_eq_true hu
  have hv' : v.val = 0 ∨ v.val = 9 ∨ v.val = 73 := of_decide_eq_true hv
  rcases hu' with hu | hu | hu <;> rcases hv' with hv | hv | hv <;>
    simp only [adjacent, incidence, hu, hv] <;> decide

lemma false_positive : circuitFun 128 circuit witness = true ∧
    ¬ ∃ u v : Fin 128, adjacent u v ∧ witness u = true ∧ witness v = true := by
  refine ⟨accepted_witness, ?_⟩
  rintro ⟨u, v, hadj, hu, hv⟩
  exact no_edge_on_witness u v hu hv hadj

def graph : SimpleGraph (Fin 128) where
  Adj := adjacent
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro v h
    rcases h with h | h <;> have hp := h.1 <;> have hl := h.2.1 <;> omega⟩

abbrev graphAdjDecidable : DecidableRel graph.Adj := by
  intro u v
  change Decidable (adjacent u v)
  unfold adjacent incidence
  infer_instance

lemma bipartite : ∃ c : Fin 128 → Bool, ∀ u v, graph.Adj u v → c u ≠ c v := by
  refine ⟨fun v => decide (64 ≤ v.val), ?_⟩
  intro u v h
  change incidence u v ∨ incidence v u at h
  rcases h with h | h
  · have hu : ¬ 64 ≤ u.val := by have := h.1; omega
    have hv : 64 ≤ v.val := h.2.1
    simp [hu, hv]
  · have hu : 64 ≤ u.val := h.2.1
    have hv : ¬ 64 ≤ v.val := by have := h.1; omega
    simp [hu, hv]

def linePerm (p : Fin 64) : Fin 64 :=
  Fin.ofNat 64 (8 * (p.val / 8) +
    ((BitVec.ofNat 3 (p.val % 8)) ^^^
      gfMul (BitVec.ofNat 3 (p.val / 8)) (BitVec.ofNat 3 (p.val / 8))).toNat)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma linePerm_involutive : Function.Involutive linePerm := by
  change ∀ p : Fin 64, linePerm (linePerm p) = p
  decide

lemma linePerm_injective : Function.Injective linePerm := linePerm_involutive.injective

def ends (p : Fin 64 × Bool) : Fin 128 :=
  if p.2 then Fin.natAdd 64 (linePerm p.1) else Fin.castAdd 64 p.1

lemma ends_injective : Function.Injective ends := by
  rintro ⟨p, b⟩ ⟨q, c⟩ h
  have hv := congrArg Fin.val h
  cases b <;> cases c
  · have hp : p = q := Fin.ext (by simpa [ends] using hv)
    exact Prod.ext hp rfl
  · have hp := p.isLt
    simp [ends] at hv
    omega
  · have hq := q.isLt
    simp [ends] at hv
    omega
  · have hidx : (linePerm p).val = (linePerm q).val := by
      simp [ends] at hv
      omega
    exact Prod.ext (linePerm_injective (Fin.ext hidx)) rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma matching_adj : ∀ p : Fin 64, graph.Adj (ends (p, false)) (ends (p, true)) := by
  change ∀ p : Fin 64, adjacent (ends (p, false)) (ends (p, true))
  unfold adjacent incidence
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma degree_eq :
    letI : DecidableRel graph.Adj := graphAdjDecidable
    ∀ v : Fin 128, graph.degree v = 8 := by
  letI : DecidableRel graph.Adj := graphAdjDecidable
  change ∀ v : Fin 128, graph.degree v = 8
  decide

def pointCover : Finset (Fin 128) := Finset.univ.filter fun v => v.val < 64

lemma pointCover_card : pointCover.card = 64 := by decide

lemma pointCover_covers : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover graph pointCover := by
  intro u v h
  change incidence u v ∨ incidence v u at h
  rcases h with h | h
  · exact Or.inl (by simpa [pointCover] using h.1)
  · exact Or.inr (by simpa [pointCover] using h.1)

lemma cover_lower (T : Finset (Fin 128))
    (hT : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover graph T) : 64 ≤ T.card := by
  classical
  let side : Fin 64 → Bool := fun i => if ends (i, false) ∈ T then false else true
  let pick : Fin 64 → Fin 128 := fun i => ends (i, side i)
  have hmem : ∀ i, pick i ∈ T := by
    intro i
    have h := hT _ _ (matching_adj i)
    dsimp [pick, side]
    split_ifs with hf
    · exact hf
    · exact h.resolve_left hf
  have hpick : Function.Injective pick := by
    intro i j heq
    exact congrArg Prod.fst (ends_injective heq)
  have hsub : Finset.univ.image pick ⊆ T := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i
  have hcard := Finset.card_le_card hsub
  simpa [Finset.card_image_of_injective _ hpick] using hcard

lemma minimum_cover : ∃ T : Finset (Fin 128),
    PEqualNP.MetaComplexity.CoverPromise.IsVertexCover graph T ∧ T.card = 64 ∧
      ∀ S : Finset (Fin 128),
        PEqualNP.MetaComplexity.CoverPromise.IsVertexCover graph S → T.card ≤ S.card := by
  refine ⟨pointCover, pointCover_covers, pointCover_card, ?_⟩
  intro S hS
  rw [pointCover_card]
  exact cover_lower S hS

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma mul_comm : ∀ a b : BitVec 3, gfMul a b = gfMul b a := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma mul_xor : ∀ a x y : BitVec 3,
    gfMul a (x ^^^ y) = gfMul a x ^^^ gfMul a y := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma mul_eq_zero_iff : ∀ a x : BitVec 3, gfMul a x = 0 ↔ a = 0 ∨ x = 0 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma mul_right_injective : ∀ x : BitVec 3, x ≠ 0 → Function.Injective (fun a => gfMul a x) := by
  change ∀ x : BitVec 3, x ≠ 0 → ∀ a b : BitVec 3, gfMul a x = gfMul b x → a = b
  decide

lemma rectangle {a a' x x' : BitVec 3} (ha : a ≠ a') (hx : x ≠ x') :
    gfMul a x ^^^ gfMul a x' ≠ gfMul a' x ^^^ gfMul a' x' := by
  intro h
  have hnonzero : x ^^^ x' ≠ 0 := fun hz => hx (BitVec.xor_eq_zero_iff.mp hz)
  apply ha
  apply mul_right_injective (x ^^^ x') hnonzero
  simpa only [mul_xor] using h

lemma xor_double_cancel {w : ℕ} (u v b : BitVec w) :
    (u ^^^ b) ^^^ (v ^^^ b) = u ^^^ v := by
  calc
    (u ^^^ b) ^^^ (v ^^^ b) = (u ^^^ v) ^^^ (b ^^^ b) := by ac_rfl
    _ = u ^^^ v := by simp

lemma common_line_unique {x y x' y' a b a' b' : BitVec 3}
    (hpoints : (x, y) ≠ (x', y'))
    (h1 : y = gfMul a x ^^^ b) (h2 : y' = gfMul a x' ^^^ b)
    (h3 : y = gfMul a' x ^^^ b') (h4 : y' = gfMul a' x' ^^^ b') :
    (a, b) = (a', b') := by
  have hx : x ≠ x' := by
    intro hx
    have hy : y = y' := by rw [h1, h2, hx]
    exact hpoints (Prod.ext hx hy)
  have hl : y ^^^ y' = gfMul a x ^^^ gfMul a x' := by
    rw [h1, h2]
    exact xor_double_cancel _ _ _
  have hr : y ^^^ y' = gfMul a' x ^^^ gfMul a' x' := by
    rw [h3, h4]
    exact xor_double_cancel _ _ _
  have ha : a = a' := by
    by_contra hne
    exact rectangle hne hx (hl.symm.trans hr)
  have hb : b = b' := by
    apply (BitVec.xor_right_inj (gfMul a x)).mp
    simpa only [ha] using h1.symm.trans h3
  exact Prod.ext ha hb

lemma common_point_unique {x y x' y' a b a' b' : BitVec 3}
    (hlines : (a, b) ≠ (a', b'))
    (h1 : y = gfMul a x ^^^ b) (h2 : y' = gfMul a x' ^^^ b)
    (h3 : y = gfMul a' x ^^^ b') (h4 : y' = gfMul a' x' ^^^ b') :
    (x, y) = (x', y') := by
  by_contra hpoints
  exact hlines (common_line_unique hpoints h1 h2 h3 h4)

lemma coordinatesNat_injective {u v : ℕ} (hu : u < 64) (hv : v < 64)
    (h : (BitVec.ofNat 3 (u / 8), BitVec.ofNat 3 (u % 8)) =
      (BitVec.ofNat 3 (v / 8), BitVec.ofNat 3 (v % 8))) : u = v := by
  have hx := congrArg (fun p : BitVec 3 × BitVec 3 => p.1.toNat) h
  have hy := congrArg (fun p : BitVec 3 × BitVec 3 => p.2.toNat) h
  simp only [BitVec.toNat_ofNat] at hx hy
  norm_num at hx hy
  omega

def pointCoordinates (p : Fin 128) : BitVec 3 × BitVec 3 :=
  (BitVec.ofNat 3 (p.val / 8), BitVec.ofNat 3 (p.val % 8))

def lineCoordinates (l : Fin 128) : BitVec 3 × BitVec 3 :=
  (BitVec.ofNat 3 ((l.val - 64) / 8), BitVec.ofNat 3 ((l.val - 64) % 8))

lemma pointCoordinates_injective {p q : Fin 128} (hp : p.val < 64) (hq : q.val < 64)
    (h : pointCoordinates p = pointCoordinates q) : p = q := by
  exact Fin.ext (coordinatesNat_injective hp hq h)

lemma lineCoordinates_injective {p q : Fin 128} (hp : 64 ≤ p.val) (hq : 64 ≤ q.val)
    (h : lineCoordinates p = lineCoordinates q) : p = q := by
  have hp' : p.val - 64 < 64 := by have := p.isLt; omega
  have hq' : q.val - 64 < 64 := by have := q.isLt; omega
  have he := coordinatesNat_injective hp' hq' h
  apply Fin.ext
  omega

lemma incidence_of_point_adj {p l : Fin 128} (hp : p.val < 64) (h : graph.Adj p l) :
    incidence p l := by
  change incidence p l ∨ incidence l p at h
  rcases h with h | h
  · exact h
  · have := h.2.1
    omega

lemma incidence_of_line_adj {l p : Fin 128} (hl : 64 ≤ l.val) (h : graph.Adj l p) :
    incidence p l := by
  change incidence l p ∨ incidence p l at h
  rcases h with h | h
  · have := h.1
    omega
  · exact h

lemma common_neighbor_unique {a b u v : Fin 128} (hab : a ≠ b)
    (hau : graph.Adj a u) (hbu : graph.Adj b u)
    (hav : graph.Adj a v) (hbv : graph.Adj b v) : u = v := by
  by_cases ha : a.val < 64
  · have hau' := incidence_of_point_adj ha hau
    have hav' := incidence_of_point_adj ha hav
    by_cases hb : b.val < 64
    · have hbu' := incidence_of_point_adj hb hbu
      have hbv' := incidence_of_point_adj hb hbv
      have hpoints : pointCoordinates a ≠ pointCoordinates b :=
        fun h => hab (pointCoordinates_injective ha hb h)
      have he := common_line_unique hpoints hau'.2.2 hbu'.2.2 hav'.2.2 hbv'.2.2
      exact lineCoordinates_injective hau'.2.1 hav'.2.1 he
    · have hb' : 64 ≤ b.val := by omega
      have hub := incidence_of_line_adj hb' hbu
      have := hau'.2.1
      have := hub.1
      omega
  · have ha' : 64 ≤ a.val := by omega
    have hua := incidence_of_line_adj ha' hau
    have hva := incidence_of_line_adj ha' hav
    by_cases hb : b.val < 64
    · have hbu' := incidence_of_point_adj hb hbu
      have := hua.1
      have := hbu'.2.1
      omega
    · have hb' : 64 ≤ b.val := by omega
      have hub := incidence_of_line_adj hb' hbu
      have hvb := incidence_of_line_adj hb' hbv
      have hlines : lineCoordinates a ≠ lineCoordinates b :=
        fun h => hab (lineCoordinates_injective ha' hb' h)
      have he := common_point_unique hlines hua.2.2 hva.2.2 hub.2.2 hvb.2.2
      exact pointCoordinates_injective hua.1 hva.1 he

lemma no_four_cycle : @PEqualNP.TopForm.NoFourCycle 128 graph graphAdjDecidable := by
  intro a b hab
  apply Finset.card_le_one.mpr
  intro u hu v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
  exact common_neighbor_unique hab hu.1 hu.2 hv.1 hv.2

lemma edge_card :
    letI : DecidableRel graph.Adj := graphAdjDecidable
    graph.edgeFinset.card = 512 := by
  letI : DecidableRel graph.Adj := graphAdjDecidable
  change graph.edgeFinset.card = 512
  have hd : ∀ v : Fin 128, graph.degree v = 8 := degree_eq
  have hs : 1024 = 2 * graph.edgeFinset.card := by
    simpa [hd] using graph.sum_degrees_eq_twice_card_edges
  omega

lemma graph_false_on_witness :
    @PEqualNP.MetaComplexity.NestedCover.graphFun 128 graph graphAdjDecidable ∅ witness = false := by
  have h : ¬ ∃ u v : Fin 128, graph.Adj u v ∧ witness u = true ∧ witness v = true :=
    false_positive.2
  simp [PEqualNP.MetaComplexity.NestedCover.graphFun, h]

lemma does_not_compute_graph : circuitFun 128 circuit ≠
    @PEqualNP.MetaComplexity.NestedCover.graphFun 128 graph graphAdjDecidable ∅ := by
  intro h
  have he := congrFun h witness
  rw [accepted_witness, graph_false_on_witness] at he
  exact Bool.noConfusion he

end GF8Representation

namespace GF8Representation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma circuit_eq_structured (x : Fin 128 → Bool) :
    circuitFun 128 circuit x = GF8Coordinates.structuredEval x := by
  rw [circuit_eval_eq_named_table, table_output, named_output_eq_structured]

lemma circuit_pair_correct (u v : Fin 128) :
    circuitFun 128 circuit (GF8Coordinates.pairInput u v) =
      @decide (adjacent u v) (graphAdjDecidable u v) := by
  rw [circuit_eq_structured]
  exact GF8Coordinates.structured_pair_correct u v

lemma circuit_singleton_false (u : Fin 128) :
    circuitFun 128 circuit (fun w => decide (w = u)) = false := by
  rw [circuit_eq_structured]
  exact GF8Coordinates.structured_singleton u

lemma circuit_empty_false : circuitFun 128 circuit (fun _ => false) = false := by
  rw [circuit_eq_structured]
  exact GF8Coordinates.structured_empty

end GF8Representation

namespace GF8PairDomain

open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3566.GF8Coordinates

def support (x : Fin 128 → Bool) : Finset (Fin 128) :=
  Finset.univ.filter (fun v => x v = true)

lemma mem_support (x : Fin 128 → Bool) (v : Fin 128) :
    v ∈ support x ↔ x v = true := by
  simp [support]

lemma eq_indicator_of_support_eq (x : Fin 128 → Bool) (s : Finset (Fin 128))
    (h : support x = s) : x = (fun w => decide (w ∈ s)) := by
  funext w
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [← mem_support, h]

lemma support_cases (x : Fin 128 → Bool) (hx : (support x).card ≤ 2) :
    x = (fun _ => false) ∨
      (∃ u : Fin 128, x = (fun w => decide (w = u))) ∨
      (∃ u v : Fin 128, x = pairInput u v) := by
  have hc : (support x).card = 0 ∨ (support x).card = 1 ∨ (support x).card = 2 := by
    omega
  rcases hc with hc | hc | hc
  · left
    simpa using eq_indicator_of_support_eq x ∅ (Finset.card_eq_zero.mp hc)
  · right
    left
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hc
    refine ⟨u, ?_⟩
    simpa using eq_indicator_of_support_eq x {u} hu
  · right
    right
    obtain ⟨u, v, _, huv⟩ := Finset.card_eq_two.mp hc
    refine ⟨u, v, ?_⟩
    calc
      x = (fun w => decide (w ∈ ({u, v} : Finset (Fin 128)))) :=
        eq_indicator_of_support_eq x {u, v} huv
      _ = pairInput u v := by
        funext w
        simp only [Finset.mem_insert, Finset.mem_singleton, pairInput]

lemma graphFun_empty (G : SimpleGraph (Fin 128)) [DecidableRel G.Adj] :
    graphFun G ∅ (fun _ => false) = false := by
  simp [graphFun]

lemma graphFun_singleton (G : SimpleGraph (Fin 128)) [DecidableRel G.Adj]
    (u : Fin 128) : graphFun G ∅ (fun w => decide (w = u)) = false := by
  simp [graphFun]

lemma graphFun_pair (G : SimpleGraph (Fin 128)) [DecidableRel G.Adj]
    (u v : Fin 128) : graphFun G ∅ (pairInput u v) = decide (G.Adj u v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
  simp
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (G.loopless.irrefl _ hab)
    · exact hab
    · exact G.adj_symm hab
    · exact False.elim (G.loopless.irrefl _ hab)
  · intro huv
    refine ⟨u, v, huv, ?_, ?_⟩ <;> simp [pairInput]

lemma agrees_on_support_le_two (G : SimpleGraph (Fin 128)) [DecidableRel G.Adj]
    (f : (Fin 128 → Bool) → Bool)
    (hzero : f (fun _ => false) = false)
    (hone : ∀ u : Fin 128, f (fun w => decide (w = u)) = false)
    (htwo : ∀ u v : Fin 128, f (pairInput u v) = decide (G.Adj u v))
    (x : Fin 128 → Bool) (hx : (support x).card ≤ 2) :
    f x = graphFun G ∅ x := by
  rcases support_cases x hx with rfl | ⟨u, rfl⟩ | ⟨u, v, rfl⟩
  · rw [hzero, graphFun_empty]
  · rw [hone, graphFun_singleton]
  · rw [htwo, graphFun_pair]

lemma structured_agrees_on_support_le_two (G : SimpleGraph (Fin 128))
    [DecidableRel G.Adj]
    (hG : ∀ u v : Fin 128, G.Adj u v ↔ adjacent u v)
    (x : Fin 128 → Bool) (hx : (support x).card ≤ 2) :
    structuredEval x = graphFun G ∅ x := by
  apply agrees_on_support_le_two G structuredEval structured_empty structured_singleton ?_ x hx
  intro u v
  rw [structured_pair_correct]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (hG u v).symm

end GF8PairDomain

namespace GF8Representation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma circuit_correct_on_support_le_two (x : Fin 128 → Bool)
    (hx : (GF8PairDomain.support x).card ≤ 2) :
    circuitFun 128 circuit x =
      @NestedCover.graphFun 128 graph graphAdjDecidable ∅ x := by
  rw [circuit_eq_structured]
  exact @GF8PairDomain.structured_agrees_on_support_le_two graph graphAdjDecidable
    (fun _ _ => Iff.rfl) x hx

lemma size_below_edge_cover_bound :
    letI : DecidableRel graph.Adj := graphAdjDecidable
    circuit.size < graph.edgeFinset.card + pointCover.card - 1 := by
  letI : DecidableRel graph.Adj := graphAdjDecidable
  change circuit.size < graph.edgeFinset.card + pointCover.card - 1
  have he : graph.edgeFinset.card = 512 := edge_card
  rw [size_eq, he, pointCover_card]
  decide

end GF8Representation

end PEqualNP.Outside.L_meta_3566
