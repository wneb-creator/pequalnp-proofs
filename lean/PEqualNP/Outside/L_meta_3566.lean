import Mathlib.Tactic
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

namespace GF8Representation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

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

end PEqualNP.Outside.L_meta_3566
