import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

namespace PEqualNP.Outside.L_meta_1904_aux

namespace Builder

-- Circuit builder adapted from L_meta_1003.lean (H926, H926.EdgeUpper), strengthened to carry
-- monotonicity (AND/OR, fan-in two) and an upper bound on every AND gate's wire.

open PEqualNP PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

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

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

def OkM (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Bld (n : ℕ) (P : (Fin n → Bool) → Prop) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, OkM g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ (∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)) ∧
    ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD (m + j) false = true → P (fun i => w.getD i false)

lemma bld_mono {n : ℕ} {P} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n P F s)
    (hs : s ≤ s') : Bld n P F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev, ha⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev, ha⟩

lemma bld_congr {n : ℕ} {P} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n P F s)
    (e : ∀ x, F x = H x) : Bld n P H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev, ha⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e], ha⟩

lemma bld_var {n : ℕ} {P} (i : Fin n) : Bld n P (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_, ?_⟩
  · intro w _
    simp [wiresFrom]
  · intro j g hj
    simp at hj

lemma bld_bin {n : ℕ} {P} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n P F s1) (h2 : Bld n P H s2)
    (hA : op = GateOp.and → ∀ x, c (F x) (H x) = true → P x) :
    Bld n P (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1, ha1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2, ha2⟩ := h2 (m + gs1.length) (by omega)
  have main : ∀ w : List Bool, w.length = m →
      (wiresFrom gs2 (wiresFrom gs1 w)).length = m + gs1.length + gs2.length ∧
      (wiresFrom (gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩]) w)
        = wiresFrom gs2 (wiresFrom gs1 w) ++
          [c (F (fun i : Fin n => w.getD i false)) (H (fun i : Fin n => w.getD i false))] ∧
      (fun i : Fin n => (wiresFrom gs1 w).getD i false) = (fun i : Fin n => w.getD i false) := by
    intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have hvw : (fun i : Fin n => v.getD i false) = (fun i : Fin n => w.getD i false) := by
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    refine ⟨lu, ?_, hvw⟩
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv, hvw]
    rw [e1, e2]
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [OkM, h]
  · simp; omega
  · simp; omega
  · intro w hw
    obtain ⟨lu, hm2, _⟩ := main w hw
    rw [hm2, ← lu, getD_snoc_eq]
  · intro j g hj hop' w hw hval
    obtain ⟨lu, hm2, hvw⟩ := main w hw
    rw [hm2] at hval
    rcases lt_or_ge j gs1.length with hj1 | hj1
    · have hg : gs1[j]? = some g := by
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left hj1] at hj
        exact hj
      apply ha1 j g hg hop' w hw
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_wiresFrom _ _ _ (by
        rw [length_wiresFrom, hw]; omega)] at hval
      exact hval
    · rcases lt_or_ge j (gs1.length + gs2.length) with hj2 | hj2
      · obtain ⟨j', rfl⟩ : ∃ j', j = gs1.length + j' := ⟨j - gs1.length, by omega⟩
        have hg : gs2[j']? = some g := by
          rw [List.getElem?_append_left (by simp; omega),
            List.getElem?_append_right (by omega)] at hj
          simpa using hj
        have lv : (wiresFrom gs1 w).length = m + gs1.length := by rw [length_wiresFrom, hw]
        have := ha2 j' g hg hop' (wiresFrom gs1 w) lv
        rw [hvw] at this
        apply this
        rw [getD_snoc_ne _ _ _ _ (by omega)] at hval
        rw [← add_assoc] at hval
        exact hval
      · have hjeq : j = gs1.length + gs2.length := by
          by_contra hne
          have : (gs1 ++ gs2 ++ [(⟨op, [o1, o2]⟩ : Gate)])[j]? = none :=
            List.getElem?_eq_none (by simp; omega)
          rw [this] at hj
          simp at hj
        subst hjeq
        have hg : g = ⟨op, [o1, o2]⟩ := by
          rw [List.getElem?_append_right (by simp)] at hj
          simp at hj
          exact hj.symm
        subst hg
        rw [show m + (gs1.length + gs2.length) = (wiresFrom gs2 (wiresFrom gs1 w)).length by
          omega, getD_snoc_eq] at hval
        exact hA hop' _ hval

lemma bld_or {n : ℕ} {P} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n P F s1)
    (h2 : Bld n P H s2) : Bld n P (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2
    (by intro h; cases h)

lemma bld_and {n : ℕ} {P} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n P F s1)
    (h2 : Bld n P H s2) (hP : ∀ x, F x = true → H x = true → P x) :
    Bld n P (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2
    (by
      intro _ x hx
      simp only [Bool.and_eq_true] at hx
      exact hP x hx.1 hx.2)

lemma bld_anyList {n : ℕ} {P} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n P (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var (P := P) v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

lemma bld_anyFinset {n : ℕ} {P} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n P (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
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
lemma bld_edges (n : ℕ) (P : (Fin n → Bool) → Prop) (T : Finset (Fin n)) :
    ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) → (∀ x, (∃ e ∈ E, ∀ v ∈ e, x v = true) → P x) →
    Bld n P (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc _
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc hPE
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
    have p2 : ∀ x, (∃ e ∈ E2, ∀ v ∈ e, x v = true) → P x := by
      rintro x ⟨e, he, h⟩
      exact hPE x ⟨e, (Finset.mem_filter.1 he).1, h⟩
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have star : E1.Nonempty → Bld n P (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSc : S.card ≤ E1.card := by
        refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
        · intro v hv
          simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
          exact hv
        · intro a _ b _ hab
          exact Sym2.congr_right.1 hab
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var (P := P) t) (bld_anyFinset S hSne) (by
        intro x ht hv
        rw [decide_eq_true_iff] at hv
        obtain ⟨v, hv, hxv⟩ := hv
        refine hPE x ⟨s(t, v), (Finset.mem_filter.1 (Finset.mem_filter.1 hv).2).1, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption)
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
      · have := bld_or (star h1) (ih E2 h2 c2 p2)
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
      refine bld_congr (bld_mono (ih E2 h2 c2 p2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (hc : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
    ∃ C : Circuit, Monotone2 C ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x)
        = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) ∧
      C.size ≤ G.edgeFinset.card + T.card - 1 ∧
      ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and → ∀ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD (n + j) false = true →
          ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  by_cases hE : ∃ i j : Fin n, G.Adj i j
  · obtain ⟨i0, j0, h0⟩ := hE
    have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
    have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
      intro e
      refine Sym2.ind (fun a b => ?_) e
      intro he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases hc a b he with h | h
      · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
      · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
    have conv : ∀ x : Fin n → Bool, (∃ e ∈ G.edgeFinset, ∀ v ∈ e, x v = true) ↔
        (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
      intro x
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
    have hb := bld_edges n (fun x => ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) T
      G.edgeFinset hne cov (fun x h => (conv x).1 h)
    obtain ⟨gs, out, ok, len, _, ev, ha⟩ := hb n le_rfl
    have hx : ∀ x : Fin n → Bool, (fun i : Fin n => (List.ofFn x).getD i false) = x := by
      intro x; funext i; exact getD_ofFn x i
    refine ⟨⟨gs, out⟩, ok, ?_, len, ?_⟩
    · intro x
      have e := ev (List.ofFn x) (by simp)
      rw [hx] at e
      simp only [Circuit.eval, wires_eq, e]
      exact decide_eq_decide.2 (conv x)
    · intro j g hj hop x hv
      have := ha j g hj hop (List.ofFn x) (by simp) hv
      rw [hx] at this
      exact this
  · refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_⟩
    · intro g hg; simp at hg
    · intro x
      have : ¬ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
        rintro ⟨u, v, h, _⟩; exact hE ⟨u, v, h⟩
      simp only [Circuit.eval, Circuit.wires, List.foldl_nil, this, decide_false]
      exact List.getD_eq_default _ _ (by simp)
    · simp [Circuit.size]
    · intro j g hj; simp at hj


end Builder

namespace Selection

lemma exists_minimum_for_property (P : Circuit → Prop) (h : ∃ C, P C) :
    ∃ C, P C ∧ ∀ D, P D → C.size ≤ D.size := by
  classical
  have hs : ∃ s : ℕ, ∃ C, P C ∧ C.size = s := by
    obtain ⟨C, hC⟩ := h
    exact ⟨C.size, C, hC, rfl⟩
  obtain ⟨C, hC, hsize⟩ := Nat.find_spec hs
  refine ⟨C, hC, ?_⟩
  intro D hD
  rw [hsize]
  exact Nat.find_min' hs ⟨D, hD, rfl⟩

lemma exists_minimum_monotone {n : ℕ} (f : (Fin n → Bool) → Bool)
    (h : ∃ C, Monotone2 C ∧ ∀ x, C.eval (List.ofFn x) = f x) :
    ∃ C, Monotone2 C ∧ (∀ x, C.eval (List.ofFn x) = f x) ∧
      ∀ D, Monotone2 D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size := by
  obtain ⟨C, hC, hmin⟩ := exists_minimum_for_property _ h
  exact ⟨C, hC.1, hC.2, fun D hD hDf => hmin D ⟨hD, hDf⟩⟩

lemma exists_minimum_monotone_with_property {n : ℕ} (f : (Fin n → Bool) → Bool)
    (P : Circuit → Prop)
    (h : ∃ C, Monotone2 C ∧ (∀ x, C.eval (List.ofFn x) = f x) ∧ P C) :
    ∃ C, Monotone2 C ∧ (∀ x, C.eval (List.ofFn x) = f x) ∧ P C ∧
      ∀ D, Monotone2 D → (∀ x, D.eval (List.ofFn x) = f x) → P D → C.size ≤ D.size := by
  obtain ⟨C, hC, hmin⟩ := exists_minimum_for_property _ h
  exact ⟨C, hC.1, hC.2.1, hC.2.2, fun D hD hDf hDP => hmin D ⟨hD, hDf, hDP⟩⟩

lemma exists_minimum_with_property_of_nonincreasing_normalization
    (P Q : Circuit → Prop) (h : ∃ C, P C)
    (hnorm : ∀ C, P C → ∃ D, P D ∧ Q D ∧ D.size ≤ C.size) :
    ∃ C, P C ∧ (∀ D, P D → C.size ≤ D.size) ∧ Q C := by
  obtain ⟨C, hC, hmin⟩ := exists_minimum_for_property P h
  obtain ⟨D, hD, hQ, hsize⟩ := hnorm C hC
  exact ⟨D, hD, fun E hE => hsize.trans (hmin E hE), hQ⟩

lemma exists_minimum_with_property_of_strict_descent
    (P Q : Circuit → Prop) (h : ∃ C, P C)
    (hdesc : ∀ C, P C → ¬ Q C → ∃ D, P D ∧ D.size < C.size) :
    ∃ C, P C ∧ (∀ D, P D → C.size ≤ D.size) ∧ Q C := by
  classical
  obtain ⟨C, hC, hmin⟩ := exists_minimum_for_property P h
  refine ⟨C, hC, hmin, ?_⟩
  by_contra hQ
  obtain ⟨D, hD, hsize⟩ := hdesc C hC hQ
  exact (Nat.not_lt_of_ge (hmin D hD)) hsize

lemma exists_lexicographic_minimum (P : Circuit → Prop) (rank : Circuit → ℕ)
    (h : ∃ C, P C) :
    ∃ C, P C ∧ (∀ D, P D → C.size ≤ D.size) ∧
      ∀ D, P D → D.size = C.size → rank C ≤ rank D := by
  classical
  obtain ⟨C, hC, hmin⟩ := exists_minimum_for_property P h
  have hs : ∃ r : ℕ, ∃ D, P D ∧ D.size = C.size ∧ rank D = r :=
    ⟨rank C, C, hC, rfl, rfl⟩
  obtain ⟨D, hD, hsize, hrank⟩ := Nat.find_spec hs
  refine ⟨D, hD, ?_, ?_⟩
  · intro E hE
    rw [hsize]
    exact hmin E hE
  · intro E hE hED
    rw [hrank]
    exact Nat.find_min' hs ⟨E, hE, hED.trans hsize, rfl⟩

lemma exists_minimum_with_property_of_lexicographic_descent
    (P Q : Circuit → Prop) (rank : Circuit → ℕ) (h : ∃ C, P C)
    (hdesc : ∀ C, P C → ¬ Q C → ∃ D, P D ∧ D.size ≤ C.size ∧
      (D.size = C.size → rank D < rank C)) :
    ∃ C, P C ∧ (∀ D, P D → C.size ≤ D.size) ∧ Q C := by
  classical
  obtain ⟨C, hC, hmin, hrank⟩ := exists_lexicographic_minimum P rank h
  refine ⟨C, hC, hmin, ?_⟩
  by_contra hQ
  obtain ⟨D, hD, hsize, hless⟩ := hdesc C hC hQ
  have heq := Nat.le_antisymm hsize (hmin D hD)
  exact (Nat.not_lt_of_ge (hrank D hD heq)) (hless heq)

lemma exists_minimum_with_property_iff_nonincreasing_normalization
    (P Q : Circuit → Prop) (h : ∃ C, P C) :
    (∃ C, P C ∧ (∀ D, P D → C.size ≤ D.size) ∧ Q C) ↔
      (∀ C, P C → ∃ D, P D ∧ Q D ∧ D.size ≤ C.size) := by
  constructor
  · rintro ⟨D, hD, hmin, hQ⟩ C hC
    exact ⟨D, hD, hQ, hmin C hC⟩
  · exact exists_minimum_with_property_of_nonincreasing_normalization P Q h

lemma exists_minimum_with_property_of_matching_bounds
    (P Q : Circuit → Prop) (bound : ℕ)
    (hupper : ∃ C, P C ∧ Q C ∧ C.size ≤ bound)
    (hlower : ∀ C, P C → bound ≤ C.size) :
    ∃ C, P C ∧ (∀ D, P D → C.size ≤ D.size) ∧ Q C := by
  obtain ⟨C, hC, hQ, hsize⟩ := hupper
  exact ⟨C, hC, fun D hD => hsize.trans (hlower D hD), hQ⟩

def EdgeCorrect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
    decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)

def EdgeSafe {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
    ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = true →
      ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true

lemma exists_safe_minimum_of_cover_lower_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (T : Finset (Fin n))
    (builder : ∃ C, Monotone2 C ∧ EdgeCorrect G C ∧
      C.size ≤ G.edgeFinset.card + T.card - 1 ∧ EdgeSafe G C)
    (lower : ∀ C, Monotone2 C → EdgeCorrect G C →
      G.edgeFinset.card + T.card - 1 ≤ C.size) :
    ∃ C, Monotone2 C ∧ EdgeCorrect G C ∧
      (∀ D, Monotone2 D → EdgeCorrect G D → C.size ≤ D.size) ∧ EdgeSafe G C := by
  obtain ⟨C, hmono, hcorrect, hsize, hsafe⟩ := builder
  exact ⟨C, hmono, hcorrect, fun D hD hcorrectD =>
    hsize.trans (lower D hD hcorrectD), hsafe⟩


end Selection

lemma junk_subset_of_pointwise_decrease {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (hsize : D.size ≤ C.size)
    (hops : ∀ j, j < D.size → (gateAt D j).op = GateOp.and →
      (gateAt C j).op = GateOp.and)
    (hval : ∀ j, j < D.size → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C j x = true) :
    TopForm.junk G D ⊆ TopForm.junk G C := by
  intro j hj
  have hd : IsDirtyAnd n G D j := (Finset.mem_filter.mp hj).2
  obtain ⟨hop, hj, x, hx, hf⟩ := hd
  have hjD : j < D.size := hj
  have hjC : j < C.gates.length := lt_of_lt_of_le hjD hsize
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjC,
    hops j hjD hop, hjC, x, hval j hjD x hf hx, hf⟩

lemma junk_ssubset_of_pointwise_repair {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (hsize : D.size ≤ C.size)
    (hops : ∀ j, j < D.size → (gateAt D j).op = GateOp.and →
      (gateAt C j).op = GateOp.and)
    (hval : ∀ j, j < D.size → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C j x = true)
    (j : ℕ) (hdirty : IsDirtyAnd n G C j) (hclean : TopForm.BelowF G D j) :
    TopForm.junk G D ⊂ TopForm.junk G C := by
  classical
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨junk_subset_of_pointwise_decrease G C D hsize hops hval, ?_⟩
  intro heq
  have hj : j ∈ TopForm.junk G C := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdirty.2.1, hdirty⟩
  rw [← heq] at hj
  have hd := (Finset.mem_filter.mp hj).2
  obtain ⟨x, hx, hf⟩ := hd.2.2
  have ht := hclean x hx
  rw [hf] at ht
  cases ht

lemma junk_card_lt_of_pointwise_repair {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (hsize : D.size ≤ C.size)
    (hops : ∀ j, j < D.size → (gateAt D j).op = GateOp.and →
      (gateAt C j).op = GateOp.and)
    (hval : ∀ j, j < D.size → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C j x = true)
    (j : ℕ) (hdirty : IsDirtyAnd n G C j) (hclean : TopForm.BelowF G D j) :
    (TopForm.junk G D).card < (TopForm.junk G C).card :=
  Finset.card_lt_card (junk_ssubset_of_pointwise_repair G C D hsize hops hval j hdirty hclean)

lemma gateAt_patch_op (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hop : h.op = GateOp.and → g.op = GateOp.and) (j : ℕ) :
    (gateAt ⟨pre ++ h :: post, out⟩ j).op = GateOp.and →
      (gateAt ⟨pre ++ g :: post, out⟩ j).op = GateOp.and := by
  by_cases hj : j < pre.length
  · simp only [gateAt, List.getD_append _ _ _ _ hj]
    exact id
  · have hj' : pre.length ≤ j := Nat.le_of_not_gt hj
    simp only [gateAt, List.getD_append_right _ _ _ _ hj']
    by_cases heq : j - pre.length = 0
    · simp only [heq, List.getD_cons_zero]
      exact hop
    · obtain ⟨k, hk⟩ : ∃ k, j - pre.length = k + 1 :=
        ⟨j - pre.length - 1, by omega⟩
      simp only [hk, List.getD_cons_succ]
      exact id

lemma junk_patch_ssubset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hop : h.op = GateOp.and → g.op = GateOp.and)
    (hval : ∀ j, j < pre.length + 1 + post.length → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false →
      gateVal n ⟨pre ++ h :: post, out⟩ j x = true →
      gateVal n ⟨pre ++ g :: post, out⟩ j x = true)
    (hdirty : IsDirtyAnd n G ⟨pre ++ g :: post, out⟩ pre.length)
    (hclean : TopForm.BelowF G ⟨pre ++ h :: post, out⟩ pre.length) :
    TopForm.junk G ⟨pre ++ h :: post, out⟩ ⊂
      TopForm.junk G ⟨pre ++ g :: post, out⟩ := by
  apply junk_ssubset_of_pointwise_repair G _ _
    (by simp [Circuit.size])
    (fun j _ => gateAt_patch_op pre post g h out hop j)
    (fun j hj => hval j (by simpa [Circuit.size, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hj)) pre.length hdirty hclean

noncomputable def dirtyEvents {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) : Finset (ℕ × (Fin n → Bool)) := by
  classical
  exact ((Finset.range C.size) ×ˢ Finset.univ).filter fun p =>
    (gateAt C p.1).op = GateOp.and ∧ gateVal n C p.1 p.2 = true ∧ graphFun G ∅ p.2 = false

lemma dirtyEvents_subset_of_pointwise_decrease {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (hsize : D.size ≤ C.size)
    (hops : ∀ j, j < D.size → (gateAt D j).op = GateOp.and →
      (gateAt C j).op = GateOp.and)
    (hval : ∀ j, j < D.size → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C j x = true) :
    dirtyEvents G D ⊆ dirtyEvents G C := by
  classical
  intro p hp
  obtain ⟨hpair, hop, hx, hf⟩ := Finset.mem_filter.mp hp
  have hj : p.1 < D.size := Finset.mem_range.mp (Finset.mem_product.mp hpair).1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le hj hsize),
    Finset.mem_univ _⟩, hops p.1 hj hop, hval p.1 hj p.2 hf hx, hf⟩

lemma dirtyEvents_ssubset_of_killed_activation {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (hsub : dirtyEvents G D ⊆ dirtyEvents G C)
    (j : ℕ) (hj : j < C.size) (hop : (gateAt C j).op = GateOp.and)
    (x : Fin n → Bool) (hx : gateVal n C j x = true) (hf : graphFun G ∅ x = false)
    (hkill : gateVal n D j x = false) :
    dirtyEvents G D ⊂ dirtyEvents G C := by
  classical
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro heq
  have hmem : (j, x) ∈ dirtyEvents G C :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hj, Finset.mem_univ x⟩, hop, hx, hf⟩
  rw [← heq] at hmem
  have ht := (Finset.mem_filter.mp hmem).2.2.1
  rw [hkill] at ht
  cases ht

lemma dirtyEvents_card_lt_of_pointwise_decrease {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (hsize : D.size ≤ C.size)
    (hops : ∀ j, j < D.size → (gateAt D j).op = GateOp.and →
      (gateAt C j).op = GateOp.and)
    (hval : ∀ j, j < D.size → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C j x = true)
    (j : ℕ) (hj : j < C.size) (hop : (gateAt C j).op = GateOp.and)
    (x : Fin n → Bool) (hx : gateVal n C j x = true) (hf : graphFun G ∅ x = false)
    (hkill : gateVal n D j x = false) :
    (dirtyEvents G D).card < (dirtyEvents G C).card := by
  exact Finset.card_lt_card (dirtyEvents_ssubset_of_killed_activation G C D
    (dirtyEvents_subset_of_pointwise_decrease G C D hsize hops hval) j hj hop x hx hf hkill)



open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

def negativeEvents {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Finset (ℕ × (Fin n → Bool)) :=
  ((Finset.range C.size).product Finset.univ).filter fun p =>
    graphFun G ∅ p.2 = false ∧ gateVal n C p.1 p.2 = true

lemma mem_negativeEvents {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {j : ℕ} {x : Fin n → Bool} :
    (j, x) ∈ negativeEvents G C ↔
      j < C.size ∧ graphFun G ∅ x = false ∧ gateVal n C j x = true := by
  simp [negativeEvents]

lemma negativeEvents_reindex_injective {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {D : Circuit} {rename : ℕ → ℕ}
    (hinj : Set.InjOn rename (↑(Finset.range D.size) : Set ℕ)) :
    Set.InjOn (fun p : ℕ × (Fin n → Bool) => (rename p.1, p.2))
      (↑(negativeEvents G D) : Set (ℕ × (Fin n → Bool))) := by
  intro p hp q hq heq
  apply Prod.ext
  · apply hinj
    · exact Finset.mem_range.mpr (mem_negativeEvents.mp hp).1
    · exact Finset.mem_range.mpr (mem_negativeEvents.mp hq).1
    · exact congrArg Prod.fst heq
  · exact (Prod.mk.inj heq).2

lemma negativeEvents_card_le_of_injective_map {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C D : Circuit} (rename : ℕ → ℕ)
    (hinj : Set.InjOn rename (↑(Finset.range D.size) : Set ℕ))
    (hmap : ∀ j x, (j, x) ∈ negativeEvents G D →
      (rename j, x) ∈ negativeEvents G C) :
    (negativeEvents G D).card ≤ (negativeEvents G C).card := by
  apply Finset.card_le_card_of_injOn (fun p => (rename p.1, p.2))
  · intro p hp
    exact hmap p.1 p.2 hp
  · exact negativeEvents_reindex_injective hinj

lemma negativeEvents_card_lt_of_injective_map {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C D : Circuit} (rename : ℕ → ℕ)
    (hinj : Set.InjOn rename (↑(Finset.range D.size) : Set ℕ))
    (hmap : ∀ j x, (j, x) ∈ negativeEvents G D →
      (rename j, x) ∈ negativeEvents G C)
    (j : ℕ) (x : Fin n → Bool) (hold : (j, x) ∈ negativeEvents G C)
    (hmiss : ∀ k, k < D.size → rename k = j → gateVal n D k x = false) :
    (negativeEvents G D).card < (negativeEvents G C).card := by
  have hle : (negativeEvents G D).card ≤ ((negativeEvents G C).erase (j, x)).card := by
    apply Finset.card_le_card_of_injOn (fun p => (rename p.1, p.2))
    · intro p hp
      refine Finset.mem_erase.mpr ⟨?_, hmap p.1 p.2 hp⟩
      intro heq
      have hsize := (mem_negativeEvents.mp hp).1
      have hactive := (mem_negativeEvents.mp hp).2.2
      have hfalse := hmiss p.1 hsize (congrArg Prod.fst heq)
      rw [congrArg Prod.snd heq] at hactive
      exact Bool.false_ne_true (hfalse.symm.trans hactive)
    · exact negativeEvents_reindex_injective hinj
  exact hle.trans_lt (Finset.card_erase_lt_of_mem hold)

lemma negativeEvents_card_le_of_reindexing {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C D : Circuit} (rename : ℕ → ℕ)
    (hinj : Set.InjOn rename (↑(Finset.range D.size) : Set ℕ))
    (hindex : ∀ j, j < D.size → rename j < C.size)
    (hactive : ∀ j, j < D.size → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C (rename j) x = true) :
    (negativeEvents G D).card ≤ (negativeEvents G C).card := by
  apply negativeEvents_card_le_of_injective_map rename hinj
  intro j x hevent
  obtain ⟨hj, hx, hv⟩ := mem_negativeEvents.mp hevent
  exact mem_negativeEvents.mpr ⟨hindex j hj, hx, hactive j hj x hx hv⟩

lemma negativeEvents_card_lt_of_reindexing {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C D : Circuit} (rename : ℕ → ℕ)
    (hinj : Set.InjOn rename (↑(Finset.range D.size) : Set ℕ))
    (hindex : ∀ j, j < D.size → rename j < C.size)
    (hactive : ∀ j, j < D.size → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C (rename j) x = true)
    (j : ℕ) (x : Fin n → Bool) (hj : j < C.size)
    (hx : graphFun G ∅ x = false) (hv : gateVal n C j x = true)
    (hmiss : ∀ k, k < D.size → rename k = j → gateVal n D k x = false) :
    (negativeEvents G D).card < (negativeEvents G C).card := by
  apply negativeEvents_card_lt_of_injective_map rename hinj ?_ j x
    (mem_negativeEvents.mpr ⟨hj, hx, hv⟩) hmiss
  intro k y hevent
  obtain ⟨hk, hy, hw⟩ := mem_negativeEvents.mp hevent
  exact mem_negativeEvents.mpr ⟨hindex k hk, hy, hactive k hk y hy hw⟩


namespace InputSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n : ℕ}

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def SupportsImplication (x y : Fin n → Bool) (L : List (Finset (Fin n)))
    (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = true → y i = true) →
      w.getD j false = true → w'.getD j false = true

lemma gate_implication (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg
  · simp only [hg, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro hall i hi
    exact h i hi (hall i hi)
  · simp only [hg, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hval⟩
    exact ⟨i, hi, h i hi hval⟩

lemma implication_wiresFrom (x y : Fin n → Bool) (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), SupportsImplication x y L w w' →
      SupportsImplication x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (fun a ha => hmono a (List.mem_cons_of_mem _ ha)) (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      apply gate_implication g (hmono g List.mem_cons_self)
      intro a ha hval
      apply h3 a ?_ hval
      intro i hi
      exact hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩)
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

lemma implication_inputs (x y : Fin n → Bool) :
    SupportsImplication x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = true → y ⟨j, hjn⟩ = true := hj _ (by simp [inputSupps, hjn])
    simpa [hjn] using hx
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

lemma cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

lemma small_input_support {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    ∃ S : Finset (Fin n), S.card ≤ C.size + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = true → y i = true) →
        C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  let S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅
  refine ⟨S, ?_, ?_⟩
  · have hc := cnt_suppsFrom C.gates 0 (inputSupps n)
      (fun g hg => (hmono g hg).2) cnt_inputs {C.output}
    simpa only [Finset.singleton_biUnion, Finset.card_singleton, zero_add, S, Circuit.size] using hc
  · intro x y hS hx
    have himp := implication_wiresFrom x y C.gates
      (fun g hg => by simpa using (hmono g hg).1) _ _ _ (implication_inputs x y)
    exact himp.2.2 C.output hS hx

lemma separation_of_support {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (hsupport : ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = true → y i = true) →
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true)
    (x y : Fin n → Bool) (hx : C.eval (List.ofFn x) = true)
    (hy : C.eval (List.ofFn y) = false) :
    ∃ i ∈ S, x i = true ∧ y i = false := by
  classical
  have hnot : ¬ ∀ i ∈ S, x i = true → y i = true := by
    intro himp
    have htrue := hsupport x y himp hx
    rw [hy] at htrue
    contradiction
  push Not at hnot
  obtain ⟨i, hi, hxi, hyi⟩ := hnot
  exact ⟨i, hi, hxi, Bool.eq_false_iff.mpr hyi⟩

lemma small_input_separating_support {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    ∃ S : Finset (Fin n), S.card ≤ C.size + 1 ∧
      ∀ x y : Fin n → Bool, C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = false →
        ∃ i ∈ S, x i = true ∧ y i = false := by
  obtain ⟨S, hcard, hsupport⟩ := small_input_support C hmono
  exact ⟨S, hcard, separation_of_support C S hsupport⟩


end InputSupport

namespace DNF

open PEqualNP.CircuitLowerBounds

abbrev Terms (n : ℕ) := Finset (Finset (Fin n))

def eval {n : ℕ} (D : Terms n) (x : Fin n → Bool) : Bool :=
  decide (∃ t ∈ D, ∀ i ∈ t, x i = true)

def prod {n : ℕ} (A B : Terms n) : Terms n :=
  A.biUnion fun s => B.image fun t => s ∪ t

lemma eval_empty {n : ℕ} (x : Fin n → Bool) : eval ∅ x = false := by
  simp [eval]

lemma eval_one {n : ℕ} (x : Fin n → Bool) : eval {∅} x = true := by
  simp [eval]

lemma eval_var {n : ℕ} (i : Fin n) (x : Fin n → Bool) : eval {{i}} x = x i := by
  cases h : x i <;> simp [eval, h]

lemma eval_union {n : ℕ} (A B : Terms n) (x : Fin n → Bool) :
    eval (A ∪ B) x = (eval A x || eval B x) := by
  apply Bool.eq_iff_iff.mpr
  simp [eval, Finset.mem_union, or_and_right, exists_or]

lemma eval_prod {n : ℕ} (A B : Terms n) (x : Fin n → Bool) :
    eval (prod A B) x = (eval A x && eval B x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [eval, decide_eq_true_eq, Bool.and_eq_true, prod, Finset.mem_biUnion,
    Finset.mem_image]
  constructor
  · rintro ⟨u, ⟨s, hs, t, ht, rfl⟩, hu⟩
    exact ⟨⟨s, hs, fun i hi => hu i (Finset.mem_union_left _ hi)⟩,
      ⟨t, ht, fun i hi => hu i (Finset.mem_union_right _ hi)⟩⟩
  · rintro ⟨⟨s, hs, hxs⟩, ⟨t, ht, hxt⟩⟩
    refine ⟨s ∪ t, ⟨s, hs, t, ht, rfl⟩, ?_⟩
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hxs i hi
    · exact hxt i hi

def gate {n : ℕ} (op : GateOp) (ins : List (Terms n)) : Terms n :=
  match op with
  | GateOp.and => ins.foldr prod {∅}
  | GateOp.or => ins.foldr (· ∪ ·) ∅
  | _ => ∅

lemma eval_and_list {n : ℕ} (ins : List (Terms n)) (x : Fin n → Bool) :
    eval (ins.foldr prod {∅}) x = (ins.map fun D => eval D x).all id := by
  induction ins with
  | nil => simp [eval_one]
  | cons D ins ih => simp [List.foldr_cons, eval_prod, ih]

lemma eval_or_list {n : ℕ} (ins : List (Terms n)) (x : Fin n → Bool) :
    eval (ins.foldr (· ∪ ·) ∅) x = (ins.map fun D => eval D x).any id := by
  induction ins with
  | nil => simp [eval_empty]
  | cons D ins ih => simp [List.foldr_cons, eval_union, ih]

lemma eval_gate {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List (Terms n)) (x : Fin n → Bool) :
    eval (gate op ins) x = op.eval (ins.map fun D => eval D x) := by
  rcases hop with rfl | rfl
  · exact eval_and_list ins x
  · exact eval_or_list ins x


def step {n : ℕ} (w : List (Terms n)) (g : Gate) : List (Terms n) :=
  w ++ [gate g.op (g.inputs.map fun i => w.getD i ∅)]

def run {n : ℕ} (gs : List Gate) (w : List (Terms n)) : List (Terms n) :=
  gs.foldl step w

lemma eval_getD {n : ℕ} (w : List (Terms n)) (i : ℕ) (x : Fin n → Bool) :
    eval (w.getD i ∅) x = (w.map fun D => eval D x).getD i false := by
  induction w generalizing i with
  | nil => simp [eval_empty]
  | cons D w ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

lemma step_sound {n : ℕ} (w : List (Terms n)) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (x : Fin n → Bool) :
    (step w g).map (fun D => eval D x) =
      (w.map fun D => eval D x) ++
        [g.op.eval (g.inputs.map fun i => (w.map fun D => eval D x).getD i false)] := by
  simp only [step, List.map_append, List.map_cons, List.map_nil, eval_gate g.op hg,
    List.map_map, Function.comp_def, eval_getD]

lemma run_sound {n : ℕ} (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List (Terms n)) (x : Fin n → Bool) :
    (run gs w).map (fun D => eval D x) =
      gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])
        (w.map fun D => eval D x) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).map (fun D => eval D x) = _
    rw [ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))]
    rw [step_sound w g (hgs g (List.mem_cons_self)) x]
    rfl

def wires (n : ℕ) (C : Circuit) : List (Terms n) :=
  run C.gates (List.ofFn fun i : Fin n => ({{i}} : Terms n))

def output (n : ℕ) (C : Circuit) : Terms n :=
  (wires n C).getD C.output ∅

lemma wires_sound (n : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) :
    (wires n C).map (fun D => eval D x) = C.wires (List.ofFn x) := by
  rw [wires, run_sound C.gates hC]
  simp only [List.map_ofFn, Function.comp_def, eval_var, Circuit.wires]

lemma output_sound (n : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) :
    eval (output n C) x = C.eval (List.ofFn x) := by
  rw [output, eval_getD, wires_sound n C hC x]
  rfl

lemma output_sound_monotone2 (n : ℕ) (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (x : Fin n → Bool) :
    eval (output n C) x = C.eval (List.ofFn x) := by
  apply output_sound
  intro g hg
  simpa using (hC g hg).1

lemma eval_graph_of_certificate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Terms n)
    (sound : ∀ t ∈ D, ∃ u ∈ t, ∃ v ∈ t, G.Adj u v)
    (complete : ∀ u v, G.Adj u v → ∃ t ∈ D, t ⊆ {u, v})
    (x : Fin n → Bool) :
    eval D x = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [eval, decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht, hxt⟩
    obtain ⟨u, hu, v, hv, huv⟩ := sound t ht
    exact ⟨u, v, huv, hxt u hu, hxt v hv⟩
  · rintro ⟨u, v, huv, hxu, hxv⟩
    obtain ⟨t, ht, hsub⟩ := complete u v huv
    refine ⟨t, ht, ?_⟩
    intro i hi
    have hmem := hsub hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact hxu
    · exact hxv

lemma circuit_graph_of_certificate (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (sound : ∀ t ∈ output n C, ∃ u ∈ t, ∃ v ∈ t, G.Adj u v)
    (complete : ∀ u v, G.Adj u v → ∃ t ∈ output n C, t ⊆ {u, v}) :
    ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
  intro x
  rw [← output_sound_monotone2 n C hC x]
  exact eval_graph_of_certificate G (output n C) sound complete x


lemma eval_imp_of_subsumes {n : ℕ} (A B : Terms n)
    (h : ∀ t ∈ A, ∃ s ∈ B, s ⊆ t) (x : Fin n → Bool) :
    eval A x = true → eval B x = true := by
  simp only [eval, decide_eq_true_eq]
  rintro ⟨t, ht, hxt⟩
  obtain ⟨s, hs, hst⟩ := h t ht
  exact ⟨s, hs, fun i hi => hxt i (hst hi)⟩

lemma eval_eq_of_subsumes {n : ℕ} (A B : Terms n)
    (hAB : ∀ t ∈ A, ∃ s ∈ B, s ⊆ t)
    (hBA : ∀ t ∈ B, ∃ s ∈ A, s ⊆ t) (x : Fin n → Bool) :
    eval A x = eval B x := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨eval_imp_of_subsumes A B hAB x, eval_imp_of_subsumes B A hBA x⟩

end DNF

end PEqualNP.Outside.L_meta_1904_aux
