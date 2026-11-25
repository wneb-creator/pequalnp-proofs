import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4320_aux

-- Circuit builder adapted from L_meta_1003.lean (H926, H926.EdgeUpper), strengthened to carry
-- monotonicity (AND/OR, fan-in two) and an upper bound on every AND gate's wire.

open PEqualNP PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

def OkM (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Bld (n : ℕ) (P : (Fin n → Bool) → Prop) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, OkM g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ (∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)) ∧
    ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD (m + j) false = true → P (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {P} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n P F s)
    (hs : s ≤ s') : Bld n P F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev, ha⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev, ha⟩

theorem bld_congr {n : ℕ} {P} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n P F s)
    (e : ∀ x, F x = H x) : Bld n P H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev, ha⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e], ha⟩

theorem bld_var {n : ℕ} {P} (i : Fin n) : Bld n P (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_, ?_⟩
  · intro w _
    simp [wiresFrom]
  · intro j g hj
    simp at hj

theorem bld_bin {n : ℕ} {P} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
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

theorem bld_or {n : ℕ} {P} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n P F s1)
    (h2 : Bld n P H s2) : Bld n P (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2
    (by intro h; cases h)

theorem bld_and {n : ℕ} {P} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n P F s1)
    (h2 : Bld n P H s2) (hP : ∀ x, F x = true → H x = true → P x) :
    Bld n P (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2
    (by
      intro _ x hx
      simp only [Bool.and_eq_true] at hx
      exact hP x hx.1 hx.2)

theorem bld_anyList {n : ℕ} {P} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n P (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var (P := P) v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} {P} (S : Finset (Fin n)) (hS : S.Nonempty) :
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
theorem bld_edges (n : ℕ) (P : (Fin n → Bool) → Prop) (T : Finset (Fin n)) :
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

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
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

end PEqualNP.Outside.L_meta_4320_aux

theorem PEqualNP.Outside.L_meta_4320 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) ∧ x6.size ≤ x2.edgeFinset.card + x4.card - (1 : ℕ) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin x1 → Bool), (x6.wires (List.ofFn x11)).getD (x1 + x7) Bool.false = Bool.true → ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x11 x14 = Bool.true := by
  intro x1 x2 x3 x4 hc
  exact PEqualNP.Outside.L_meta_4320_aux.main x1 x2 x4 hc
