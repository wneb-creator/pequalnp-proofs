import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_217

private def CoversOn {V : Type*} (G : SimpleGraph V) (W S : Finset V) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, G.Adj u v → u ∈ S ∨ v ∈ S

/- A vertex-minimal obstruction has at most twice its minimum cover size. Track a union of minimum covers and the vertices that still meet its boundary. -/
private theorem cover_union_bound {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (t : ℕ) (hlower : ∀ S, CoversOn G W S → t ≤ S.card)
    (hreach : ∀ v ∈ W, ∃ T ⊆ W, v ∈ T ∧ T.card = t ∧ CoversOn G W T)
    (P Q : Finset V) (hPW : P ⊆ W) (hQP : Q ⊆ P) (hbudget : P.card + Q.card ≤ 2*t)
    (hboundary : ∀ u ∈ W, u ∉ P → ∀ v ∈ W, G.Adj u v → v ∈ Q) :
    W.card ≤ 2*t := by
  classical
  by_cases h : W ⊆ P
  · have := Finset.card_le_card h
    omega
  obtain ⟨a, ha, haP⟩ := Finset.not_subset.mp h
  obtain ⟨T, hTW, haT, hT, hc⟩ := hreach a ha
  have cover : CoversOn G W ((T ∩ P) ∪ (Q \ T)) := by
    intro u hu v hv huv
    have step (x y : V) (hx : x ∈ W) (hy : y ∈ W) (he : G.Adj x y) (ht : x ∈ T) :
        x ∈ (T ∩ P) ∪ (Q \ T) ∨ y ∈ (T ∩ P) ∪ (Q \ T) := by
      by_cases hp : x ∈ P
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ht, hp⟩))
      have hyq := hboundary x hx hp y hy he
      by_cases hyt : y ∈ T
      · exact Or.inr (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hyt, hQP hyq⟩))
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hyq, hyt⟩))
    exact (hc u hu v hv huv).elim (step u v hu hv huv) (fun e => (step v u hv hu huv.symm e).symm)
  have hcost := hlower _ cover
  have hu := Finset.card_union_le (T ∩ P) (Q \ T)
  have hcount := Finset.card_union_add_card_inter T P
  have hsplit := Finset.card_sdiff_add_card_inter Q T
  have hbig : P ⊂ T ∪ P := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_right,
    fun eq => haP (eq ▸ Finset.mem_union_left _ haT)⟩
  have hPW' : T ∪ P ⊆ W := Finset.union_subset hTW hPW
  exact cover_union_bound G W t hlower hreach (T ∪ P) (Q ∩ T) hPW'
    (fun _ hx => Finset.mem_union_left _ (Finset.mem_inter.mp hx).2) (by omega) (by
      intro u huW huP v hvW huv
      have e := Finset.notMem_union.mp huP
      exact Finset.mem_inter.mpr ⟨hboundary u huW e.2 v hvW huv, (hc u huW v hvW huv).resolve_left e.1⟩)
termination_by W.card - P.card
decreasing_by
  have := Finset.card_lt_card hbig
  have := Finset.card_le_card hPW'
  omega

private theorem critical_obstruction {V : Type*} [DecidableEq V] (G : SimpleGraph V) (t : ℕ)
    (U : Finset V) (h : ∀ S, CoversOn G U S → t ≤ S.card) :
    ∃ W ⊆ U, W.card ≤ 2*t ∧ (∀ S, CoversOn G W S → t ≤ S.card) ∧
      ∀ v ∈ W, ∃ T ⊆ W, v ∈ T ∧ T.card = t ∧ CoversOn G W T := by
  classical
  let candidates := U.powerset.filter (fun W => ∀ S, CoversOn G W S → t ≤ S.card)
  have hu : U ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by rfl), h⟩
  obtain ⟨W, hw, hmin⟩ := Finset.exists_min_image candidates Finset.card ⟨U, hu⟩
  obtain ⟨hwU, hlower⟩ := Finset.mem_filter.mp hw
  have hWU := Finset.mem_powerset.mp hwU
  have reach (v : V) (hv : v ∈ W) : ∃ T ⊆ W, v ∈ T ∧ T.card = t ∧ CoversOn G W T := by
    have hsmall : ¬ ∀ S, CoversOn G (W.erase v) S → t ≤ S.card := by
      intro e
      have := hmin (W.erase v) (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans hWU), e⟩)
      exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem hv)) this
    push Not at hsmall
    obtain ⟨S, hcover, hsize⟩ := hsmall
    let T := insert v (S ∩ W)
    have hc : CoversOn G W T := by
      intro x hx y hy hxy
      by_cases ex : x = v
      · exact Or.inl (by simp [T, ex])
      by_cases ey : y = v
      · exact Or.inr (by simp [T, ey])
      exact (hcover x (Finset.mem_erase.mpr ⟨ex, hx⟩) y (Finset.mem_erase.mpr ⟨ey, hy⟩) hxy).imp
        (fun e => Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨e, hx⟩))
        (fun e => Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨e, hy⟩))
    have lower := hlower T hc
    have upper := Finset.card_insert_le v (S ∩ W)
    have bound := Finset.card_le_card (Finset.inter_subset_left (s₁ := S) (s₂ := W))
    exact ⟨T, Finset.insert_subset hv Finset.inter_subset_right, by simp [T],
      by dsimp [T] at *; omega, hc⟩
  refine ⟨W, hWU, ?_, hlower, reach⟩
  rcases W.eq_empty_or_nonempty with e | ⟨v, hv⟩
  · simp [e]
  obtain ⟨T, hTW, _, hT, hc⟩ := reach v hv
  exact cover_union_bound G W t hlower reach T T hTW (by rfl) (by omega)
    (fun u hu ht v hv huv => (hc u hu v hv huv).resolve_left ht)

private theorem finite_obstruction {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ)
    (hlower : ∀ S : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card)
    (hfree : ∀ a b c d, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    ∃ (k : ℕ) (e : Fin k ↪ Fin n), k ≤ 2*t ∧
      (∀ a b c d, a ≠ c → b ≠ d → ¬ ((G.comap e).Adj a b ∧
        (G.comap e).Adj b c ∧ (G.comap e).Adj c d ∧ (G.comap e).Adj d a)) ∧
      (∀ S : Finset (Fin k), (∀ u v, (G.comap e).Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) ∧
      (∀ w : Fin k, ∃ S : Finset (Fin k), w ∈ S ∧ S.card = t ∧
        ∀ u v, (G.comap e).Adj u v → u ∈ S ∨ v ∈ S) := by
  classical
  obtain ⟨W, _, hk, hw, hcrit⟩ := critical_obstruction G t Finset.univ
    (fun S hs => hlower S (fun u v => hs u (Finset.mem_univ u) v (Finset.mem_univ v)))
  let e := (W.orderEmbOfFin rfl).toEmbedding
  have mem (j : Fin W.card) : e j ∈ W := W.orderEmbOfFin_mem rfl j
  have surj (x : Fin n) (hx : x ∈ W) : ∃ j, e j = x := by
    have hr := W.range_orderEmbOfFin rfl
    exact Set.ext_iff.mp hr x |>.mpr hx
  refine ⟨W.card, e, hk, ?_, ?_, ?_⟩
  · intro a b c d hac hbd
    exact hfree _ _ _ _ (e.injective.ne hac) (e.injective.ne hbd)
  · intro S hs
    have hsize := hw (S.map e) (by
      intro x hx y hy hxy
      obtain ⟨a, rfl⟩ := surj x hx
      obtain ⟨b, rfl⟩ := surj y hy
      exact (hs a b hxy).imp (fun h => Finset.mem_map.mpr ⟨a, h, rfl⟩)
        (fun h => Finset.mem_map.mpr ⟨b, h, rfl⟩))
    simpa using hsize
  · intro w
    obtain ⟨T, hTW, hwT, hcard, hc⟩ := hcrit _ (mem w)
    let S := Finset.univ.filter (fun j => e j ∈ T)
    have heq : S.map e = T := by
      ext x
      constructor
      · intro hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
        exact (Finset.mem_filter.mp hj).2
      · intro hx
        obtain ⟨j, rfl⟩ := surj x (hTW hx)
        exact Finset.mem_map.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
    refine ⟨S, by simpa [S] using hwT, ?_, ?_⟩
    · simpa [← heq] using hcard
    · intro a b hab
      simpa [S] using hc (e a) (mem a) (e b) (mem b) hab


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private lemma proj_snoc_read {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

private def projWmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

private def projGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (projWmap n m π)⟩

private def projStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def ProjRel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (projWmap n m π w) false = W.getD w false

private lemma proj_rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : ProjRel n m π W W') : ProjRel n m π (projStep W g) (projStep W' (projGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (projGate n m π g).op.eval
      ((projGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [projGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [projStep]; omega, by simp [projStep]; omega, ?_⟩
  intro w
  simp only [projStep, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : projWmap n m π w < W'.length := by
      unfold projWmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : projWmap n m π w = W'.length := by
      unfold projWmap
      split
      · omega
      · omega
    rw [he, hw, proj_snoc_read, proj_snoc_read]
  · have hge : W'.length + 1 ≤ projWmap n m π w := by
      unfold projWmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma proj_rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, ProjRel n m π W W' →
      ProjRel n m π (gs.foldl projStep W) ((gs.map (projGate n m π)).foldl projStep W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (proj_rel_step n m π W W' g h)

private lemma proj_rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    ProjRel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold projWmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

private def projectWithZero {n k : ℕ} (π : Fin n → Fin (k + 1)) (C : Circuit) : Circuit :=
  ⟨⟨.or, []⟩ :: C.gates.map (projGate n (k + 1) π), projWmap n (k + 1) π C.output⟩

private theorem projectWithZero_eval {n k : ℕ} (π : Fin n → Fin (k + 1)) (C : Circuit)
    (x : Fin k → Bool) :
    (projectWithZero π C).eval (List.ofFn x) = C.eval (List.ofFn ((Fin.lastCases false x) ∘ π)) := by
  have hlist : List.ofFn (Fin.lastCases false x) = List.ofFn x ++ [false] := by
    rw [List.ofFn_succ_last]
    simp
  have h := (proj_rel_fold n (k+1) π C.gates _ _
    (proj_rel_init n (k+1) π (Fin.lastCases false x))).2.2 C.output
  rw [hlist] at h
  exact h

private theorem projectWithZero_mono {n k : ℕ} (π : Fin n → Fin (k+1)) (C : Circuit)
    (h : Monotone2 C) : Monotone2 (projectWithZero π C) := by
  intro g hg
  rcases List.mem_cons.mp hg with he | hm
  · subst g
    simp
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hm
    exact ⟨(h g' hg').1, by simpa [projGate] using (h g' hg').2⟩

private theorem projectWithZero_count {n k : ℕ} (π : Fin n → Fin (k+1)) (C : Circuit)
    (A : Finset ℕ)
    (h : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A) :
    ∀ j g, (projectWithZero π C).gates[j]? = some g → g.op = GateOp.and →
      j ∈ A.image Nat.succ := by
  intro j g hg hop
  cases j with
  | zero =>
    simp [projectWithZero] at hg
    subst g
    cases hop
  | succ j =>
    change ((C.gates.map (projGate n (k+1) π))[j]?) = some g at hg
    rw [List.getElem?_map] at hg
    cases hh : C.gates[j]? with
    | none => simp [hh] at hg
    | some u =>
      simp [hh] at hg
      subst g
      exact Finset.mem_image.mpr ⟨j, h j u hh hop, rfl⟩

private theorem project_induced {n k : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (e : Fin k ≃ W) (C : Circuit) (A : Finset ℕ)
    (hm : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A) :
    ∃ (D : Circuit) (B : Finset ℕ), B.card = A.card ∧ Monotone2 D ∧
      (∀ x : Fin k → Bool, D.eval (List.ofFn x) = true ↔
        ∃ u v : Fin k, G.Adj (e u).val (e v).val ∧ x u = true ∧ x v = true) ∧
      ∀ j g, D.gates[j]? = some g → g.op = GateOp.and → j ∈ B := by
  classical
  let π (i : Fin n) : Fin (k+1) :=
    if h : i ∈ W then (e.symm ⟨i,h⟩).castSucc else Fin.last k
  refine ⟨projectWithZero π C, A.image Nat.succ, Finset.card_image_of_injective _ Nat.succ_injective,
    projectWithZero_mono π C hm, ?_, projectWithZero_count π C A hA⟩
  intro x
  rw [projectWithZero_eval, he]
  have within (v : Fin k) : (Fin.lastCases false x ∘ π) (e v).val = x v := by
    simp [π, (e v).property]
  constructor
  · rintro ⟨u, v, h, hu, hv⟩
    have source (i : Fin n) (hi : (Fin.lastCases false x ∘ π) i = true) : i ∈ W := by
      by_contra hnot
      simp [π,hnot] at hi
    let p := e.symm ⟨u,source u hu⟩
    let q := e.symm ⟨v,source v hv⟩
    have ep : (e p).val = u := by simp [p]
    have eq : (e q).val = v := by simp [q]
    exact ⟨p, q, ep ▸ eq ▸ h, (within p).symm.trans (ep ▸ hu), (within q).symm.trans (eq ▸ hv)⟩
  · rintro ⟨p,q,h,hp,hq⟩
    exact ⟨_,_,h,(within p).trans hp,(within q).trans hq⟩

private def AndBound (n t : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (C : Circuit) (A : Finset ℕ), Monotone2 C →
    (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
    (∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A) → t ≤ A.card

private def FourCycleFree {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

private def VertexCover {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S

private theorem reduce_to_critical_graphs
    (finiteCases : ∀ (k t : ℕ) (H : SimpleGraph (Fin k)), t ≤ 5 → k ≤ 2*t →
      FourCycleFree H → (∀ S, VertexCover H S → t ≤ S.card) →
      (∀ w, ∃ S, w ∈ S ∧ S.card = t ∧ VertexCover H S) → AndBound k t H)
    {n t : ℕ} (G : SimpleGraph (Fin n)) (ht : t ≤ 5) (hfree : FourCycleFree G)
    (hcover : ∀ S, VertexCover G S → t ≤ S.card) : AndBound n t G := by
  classical
  obtain ⟨k, e, hk, hf, hlow, hcrit⟩ := finite_obstruction G t hcover hfree
  let W := Finset.univ.map e
  let f (i : Fin k) : W := ⟨e i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let iso : Fin k ≃ W := Equiv.ofBijective f ⟨fun _ _ h => e.injective (congrArg Subtype.val h), by
    rintro ⟨v, hv⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
    exact ⟨i, rfl⟩⟩
  intro C A hm he hA
  obtain ⟨D, B, hb, hm', he', hB⟩ := project_induced G W iso C A hm he hA
  have := finiteCases k t (G.comap e) ht hk hf hlow hcrit D B hm' he' hB
  rwa [hb] at this



private def IsCover {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S

private theorem private_neighbor {n t : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (hlower : ∀ S, IsCover G S → t ≤ S.card) (hT : IsCover G T) (hc : T.card = t)
    (a : Fin n) (ha : a ∈ T) : ∃ w, G.Adj a w ∧ w ∉ T := by
  classical
  by_contra! h
  have := hlower (T.erase a) (by
    intro u v huv
    by_cases hu : u = a
    · subst u
      exact Or.inr (Finset.mem_erase.mpr ⟨huv.ne.symm, h v huv⟩)
    by_cases hv : v = a
    · subst v
      exact Or.inl (Finset.mem_erase.mpr ⟨huv.ne, h u huv.symm⟩)
    exact (hT u v huv).imp (fun e => Finset.mem_erase.mpr ⟨hu, e⟩)
      (fun e => Finset.mem_erase.mpr ⟨hv, e⟩))
  have := Finset.card_erase_lt_of_mem ha
  omega

private theorem distinct_neighborhoods {n t : ℕ} (G : SimpleGraph (Fin n))
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hlower : ∀ S, IsCover G S → t ≤ S.card)
    (hreach : ∀ w, ∃ S, w ∈ S ∧ S.card = t ∧ IsCover G S)
    {a b : Fin n} (hab : a ≠ b) : ¬ (∀ v, G.Adj a v ↔ G.Adj b v) := by
  classical
  intro twin
  obtain ⟨T, ha, hsize, hT⟩ := hreach a
  obtain ⟨w, haw, hw⟩ := private_neighbor G T hlower hT hsize a ha
  have hbw := (twin w).mp haw
  have hb := (hT b w hbw).resolve_right hw
  have unique (v : Fin n) (hv : G.Adj a v) : v = w := by
    by_contra hvw
    exact hfree a v b w hab hvw ⟨hv, ((twin v).mp hv).symm, hbw, haw.symm⟩
  let T' := insert w ((T.erase a).erase b)
  have hc : IsCover G T' := by
    intro x y hxy
    have step (u v : Fin n) (he : G.Adj u v) (hu : u ∈ T) : u ∈ T' ∨ v ∈ T' := by
      by_cases hua : u = a
      · subst u
        exact Or.inr (by simp [T', unique v he])
      by_cases hub : u = b
      · subst u
        exact Or.inr (by simp [T', unique v ((twin v).mpr he)])
      exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr
        ⟨hub, Finset.mem_erase.mpr ⟨hua, hu⟩⟩))
    exact (hT x y hxy).elim (step x y hxy) (fun e => (step y x hxy.symm e).symm)
  have lower := hlower T' hc
  have u1 := Finset.card_erase_lt_of_mem ha
  have u2 := Finset.card_erase_lt_of_mem (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)
  have u3 := Finset.card_insert_le w ((T.erase a).erase b)
  dsimp [T'] at lower
  omega

private theorem neighborhood_encoding {n t : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Finset (Fin n)) (hc : IsCover G C)
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hlower : ∀ S, IsCover G S → t ≤ S.card)
    (hreach : ∀ w, ∃ S, w ∈ S ∧ S.card = t ∧ IsCover G S) :
    ∃ f : {v : Fin n // v ∉ C} ↪ Finset (Fin n),
      (∀ a, (f a).Nonempty ∧ f a ⊆ C ∧ ∀ v, v ∈ f a ↔ G.Adj a.val v) ∧
      (∀ a b, a ≠ b → (f a ∩ f b).card ≤ 1) ∧
      (∀ a, ∀ u ∈ C, ((f a).filter (G.Adj u)).card ≤ 1) := by
  classical
  let f (a : {v : Fin n // v ∉ C}) := C.filter (G.Adj a.val)
  have mem (a : {v : Fin n // v ∉ C}) (v : Fin n) : v ∈ f a ↔ G.Adj a.val v :=
    ⟨fun h => (Finset.mem_filter.mp h).2, fun h =>
      Finset.mem_filter.mpr ⟨(hc _ _ h).resolve_left a.property, h⟩⟩
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    by_contra hab
    exact distinct_neighborhoods G hfree hlower hreach hab (fun v =>
      (mem a v).symm.trans (he ▸ mem b v))
  refine ⟨⟨f, hinj⟩, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨S, ha, hs, hS⟩ := hreach a.val
    obtain ⟨v, hv, _⟩ := private_neighbor G S hlower hS hs a.val ha
    exact ⟨⟨v, (mem a v).mpr hv⟩, Finset.filter_subset _ _, mem a⟩
  · intro a b hab
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have ⟨hax, hbx⟩ := Finset.mem_inter.mp hx
    have ⟨hay, hby⟩ := Finset.mem_inter.mp hy
    by_contra hxy
    exact hfree a.val x b.val y (fun eq => hab (Subtype.ext eq)) hxy
      ⟨(mem a x).mp hax, ((mem b x).mp hbx).symm, (mem b y).mp hby, ((mem a y).mp hay).symm⟩
  · intro a u hu
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have ⟨hax, hux⟩ := Finset.mem_filter.mp hx
    have ⟨hay, huy⟩ := Finset.mem_filter.mp hy
    by_contra hxy
    exact hfree a.val x u y (fun eq => a.property (eq ▸ hu)) hxy
      ⟨(mem a x).mp hax, hux.symm, huy, ((mem a y).mp hay).symm⟩

private def splitAdj {t : ℕ} (H : SimpleGraph (Fin t)) (M : Finset (Finset (Fin t))) :
    (Fin t ⊕ M) → (Fin t ⊕ M) → Prop
  | .inl i, .inl j => H.Adj i j
  | .inl i, .inr b => i ∈ b.val
  | .inr a, .inl j => j ∈ a.val
  | .inr _, .inr _ => False

private theorem minimum_split_representation {n t : ℕ} (G : SimpleGraph (Fin n))
    (cost : SimpleGraph (Fin t) → ℕ)
    (quality : Finset (Finset (Fin t)) → Nat)
    (C : Finset (Fin n)) (hc : IsCover G C) (hcard : C.card = t) (hn : n ≤ 2*t)
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hlower : ∀ S, IsCover G S → t ≤ S.card)
    (hreach : ∀ w, ∃ S, w ∈ S ∧ S.card = t ∧ IsCover G S) :
    ∃ (H : SimpleGraph (Fin t)) (M : Finset (Finset (Fin t))) (e : (Fin t ⊕ M) ≃ Fin n),
      (∀ σ : Equiv.Perm (Fin t), cost H ≤ cost (H.comap σ)) ∧
      (∀ τ : Equiv.Perm (Fin t), cost (H.comap τ) = cost H →
        quality (M.image (fun S => S.image τ.symm)) ≤ quality M) ∧
      M.card ≤ t ∧ (∀ a ∈ M, a.Nonempty) ∧
      (∀ a ∈ M, ∀ b ∈ M, a ≠ b → (a ∩ b).card ≤ 1) ∧
      (∀ u v, splitAdj H M u v ↔ G.Adj (e u) (e v)) := by
  classical
  let K := {v : Fin n // v ∉ C}
  let first := (C.orderIsoOfFin hcard).toEquiv
  let price (σ : Equiv.Perm (Fin t)) := cost (G.comap (fun i => (first (σ i)).val))
  obtain ⟨σ₀, _, hmin⟩ := Finset.exists_min_image Finset.univ price
    ⟨Equiv.refl _, Finset.mem_univ _⟩
  let rawFor (π : Equiv.Perm (Fin t)) (a : K) :=
    Finset.univ.filter fun i : Fin t => G.Adj a.val (first (π i)).val
  let family (π : Equiv.Perm (Fin t)) := Finset.univ.image (rawFor π)
  let winners := Finset.univ.filter fun π => price π = price σ₀
  obtain ⟨σ, hwin, hbest⟩ := Finset.exists_max_image winners (fun π => quality (family π))
    ⟨σ₀,by simp [winners]⟩
  have bestPrice := (Finset.mem_filter.mp hwin).2
  let lab := σ.trans first
  let raw (a : K) := Finset.univ.filter (fun i : Fin t => G.Adj a.val (lab i).val)
  have hmem (a : K) (i : Fin t) : i ∈ raw a ↔ G.Adj a.val (lab i).val := by simp [raw]
  have inj : Function.Injective raw := by
    intro a b he
    apply Subtype.ext
    by_contra hab
    apply distinct_neighborhoods G hfree hlower hreach hab
    intro v
    by_cases hv : v ∈ C
    · obtain ⟨i, hi⟩ := lab.surjective ⟨v,hv⟩
      have eq : (lab i).val = v := congrArg Subtype.val hi
      rw [← eq, ← hmem, ← hmem, he]
    · exact iff_of_false (fun h => (hc _ _ h).elim a.property hv)
        (fun h => (hc _ _ h).elim b.property hv)
  let M := Finset.univ.image raw
  let injM (a : K) : M := ⟨raw a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  let code : K ≃ M := Equiv.ofBijective injM ⟨fun _ _ h => inj (congrArg Subtype.val h), by
    rintro ⟨b, hb⟩
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨a,rfl⟩⟩
  let e := (Equiv.sumCongr lab code.symm).trans (Equiv.sumCompl (· ∈ C))
  let H := G.comap (fun i : Fin t => (lab i).val)
  have hright (a : M) : raw (code.symm a) = a.val := congrArg Subtype.val (code.apply_symm_apply a)
  refine ⟨H, M, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ
    change price σ ≤ price (τ.trans σ)
    rw [bestPrice]
    exact hmin (τ.trans σ) (Finset.mem_univ _)
  · intro τ heq
    change price (τ.trans σ) = price σ at heq
    have hτ : τ.trans σ ∈ winners :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,heq.trans bestPrice⟩
    have front (a : K) : rawFor (τ.trans σ) a = (raw a).image τ.symm := by
      ext j
      constructor
      · intro hj
        apply Finset.mem_image.mpr
        exact ⟨τ j,(hmem a (τ j)).mpr (Finset.mem_filter.mp hj).2,τ.symm_apply_apply j⟩
      · intro hj
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
        change τ.symm i ∈ Finset.univ.filter (fun j : Fin t => G.Adj a.val (first (σ (τ j))).val)
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,τ.apply_symm_apply]
        exact (hmem a i).mp hi
    have mapEq : family (τ.trans σ) = M.image (fun S => S.image τ.symm) := by
      change Finset.univ.image _ = (Finset.univ.image raw).image _
      rw [Finset.image_image]
      exact Finset.image_congr (fun a _ => front a)
    have h := hbest (τ.trans σ) hτ
    rw [mapEq] at h
    exact h
  · have h := Fintype.card_congr e
    simp at h
    omega
  · intro a ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨T, hbT, hs, hT⟩ := hreach b.val
    obtain ⟨w, hw, _⟩ := private_neighbor G T hlower hT hs b.val hbT
    have hwC := (hc _ _ hw).resolve_left b.property
    obtain ⟨i, hi⟩ := lab.surjective ⟨w, hwC⟩
    exact ⟨i, (hmem b i).mpr (by simpa [hi] using hw)⟩
  · intro a ha b hb hab
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hb
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    obtain ⟨hpi, hqi⟩ := Finset.mem_inter.mp hi
    obtain ⟨hpj, hqj⟩ := Finset.mem_inter.mp hj
    exact hfree p.val (lab i).val q.val (lab j).val (fun h => hab (congrArg raw (Subtype.ext h)))
      (fun h => hij (lab.injective (Subtype.ext h))) ⟨(hmem _ _).mp hpi,
        ((hmem _ _).mp hqi).symm, (hmem _ _).mp hqj, ((hmem _ _).mp hpj).symm⟩
  · rintro (i | a) (j | b)
    · rfl
    · change i ∈ b.val ↔ G.Adj (lab i).val (code.symm b).val
      rw [← hright b, hmem]
      exact G.adj_comm _ _
    · change j ∈ a.val ↔ G.Adj (code.symm a).val (lab j).val
      rw [← hright a, hmem]
    · exact iff_of_false id (fun h => (hc _ _ h).elim (code.symm a).property (code.symm b).property)


private theorem core_restrictions {n t : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin t))
    (M : Finset (Finset (Fin t))) (e : (Fin t ⊕ M) ≃ Fin n)
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (he : ∀ u v, splitAdj H M u v ↔ G.Adj (e u) (e v)) [DecidableRel H.Adj] :
    (∀ a b c d, a ≠ c → b ≠ d → ¬ (H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a)) ∧
      ∀ S ∈ M, ∀ u, (S.filter (H.Adj u)).card ≤ 1 := by
  have nol (a b c d : Fin t ⊕ M) (hac : a ≠ c) (hbd : b ≠ d)
      (ab : splitAdj H M a b) (bc : splitAdj H M b c)
      (cd : splitAdj H M c d) (da : splitAdj H M d a) : False :=
    hfree _ _ _ _ (e.injective.ne hac) (e.injective.ne hbd)
      ⟨(he _ _).mp ab, (he _ _).mp bc, (he _ _).mp cd, (he _ _).mp da⟩
  constructor
  · rintro a b c d hac hbd ⟨ab,bc,cd,da⟩
    exact nol (.inl a) (.inl b) (.inl c) (.inl d) (fun h => hac (Sum.inl.inj h))
      (fun h => hbd (Sum.inl.inj h)) ab bc cd da
  · intro S hS u
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxs, hux⟩ := Finset.mem_filter.mp hx
    obtain ⟨hys, huy⟩ := Finset.mem_filter.mp hy
    by_contra hxy
    exact nol (.inr ⟨S,hS⟩) (.inl x) (.inl u) (.inl y) (by simp)
      (fun h => hxy (Sum.inl.inj h)) hxs hux.symm huy hys



private def visitMasks {α : Type*} (compatible : α → α → Bool) (verify : List α → Bool) :
    ℕ → List α → List α → Bool
  | 0, _, acc => verify acc
  | _ + 1, [], acc => verify acc
  | d + 1, m :: tail, acc =>
    visitMasks compatible verify (d+1) tail acc &&
      (!(acc.all (compatible m)) || visitMasks compatible verify d tail (m :: acc))
termination_by d rest _ => (d, rest.length)

private theorem visitMasks_complete {α : Type*} (compatible : α → α → Bool)
    (verify : List α → Bool) (d : ℕ) (choices acc picks : List α)
    (hvisit : visitMasks compatible verify d choices acc = true)
    (hlen : picks.length ≤ d) (hsub : picks.Sublist choices)
    (hpair : picks.Pairwise (fun a b => compatible b a = true))
    (hacc : ∀ m ∈ picks, ∀ a ∈ acc, compatible m a = true) :
    verify (picks.reverse ++ acc) = true := by
  induction choices generalizing d acc picks with
  | nil =>
    have e : picks = [] := List.sublist_nil.mp hsub
    subst picks
    cases d <;> simpa [visitMasks] using hvisit
  | cons m tail ih =>
    cases d with
    | zero =>
      have e : picks = [] := List.length_eq_zero_iff.mp (by omega)
      subst picks
      simpa [visitMasks] using hvisit
    | succ d =>
      rw [visitMasks, Bool.and_eq_true] at hvisit
      cases hsub with
      | cons _ hrest => exact ih _ _ _ hvisit.1 hlen hrest hpair hacc
      | cons_cons _ hrest =>
        have hm := List.all_eq_true.mpr (hacc m (by simp))
        have hv := hvisit.2
        rw [hm] at hv
        simp only [Bool.not_true, Bool.false_or] at hv
        have pp := List.pairwise_cons.mp hpair
        have ht := ih d (m :: acc) _ hv (by simpa using hlen) hrest pp.2 (by
          intro x hx y hy
          rcases List.mem_cons.mp hy with rfl | h
          · exact pp.1 x hx
          · exact hacc x (List.mem_cons_of_mem _ hx) y h)
        simpa using ht

def packMaskBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k+1, f => Nat.bit (f 0) (packMaskBits k (fun j => f (j+1)))

theorem packMask_test (k j : Nat) (f : Nat → Bool) :
    (packMaskBits k f).testBit j = (decide (j < k) && f j) := by
  induction k generalizing j f with
  | zero => simp [packMaskBits]
  | succ k ih =>
    cases j with
    | zero => simp [packMaskBits]
    | succ j => simp [packMaskBits, Nat.testBit_bit_succ, ih]

theorem packMask_lt (k : Nat) (f : Nat → Bool) : packMaskBits k f < 2^k := by
  induction k generalizing f with
  | zero => simp [packMaskBits]
  | succ k ih =>
    have h := ih (fun j => f (j+1))
    cases hb : f 0 <;> simp [packMaskBits, hb, Nat.bit, pow_succ] <;> omega

private def encodeMask {t : ℕ} (S : Finset (Fin t)) : ℕ :=
  packMaskBits t fun j => if h : j < t then decide (⟨j,h⟩ ∈ S) else false

private theorem encodeMask_inj {t : ℕ} : Function.Injective (@encodeMask t) := by
  intro A B he
  ext j
  have hh := congrArg (fun z : ℕ => z.testBit j.val) he
  simpa [encodeMask, packMask_test, j.isLt] using hh

private theorem encodeMask_inter {t : ℕ} (A B : Finset (Fin t)) :
    encodeMask (A ∩ B) = encodeMask A &&& encodeMask B := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < t <;> simp [encodeMask, packMask_test, Nat.testBit_and, hj]

private def maskPair (a b : ℕ) : Bool :=
  let m := a &&& b
  (m &&& (m-1)) == 0

private theorem pair_ok {t : ℕ} {A B : Finset (Fin t)} (h : (A ∩ B).card ≤ 1) :
    maskPair (encodeMask A) (encodeMask B) = true := by
  rw [maskPair, ← encodeMask_inter]
  rcases Finset.card_le_one_iff_subsingleton.mp h with hsmall
  by_cases empty : A ∩ B = ∅
  · have hz : encodeMask (A ∩ B) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < t <;> simp [encodeMask, empty, packMask_test, hj]
    simp [hz]
  · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have eq : A ∩ B = {i} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun j hj => hsmall hj hi⟩
    have hp : encodeMask (A ∩ B) = 2^i.val := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < t
      · simp [encodeMask, eq, packMask_test, Nat.testBit_two_pow, hj, Fin.ext_iff, eq_comm]
      · have hn : j ≠ i.val := by have := i.isLt; omega
        simp [encodeMask, packMask_test, hj, Ne.symm hn]
    simp [hp]

private theorem enumerate_mask_sets {t : ℕ} (M : Finset (Finset (Fin t)))
    (eligible : ℕ → Bool) (verify : List ℕ → Bool)
    (hsize : M.card ≤ t) (hel : ∀ S ∈ M, eligible (encodeMask S) = true)
    (hpair : ∀ A ∈ M, ∀ B ∈ M, A ≠ B → (A ∩ B).card ≤ 1)
    (hall : visitMasks maskPair verify t ((List.range (2^t)).filter eligible) [] = true) :
    ∃ ls : List ℕ, ls.Nodup ∧ ls.toFinset = M.image encodeMask ∧ verify ls = true := by
  classical
  let choices := (List.range (2^t)).filter eligible
  let F := M.image encodeMask
  let picks := choices.filter (fun a => decide (a ∈ F))
  have hn : picks.Nodup := (List.nodup_range.filter eligible).filter _
  have hset : picks.toFinset = F := by
    ext a
    simp only [picks, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    refine ⟨And.right, fun ha => ⟨?_, ha⟩⟩
    obtain ⟨S, hs, rfl⟩ := Finset.mem_image.mp ha
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (packMask_lt _ _), hel S hs⟩
  have hlen : picks.length ≤ t := by
    rw [← List.toFinset_card_of_nodup hn, hset, Finset.card_image_of_injective _ encodeMask_inj]
    exact hsize
  have hcode (a : ℕ) (ha : a ∈ picks) : ∃ S ∈ M, encodeMask S = a :=
    Finset.mem_image.mp (show a ∈ F by rw [← hset]; exact List.mem_toFinset.mpr ha)
  have hp : picks.Pairwise (fun a b => maskPair b a = true) := by
    apply hn.imp_of_mem
    intro a b ha hb hne
    obtain ⟨A, hA, rfl⟩ := hcode a ha
    obtain ⟨B, hB, rfl⟩ := hcode b hb
    exact pair_ok (hpair B hB A hA (fun e => hne (congrArg encodeMask e.symm)))
  have hv := visitMasks_complete maskPair verify t choices [] picks hall hlen
    List.filter_sublist hp (by simp)
  exact ⟨picks.reverse, by simpa using hn, by simpa using hset, by simpa using hv⟩

private def pairBit (i j : ℕ) : ℕ :=
  let a := max i j
  a * (a - 1) / 2 + min i j

private theorem pairBit_unique : ∀ i j a b : Fin 5, i ≠ j → a ≠ b →
    pairBit i.val j.val = pairBit a.val b.val → (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by decide

private theorem pairBit_bounded : ∀ i j : Fin 5, i ≠ j → pairBit i.val j.val < 10 := by decide

private noncomputable def labelCore {t : ℕ} (H : SimpleGraph (Fin t)) : ℕ := by
  classical
  exact packMaskBits 10 fun k => decide (∃ i j : Fin t, pairBit i.val j.val = k ∧ H.Adj i j)

private def coreEdge (c i j : ℕ) : Bool :=
  decide (i ≠ j) && c.testBit (pairBit i j)

private theorem labelCore_edge {t : ℕ} (ht : t ≤ 5) (H : SimpleGraph (Fin t)) (i j : Fin t) :
    coreEdge (labelCore H) i.val j.val = true ↔ H.Adj i j := by
  classical
  by_cases h : i = j
  · subst j
    simp [coreEdge]
  have hne := (Fin.val_injective.ne h)
  have hij : i.castLE ht ≠ j.castLE ht := fun e => hne (congrArg (fun v : Fin 5 => v.val) e)
  have hlt := pairBit_bounded _ _ hij
  change pairBit i.val j.val < 10 at hlt
  simp only [coreEdge, hne, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
    labelCore, packMask_test, hlt, decide_eq_true_eq]
  constructor
  · rintro ⟨a,b,he,hab⟩
    have hab' : a.castLE ht ≠ b.castLE ht := fun e => hab.ne (Fin.ext (congrArg (fun v : Fin 5 => v.val) e))
    rcases pairBit_unique _ _ _ _ hab' hij he with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · have ha : a = i := Fin.ext (congrArg (fun v : Fin 5 => v.val) h1)
      have hb : b = j := Fin.ext (congrArg (fun v : Fin 5 => v.val) h2)
      simpa [ha,hb] using hab
    · have ha : a = j := Fin.ext (congrArg (fun v : Fin 5 => v.val) h1)
      have hb : b = i := Fin.ext (congrArg (fun v : Fin 5 => v.val) h2)
      simpa [ha,hb] using hab.symm
  · exact fun hab => ⟨i,j,rfl,hab⟩

private def splitEdge (t c : ℕ) (ls : List ℕ) (i j : ℕ) : Bool :=
  if i < t then
    if j < t then coreEdge c i j else (ls.getD (j-t) 0).testBit i
  else
    if j < t then (ls.getD (i-t) 0).testBit j else false

private theorem list_labels {t : ℕ} (M : Finset (Finset (Fin t))) (ls : List ℕ)
    (hn : ls.Nodup) (hset : ls.toFinset = M.image encodeMask) :
    ∃ e : Fin ls.length ≃ M, ∀ j, encodeMask (e j).val = ls.get j := by
  classical
  have hget (j : Fin ls.length) : ∃ a : M, encodeMask a.val = ls.get j := by
    have hm : ls.get j ∈ M.image encodeMask := hset ▸ List.mem_toFinset.mpr (ls.get_mem j)
    obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp hm
    exact ⟨⟨a,ha⟩,eq⟩
  choose f hf using hget
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, hf⟩
  · intro a b he
    apply (List.nodup_iff_injective_get.mp hn)
    simp only [← hf, he]
  · intro a
    have hx : encodeMask a.val ∈ ls := List.mem_toFinset.mp (by
      rw [hset]; exact Finset.mem_image.mpr ⟨a.val,a.property,rfl⟩)
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hx
    exact ⟨i, Subtype.ext (encodeMask_inj ((hf i).trans hi))⟩

private theorem splitEdge_model {t : ℕ} (ht : t ≤ 5) (H : SimpleGraph (Fin t))
    (M : Finset (Finset (Fin t))) (ls : List ℕ) (hn : ls.Nodup)
    (hset : ls.toFinset = M.image encodeMask) :
    ∃ e : Fin (t + ls.length) ≃ (Fin t ⊕ M), ∀ i j,
      splitEdge t (labelCore H) ls i.val j.val = true ↔ splitAdj H M (e i) (e j) := by
  classical
  obtain ⟨f,hf⟩ := list_labels M ls hn hset
  let iso : Fin t ⊕ Fin ls.length ≃ Fin (t + ls.length) := finSumFinEquiv
  let e := iso.symm.trans (Equiv.sumCongr (Equiv.refl (Fin t)) f)
  refine ⟨e, ?_⟩
  have left (i : Fin t) : e (iso (.inl i)) = .inl i := by simp [e]
  have right (i : Fin ls.length) : e (iso (.inr i)) = .inr (f i) := by simp [e]
  have readMask (i : Fin t) (j : Fin ls.length) :
      (ls.getD j.val 0).testBit i.val = true ↔ i ∈ (f j).val := by
    rw [List.getD_eq_getElem?_getD]
    simp [j.isLt, ← List.get_eq_getElem, ← hf, encodeMask, packMask_test, i.isLt]
  intro i j
  obtain ⟨a | a, rfl⟩ := iso.surjective i <;> obtain ⟨b | b, rfl⟩ := iso.surjective j
  · rw [left,left]
    simpa [splitEdge, iso, a.isLt, b.isLt, splitAdj] using labelCore_edge ht H a b
  · rw [left,right]
    simpa [splitEdge, iso, a.isLt, splitAdj] using readMask a b
  · rw [right,left]
    simpa [splitEdge, iso, b.isLt, splitAdj] using readMask b a
  · rw [right,right]
    simp [splitEdge, iso, splitAdj]

private def coreRowMask (t c u : ℕ) : ℕ := packMaskBits t (coreEdge c u)
private def eligibleMask (t c m : ℕ) : Bool :=
  (m != 0) && (List.range t).all (fun u => maskPair m (coreRowMask t c u))

private theorem eligible_for_model {t : ℕ} (ht : t ≤ 5) (H : SimpleGraph (Fin t))
    [DecidableRel H.Adj] (S : Finset (Fin t)) (hS : S.Nonempty)
    (hrows : ∀ u, (S.filter (H.Adj u)).card ≤ 1) :
    eligibleMask t (labelCore H) (encodeMask S) = true := by
  classical
  obtain ⟨i,hi⟩ := hS
  have ne : encodeMask S ≠ 0 := by
    intro e
    have := congrArg (fun z : ℕ => z.testBit i.val) e
    simp [encodeMask, packMask_test, i.isLt, hi] at this
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by simpa using ne, List.all_eq_true.mpr ?_⟩
  intro u hu
  let v : Fin t := ⟨u, List.mem_range.mp hu⟩
  let N := Finset.univ.filter (H.Adj v)
  have hmask : coreRowMask t (labelCore H) u = encodeMask N := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < t
    · let w : Fin t := ⟨j,hj⟩
      have e := labelCore_edge ht H v w
      have key : coreEdge (labelCore H) u j = decide (H.Adj v w) := by
        apply Bool.eq_iff_iff.mpr
        simpa using e
      simp [coreRowMask, encodeMask, packMask_test, hj, key, N, w]
    · simp [coreRowMask, encodeMask, packMask_test, hj]
  rw [hmask]
  apply pair_ok
  have eq : S ∩ N = S.filter (H.Adj v) := by ext j; simp [N]
  rw [eq]
  exact hrows v

private theorem bound_under_labels {k n t : ℕ} (G : SimpleGraph (Fin n)) (e : Fin k ≃ Fin n)
    (hb : AndBound k t (G.comap e)) : AndBound n t G := by
  let W : Finset (Fin n) := Finset.univ
  let iso := e.trans (Equiv.ofBijective (fun x : Fin n => (⟨x,Finset.mem_univ _⟩ : W))
    ⟨fun _ _ h => congrArg Subtype.val h, fun v => ⟨v.val, Subtype.ext rfl⟩⟩)
  intro C A hm he hA
  obtain ⟨D,B,hcard,hD,heD,hB⟩ := project_induced G W iso C A hm he hA
  exact hcard ▸ hb D B hD heD hB

/- Choose a minimum cover with the least adjacency code. Outside vertices have distinct nonempty neighborhoods, which determine the graph up to relabeling. -/
private def inspectLeaves {α C : Type*} (ok : α → α → Bool) (step : List α → C → Option C) :
    ℕ → List α → List α → C → Option C
  | 0, _, acc, idx => step acc idx
  | _+1, [], acc, idx => step acc idx
  | d+1, m :: rest, acc, idx => do
    let mid ← inspectLeaves ok step (d+1) rest acc idx
    if acc.all (ok m) then inspectLeaves ok step d rest (m :: acc) mid else some mid
termination_by structural _ rest _ _ => rest

private theorem visit_of_inspect {α C : Type*} (ok : α → α → Bool)
    (step : List α → C → Option C) (verify : List α → Bool)
    (atLeaf : ∀ ls i j, step ls i = some j → verify ls = true)
    (d : ℕ) (choices acc : List α) (i j : C)
    (run : inspectLeaves ok step d choices acc i = some j) :
    visitMasks ok verify d choices acc = true := by
  induction choices generalizing d acc i j with
  | nil =>
    cases d <;> rw [visitMasks] <;> apply atLeaf _ i j <;> simpa [inspectLeaves] using run
  | cons m rest ih =>
    cases d with
    | zero => rw [visitMasks]; apply atLeaf _ i j; simpa [inspectLeaves] using run
    | succ d =>
      rw [inspectLeaves] at run
      cases e : inspectLeaves ok step (d+1) rest acc i with
      | none => simp [e] at run
      | some mid =>
        have left := ih _ _ _ _ e
        rw [visitMasks, left, Bool.true_and]
        by_cases h : acc.all (ok m) = true
        · simp [e,h] at run
          simpa [h] using ih _ _ _ _ run
        · simp [h]

private def streamWord (arr : Array Nat) (width count idx : Nat) :=
  ((arr[idx / count]?.getD 0) >>> (width * (idx % count))) % (2^width)

private def unrankPerm (n rank : Nat) : List Nat :=
  let rec go : Nat → List Nat → Nat → List Nat
    | 0, _, _ => []
    | k+1, pool, r =>
      let idx := r / k.factorial
      pool.getD idx n :: go k (pool.eraseIdx idx) (r % k.factorial)
  go n (List.range n) rank



private def repCheck (t c : Nat) (ls rows p : List Nat) : Bool :=
  let N := t + ls.length
  (rows.length == N) && (p.length == N) && decide p.Nodup && p.all (· < rows.length) &&
    (List.range N).all fun i => (List.range N).all fun j =>
      splitEdge t c ls i j == (rows.getD (p.getD i 0) 0).testBit (p.getD j 0)

private theorem rep_transport {t c : Nat} (ls rows p : List Nat)
    (checked : repCheck t c ls rows p = true)
    (repBound : ∀ H : SimpleGraph (Fin rows.length),
      (∀ a b : Fin rows.length, (rows.getD a.val 0).testBit b.val = true ↔ H.Adj a b) →
      AndBound rows.length t H)
    (J : SimpleGraph (Fin (t+ls.length)))
    (model : ∀ i j : Fin (t+ls.length), splitEdge t c ls i.val j.val = true ↔ J.Adj i j) :
    AndBound (t+ls.length) t J := by
  simp only [repCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at checked
  obtain ⟨⟨⟨⟨size,plen⟩,nd⟩,range⟩,pairs⟩ := checked
  let f (i : Fin (t+ls.length)) : Fin rows.length :=
    ⟨p.getD i.val 0, by
      have hi : i.val < p.length := by rw [plen]; exact i.isLt
      rw [List.getD_eq_getElem _ _ hi]
      exact range _ (List.getElem_mem hi)⟩
  have inj : Function.Injective f := by
    intro i j he
    have hi : i.val < p.length := by rw [plen]; exact i.isLt
    have hj : j.val < p.length := by rw [plen]; exact j.isLt
    have eq := congrArg Fin.val he
    change p.getD i.val 0 = p.getD j.val 0 at eq
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at eq
    exact Fin.ext (nd.eq_of_getElem_eq hi hj eq)
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨inj,by simpa only [Fintype.card_fin] using size.symm⟩)
  apply bound_under_labels J e.symm
  apply repBound
  intro a b
  obtain ⟨i,rfl⟩ := e.surjective a
  obtain ⟨j,rfl⟩ := e.surjective b
  change (rows.getD (p.getD i.val 0) 0).testBit (p.getD j.val 0) = true ↔
    J.Adj (e.symm (e i)) (e.symm (e j))
  rw [e.symm_apply_apply,e.symm_apply_apply,← pairs i.val i.isLt j.val j.isLt]
  exact model i j


private def between {t : ℕ} {β : Type*} (H : SimpleGraph (Fin t)) (mask : β → Finset (Fin t)) :
    Fin t ⊕ β → Fin t ⊕ β → Prop
  | .inl a, .inl b => H.Adj a b
  | .inl a, .inr b => a ∈ mask b
  | .inr a, .inl b => b ∈ mask a
  | .inr _, .inr _ => False

private def maskNeighbors {t : ℕ} {β : Type*} [Fintype β] (mask : β → Finset (Fin t))
    (A : Finset (Fin t)) : Finset β := Finset.univ.filter (fun b => ((mask b) ∩ A).Nonempty)

private theorem critical_filter {t : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (H : SimpleGraph (Fin t)) (mask : β → Finset (Fin t))
    (low : ∀ S : Finset (Fin t ⊕ β), (∀ a b, between H mask a b → a ∈ S ∨ b ∈ S) → t ≤ S.card)
    (reach : ∀ b : β, ∃ S : Finset (Fin t ⊕ β), Sum.inr b ∈ S ∧ S.card = t ∧
      ∀ x y, between H mask x y → x ∈ S ∨ y ∈ S) :
    (∀ A, (∀ a ∈ A, ∀ b ∈ A, ¬ H.Adj a b) → A.card ≤ (maskNeighbors mask A).card) ∧
      ∀ v, ∃ A, (∀ a ∈ A, ∀ b ∈ A, ¬ H.Adj a b) ∧
        A.card = (maskNeighbors mask A).card ∧ v ∈ maskNeighbors mask A := by
  classical
  have lower (A : Finset (Fin t)) (ha : ∀ a ∈ A, ∀ b ∈ A, ¬ H.Adj a b) :
      A.card ≤ (maskNeighbors mask A).card := by
    let T := Aᶜ.disjSum (maskNeighbors mask A)
    have pick (a : Fin t) (b : β) (hm : a ∈ mask b) : Sum.inl a ∈ T ∨ Sum.inr b ∈ T := by
      by_cases h : a ∈ A
      · exact Or.inr (Finset.inr_mem_disjSum.mpr (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, a, Finset.mem_inter.mpr ⟨hm,h⟩⟩))
      · exact Or.inl (Finset.inl_mem_disjSum.mpr (Finset.mem_compl.mpr h))
    have ht := low T (by
      rintro (a | a) (b | b) he
      · by_cases h : a ∈ A
        · exact Or.inr (Finset.inl_mem_disjSum.mpr (Finset.mem_compl.mpr (fun hb => ha a h b hb he)))
        · exact Or.inl (Finset.inl_mem_disjSum.mpr (Finset.mem_compl.mpr h))
      · exact pick a b he
      · exact (pick b a he).symm
      · exact False.elim he)
    have hcard := Finset.card_compl_add_card A
    simp only [T, Finset.card_disjSum] at ht
    simp only [Fintype.card_fin] at hcard
    omega
  refine ⟨lower, ?_⟩
  intro b
  obtain ⟨S,hb,hs,hc⟩ := reach b
  let A := S.toLeftᶜ
  have independent : ∀ i ∈ A, ∀ j ∈ A, ¬ H.Adj i j := by
    intro i hi j hj he
    have h := hc (.inl i) (.inl j) he
    exact (h.elim (fun u => Finset.mem_compl.mp hi (Finset.mem_toLeft.mpr u))
      (fun v => Finset.mem_compl.mp hj (Finset.mem_toLeft.mpr v)))
  have bound := lower A independent
  have sub : maskNeighbors mask A ⊆ S.toRight := by
    intro v hv
    obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hv).2
    obtain ⟨him,hia⟩ := Finset.mem_inter.mp hi
    have hc' := hc (.inl i) (.inr v) him
    exact Finset.mem_toRight.mpr (hc'.resolve_left (fun e => Finset.mem_compl.mp hia (Finset.mem_toLeft.mpr e)))
  have counts := Finset.card_compl_add_card S.toLeft
  simp only [Fintype.card_fin] at counts
  have split := Finset.card_toLeft_add_card_toRight (u := S)
  have le := Finset.card_le_card sub
  have heq : (maskNeighbors mask A).card = S.toRight.card := by dsimp [A] at *; omega
  have ex := Finset.eq_of_subset_of_card_le sub heq.ge
  refine ⟨A, independent, ?_, ?_⟩
  · dsimp [A] at *; omega
  · rw [ex]
    exact Finset.mem_toRight.mpr hb



private def coreCodes : Nat → List Nat
  | 0 => [0]
  | 1 => [0]
  | 2 => [0, 1]
  | 3 => [0, 1, 3, 7]
  | 4 => [0, 1, 3, 7, 11, 12, 13, 15]
  | 5 => [0, 1, 3, 7, 11, 12, 13, 15, 75, 76, 77, 79, 86, 87, 116, 117, 235, 236]
  | _ => []

private def coreBook : Array Nat := #[
  0x10ca0000000000000000000000500a000c040802010200000000100a0000000000000000000000000000000000000000,
  0x3426400c0990014264004099000000000d0ca000000000000000000000090ca000c26400209900000000050ca000c3408020d02,
  0x4c3280110ca00483280100ca00003284000ca105c264016099003c26400e099001c264006099003c34080e0d0202c34080a0d02,
  0x26442c0990094264024099000034441d0ca000034441c0ca006c3280190ca008c264022099005c3280150ca00583280140ca0,
  0x18ca000000000000000003444000ca1000344436099000026442e099009c26402609900002644350ca00ac34082a0d02,
  0x3626400c8990016264004899000000000d8ca000000000000000000000098ca000e26400289900000000058ca000e3408028d02,
  0x4e3280118ca004a3280108ca00003284000ca105e264016899003e26400e899001e264006899003e34080e8d0202e34080a8d02,
  0x26442c8990096264024899000034441d8ca000034441c8ca006e3280198ca008e264022899005e3280158ca005a3280148ca0,
  0x2dc4400a7110025c4400871100003444000ca1000344436899000026442e899009e26402689900002644358ca00ae34082a8d02,
  0x13626404c8990116264044899000000004d8ca000000000000000000000498ca010e264042899003dc4400e7110035c4400c7110,
  0x14e3280518ca014a3280508ca00003284000ca115e264056899013e26404e899011e2640468990000000000000014dc408527102,
  0x26446c8990196264064899000034445d8ca000034445c8ca016e3280598ca018e264062899015e3280558ca015a3280548ca0,
  0x4dc440127110045c4401071100003444000ca1000344476899000026446e899019e26406689900002644758ca00000000000000,
  0x23626408c8990216264084899015dc440567110155c44054711014dc440527110145c44050711005dc440167110055c440147110,
  0x1963408a170a01863408608d020003284000ca125e264096899023e26408e899021e264086899013e34084e8d0212e34084a8d02,
  0x2644ac89902962640a489900003444768d020003444728d021d63408748d0228e2640a2899019e3408a570a018e3408628d02,
  0x6dc4401a7110065c4401871100003444000ca10003444b689900002644ae899029e2640a6899000026446e8d021ae34086a8d02,
  0x26dc4409a7110265c44098711000042840010a1175c4405c711016dc4405a7110165c44058711000042840010a1075c4401c7110,
  0x2adc280a970a02a9c280a870a00003284000ca100042c40010b100042c40010b100042c40010b100042840010a1275c4409c7110,
  0x2644ec89903962640e4899000034440010a100034440000000000000e970a038e2640e2899000042840010a12b9c280ac70a0,
  0x8dc440227110085c4402071100003444000ca100034440010b100026440010b100042c40010b100026440010a13ae3408ea8d02,
  0x28dc440a27110285c440a0711019dc440667110195c44064711018dc440627110185c44060711009dc440267110095c440247110,
  0x24e3280918ca024a3280908ca00003284000ca1395c440e4711038dc440e27110385c440e0711029dc440a67110295c440a47110,
  0x2644b18ca02ca3280b08ca000034449d8ca000034449c8ca026e3280998ca026a3280988ca025e3280958ca025a3280948ca0,
  0xadc4402a71100a5c4402871100003444000ca10003444bc8ca00002644b98ca02ea3280b88ca00002644b58ca02da3280b48ca0,
  0x2adc440aa71102a5c440a8711000044446e711000044446c71101adc4406a71101a5c44068711000044442e711000044442c7110,
  0x4adc4412a71104a5c4412871100004444000ca10004444ec71103adc440ea71103a5c440e871100004444ae71100004444ac7110,
  0x2644f18ca03ca3280f08ca00003444001131000344400113100044c400113100044c400113100044452e711000044452c7110,
  0x28443271100c5c4403071100003444000ca10003444001131000264400113100044c40011310004444f58ca00004444f48ca0,
  0x2844b271102c5c440b0711000028447671101d5c44074711000028447271101c5c44070711000028443671100d5c440347110,
  0x28453271104c5c4413071100002844000ca13d5c440f471100002844f271103c5c440f071100002844b671102d5c440b47110,
  0x264400113300044cc0011330003445767110000344574711000028457271105c5c44170711000028453671104d5c441347110,
  0x28443a71100e5c4403871100003444000ca10003444001133000264400113300044cc001133000264400113300044cc001133,
  0x2844ba71102e5c440b8711000044440010a100044447c711000028447a71101e5c44078711000044440010a100044443c7110,
  0x28453a71104e5c4413871100004444000ca100044440010b100028440010b100042c40010b100044440010a10004444bc7110,
  0x264400113300044cc00113300034440010a10003444001131000284400113100044c400113100044440010a100044453c7110,
  0x426264108899040626410089900003444000ca100034440010b100026440010b100042c40010b100044440010a10004444001133,
  0x43626410c8990416264104899046e26411a899044e264112899042e26410a899040e264102899046626411889904462641108990,
  0x4a6264128899048626412089900003284000ca145e264116899043e26410e899041e264106899047626411c89904562641148990,
  0x26452c8990496264124899000034453a899000034453289904ae26412a899048e26412289904e626413889904c62641308990,
  0x82dc4420a7110825c4420871100003444000ca1000344536899000026452e899049e264126899000026453c89904d62641348990,
  0x46454c8990000464544899056e26415a899054e264152899052e26414a899050e264142899083dc4420e7110835c4420c7110,
  0x46840011a158626416089900004644000ca1000464556899000046454e8990000464546899000046455c89900004645548990,
  0x26440011a1000464564899000034440011a1000344572899000046840011a158e264162899000046840011a15c62641708990,
  0x84dc442127110845c4421071100003444000ca1000344576899000026440011a1000464566899000026440011a10004645748990,
  0x63626418c89906162641848990000384656711000038465471100003846527110000384650711085dc442167110855c442147110,
  0x6a62641a889906862641a089900003844000ca1000384596899000038458e8990000384586899067626419c89906562641948990,
  0x2645ac89906962641a4899000034440011a300034440011a30003845aa89900003845a28990000468c0011a3000468c0011a3,
  0x86dc4421a7110865c4421871100003444000ca100034440011a30002645ae89900003845a6899000026440011a3000468c0011a3,
  0x46469a7110000464698711000038440010a100038465c711000038465a7110000384658711000042840010a1875c4421c7110,
  0x46840011a17862641e089900004644000ca100046440010b100046440010b100046440010b100046440010a100046469c7110,
  0x26440011a10004645e4899000034440010a100034440011a300038440011a10003845e2899000042840010a1000468c0011a3,
  0x88dc442227110885c4422071100003444000ca100034440010b100026440011a100046440010b100026440010a100046440011a3,
  0xa8dc442a27110a85c442a071100003884000e21995c4426471100003884000e21985c44260711089dc442267110895c442247110,
  0xa4e3282918ca0a4a3282908ca00003284000ca1000388c000e230003884000e21b85c442e07110000388c000e23000388c000e23,
  0x26472c8990c9626432489900003444000e2100034469c8ca00003884000e21c8e2643228990a5e3282958ca0a5a3282948ca0,
  0x8adc4422a71108a5c4422871100003444000ca10003444000e230002644000e21c9e26432689900002644000e23000388c000e23,
  0x4646aa71100004646a871100004444000e2100044466c71100003884000e219a5c44268711000044462e711000044462c7110,
  0x46840011a1ca5c4432871100004444000ca10004444000e230004644000e210004646e871100004444000e230004444000e23,
  0x26440011a1000464764899000034440011a1000344400113100046840011a100044c400113100044440011a100044472c7110,
  0x28463271108c5c4423071100003444000ca1000344400113100026440011a1000464400113100044440011a10004444000e23,
  0x2846b27110ac5c442b071100002844000e2100038467471100002844000e21000384670711000028463671108d5c442347110,
  0x2847327110cc5c4433071100002844000ca10003844000e230002844000e210003846f071100002844000e23000388c000e23,
  0x264400113300044cc0011330003444000e2100034440011a30002844000e21000384770711000028440011a3000468c0011a3,
  0x28463a71108e5c4423871100003444000ca100034440011a30002644000e21000384400113300026440011a3000468c0011a3,
  0x4646ba71100004646b8711000044440010a100044467c71100002844000e21000384678711000044440010a100044463c7110,
  0x28440011a1ce5c4433871100004444000ca100044440010b10004644000e2100046440010b100044440010a10004444000e23,
  0x26440011a1000464400113300034440010a1000344400113100028440011a1000384400113100044440010a100044440011a3,
  0x3444000ca100034440010b100026440011a100046440010b100044440010a100044440011a3]

private def coreWidth (t : Nat) := t*(t-1)/2

private def coreWord (t c : Nat) : Nat :=
  let i := [0,1,2,4,12,76].getD t 0 + c
  ((coreBook[i/16]?.getD 0) >>> (26*(i % 16))) % (2^26)

private def corePick (word i : Nat) : Nat := (word >>> (1+3*i)) % 8

private def coreCheck (t c : Nat) : Bool :=
  let w := coreWord t c
  let v := corePick w
  let d := w >>> 16
  (coreCodes t).contains c ||
    if w.testBit 0 then
      (v 0 < t && v 1 < t && v 2 < t && v 3 < t) &&
      ((v 0 != v 2) && (v 1 != v 3)) &&
      (coreEdge c (v 0) (v 1) && coreEdge c (v 1) (v 2) &&
        coreEdge c (v 2) (v 3) && coreEdge c (v 3) (v 0))
    else
      d < c && ((List.range t).all fun i => v i < t) &&
        ((List.range t).all fun i => (List.range t).all fun j =>
          (i == j || v i != v j) &&
          (!coreEdge c (v i) (v j) || d.testBit (pairBit i j)))

private theorem coreIndex_lt : ∀ t : Fin 6, ∀ i j : Fin t.val, i ≠ j →
    pairBit i.val j.val < coreWidth t.val := by decide

private theorem coreWidth_bound {t : Nat} (ht : t ≤ 5) (H : SimpleGraph (Fin t)) :
    labelCore H < 2^coreWidth t := by
  classical
  have h : labelCore H ≤ 2^coreWidth t - 1 := by
    apply Nat.le_of_testBit
    intro k hk
    simp only [labelCore,packMask_test,Bool.and_eq_true,decide_eq_true_eq] at hk
    obtain ⟨_,i,j,rfl,he⟩ := hk
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact coreIndex_lt ⟨t,by omega⟩ i j he.ne
  have := Nat.two_pow_pos (coreWidth t)
  omega

private theorem coreBit_bound {t d : Nat} (H : SimpleGraph (Fin t))
    (h : ∀ i j : Fin t, H.Adj i j → d.testBit (pairBit i.val j.val) = true) : labelCore H ≤ d := by
  classical
  apply Nat.le_of_testBit
  intro k hk
  simp only [labelCore, packMask_test,Bool.and_eq_true,decide_eq_true_eq] at hk
  obtain ⟨_,i,j,rfl,he⟩ := hk
  exact h i j he

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checkedCoreBook : ∀ t : Fin 6, ∀ c : Fin (2^(coreWidth t.val)),
    coreCheck t.val c.val = true := by decide +kernel

private theorem core_catalogue {t : Nat} (ht : t ≤ 5) (H : SimpleGraph (Fin t))
    (free : FourCycleFree H) (minimal : ∀ σ : Equiv.Perm (Fin t), labelCore H ≤ labelCore (H.comap σ)) :
    labelCore H ∈ coreCodes t := by
  classical
  let c := labelCore H
  let w := coreWord t c
  let v := corePick w
  let d := w >>> 16
  have checked := checkedCoreBook ⟨t,by omega⟩ ⟨c,coreWidth_bound ht H⟩
  change coreCheck t c = true at checked
  unfold coreCheck at checked
  rw [Bool.or_eq_true] at checked
  rcases checked with listed | proof
  · exact List.contains_iff_mem.mp listed
  change (if w.testBit 0 then _ else _) = true at proof
  cases parity : w.testBit 0 <;> rw [parity] at proof
  · change ((decide (d<c) && _) && _) = true at proof
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range,Bool.or_eq_true,
      beq_iff_eq,bne_iff_ne,Bool.not_eq_true'] at proof
    obtain ⟨⟨hlt,hv⟩, hp⟩ := proof
    let f (i : Fin t) : Fin t := ⟨v i.val,hv i.val i.isLt⟩
    have inj : Function.Injective f := by
      intro i j h
      have eq : v i.val = v j.val := congrArg Fin.val h
      exact Fin.ext (((hp i.val i.isLt j.val j.isLt).1).resolve_right (fun neq => neq eq))
    let σ := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp inj)
    have small : labelCore (H.comap σ) ≤ d := by
      apply coreBit_bound
      intro i j hij
      have yes : coreEdge c (v i.val) (v j.val) = true :=
        (labelCore_edge ht H (f i) (f j)).mpr hij
      exact ((hp i.val i.isLt j.val j.isLt).2).resolve_left (by rw [yes]; decide)
    exact False.elim ((Nat.not_lt_of_ge (minimal σ)) (lt_of_le_of_lt small hlt))
  · change ((v 0 < t && v 1 < t && v 2 < t && v 3 < t) &&
      ((v 0 != v 2) && (v 1 != v 3)) &&
      (coreEdge c (v 0) (v 1) && coreEdge c (v 1) (v 2) &&
        coreEdge c (v 2) (v 3) && coreEdge c (v 3) (v 0))) = true at proof
    simp only [Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at proof
    have ⟨⟨⟨⟨⟨b0,b1⟩,b2⟩,b3⟩,hn0,hn1⟩,⟨⟨l0,l1⟩,l2⟩,l3⟩ := proof
    let a : Fin t := ⟨v 0,b0⟩
    let b : Fin t := ⟨v 1,b1⟩
    let e : Fin t := ⟨v 2,b2⟩
    let f : Fin t := ⟨v 3,b3⟩
    exact False.elim (free a b e f (fun h => hn0 (congrArg Fin.val h))
      (fun h => hn1 (congrArg Fin.val h)) ⟨(labelCore_edge ht H a b).mp l0,
      (labelCore_edge ht H b e).mp l1,(labelCore_edge ht H e f).mp l2,(labelCore_edge ht H f a).mp l3⟩)



open PEqualNP.CircuitLowerBounds

private def collapse_wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

private lemma collapse_wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    collapse_wiresFrom (gs₁ ++ gs₂) w = collapse_wiresFrom gs₂ (collapse_wiresFrom gs₁ w) := by
  simp [collapse_wiresFrom, List.foldl_append]

private lemma collapse_wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, collapse_wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [collapse_wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : collapse_wiresFrom (g :: gs) w = collapse_wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

private lemma collapse_length_wiresFrom (gs : List Gate) (w : List Bool) :
    (collapse_wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := collapse_wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

private lemma collapse_getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (collapse_wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := collapse_wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

private lemma collapse_getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (collapse_wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (collapse_wiresFrom gs w).getD i false else false := by
  have hlen : (collapse_wiresFrom (gs.take k) w).length = w.length + k := by
    rw [collapse_length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, collapse_wiresFrom_append]
    exact (collapse_getD_wiresFrom_lt (gs.drop k) (collapse_wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

private lemma collapse_getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

private lemma collapse_getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (collapse_wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (collapse_wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (collapse_wiresFrom (gs.take k) w).length = w.length + k := by
    rw [collapse_length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : collapse_wiresFrom gs w =
      collapse_wiresFrom (gs.drop (k + 1))
        (collapse_wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (collapse_wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, collapse_wiresFrom_append]
    rfl
  rw [heq, collapse_getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, collapse_getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [collapse_getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

open PEqualNP.MetaComplexity PEqualNP.AndCount

private abbrev CollSide (n k : ℕ) := Finset (Fin n) × Finset (Fin k)

private def collVal {n k : ℕ} (U : Finset (Fin n)) (v : Fin k → Bool)
    (s : CollSide n k) : Bool := decide ((∃ x ∈ s.1, x ∈ U) ∨ ∃ i ∈ s.2, v i = true)

private def collCollect {n k : ℕ} (L : List ℕ) (s : ℕ → CollSide n k) : CollSide n k :=
  ⟨L.toFinset.biUnion (fun j => (s j).1), L.toFinset.biUnion (fun j => (s j).2)⟩

private lemma collCollect_true {n k : ℕ} (U : Finset (Fin n)) (v : Fin k → Bool)
    (L : List ℕ) (s : ℕ → CollSide n k) :
    collVal U v (collCollect L s) = true ↔ ∃ j ∈ L, collVal U v (s j) = true := by
  classical
  simp only [collVal, collCollect, decide_eq_true_eq, Finset.mem_biUnion, List.mem_toFinset]
  aesop

private def collOrig {n : ℕ} (C : Circuit) (U : Finset (Fin n)) (w : ℕ) : Bool :=
  (collapse_wiresFrom C.gates (List.ofFn (fun i : Fin n => decide (i ∈ U)))).getD w false

private lemma coll_gate {n : ℕ} (C : Circuit) (U : Finset (Fin n)) (j : ℕ)
    (h : j < C.gates.length) :
    collOrig C U (n+j) = C.gates[j].op.eval (C.gates[j].inputs.map
      (fun i => if i < n+j then collOrig C U i else false)) := by
  simpa only [collOrig,List.length_ofFn] using collapse_getD_wiresFrom_gate C.gates
    (List.ofFn (fun i : Fin n => decide (i ∈ U))) j h

private def collV {n k : ℕ} (C : Circuit) (ord : Fin k → ℕ) (U : Finset (Fin n))
    (j : Fin k) : Bool := collOrig C U (n+ord j)

private lemma coll_prior {n k w : ℕ} (C : Circuit) (ord : Fin k → ℕ)
    (ih : ∀ i < w, ∃ s : CollSide n k, (∀ j ∈ s.2, n + ord j ≤ i) ∧
      ∀ U : Finset (Fin n), collVal U (collV C ord U) s = collOrig C U i) :
    ∃ f : ℕ → CollSide n k, (∀ i j, j ∈ (f i).2 → n + ord j < w) ∧
      ∀ i (U : Finset (Fin n)), collVal U (collV C ord U) (f i) =
        if i < w then collOrig C U i else false := by
  classical
  let f (i : ℕ) : CollSide n k := if hi : i < w then (ih i hi).choose else (∅,∅)
  refine ⟨f, ?_, ?_⟩
  · intro i j hj
    by_cases hi : i < w
    · simp only [f,dite_eq_left hi] at hj
      exact Nat.lt_of_le_of_lt ((ih i hi).choose_spec.1 _ hj) hi
    · simp [f,hi] at hj
  · intro i U
    by_cases hi : i < w
    · simpa only [f,dite_eq_left hi,ite_eq_left hi] using (ih i hi).choose_spec.2 U
    · simp [f, hi, collVal]

private lemma coll_wires {n k : ℕ} (C : Circuit) (hm : Monotone2 C) (ord : Fin k → ℕ)
    (allAnd : ∀ (j : ℕ) (hj : j < C.gates.length), C.gates[j].op = GateOp.and →
      ∃ i, ord i = j) (w : ℕ) :
    ∃ s : CollSide n k, (∀ j ∈ s.2, n + ord j ≤ w) ∧
      ∀ U : Finset (Fin n), collVal U (collV C ord U) s = collOrig C U w := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hinput : w < n
    · let p : Fin n := ⟨w,hinput⟩
      refine ⟨({p},∅), by simp, ?_⟩
      intro U
      unfold collOrig
      rw [collapse_getD_wiresFrom_lt _ _ _ (by simpa using hinput)]
      rw [List.getD_eq_getElem _ _ (by simpa using hinput), List.getElem_ofFn]
      simp [collVal,p]
    let j := w-n
    have hw : n + j = w := by dsimp [j]; omega
    by_cases hj : j < C.gates.length
    · obtain h | h := (hm C.gates[j] (List.getElem_mem hj)).1
      · obtain ⟨z,hz⟩ := allAnd j hj h
        exact ⟨(∅,{z}), by simp [hz,hw], fun U => by simp [collVal,collV,hz,hw]⟩
      · obtain ⟨f,hf,he⟩ := coll_prior C ord ih
        refine ⟨collCollect C.gates[j].inputs f, ?_, ?_⟩
        · intro z hz
          obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
          exact Nat.le_of_lt (hf i z hi)
        · intro U
          rw [← hw, coll_gate C U j hj, show C.gates[j].op = GateOp.or from h]
          apply Bool.eq_iff_iff.mpr
          rw [collCollect_true]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
          simp_rw [he, hw]
    · refine ⟨(∅,∅), by simp, ?_⟩
      intro U
      unfold collOrig
      rw [List.getD_eq_default _ _ (by simp only [collapse_length_wiresFrom, List.length_ofFn]; omega)]
      simp [collVal]

private theorem coll_sides {n k : ℕ} (C : Circuit) (hm : Monotone2 C) (ord : Fin k ↪o ℕ)
    (allAnd : ∀ j (hj : j < C.gates.length), C.gates[j].op = GateOp.and →
      ∃ i, ord i = j)
    (ok : ∀ i, ∃ h : ord i < C.gates.length, C.gates[ord i].op = GateOp.and)
    (i : Fin k) :
    ∃ l r : CollSide n k,
      (∀ z ∈ l.2, z < i) ∧ (∀ z ∈ r.2, z < i) ∧
      ∀ U : Finset (Fin n), U.Nonempty →
        (collVal U (collV C ord U) l && collVal U (collV C ord U) r) = collV C ord U i := by
  classical
  obtain ⟨h,hop⟩ := ok i
  let g := C.gates[ord i]
  have hlen := (hm g (List.getElem_mem h)).2
  obtain ⟨f, hf, he⟩ := coll_prior (w := n + ord i) C ord
    (fun w _ => coll_wires C hm ord allAnd w)
  have ltj (a : ℕ) (z : Fin k) (hz : z ∈ (f a).2) : z < i :=
    ord.lt_iff_lt.mp (Nat.lt_of_add_lt_add_left (hf _ _ hz))
  have gate (U : Finset (Fin n)) :
      collV C ord U i = (g.inputs.map fun j => collVal U (collV C ord U) (f j)).all id := by
    rw [collV, coll_gate C U (ord i) h, hop]
    simp only [GateOp.eval, he, g]
  cases hL : g.inputs with
  | nil =>
    refine ⟨(Finset.univ,∅), (Finset.univ,∅), by simp, by simp, ?_⟩
    intro U hu
    rw [gate,hL]
    simpa [collVal] using (show ∃ x, x ∈ U from hu)
  | cons a L =>
    cases L with
    | nil =>
      refine ⟨f a, f a, ltj a, ltj a, ?_⟩
      intro U _
      simp [gate, hL]
    | cons b L =>
      have hem : L = [] := by rw [hL] at hlen; simpa using hlen
      subst L
      refine ⟨f a, f b, ltj a, ltj b, ?_⟩
      intro U _
      simp [gate, hL]

private lemma coll_empty_gate {n : ℕ} (D : AndCountCircuit n) (d : ℕ) :
    ∀ i, D.gateValFuel ∅ d i = false := by
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
    intro i
    simp [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue, ih]

private theorem coll_realize {n k : ℕ} (val : Finset (Fin n) → Fin k → Bool)
    (l r : Fin k → CollSide n k) (o : CollSide n k)
    (hl : ∀ i z, z ∈ (l i).2 → z < i) (hr : ∀ i z, z ∈ (r i).2 → z < i)
    (hv : ∀ i (U : Finset (Fin n)), U.Nonempty →
      (collVal U (val U) (l i) && collVal U (val U) (r i)) = val U i) :
    ∃ D : AndCountCircuit n, D.size = k ∧ D.WellFormed ∧ D.eval ∅ = false ∧
      ∀ U : Finset (Fin n), U.Nonempty → D.eval U = collVal U (val U) o := by
  classical
  let D : AndCountCircuit n := ⟨k,fun i => (l i).1,fun i => (l i).2,
    fun i => (r i).1,fun i => (r i).2,o.1,o.2⟩
  refine ⟨D, rfl, fun i => ⟨hl i,hr i⟩, ?_, ?_⟩
  · simp [AndCountCircuit.eval, AndCountCircuit.gateVal, coll_empty_gate]
  intro U hU
  have fuel (d : ℕ) : ∀ i : Fin k, i.val < d → D.gateValFuel U d i = val U i := by
    induction d with
    | zero => intro i; omega
    | succ d ih =>
      intro i hd
      have eqSide (s : CollSide n k) (hs : ∀ z ∈ s.2, z < i) :
          AndCountCircuit.sideTrue U s.1 s.2 i (D.gateValFuel U d) = collVal U (val U) s := by
        unfold AndCountCircuit.sideTrue collVal
        congr 1
        apply propext
        apply or_congr_right
        constructor
        · rintro ⟨j,hj,hji,hval⟩
          exact ⟨j,hj,(ih j (by have := hji; change j.val < i.val at this; omega)).symm.trans hval⟩
        · rintro ⟨j,hj,hval⟩
          have hji := hs j hj
          exact ⟨j,hj,hji,(ih j (by change j.val < i.val at hji; omega)).trans hval⟩
      change (AndCountCircuit.sideTrue U (l i).1 (l i).2 i (D.gateValFuel U d) &&
        AndCountCircuit.sideTrue U (r i).1 (r i).2 i (D.gateValFuel U d)) = _
      rw [eqSide _ (hl i), eqSide _ (hr i), hv _ _ hU]
  have gate (i : Fin k) : D.gateVal U i = val U i := fuel k i i.isLt
  simp only [AndCountCircuit.eval, gate, collVal, D]

private theorem collapse_and_count {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (A : Finset ℕ)
    (hm : Monotone2 C)
    (hG : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A) :
    ∃ D : AndCountCircuit n, D.size ≤ A.card ∧ D.WellFormed ∧ D.Computes G := by
  classical
  let T := A.filter (fun j => ∃ h : j < C.gates.length, C.gates[j].op = GateOp.and)
  let ord := T.orderEmbOfFin rfl
  have memOrd (i : Fin T.card) : ord i ∈ T := T.orderEmbOfFin_mem rfl i
  have allAnd (j : ℕ) (hj : j < C.gates.length) (ha : C.gates[j].op = GateOp.and) :
      ∃ i, ord i = j := by
    have hT : j ∈ T := Finset.mem_filter.mpr ⟨hA j _ (List.getElem?_eq_getElem hj) ha, hj,ha⟩
    change j ∈ Set.range (T.orderEmbOfFin rfl)
    rwa [Finset.range_orderEmbOfFin]
  have ok (i : Fin T.card) : ∃ h : ord i < C.gates.length, C.gates[ord i].op = GateOp.and :=
    (Finset.mem_filter.mp (memOrd i)).2
  choose l r hl hr hex using coll_sides (n := n) C hm ord allAnd ok
  obtain ⟨o,_,ho⟩ := coll_wires (n := n) C hm ord allAnd C.output
  obtain ⟨D,hsize,hw,hempty,hval⟩ := coll_realize (collV C ord) l r o hl hr hex
  refine ⟨D,hsize ▸ Finset.card_filter_le _ _,hw,?_⟩
  intro U
  by_cases hn : U.Nonempty
  · rw [hval U hn, ho]
    change C.eval (List.ofFn (fun i : Fin n => decide (i ∈ U))) = true ↔ _
    rw [hG]
    constructor
    · rintro ⟨u,v,hadj,hu,hv⟩
      exact ⟨u,of_decide_eq_true hu,v,of_decide_eq_true hv,hadj⟩
    · rintro ⟨u,hu,v,hv,hadj⟩
      exact ⟨u,v,hadj,decide_eq_true hu,decide_eq_true hv⟩
  · suffices h : U = ∅ by rw [h,hempty]; simp
    exact Finset.not_nonempty_iff_eq_empty.mp hn


open PEqualNP.AndCount

private theorem one_and_of_cover {n : ℕ} (G : SimpleGraph (Fin n)) (D : AndCountCircuit n)
    (h : D.Computes G) (low : ∀ S : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) → 1 ≤ S.card) :
    1 ≤ D.size := by
  classical
  by_contra! zero
  have vars (v : Fin n) (hv : v ∈ D.outVars) : False := by
    have e := (h {v}).mp (by
      apply decide_eq_true
      exact Or.inl ⟨v,hv,Finset.mem_singleton_self v⟩)
    simpa using e
  have noEdge (u v : Fin n) (huv : G.Adj u v) : False := by
    have e := (h {u,v}).mpr ⟨u,by simp,v,by simp,huv⟩
    rcases of_decide_eq_true e with ⟨a,ha,_⟩ | ⟨j,_,_⟩
    · exact vars a ha
    · have := j.isLt
      omega
  simpa using low ∅ (fun u v he => False.elim (noEdge u v he))


private def rejectPop (s : ℕ) : ℕ := (55157063682984551670960690248 >>> (3*s)) &&& 7
private def rejectPairs (s : ℕ) : ℕ := (2135833961384262493561583190285464573412925001109612895589066872643277448309491847560500871168000 >>> (10*s)) &&& 1023
private def rejectHits (ls : List ℕ) (s : ℕ) : ℕ := ls.countP (fun m => (m &&& s) != 0)
private def rejectLeaf (t c : ℕ) (ls : List ℕ) (tag : ℕ) : Bool :=
  if tag < 32 then
    decide (tag < 2^t) && ((c &&& rejectPairs tag) == 0) && decide (rejectHits ls tag < rejectPop tag)
  else if tag < 37 && tag - 32 < ls.length then
    (List.range (2^t)).all fun s => ((ls.getD (tag-32) 0 &&& s) == 0) ||
      ((c &&& rejectPairs s) != 0) || (rejectHits ls s != rejectPop s)
  else false

private def rejectSet (t s : ℕ) : Finset (Fin t) :=
  Finset.univ.filter (fun i => s.testBit i.val)

set_option maxRecDepth 10000 in
private theorem rejectPop_table : ∀ (t : Fin 6) (s : Fin 32), s.val < 2^t.val →
    rejectPop s.val = (rejectSet t.val s.val).card := by decide +kernel

private theorem rejectPairs_bound : ∀ s : Fin 32, rejectPairs s.val < 2^10 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem rejectPairs_table : ∀ (s : Fin 32) (b : Fin 10),
    (rejectPairs s.val).testBit b.val = true ↔
      ∃ i j : Fin 5, i ≠ j ∧ pairBit i.val j.val = b.val ∧
        s.val.testBit i.val = true ∧ s.val.testBit j.val = true := by decide +kernel

private theorem reject_small {s t : ℕ} (ht : t ≤ 5) (hs : s < 2^t) : s < 32 :=
  lt_of_lt_of_le hs (show 2^t ≤ 2^5 from Nat.pow_le_pow_right (by decide) ht)

private theorem reject_bit_lt {s t i : ℕ} (hs : s < 2^t) (hi : s.testBit i = true) : i < t := by
  by_contra! h
  have hz := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) h))
  simp [hi] at hz

private theorem reject_zero {a b : ℕ} : a &&& b = 0 ↔
    ¬ ∃ i, a.testBit i = true ∧ b.testBit i = true := by
  constructor
  · rintro h ⟨i,ha,hb⟩
    have hh := congrArg (fun x : ℕ => x.testBit i) h
    simp [Nat.testBit_and,ha,hb] at hh
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simpa [Nat.testBit_and] using not_and.mp (show ¬ (a.testBit i = true ∧ b.testBit i = true)
      from fun ⟨ha,hb⟩ => h ⟨i,ha,hb⟩)

private theorem reject_indep {t c s : ℕ} (ht : t ≤ 5) (hs : s < 2^t) :
    c &&& rejectPairs s = 0 ↔
    ∀ i ∈ rejectSet t s, ∀ j ∈ rejectSet t s, coreEdge c i.val j.val ≠ true := by
  rw [reject_zero]
  let S : Fin 32 := ⟨s, reject_small ht hs⟩
  constructor
  · intro h i hi j hj hij
    obtain ⟨hne,he⟩ := Bool.and_eq_true_iff.mp hij
    have ne : i.castLE ht ≠ j.castLE ht :=
      fun eq => (of_decide_eq_true hne) (congrArg (fun x : Fin 5 => x.val) eq)
    have bitlt := pairBit_bounded (i.castLE ht) (j.castLE ht) ne
    have p := (rejectPairs_table S ⟨_,bitlt⟩).mpr
      ⟨i.castLE ht,j.castLE ht,ne,rfl,(Finset.mem_filter.mp hi).2,(Finset.mem_filter.mp hj).2⟩
    exact h ⟨_,he,p⟩
  · rintro h ⟨b,hc,hb⟩
    have hb' : b < 10 := reject_bit_lt (rejectPairs_bound S) hb
    obtain ⟨i,j,ne,r,hi,hj⟩ := (rejectPairs_table S ⟨b,hb'⟩).mp hb
    let p : Fin t := ⟨i.val,reject_bit_lt hs hi⟩
    let q : Fin t := ⟨j.val,reject_bit_lt hs hj⟩
    have pq : p.val ≠ q.val := fun eq => ne (Fin.ext eq)
    exact h p (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
      q (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩) (by simpa [coreEdge,pq,p,q,r] using hc)

private theorem reject_hit {t s m : ℕ} (hs : s < 2^t) :
    m &&& s ≠ 0 ↔ ((rejectSet t m) ∩ (rejectSet t s)).Nonempty := by
  simp only [ne_eq, reject_zero, not_not]
  constructor
  · rintro ⟨i,hm,hi⟩
    exact ⟨⟨i,reject_bit_lt hs hi⟩,Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩⟩
  · rintro ⟨i,hi⟩
    obtain ⟨hm,hs'⟩ := Finset.mem_inter.mp hi
    exact ⟨i.val,(Finset.mem_filter.mp hm).2,(Finset.mem_filter.mp hs').2⟩

private theorem reject_hits_count (ls : List ℕ) {t s : ℕ} (hs : s < 2^t) :
    rejectHits ls s = (maskNeighbors (fun j : Fin ls.length => rejectSet t (ls.getD j.val 0))
      (rejectSet t s)).card := by
  have h := List.countP_ofFn ls.get (fun m => (m &&& s) != 0)
  rw [List.ofFn_get] at h
  rw [rejectHits,h]
  congr 1
  ext j
  simp [maskNeighbors, List.getD_eq_getElem?_getD, reject_hit hs, List.get_eq_getElem]

private theorem reject_recovers {t : ℕ} (A : Finset (Fin t)) : rejectSet t (encodeMask A) = A := by
  ext i
  simp [rejectSet,encodeMask,packMask_test]

private theorem rejectLeaf_sound {t c : ℕ} (ht : t ≤ 5) (ls : List ℕ) (tag : ℕ)
    (J : SimpleGraph (Fin (t+ls.length)))
    (model : ∀ i j : Fin (t+ls.length), splitEdge t c ls i.val j.val = true ↔ J.Adj i j)
    (low : ∀ S, VertexCover J S → t ≤ S.card)
    (reach : ∀ v, ∃ S, v ∈ S ∧ S.card = t ∧ VertexCover J S) :
    rejectLeaf t c ls tag = false := by
  classical
  let e : Fin t ⊕ Fin ls.length ≃ Fin (t+ls.length) := finSumFinEquiv
  let H := J.comap (fun i : Fin t => e (.inl i))
  let M := fun j : Fin ls.length => rejectSet t (ls.getD j.val 0)
  have core (i j : Fin t) : coreEdge c i.val j.val = true ↔ H.Adj i j := by
    simpa [H,e,splitEdge,i.isLt,j.isLt] using model (e (.inl i)) (e (.inl j))
  have rel (a b : Fin t ⊕ Fin ls.length) : between H M a b ↔ J.Adj (e a) (e b) := by
    cases a with
    | inl i =>
      cases b with
      | inl j => rfl
      | inr j => simpa [between,M,rejectSet,e,splitEdge,i.isLt] using model (e (.inl i)) (e (.inr j))
    | inr i =>
      cases b with
      | inl j => simpa [between,M,rejectSet,e,splitEdge,j.isLt] using model (e (.inr i)) (e (.inl j))
      | inr j => simpa [between,e,splitEdge] using model (e (.inr i)) (e (.inr j))
  have cf := critical_filter H M (by
    intro S h
    have le := low (S.map e.toEmbedding) (by
      intro x y hj
      obtain ⟨a,rfl⟩ := e.surjective x
      obtain ⟨b,rfl⟩ := e.surjective y
      simpa using h a b ((rel a b).mpr hj))
    simpa using le) (by
    intro b
    obtain ⟨S,hb,hs,hc⟩ := reach (e (.inr b))
    refine ⟨S.map e.symm.toEmbedding,by simpa using hb,by simpa using hs,?_⟩
    intro x y h
    simpa using hc (e x) (e y) ((rel x y).mp h))
  have pop (s : ℕ) (hs : s < 2^t) : rejectPop s = (rejectSet t s).card :=
    rejectPop_table ⟨t,by omega⟩ ⟨s,reject_small ht hs⟩ hs
  unfold rejectLeaf
  split
  · by_cases htag : tag < 2^t
    · by_cases hz : c &&& rejectPairs tag = 0
      · have ind := (reject_indep ht htag).mp hz
        have le := cf.1 (rejectSet t tag) (fun i hi j hj he => ind i hi j hj ((core i j).mpr he))
        rw [← reject_hits_count ls htag,← pop _ htag] at le
        simp [htag,hz,not_lt_of_ge le]
      · simp [hz]
    · simp [htag]
  · split
    · rename_i htag
      have hj : tag-32 < ls.length := by simpa using (Bool.and_eq_true_iff.mp htag).2
      let j : Fin ls.length := ⟨tag-32,hj⟩
      obtain ⟨A,ind,eq,hit⟩ := cf.2 j
      let s := encodeMask A
      have hs : s < 2^t := packMask_lt _ _
      have restore : rejectSet t s = A := reject_recovers A
      have zero := (reject_indep ht hs).mpr (fun i hi q hq hh =>
        ind i (restore ▸ hi) q (restore ▸ hq) ((core i q).mp hh))
      have p := pop s hs
      have nh := reject_hits_count ls hs
      rw [restore] at p nh
      have cnt : rejectHits ls s = rejectPop s := by rw [nh, p]; exact eq.symm
      have ne := (reject_hit (m := ls.getD j.val 0) hs).mpr (by
        rw [restore]
        exact (Finset.mem_filter.mp hit).2)
      apply Bool.eq_false_iff.mpr
      intro hall
      have bad := List.all_eq_true.mp hall s (List.mem_range.mpr hs)
      change ls.getD (tag-32) 0 &&& s ≠ 0 at ne
      simp [zero,cnt] at bad
      exact ne (by simpa only [List.getD_eq_getElem?_getD] using bad)
    · rfl

private def matrixRows : List Nat → Nat
  | [] => 0
  | r :: rs => (matrixRows rs <<< 16) ||| (r % 65536)

private def matrixLanes : Nat := 0x1000100010001000100010001000100010001

private def matrixColumns : List Nat → Nat
  | [] => 0
  | f :: fs => (matrixColumns fs <<< 1) ||| (f &&& matrixLanes)

private def matrixActual (rows p : List Nat) : Nat :=
  let r := matrixRows (p.map (fun v => rows.getD v 0))
  matrixColumns (p.map (fun v => r >>> v))

private def matrixOuter (ls : List Nat) (i : Nat) :=
  ls.foldr (fun m r => Nat.bit (m.testBit i) r) 0

private def matrixExpected (t c : Nat) (ls : List Nat) : Nat :=
  matrixRows (((List.range t).map fun i => coreRowMask t c i ||| (matrixOuter ls i <<< t)) ++
    ls.map fun m => m % (2^t))

private def matrixCheck (t c : Nat) (ls rows p : List Nat) : Bool :=
  let n := t+ls.length
  n ≤ 10 && rows.length == n && p.length == n && decide p.Nodup && p.all (· < rows.length) &&
    matrixExpected t c ls == matrixActual rows p

private theorem matrixRows_test (xs : List Nat) (i j : Nat) (hj : j < 16) :
    (matrixRows xs).testBit (16*i+j) = (xs.getD i 0).testBit j := by
  induction xs generalizing i with
  | nil => simp [matrixRows]
  | cons a xs ih =>
    change (((matrixRows xs) <<< 16) ||| (a % 2^16)).testBit _ = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
    cases i with
    | zero => simp [hj,Nat.not_le_of_lt hj]
    | succ k =>
      have ge : 16 ≤ 16*(k+1)+j := by omega
      have sub : 16*(k+1)+j-16 = 16*k+j := by omega
      simp [ge,Nat.not_lt.mpr ge,sub,ih]

private theorem matrixLanes_test : ∀ i : Fin 10, ∀ j : Fin 16,
    matrixLanes.testBit (16*i.val+j.val) = decide (j.val=0) := by decide

private theorem matrixColumns_test (xs : List Nat) (hxs : xs.length ≤ 10)
    (i j : Nat) (hi : i < 10) (hj : j < 16) :
    (matrixColumns xs).testBit (16*i+j) = (xs.getD j 0).testBit (16*i) := by
  induction xs generalizing i j with
  | nil => simp [matrixColumns]
  | cons a xs ih =>
    have hx : xs.length < 10 := by simpa using hxs
    change (((matrixColumns xs) <<< 1) ||| (a &&& matrixLanes)).testBit _ = _
    rw [Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,matrixLanes_test ⟨i,hi⟩ ⟨j,hj⟩]
    change (_ || (_ && decide (j=0))) = _
    cases j with
    | zero =>
      cases i with
      | zero => simp
      | succ k =>
        have ge : 1 ≤ 16*(k+1) := by omega
        have sub : 16*(k+1)-1 = 16*k+15 := by omega
        have old := ih hx.le k 15 (by omega) (by decide)
        have past : xs.getD 15 0 = 0 := List.getD_eq_default xs 0 (by omega)
        simp only [past,Nat.zero_testBit] at old
        simp [ge,sub,old]
    | succ k =>
      have ge : 1 ≤ 16*i+(k+1) := by omega
      have sub : 16*i+(k+1)-1 = 16*i+k := by omega
      simp [ge,sub,ih hx.le i k hi (by omega)]

private theorem matrixOuter_test (ls : List Nat) (i j : Nat) :
    (matrixOuter ls i).testBit j = (ls.getD j 0).testBit i := by
  induction ls generalizing j with
  | nil => simp [matrixOuter]
  | cons a xs ih =>
    cases j with
    | zero => simp [matrixOuter]
    | succ j => simpa [matrixOuter,Nat.testBit_bit_succ] using ih j

private theorem matrix_getD_map (xs : List Nat) (f : Nat → Nat) (i : Nat) (hi : i < xs.length) :
    (xs.map f).getD i 0 = f (xs.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ hi,List.getElem_map]

private theorem matrixActual_test (rows p : List Nat) (h : p.length ≤ 10) (i j : Nat)
    (hi : i < p.length) (hj : j < p.length) (hv : p.getD j 0 < 16) :
    (matrixActual rows p).testBit (16*i+j) = (rows.getD (p.getD i 0) 0).testBit (p.getD j 0) := by
  simp only [matrixActual]
  rw [matrixColumns_test _ (by simpa using h) i j (by omega) (by omega),
    matrix_getD_map _ _ _ hj,Nat.testBit_shiftRight,Nat.add_comm (p.getD j 0),
    matrixRows_test _ _ _ hv,matrix_getD_map _ _ _ hi]

private theorem matrixExpected_test (t c : Nat) (ls : List Nat) (i j : Nat)
    (hi : i < t+ls.length) (hj : j < t+ls.length) (hn : t+ls.length ≤ 10) :
    (matrixExpected t c ls).testBit (16*i+j) = splitEdge t c ls i j := by
  unfold matrixExpected
  rw [matrixRows_test _ _ _ (by omega)]
  by_cases a : i < t
  · rw [List.getD_append _ _ _ _ (by simpa using a), matrix_getD_map _ _ _ (by simpa using a)]
    have range : (List.range t).getD i 0 = i := by
      rw [List.getD_eq_getElem _ _ (by simpa using a),List.getElem_range]
    rw [range,Nat.testBit_or,Nat.testBit_shiftLeft]
    simp only [coreRowMask,packMask_test]
    by_cases b : j < t
    · simp [a,b,Nat.not_le_of_lt b,splitEdge]
    · simp [a,b,Nat.le_of_not_lt b,splitEdge,matrixOuter_test]
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt a)]
    simp only [List.length_map,List.length_range]
    rw [matrix_getD_map _ _ _ (by omega),Nat.testBit_mod_two_pow]
    by_cases b : j < t <;> simp [a,b,splitEdge]

private theorem matrixCheck_sound {t c : Nat} {ls rows p : List Nat}
    (ok : matrixCheck t c ls rows p = true) : repCheck t c ls rows p = true := by
  simp only [matrixCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨bound,size⟩,plen⟩,nd⟩,range⟩,eq⟩ := ok
  simp only [repCheck,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,List.all_eq_true,List.mem_range]
  refine ⟨⟨⟨⟨size,plen⟩,nd⟩,fun x hx => of_decide_eq_true (List.all_eq_true.mp range x hx)⟩,?_⟩
  intro i hi j hj
  have val : p.getD j 0 < rows.length := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.all_eq_true.mp range _ (List.getElem_mem _ ) |> of_decide_eq_true
  rw [← matrixExpected_test t c ls i j hi hj bound,eq,matrixActual_test _ _ (by omega) _ _ (by omega) (by omega) (by omega)]
private abbrev BranchState (α : Type*) := Nat × List α × List α

private def selectBranch {α : Type*} (ok : α → α → Bool) :
    Nat → Nat → List α → List α → Nat → Option (BranchState α)
  | 0, d, cs, acc, i => if i = 0 then some (d,cs,acc) else none
  | _+1, 0, cs, acc, i => if i = 0 then some (0,cs,acc) else none
  | _+1, d+1, [], acc, i => if i = 0 then some (d+1,[],acc) else none
  | k+1, d+1, m :: cs, acc, i =>
    if i % 2 = 0 then selectBranch ok k (d+1) cs acc (i/2)
    else if acc.all (ok m) then selectBranch ok k d cs (m::acc) (i/2)
    else none

private theorem visit_of_branches {α : Type*} (ok : α → α → Bool) (v : List α → Bool)
    (k d : Nat) (cs acc : List α)
    (h : ∀ i < 2^k, ∀ f, selectBranch ok k d cs acc i = some f →
      visitMasks ok v f.1 f.2.1 f.2.2 = true) : visitMasks ok v d cs acc = true := by
  induction k generalizing d cs acc with
  | zero => exact h 0 (by decide) (d,cs,acc) (by simp [selectBranch])
  | succ k ih =>
    have pos : 0 < 2^(k+1) := Nat.two_pow_pos _
    cases d with
    | zero => exact h 0 pos (0,cs,acc) (by simp [selectBranch])
    | succ d =>
      cases cs with
      | nil => exact h 0 pos (d+1,[],acc) (by simp [selectBranch])
      | cons m rest =>
        have left := ih (d+1) rest acc (fun i hi f hf => by
          apply h (2*i) (by rw [pow_succ]; omega) f
          simpa [selectBranch] using hf)
        rw [visitMasks,left,Bool.true_and]
        by_cases feasible : acc.all (ok m) = true
        · have right := ih d rest (m::acc) (fun i hi f hf => by
            apply h (2*i+1) (by rw [pow_succ]; omega) f
            simpa [selectBranch,feasible,Nat.add_div] using hf)
          simp [feasible,right]
        · simp [feasible]

private def branchCheck {α C : Type*} (ok : α → α → Bool) (step : List α → C → Option C)
    (k d : Nat) (cs acc : List α) (start : Nat → C) (i : Nat) : Bool :=
  match selectBranch ok k d cs acc i with
  | none => true
  | some (rem,cs',acc') => (inspectLeaves ok step rem cs' acc' (start i)).isSome

private def rangePass (p : Nat → Bool) (lo len : Nat) : Prop :=
  ((List.range len).all (fun j => p (lo+j))) = true

private theorem rangeJoin {p : Nat → Bool} {a b c : Nat} (ab : rangePass p a b)
    (bc : rangePass p (a+b) c) : rangePass p a (b+c) := by
  apply List.all_eq_true.mpr
  intro j hj
  have hj' := List.mem_range.mp hj
  by_cases lt : j < b
  · exact List.all_eq_true.mp ab j (List.mem_range.mpr lt)
  · have h := List.all_eq_true.mp bc (j-b) (List.mem_range.mpr (by omega))
    simpa only [show a+b+(j-b)=a+j by omega] using h

private theorem visit_of_pieces {α C : Type*} (ok : α → α → Bool)
    (step : List α → C → Option C) (v : List α → Bool)
    (valid : ∀ ls i j, step ls i = some j → v ls = true)
    (k d : Nat) (cs acc : List α) (start : Nat → C)
    (h : rangePass (branchCheck ok step k d cs acc start) 0 (2^k)) : visitMasks ok v d cs acc = true := by
  apply visit_of_branches ok v k d cs acc
  intro i hi f hf
  obtain ⟨rem,rest,chosen⟩ := f
  have good := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Nat.zero_add, branchCheck, hf] at good
  obtain ⟨j,hj⟩ := Option.isSome_iff_exists.mp good
  exact visit_of_inspect ok step v valid rem rest chosen _ j hj

/- Each base-sixteen digit counts the outside neighbors of one subset of the cover. A high bit identifies the subsets that meet the minimum-cover inequality. -/
private def laneDigits : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n+1, f => f 0 + 16 * laneDigits n (fun i => f (i+1))

private def laneRow (m : Nat) : Nat :=
  (#[0,21351050473470648687898014583954083856,22597220734568157366179999870955294976,22680298751974657944732132223422042384,22685144980220458816175817500189065216,22685470766424793324143650907494617104,22685489781183801174803252079127236864,22685491048834401698180558823902744848,22685491122780686731170467593842589696,22685491127751865554437453854180118544,22685491128042012178363542546417717504,22685491128061355286625281792566890768,22685491128062483637066782458420199424,22685491128062559490078413552096448528,22685491128062563917296991242388836608,22685491128062564212444896421741662480,22685491128062564229661857557203910656,22685491128062564230819300322613137424,22685491128062564230886855347831574784,22685491128062564230891359016179470608,22685491128062564230891621730739093504,22685491128062564230891639391644618768,22685491128062564230891640422436770048,22685491128062564230891640491156246800,22685491128062564230891640495164882944,22685491128062564230891640495434371088,22685491128062564230891640495450099968,22685491128062564230891640495451148560,22685491128062564230891640495451209728,22685491128062564230891640495451213840,22685491128062564230891640495451214080,22685491128062564230891640495451214096] : Array Nat)[m]?.getD 0

private def laneSum : List Nat → Nat
  | [] => 0
  | m :: ms => laneRow m + laneSum ms

private def laneBase : Nat := 69479530585397998016046966857464768376
private def laneStrict : Nat := 46794039457335433785155326362013554279

private def laneInd (t c : Nat) : Nat := laneDigits 32 fun s =>
  if s < 2^t ∧ c &&& rejectPairs s = 0 then 8 else 0

private def laneReject (t c : Nat) (ls : List Nat) : Bool :=
  if ls.length ≤ 5 ∧ ls.all (fun m => decide (m < 32)) then
    let ind := laneInd t c
    let n := laneSum ls
    if (n + laneBase) &&& ind != ind then true else
      let tight := ind ^^^ ((n + laneStrict) &&& ind)
      ls.any fun m => ((laneRow m <<< 3) &&& tight) == 0
  else false


private theorem laneDigits_add (n : Nat) (f g : Nat → Nat) :
    laneDigits n (fun s => f s + g s) = laneDigits n f + laneDigits n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp [laneDigits, ih, Nat.mul_add]
    omega

private theorem laneDigits_zero (n : Nat) : laneDigits n (fun _ => 0) = 0 := by
  induction n <;> simp [laneDigits, *]

private theorem laneDigits_congr (n : Nat) {f g : Nat → Nat} (h : ∀ i, i < n → f i = g i) :
    laneDigits n f = laneDigits n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [laneDigits]
    rw [h 0 (by omega), ih (fun i hi => h (i+1) (by omega))]

private theorem laneDigitBit (n s k : Nat) (f : Nat → Nat) (hf : ∀ i, i < n → f i < 16)
    (hs : s < n) (hk : k < 4) : (laneDigits n f).testBit (4*s+k) = (f s).testBit k := by
  induction n generalizing f s with
  | zero => omega
  | succ n ih =>
    obtain h0 := hf 0 (by omega)
    cases s with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, laneDigits]
      have hm := Nat.testBit_mod_two_pow (f 0 + 16 * laneDigits n (fun i => f (i+1))) 4 k
      have hmod : (f 0 + 16 * laneDigits n (fun i => f (i+1))) % 2^4 = f 0 := by
        change (_ + 16 * _) % 16 = _
        omega
      simpa only [hmod, decide_eq_true hk, Bool.true_and] using hm.symm
    | succ s =>
      rw [show 4*(s+1)+k = (4*s+k)+4 by omega, Nat.testBit_add]
      simp only [laneDigits]
      have hdiv : (f 0 + 16 * laneDigits n (fun i => f (i+1))) / 2^4 =
          laneDigits n (fun i => f (i+1)) := by
        change (_ + 16 * _) / 16 = _
        omega
      rw [hdiv, ih s (fun i => f (i+1)) (fun i hi => hf _ (by omega)) (by omega)]

private theorem laneBit (n s : Nat) (f : Nat → Nat) (hf : ∀ i, i < n → f i < 16) (hs : s < n) :
    (laneDigits n f).testBit (4*s+3) = decide (8 ≤ f s) := by
  rw [laneDigitBit n s 3 f hf hs (by decide), Nat.testBit_eq_decide_div_mod_eq]
  have h := hf s hs
  norm_num
  omega

set_option maxRecDepth 10000 in
private theorem laneRow_table : ∀ m : Fin 32, laneRow m = laneDigits 32
    (fun s => if (m.val &&& s) != 0 then 1 else 0) := by decide +kernel

set_option maxRecDepth 10000 in
private theorem laneBase_table : laneBase = laneDigits 32 (fun s => 8 - rejectPop s) ∧
    laneStrict = laneDigits 32 (fun s => 7 - rejectPop s) ∧
    (∀ s : Fin 32, rejectPop s ≤ 5) := by decide +kernel

private theorem laneSum_eq (ls : List Nat) (h : ∀ m ∈ ls, m < 32) :
    laneSum ls = laneDigits 32 (rejectHits ls) := by
  induction ls with
  | nil =>
    change 0 = laneDigits 32 (fun _ => 0)
    exact (laneDigits_zero 32).symm
  | cons m ms ih =>
    rw [laneSum, laneRow_table ⟨m, h m (by simp)⟩, ih (fun x hx => h x (by simp [hx])), ← laneDigits_add]
    apply laneDigits_congr
    intro s _
    by_cases e : (m &&& s) = 0 <;> simp [rejectHits, e, Nat.add_comm]

private theorem laneDigits_lt (n : Nat) (f : Nat → Nat) (hf : ∀ i, i < n → f i < 16) :
    laneDigits n f < 16^n := by
  induction n generalizing f with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    have a := ih (fun i => f (i+1)) (fun i hi => hf (i+1) (by omega))
    have b := hf 0 (by omega)
    simp only [laneDigits, pow_succ]
    omega

private theorem laneInd_bit (t c i : Nat) :
    (laneInd t c).testBit i = true ↔
    ∃ s, s < 32 ∧ s < 2^t ∧ c &&& rejectPairs s = 0 ∧ i = 4*s+3 := by
  let f s := if s < 2^t ∧ c &&& rejectPairs s = 0 then 8 else 0
  have hf : ∀ i, i < 32 → f i < 16 := by intro i _; dsimp [f]; split <;> decide
  change (laneDigits 32 f).testBit i = true ↔ _
  by_cases hb : i < 128
  · let s := i / 4
    have hs : s < 32 := by dsimp [s]; omega
    let k := i % 4
    have hk : k < 4 := Nat.mod_lt _ (by decide)
    have hi : i = 4*s+k := by dsimp [s,k]; omega
    rw [hi, laneDigitBit 32 s k f hf hs hk]
    have eight : (8 : Nat).testBit k = decide (k=3) := by interval_cases k <;> decide
    constructor
    · intro h
      unfold f at h
      split at h
      · rename_i ok
        rw [eight] at h
        exact ⟨s,hs,ok.1,ok.2,by rw [of_decide_eq_true h]⟩
      · simp at h
    · rintro ⟨a,_,ha,hc,eq⟩
      have ea : a = s := by omega
      have ek : k = 3 := by omega
      subst a
      simp only [f,ha,hc,and_self,↓reduceIte,ek]
      decide
  · have hn : laneDigits 32 f < 2^i := lt_of_lt_of_le (laneDigits_lt 32 f hf)
      (show 16^32 ≤ 2^i by exact Nat.pow_le_pow_right (show 0 < 2 by decide) (show 128 ≤ i by omega))
    simp [Nat.testBit_lt_two_pow hn]
    omega

private theorem lane_high (ls : List Nat) (hm : ∀ m ∈ ls, m < 32) (hlen : ls.length ≤ 5)
    (s : Nat) (hs : s < 32) (b : Nat) (hb : b = 7 ∨ b = 8) :
    (laneSum ls + laneDigits 32 (fun i => b - rejectPop i)).testBit (4*s+3) =
    decide (8 ≤ rejectHits ls s + (b - rejectPop s)) := by
  rw [laneSum_eq ls hm, ← laneDigits_add]
  apply laneBit
  · intro i _
    have hcount : rejectHits ls i ≤ ls.length := List.countP_le_length
    omega
  · exact hs

set_option maxRecDepth 10000 in
private theorem laneRow_high : ∀ m s : Fin 32,
    ((laneRow m <<< 3).testBit (4*s.val+3)) = (m.val &&& s.val != 0) := by decide +kernel

private theorem laneReject_of_scalar (t c : Nat) (ht : t ≤ 5) (ls : List Nat)
    (scalar : ∀ tag, rejectLeaf t c ls tag = false) : laneReject t c ls = false := by
  unfold laneReject
  split
  next valid =>
    obtain ⟨hlen,hmasks⟩ := valid
    have hm : ∀ m ∈ ls, m < 32 := by
      intro m mem
      exact of_decide_eq_true (List.all_eq_true.mp hmasks m mem)
    have bound (s : Nat) (hs : s < 2^t) (hind : c &&& rejectPairs s = 0) :
        rejectPop s ≤ rejectHits ls s := by
      have hs32 : s < 32 := lt_of_lt_of_le hs (show 2^t ≤ 2^5 from Nat.pow_le_pow_right (by decide) ht)
      have h := scalar s
      simpa [rejectLeaf, hs32, hs, hind] using h
    have allbound : (laneSum ls + laneBase) &&& laneInd t c = laneInd t c := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and]
      cases h : (laneInd t c).testBit i with
      | false => simp
      | true =>
        obtain ⟨s,hs,hs',hind,rfl⟩ := (laneInd_bit t c i).mp h
        rw [laneBase_table.1, lane_high ls hm hlen s hs 8 (.inr rfl)]
        have a := bound s hs' hind
        have b : rejectPop s ≤ 5 := laneBase_table.2.2 ⟨s,hs⟩
        simp [show 8 ≤ rejectHits ls s + (8 - rejectPop s) by omega]
    simp only [allbound, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    apply List.any_eq_false.mpr
    intro m mem
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp mem
    have jlt : j < 5 := by omega
    have excluded := scalar (32+j)
    have js : 32+j < 37 := by omega
    have bad : ¬ (List.range (2^t)).all (fun s =>
        ((ls[j] &&& s) == 0) || ((c &&& rejectPairs s) != 0) || (rejectHits ls s != rejectPop s)) = true := by
      simpa [rejectLeaf,js,hj,List.getD_eq_getElem?_getD] using excluded
    rw [List.all_eq_true] at bad
    push Not at bad
    obtain ⟨s,hs,hb⟩ := bad
    have hs' := List.mem_range.mp hs
    have hs32 : s < 32 := lt_of_lt_of_le hs' (show 2^t ≤ 2^5 from Nat.pow_le_pow_right (by decide) ht)
    replace hb := Bool.eq_false_iff.mpr hb
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at hb
    obtain ⟨⟨hit,ind⟩,tight⟩ := hb
    have hact := (laneInd_bit t c (4*s+3)).mpr ⟨s,hs32,hs',ind,rfl⟩
    have hr := laneRow_high ⟨ls[j],hm _ (List.getElem_mem hj)⟩ ⟨s,hs32⟩
    have pop : rejectPop s ≤ 5 := laneBase_table.2.2 ⟨s,hs32⟩
    have hstrict : (laneSum ls + laneStrict).testBit (4*s+3) = false := by
      rw [laneBase_table.2.1, lane_high ls hm hlen s hs32 7 (.inl rfl)]
      simp [tight,show ¬ 8 ≤ rejectPop s + (7 - rejectPop s) by omega]
    intro zero
    have hz := beq_iff_eq.mp zero
    have bits := congrArg (fun n : Nat => n.testBit (4*s+3)) hz
    simp [Nat.testBit_and, Nat.testBit_xor, hact, hstrict, hr, hit] at bits
  next => rfl

private theorem small_case {n t : Nat} (h2 : t < 2) (J : SimpleGraph (Fin n))
    (hl : ∀ S, VertexCover J S → t ≤ S.card) : AndBound n t J := by
  intro C A hm he hA
  rcases t with _|t
  · exact Nat.zero_le _
  · have eq : t = 0 := by omega
    subst t
    obtain ⟨D,hsize,_,hD⟩ := collapse_and_count J C A hm he hA
    exact (one_and_of_cover J D hD hl).trans hsize

private def orbitDest (perm i : Nat) := (perm >>> (3*i)) % 8

private def orbitMap (table m : Nat) := (table >>> (5*(m % 32))) % 32

private def orbitPermCheck (t c perm table : Nat) : Bool :=
  let vs := List.range t
  let p := orbitDest perm
  (vs.all fun i => p i < t) &&
  (vs.all fun i => vs.all fun j => (i == j || p i != p j) && (coreEdge c i j == coreEdge c (p i) (p j))) &&
  ((List.range 32).all fun m => vs.all fun i => (orbitMap table m).testBit (p i) == m.testBit i)

private def orbitSet (ls : List Nat) : Nat :=
  ls.foldr (fun m r => (1 <<< m) ||| r) 0

private def orbitImage (table : Nat) (ls : List Nat) : Nat :=
  ls.foldr (fun m r => (1 <<< orbitMap table m) ||| r) 0

private def orbitCheck (table size family : Nat) (ls : List Nat) : Bool :=
  ls.length == size && orbitImage table ls == family

private theorem orbitSet_test (ls : List Nat) (m : Nat) :
    (orbitSet ls).testBit m = true ↔ m ∈ ls := by
  induction ls with
  | nil => simp [orbitSet]
  | cons x xs ih =>
    change ((1 <<< x) ||| orbitSet xs).testBit m = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true,ih,Nat.one_shiftLeft,Nat.testBit_two_pow]
    simp [eq_comm]

private theorem orbitImage_test (ls : List Nat) (table : Nat) :
    orbitImage table ls = orbitSet (ls.map (orbitMap table)) := by
  induction ls with
  | nil => rfl
  | cons a xs ih =>
    simpa only [List.map_cons,orbitImage,orbitSet,List.foldr_cons] using
      congrArg (fun s => (1 <<< orbitMap table a) ||| s) ih

private theorem orbitTransport {t c perm table : Nat} (ht : t ≤ 5)
    (permOK : orbitPermCheck t c perm table = true)
    (ls base : List Nat) (baseND : base.Nodup)
    (ok : orbitCheck table base.length (orbitSet base) ls = true)
    (known : ∀ K : SimpleGraph (Fin (t+base.length)),
      (∀ a b : Fin (t+base.length), splitEdge t c base a.val b.val = true ↔ K.Adj a b) →
      AndBound _ t K)
    (J : SimpleGraph (Fin (t+ls.length)))
    (model : ∀ i j : Fin (t+ls.length), splitEdge t c ls i.val j.val = true ↔ J.Adj i j) :
    AndBound _ t J := by
  classical
  simp only [orbitPermCheck,Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq,bne_iff_ne] at permOK
  obtain ⟨⟨range,adj⟩,bits⟩ := permOK
  simp only [orbitCheck,Bool.and_eq_true,beq_iff_eq,orbitImage_test] at ok
  obtain ⟨len,setEq⟩ := ok
  let f (i : Fin t) : Fin t := ⟨orbitDest perm i.val,range i.val i.isLt⟩
  have inj : Function.Injective f := by
    intro i j h
    apply Fin.ext
    exact ((adj i.val i.isLt j.val j.isLt).1).resolve_right (fun ne => ne (congrArg Fin.val h))
  let σ := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp inj)
  have lift (i : Fin t) (m : Nat) : (orbitMap table m).testBit (σ i).val = m.testBit i.val := by
    have hh := bits (m % 32) (Nat.mod_lt _ (by decide)) i.val i.isLt
    change (orbitMap table m).testBit (orbitDest perm i.val) = _
    have hi : i.val < 5 := lt_of_lt_of_le i.isLt ht
    have hm : (m % 32).testBit i.val = m.testBit i.val := by
      change (m % 2^5).testBit i.val = _
      exact (Nat.testBit_mod_two_pow m 5 i.val).trans (by simp [hi])
    simpa only [orbitMap,Nat.mod_mod,hm] using hh
  have back (j : Fin base.length) : ∃ k : Fin ls.length, orbitMap table (ls.get k) = base.get j := by
    have hx : (orbitSet base).testBit (base.get j) = true :=
      (orbitSet_test _ _).mpr (base.get_mem j)
    rw [← setEq,orbitSet_test,List.mem_map] at hx
    obtain ⟨m,hm,em⟩ := hx
    obtain ⟨k,rfl⟩ := List.mem_iff_get.mp hm
    exact ⟨k,em⟩
  choose g hg using back
  have gj : Function.Injective g := by
    intro i j h
    apply (List.nodup_iff_injective_get.mp baseND)
    rw [← hg i,← hg j,h]
  let e := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr
    ⟨gj,by simpa using len.symm⟩)
  let src : Fin t ⊕ Fin base.length ≃ Fin (t+base.length) := finSumFinEquiv
  let dst : Fin t ⊕ Fin ls.length ≃ Fin (t+ls.length) := finSumFinEquiv
  let v := (src.symm.trans (Equiv.sumCongr σ.symm e)).trans dst
  have left (a : Fin t) : v (src (.inl a)) = dst (.inl (σ.symm a)) := by simp [v]
  have right (a : Fin base.length) : v (src (.inr a)) = dst (.inr (e a)) := by simp [v]
  have bit (a : Fin t) (b : Fin base.length) :
      (base.getD b.val 0).testBit a.val = (ls.getD (e b).val 0).testBit (σ.symm a).val := by
    rw [List.getD_eq_getElem _ _ b.isLt,List.getD_eq_getElem _ _ (e b).isLt]
    change (base.get b).testBit a.val = (ls.get (g b)).testBit (σ.symm a).val
    have h := lift (σ.symm a) (ls.get (g b))
    simpa only [σ.apply_symm_apply,hg] using h
  apply bound_under_labels J v
  apply known
  intro i j
  change _ ↔ J.Adj (v i) (v j)
  rw [← model]
  apply Bool.eq_iff_iff.mp
  obtain ⟨a | a,rfl⟩ := src.surjective i <;> obtain ⟨b | b,rfl⟩ := src.surjective j
  · rw [left,left]
    have h := (adj (σ.symm a).val (σ.symm a).isLt (σ.symm b).val (σ.symm b).isLt).2
    change coreEdge c (σ.symm a).val (σ.symm b).val = coreEdge c (σ (σ.symm a)).val (σ (σ.symm b)).val at h
    simpa [src,dst,splitEdge,a.isLt,b.isLt,(σ.symm a).isLt,(σ.symm b).isLt] using h.symm
  · rw [left,right]
    simpa [src,dst,splitEdge,a.isLt,(σ.symm a).isLt] using bit a b
  · rw [right,left]
    simpa [src,dst,splitEdge,b.isLt,(σ.symm b).isLt] using bit b a
  · rw [right,right]
    simp [src,dst,splitEdge]

private def minimumScore (ls : List Nat) : Nat :=
  orbitSet (ls.map fun m => 31-m)

private def minimumActionOK (t c perm table : Nat) : Bool :=
  orbitPermCheck t c perm table && (List.range (2^t)).all fun m => orbitMap table m < 2^t

private def minimumFamilyOK (t c : Nat) (ls : List Nat) : Prop :=
  ∀ perm table, minimumActionOK t c perm table = true →
    minimumScore (ls.map (orbitMap table)) ≤ minimumScore ls

private noncomputable def minimumQuality {t : Nat} (M : Finset (Finset (Fin t))) : Nat :=
  minimumScore (M.image encodeMask).toList

private theorem minimumScore_congr {a b : List Nat} (h : a.toFinset = b.toFinset) :
    minimumScore a = minimumScore b := by
  have mem (m : Nat) : m ∈ a ↔ m ∈ b := by
    simpa using Finset.ext_iff.mp h m
  apply Nat.eq_of_testBit_eq
  intro k
  apply Bool.eq_iff_iff.mpr
  simp only [minimumScore,orbitSet_test,List.mem_map]
  constructor <;> rintro ⟨x,hx,hk⟩
  · exact ⟨x,(mem x).mp hx,hk⟩
  · exact ⟨x,(mem x).mpr hx,hk⟩

private theorem minimumFamily_numeric {t : Nat} (ht : t ≤ 5) (H : SimpleGraph (Fin t))
    (M : Finset (Finset (Fin t))) (ls : List Nat) (marks : ls.toFinset = M.image encodeMask)
    (optimal : ∀ τ : Equiv.Perm (Fin t), labelCore (H.comap τ) = labelCore H →
      minimumQuality (M.image (fun S => S.image τ.symm)) ≤ minimumQuality M) :
    minimumFamilyOK t (labelCore H) ls := by
  classical
  intro perm table h
  simp only [minimumActionOK,orbitPermCheck,Bool.and_eq_true,List.all_eq_true,List.mem_range,
    decide_eq_true_eq,Bool.or_eq_true,beq_iff_eq,bne_iff_ne] at h
  obtain ⟨⟨⟨range,adj⟩,bits⟩,bound⟩ := h
  let f (i : Fin t) : Fin t := ⟨orbitDest perm i.val,range i.val i.isLt⟩
  have inj : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact ((adj i.val i.isLt j.val j.isLt).1).resolve_right (fun ne => ne (congrArg Fin.val he))
  let σ := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp inj)
  have same : H.comap σ.symm = H := by
    ext a b
    obtain ⟨i,rfl⟩ := σ.surjective a
    obtain ⟨j,rfl⟩ := σ.surjective b
    change H.Adj (σ.symm (σ i)) (σ.symm (σ j)) ↔ H.Adj (σ i) (σ j)
    rw [σ.symm_apply_apply,σ.symm_apply_apply,← labelCore_edge ht H,← labelCore_edge ht H]
    rw [(adj i.val i.isLt j.val j.isLt).2]
    rfl
  have hopt := optimal σ.symm (congrArg labelCore same)
  change minimumQuality (M.image (fun S => S.image σ)) ≤ minimumQuality M at hopt
  have encode (S : Finset (Fin t)) :
      orbitMap table (encodeMask S) = encodeMask (S.image σ) := by
    have small : encodeMask S < 2^t := packMask_lt _ _
    have small' : encodeMask S < 32 := lt_of_lt_of_le small
      (show 2^t ≤ 2^5 from Nat.pow_le_pow_right (by decide) ht)
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases inside : j < t
    · let v : Fin t := ⟨j,inside⟩
      obtain ⟨u,hu⟩ := σ.surjective v
      have idx : orbitDest perm u.val = j := congrArg Fin.val hu
      have hb := bits (encodeMask S) small' u.val u.isLt
      rw [idx] at hb
      rw [hb]
      simp only [encodeMask,packMask_test,u.isLt,inside,decide_true,Bool.true_and,dite_eq_left]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      change u ∈ S ↔ v ∈ S.image σ
      rw [← hu]
      simp
    · have large := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_lt inside)
      exact (Nat.testBit_lt_two_pow ((bound _ small).trans_le large)).trans
        (Nat.testBit_lt_two_pow ((packMask_lt _ _).trans_le large)).symm
  have eq₁ : minimumScore ls = minimumQuality M := by
    apply minimumScore_congr
    simpa using marks
  have eq₂ : minimumScore (ls.map (orbitMap table)) =
      minimumQuality (M.image fun S => S.image σ) := by
    apply minimumScore_congr
    have mapSet : (ls.map (orbitMap table)).toFinset = ls.toFinset.image (orbitMap table) := by
      ext m
      simp
    rw [mapSet,marks,Finset.toList_toFinset,Finset.image_image,Finset.image_image]
    exact Finset.image_congr (fun S _ => encode S)
  simpa only [eq₁,eq₂] using hopt

private theorem minimumFamily_prune {t c perm table : Nat} {ls : List Nat}
    (small : minimumFamilyOK t c ls) (act : minimumActionOK t c perm table = true)
    (better : minimumScore ls < minimumScore (ls.map (orbitMap table))) : False :=
  (Nat.not_lt_of_ge (small perm table act)) better

private theorem minimum_rank_from_codes
    (check : ℕ → ℕ → List ℕ → Bool)
    (allChecks : ∀ t, t ≤ 5 → ∀ H : SimpleGraph (Fin t),
      FourCycleFree H → (∀ σ : Equiv.Perm (Fin t), labelCore H ≤ labelCore (H.comap σ)) →
      visitMasks maskPair (check t (labelCore H)) t
        ((List.range (2^t)).filter (eligibleMask t (labelCore H))) [] = true)
    (sound : ∀ t c ls, t ≤ 5 → c < 1024 → ls.Nodup → minimumFamilyOK t c ls → check t c ls = true →
      ∀ J : SimpleGraph (Fin (t+ls.length)),
      (∀ i j, splitEdge t c ls i.val j.val = true ↔ J.Adj i j) →
      (∀ S, VertexCover J S → t ≤ S.card) →
      (∀ w, ∃ S, w ∈ S ∧ S.card = t ∧ VertexCover J S) → AndBound _ t J)
    {n t : ℕ} (G : SimpleGraph (Fin n)) (ht : t ≤ 5) (hfree : FourCycleFree G)
    (hcover : ∀ S, VertexCover G S → t ≤ S.card) : AndBound n t G := by
  classical
  refine reduce_to_critical_graphs (fun k r J hr hk hf hlow reach => ?_) G ht hfree hcover
  by_cases pos : 0 < k
  · obtain ⟨C, _, hc, hC⟩ := reach ⟨0,pos⟩
    obtain ⟨H,M,f,hmin,optimal,hsize,hnon,hpair,hiso⟩ :=
      minimum_split_representation J labelCore minimumQuality C hC hc hk hf hlow reach
    obtain ⟨hfreeH,hrow⟩ := core_restrictions J H M f hf hiso
    have eligible := fun S hS => eligible_for_model hr H S (hnon S hS) (hrow S hS)
    obtain ⟨ls, hn, hset, hcheck⟩ := enumerate_mask_sets M _ _ hsize eligible hpair
      (allChecks r hr H hfreeH hmin)
    obtain ⟨g, hg⟩ := splitEdge_model hr H M ls hn hset
    let e := g.trans f
    apply bound_under_labels J e
    apply sound r (labelCore H) ls hr (packMask_lt _ _) hn
      (minimumFamily_numeric hr H M ls hset optimal) hcheck (J.comap e)
    · exact fun i j => (hg i j).trans (hiso _ _)
    · intro S hS
      have := hlow (S.map e.toEmbedding) (fun a b hab => by
        obtain ⟨i,rfl⟩ := e.surjective a
        obtain ⟨j,rfl⟩ := e.surjective b
        exact (hS i j hab).imp (fun h => Finset.mem_map.mpr ⟨i,h,rfl⟩)
          (fun h => Finset.mem_map.mpr ⟨j,h,rfl⟩))
      simpa using this
    · intro w
      obtain ⟨S,hw,hs,hc⟩ := reach (e w)
      let T := S.map e.symm.toEmbedding
      have mem (v) : v ∈ T ↔ e v ∈ S := by simp [T]
      exact ⟨T, (mem w).mpr hw, by simpa [T] using hs,
        fun a b h => (hc _ _ h).imp (mem a).mpr (mem b).mpr⟩
  · have h := hlow ∅ (fun a _ _ => False.elim (by have := a.isLt; omega))
    simp at h
    subst r
    exact fun _ _ _ _ _ => Nat.zero_le _


private theorem minimumScore_mono {a b : List Nat} (h : a ⊆ b) : minimumScore a ≤ minimumScore b := by
  apply Nat.le_of_testBit
  intro i hi
  rw [minimumScore, orbitSet_test] at hi ⊢
  exact List.map_subset _ h hi

private theorem prefix_improves {acc rest ls : List Nat} {table : Nat}
    (chosen : acc ⊆ ls) (possible : ls ⊆ acc ++ rest)
    (cut : minimumScore (acc ++ rest) < minimumScore (acc.map (orbitMap table))) :
    minimumScore ls < minimumScore (ls.map (orbitMap table)) :=
  lt_of_le_of_lt (minimumScore_mono possible)
    (lt_of_lt_of_le cut (minimumScore_mono (List.map_subset _ chosen)))

private def inspectHint {C : Type*} (h : Option (Bool × C)) (run : C → Option C) : Option C :=
  match h with
  | none => none
  | some (true,j) => some j
  | some (false,j) => run j

private theorem inspectHint_elim {C : Type*} {h : Option (Bool × C)} {run : C → Option C}
    {P : Prop} {j : C} (e : inspectHint h run = some j)
    (cut : ∀ i, h = some (true,i) → P)
    (next : ∀ i, h = some (false,i) → run i = some j → P) : P := by
  cases hh : h with
  | none => simp [inspectHint,hh] at e
  | some data =>
    rcases data with ⟨d,i⟩
    cases d with
    | false => exact next i hh (by simpa [inspectHint,hh] using e)
    | true => exact cut i hh

private def prefixInspect {α C : Type*} (ok : α → α → Bool)
    (hint : List α → List α → C → Option (Bool × C)) (step : List α → C → Option C) :
    Nat → List α → List α → C → Option C
  | 0, _, acc, i => inspectHint (hint [] acc i) (step acc)
  | _+1, [], acc, i => inspectHint (hint [] acc i) (step acc)
  | d+1, m::rest, acc, i =>
    inspectHint (hint (m::rest) acc i) fun start => do
      let mid ← prefixInspect ok hint step (d+1) rest acc start
      if acc.all (ok m) then prefixInspect ok hint step d rest (m::acc) mid else some mid
termination_by structural _ cs _ _ => cs

private theorem visit_of_extensions {α : Type*} (ok : α → α → Bool) (v : List α → Bool)
    (d : Nat) (cs acc : List α)
    (allgood : ∀ ls, acc ⊆ ls → ls ⊆ acc ++ cs → v ls = true) :
    visitMasks ok v d cs acc = true := by
  induction cs generalizing d acc with
  | nil =>
    cases d <;> rw [visitMasks] <;> exact allgood acc (fun _ h => h) (fun _ h => List.mem_append_left _ h)
  | cons m cs ih =>
    cases d with
    | zero => rw [visitMasks]; exact allgood acc (fun _ h => h) (fun _ h => List.mem_append_left _ h)
    | succ d =>
      have widen : acc ++ cs ⊆ acc ++ m :: cs := by
        intro x hx
        rcases List.mem_append.mp hx with ha | hc
        · exact List.mem_append_left _ ha
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hc)
      have left := ih (d+1) acc (fun ls ha hc => allgood ls ha (fun _ hh => widen (hc hh)))
      have right := ih d (m::acc) (fun ls ha hc => allgood ls
        (fun _ hh => ha (List.mem_cons_of_mem _ hh)) (by
          intro x hx
          rcases List.mem_append.mp (hc hx) with h | h
          · rcases List.mem_cons.mp h with rfl | h
            · exact List.mem_append_right _ (List.mem_cons_self ..)
            · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)))
      simp [visitMasks,left,right]

private theorem visit_of_prefix {α C : Type*} (ok : α → α → Bool)
    (hint : List α → List α → C → Option (Bool × C)) (step : List α → C → Option C)
    (v : List α → Bool)
    (atCut : ∀ cs acc i j, hint cs acc i = some (true,j) →
      ∀ ls, acc ⊆ ls → ls ⊆ acc ++ cs → v ls = true)
    (atLeaf : ∀ ls i j, step ls i = some j → v ls = true)
    (d : Nat) (cs acc : List α) (i j : C)
    (run : prefixInspect ok hint step d cs acc i = some j) : visitMasks ok v d cs acc = true := by
  have terminal (acc : List α) (i j : C) (e : inspectHint (hint [] acc i) (step acc) = some j) :=
    inspectHint_elim e (fun k hk => atCut [] acc i k hk acc (fun _ h => h) (fun _ h => List.mem_append_left _ h))
      (fun k _ hk => atLeaf acc k j hk)
  induction cs generalizing d acc i j with
  | nil =>
    cases d <;> rw [visitMasks] <;> apply terminal acc i j <;> simpa only [prefixInspect] using run
  | cons m rest ih =>
    cases d with
    | zero => rw [visitMasks]; apply terminal acc i j; simpa only [prefixInspect] using run
    | succ d =>
      rw [prefixInspect] at run
      apply inspectHint_elim run
      · intro k h
        exact visit_of_extensions ok v (d+1) (m::rest) acc (atCut _ _ _ _ h)
      · intro k _ next
        cases he : prefixInspect ok hint step (d+1) rest acc k with
        | none => simp [he] at next
        | some mid =>
          have left := ih _ _ _ _ he
          rw [visitMasks,left,Bool.true_and]
          by_cases h : acc.all (ok m) = true
          · simp [he,h] at next
            simpa [h] using ih _ _ _ _ next
          · simp [h]

private def countdownGate (acts : Array Nat) (hint : Nat → Nat)
    (rest chosen : List Nat) (i : Nat × Nat × Nat) : Option (Bool × (Nat × Nat × Nat)) :=
  if i.1 = 0 then
    let op := hint i.2.1
    match acts[op % 128 - 1]? with
    | none => none
    | some a =>
      if minimumScore (chosen ++ rest) < minimumScore (chosen.map (orbitMap (a >>> 15)))
      then some (true,op >>> 7,i.2.1+1,i.2.2) else none
  else some (false,i.1-1,i.2.1,i.2.2)

private theorem countdown_excludes {t c : Nat} (acts : Array Nat) (hint : Nat → Nat)
    (valid : ∀ a ∈ acts, minimumActionOK t c (a % 32768) (a >>> 15) = true)
    (rest chosen : List Nat) (i j : Nat × Nat × Nat)
    (h : countdownGate acts hint rest chosen i = some (true,j))
    (ls : List Nat) (chosenIn : chosen ⊆ ls) (lsIn : ls ⊆ chosen ++ rest) : ¬ minimumFamilyOK t c ls := by
  intro minFam
  by_cases z : i.1 = 0
  · cases e : acts[hint i.2.1 % 128 - 1]? with
    | none => simp [countdownGate,z,e] at h
    | some act =>
      by_cases better : minimumScore (chosen ++ rest) < minimumScore (chosen.map (orbitMap (act >>> 15)))
      · exact (Nat.not_lt_of_ge (minFam _ _ (valid _ (Array.mem_of_getElem? e))))
          (prefix_improves chosenIn lsIn better)
      · simp [countdownGate,z,e,better] at h
  · simp [countdownGate,z] at h

private def countdownLeaf (t c : Nat) (positive : List Nat → Nat → Bool) (ls : List Nat)
    (i : Nat × Nat × Nat) : Option (Nat × Nat × Nat) :=
  if laneReject t c ls then some i else if positive ls i.2.2 then some (i.1,i.2.1,i.2.2+1) else none

private def countdownPiece (acts : Nat → Nat → Array Nat) (hint : Nat → Nat → Nat → Nat)
    (positive : Nat → Nat → List Nat → Nat → Bool) (depth : Nat → Nat → Nat)
    (start : Nat → Nat → Nat → Nat × Nat × Nat) (t c index : Nat) : Bool :=
  match selectBranch maskPair (depth t c) t ((List.range (2^t)).filter (eligibleMask t c)) [] index with
  | none => true
  | some (d,rest,chosen) =>
    (prefixInspect maskPair (countdownGate (acts t c) (hint t c)) (countdownLeaf t c (positive t c))
      d rest chosen (start t c index)).isSome

private theorem rank_from_countdown (acts : Nat → Nat → Array Nat)
    (hint : Nat → Nat → Nat → Nat) (positive : Nat → Nat → List Nat → Nat → Bool)
    (depth : Nat → Nat → Nat) (start : Nat → Nat → Nat → Nat × Nat × Nat)
    (valid : ∀ t c a, a ∈ acts t c → minimumActionOK t c (a % 32768) (a >>> 15) = true)
    (runs : ∀ t, 2 ≤ t → t ≤ 5 → ∀ c ∈ coreCodes t,
      rangePass (countdownPiece acts hint positive depth start t c) 0 (2^(depth t c)))
    (sound : ∀ t c ls i, 2 ≤ t → t ≤ 5 → positive t c ls i = true →
      ∀ J : SimpleGraph (Fin (t+ls.length)),
      (∀ a b, splitEdge t c ls a.val b.val = true ↔ J.Adj a b) → AndBound _ t J)
    {n t : Nat} (G : SimpleGraph (Fin n)) (ht : t ≤ 5) (hf : FourCycleFree G)
    (hl : ∀ S, VertexCover G S → t ≤ S.card) : AndBound n t G := by
  classical
  let v (t c : Nat) (ls : List Nat) := decide (t < 2 ∨ ¬ minimumFamilyOK t c ls ∨
    ∃ i j, countdownLeaf t c (positive t c) ls i = some j)
  apply minimum_rank_from_codes v _ _ G ht hf hl
  · intro t ht H hf hm
    let c := labelCore H
    by_cases h2 : 2 ≤ t
    · have all := runs t h2 ht c (core_catalogue ht H hf hm)
      apply visit_of_branches maskPair (v t c) (depth t c) t ((List.range (2^t)).filter (eligibleMask t c)) []
      intro idx hi state hs
      rcases state with ⟨d,rest,chosen⟩
      have good := List.all_eq_true.mp all idx (List.mem_range.mpr hi)
      simp only [Nat.zero_add,countdownPiece] at good
      rw [hs] at good
      obtain ⟨j,hj⟩ := Option.isSome_iff_exists.mp good
      apply visit_of_prefix maskPair (countdownGate (acts t c) (hint t c)) (countdownLeaf t c (positive t c))
        (v t c) _ _ d rest chosen (start t c idx) j hj
      · intro rest acc i j h ls hacc hrest
        exact decide_eq_true (Or.inr (Or.inl (countdown_excludes _ _ (valid t c) _ _ _ _ h _ hacc hrest)))
      · exact fun ls i j h => decide_eq_true (.inr (.inr ⟨i,j,h⟩))
    · exact visit_of_extensions maskPair (v t c) _ _ _ (fun _ _ _ => decide_eq_true (.inl (by omega)))
  · intro t c ls ht hc nd canonical h J model low reach
    rcases of_decide_eq_true h with lt | impossible | ⟨i,j,hj⟩
    · exact small_case lt J low
    · exact False.elim (impossible canonical)
    by_cases lt : t < 2
    · exact small_case lt J low
    apply sound t c ls i.2.2 (by omega) ht _ J model
    have reject := laneReject_of_scalar t c ht ls (fun tag => rejectLeaf_sound ht ls tag J model low reach)
    simp only [countdownLeaf,reject,Bool.false_eq_true,ite_false] at hj
    by_contra h
    simp [h] at hj


end PEqualNP.Outside.L_meta_217

namespace PEqualNP.Outside.L_meta_217.corner

open PEqualNP.AndCount AndCountCircuit

variable {n : Nat}

def left (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

def right (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I)

private theorem side_congr {k : Nat} (I B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) {a b : Fin k → Bool} (h : ∀ j, j < i → a j = b j) :
    sideTrue I B F i a = sideTrue I B F i b := by
  unfold sideTrue
  congr 1
  apply propext
  constructor <;> rintro (raw | ⟨j, hj, lt, val⟩)
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, lt, (h j lt) ▸ val⟩
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, lt, (h j lt).symm ▸ val⟩

private theorem stable (C : AndCountCircuit n) (I : Finset (Fin n)) (m : Nat) :
    ∀ i : Fin C.size, i.val < m → ∀ a b : Nat, i.val < a → i.val < b →
    C.gateValFuel I a i = C.gateValFuel I b i := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi a b ha hb
    cases a with
    | zero => omega
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        simp only [gateValFuel]
        have eq (j : Fin C.size) (lt : j < i) :
            C.gateValFuel I a j = C.gateValFuel I b j :=
          ih j (by change j.val < i.val at lt; omega) a b
            (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
        rw [side_congr I _ _ i eq, side_congr I _ _ i eq]

theorem gate_eq (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal I i = (left C I i && right C I i) := by
  have h := stable C I C.size i i.isLt C.size (C.size + 1) i.isLt (by omega)
  exact h

def vars (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :=
  if q i then C.rightVars i else C.leftVars i

def parents (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :=
  if q i then C.rightGates i else C.leftGates i

def support (C : AndCountCircuit n) (q : Fin C.size → Bool) :
    Nat → Fin C.size → Finset (Fin n)
  | 0, _ => ∅
  | d+1, i => vars C q i ∪ ((parents C q i).filter (· < i)).biUnion (support C q d)

def hits (I S : Finset (Fin n)) := ∃ v ∈ S, v ∈ I

theorem hit_step (C : AndCountCircuit n) (q : Fin C.size → Bool) (d : Nat)
    (i : Fin C.size) (I : Finset (Fin n)) :
    hits I (support C q (d+1) i) ↔ hits I (vars C q i) ∨
      ∃ j ∈ parents C q i, j < i ∧ hits I (support C q d j) := by
  simp only [hits, support, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨v, hv | ⟨j, ⟨hj, lt⟩, hv⟩, hI⟩
    · exact Or.inl ⟨v, hv, hI⟩
    · exact Or.inr ⟨j, hj, lt, v, hv, hI⟩
  · rintro (⟨v, hv, hI⟩ | ⟨j, hj, lt, v, hv, hI⟩)
    · exact ⟨v, Or.inl hv, hI⟩
    · exact ⟨v, Or.inr ⟨j, ⟨hj, lt⟩, hv⟩, hI⟩

def clause (C : AndCountCircuit n) (q : Fin C.size → Bool) :=
  C.outVars ∪ C.outGates.biUnion (support C q C.size)

theorem clause_hit (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n)) :
    hits I (clause C q) ↔ hits I C.outVars ∨ ∃ j ∈ C.outGates, hits I (support C q C.size j) := by
  simp only [hits, clause, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv | ⟨j, hj, hv⟩, hi⟩
    · exact Or.inl ⟨v, hv, hi⟩
    · exact Or.inr ⟨j, hj, v, hv, hi⟩
  · rintro (⟨v, hv, hi⟩ | ⟨j, hj, v, hv, hi⟩)
    · exact ⟨v, Or.inl hv, hi⟩
    · exact ⟨v, Or.inr ⟨j, hj, hv⟩, hi⟩

theorem dominates (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n))
    (d : Nat) (i : Fin C.size) (hd : i.val < d) :
    C.gateVal I i = true → hits I (support C q d i) := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    intro h
    rw [gate_eq, Bool.and_eq_true] at h
    apply (hit_step C q d i I).2
    have hs : sideTrue I (vars C q i) (parents C q i) i (C.gateVal I) = true := by
      cases e : q i <;> simp [vars, parents, e]
      · exact h.1
      · exact h.2
    rw [sideTrue, decide_eq_true_eq] at hs
    rcases hs with raw | ⟨j, hj, lt, val⟩
    · exact Or.inl raw
    · exact Or.inr ⟨j, hj, lt, ih j (by change j.val < i.val at lt; omega) val⟩

theorem chosen (C : AndCountCircuit n) (I : Finset (Fin n)) (d : Nat)
    (i : Fin C.size) (hd : i.val < d) :
    hits I (support C (left C I) d i) → C.gateVal I i = true := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    intro h
    have hs : sideTrue I (vars C (left C I) i) (parents C (left C I) i) i (C.gateVal I) = true := by
      rw [sideTrue, decide_eq_true_eq]
      rcases (hit_step _ _ _ _ _).1 h with raw | ⟨j, hj, lt, val⟩
      · exact Or.inl raw
      · exact Or.inr ⟨j, hj, lt, ih j (by change j.val < i.val at lt; omega) val⟩
    rw [gate_eq, Bool.and_eq_true]
    cases hl : left C I i with
    | false =>
      simp [vars, parents, hl] at hs
      change left C I i = true at hs
      simp [hl] at hs
    | true =>
      exact ⟨rfl, by simpa [vars, parents, hl, right] using hs⟩

theorem gives_hit (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n))
    (h : C.eval I = true) : hits I (clause C q) := by
  rw [eval, decide_eq_true_eq] at h
  apply (clause_hit _ _ _).2
  rcases h with raw | ⟨j, hj, val⟩
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, dominates C q I C.size j j.isLt val⟩

theorem avoids (C : AndCountCircuit n) (I : Finset (Fin n)) (h : C.eval I = false) :
    ¬ hits I (clause C (left C I)) := by
  intro hit
  have ht : C.eval I = true := by
    rw [eval, decide_eq_true_eq]
    rcases (clause_hit _ _ _).1 hit with raw | ⟨j, hj, val⟩
    · exact Or.inl raw
    · exact Or.inr ⟨j, hj, chosen C I C.size j j.isLt val⟩
  simp [h] at ht

theorem complement_clause (C : AndCountCircuit n) (I : Finset (Fin n))
    (h : C.eval I = false) (positive : ∀ u, u ∉ I → C.eval (insert u I) = true) :
    ∀ u, u ∈ I ↔ u ∉ clause C (left C I) := by
  intro u
  constructor
  · intro hu hc
    exact avoids C I h ⟨u, hc, hu⟩
  · intro absent
    by_contra missing
    obtain ⟨v, hv, hin⟩ := gives_hit C (left C I) _ (positive u missing)
    rcases Finset.mem_insert.mp hin with rfl | inside
    · exact absent hv
    · exact avoids C I h ⟨v, hv, inside⟩

def indep (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) :=
  ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b

def maximalIndep (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) :=
  indep G I ∧ ∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v

def packBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k+1, f => Nat.bit (f 0) (packBits k (fun j => f (j+1)))

theorem pack_test (k j : Nat) (f : Nat → Bool) :
    (packBits k f).testBit j = (decide (j < k) && f j) := by
  induction k generalizing j f with
  | zero => simp [packBits]
  | succ k ih =>
    cases j with
    | zero => simp [packBits]
    | succ j => simp [packBits, Nat.testBit_bit_succ, ih]

theorem pack_lt (k : Nat) (f : Nat → Bool) : packBits k f < 2^k := by
  induction k generalizing f with
  | zero => simp [packBits]
  | succ k ih =>
    have h := ih (fun j => f (j+1))
    cases hb : f 0 <;> simp [packBits, hb, Nat.bit, pow_succ] <;> omega

def maskOf (S : Finset (Fin 8)) :=
  packBits 8 fun j => if h : j < 8 then decide ((⟨j,h⟩ : Fin 8) ∈ S) else false

theorem mask_bit (S : Finset (Fin 8)) (i : Fin 8) :
    (maskOf S).testBit i.val = decide (i ∈ S) := by simp [maskOf, pack_test, i.isLt]

theorem mask_inter (S T : Finset (Fin 8)) :
    maskOf (S ∩ T) = maskOf S &&& maskOf T := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8 <;> simp [maskOf, pack_test, Nat.testBit_and, hi]

theorem mask_zero (S : Finset (Fin 8)) : maskOf S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have e := mask_bit S v
    simp [h, hv] at e
  · rintro rfl
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8 <;> simp [maskOf, pack_test, hi]

def sideChoice (C : AndCountCircuit n) (c : Fin 16) (i : Fin C.size) := c.val.testBit i.val

theorem all_choices (C : AndCountCircuit n) (bound : C.size ≤ 4) :
    Function.Surjective (sideChoice C) := by
  intro q
  let f (i : Nat) := if h : i < C.size then q ⟨i,h⟩ else false
  refine ⟨⟨packBits 4 f, pack_lt 4 f⟩, ?_⟩
  funext i
  have hi : i.val < 4 := lt_of_lt_of_le i.isLt bound
  simp [sideChoice, pack_test, hi, f, i.isLt]

def wiring (C : AndCountCircuit n) (i : Nat) (b : Bool) (j : Nat) : Bool :=
  if hi : i < C.size then
    if hj : j < C.size then decide ((⟨j,hj⟩ : Fin C.size) ∈
      if b then C.rightGates ⟨i,hi⟩ else C.leftGates ⟨i,hi⟩) else false
  else false

def outputFlag (C : AndCountCircuit n) (i : Nat) : Bool :=
  if h : i < C.size then decide ((⟨i,h⟩ : Fin C.size) ∈ C.outGates) else false

def topology (C : AndCountCircuit n) := packBits 16 fun k => match k with
  | 0 => outputFlag C 0
  | 1 => outputFlag C 1
  | 2 => outputFlag C 2
  | 3 => outputFlag C 3
  | 4 => wiring C 3 false 0
  | 5 => wiring C 3 false 1
  | 6 => wiring C 3 false 2
  | 7 => wiring C 3 true 0
  | 8 => wiring C 3 true 1
  | 9 => wiring C 3 true 2
  | 10 => wiring C 2 false 0
  | 11 => wiring C 2 false 1
  | 12 => wiring C 2 true 0
  | 13 => wiring C 2 true 1
  | 14 => wiring C 1 false 0
  | 15 => wiring C 1 true 0
  | _ => false

def wireSlot (i : Nat) (b : Bool) (j : Nat) :=
  16 - i * (i+1) + b.toNat * i + j

theorem topology_wire (C : AndCountCircuit n) (i j : Nat) (b : Bool)
    (hi : i < 4) (hj : j < i) :
    (topology C).testBit (wireSlot i b j) = wiring C i b j := by
  unfold topology
  rw [pack_test]
  interval_cases i <;> interval_cases j <;> cases b <;> rfl

theorem topology_out (C : AndCountCircuit n) (i : Nat) (hi : i < 4) :
    (topology C).testBit i = outputFlag C i := by
  unfold topology
  rw [pack_test]
  interval_cases i <;> rfl

def rawFlag (C : AndCountCircuit n) (v : Fin n) (i : Nat) (b : Bool) : Bool :=
  if hi : i < C.size then
    decide (v ∈ if b then C.rightVars ⟨i,hi⟩ else C.leftVars ⟨i,hi⟩)
  else false

def patternOf (C : AndCountCircuit n) (v : Fin n) := packBits 8 fun k =>
  rawFlag C v (k/2) (k.testBit 0)

theorem pattern_raw (C : AndCountCircuit n) (v : Fin n) (i : Nat) (b : Bool) (hi : i < 4) :
    (patternOf C v).testBit (2*i + b.toNat) = rawFlag C v i b := by
  unfold patternOf
  rw [pack_test]
  interval_cases i <;> cases b <;> rfl

def numGate (t p c : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | d+1, i =>
    let b := c.testBit i
    p.testBit (2*i + b.toNat) || (List.range i).any fun j =>
      t.testBit (wireSlot i b j) && numGate t p c d j

theorem num_support (C : AndCountCircuit n) (bound : C.size ≤ 4) (v : Fin n) (c : Fin 16)
    (d : Nat) (i : Fin C.size) :
    numGate (topology C) (patternOf C v) c.val d i.val = true ↔
      v ∈ support C (sideChoice C c) d i := by
  induction d generalizing i with
  | zero => simp [numGate, support]
  | succ d ih =>
    have h3 := lt_of_lt_of_le i.isLt bound
    simp only [numGate, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
      support, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, pattern_raw C v _ _ h3]
    apply or_congr
    · cases e : c.val.testBit i.val <;> simp [rawFlag, vars, sideChoice, i.isLt, e]
    · constructor
      · rintro ⟨j, lt, wire, pass⟩
        let k : Fin C.size := ⟨j, lt_trans lt i.isLt⟩
        rw [topology_wire _ _ _ _ h3 lt] at wire
        have mem : k ∈ parents C (sideChoice C c) i := by
          cases e : c.val.testBit i.val <;> simpa [wiring, parents, sideChoice, i.isLt, k, lt_trans lt i.isLt, e] using wire
        exact ⟨k, ⟨mem, lt⟩, (ih k).mp pass⟩
      · rintro ⟨k, ⟨mem, lt⟩, pass⟩
        refine ⟨k.val, lt, ?_, (ih k).mpr pass⟩
        rw [topology_wire _ _ _ _ h3 lt]
        cases e : c.val.testBit i.val <;> simpa [wiring, parents, sideChoice, i.isLt, k.isLt, e] using mem

theorem support_stable (C : AndCountCircuit n) (q : Fin C.size → Bool)
    (a : Nat) (i : Fin C.size) (ha : i.val < a) (b : Nat) (hb : i.val < b) :
    support C q a i = support C q b i := by
  induction a generalizing i b with
  | zero => omega
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      simp only [support]
      congr 1
      apply Finset.biUnion_congr rfl
      intro j hj
      have lt : j.val < i.val := (Finset.mem_filter.mp hj).2
      exact ih j (by omega) b (by omega)

theorem no_outVar (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : C.Computes G)
    (v : Fin n) : v ∉ C.outVars := by
  intro hv
  have ht : C.eval {v} = true := decide_eq_true (Or.inl ⟨v,hv,by simp⟩)
  obtain ⟨a,ha,b,hb,hab⟩ := (h _).mp ht
  simp only [Finset.mem_singleton] at ha hb
  subst a; subst b; exact G.loopless.irrefl _ hab

def numOut (t p c : Nat) :=
  (List.range 4).any fun i => t.testBit i && numGate t p c 4 i

theorem num_clause (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : C.Computes G)
    (bound : C.size ≤ 4) (v : Fin n) (c : Fin 16) :
    numOut (topology C) (patternOf C v) c.val = true ↔ v ∈ clause C (sideChoice C c) := by
  simp only [numOut, List.any_eq_true, List.mem_range, Bool.and_eq_true, clause, Finset.mem_union,
    no_outVar C G h v, false_or, Finset.mem_biUnion]
  constructor
  · rintro ⟨i, hi, flag, ok⟩
    rw [topology_out C i hi] at flag
    by_cases inside : i < C.size
    · let j : Fin C.size := ⟨i, inside⟩
      refine ⟨j, by simpa [outputFlag, inside, j] using flag, ?_⟩
      rw [support_stable C _ C.size j j.isLt 4 hi]
      exact (num_support C bound v c 4 j).mp ok
    · simp [outputFlag, inside] at flag
  · rintro ⟨j, hout, hv⟩
    have hi := lt_of_lt_of_le j.isLt bound
    refine ⟨j.val, hi, ?_, (num_support C bound v c 4 j).mpr ?_⟩
    · simpa [topology_out C _ hi, outputFlag, j.isLt] using hout
    · rwa [support_stable C _ 4 j hi C.size j.isLt]


def rawLeaf (i : Fin 4) (b : Bool) : Fin 8 :=
  ⟨2*i.val+b.toNat, by cases b <;> have := i.isLt <;> simp <;> omega⟩

def rawGate (t c : Nat) : Nat → Fin 4 → Finset (Fin 8)
  | 0, _ => ∅
  | d+1, i =>
    let b := c.testBit i.val
    insert (rawLeaf i b) ((Finset.univ.filter fun j : Fin 4 =>
      j < i ∧ t.testBit (wireSlot i.val b j.val) = true).biUnion (rawGate t c d))

def rawCorner (t : Nat) (c : Fin 16) : Finset (Fin 8) :=
  (Finset.univ.filter fun i : Fin 4 => t.testBit i.val = true).biUnion (rawGate t c.val 4)

def allRaw (t : Nat) : Finset (Finset (Fin 8)) := Finset.univ.image (rawCorner t)

def minimalRaw (t : Nat) : Finset (Finset (Fin 8)) :=
  (allRaw t).filter fun s => ∀ r ∈ allRaw t, ¬ r ⊂ s

def minimalFamily (t : Nat) : Finset Nat := (minimalRaw t).image maskOf

def activeSide (p : Nat) : Finset (Fin 8) :=
  Finset.univ.filter fun z => p.testBit z.val = true

theorem num_gate_raw (t p c : Nat) (d : Nat) (i : Fin 4) :
    numGate t p c d i.val = true ↔
      ∃ z ∈ rawGate t c d i, p.testBit z.val = true := by
  induction d generalizing i with
  | zero => simp [numGate,rawGate]
  | succ d ih =>
    simp only [numGate, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
      rawGate,Finset.mem_insert,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro (hit | ⟨j, hj, link, yes⟩)
      · exact ⟨_,Or.inl rfl,hit⟩
      · let z : Fin 4 := ⟨j,lt_trans hj i.isLt⟩
        obtain ⟨a,ha,bit⟩ := (ih z).mp yes
        exact ⟨a, Or.inr ⟨z, ⟨hj,link⟩,ha⟩,bit⟩
    · rintro ⟨a, ha | ⟨j,⟨lt,edge⟩,ha⟩,hit⟩
      · subst a; exact Or.inl hit
      · exact Or.inr ⟨j.val,lt,edge,(ih j).mpr ⟨a,ha,hit⟩⟩

theorem num_out_raw (t p : Nat) (c : Fin 16) :
    numOut t p c.val = true ↔ ¬Disjoint (rawCorner t c) (activeSide p) := by
  simp only [numOut,List.any_eq_true,List.mem_range,Bool.and_eq_true,Finset.not_disjoint_iff,
    rawCorner,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_univ,true_and,activeSide]
  constructor
  · rintro ⟨j,hj,hout,hg⟩
    let i : Fin 4 := ⟨j,hj⟩
    obtain ⟨z,hz,hb⟩ := (num_gate_raw t p c.val 4 i).mp hg
    exact ⟨z,⟨i,hout,hz⟩,hb⟩
  · rintro ⟨z,⟨i,hout,hz⟩,hb⟩
    exact ⟨i,i.isLt,hout,(num_gate_raw t p c.val 4 i).mpr ⟨z,hz,hb⟩⟩

theorem raw_clause (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (hc : C.Computes G)
    (hk : C.size ≤ 4) (v : Fin n) (q : Fin 16) :
    Disjoint (rawCorner (topology C) q) (activeSide (patternOf C v)) ↔
    v ∉ clause C (sideChoice C q) := by
  rw [← num_clause C G hc hk, num_out_raw]
  simp

theorem minimal_subset_of_corner (t : Nat) (q : Fin 16) :
    ∃ s ∈ minimalRaw t, s ⊆ rawCorner t q := by
  classical
  let candidates := (allRaw t).filter (· ⊆ rawCorner t q)
  have hq : rawCorner t q ∈ candidates := Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩, Finset.Subset.rfl⟩
  obtain ⟨s,hs,hle⟩ := Finset.exists_min_image candidates Finset.card ⟨_,hq⟩
  obtain ⟨h1,h2⟩ := Finset.mem_filter.mp hs
  refine ⟨s,Finset.mem_filter.mpr ⟨h1,?_⟩,h2⟩
  intro r hr hlt
  have hm := hle r (Finset.mem_filter.mpr ⟨hr,hlt.subset.trans h2⟩)
  exact (Nat.not_le_of_lt (Finset.card_lt_card hlt)) hm

theorem minimal_separates (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (hc : C.Computes G)
    (hk : C.size ≤ 4) {u v : Fin n} (he : G.Adj u v) (s : Finset (Fin 8))
    (hs : s ∈ minimalRaw (topology C)) :
    ¬(Disjoint s (activeSide (patternOf C u)) ∧ Disjoint s (activeSide (patternOf C v))) := by
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  intro ⟨hu,hv⟩
  have hpos : C.eval {u,v} = true := (hc _).mpr ⟨u,by simp,v,by simp,he⟩
  obtain ⟨x,hx,hmem⟩ := gives_hit C (sideChoice C q) _ hpos
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · exact ((raw_clause C G hc hk _ q).mp hu) hx
  · exact ((raw_clause C G hc hk _ q).mp hv) hx

theorem minimal_MIS (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (hc : C.Computes G)
    (hk : C.size ≤ 4) (I : Finset (Fin n)) (hI : maximalIndep G I) :
    ∃ s ∈ minimalRaw (topology C), ∀ v : Fin n,
      v ∈ I ↔ Disjoint s (activeSide (patternOf C v)) := by
  classical
  have hno : C.eval I = false := Bool.eq_false_iff.mpr fun h => by
    obtain ⟨a,ha,b,hb,he⟩ := (hc I).mp h
    exact hI.1 a ha b hb he
  have hpos (u) (hu : u ∉ I) : C.eval (insert u I) = true := by
    obtain ⟨v,hv,he⟩ := hI.2 u hu
    exact (hc _).mpr ⟨u,by simp,v,Finset.mem_insert_of_mem hv,he⟩
  obtain ⟨q,hq⟩ := all_choices C hk (left C I)
  obtain ⟨s,hs,hsub⟩ := minimal_subset_of_corner (topology C) q
  have leftward (v) (hv : v ∈ I) : Disjoint s (activeSide (patternOf C v)) := by
    apply Disjoint.mono_left hsub
    apply (raw_clause C G hc hk v q).mpr
    rw [hq]
    exact (complement_clause C I hno hpos v).mp hv
  refine ⟨s,hs,fun v => ⟨leftward v,?_⟩⟩
  intro h
  by_contra hv
  obtain ⟨w,hw,he⟩ := hI.2 v hv
  exact minimal_separates C G hc hk he s hs ⟨h,leftward w hw⟩

def gateLink (t q : Nat) (parent child : Fin 4) : Prop :=
  child < parent ∧ t.testBit (wireSlot parent.val (q.testBit parent.val) child.val) = true

def reachable (t : Nat) (q : Fin 16) (i : Fin 4) : Prop :=
  ∃ root : Fin 4, t.testBit root.val = true ∧ Relation.ReflTransGen (gateLink t q.val) root i

theorem raw_path {t q d : Nat} (i : Fin 4) (hi : i.val < d) (x : Fin 8) :
    x ∈ rawGate t q d i ↔ ∃ j : Fin 4,
      Relation.ReflTransGen (gateLink t q) i j ∧ x = rawLeaf j (q.testBit j.val) := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    simp only [rawGate, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | ⟨j,⟨hji,hbit⟩,hx⟩)
      · exact ⟨i,.refl,rfl⟩
      · obtain ⟨k,hk,eq⟩ := (ih j (by change j.val < i.val at hji; omega)).mp hx
        exact ⟨k, hk.head (show gateLink t q i j from ⟨hji,hbit⟩),eq⟩
    · rintro ⟨j,hp,eq⟩
      rcases hp.cases_head with e | ⟨z,hz,hp⟩
      · subst j; exact Or.inl eq
      · have hzi : z.val < i.val := hz.1
        exact Or.inr ⟨z,hz,(ih z (by omega)).mpr ⟨j,hp,eq⟩⟩

theorem rawCorner_path {t : Nat} (q : Fin 16) (x : Fin 8) :
    x ∈ rawCorner t q ↔ ∃ i : Fin 4, reachable t q i ∧ x = rawLeaf i (q.val.testBit i.val) := by
  simp only [rawCorner, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,true_and]
  constructor
  · rintro ⟨root,out,hx⟩
    obtain ⟨i,hi,eq⟩ := (raw_path root root.isLt x).mp hx
    exact ⟨i,⟨root,out,hi⟩,eq⟩
  · rintro ⟨i,⟨root,out,hi⟩,eq⟩
    exact ⟨root,out,(raw_path root root.isLt x).mpr ⟨i,hi,eq⟩⟩

theorem rawLeaf_inj {i j : Fin 4} {b c : Bool} (h : rawLeaf i b = rawLeaf j c) : i = j ∧ b = c := by
  have eq := congrArg Fin.val h
  change 2*i.val+b.toNat=2*j.val+c.toNat at eq
  cases b <;> cases c <;> simp only [Bool.toNat_false,Bool.toNat_true] at eq <;>
    first | exact ⟨Fin.ext (by omega),rfl⟩ | omega

theorem rawCorner_bit {t : Nat} (q : Fin 16) (i : Fin 4) (b : Bool) :
    rawLeaf i b ∈ rawCorner t q ↔ reachable t q i ∧ b = q.val.testBit i.val := by
  rw [rawCorner_path]
  constructor
  · rintro ⟨j,hj,h⟩
    obtain ⟨rfl,he⟩ := rawLeaf_inj h
    exact ⟨hj,he⟩
  · rintro ⟨hi,rfl⟩
    exact ⟨i,hi,rfl⟩

theorem reachable_step {t : Nat} (q : Fin 16) (i : Fin 4) :
    reachable t q i ↔ t.testBit i.val = true ∨
      ∃ j : Fin 4, reachable t q j ∧ i < j ∧ t.testBit (wireSlot j.val (q.val.testBit j.val) i.val) = true := by
  constructor
  · rintro ⟨root,out,hp⟩
    rcases hp.cases_tail with rfl | ⟨j,hj,edge⟩
    · exact Or.inl out
    · exact Or.inr ⟨j,⟨root,out,hj⟩,edge⟩
  · rintro (out | ⟨j,⟨root,out,hp⟩,edge⟩)
    · exact ⟨i,out,.refl⟩
    · exact ⟨root,out,hp.tail edge⟩

theorem rawCorner_antichain {t : Nat} {p q : Fin 16} (hs : rawCorner t p ⊆ rawCorner t q) :
    rawCorner t p = rawCorner t q := by
  have agrees (i : Fin 4) (hi : reachable t p i) : p.val.testBit i.val = q.val.testBit i.val :=
    ((rawCorner_bit q i _).mp (hs ((rawCorner_bit p i _).mpr ⟨hi,rfl⟩))).2
  have back {i : Fin 4} (hi : reachable t q i) : reachable t p i := by
    obtain ⟨root,out,path⟩ := hi
    induction path with
    | refl => exact ⟨root,out,.refl⟩
    | @tail j i _ edge ih =>
      obtain ⟨hij,hbit⟩ := edge
      rw [← agrees j ih] at hbit
      exact (reachable_step p i).mpr (Or.inr ⟨j,ih,hij,hbit⟩)
  apply Finset.Subset.antisymm hs
  intro x hx
  obtain ⟨i,hi,rfl⟩ := (rawCorner_path q x).mp hx
  have hp := back hi
  exact (rawCorner_bit p i _).mpr ⟨hp,(agrees i hp).symm⟩

theorem minimal_eq_all (t : Nat) : minimalRaw t = allRaw t := by
  apply Finset.Subset.antisymm (Finset.filter_subset _ _)
  intro s hs
  refine Finset.mem_filter.mpr ⟨hs,?_⟩
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hs
  intro r hr lt
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hr
  exact lt.ne (rawCorner_antichain lt.subset)

end PEqualNP.Outside.L_meta_217.corner

namespace PEqualNP.Outside.L_meta_217

private def chooseUnions : List ℕ → List ℕ
  | [] => [0]
  | a :: l => let tail := chooseUnions l; tail ++ tail.map (a ||| ·)

private theorem union_sublist {p l : List ℕ} (h : p.Sublist l) :
    p.foldr (· ||| ·) 0 ∈ chooseUnions l := by
  induction h with
  | slnil => simp [chooseUnions]
  | cons a hs ih => exact List.mem_append_left _ ih
  | cons_cons a hs ih => exact List.mem_append_right _ (List.mem_map.mpr ⟨_,ih,rfl⟩)

def choiceField (i : ℕ) := [43690,52428,61680,65280].getD i 0

def sideFields : ℕ → List ℕ → List ℕ
  | _, [] => []
  | i, r :: tail => (r &&& (65535 ^^^ choiceField i)) :: (r &&& choiceField i) ::
    sideFields (i+1) tail

def newRows (i : ℕ) (sig : List ℕ) :=
  ((65535 :: chooseUnions (sideFields (i+1) sig)).eraseDups).map (· :: sig)

theorem row_of_sublist (i : ℕ) (sig picks : List ℕ) (h : picks.Sublist (sideFields (i+1) sig)) :
    (picks.foldr (· ||| ·) 0 :: sig) ∈ newRows i sig := by
  apply List.mem_map.mpr
  exact ⟨_,List.mem_eraseDups.mpr (List.mem_cons_of_mem _ (union_sublist h)),rfl⟩

theorem row_of_output (i : ℕ) (sig : List ℕ) : 65535 :: sig ∈ newRows i sig := by
  apply List.mem_map.mpr
  exact ⟨_,List.mem_eraseDups.mpr (List.mem_cons_self),rfl⟩

def shape01 := [([] : List ℕ)].flatMap (newRows 3)
def shape02 := shape01.flatMap (newRows 2)
def shape03 := shape02.flatMap (newRows 1)
def shape04 := shape03.flatMap (newRows 0)

def rawAtShapeAux (q : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | i,r :: tail =>
    (if r.testBit q then 1 <<< (2*i + (q.testBit i).toNat) else 0) |||
      rawAtShapeAux q (i+1) tail

def shapeRaw (sig : List ℕ) (q : ℕ) := rawAtShapeAux q 0 sig


end PEqualNP.Outside.L_meta_217

namespace PEqualNP.Outside.L_meta_217.corner

noncomputable def reachMask (t : Nat) (i : Fin 4) : Nat := by
  classical
  exact packBits 16 fun q => if h : q < 16 then decide (reachable t ⟨q,h⟩ i) else false

theorem reachMask_bit (t : Nat) (i : Fin 4) (q : Fin 16) :
    (reachMask t i).testBit q.val = true ↔ reachable t q i := by
  classical
  simp [reachMask, pack_test, q.isLt]

theorem reachMask_out (t : Nat) (i : Fin 4) (q : Nat) (hq : 16 ≤ q) :
    (reachMask t i).testBit q = false := by
  classical
  simp [reachMask, pack_test, Nat.not_lt.mpr hq]

theorem field_bit : ∀ (i : Fin 4) (q : Fin 16), (choiceField i.val).testBit q.val = q.val.testBit i.val := by
  decide +kernel

theorem full_bit (q : Nat) : (65535 : Nat).testBit q = decide (q < 16) :=
  Nat.testBit_two_pow_sub_one 16 q

def consecutives : Nat → List (Fin 4) → Prop
  | _, [] => True
  | k, j :: js => j.val = k ∧ consecutives (k+1) js

noncomputable def picked (t i : Nat) : List (Fin 4) → List Nat
  | [] => []
  | j :: js =>
    (if t.testBit (wireSlot j.val false i) then [reachMask t j &&& (65535 ^^^ choiceField j.val)] else []) ++
    (if t.testBit (wireSlot j.val true i) then [reachMask t j &&& choiceField j.val] else []) ++
    picked t i js

theorem picked_sub (t i k : Nat) (js : List (Fin 4)) (h : consecutives k js) :
    (picked t i js).Sublist (sideFields k (js.map (reachMask t))) := by
  induction js generalizing k with
  | nil => simp [picked,sideFields]
  | cons j js ih =>
    obtain ⟨e,hs⟩ := h
    subst k
    have hrec := ih _ hs
    cases a : t.testBit (wireSlot j.val false i) <;> cases b : t.testBit (wireSlot j.val true i) <;>
      simp only [picked,a,b,Bool.false_eq_true,reduceIte,List.nil_append,
        List.map_cons,sideFields,List.cons_append] <;>
      first | exact (hrec.cons _).cons _
            | exact (hrec.cons_cons _).cons _
            | exact (hrec.cons _).cons_cons _
            | exact (hrec.cons_cons _).cons_cons _

theorem fold_or_bit (L : List Nat) (q : Nat) :
    (L.foldr (· ||| ·) 0).testBit q = true ↔ ∃ r ∈ L, r.testBit q = true := by
  induction L with
  | nil => simp
  | cons a l ih => simp [Nat.testBit_or,ih]

theorem picked_mem_bit (t i : Nat) (js : List (Fin 4)) (q : Fin 16) :
    (∃ r ∈ picked t i js, r.testBit q.val = true) ↔
      ∃ j ∈ js, reachable t q j ∧ t.testBit (wireSlot j.val (q.val.testBit j.val) i) = true := by
  induction js with
  | nil => simp [picked]
  | cons j js ih =>
    have hr := reachMask_bit t j q
    have hc := field_bit j q
    have hf := full_bit q.val
    simp only [q.isLt,decide_true] at hf
    cases a : t.testBit (wireSlot j.val false i) <;> cases b : t.testBit (wireSlot j.val true i) <;>
      cases c : q.val.testBit j.val <;>
      simp [picked,a,b,c,Nat.testBit_and,Nat.testBit_xor,hf,hc,ih,hr]

theorem picked_out (t i q : Nat) (js : List (Fin 4)) (hq : 16 ≤ q) :
    ∀ r ∈ picked t i js, r.testBit q = false := by
  induction js with
  | nil => simp [picked]
  | cons j js ih =>
    cases a : t.testBit (wireSlot j.val false i) <;> cases b : t.testBit (wireSlot j.val true i) <;>
      simpa [picked,a,b, Nat.testBit_and, reachMask_out t j q hq] using ih

theorem reach_row (t : Nat) (i : Fin 4) (js : List (Fin 4)) (hc : consecutives (i.val+1) js)
    (hjs : ∀ j, j ∈ js ↔ i < j) :
    reachMask t i :: js.map (reachMask t) ∈ newRows i.val (js.map (reachMask t)) := by
  classical
  cases hout : t.testBit i.val with
  | true =>
    have eq : reachMask t i = 65535 := by
      apply Nat.eq_of_testBit_eq
      intro q
      by_cases hq : q < 16
      · let a : Fin 16 := ⟨q,hq⟩
        exact ((reachMask_bit t i a).mpr ((reachable_step a i).mpr (Or.inl hout))).trans
          (by simp [full_bit,hq])
      · simp [reachMask_out t i q (by omega),full_bit,hq]
    rw [eq]
    exact row_of_output _ _
  | false =>
    have eq : reachMask t i = (picked t i.val js).foldr (· ||| ·) 0 := by
      apply Nat.eq_of_testBit_eq
      intro q
      apply Bool.eq_iff_iff.mpr
      rw [fold_or_bit]
      by_cases hq : q < 16
      · let a : Fin 16 := ⟨q,hq⟩
        rw [show q = a.val from rfl, reachMask_bit, reachable_step, picked_mem_bit, hout]
        simp only [Bool.false_eq_true,false_or]
        constructor
        · rintro ⟨j,hj,hij,hb⟩
          exact ⟨j,(hjs j).mpr hij,hj,hb⟩
        · rintro ⟨j,mem,hj,hb⟩
          exact ⟨j,hj,(hjs j).mp mem,hb⟩
      · simp only [reachMask_out t i q (by omega),Bool.false_eq_true,false_iff,not_exists]
        rintro r ⟨hr,ht⟩
        rw [picked_out t i.val q js (by omega) r hr] at ht
        contradiction
    rw [eq]
    exact row_of_sublist _ _ _ (picked_sub t i.val _ js hc)

noncomputable def reachSignature (t : Nat) := ([0,1,2,3] : List (Fin 4)).map (reachMask t)

theorem signature_listed (t : Nat) : reachSignature t ∈ shape04 := by
  have r3 := reach_row t 3 [] (by norm_num [consecutives]) (by decide)
  have r2 := reach_row t 2 [3] (by norm_num [consecutives]) (by decide)
  have r1 := reach_row t 1 [2,3] (by norm_num [consecutives]) (by decide)
  have r0 := reach_row t 0 [1,2,3] (by norm_num [consecutives]) (by decide)
  exact List.mem_flatMap.mpr ⟨_,List.mem_flatMap.mpr ⟨_,List.mem_flatMap.mpr ⟨_,
    List.mem_flatMap.mpr ⟨[],by simp,r3⟩,r2⟩,r1⟩,r0⟩

theorem aux_shape_bit (t : Nat) (q : Fin 16) (k j : Nat) (js : List (Fin 4)) (h : consecutives k js) :
    (rawAtShapeAux q.val k (js.map (reachMask t))).testBit j = true ↔
      ∃ i ∈ js, reachable t q i ∧ (rawLeaf i (q.val.testBit i.val)).val = j := by
  induction js generalizing k with
  | nil => simp [rawAtShapeAux]
  | cons i js ih =>
    obtain ⟨eq,rest⟩ := h
    subst k
    cases e : (reachMask t i).testBit q.val
    · have hn : ¬reachable t q i := fun h => Bool.noConfusion (e.symm.trans ((reachMask_bit _ _ _).mpr h))
      simp [rawAtShapeAux,e,ih _ rest,hn]
    · have yes := (reachMask_bit t i q).mp e
      simp [rawAtShapeAux,e,Nat.testBit_or, Nat.shiftLeft_eq,Nat.testBit_two_pow,ih _ rest,yes,rawLeaf]

theorem signature_raw (t : Nat) (q : Fin 16) : shapeRaw (reachSignature t) q.val = maskOf (rawCorner t q) := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply Bool.eq_iff_iff.mpr
  rw [show shapeRaw (reachSignature t) q.val = rawAtShapeAux q.val 0 (([0,1,2,3] : List (Fin 4)).map (reachMask t)) from rfl]
  rw [aux_shape_bit _ _ _ _ _ (by norm_num [consecutives])]
  by_cases hj : j < 8
  · let z : Fin 8 := ⟨j,hj⟩
    rw [show j = z.val from rfl,mask_bit,decide_eq_true_eq,rawCorner_path]
    have hall : ∀ i : Fin 4, i ∈ ([0,1,2,3] : List (Fin 4)) := by decide
    constructor
    · rintro ⟨i,_,hi,he⟩
      exact ⟨i,hi,Fin.ext he.symm⟩
    · rintro ⟨i,hi,he⟩
      exact ⟨i,hall i,hi,congrArg Fin.val he.symm⟩
  · simp only [maskOf,pack_test,hj,decide_false,Bool.false_and,Bool.false_eq_true,iff_false,not_exists]
    rintro i ⟨_,_,he⟩
    have := (rawLeaf i (q.val.testBit i.val)).isLt
    omega

end PEqualNP.Outside.L_meta_217.corner

namespace PEqualNP.Outside.L_meta_217
private def permRawAux (p x : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => permRawAux p x i |||
    (if x.testBit i then 1 <<< ((p >>> (3*i)) % 8) else 0)

def permRaw (p x : ℕ) := permRawAux p x 8

def shapeClasses : Array (List ℕ) := #[[0],
[1, 2],
[5, 6, 9, 10],
[21, 22, 25, 26, 37, 38, 41, 42],
[85, 86, 89, 90, 101, 102, 105, 106, 149, 150, 153, 154, 165, 166, 169, 170],
[1, 6, 10],
[5, 6, 25, 26, 41, 42],
[21, 22, 25, 26, 101, 102, 105, 106, 165, 166, 169, 170],
[1, 22, 26, 38, 42],
[5, 6, 89, 90, 105, 106, 153, 154, 169, 170],
[1, 86, 90, 102, 106, 150, 154, 166, 170],
[5, 6, 24, 40],
[21, 22, 25, 26, 97, 98, 161, 162],
[5, 6, 88, 104, 152, 168],
[5, 22, 25, 26, 38, 41, 42],
[21, 22, 89, 90, 101, 102, 105, 106, 153, 154, 165, 166, 169, 170],
[5, 22, 38, 73, 90, 106, 137, 154, 170],
[5, 22, 38, 89, 90, 105, 106, 153, 154, 169, 170],
[1, 6, 26, 42],
[5, 6, 25, 26, 105, 106, 169, 170],
[1, 22, 26, 102, 106, 166, 170],
[21, 22, 25, 26, 97, 102, 106, 161, 166, 170],
[5, 6, 24, 41, 42],
[21, 22, 25, 26, 97, 98, 165, 166, 169, 170],
[5, 6, 88, 104, 153, 154, 169, 170],
[5, 6, 24, 104, 168],
[5, 22, 38, 88, 104, 152, 168],
[5, 86, 89, 90, 102, 105, 106, 150, 153, 154, 166, 169, 170],
[1, 6, 90, 106, 154, 170],
[21, 22, 88, 101, 102, 105, 106, 152, 165, 166, 169, 170],
[5, 6, 24, 105, 106, 169, 170],
[5, 82, 89, 98, 105, 146, 153, 162, 169],
[1, 22, 26, 98, 162],
[21, 22, 89, 90, 101, 102, 104, 153, 154, 165, 166, 168],
[5, 6, 25, 26, 104, 168],
[21, 22, 25, 26, 97, 98, 164, 168],
[21, 86, 89, 90, 101, 102, 105, 106, 150, 153, 154, 165, 166, 169, 170],
[5, 22, 38, 73, 90, 106, 153, 154, 169, 170],
[1, 22, 90, 102, 106, 154, 166, 170],
[21, 22, 25, 26, 97, 102, 106, 165, 166, 169, 170],
[5, 6, 88, 105, 106, 153, 154, 169, 170],
[5, 18, 73, 98, 137, 162],
[5, 22, 25, 26, 102, 105, 106, 166, 169, 170],
[5, 22, 89, 90, 102, 105, 106, 153, 154, 166, 169, 170],
[1, 6, 26, 106, 170],
[21, 22, 73, 90, 101, 102, 106, 137, 154, 165, 166, 170],
[5, 6, 24, 104, 169, 170],
[5, 18, 25, 98, 105, 162, 169],
[5, 22, 38, 88, 104, 153, 154, 169, 170],
[5, 22, 88, 102, 104, 152, 166, 168],
[21, 22, 88, 101, 102, 105, 106, 153, 154, 165, 166, 169, 170],
[5, 18, 73, 102, 106, 137, 166, 170],
[1, 22, 26, 98, 166, 170],
[21, 22, 89, 90, 101, 102, 104, 153, 154, 165, 166, 169, 170],
[5, 6, 25, 26, 104, 169, 170],
[5, 22, 38, 73, 90, 106, 152, 168],
[21, 22, 25, 26, 97, 98, 164, 169, 170]]

def shapeCheck (sig : List ℕ) (hint : ℕ) :=
  let cs := shapeClasses[hint % 64]?.getD []
  let p := hint >>> 6
  let cols := ((List.range 16).map fun i => permRaw p (shapeRaw sig i)).eraseDups
  (hint % 64 < shapeClasses.size) && (List.range 8).all (fun i =>
    (List.range 8).all fun j => i == j || (p >>> (3*i)) % 8 != (p >>> (3*j)) % 8) &&
    cols.all (fun y => cs.contains y) && cs.all (fun y => cols.contains y)

private theorem corner_permAux_bit (p x d j : Nat) :
    (permRawAux p x d).testBit j = true ↔
      ∃ i < d, x.testBit i = true ∧ (p >>> (3*i)) % 8 = j := by
  induction d with
  | zero => simp [permRawAux]
  | succ d ih =>
    rw [Nat.exists_lt_succ_right]
    cases hx : x.testBit d <;> simp [permRawAux, hx, Nat.testBit_or, Nat.shiftLeft_eq,Nat.testBit_two_pow, ih, or_comm]

end PEqualNP.Outside.L_meta_217

namespace PEqualNP.Outside.L_meta_217.corner

def permMap (p : Nat) (i : Fin 8) : Fin 8 :=
  ⟨(p >>> (3*i.val)) % 8,Nat.mod_lt _ (by decide)⟩

theorem perm_mask (p : Nat) (S : Finset (Fin 8)) :
    permRaw p (maskOf S) = maskOf (S.image (permMap p)) := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply Bool.eq_iff_iff.mpr
  change (permRawAux p (maskOf S) 8).testBit j = true ↔ _
  rw [corner_permAux_bit]
  by_cases hj : j < 8
  · let k : Fin 8 := ⟨j,hj⟩
    rw [show j = k.val from rfl, mask_bit, decide_eq_true_eq, Finset.mem_image]
    constructor
    · rintro ⟨a,ha,bit,eq⟩
      let z : Fin 8 := ⟨a,ha⟩
      exact ⟨z,of_decide_eq_true ((mask_bit S z).symm.trans bit),Fin.ext eq⟩
    · rintro ⟨z,hz,he⟩
      exact ⟨z.val,z.isLt,(mask_bit S z).trans (decide_eq_true hz),congrArg Fin.val he⟩
  · simp only [maskOf,pack_test,hj,decide_false,Bool.false_and,Bool.false_eq_true,iff_false,not_exists]
    rintro i ⟨_,_,eq⟩
    have := Nat.mod_lt (p >>> (3*i)) (by decide : 0 < 8)
    omega

theorem shape_rows_short : ∀ j : Fin shapeClasses.size, (shapeClasses[j.val]).length ≤ 16 := by
  decide +kernel

theorem classified_raw {t hint : Nat} (ok : shapeCheck (reachSignature t) hint = true) :
    let cs := shapeClasses[hint % 64]?.getD []
    let σ := permMap (hint >>> 6)
    hint % 64 < shapeClasses.size ∧ cs.length ≤ 16 ∧ Function.Injective σ ∧
      ∀ a : Nat, a ∈ cs ↔ ∃ r ∈ minimalRaw t, a = maskOf (r.image σ) := by
  classical
  let cs := shapeClasses[hint % 64]?.getD []
  let p := hint >>> 6
  let cols := ((List.range 16).map (fun i => permRaw p (shapeRaw (reachSignature t) i))).eraseDups
  change (((decide (hint % 64 < shapeClasses.size) && (List.range 8).all (fun i =>
    (List.range 8).all fun j => i == j || (p >>> (3*i)) % 8 != (p >>> (3*j)) % 8)) &&
    cols.all (fun y => cs.contains y)) && cs.all (fun y => cols.contains y)) = true at ok
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range,
    Bool.or_eq_true,beq_iff_eq,bne_iff_ne,List.contains_iff_mem] at ok
  obtain ⟨⟨⟨valid,inject⟩,forward⟩,backward⟩ := ok
  refine ⟨valid,?_,?_,?_⟩
  · simpa [Array.getElem?_eq_getElem valid] using shape_rows_short ⟨_,valid⟩
  · intro i j h
    rcases inject i.val i.isLt j.val j.isLt with eq | neq
    · exact Fin.ext eq
    · exact False.elim (neq (congrArg Fin.val h))
  intro a
  have mem : a ∈ cs ↔ a ∈ cols := ⟨backward a,forward a⟩
  change a ∈ cs ↔ _
  rw [mem, minimal_eq_all]
  simp only [cols, List.mem_eraseDups,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨q,hq,rfl⟩
    let z : Fin 16 := ⟨q,hq⟩
    exact ⟨rawCorner t z, Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩,
      (congrArg (permRaw p) (signature_raw t z)).trans (perm_mask _ _)⟩
  · rintro ⟨r,hr,eq⟩
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨q.val,q.isLt,((congrArg (permRaw p) (signature_raw t q)).trans (perm_mask _ _)).trans eq.symm⟩

def profileNumber (cs : List Nat) (p : Nat) := packBits 16 fun j =>
  if h : j < cs.length then decide (cs[j] &&& p = 0) else false

theorem profile_bit (cs : List Nat) (p : Nat) (i : Fin 16) :
    (profileNumber cs p).testBit i.val = true ↔ ∃ h : i.val < cs.length, cs[i.val] &&& p = 0 := by
  by_cases h : i.val < cs.length <;> simp [profileNumber, pack_test,i.isLt,h]

theorem map_disjoint (σ : Fin 8 → Fin 8) (hinj : Function.Injective σ) (s a : Finset (Fin 8)) :
    maskOf (s.image σ) &&& maskOf (a.image σ) = 0 ↔ Disjoint s a := by
  rw [← mask_inter, mask_zero, ← Finset.disjoint_iff_inter_eq_empty]
  simp only [Finset.disjoint_left]
  constructor
  · intro h z zs za
    exact h (Finset.mem_image_of_mem σ zs) (Finset.mem_image_of_mem σ za)
  · intro h z hz hz'
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨b,hb,hb'⟩ := Finset.mem_image.mp hz'
    exact h ha ((hinj hb') ▸ hb)

open PEqualNP.AndCount

variable {n : Nat}

theorem classified_placement (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (hc : C.Computes G) (hk : C.size ≤ 4) (hint : Nat)
    (hclass : shapeCheck (reachSignature (topology C)) hint = true)
    (B : Finset (Fin 16)) (I : Fin 16 → Finset (Fin n))
    (hmis : ∀ i ∈ B, maximalIndep G (I i)) (hdist : Set.InjOn I B) :
    let cs := shapeClasses[hint % 64]?.getD []
    ∃ (f : Fin 16 → Fin 16) (p : Fin n → Nat), Set.InjOn f B ∧ (∀ v, p v < 256) ∧
      (∀ i ∈ B, (f i).val < cs.length) ∧
      (∀ v i, i ∈ B → (v ∈ I i ↔ (profileNumber cs (p v)).testBit (f i).val = true)) ∧
      ∀ a b, G.Adj a b → profileNumber cs (p a) &&& profileNumber cs (p b) = 0 := by
  classical
  let cs := shapeClasses[hint % 64]?.getD []
  let σ := permMap (hint >>> 6)
  obtain ⟨_,hlen,hinj,hclassmem⟩ := classified_raw hclass
  let raw (v : Fin n) := activeSide (patternOf C v)
  let p (v : Fin n) := maskOf ((raw v).image σ)
  have existsIdx (i : Fin 16) (hi : i ∈ B) : ∃ j : Fin 16, ∃ hj : j.val < cs.length,
      ∀ v, v ∈ I i ↔ (profileNumber cs (p v)).testBit j.val = true := by
    obtain ⟨s,hs,hsv⟩ := minimal_MIS C G hc hk (I i) (hmis i hi)
    have hmem : maskOf (s.image σ) ∈ cs := (hclassmem _).mpr ⟨s,hs,rfl⟩
    obtain ⟨j,hj,he⟩ := List.getElem_of_mem hmem
    let z : Fin 16 := ⟨j,lt_of_lt_of_le hj hlen⟩
    refine ⟨z,hj,?_⟩
    intro v
    rw [profile_bit]
    have eqmask : cs[j] &&& p v = 0 ↔ Disjoint s (raw v) := by
      rw [he, show p v = maskOf ((raw v).image σ) from rfl, map_disjoint σ hinj]
    exact ⟨fun hm => ⟨hj,eqmask.mpr ((hsv v).mp hm)⟩,
      fun ⟨_,eqm⟩ => (hsv v).mpr (eqmask.mp eqm)⟩
  let f (i : Fin 16) := if h : i ∈ B then (existsIdx i h).choose else 0
  have spec (i : Fin 16) (hi : i ∈ B) : ∃ h : (f i).val < cs.length,
      ∀ v, v ∈ I i ↔ (profileNumber cs (p v)).testBit (f i).val = true := by
    simpa only [f,dite_eq_left hi] using (existsIdx i hi).choose_spec
  refine ⟨f,p,?_,fun v => pack_lt 8 _,fun i hi => (spec i hi).choose,
    fun v i hi => (spec i hi).choose_spec v,?_⟩
  · intro i hi j hj h
    apply hdist hi hj
    ext v
    rw [(spec i hi).choose_spec v,(spec j hj).choose_spec v,h]
  intro a b he
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and,Nat.zero_testBit]
  by_cases hbit : (profileNumber cs (p a)).testBit j = true
  · rw [hbit, Bool.true_and]
    apply Bool.eq_false_iff.mpr
    intro hb
    by_cases hj : j < 16
    · let z : Fin 16 := ⟨j,hj⟩
      obtain ⟨hz,h1⟩ := (profile_bit cs (p a) z).mp hbit
      obtain ⟨_,h2⟩ := (profile_bit cs (p b) z).mp hb
      obtain ⟨s,hs,eq⟩ := (hclassmem _).mp (List.getElem_mem (l := cs) hz)
      rw [eq] at h1 h2
      exact minimal_separates C G hc hk he s hs
        ⟨(map_disjoint _ hinj _ (raw a)).mp h1,(map_disjoint _ hinj _ (raw b)).mp h2⟩
    · simp [profileNumber,pack_test,hj] at hbit
  · change ((profileNumber cs (p a)).testBit j && (profileNumber cs (p b)).testBit j) = false
    rw [Bool.eq_false_iff.mpr hbit,Bool.false_and]

end PEqualNP.Outside.L_meta_217.corner

namespace PEqualNP.Outside.L_meta_217

open PEqualNP.AndCount

def rowMaskOK (n : Nat) (rows : List Nat) (m : Nat) : Bool :=
  (List.range n).all fun i => m.testBit i == (rows.getD i 0 &&& m == 0)

def rowMIS (n : Nat) (rows : List Nat) : List Nat :=
  (List.range (2^n)).filter (rowMaskOK n rows)

def rowISet (n m : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun i => m.testBit i.val

def rowBase (n : Nat) (rows : List Nat) := 2^(rowMIS n rows).length - 1

def rowPattern (n : Nat) (rows : List Nat) (v : Nat) : Nat :=
  corner.packBits 16 fun i => ((rowMIS n rows).getD i 0).testBit v

private theorem rowMax {n : Nat} (rows : List Nat) (G : SimpleGraph (Fin n))
    (hadj : ∀ a b : Fin n, (rows.getD a.val 0).testBit b.val = true ↔ G.Adj a b)
    (m : Nat) (hm : m ∈ rowMIS n rows) :
    corner.maximalIndep G (rowISet n m) := by
  have hr := List.mem_filter.mp hm
  have hs := List.mem_range.mp hr.1
  have e (i : Fin n) : m.testBit i.val = (rows.getD i.val 0 &&& m == 0) :=
    beq_iff_eq.mp (List.all_eq_true.mp hr.2 i.val (List.mem_range.mpr i.isLt))
  constructor
  · intro u hu v hv huv
    have bu := (Finset.mem_filter.mp hu).2
    have bv := (Finset.mem_filter.mp hv).2
    have eq : rows.getD u.val 0 &&& m = 0 := beq_iff_eq.mp ((e u).symm.trans bu)
    have h := congrArg (fun z : Nat => z.testBit v.val) eq
    change (rows.getD u.val 0 &&& m).testBit v.val = (0 : Nat).testBit v.val at h
    rw [Nat.testBit_and, (hadj u v).mpr huv,bv,Nat.zero_testBit] at h
    contradiction
  · intro u hmiss
    have hmU : m.testBit u.val = false := Bool.eq_false_iff.mpr
      (fun h => hmiss (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
    have nn : rows.getD u.val 0 &&& m ≠ 0 := by
      intro h
      have e' := e u
      rw [hmU,h] at e'
      contradiction
    obtain ⟨j,hj⟩ := Nat.exists_testBit_of_ne_zero nn
    rw [Nat.testBit_and,Bool.and_eq_true] at hj
    have hlt : j < n := by
      by_contra! h
      have hstop := Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) h))
      rw [hstop] at hj
      simp at hj
    refine ⟨⟨j,hlt⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj.2⟩,(hadj _ _).mp hj.1⟩

private theorem rowISet_inj {n a b : Nat} (ha : a < 2^n) (hb : b < 2^n)
    (h : rowISet n a = rowISet n b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · apply Bool.eq_iff_iff.mpr
    have hm := Finset.ext_iff.mp h (⟨i,hi⟩ : Fin n)
    simpa [rowISet] using hm
  · have hm := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_lt hi)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hm),Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hm)]

private theorem rowMIS_nodup (n : Nat) (rows : List Nat) : (rowMIS n rows).Nodup :=
  (List.nodup_range).filter _

def rowIs (n : Nat) (rows : List Nat) (i : Fin 16) :=
  rowISet n ((rowMIS n rows).getD i.val 0)

def rowSlots (n : Nat) (rows : List Nat) : Finset (Fin 16) :=
  Finset.univ.filter fun i => (rowBase n rows).testBit i.val

theorem rowSlot_mem {n : Nat} {rows : List Nat} (i : Fin 16) :
    i ∈ rowSlots n rows ↔ i.val < (rowMIS n rows).length := by
  simp [rowSlots,rowBase,Nat.testBit_two_pow_sub_one]

theorem rowIs_max {n : Nat} (rows : List Nat) (G : SimpleGraph (Fin n))
    (hadj : ∀ a b : Fin n, (rows.getD a.val 0).testBit b.val = true ↔ G.Adj a b)
    (i : Fin 16) (hi : i ∈ rowSlots n rows) : corner.maximalIndep G (rowIs n rows i) := by
  apply rowMax rows G hadj
  rw [List.getD_eq_getElem _ _ (rowSlot_mem i |>.mp hi)]
  exact List.getElem_mem _

theorem rowIs_inj (n : Nat) (rows : List Nat) : Set.InjOn (rowIs n rows) (rowSlots n rows) := by
  intro i hi j hj he
  have hi' := (rowSlot_mem i).mp hi
  have hj' := (rowSlot_mem j).mp hj
  simp only [rowIs,List.getD_eq_getElem _ _ hi',List.getD_eq_getElem _ _ hj'] at he
  have small (m) (hm : m ∈ rowMIS n rows) := List.mem_range.mp (List.mem_filter.mp hm).1
  apply Fin.ext
  apply (rowMIS_nodup n rows).eq_of_getElem_eq hi' hj'
  exact rowISet_inj (small _ (List.getElem_mem _)) (small _ (List.getElem_mem _)) he

theorem rowPattern_bit (n : Nat) (rows : List Nat) (v : Fin n) (i : Fin 16) :
    (rowPattern n rows v.val).testBit i.val = true ↔ v ∈ rowIs n rows i := by
  simp [rowPattern, corner.pack_test, i.isLt,rowIs,rowISet]

theorem rowMIS_count {n : Nat} (rows : List Nat) (G : SimpleGraph (Fin n))
    (hadj : ∀ a b : Fin n, (rows.getD a.val 0).testBit b.val = true ↔ G.Adj a b)
    (C : AndCountCircuit n) (hc : C.Computes G) :
    (rowMIS n rows).length ≤ 2^C.size := by
  let M := rowMIS n rows
  let sets (i : Fin M.length) := rowISet n M[i.val]
  have rep (i : Fin M.length) : ∀ v : Fin n,
      v ∈ sets i ↔ v ∉ corner.clause C (corner.left C (sets i)) := by
    have h := rowMax rows G hadj M[i.val] (List.getElem_mem i.isLt)
    apply corner.complement_clause
    · apply Bool.eq_false_iff.mpr
      intro hh
      obtain ⟨a,ha,b,hb,he⟩ := (hc _).mp hh
      exact h.1 a ha b hb he
    · intro u hu
      obtain ⟨v,hv,he⟩ := h.2 u hu
      exact (hc _).mpr ⟨u,by simp,v,Finset.mem_insert_of_mem hv,he⟩
  let f (i : Fin M.length) := corner.left C (sets i)
  have inj : Function.Injective f := by
    intro i j he
    have eq : sets i = sets j := by
      ext v
      rw [rep i, rep j]
      change v ∉ corner.clause C (f i) ↔ v ∉ corner.clause C (f j)
      rw [he]
    have small (i : Fin M.length) : M[i.val] < 2^n :=
      List.mem_range.mp (List.mem_filter.mp (List.getElem_mem (l := M) i.isLt)).1
    exact Fin.ext ((rowMIS_nodup n rows).eq_of_getElem_eq i.isLt j.isLt
      (rowISet_inj (small i) (small j) eq))
  simpa [M] using Fintype.card_le_of_injective f inj


def classUses (cs : List Nat) : Finset (Fin 8) :=
  Finset.univ.filter fun j => (cs.foldr (· ||| ·) 0).testBit j.val

theorem classUses_bound {n : Nat} (C : AndCountCircuit n) (_hk : C.size ≤ 4) (hint : Nat)
    (hclass : shapeCheck (corner.reachSignature (corner.topology C)) hint = true) :
    (classUses (shapeClasses[hint % 64]?.getD [])).card ≤ 2*C.size := by
  classical
  let σ := corner.permMap (hint >>> 6)
  let S : Finset (Fin 8) := Finset.univ.filter fun z => z.val < 2*C.size
  have used {q : Fin 16} {z : Fin 8} (hz : z ∈ corner.rawCorner (corner.topology C) q) : z ∈ S := by
    obtain ⟨i,⟨a,ha,path⟩,rfl⟩ := (corner.rawCorner_path q z).mp hz
    have bound : i ≤ a := by
      clear hz
      induction path with
      | refl => exact le_rfl
      | tail _ e ih => exact le_trans (le_of_lt e.1) ih
    have haC : a.val < C.size := by
      by_contra! h
      rw [corner.topology_out C a.val a.isLt] at ha
      simp [corner.outputFlag, Nat.not_lt.mpr h] at ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change 2*i.val + (q.val.testBit i.val).toNat < 2*C.size
    change i.val ≤ a.val at bound
    cases q.val.testBit i.val <;> simp <;> omega
  obtain ⟨_,_,_,hmem⟩ := corner.classified_raw hclass
  have sub : classUses (shapeClasses[hint % 64]?.getD []) ⊆ S.image σ := by
    intro z hz
    obtain ⟨m,hm,hb⟩ := (corner.fold_or_bit _ z.val).mp (Finset.mem_filter.mp hz).2
    obtain ⟨r,hr,rfl⟩ := (hmem m).mp hm
    rw [corner.mask_bit,decide_eq_true_eq] at hb
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    exact Finset.mem_image_of_mem σ (used hj)
  have cardS : S.card ≤ 2*C.size := by
    have sm : S.image Fin.val ⊆ Finset.range (2*C.size) := by
      rintro v hv
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    simpa [Finset.card_image_of_injective _ Fin.val_injective] using Finset.card_le_card sm
  exact (Finset.card_le_card sub).trans ((Finset.card_image_le).trans cardS)

def rowClassHost (cs : List Nat) : List Nat :=
  ((List.range 256).map (corner.profileNumber cs)).eraseDups.mergeSort


def samplePattern (ms : List Nat) (v : Nat) : Nat :=
  corner.packBits 16 fun i => (ms.getD i 0).testBit v

def sampleSlots (ms : List Nat) : Finset (Fin 16) :=
  Finset.univ.filter fun i => (2^ms.length-1 : Nat).testBit i.val

private theorem sampleSlots_lt (ms : List Nat) (i : Fin 16) :
    i ∈ sampleSlots ms ↔ i.val < ms.length := by
  simp [sampleSlots,Nat.testBit_two_pow_sub_one]

theorem sampleRows_count {n : Nat} (rows : List Nat) (G : SimpleGraph (Fin n))
    (hadj : ∀ a b : Fin n, (rows.getD a.val 0).testBit b.val = true ↔ G.Adj a b)
    (C : AndCountCircuit n) (hc : C.Computes G)
    (ms : List Nat) (hn : ms.Nodup) (hok : ∀ m ∈ ms, m < 2^n ∧ rowMaskOK n rows m = true) :
    ms.length ≤ 2^C.size := by
  have sub : ms ⊆ rowMIS n rows := by
    intro m hm
    have h := hok m hm
    exact List.mem_filter.mpr ⟨List.mem_range.mpr h.1,h.2⟩
  exact (hn.subperm sub).length_le.trans (rowMIS_count rows G hadj C hc)

theorem sampleRows_placement {n : Nat} (rows : List Nat) (G : SimpleGraph (Fin n))
    (hadj : ∀ a b : Fin n, (rows.getD a.val 0).testBit b.val = true ↔ G.Adj a b)
    (C : AndCountCircuit n) (hc : C.Computes G) (hk : C.size ≤ 4) (hint : Nat)
    (hclass : shapeCheck (corner.reachSignature (corner.topology C)) hint = true)
    (ms : List Nat) (hn : ms.Nodup) (hok : ∀ m ∈ ms, m < 2^n ∧ rowMaskOK n rows m = true)
    (vertices : List Nat) (hverts : ∀ v ∈ vertices, v < n) :
    let cs := shapeClasses[hint % 64]?.getD []
    ∃ (profile : Nat → Nat) (f : Fin 16 → Fin 16),
      Set.InjOn f (sampleSlots ms) ∧
      (∀ i ∈ sampleSlots ms, (2^cs.length-1 : Nat).testBit (f i).val = true) ∧
      (∀ v ∈ vertices, profile v ∈ rowClassHost cs) ∧
      (∀ v ∈ vertices, ∀ i ∈ sampleSlots ms, (samplePattern ms v).testBit i.val =
        (profile v).testBit (f i).val) ∧
      ∀ v ∈ vertices, ∀ w ∈ vertices, (rows.getD v 0).testBit w = true →
        profile v &&& profile w = 0 := by
  let I (i : Fin 16) := rowISet n (ms.getD i.val 0)
  have hm (i : Fin 16) (hi : i ∈ sampleSlots ms) : ms.getD i.val 0 ∈ ms := by
    rw [List.getD_eq_getElem _ _ ((sampleSlots_lt ms i).mp hi)]
    exact List.getElem_mem _
  have hmax (i : Fin 16) (hi : i ∈ sampleSlots ms) : corner.maximalIndep G (I i) := by
    apply rowMax rows G hadj
    have h := hok _ (hm i hi)
    exact List.mem_filter.mpr ⟨List.mem_range.mpr h.1,h.2⟩
  have hiI : Set.InjOn I (sampleSlots ms) := by
    intro i hi j hj he
    have eq := rowISet_inj (hok _ (hm i hi)).1 (hok _ (hm j hj)).1 he
    have bi := (sampleSlots_lt ms i).mp hi
    have bj := (sampleSlots_lt ms j).mp hj
    rw [List.getD_eq_getElem _ _ bi,List.getD_eq_getElem _ _ bj] at eq
    exact Fin.ext (hn.eq_of_getElem_eq bi bj eq)
  have pbit (v : Fin n) (i : Fin 16) :
      (samplePattern ms v.val).testBit i.val = true ↔ v ∈ I i := by
    simp [samplePattern,corner.pack_test,i.isLt,I,rowISet]
  let cs := shapeClasses[hint % 64]?.getD []
  obtain ⟨f,p,hinj,hp,hvalid,hbit,hedge⟩ := corner.classified_placement C G hc hk hint hclass
    (sampleSlots ms) I hmax hiI
  let profile (j : Nat) := if h : j < n then corner.profileNumber cs (p ⟨j,h⟩) else 0
  refine ⟨profile,f,hinj,?_,?_,?_,?_⟩
  · intro i hi
    simpa only [Nat.testBit_two_pow_sub_one,decide_eq_true_eq] using hvalid i hi
  · intro v hv
    have hvn := hverts v hv
    simp only [profile,dite_eq_left hvn,rowClassHost,List.mem_mergeSort,List.mem_eraseDups,List.mem_map,List.mem_range]
    exact ⟨p ⟨v,hvn⟩,hp _,rfl⟩
  · intro v hv i hi
    have hvn := hverts v hv
    apply Bool.eq_iff_iff.mpr
    exact (pbit ⟨v,hvn⟩ i).trans (by simpa only [profile,dite_eq_left hvn] using hbit ⟨v,hvn⟩ i hi)
  · intro v hv w hw adj
    have hvn := hverts v hv
    have hwn := hverts w hw
    simpa only [profile,dite_eq_left hvn,dite_eq_left hwn] using
      hedge ⟨v,hvn⟩ ⟨w,hwn⟩ ((hadj ⟨v,hvn⟩ ⟨w,hwn⟩).mp adj)

theorem rows_placement {n : Nat} (rows : List Nat) (G : SimpleGraph (Fin n))
    (hadj : ∀ a b : Fin n, (rows.getD a.val 0).testBit b.val = true ↔ G.Adj a b)
    (C : AndCountCircuit n) (hc : C.Computes G) (hk : C.size ≤ 4) (hint : Nat)
    (hclass : shapeCheck (corner.reachSignature (corner.topology C)) hint = true)
    (vertices : List Nat) (hverts : ∀ v ∈ vertices, v < n) :
    let cs := shapeClasses[hint % 64]?.getD []
    ∃ (profile : Nat → Nat) (f : Fin 16 → Fin 16),
      Set.InjOn f (rowSlots n rows) ∧
      (∀ i ∈ rowSlots n rows, (2^cs.length-1 : Nat).testBit (f i).val = true) ∧
      (∀ v ∈ vertices, profile v ∈ rowClassHost cs) ∧
      (∀ v ∈ vertices, ∀ i ∈ rowSlots n rows, (rowPattern n rows v).testBit i.val =
        (profile v).testBit (f i).val) ∧
      ∀ v ∈ vertices, ∀ w ∈ vertices, (rows.getD v 0).testBit w = true →
        profile v &&& profile w = 0 := by
  apply sampleRows_placement rows G hadj C hc hk hint hclass (rowMIS n rows) (rowMIS_nodup n rows) _ vertices hverts
  intro m hm
  have h := List.mem_filter.mp hm
  exact ⟨List.mem_range.mp h.1,h.2⟩

end PEqualNP.Outside.L_meta_217

namespace PEqualNP.Outside.L_meta_217
/- Circuits with fewer than five AND gates have finitely many clause shapes. The hints identify an equivalent shape and the checker verifies each identification. -/
def shapeHints : List ℕ := [
0x3eb1a204,0x2c688f83,0x2c688f87,0x25688f87,0x1ab08f87,0x2c688f8f,0x25688f8f,0x1a948f87,0x2c4c8f8f,0x254c8f8f,0x1a22cf87,0x2c21af8f,
0x2521af8f,0x8b1af8f,0x2c688fa4,0x25688fa4,0x895af8f,0x2c4c8fa4,0x254c8fa4,0x1a225f87,0x2c213f8f,0x25213f8f,0x8b13f8f,0x2c681fa4,
0x25681fa4,0x8953f8f,0x2c4c1fa4,0x254c1fa4,0x2c6be203,0x1a23eb02,0x1a23eb06,0x1323eb06,0x86beb06,0x1a23eb0e,0x1323eb0e,0x84feb06,
0x1a07eb0e,0x1307eb0e,0x2c6be207,0x1a22cf86,0x1a23eb09,0x2c23e68c,0x1a23eb10,0x1a23eb11,0x2c23e695,0x1a07eb10,0x1a07eb11,0x2c07e695,
0x1a22cf93,0x2c23e697,0x1a23eb25,0x2c23e6a7,0x1a07eb25,0x2c07e6a7,0x1a225f93,0x2c237697,0x1a237b25,0x2c2376a7,0x1a077b25,0x2c0776a7,
0x256be207,0x1322cf86,0x2523e68c,0x1323eb09,0x1323eb10,0x2523e695,0x1323eb11,0x1307eb10,0x2507e695,0x1307eb11,0x1322cf93,0x2523e697,
0x1323eb25,0x2523e6a7,0x1307eb25,0x2507e6a7,0x13225f93,0x25237697,0x13237b25,0x252376a7,0x13077b25,0x250776a7,0x1ab3e207,0x86acf86,
0x86beb10,0x16beb10,0x86beb09,0x86beb11,0x16beb11,0x8b3e68c,0x8b3e695,0x1b3e695,0x86acf93,0x86beb25,0x16beb25,0x8b3e697,
0x8b3e6a7,0x1b3e6a7,0x86a5f93,0x86b7b25,0x16b7b25,0x8b37697,0x8b376a7,0x1b376a7,0x2c6be20f,0x1a22cf8e,0x1a22cf91,0x2521af95,
0x86acf91,0x1a23eb1b,0x1ab3e21d,0x895af95,0x2c6be21d,0x2c6be221,0x1a22cfaa,0x1a22cfab,0x1322cfad,0x86acfab,0x1ab3e232,0x84ecfad,
0x2c6be232,0x2c6be235,0x1a225faa,0x1a225fab,0x13225fad,0x86a5fab,0x1ab37232,0x84e5fad,0x2c6b7232,0x2c6b7235,0x256be20f,0x1322cf8e,
0x2c21af95,0x1322cf91,0x16acf91,0x13b3e21d,0x1323eb1b,0x195af95,0x256be221,0x256be21d,0x1322cfaa,0x1a22cfad,0x1322cfab,0x16acfab,
0x13b3e232,0x14ecfad,0x256be235,0x256be232,0x13225faa,0x1a225fad,0x13225fab,0x16a5fab,0x13b37232,0x14e5fad,0x256b7235,0x256b7232,
0x1a97e207,0x84ecf86,0x84feb10,0x14feb10,0x897e68c,0x897e695,0x197e695,0x84feb09,0x84feb11,0x14feb11,0x84ecf93,0x84feb25,
0x14feb25,0x897e697,0x897e6a7,0x197e6a7,0x84e5f93,0x84f7b25,0x14f7b25,0x8977697,0x89776a7,0x19776a7,0x2c4fe20f,0x1a06cf8e,
0x1a06cf91,0x2505af95,0x8b1af95,0x2c4fe21d,0x2c4fe221,0x84ecf91,0x1a07eb1b,0x1a97e21d,0x1a06cfaa,0x1a06cfab,0x1306cfad,0x86acfad,
0x2c4fe232,0x2c4fe235,0x84ecfab,0x1a97e232,0x1a065faa,0x1a065fab,0x13065fad,0x86a5fad,0x2c4f7232,0x2c4f7235,0x84e5fab,0x1a977232,
0x254fe20f,0x1306cf8e,0x2c05af95,0x1306cf91,0x1b1af95,0x254fe221,0x254fe21d,0x14ecf91,0x1397e21d,0x1307eb1b,0x1306cfaa,0x1a06cfad,
0x1306cfab,0x16acfad,0x254fe235,0x254fe232,0x14ecfab,0x1397e232,0x13065faa,0x1a065fad,0x13065fab,0x16a5fad,0x254f7235,0x254f7232,
0x14e5fab,0x13977232,0x2cf9a203,0x1af88b02,0x1af88b06,0x13f88b06,0x8f9ab06,0x1af88b0e,0x13f88b0e,0x8f93b06,0x1af81b0e,0x13f81b0e,
0x1afac202,0x8fac681,0x8fac685,0x1fac685,0x1afac206,0x8f9ab05,0x8fac688,0x1afac20b,0x8f9ab12,0x1afac216,0x8f93b12,0x1afa5216,
0x13fac206,0x1f9ab05,0x13fac20b,0x1fac688,0x1f9ab12,0x13fac216,0x1f93b12,0x13fa5216,0x2cf9a207,0x1ab08f86,0x1af88b09,0x2cf8868c,
0x1ab08f93,0x2cf88697,0x1a948f93,0x2cdc8697,0x1af88b10,0x1af88b11,0x2cf88695,0x1af88b25,0x2cf886a7,0x1adc8b25,0x2cdc86a7,0x1af81b10,
0x1af81b11,0x2cf81695,0x1af81b25,0x2cf816a7,0x1adc1b25,0x2cdc16a7,0x1ab3e206,0x86beb05,0x8b3e688,0x1ab3e20b,0x86beb12,0x1ab3e216,
0x84feb12,0x1a97e216,0x1afac209,0x8b1af88,0x8fac68a,0x1afac20d,0x8b1af94,0x1afac218,0x895af94,0x1adec218,0x86acf94,0x1ab3e218,
0x8b1afa6,0x1afac228,0x895afa6,0x1adec228,0x86a5f94,0x1ab37218,0x8b13fa6,0x1afa5228,0x8953fa6,0x1ade5228,0x2cf9a20c,0x1ab08f8b,
0x1af88b0d,0x1323eb0d,0x1ab08f99,0x1323eb1a,0x1a948f99,0x1307eb1a,0x1322cf99,0x1af88b1a,0x8b1afa9,0x895afa9,0x13225f99,0x1af81b1a,
0x8b13fa9,0x8953fa9,0x1ab3e213,0x86acf92,0x8b3e694,0x1ab3e219,0x86beb1c,0x1ab3e21e,0x8b3e6a0,0x1ab3e222,0x86acfac,0x1ab3e22e,
0x8b3e6b4,0x1ab3e236,0x86a5fac,0x1ab3722e,0x8b376b4,0x1ab37236,0x2cf9a217,0x1ab08f96,0x1af88b18,0x1322cf9a,0x1ab08f9e,0x16beb1f,
0x1a948fa2,0x2cf9a223,0x16acfaf,0x1af88b30,0x1322cfb1,0x8b1afb3,0x1adc8b37,0x2cf9a238,0x16a5faf,0x1af81b30,0x13225fb1,0x8b13fb3,
0x1adc1b37,0x2cf93238,0x1a97e213,0x84ecf92,0x897e694,0x1a97e219,0x897e6a0,0x1a97e222,0x84feb1c,0x1a97e21e,0x84ecfac,0x1a97e22e,
0x897e6b4,0x1a97e236,0x84e5fac,0x1a97722e,0x89776b4,0x1a977236,0x2cdda217,0x1a948f96,0x1adc8b18,0x1306cf9a,0x1ab08fa2,0x2cdda223,
0x1a948f9e,0x14feb1f,0x14ecfaf,0x1adc8b30,0x1306cfb1,0x1af88b37,0x2cdda238,0x895afb3,0x14e5faf,0x1adc1b30,0x13065fb1,0x1af81b37,
0x2cdd3238,0x8953fb3,0x25f9a207,0x13b08f86,0x25f8868c,0x13f88b09,0x13b08f93,0x25f88697,0x13948f93,0x25dc8697,0x13f88b10,0x25f88695,
0x13f88b11,0x13f88b25,0x25f886a7,0x13dc8b25,0x25dc86a7,0x13f81b10,0x25f81695,0x13f81b11,0x13f81b25,0x25f816a7,0x13dc1b25,0x25dc16a7,
0x13b3e206,0x16beb05,0x13b3e20b,0x1b3e688,0x16beb12,0x13b3e216,0x14feb12,0x1397e216,0x25f9a20c,0x13b08f8b,0x1a23eb0d,0x13f88b0d,
0x13b08f99,0x1a23eb1a,0x13948f99,0x1a07eb1a,0x1a22cf99,0x13f88b1a,0x1b1afa9,0x195afa9,0x1a225f99,0x13f81b1a,0x1b13fa9,0x1953fa9,
0x13fac209,0x1b1af88,0x13fac20d,0x1fac68a,0x1b1af94,0x13fac218,0x195af94,0x13dec218,0x16acf94,0x13b3e218,0x1b1afa6,0x13fac228,
0x195afa6,0x13dec228,0x16a5f94,0x13b37218,0x1b13fa6,0x13fa5228,0x1953fa6,0x13de5228,0x13b3e213,0x16acf92,0x13b3e219,0x1b3e694,
0x16beb1c,0x13b3e21e,0x1b3e6a0,0x13b3e222,0x16acfac,0x13b3e22e,0x1b3e6b4,0x13b3e236,0x16a5fac,0x13b3722e,0x1b376b4,0x13b37236,
0x25f9a217,0x13b08f96,0x1a22cf9a,0x13f88b18,0x13b08f9e,0x86beb1f,0x13948fa2,0x25f9a223,0x86acfaf,0x1a22cfb1,0x13f88b30,0x1b1afb3,
0x13dc8b37,0x25f9a238,0x86a5faf,0x1a225fb1,0x13f81b30,0x1b13fb3,0x13dc1b37,0x25f93238,0x1397e213,0x14ecf92,0x1397e219,0x197e694,
0x197e6a0,0x1397e222,0x14feb1c,0x1397e21e,0x14ecfac,0x1397e22e,0x197e6b4,0x1397e236,0x14e5fac,0x1397722e,0x19776b4,0x13977236,
0x25dda217,0x13948f96,0x1a06cf9a,0x13dc8b18,0x13b08fa2,0x25dda223,0x13948f9e,0x84feb1f,0x84ecfaf,0x1a06cfb1,0x13dc8b30,0x13f88b37,
0x25dda238,0x195afb3,0x84e5faf,0x1a065fb1,0x13dc1b30,0x13f81b37,0x25dd3238,0x1953fb3,0x3eb1a203,0x3e688b02,0x3e688b06,0x3e4c8b06,
0x3e21ab06,0x3e688b0e,0x3e4c8b0e,0x3e213b06,0x3e681b0e,0x3e4c1b0e,0x3e6ac202,0x3e22c681,0x3e22c685,0x3e06c685,0x3e6ac206,0x3e21ab05,
0x3e22c688,0x3e6ac20b,0x3e21ab12,0x3e6ac216,0x3e213b12,0x3e6a5216,0x3e4ec206,0x3e05ab05,0x3e4ec20b,0x3e06c688,0x3e05ab12,0x3e4ec216,
0x3e053b12,0x3e4e5216,0x3eb1a202,0x3eb08681,0x3eb08685,0x3eb01685,0x3eb1a201,0x3eb1a200]

def shapeCheckList : List (List ℕ) → List ℕ → Bool
  | [], [] => true
  | a::xs, b::ys => shapeCheck a b && shapeCheckList xs ys
  | _,_ => false

set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem shape_test : shapeCheckList shape04 shapeHints = true := by decide +kernel

theorem classification_hint (sig : List ℕ) (hs : sig ∈ shape04) :
    ∃ h, shapeCheck sig h = true := by
  have all (rows : List (List ℕ)) (hints : List ℕ)
      (h : shapeCheckList rows hints = true) (mem : sig ∈ rows) : ∃ h, shapeCheck sig h = true := by
    induction rows generalizing hints with
    | nil => simp at mem
    | cons a l ih =>
      cases hints with
      | nil => simp [shapeCheckList] at h
      | cons b bs =>
        rw [shapeCheckList, Bool.and_eq_true] at h
        rcases List.mem_cons.mp mem with rfl | hm
        · exact ⟨b,h.1⟩
        · exact ih bs h.2 hm
  exact all _ _ shape_test hs



private def sites (a : ℕ) : Finset (Fin 16) :=
  Finset.univ.filter fun i => a.testBit i.val

private def countNibble (x : ℕ) := (0x4332322132212110 >>> (4*(x % 16))) % 16

private theorem nibble_spec (x : ℕ) : countNibble x =
    (x.testBit 0).toNat + (x.testBit 1).toNat + (x.testBit 2).toNat + (x.testBit 3).toNat := by
  have table : ∀ i : Fin 16, countNibble i.val =
    (i.val.testBit 0).toNat + (i.val.testBit 1).toNat + (i.val.testBit 2).toNat +
      (i.val.testBit 3).toNat := by decide
  have hor (j : ℕ) (hj : j < 4) : (x % 16).testBit j = x.testBit j := by
    exact (Nat.testBit_mod_two_pow x 4 j).trans (by simp [hj])
  simpa only [countNibble,Nat.mod_mod,hor 0 (by decide),hor 1 (by decide),hor 2 (by decide),hor 3 (by decide)] using
    table ⟨x % 16, Nat.mod_lt _ (by decide)⟩

private def weight (x : ℕ) :=
  countNibble x + countNibble (x >>> 4) + countNibble (x >>> 8) + countNibble (x >>> 12)

private theorem weight_spec (x : ℕ) : weight x = (sites x).card := by
  rw [sites,Finset.card_filter]
  simp only [weight,nibble_spec,Nat.testBit_shiftRight]
  repeat rw [Fin.sum_univ_succ]
  simp [Bool.toNat, Nat.add_assoc]

private def withoutBits (a b : ℕ) := a ^^^ (a &&& b)

private theorem bit_without (a b i : ℕ) :
    (withoutBits a b).testBit i = (a.testBit i && !(b.testBit i)) := by
  simp only [withoutBits, Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> decide

private def mapsRegion (f : Fin 16 → Fin 16) (base : ℕ) (R : ℕ × ℕ) :=
  ∀ i ∈ sites R.1, i ∈ sites base ∧ f i ∈ sites R.2

private theorem room {f : Fin 16 → Fin 16} {base : ℕ} {R : ℕ × ℕ}
    (hf : Set.InjOn f (sites base)) (h : mapsRegion f base R) :
    weight R.1 ≤ weight R.2 := by
  have inj : Set.InjOn f (sites R.1) := fun i hi j hj e =>
    hf (h i hi).1 (h j hj).1 e
  have sub : (sites R.1).image f ⊆ sites R.2 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact (h i hi).2
  simpa only [weight_spec, Finset.card_image_iff.mpr inj] using Finset.card_le_card sub


private theorem maps_split {f : Fin 16 → Fin 16} {base p u : ℕ} {R : ℕ × ℕ}
    (hr : mapsRegion f base R)
    (he : ∀ i ∈ sites base, p.testBit i.val = u.testBit (f i).val) :
    mapsRegion f base (R.1 &&& p, R.2 &&& u) ∧
    mapsRegion f base (withoutBits R.1 p, withoutBits R.2 u) := by
  constructor
  · intro i hi
    simp only [sites, Finset.mem_filter, Finset.mem_univ, true_and, Nat.testBit_and,
      Bool.and_eq_true] at hi
    obtain ⟨hbase, hs⟩ := hr i (by simpa [sites] using hi.1)
    refine ⟨hbase, ?_⟩
    simp only [sites, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    simp [Nat.testBit_and, hs, ← he i hbase, hi.2]
  · intro i hi
    simp only [sites, Finset.mem_filter, Finset.mem_univ, true_and, bit_without,
      Bool.and_eq_true, Bool.not_eq_true'] at hi
    obtain ⟨hbase, hs⟩ := hr i (by simpa [sites] using hi.1)
    refine ⟨hbase, ?_⟩
    simp only [sites, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    simp [bit_without, hs, ← he i hbase, hi.2]

private def fitsPair (base corner p q u w : ℕ) (edge : Bool) : Bool :=
  (!edge || decide (u &&& w = 0)) &&
  decide (weight (base &&& p &&& q) ≤ weight (corner &&& u &&& w)) &&
  decide (weight (withoutBits (base &&& p) q) ≤ weight (withoutBits (corner &&& u) w)) &&
  decide (weight (withoutBits base p &&& q) ≤ weight (withoutBits corner u &&& w)) &&
  decide (weight (withoutBits (withoutBits base p) q) ≤
    weight (withoutBits (withoutBits corner u) w))

set_option maxHeartbeats 1600000 in
private theorem fits_pair {base corner p q u w : ℕ} {edge : Bool}
    {f : Fin 16 → Fin 16} (hf : Set.InjOn f (sites base))
    (hc : mapsRegion f base (base,corner))
    (hp : ∀ i ∈ sites base, p.testBit i.val = u.testBit (f i).val)
    (hq : ∀ i ∈ sites base, q.testBit i.val = w.testBit (f i).val)
    (hed : edge = true → u &&& w = 0) :
    fitsPair base corner p q u w edge = true := by
  obtain ⟨py,pn⟩ := maps_split hc hp
  obtain ⟨yy,yn⟩ := maps_split py hq
  obtain ⟨ny,nn⟩ := maps_split pn hq
  have hEdge : (!edge || decide (u &&& w = 0)) = true := by
    cases h : edge <;> simp [h,hed]
  simp only [fitsPair, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨hEdge,room (R := ((base &&& p) &&& q,(corner &&& u) &&& w)) hf yy⟩,room (R := (withoutBits (base &&& p) q,withoutBits (corner &&& u) w)) hf yn⟩,room (R := (withoutBits base p &&& q,withoutBits corner u &&& w)) hf ny⟩,room (R := (withoutBits (withoutBits base p) q,withoutBits (withoutBits corner u) w)) hf nn⟩


private theorem weight_le_16 (a : ℕ) : weight a ≤ 16 := by
  rw [weight_spec]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

private def packLanes : List ℕ → ℕ
  | [] => 0
  | a :: l => a + 256 * packLanes l

private def ones (n : ℕ) := packLanes (List.replicate n 1)

private def meets (r : ℕ) (lanes : ℕ) (threshold : ℕ) := lanes + r * (128-threshold)

private theorem lane_test {xs : List ℕ} (h : ∀ x ∈ xs, x ≤ 16)
    (i : ℕ) (hi : i < xs.length) (k : ℕ) (hk : k ≤ 16) :
    (meets (ones xs.length) (packLanes xs) k).testBit (8*i+7) = decide (k ≤ xs[i]) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons v vs ih =>
    have hv := h v (by simp)
    have eq : meets (ones (v::vs).length) (packLanes (v::vs)) k =
        2^8 * meets (ones vs.length) (packLanes vs) k + (v+(128-k)) := by
      simp only [meets,packLanes,List.length_cons,ones,List.replicate_succ,Nat.mul_add,
        Nat.add_mul,Nat.one_mul]
      ring
    rw [eq,Nat.testBit_two_pow_mul_add _ (show v+(128-k) < 2^8 by omega)]
    cases i with
    | zero =>
      change (if 7 < 8 then (v+(128-k)).testBit 7 else _) = decide (k ≤ v)
      rw [ite_eq_left (by decide),Nat.testBit_eq_decide_div_mod_eq,show (2:ℕ)^7 = 128 by decide]
      have lt : v+(128-k) < 256 := by omega
      have hu : (v+(128-k)) / 128 ≤ 1 := by omega
      have hm : (v+(128-k)) / 128 % 2 = (v+(128-k)) / 128 := Nat.mod_eq_of_lt (by omega)
      rw [hm]
      apply decide_eq_decide.mpr
      omega
    | succ i =>
      rw [ite_eq_right (show ¬ 8*(i+1)+7 < 8 by omega)]
      rw [show 8*(i+1)+7-8 = 8*i+7 by omega]
      exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) i (by simpa using hi)

private def requirements (f u w : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (weight (f &&& u &&& w), weight (withoutBits (f &&& u) w),
    weight (withoutBits f u &&& w), weight (withoutBits (withoutBits f u) w))

private abbrev FourCounts := ℕ × ℕ × ℕ × ℕ

private def packRows (h : List ℕ) (f u : ℕ) : FourCounts :=
  (packLanes (h.map fun w => (requirements f u w).1),
   packLanes (h.map fun w => (requirements f u w).2.1),
   packLanes (h.map fun w => (requirements f u w).2.2.1),
   packLanes (h.map fun w => (requirements f u w).2.2.2))

private def packedAllowed (r : ℕ) (table req : FourCounts) (edge : Bool) :=
  let caps := meets r table.1 req.1 &&& meets r table.2.1 req.2.1 &&&
    meets r table.2.2.1 req.2.2.1 &&& meets r table.2.2.2 req.2.2.2
  if edge then withoutBits caps (meets r table.1 1) else caps


private theorem at_high (n i : ℕ) (h : i < n) :
    (128 * ones n).testBit (8*i+7) = true := by
  have hmap : packLanes (List.replicate n 0) = 0 := by
    clear h i
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ,packLanes,ih]
  have eq := lane_test (xs := List.replicate n 0)
    (fun x hx => by simp [List.eq_of_mem_replicate hx]) i (by simpa using h) 0 (by decide)
  simpa [meets,hmap,Nat.mul_comm] using eq

private theorem lane_map (xs : List ℕ) (g : ℕ → ℕ) (hg : ∀ u, g u ≤ 16)
    {i : ℕ} (hi : i < xs.length) (k : ℕ) (hk : k ≤ 16) :
    (meets (ones xs.length) (packLanes (xs.map g)) k).testBit (8*i+7) =
      decide (k ≤ g xs[i]) := by
  have ei : i < (xs.map g).length := by simpa using hi
  have bound : ∀ x ∈ xs.map g,x ≤ 16 := by simpa using fun x _ => hg x
  have H := lane_test bound i ei k hk
  rw [List.getElem_map] at H
  simpa only [List.length_map] using H

private theorem packed_index (h : List ℕ) (base corner p q u i : ℕ) (hi : i < h.length)
    (edge : Bool) (ho : fitsPair base corner p q u h[i] edge = true) :
    (packedAllowed (ones h.length) (packRows h corner u) (requirements base p q) edge).testBit
      (8*i+7) = true := by
  simp only [fitsPair, Bool.and_eq_true, decide_eq_true_eq] at ho
  obtain ⟨⟨⟨⟨hed,h11⟩,h10⟩,h01⟩,h00⟩ := ho
  have lt (g : ℕ → ℕ) (k : ℕ) (hk : k ≤ 16) :=
    lane_map h (fun x => weight (g x)) (fun _ => weight_le_16 _) hi k hk
  unfold packedAllowed packRows requirements
  dsimp only
  have ca :
      (meets (ones h.length) (packLanes (h.map (fun w => weight (corner &&& u &&& w))))
        (weight (base &&& p &&& q))).testBit (8*i+7) = true := by
    rw [lt (fun w => corner &&& u &&& w) _ (weight_le_16 _)]
    exact decide_eq_true h11
  have cb :=
    (lt (fun w => withoutBits (corner &&& u) w) _ (weight_le_16 _)).trans (decide_eq_true h10)
  have cc :=
    (lt (fun w => withoutBits corner u &&& w) _ (weight_le_16 _)).trans (decide_eq_true h01)
  have cd := (lt (fun w => withoutBits (withoutBits corner u) w) _ (weight_le_16 _)).trans
    (decide_eq_true h00)
  cases edge with
  | false => simpa only [Bool.false_eq_true, ite_false, Nat.testBit_and,ca,cb,cc,cd]
  | true =>
    have uz : u &&& h[i] = 0 := by simpa using hed
    have ct : corner &&& u &&& h[i] = 0 := by rw [Nat.and_assoc,uz,Nat.and_zero]
    have none :=
      lt (fun w => corner &&& u &&& w) 1 (by decide)
    rw [ct] at none
    simpa only [ite_true,bit_without,Nat.testBit_and,ca,cb,cc,cd, none,Bool.true_and] using
      (show (!(decide (1 ≤ weight 0))) = true by decide)

private def scanBytes (test : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0,_,_ => false
  | n+1,d,offset =>
    d != 0 && ((d.testBit 7 && test offset) || scanBytes test n (d >>> 8) (offset+1))

private theorem scanBytes_mem {test : ℕ → Bool} {n d offset i : ℕ} (hlt : i < n)
    (hb : d.testBit (8*i+7) = true) (hp : test (offset+i) = true) :
    scanBytes test n d offset = true := by
  induction n generalizing d offset i with
  | zero => omega
  | succ n ih =>
    have hd : d ≠ 0 := by rintro rfl; simp at hb
    simp only [scanBytes,Bool.and_eq_true,bne_iff_ne,Bool.or_eq_true]
    refine ⟨hd,?_⟩
    cases i with
    | zero => exact Or.inl ⟨by simpa using hb,by simpa using hp⟩
    | succ i =>
      apply Or.inr
      apply ih (by omega : i<n)
      · simpa only [Nat.testBit_shiftRight,show 8+(8*i+7)=8*(i+1)+7 by omega] using hb
      · simpa only [show offset+1+i=offset+(i+1) by omega] using hp

private def scanBlocks (test : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0,_,_ => false
  | n+1,d,offset =>
    d != 0 && (scanBytes test 8 (d % 2^64) offset || scanBlocks test n (d >>> 64) (offset+8))

private theorem scanBlocks_mem {test : ℕ → Bool} {n d offset i : ℕ} (hlt : i < 8*n)
    (hb : d.testBit (8*i+7) = true) (hp : test (offset+i) = true) :
    scanBlocks test n d offset = true := by
  induction n generalizing d offset i with
  | zero => omega
  | succ n ih =>
    have hd : d ≠ 0 := by rintro rfl; simp at hb
    simp only [scanBlocks,Bool.and_eq_true,bne_iff_ne,Bool.or_eq_true]
    refine ⟨hd,?_⟩
    by_cases small : i < 8
    · apply Or.inl
      apply scanBytes_mem small _ hp
      rw [Nat.testBit_mod_two_pow d 64 (8*i+7)]
      simpa only [show 8*i+7<64 by omega,decide_true,Bool.true_and] using hb
    · apply Or.inr
      apply ih (i:=i-8) (by omega)
      · simpa only [Nat.testBit_shiftRight,show 64+(8*(i-8)+7)=8*i+7 by omega] using hb
      · simpa only [show offset+8+(i-8)=offset+i by omega] using hp

private def packedSolve (choices : ℕ) (allow : ℕ → ℕ → ℕ → ℕ) :
    ℕ → List (ℕ × ℕ) → Bool
  | 0, _ => true
  | _ + 1, [] => true
  | k + 1, (v,d) :: later =>
    scanBlocks (fun i =>
      let next := later.map fun (w,e) => (w,e &&& allow v w i)
      next.all (fun a => a.2 != 0) && packedSolve choices allow k next) ((choices+7)/8) d 0

private theorem packed_solve_pass {choices : ℕ} (allow : ℕ → ℕ → ℕ → ℕ)
    (vs : List ℕ) (idx : ℕ → ℕ) (hi : ∀ v ∈ vs,idx v < choices)
    (passes : ∀ v ∈ vs,∀ w ∈ vs, (allow v w (idx v)).testBit (8*idx w+7) = true) :
    ∀ (k : ℕ) (ds : List (ℕ × ℕ)),
      (∀ e ∈ ds, e.1 ∈ vs ∧ e.2.testBit (8*idx e.1+7) = true) →
      packedSolve choices allow k ds = true := by
  intro k
  induction k with
  | zero => simp [packedSolve]
  | succ k ih =>
    intro ds h
    cases ds with
    | nil => rfl
    | cons entry later =>
      obtain ⟨v,d⟩ := entry
      have ⟨hv,ht⟩ := h (v,d) (by simp)
      apply scanBlocks_mem (i:=idx v) (by have := hi v hv; omega) ht
      simp only [Nat.zero_add,Bool.and_eq_true]
      have step : ∀ e ∈ later.map (fun a : ℕ × ℕ => (a.1,a.2 &&& allow v a.1 (idx v))),
          e.1 ∈ vs ∧ e.2.testBit (8*idx e.1+7) = true := by
        intro e he
        obtain ⟨⟨w,f⟩,hw,rfl⟩ := List.mem_map.mp he
        have ⟨hW,hval⟩ := h (w,f) (List.mem_cons_of_mem _ hw)
        dsimp only at *
        exact ⟨hW,by simp [Nat.testBit_and,hval,passes v hv w hW]⟩
      refine ⟨?_,ih _ step⟩
      apply List.all_eq_true.mpr
      intro e he
      have key := (step e he).2
      by_contra! hzero
      have hz : e.2 = 0 := by simpa using hzero
      simp [hz] at key


private def packedVerify (host : List ℕ) (base _corner : ℕ) (pat nbr : ℕ → ℕ)
    (vertices : List ℕ) (table : ℕ → FourCounts) (init : FourCounts) :=
  let r := ones host.length
  let allow v w i := packedAllowed r (table i)
    (requirements base (pat v) (pat w)) ((nbr v).testBit w)
  let ds := vertices.map fun w => (w,(128*r) &&& packedAllowed r init (requirements base base (pat w)) false)
  packedSolve host.length allow vertices.length ds

theorem packed_verify_pass (host : List ℕ) (base corner : ℕ) (pat nbr : ℕ → ℕ)
    (vertices : List ℕ) (profile : ℕ → ℕ) (f : Fin 16 → Fin 16)
    (hf : Set.InjOn f (sites base)) (hc : ∀ i ∈ sites base, f i ∈ sites corner)
    (hh : ∀ v ∈ vertices, profile v ∈ host)
    (agrees : ∀ v ∈ vertices, ∀ i ∈ sites base, (pat v).testBit i.val =
      (profile v).testBit (f i).val)
    (hed : ∀ v ∈ vertices, ∀ w ∈ vertices, (nbr v).testBit w = true → profile v &&& profile w = 0)
    (table : ℕ → FourCounts) (init : FourCounts)
    (htab : ∀ i (hi : i < host.length), table i = packRows host corner host[i])
    (hini : init = packRows host corner corner) :
    packedVerify host base corner pat nbr vertices table init = true := by
  classical
  have hmc : mapsRegion f base (base,corner) := fun i hi => ⟨hi,hc i hi⟩
  let idx v := host.idxOf (profile v)
  have hi (v) (hm : v ∈ vertices) : idx v < host.length := List.idxOf_lt_length_iff.mpr (hh v hm)
  have heq (v) (hm : v ∈ vertices) : host[idx v]'(hi v hm) = profile v :=
    List.getElem_idxOf (hi v hm)
  unfold packedVerify
  apply packed_solve_pass _ vertices idx hi
  · intro v hv w hw
    rw [htab _ (hi v hv),heq v hv]
    apply packed_index _ _ _ _ _ _ _ (hi w hw)
    rw [heq w hw]
    exact fits_pair hf hmc (agrees v hv) (agrees w hw) (hed v hv w hw)
  · intro e he
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp he
    refine ⟨hw,?_⟩
    simp only [hini,Nat.testBit_and,Bool.and_eq_true]
    refine ⟨at_high _ _ (hi w hw),?_⟩
    apply packed_index _ _ _ _ _ _ _ (hi w hw)
    rw [heq w hw]
    apply fits_pair hf hmc _ (agrees w hw) (by simp)
    intro i hi
    have h0 := hc i hi
    simp only [sites,Finset.mem_filter,Finset.mem_univ,true_and] at hi h0
    rw [hi,h0]


private def classWeightCalc (cs : List ℕ) := weight (cs.foldr (· ||| ·) 0)
private abbrev PackedShape := List ℕ × Array ℕ × ℕ

private def sumSources (bits x : ℕ) (bases : Array ℕ) : ℕ :=
  ((List.range bits).filter x.testBit).foldl (fun a i => a + bases[i]?.getD 0) 0

private def cacheRow (h : PackedShape) (fullWeight u : ℕ) : FourCounts :=
  let q := sumSources 16 u h.2.1
  let v := h.2.2 - q
  let r := ones h.1.length
  let t := weight u
  (q,r*t-q,v,r*(fullWeight-t)-v)

private def cornerTable (h : PackedShape) (cw i : ℕ) : FourCounts :=
  cacheRow h cw (h.1.getD i 0)

private def decodedVertices : ℕ → ℕ → List ℕ
  | 0, _ => []
  | len+1, v => if v = 0 then [] else (v % 16-1)::decodedVertices len (v>>>4)

private def cachedShapes : Array PackedShape := #[([],#[],0),
([],#[],0),
([0,1,2,3,4,5,8,10,12,15],#[0x1000000010001000100,0x1000100000001010000,0x1010000010100000000,0x1010101000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],0x4020201020102010100),
([0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,80,85,128,136,160,170,192,204,240,255],#[0x1000000000000000100000001000000010001000000010001000100,0x1000000010000000000000001000100000001000100000001010000,0x1000100000000000100010000000000000001010000010100000000,0x1000100010001000000000000000000000001010101000000000000,0x1010000000000000101000001010000010100000000000000000000,0x1010000010100000000000001010101000000000000000000000000,0x1010101000000000101010100000000000000000000000000000000,0x1010101010101010000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],0x8040402040202010402020104020201020104020201020102010100),
([0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,80,85,128,136,160,170,192,204,240,255,256,257,512,514,768,771,1024,1028,1280,1285,2048,2056,2560,2570,3072,3084,3840,3855,4096,4112,4352,4369,8192,8224,8704,8738,12288,12336,13056,13107,16384,16448,17408,17476,20480,20560,21760,21845,32768,32896,34816,34952,40960,41120,43520,43690,49152,49344,52224,52428,61440,61680,65280,65535],#[0x1000000000000000000000000000000010000000000000001000000000000000100000001000000000000000100000001000000010001000000000000000100000001000000010001000000010001000100,0x1000000000000000100000000000000000000000000000001000000010000000000000001000000010000000000000001000100000001000000010000000000000001000100000001000100000001010000,0x1000000010000000000000000000000010000000100000000000000000000000000000001000100000000000100010000000000000001000100000000000100010000000000000001010000010100000000,0x1000000010000000100000001000000000000000000000000000000000000000000000001000100010001000000000000000000000001000100010001000000000000000000000001010101000000000000,0x1000100000000000000000000000000010001000000000001000100000000000100010000000000000000000000000000000000000001010000000000000101000001010000010100000000000000000000,0x1000100000000000100010000000000000000000000000001000100010001000000000000000000000000000000000000000000000001010000010100000000000001010101000000000000000000000000,0x1000100010001000000000000000000010001000100010000000000000000000000000000000000000000000000000000000000000001010101000000000101010100000000000000000000000000000000,0x1000100010001000100010001000100000000000000000000000000000000000000000000000000000000000000000000000000000001010101010101010000000000000000000000000000000000000000,0x1010000000000000000000000000000010100000000000001010000000000000101000001010000000000000101000001010000010100000000000000000000000000000000000000000000000000000000,0x1010000000000000101000000000000000000000000000001010000010100000000000001010000010100000000000001010101000000000000000000000000000000000000000000000000000000000000,0x1010000010100000000000000000000010100000101000000000000000000000000000001010101000000000101010100000000000000000000000000000000000000000000000000000000000000000000,0x1010000010100000101000001010000000000000000000000000000000000000000000001010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101000000000000000000000000010101010000000001010101000000000101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101000000000101010100000000000000000000000001010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010000000000000000010101010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000],0x10080804080404020804040204020201080404020402020108040402040202010402020108040402040202010402020104020201020108040402040202010402020104020201020104020201020102010100),
([],#[],0),
([],#[],0),
([0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,80,85,128,136,160,170,192,204,240,255,256,257,272,273,512,514,544,546,768,771,816,819,1024,1028,1088,1092,1280,1285,1360,1365,2048,2056,2176,2184,2560,2570,2720,2730,3072,3084,3264,3276,3840,3855,4080,4095],#[0x1000100000000000000000000000000010001000000000001000100000000000100010001000000000000000100000001000000010001000000010001000100,0x1000100000000000100010000000000000000000000000001000100010001000000000001000000010000000000000001000100000001000100000001010000,0x1000100010001000000000000000000010001000100010000000000000000000000000001000100000000000100010000000000000001010000010100000000,0x1000100010001000100010001000100000000000000000000000000000000000000000001000100010001000000000000000000000001010101000000000000,0x1010000000000000000000000000000010100000000000001010000000000000101000001010000000000000101000001010000010100000000000000000000,0x1010000000000000101000000000000000000000000000001010000010100000000000001010000010100000000000001010101000000000000000000000000,0x1010000010100000000000000000000010100000101000000000000000000000000000001010101000000000101010100000000000000000000000000000000,0x1010000010100000101000001010000000000000000000000000000000000000000000001010101010101010000000000000000000000000000000000000000,0x1010101000000000000000000000000010101010000000001010101000000000101010100000000000000000000000000000000000000000000000000000000,0x1010101000000000101010100000000000000000000000001010101010101010000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010000000000000000010101010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0],0xc080804060404020604040203020201060404020302020106040402030202010302020108040402040202010402020104020201020104020201020102010100),
([],#[],0),
([0,1,2,3,4,5,8,10,12,15,16,17,20,21,32,34,40,42,48,51,60,63,64,65,68,69,128,130,136,138,192,195,204,207,256,257,272,273,320,321,340,341,512,514,544,546,640,642,680,682,768,771,816,819,960,963,1020,1023],#[0x1000100010001000000000000000000010001000100010001000100000000000100010001000100000000000100010001000000010001000100,0x1000100010001000100010001000100000000000000000001000100010001000000000001000100010001000000000001000100000001010000,0x1010000000000000000000000000000010100000000000001010000000000000101000001010000000000000101000001010000010100000000,0x1010000000000000101000000000000000000000000000001010000010100000000000001010000010100000000000001010101000000000000,0x1010000010100000000000000000000010100000101000000000000000000000000000001010101000000000101010100000000000000000000,0x1010000010100000101000001010000000000000000000000000000000000000000000001010101010101010000000000000000000000000000,0x1010101000000000000000000000000010101010000000001010101000000000101010100000000000000000000000000000000000000000000,0x1010101000000000101010100000000000000000000000001010101010101010000000000000000000000000000000000000000000000000000,0x1010101010101010000000000000000010101010101010100000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0],0xa080604060404020504030203020201050403020302020106040402030202010302020106040402030202010302020104020201020102010100),
([],#[],0),
([],#[],0),
([],#[],0),
([],#[],0),
([0,1,2,3,4,5,8,10,12,15,16,17,18,19,32,33,36,37,64,72,80,90,96,108,113,127],#[0x101000000000000010001000100010001000000010001000100,0x100000001000000000000000101000001000100000001010000,0x100010000000000010100000000000001010000010100000000,0x100010001000100000000000000000001010101000000000000,0x101000001010000000000000101010100000000000000000000,0x101010100000000010101010000000000000000000000000000,0x101010101010101000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],0x704040204020201030202010302020104020201020102010100),
([0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,80,85,128,136,160,170,192,204,240,255,256,257,260,261,512,514,520,522,768,771,780,783,1024,1025,1040,1041,2048,2050,2080,2082,3072,3075,3120,3123,4096,4160,4352,4420,5120,5200,5377,5461,8192,8320,8704,8840,10240,10400,10754,10922,12288,12480,13056,13260,15360,15600,16131,16383],#[0x1010000000000000000000000000000010100000000000001000100000000000100010001000100000000000100010001000000000000000100000001000000010001000000010001000100,0x1010000000000000101000000000000000000000000000001000100010001000000000001000100010001000000000001000000010000000000000001000100000001000100000001010000,0x1000000010000000000000000000000010000000100000000000000000000000000000001010000000000000101000001000100000000000100010000000000000001010000010100000000,0x1000000010000000100000001000000000000000000000000000000000000000000000001010000010100000000000001000100010001000000000000000000000001010101000000000000,0x1000100000000000000000000000000010001000000000001010000000000000101000000000000000000000000000001010000000000000101000001010000010100000000000000000000,0x1000100000000000100010000000000000000000000000001010000010100000000000000000000000000000000000001010000010100000000000001010101000000000000000000000000,0x1000100010001000000000000000000010001000100010000000000000000000000000000000000000000000000000001010101000000000101010100000000000000000000000000000000,0x1000100010001000100010001000100000000000000000000000000000000000000000000000000000000000000000001010101010101010000000000000000000000000000000000000000,0x1010000010100000000000000000000010100000101000000000000000000000000000001010101000000000101010100000000000000000000000000000000000000000000000000000000,0x1010000010100000101000001010000000000000000000000000000000000000000000001010101010101010000000000000000000000000000000000000000000000000000000000000000,0x1010101000000000000000000000000010101010000000001010101000000000101010100000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101000000000101010100000000000000000000000001010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010000000000000000010101010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0],0xe080804080404020704040204020201070404020402020106040402030202010302020106040402030202010302020108040402040202010402020104020201020104020201020102010100),
([],#[],0),
([0,1,2,3,4,5,6,7,8,9,16,18,24,27,32,33,40,41,64,68,80,86,96,101,120,127,128,129,136,137,256,258,272,274,384,387,408,411,512,513,544,545,640,641,680,681,1024,1028,1088,1092,1280,1286,1360,1366,1536,1541,1632,1637,1920,1927,2040,2047],#[0x100010001000100000000000000000001000100010001000100010000000000010001000100010000000000010001000100000001000100010001000100,0x100010000000000010001000000000000000000000000000100010001000100000000000100000001000000000000000100010000000101000001010000,0x100010001000100010001000100010000000000000000000000000000000000000000000100010001000100000000000000000000000101010100000000,0x101000000000000000000000000000001010000000000000101000000000000010100000101000000000000010100000101000001010000000000000000,0x101000000000000010100000000000000000000000000000101000001010000000000000101000001010000000000000101010100000000000000000000,0x101000001010000000000000000000001010000010100000000000000000000000000000101010100000000010101010000000000000000000000000000,0x101000001010000010100000101000000000000000000000000000000000000000000000101010101010101000000000000000000000000000000000000,0x101010100000000000000000000000001010101000000000101010100000000010101010000000000000000000000000000000000000000000000000000,0x101010100000000010101010000000000000000000000000101010101010101000000000000000000000000000000000000000000000000000000000000,0x101010101010101000000000000000001010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000,0x101010101010101010101010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0],0xb08070406040402060404020302020105040302030202010604040203020201030202010704040204020201030202010402020102010302020102010100),
([],#[],0),
([],#[],0),
([],#[],0),
([0,1,2,3,4,5,8,10,12,15,16,17,20,21,32,34,48,51,64,72,80,92,96,106,112,127,128,129,132,133,144,145,148,149,256,258,288,290,384,387,432,435,512,520,576,584,640,652,720,732,768,778,864,874,896,911,1008,1023],#[0x1000100000000000000000000000000010001000000000001000100010001000100000000000000010000000100010001000000010001000100,0x1000100010001000000000000000000010001000100010000000000000000000100010000000000010001000000000001000100000001010000,0x1000100000000000100010000000000000000000000000001010000010100000100000001000000000000000101000001010000010100000000,0x1000100010001000100010001000100000000000000000000000000000000000100010001000100000000000000000001010101000000000000,0x1010000000000000101000000000000010100000000000001010101000000000101000001010000010100000101010100000000000000000000,0x1010000010100000000000000000000010100000101000000000000000000000101010100000000010101010000000000000000000000000000,0x1010000010100000101000001010000000000000000000000000000000000000101010101010101000000000000000000000000000000000000,0x1010101000000000101010100000000010101010000000001010101010101010000000000000000000000000000000000000000000000000000,0x1010101010101010000000000000000010101010101010100000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0],0xa060703060404020604040203020201060404020302020104030302030202010703040204020201040202010302020104020201020102010100),
([],#[],0),
([0,1,2,3,4,5,8,10,12,15,16,17,20,21,32,34,40,42,48,51,60,63,64,65,80,81,128,130,160,162,192,195,240,243,256,260,272,276,320,325,336,341,512,520,544,552,640,650,672,682,768,780,816,828,960,975,1008,1023],#[0x1000100000000000000000000000000010001000000000001000100000000000100010001000100000000000100010001000000010001000100,0x1000100000000000100010000000000000000000000000001000100010001000000000001000100010001000000000001000100000001010000,0x1000100010001000000000000000000010001000100010000000000000000000000000001010000000000000101000001010000010100000000,0x1000100010001000100010001000100000000000000000000000000000000000000000001010000010100000000000001010101000000000000,0x1010000010100000000000000000000010100000101000001010000000000000101000001010101000000000101010100000000000000000000,0x1010000010100000101000001010000000000000000000001010000010100000000000001010101010101010000000000000000000000000000,0x1010101000000000000000000000000010101010000000001010101000000000101010100000000000000000000000000000000000000000000,0x1010101000000000101010100000000000000000000000001010101010101010000000000000000000000000000000000000000000000000000,0x1010101010101010000000000000000010101010101010100000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0],0xa060804060404020503040203020201050304020302020106040402030202010302020106040402030202010302020104020201020102010100),
([],#[],0),
([],#[],0),
([],#[],0),
([0,1,2,3,4,5,8,10,12,15,16,17,18,19,32,33,36,37,64,72,80,90,96,108,113,127,128,129,130,131,256,257,260,261,512,520,640,650,768,780,897,911,1024,1025,1040,1041,1152,1153,1170,1171,2048,2049,2080,2081,2304,2305,2340,2341,4096,4160,4608,4680,5120,5200,5760,5850,6144,6240,6912,7020,7169,7281,8065,8191],#[0x101010100000000000000000000000001000100010001000100010001000100010100000000000001000100010001000101000000000000010001000100010001000000010001000100,0x100000000000000010000000000000000000000000000000101000000000000010000000100000000000000010100000100000001000000000000000101000001000100000001010000,0x100000001000000000000000000000001010000000000000000000000000000010001000000000001010000000000000100010000000000010100000000000001010000010100000000,0x100000001000000010000000100000000000000000000000000000000000000010001000100010000000000000000000100010001000100000000000000000001010101000000000000,0x100010000000000010001000000000000000000000000000101000001010000000000000000000000000000000000000101000001010000000000000101010100000000000000000000,0x100010001000100000000000000000001010000010100000000000000000000000000000000000000000000000000000101010100000000010101010000000000000000000000000000,0x100010001000100010001000100010000000000000000000000000000000000000000000000000000000000000000000101010101010101000000000000000000000000000000000000,0x101000000000000010100000000000000000000000000000101010100000000010100000101000000000000010101010000000000000000000000000000000000000000000000000000,0x101000001010000000000000000000001010101000000000000000000000000010101010000000001010101000000000000000000000000000000000000000000000000000000000000,0x101000001010000010100000101000000000000000000000000000000000000010101010101010100000000000000000000000000000000000000000000000000000000000000000000,0x101010100000000010101010000000000000000000000000101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x101010101010101000000000000000001010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x101010101010101010101010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0],0xd07070408040402080404020402020105040302030202010504030203020201070404020402020103020201030202010704040204020201030202010302020104020201020102010100),
([],#[],0),
([0,1,2,3,4,5,6,7,8,9,16,18,24,27,32,36,40,45,64,68,80,86,96,100,120,127,128,129,130,131,132,133,134,135,256,257,264,265,512,514,528,530,768,771,792,795,1024,1056,1152,1188,1280,1320,1409,1453,2048,2112,2176,2244,2560,2640,2690,2774,3072,3168,3200,3300,3840,3960,3971,4095],#[0x1010000000000000000000000000000010100000000000001000100000000000100010001000100010001000100000000000000010000000100000001000100010001000100,0x1010000000000000101000000000000000000000000000001000100010001000000000001010000010100000100000001000000000000000100010000000101000001010000,0x1000000010000000100000001000000010000000100000000000000000000000000000001010101000000000100010001000100010001000000000000000101010100000000,0x1000100000000000000000000000000010001000000000001010000000000000101000000000000000000000101000000000000010100000101000001010000000000000000,0x1000100000000000100010000000000000000000000000001010000010100000000000000000000000000000101000001010000000000000101010100000000000000000000,0x1000100010001000000000000000000010001000100010000000000000000000000000000000000000000000101010100000000010101010000000000000000000000000000,0x1000100010001000100010001000100000000000000000000000000000000000000000000000000000000000101010101010101000000000000000000000000000000000000,0x1010000010100000101000001010000010100000101000000000000000000000000000001010101010101010000000000000000000000000000000000000000000000000000,0x1010101000000000000000000000000010101010000000001010101000000000101010100000000000000000000000000000000000000000000000000000000000000000000,0x1010101000000000101010100000000000000000000000001010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010000000000000000010101010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0],0xc070804060304020704040204020201070404020402020106040402030202010302020104030302030202010704030204020201040202010402020102010302020102010100),
([],#[],0),
([],#[],0),
([],#[],0),
([0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,72,76,80,85,96,106,112,127,128,129,132,133,256,258,264,266,384,387,396,399,512,513,528,529,1024,1026,1056,1058,1536,1539,1584,1587,2048,2112,2176,2244,2304,2376,2432,2508,2560,2640,2689,2773,3072,3168,3330,3434,3584,3696,3971,4095],#[0x1010000000000000101000000000000000000000100010000000000010001000100010000000000010001000100000001000000000001000000010001000000010001000100,0x1010000010100000000000000000000000000000100010001000100000000000100010001000100000000000100010000000000000001000100000001000100000001010000,0x1000000000000000100000001000000010000000000000000000000000000000101000000000000010100000100000001000100010000000000000001010000010100000000,0x1000000010000000000000001000100000000000000000000000000000000000101000001010000000000000100010000000101000000000000000001010101000000000000,0x1000100000000000100010000000000000000000101000000000000010100000000000000000000000000000101000001010000000001010000010100000000000000000000,0x1000100010001000000000000000000000000000101000001010000000000000000000000000000000000000101010100000000000001010101000000000000000000000000,0x1000100010001000100010001000100010001000000000000000000000000000000000000000000000000000101010101010101010100000000000000000000000000000000,0x1010000000000000101000001010000010100000000000000000000000000000101010100000000010101010000000000000000000000000000000000000000000000000000,0x1010000010100000000000001010101000000000000000000000000000000000101010101010101000000000000000000000000000000000000000000000000000000000000,0x1010101000000000101010100000000000000000101010100000000010101010000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010000000000000000000000000101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010101010101010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0],0xc070603070404020704040206030402040202010604040203020201030202010604040203020201030202010703040204020302020104020201020104020201020102010100),
([],#[],0),
([],#[],0),
([0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,80,85,128,136,160,170,192,204,240,255,256,257,258,259,512,513,516,517,1024,1032,1280,1290,1536,1548,1793,1807,2048,2049,2064,2065,4096,4128,4352,4386,6144,6192,6401,6451,8192,8256,8704,8772,10240,10320,10753,10837,16384,16512,17408,17544,20480,20640,21760,21930,24576,24768,26112,26316,30720,30960,32513,32767],#[0x101000000000000000000000000000001010000000000000101000000000000010001000101000000000000010001000100010001000000000000000100000001000000010001000000010001000100,0x100000000000000010000000000000000000000000000000100000001000000000000000100000001000000000000000101000001000000010000000000000001000100000001000100000001010000,0x100000001000000000000000000000001000000010000000000000000000000000000000100010000000000010100000000000001000100000000000100010000000000000001010000010100000000,0x100000001000000010000000100000000000000000000000000000000000000000000000100010001000100000000000000000001000100010001000000000000000000000001010101000000000000,0x100010000000000000000000000000001000100000000000100010000000000010100000000000000000000000000000000000001010000000000000101000001010000010100000000000000000000,0x100010000000000010001000000000000000000000000000100010001000100000000000000000000000000000000000000000001010000010100000000000001010101000000000000000000000000,0x100010001000100000000000000000001000100010001000000000000000000000000000000000000000000000000000000000001010101000000000101010100000000000000000000000000000000,0x100010001000100010001000100010000000000000000000000000000000000000000000000000000000000000000000000000001010101010101010000000000000000000000000000000000000000,0x101000000000000010100000000000000000000000000000101000001010000000000000101000001010000000000000101010100000000000000000000000000000000000000000000000000000000,0x101000001010000000000000000000001010000010100000000000000000000000000000101010100000000010101010000000000000000000000000000000000000000000000000000000000000000,0x101000001010000010100000101000000000000000000000000000000000000000000000101010101010101000000000000000000000000000000000000000000000000000000000000000000000000,0x101010100000000000000000000000001010101000000000101010100000000010101010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x101010100000000010101010000000000000000000000000101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x101010101010101000000000000000001010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x101010101010101010101010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0],0xf08080408040402080404020402020107040402040202010704040204020201030202010704040204020201030202010302020108040402040202010402020104020201020104020201020102010100),
([0,1,2,3,4,5,6,7,8,9,16,18,24,27,32,36,40,45,48,54,56,63,64,65,72,73,128,130,144,146,192,195,216,219,256,257,264,265,320,321,328,329,512,516,544,548,640,646,688,694,768,773,808,813,960,967,1016,1023],#[0x1000100010001000000000000000000010001000100010001000100000000000100010001000000010000000100000001000100010001000100,0x1000100000000000100010000000000000000000000000001000100010001000000000001000100000000000100010000000101000001010000,0x1000100010001000100010001000100000000000000000000000000000000000000000001000100010001000000000000000101010100000000,0x1010000010100000000000000000000010100000101000001010000000000000101000001010000010100000101000001010000000000000000,0x1010000000000000101000000000000000000000000000001010000010100000000000001010101000000000101010100000000000000000000,0x1010000010100000101000001010000000000000000000000000000000000000000000001010101010101010000000000000000000000000000,0x1010101000000000000000000000000010101010000000001010101000000000101010100000000000000000000000000000000000000000000,0x1010101000000000101010100000000000000000000000001010101010101010000000000000000000000000000000000000000000000000000,0x1010101010101010000000000000000010101010101010100000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0],0xa070704060404020604040203020201040303020302020106040402030202010302020106030402040202010402020102010302020102010100),
([],#[],0),
([0,1,2,3,4,5,8,10,12,15,16,17,20,21,32,34,48,51,64,72,80,92,96,106,112,127,128,129,144,145,256,258,288,290,384,387,432,435,512,516,528,532,640,645,656,661,1024,1032,1088,1096,1280,1290,1376,1386,1536,1548,1616,1628,1920,1935,2032,2047],#[0x100010000000000000000000000000001000100000000000100010000000000010001000100000000000000010000000100010001000000010001000100,0x100010000000000010001000000000000000000000000000100010001000100000000000100010000000000010001000000000001000100000001010000,0x100010001000100000000000000000001000100010001000000000000000000000000000100000001000000000000000101000001010000010100000000,0x100010001000100010001000100010000000000000000000000000000000000000000000100010001000100000000000000000001010101000000000000,0x101000001010000000000000000000001010000010100000101000000000000010100000101000001010000010100000101010100000000000000000000,0x101000000000000010100000000000000000000000000000101000001010000000000000101010100000000010101010000000000000000000000000000,0x101000001010000010100000101000000000000000000000000000000000000000000000101010101010101000000000000000000000000000000000000,0x101010100000000000000000000000001010101000000000101010100000000010101010000000000000000000000000000000000000000000000000000,0x101010100000000010101010000000000000000000000000101010101010101000000000000000000000000000000000000000000000000000000000000,0x101010101010101000000000000000001010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000,0x101010101010101010101010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0],0xb07080406040402060404020302020105030402030202010604040203020201030202010703040204020201040202010302020104020201020102010100),
([],#[],0),
([],#[],0),
([0,1,2,3,4,5,8,10,12,15,16,17,18,19,32,33,36,37,64,72,80,90,96,108,113,127,128,129,130,131,144,145,146,147,256,257,260,261,288,289,292,293,512,520,576,584,640,650,720,730,768,780,864,876,897,911,1009,1023],#[0x1010101000000000000000000000000010001000100010001000100010001000101000000000000010001000100010001000000010001000100,0x1000100000000000100010000000000000000000000000001010000010100000100000001000000000000000101000001000100000001010000,0x1000100010001000000000000000000010100000101000000000000000000000100010000000000010100000000000001010000010100000000,0x1000100010001000100010001000100000000000000000000000000000000000100010001000100000000000000000001010101000000000000,0x1010000000000000101000000000000000000000000000001010101000000000101000001010000000000000101010100000000000000000000,0x1010000010100000000000000000000010101010000000000000000000000000101010100000000010101010000000000000000000000000000,0x1010000010100000101000001010000000000000000000000000000000000000101010101010101000000000000000000000000000000000000,0x1010101000000000101010100000000000000000000000001010101010101010000000000000000000000000000000000000000000000000000,0x1010101010101010000000000000000010101010101010100000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0,0x0,0x0],0xa070704060404020604040203020201040303020302020104030302030202010704040204020201030202010302020104020201020102010100),
([0,1,2,3,4,5,8,10,12,15,16,17,18,19,32,33,36,37,64,72,80,90,96,108,113,127,128,129,132,133,256,258,264,266,384,387,396,399,512,513,514,515,528,529,530,531,1024,1025,1056,1057,1152,1153,1188,1189,2048,2112,2304,2376,2560,2640,2818,2906,3072,3168,3456,3564,3585,3697,3971,4095],#[0x1010101000000000000000000000000010001000100010001000100010001000100010000000000010001000101000000000000010001000100010001000000010001000100,0x1010000000000000101000000000000000000000000000001010000010100000100010001000100000000000100000001000000000000000101000001000100000001010000,0x1000000010000000000000000000000010100000000000000000000000000000101000000000000010100000100010000000000010100000000000001010000010100000000,0x1000000010000000100000001000000000000000000000000000000000000000101000001010000000000000100010001000100000000000000000001010101000000000000,0x1000100000000000100010000000000000000000000000001010101000000000000000000000000000000000101000001010000000000000101010100000000000000000000,0x1000100010001000000000000000000010100000101000000000000000000000000000000000000000000000101010100000000010101010000000000000000000000000000,0x1000100010001000100010001000100000000000000000000000000000000000000000000000000000000000101010101010101000000000000000000000000000000000000,0x1010000010100000000000000000000010101010000000000000000000000000101010100000000010101010000000000000000000000000000000000000000000000000000,0x1010000010100000101000001010000000000000000000000000000000000000101010101010101000000000000000000000000000000000000000000000000000000000000,0x1010101000000000101010100000000000000000000000001010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010000000000000000010101010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0],0xc070704080404020704040204020201050403020302020104030302030202010604040203020201030202010704040204020201030202010302020104020201020102010100),
([],#[],0),
([0,1,2,3,4,5,8,10,12,15,16,17,20,21,32,34,48,51,64,68,72,76,96,106,116,127,128,129,132,133,256,258,264,266,384,387,396,399,512,513,528,529,640,641,660,661,1024,1026,1056,1058,1536,1539,1584,1587,2048,2112,2176,2244,2304,2376,2432,2508,3072,3168,3330,3434,3712,3828,3971,4095],#[0x1010000000000000000000000000000010001000000000001000100010001000100010000000000010001000100000000000000010000000100010001000000010001000100,0x1010000010100000000000000000000010001000100010000000000000000000100010001000100000000000100010000000000010001000000000001000100000001010000,0x1000100000000000100000001000000000000000000000001010000000000000101000000000000010100000101000001000100000000000101000001010000010100000000,0x1000000010000000100010000000000000000000000000000000000000000000101000001010000000000000100010001010000000000000000000001010101000000000000,0x1000100000000000000000000000000010100000000000001010000010100000000000000000000000000000101000000000000010100000101010100000000000000000000,0x1000100010001000000000000000000010100000101000000000000000000000000000000000000000000000101010100000000010101010000000000000000000000000000,0x1000100010001000100010001000100000000000000000000000000000000000000000000000000000000000101010101010101000000000000000000000000000000000000,0x1010101000000000101000001010000000000000000000001010101000000000101010100000000010101010000000000000000000000000000000000000000000000000000,0x1010000010100000101010100000000000000000000000000000000000000000101010101010101000000000000000000000000000000000000000000000000000000000000,0x1010101000000000000000000000000010101010000000001010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010000000000000000010101010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0,0x0],0xc070804070404020603040204020201060404020302020105040302030202010604040203020201030202010704040203020201040202010302020104020201020102010100),
([],#[],0),
([],#[],0),
([],#[],0),
([],#[],0),
([0,1,2,3,4,5,6,7,8,9,16,18,24,27,32,36,40,45,64,68,80,86,96,100,120,127,128,129,132,133,256,258,260,262,384,387,388,391,512,513,520,521,1024,1026,1040,1042,1536,1539,1560,1563,2048,2080,2176,2212,2560,2600,2689,2733,4096,4160,4352,4420,5120,5200,5378,5462,6144,6240,6528,6628,7680,7800,8067,8191],#[0x101000000000000000000000000000001010000000000000100010000000000010001000100010000000000010001000100000000000000010000000100000001000100010001000100,0x101000000000000010100000000000000000000000000000100010001000100000000000100010001000100000000000100000001000000000000000100010000000101000001010000,0x100000001000000010000000100000001000000010000000000000000000000000000000101000001010000010100000100010001000100010001000000000000000101010100000000,0x100010000000000000000000000000001000100000000000101000000000000010100000000000000000000000000000101000000000000010100000101000001010000000000000000,0x100010000000000010001000000000000000000000000000101000001010000000000000000000000000000000000000101000001010000000000000101010100000000000000000000,0x100010001000100000000000000000001000100010001000000000000000000000000000000000000000000000000000101010100000000010101010000000000000000000000000000,0x100010001000100010001000100010000000000000000000000000000000000000000000000000000000000000000000101010101010101000000000000000000000000000000000000,0x101000001010000000000000000000001010000010100000000000000000000000000000101010100000000010101010000000000000000000000000000000000000000000000000000,0x101000001010000010100000101000000000000000000000000000000000000000000000101010101010101000000000000000000000000000000000000000000000000000000000000,0x101010100000000000000000000000001010101000000000101010100000000010101010000000000000000000000000000000000000000000000000000000000000000000000000000,0x101010100000000010101010000000000000000000000000101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x101010101010101000000000000000001010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x101010101010101010101010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0],0xd08080407040402070404020402020107040402040202010604040203020201030202010503040203020201030202010704030204020201040202010402020102010302020102010100),
([],#[],0),
([],#[],0),
([0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,72,76,80,85,96,106,112,127,128,129,132,133,256,258,264,266,384,387,396,399,512,513,528,529,1024,1026,1056,1058,1536,1539,1584,1587,2048,2112,2176,2244,2560,2640,2689,2773,4096,4160,4352,4424,5120,5216,5378,5482,6144,6208,6528,6604,7680,7792,8067,8191],#[0x101000000000000000000000000000001010000000000000100010000000000010001000100010000000000010001000100000001000000000001000000010001000000010001000100,0x101000000000000010100000000000000000000000000000100010001000100000000000100010001000100000000000100010000000000000001000100000001000100000001010000,0x100000001000000000000000000000001000000010000000000000000000000000000000101000000000000010100000100000001000100010000000000000001010000010100000000,0x100000001000000010000000100000000000000000000000000000000000000000000000101000001010000000000000100010000000101000000000000000001010101000000000000,0x100010000000000000000000000000001000100000000000101000000000000010100000000000000000000000000000101000001010000000001010000010100000000000000000000,0x100010000000000010001000000000000000000000000000101000001010000000000000000000000000000000000000101010100000000000001010101000000000000000000000000,0x100010001000100010001000100010001000100010001000000000000000000000000000000000000000000000000000101010101010101010100000000000000000000000000000000,0x101000001010000000000000000000001010000010100000000000000000000000000000101010100000000010101010000000000000000000000000000000000000000000000000000,0x101000001010000010100000101000000000000000000000000000000000000000000000101010101010101000000000000000000000000000000000000000000000000000000000000,0x101010100000000000000000000000001010101000000000101010100000000010101010000000000000000000000000000000000000000000000000000000000000000000000000000,0x101010100000000010101010000000000000000000000000101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x101010101010101000000000000000001010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x101010101010101010101010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x0,0x0,0x0],0xd08070407040302070404020402020107040402040202010604040203020201030202010604040203020201030202010703040204020302020104020201020104020201020102010100),
([],#[],0),
([],#[],0),
([],#[],0)]
def andCatalogue : Array (ℕ × List ℕ) := #[(2,[6,5,3]),
(2,[4,8,1,2]),
(2,[12,8,1,3]),
(3,[20,8,17,2,5]),
(3,[20,24,17,2,7]),
(3,[20,24,17,18,15]),
(3,[12,24,17,3,6]),
(3,[8,16,32,1,2,4]),
(3,[40,16,32,1,2,5]),
(3,[40,48,32,1,2,7]),
(3,[56,16,32,1,35,21]),
(3,[40,48,16,1,6,3]),
(3,[24,40,48,3,5,6]),
(4,[20,40,17,34,5,10]),
(4,[52,40,17,34,5,11]),
(4,[72,16,32,65,2,4,9]),
(4,[72,80,32,65,2,4,11]),
(4,[72,80,96,65,2,4,15]),
(4,[72,80,32,65,66,4,27]),
(4,[72,80,96,65,66,4,31]),
(4,[72,80,96,65,66,68,63]),
(4,[104,80,32,65,2,5,11]),
(4,[40,16,96,65,2,5,12]),
(4,[40,80,96,65,2,5,14]),
(4,[40,80,32,1,66,5,18]),
(4,[104,80,32,1,66,5,19]),
(4,[40,80,96,1,66,5,22]),
(4,[104,80,32,65,66,5,27]),
(4,[40,80,96,65,66,5,30]),
(4,[104,80,32,1,66,69,51]),
(4,[40,48,96,65,66,7,28]),
(4,[24,48,96,65,3,6,12]),
(4,[88,48,96,65,3,6,13]),
(4,[88,48,96,1,67,6,21]),
(4,[88,48,96,1,3,70,37]),
(4,[88,48,96,65,3,70,45]),
(4,[88,48,96,33,67,14,21]),
(4,[16,32,64,128,1,2,4,8]),
(4,[144,32,64,128,1,2,4,9]),
(4,[144,160,64,128,1,2,4,11]),
(4,[144,160,192,128,1,2,4,15]),
(4,[80,160,64,128,1,2,5,10]),
(4,[208,160,64,128,1,2,5,11]),
(4,[80,160,192,128,1,2,5,14]),
(4,[208,32,64,128,1,2,133,73]),
(4,[208,160,64,128,1,2,133,75]),
(4,[80,96,64,128,129,130,7,56]),
(4,[144,32,192,64,1,2,12,5]),
(4,[144,160,192,64,1,2,12,7]),
(4,[176,96,192,128,1,3,6,13]),
(4,[176,96,64,128,1,3,134,73]),
(4,[176,32,192,64,1,131,12,37]),
(4,[144,96,160,64,1,6,10,5]),
(4,[16,96,160,192,1,6,10,12]),
(4,[144,96,160,192,1,6,10,13]),
(4,[48,80,160,192,3,5,10,12]),
(4,[72,80,96,129,130,132,7,56]),
(5,[72,144,32,65,130,4,9,18]),
(5,[200,144,32,65,130,4,9,19]),
(5,[72,144,160,65,130,4,9,22]),
(5,[200,144,160,65,130,4,9,23]),
(5,[72,144,160,65,130,132,9,54]),
(5,[200,144,160,65,130,132,9,55]),
(5,[72,80,160,65,130,132,11,52]),
(5,[200,80,160,65,130,132,11,53]),
(5,[72,208,160,65,130,132,11,54]),
(5,[72,208,160,65,2,132,139,102]),
(5,[104,208,160,65,130,133,11,54]),
(5,[168,144,96,193,130,5,12,27]),
(5,[168,208,96,65,130,5,14,19]),
(5,[168,208,96,65,130,133,14,51]),
(5,[104,208,160,1,66,133,19,38]),
(5,[168,208,96,129,66,5,22,11]),
(5,[168,208,64,33,130,9,6,19]),
(5,[40,80,192,33,130,9,6,20]),
(5,[168,80,192,33,130,9,6,21]),
(5,[168,208,128,33,66,9,18,7]),
(5,[152,48,224,65,131,6,12,21]),
(5,[88,176,96,193,3,134,13,42]),
(5,[272,32,64,128,257,2,4,8,17]),
(5,[272,288,64,128,257,2,4,8,19]),
(5,[272,288,320,128,257,2,4,8,23]),
(5,[272,288,320,384,257,2,4,8,31]),
(5,[272,288,64,128,257,258,4,8,51]),
(5,[272,288,320,128,257,258,4,8,55]),
(5,[272,288,320,384,257,258,4,8,63]),
(5,[272,288,320,128,257,258,260,8,119]),
(5,[272,288,320,384,257,258,260,8,127]),
(5,[272,288,320,384,257,258,260,264,255]),
(5,[400,288,64,128,257,2,4,9,19]),
(5,[400,288,320,128,257,2,4,9,23]),
(5,[144,32,64,384,257,2,4,9,24]),
(5,[144,288,64,384,257,2,4,9,26]),
(5,[144,288,320,384,257,2,4,9,30]),
(5,[144,288,64,128,1,258,4,9,34]),
(5,[400,288,64,128,1,258,4,9,35]),
(5,[144,288,320,128,1,258,4,9,38]),
(5,[400,288,320,128,1,258,4,9,39]),
(5,[144,288,64,384,1,258,4,9,42]),
(5,[144,288,320,384,1,258,4,9,46]),
(5,[400,288,64,128,257,258,4,9,51]),
(5,[400,288,320,128,257,258,4,9,55]),
(5,[144,288,64,384,257,258,4,9,58]),
(5,[144,288,320,384,257,258,4,9,62]),
(5,[144,288,320,128,1,258,260,9,102]),
(5,[400,288,320,128,1,258,260,9,103]),
(5,[144,288,320,384,1,258,260,9,110]),
(5,[400,288,320,128,257,258,260,9,119]),
(5,[144,288,320,384,257,258,260,9,126]),
(5,[400,288,64,128,1,258,4,265,163]),
(5,[400,288,320,128,1,258,4,265,167]),
(5,[400,288,320,128,1,258,260,265,231]),
(5,[144,160,320,384,257,2,4,11,28]),
(5,[400,160,320,128,257,258,4,11,53]),
(5,[144,160,64,384,257,258,4,11,56]),
(5,[144,160,320,384,257,258,4,11,60]),
(5,[144,160,320,384,1,2,260,11,76]),
(5,[144,160,320,128,257,2,260,11,84]),
(5,[400,160,320,128,257,2,260,11,85]),
(5,[144,416,320,128,257,2,260,11,86]),
(5,[144,160,320,384,257,2,260,11,92]),
(5,[144,160,320,128,257,258,260,11,116]),
(5,[400,160,320,128,257,258,260,11,117]),
(5,[144,160,320,384,257,258,260,11,124]),
(5,[400,160,320,128,1,2,260,267,197]),
(5,[144,160,320,384,1,2,260,267,204]),
(5,[400,160,192,128,257,258,260,15,113]),
(5,[144,160,192,384,257,258,260,15,120]),
(5,[144,288,320,256,129,2,4,17,14]),
(5,[400,288,320,256,129,2,4,17,15]),
(5,[400,160,320,256,129,258,4,19,45]),
(5,[336,416,64,128,257,2,5,10,19]),
(5,[80,160,320,128,257,2,5,10,20]),
(5,[80,416,320,128,257,2,5,10,22]),
(5,[80,160,320,384,257,2,5,10,28]),
(5,[336,416,64,128,257,258,5,10,51]),
(5,[80,416,320,128,257,258,5,10,54]),
(5,[80,160,320,384,257,258,5,10,60]),
(5,[336,416,64,128,1,258,261,10,99]),
(5,[336,160,64,384,1,258,261,10,105]),
(5,[208,416,320,128,257,258,5,11,54]),
(5,[208,160,320,384,257,258,5,11,60]),
(5,[208,416,320,128,1,258,261,11,102]),
(5,[336,288,192,128,257,2,5,12,19]),
(5,[80,288,448,128,257,2,5,12,22]),
(5,[80,32,192,384,257,2,5,12,24]),
(5,[336,32,192,384,257,2,5,12,25]),
(5,[80,288,192,384,257,2,5,12,26]),
(5,[336,288,192,384,257,2,5,12,27]),
(5,[336,288,192,128,1,258,5,12,35]),
(5,[80,288,448,128,1,258,5,12,38]),
(5,[80,288,192,384,1,258,5,12,42]),
(5,[336,288,192,384,1,258,5,12,43]),
(5,[336,288,192,128,257,258,5,12,51]),
(5,[80,288,448,128,257,258,5,12,54]),
(5,[80,288,192,384,257,258,5,12,58]),
(5,[336,288,192,384,257,258,5,12,59]),
(5,[80,288,448,128,1,2,261,12,70]),
(5,[336,32,192,384,1,2,261,12,73]),
(5,[336,288,192,384,1,2,261,12,75]),
(5,[336,288,192,128,1,258,261,12,99]),
(5,[80,288,448,128,1,258,261,12,102]),
(5,[336,288,192,384,1,258,261,12,107]),
(5,[336,32,192,384,1,2,5,268,137]),
(5,[336,288,192,384,1,2,5,268,139]),
(5,[336,32,192,384,257,2,5,268,153]),
(5,[336,288,192,384,257,2,5,268,155]),
(5,[336,288,192,128,1,258,5,268,163]),
(5,[336,288,192,384,1,258,5,268,171]),
(5,[336,288,192,384,257,258,5,268,187]),
(5,[336,416,192,128,257,2,5,14,19]),
(5,[336,416,192,128,1,258,5,14,35]),
(5,[336,160,192,384,1,258,5,14,41]),
(5,[336,160,192,128,257,258,5,14,49]),
(5,[336,416,192,128,257,258,5,14,51]),
(5,[80,160,192,384,257,258,5,14,56]),
(5,[336,160,192,384,257,258,5,14,57]),
(5,[336,160,192,384,1,2,261,14,73]),
(5,[80,416,192,128,1,258,261,14,98]),
(5,[336,416,192,128,1,258,261,14,99]),
(5,[336,160,192,384,1,258,261,14,105]),
(5,[336,416,192,128,257,2,5,270,147]),
(5,[208,416,64,256,129,2,261,19,74]),
(5,[336,288,192,256,385,2,5,20,27]),
(5,[336,416,192,256,129,2,5,22,11]),
(5,[336,416,192,256,129,2,261,22,75]),
(5,[336,160,192,256,129,258,261,22,105]),
(5,[336,288,192,384,129,2,5,28,11]),
(5,[336,32,192,384,129,2,261,28,73]),
(5,[336,288,192,384,129,2,261,28,75]),
(5,[336,160,192,256,1,130,261,38,73]),
(5,[80,416,192,256,1,130,261,38,74]),
(5,[336,416,192,256,1,130,261,38,75]),
(5,[208,288,320,384,257,2,133,73,30]),
(5,[208,288,320,384,1,258,133,73,46]),
(5,[464,288,64,128,257,258,133,73,51]),
(5,[208,288,320,384,257,258,133,73,62]),
(5,[208,416,320,128,257,258,133,75,54]),
(5,[208,160,320,384,257,258,133,75,60]),
(5,[80,96,320,384,129,130,263,312,204]),
(5,[144,160,192,320,257,258,12,7,56]),
(5,[400,160,192,320,257,258,12,7,57]),
(5,[144,160,192,320,257,2,268,7,88]),
(5,[400,160,192,320,257,2,268,7,89]),
(5,[144,416,192,320,257,2,268,7,90]),
(5,[400,160,192,64,257,258,268,7,113]),
(5,[144,160,448,64,257,258,268,7,116]),
(5,[144,160,192,320,257,258,268,7,120]),
(5,[400,160,192,320,257,258,268,7,121]),
(5,[144,288,192,320,257,2,396,69,90]),
(5,[336,416,128,256,65,2,17,6,11]),
(5,[80,416,128,256,65,2,17,262,138]),
(5,[336,416,128,256,65,2,17,262,139]),
(5,[80,288,384,128,65,2,17,12,6]),
(5,[304,96,448,128,257,3,6,12,21]),
(5,[48,96,192,384,257,3,6,12,24]),
(5,[304,96,192,384,257,3,6,12,25]),
(5,[48,352,192,384,257,3,6,12,26]),
(5,[304,96,448,128,1,259,6,12,37]),
(5,[304,96,192,384,1,259,6,12,41]),
(5,[48,352,192,384,1,259,6,12,42]),
(5,[304,96,448,128,1,3,262,12,69]),
(5,[304,96,192,384,1,3,262,12,73]),
(5,[48,352,192,384,1,3,262,12,74]),
(5,[304,96,192,128,257,3,262,12,81]),
(5,[304,96,448,128,257,3,262,12,85]),
(5,[304,96,192,384,257,3,262,12,89]),
(5,[48,352,192,384,257,3,262,12,90]),
(5,[304,96,192,384,1,3,6,268,137]),
(5,[304,96,448,128,257,3,6,268,149]),
(5,[304,96,192,384,257,3,6,268,153]),
(5,[304,96,448,128,1,259,6,268,165]),
(5,[176,352,192,384,1,3,262,13,74]),
(5,[176,352,192,384,257,3,262,13,90]),
(5,[304,96,448,256,129,3,6,20,13]),
(5,[304,96,192,384,129,3,262,28,73]),
(5,[304,160,448,64,129,259,12,22,37]),
(5,[304,160,192,320,129,259,12,22,41]),
(5,[176,288,448,64,257,131,268,37,86]),
(5,[432,32,192,320,257,131,268,37,89]),
(5,[176,288,192,320,257,131,268,37,90]),
(5,[304,160,448,64,1,259,140,70,37]),
(5,[304,160,192,320,1,259,140,70,41]),
(5,[272,96,160,448,1,262,10,12,41]),
(5,[272,352,160,192,257,262,10,12,51]),
(5,[272,96,160,448,257,262,10,12,57]),
(5,[400,352,160,192,257,6,10,13,19]),
(5,[400,352,160,192,1,262,10,13,35]),
(5,[400,96,160,192,257,262,10,13,49]),
(5,[144,352,160,192,257,262,10,13,50]),
(5,[400,352,160,192,257,262,10,13,51]),
(5,[144,96,160,448,257,262,10,13,56]),
(5,[400,352,32,192,1,134,266,41,67]),
(5,[400,96,288,192,1,134,266,41,69]),
(5,[144,96,288,192,257,134,266,41,84]),
(5,[48,192,320,384,33,17,6,10,12]),
(5,[304,192,320,384,33,17,6,10,13]),
(5,[48,336,416,192,259,5,10,12,22]),
(5,[48,336,416,192,3,261,266,12,102]),
(5,[176,336,288,192,3,133,266,41,70]),
(5,[72,336,224,385,130,260,7,28,42]),
(5,[32,64,128,256,512,1,2,4,8,16]),
(5,[544,64,128,256,512,1,2,4,8,17]),
(5,[544,576,128,256,512,1,2,4,8,19]),
(5,[544,576,640,256,512,1,2,4,8,23]),
(5,[544,576,640,768,512,1,2,4,8,31]),
(5,[288,576,128,256,512,1,2,4,9,18]),
(5,[800,576,128,256,512,1,2,4,9,19]),
(5,[288,576,640,256,512,1,2,4,9,22]),
(5,[800,576,640,256,512,1,2,4,9,23]),
(5,[288,576,128,768,512,1,2,4,9,26]),
(5,[288,576,640,768,512,1,2,4,9,30]),
(5,[800,64,128,256,512,1,2,4,521,273]),
(5,[800,576,128,256,512,1,2,4,521,275]),
(5,[800,576,640,256,512,1,2,4,521,279]),
(5,[288,320,640,256,512,513,2,4,11,52]),
(5,[288,832,640,256,512,513,2,4,11,54]),
(5,[288,320,128,256,512,513,514,4,11,112]),
(5,[288,320,640,256,512,513,514,4,11,116]),
(5,[800,320,640,256,512,1,2,4,523,277]),
(5,[288,320,896,256,512,513,514,4,15,116]),
(5,[288,320,384,256,512,513,514,516,15,240]),
(5,[544,64,128,768,256,1,2,4,24,9]),
(5,[544,576,128,768,256,1,2,4,24,11]),
(5,[544,576,640,768,256,1,2,4,24,15]),
(5,[288,576,640,768,256,1,2,4,25,14]),
(5,[672,832,128,256,512,1,2,5,10,19]),
(5,[160,320,640,768,512,1,2,5,10,28]),
(5,[672,320,128,256,512,1,2,517,10,145]),
(5,[672,832,128,256,512,1,2,517,10,147]),
(5,[672,320,128,768,512,1,2,517,10,153]),
(5,[672,832,128,256,512,1,2,517,522,403]),
(5,[416,832,128,256,512,1,2,517,11,146]),
(5,[928,320,128,256,512,1,514,517,11,209]),
(5,[672,576,384,256,512,1,2,5,12,19]),
(5,[672,64,384,768,512,1,2,5,12,25]),
(5,[160,576,384,768,512,1,2,5,12,26]),
(5,[672,576,384,768,512,1,2,5,12,27]),
(5,[672,576,384,256,512,1,2,517,12,147]),
(5,[672,64,384,256,512,1,2,5,524,273]),
(5,[672,576,384,256,512,1,2,5,524,275]),
(5,[672,832,384,256,512,1,2,5,14,19]),
(5,[672,320,384,256,512,1,514,5,14,81]),
(5,[160,320,384,256,512,513,514,5,14,112]),
(5,[672,320,384,256,512,1,2,517,14,145]),
(5,[160,832,384,256,512,1,2,517,14,146]),
(5,[672,832,384,256,512,1,2,517,14,147]),
(5,[672,320,384,256,512,1,514,517,14,209]),
(5,[160,832,384,256,512,513,2,5,526,306]),
(5,[160,576,128,768,256,1,2,5,24,10]),
(5,[672,576,128,768,256,1,2,5,24,11]),
(5,[160,576,640,768,256,1,2,5,24,14]),
(5,[672,64,128,768,256,1,2,517,24,137]),
(5,[672,576,128,768,256,1,2,517,24,139]),
(5,[672,576,384,768,256,1,2,5,28,11]),
(5,[288,320,384,128,512,513,2,524,7,176]),
(5,[288,832,384,128,512,513,2,524,7,178]),
(5,[288,320,384,128,512,513,514,524,7,240]),
(5,[288,320,640,128,256,513,514,12,19,100]),
(5,[544,576,896,128,256,1,2,12,20,7]),
(5,[544,64,384,640,256,1,2,12,20,9]),
(5,[544,576,384,640,256,1,2,12,20,11]),
(5,[32,64,384,640,768,1,2,12,20,24]),
(5,[544,64,384,640,768,1,2,12,20,25]),
(5,[544,576,384,640,768,1,2,12,20,27]),
(5,[288,576,384,640,768,1,2,12,21,26]),
(5,[608,192,896,256,512,1,3,6,12,21]),
(5,[608,192,384,768,512,1,3,6,12,25]),
(5,[608,192,384,256,512,1,3,518,12,145]),
(5,[608,192,384,256,512,1,3,6,524,273]),
(5,[608,192,896,256,512,1,3,6,524,277]),
(5,[608,192,640,768,256,1,3,6,24,13]),
(5,[608,192,128,768,256,1,515,6,24,73]),
(5,[608,192,128,768,256,1,3,518,24,137]),
(5,[608,320,640,128,256,1,515,268,146,69]),
(5,[608,64,896,128,256,1,515,268,148,69]),
(5,[800,704,320,384,512,1,6,10,13,19]),
(5,[800,192,320,384,512,1,518,10,13,81]),
(5,[288,192,320,384,512,513,518,10,13,112]),
(5,[288,192,576,640,256,1,6,10,17,12]),
(5,[800,192,576,640,256,1,6,10,17,13]),
(5,[288,192,576,640,768,1,6,10,17,28]),
(5,[800,704,64,128,256,1,6,10,529,259]),
(5,[800,192,576,128,256,1,6,10,529,261]),
(5,[800,192,576,640,256,1,6,10,529,269]),
(5,[544,192,320,640,256,1,6,10,20,9]),
(5,[544,192,832,640,256,1,6,10,20,13]),
(5,[32,192,320,640,768,1,6,10,20,24]),
(5,[544,192,320,640,768,1,6,10,20,25]),
(5,[800,576,64,384,128,1,262,536,73,131]),
(5,[288,576,64,384,128,513,262,536,73,162]),
(5,[96,672,832,384,512,3,5,10,12,22]),
(5,[96,160,320,640,768,3,5,10,20,24]),
(5,[608,160,320,640,768,3,5,10,20,25]),
(5,[272,288,320,640,513,514,4,8,7,56]),
(5,[272,288,320,128,513,514,516,8,7,112]),
(5,[272,288,320,640,513,514,516,8,7,120]),
(5,[272,288,320,384,513,514,516,520,15,240]),
(5,[144,288,320,384,513,514,516,9,14,112]),
(5,[144,288,320,384,1,514,516,521,14,224]),
(5,[336,288,192,384,513,514,5,524,11,176])]
private def cachedMIS : Array (List ℕ) := #[[1,2,4],
[3,6,9,12],
[3,6,12],
[3,6,9,12,18,24],
[3,6,9,12,24],
[3,6,9,12,16],
[3,6,12,17,24],
[7,14,21,28,35,42,49,56],
[7,14,21,28,42,56],
[7,14,21,28,56],
[7,14,28,42],
[7,14,17,44,56],
[7,12,18,33,56],
[3,6,9,12,18,24,33,36,48],
[3,6,9,12,18,24,36,48],
[7,14,21,28,35,42,49,56,70,84,98,112],
[7,14,21,28,35,42,49,56,84,112],
[7,14,21,28,35,42,49,56,112],
[7,14,21,28,35,42,49,56,68,96],
[7,14,21,28,35,42,49,56,96],
[7,14,21,28,35,42,49,56,64],
[7,14,21,28,42,56,84,112],
[7,14,21,28,42,56,67,81,98,112],
[7,14,21,28,42,56,81,112],
[7,14,21,28,42,56,69,76,104],
[7,14,21,28,42,56,76,104],
[7,14,21,28,42,56,65,104],
[7,14,21,28,42,56,68,96],
[7,14,21,28,42,56,65,96],
[7,14,21,28,42,56,76],
[7,14,21,28,56,67,96],
[7,14,28,56,67,97,112],
[7,14,28,33,56,66,112],
[7,14,28,33,56,74,104],
[7,14,28,33,56,74,88],
[7,14,28,33,56,66,80],
[7,14,28,33,48,74,96],
[15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240],
[15,30,45,60,75,90,105,120,150,180,210,240],
[15,30,45,60,75,90,105,120,180,240],
[15,30,45,60,75,90,105,120,240],
[15,30,45,60,90,120,165,180,240],
[15,30,45,60,90,120,180,240],
[15,30,45,60,90,120,161,240],
[15,30,45,60,90,120,150,180],
[15,30,45,60,90,120,180],
[15,30,45,60,120,135,192],
[15,30,45,60,67,97,154,184,210,240],
[15,30,45,60,67,82,97,184,240],
[15,30,60,73,120,146,240],
[15,30,60,73,120,150,180],
[15,30,60,67,112,154,210],
[15,30,41,69,84,97,154,184,240],
[15,30,41,56,69,84,131,146,225,240],
[15,30,41,56,69,84,97,146,240],
[15,28,42,56,69,84,131,162,193,240],
[14,21,28,35,42,49,120,135,192],
[7,14,21,28,35,42,49,56,70,84,98,112,133,140,161,168,196,224],
[7,14,21,28,35,42,49,56,70,84,98,112,140,168,196,224],
[7,14,21,28,35,42,49,56,70,84,98,112,161,168,224],
[7,14,21,28,35,42,49,56,70,84,98,112,168,224],
[7,14,21,28,35,42,49,56,70,84,98,112,129,136,192],
[7,14,21,28,35,42,49,56,70,84,98,112,136,192],
[7,14,21,28,35,42,49,56,84,112,131,138,192],
[7,14,21,28,35,42,49,56,84,112,138,192],
[7,14,21,28,35,42,49,56,84,112,129,136,192],
[7,14,21,28,35,42,49,56,84,112,145,152],
[7,14,21,28,42,56,84,112,129,136,192],
[7,14,21,28,42,56,67,81,98,112,132,224],
[7,14,21,28,42,56,81,112,140,168,224],
[7,14,21,28,42,56,81,112,140,192],
[7,14,21,28,42,56,76,104,145,152,200],
[7,14,21,28,42,56,65,104,148,176,224],
[7,14,21,28,38,52,81,88,112,140,164,200,224],
[7,14,21,28,38,52,81,88,112,131,138,162,193,200,224],
[7,14,21,28,38,52,81,88,112,138,162,200,224],
[7,14,21,28,38,52,69,76,100,152,176,200,224],
[7,14,28,56,67,97,112,138,168,194,224],
[7,14,28,33,56,66,112,133,148,208],
[15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,270,300,330,360,390,420,450,480],
[15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,300,360,420,480],
[15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,360,480],
[15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,480],
[15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,268,328,388,448],
[15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,328,448],
[15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,448],
[15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,264,384],
[15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,384],
[15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240,256],
[15,30,45,60,75,90,105,120,150,180,210,240,300,360,420,480],
[15,30,45,60,75,90,105,120,150,180,210,240,360,480],
[15,30,45,60,75,90,105,120,150,180,210,240,263,293,323,353,390,420,450,480],
[15,30,45,60,75,90,105,120,150,180,210,240,293,353,420,480],
[15,30,45,60,75,90,105,120,150,180,210,240,353,480],
[15,30,45,60,75,90,105,120,150,180,210,240,269,284,329,344,404,464],
[15,30,45,60,75,90,105,120,150,180,210,240,284,344,404,464],
[15,30,45,60,75,90,105,120,150,180,210,240,329,344,464],
[15,30,45,60,75,90,105,120,150,180,210,240,344,464],
[15,30,45,60,75,90,105,120,150,180,210,240,261,321,404,464],
[15,30,45,60,75,90,105,120,150,180,210,240,321,464],
[15,30,45,60,75,90,105,120,150,180,210,240,268,328,388,448],
[15,30,45,60,75,90,105,120,150,180,210,240,328,448],
[15,30,45,60,75,90,105,120,150,180,210,240,261,321,388,448],
[15,30,45,60,75,90,105,120,150,180,210,240,321,448],
[15,30,45,60,75,90,105,120,150,180,210,240,265,280,400],
[15,30,45,60,75,90,105,120,150,180,210,240,280,400],
[15,30,45,60,75,90,105,120,150,180,210,240,257,400],
[15,30,45,60,75,90,105,120,150,180,210,240,264,384],
[15,30,45,60,75,90,105,120,150,180,210,240,257,384],
[15,30,45,60,75,90,105,120,150,180,210,240,284,344],
[15,30,45,60,75,90,105,120,150,180,210,240,344],
[15,30,45,60,75,90,105,120,150,180,210,240,280],
[15,30,45,60,75,90,105,120,180,240,323,353,480],
[15,30,45,60,75,90,105,120,180,240,330,448],
[15,30,45,60,75,90,105,120,180,240,263,323,388,448],
[15,30,45,60,75,90,105,120,180,240,323,448],
[15,30,45,60,75,90,105,120,180,240,259,274,289,432],
[15,30,45,60,75,90,105,120,180,240,267,297,416],
[15,30,45,60,75,90,105,120,180,240,266,296,416],
[15,30,45,60,75,90,105,120,180,240,297,416],
[15,30,45,60,75,90,105,120,180,240,259,289,416],
[15,30,45,60,75,90,105,120,180,240,267,384],
[15,30,45,60,75,90,105,120,180,240,266,384],
[15,30,45,60,75,90,105,120,180,240,259,384],
[15,30,45,60,75,90,105,120,180,240,282,312],
[15,30,45,60,75,90,105,120,180,240,259,274,289,304],
[15,30,45,60,75,90,105,120,240,270,384],
[15,30,45,60,75,90,105,120,240,263,384],
[15,30,45,60,75,90,105,120,142,172,202,232,353,368,480],
[15,30,45,60,75,90,105,120,142,172,202,232,368,480],
[15,30,45,60,75,90,105,120,172,232,338,448],
[15,30,45,60,90,120,165,180,240,300,360,420,480],
[15,30,45,60,90,120,165,180,240,267,297,330,360,417,480],
[15,30,45,60,90,120,165,180,240,297,360,417,480],
[15,30,45,60,90,120,165,180,240,259,322,417,480],
[15,30,45,60,90,120,165,180,240,268,328,388,448],
[15,30,45,60,90,120,165,180,240,265,328,385,448],
[15,30,45,60,90,120,165,180,240,259,322,385,448],
[15,30,45,60,90,120,165,180,240,284,404],
[15,30,45,60,90,120,165,180,240,278,404],
[15,30,45,60,90,120,180,240,265,328,448],
[15,30,45,60,90,120,180,240,259,322,448],
[15,30,45,60,90,120,180,240,265,280,400],
[15,30,45,60,90,120,131,161,210,240,300,360,480],
[15,30,45,60,90,120,131,210,240,297,360,417,480],
[15,30,45,60,90,120,210,240,263,293,387,417,450,480],
[15,30,45,60,90,120,131,161,210,240,262,292,450,480],
[15,30,45,60,90,120,131,210,240,293,417,480],
[15,30,45,60,90,120,131,161,210,240,292,480],
[15,30,45,60,90,120,131,161,210,240,284,344,464],
[15,30,45,60,90,120,131,161,210,240,265,344,385,464],
[15,30,45,60,90,120,131,161,210,240,261,276,385,464],
[15,30,45,60,90,120,131,161,210,240,276,464],
[15,30,45,60,90,120,131,161,210,240,268,328,448],
[15,30,45,60,90,120,131,161,210,240,265,328,385,448],
[15,30,45,60,90,120,131,161,210,240,261,385,448],
[15,30,45,60,90,120,131,161,210,240,260,448],
[15,30,45,60,90,120,131,210,240,297,312,417,432],
[15,30,45,60,90,120,131,161,210,240,278,308,402,432],
[15,30,45,60,90,120,131,161,210,240,308,432],
[15,30,45,60,90,120,131,161,210,240,284,400],
[15,30,45,60,90,120,131,161,210,240,265,280,385,400],
[15,30,45,60,90,120,131,161,210,240,276,400],
[15,30,45,60,90,120,131,161,210,240,278,308,338,368],
[15,30,45,60,90,120,131,161,210,240,308,368],
[15,30,45,60,90,120,131,161,210,240,262,292,322,352],
[15,30,45,60,90,120,131,161,210,240,292,352],
[15,30,45,60,90,120,131,161,210,240,284,344],
[15,30,45,60,90,120,131,161,210,240,276,336],
[15,30,45,60,90,120,131,161,210,240,260,320],
[15,30,45,60,90,120,161,240,300,360,480],
[15,30,45,60,90,120,161,240,284,344,464],
[15,30,45,60,90,120,161,240,278,338,464],
[15,30,45,60,90,120,161,240,270,330,448],
[15,30,45,60,90,120,161,240,268,328,448],
[15,30,45,60,90,120,161,240,263,322,385,448],
[15,30,45,60,90,120,161,240,262,322,448],
[15,30,45,60,90,120,161,240,278,308,432],
[15,30,45,60,90,120,161,240,269,284,385,400],
[15,30,45,60,90,120,161,240,284,400],
[15,30,45,60,90,120,161,240,278,400],
[15,30,45,60,90,120,161,240,300,360],
[15,30,45,60,90,120,172,232,293,308,420],
[15,30,45,60,90,120,139,169,202,232,292,480],
[15,30,45,60,90,120,169,232,308,368,480],
[15,30,45,60,90,120,169,232,308,416],
[15,30,45,60,90,120,169,232,278,384],
[15,30,45,60,90,120,131,161,194,308,368,480],
[15,30,45,60,90,120,131,161,194,224,278,308,386,416],
[15,30,45,60,90,120,131,161,194,224,308,416],
[15,30,45,60,90,120,137,216,278,308,400],
[15,30,45,60,90,120,137,216,293,308,385,400],
[15,30,45,60,90,120,137,216,308,400],
[15,30,45,60,90,120,150,180,289,352,416],
[15,30,45,60,90,120,150,180,257,336,400],
[15,30,45,60,90,120,150,180,268,328,388],
[15,30,45,60,90,120,150,180,257,320,384],
[15,30,45,60,90,120,180,265,328,384],
[15,30,45,60,90,120,180,259,322,384],
[15,30,45,60,120,135,192,259,274,289,304],
[15,30,45,60,82,97,184,240,263,323,448],
[15,30,45,60,67,82,97,184,240,262,322,448],
[15,30,45,60,67,82,97,184,240,263,293,416],
[15,30,45,60,67,82,97,184,240,262,292,416],
[15,30,45,60,67,82,97,184,240,293,416],
[15,30,45,60,67,82,97,184,240,270,392],
[15,30,45,60,67,82,97,184,240,267,392],
[15,30,45,60,67,82,97,184,240,263,384],
[15,30,45,60,67,82,97,184,240,262,384],
[15,30,45,60,67,82,97,112,154,184,293,416],
[15,30,45,60,78,108,169,184,232,308,356,432,480],
[15,30,45,60,78,108,169,184,232,293,308,356],
[15,30,45,60,78,108,169,184,232,308,356],
[15,30,45,60,78,108,131,146,194,297,312,360,417,432,480],
[15,30,60,73,120,131,146,193,240,266,360,386,480],
[15,30,60,73,120,146,240,263,292,387,449,480],
[15,30,60,73,120,131,146,193,240,262,292,386,480],
[15,30,60,73,120,131,146,240,261,292,449,480],
[15,30,60,73,120,131,193,240,282,344,402,464],
[15,30,60,73,120,131,193,240,278,402,464],
[15,30,60,73,120,131,146,240,261,276,449,464],
[15,30,60,73,120,131,193,240,282,312,402,432],
[15,30,60,73,120,131,193,240,278,308,402,432],
[15,30,60,73,120,131,146,193,240,261,308,385,432],
[15,30,60,73,120,131,146,193,240,270,300,386,416],
[15,30,60,73,120,131,146,193,240,266,296,386,416],
[15,30,60,73,120,131,146,193,240,262,292,386,416],
[15,30,60,73,120,131,146,193,240,261,292,385,416],
[15,30,60,73,120,131,146,193,240,278,308,368],
[15,30,60,73,120,131,146,193,240,266,360],
[15,30,60,73,120,131,146,193,240,262,292,352],
[15,30,60,73,120,131,146,193,240,282,344],
[15,30,60,73,120,146,240,261,308,432],
[15,30,60,73,120,146,240,261,292,416],
[15,30,60,120,139,201,232,274,368,386,480],
[15,30,60,73,120,131,193,224,278,308,386,416],
[15,30,60,67,112,137,168,193,224,282,338,392,448],
[15,30,60,67,112,137,168,193,224,278,338,448],
[15,30,60,67,112,154,210,265,296,392],
[15,30,60,67,112,154,210,262,292,386],
[15,30,60,67,112,154,210,261,292,384],
[15,30,60,67,112,137,184,282,338,408],
[15,30,60,67,112,137,184,278,338,400],
[15,30,41,56,69,131,225,240,278,340,402,464],
[15,30,41,56,69,84,131,146,225,240,268,324,448],
[15,30,41,56,69,84,131,146,225,240,262,324,386,448],
[15,30,41,56,69,84,97,146,240,268,296,324,480],
[15,30,41,56,69,97,146,240,284,340,464],
[15,30,41,56,69,84,97,146,240,270,324,386,448],
[15,30,41,56,84,97,146,240,269,325,448],
[15,30,41,56,69,84,97,146,240,268,324,448],
[15,30,41,56,84,97,146,240,263,325,386,448],
[15,30,41,69,97,112,150,212,284,312,404],
[15,30,41,69,97,112,150,212,282,312,402],
[15,30,56,69,97,112,150,212,267,297,386],
[15,30,46,73,88,104,133,148,164,259,274,290,449,464,480],
[15,30,46,73,88,104,133,148,164,193,274,290,464,480],
[15,28,42,56,69,84,131,162,240,265,296,449,480],
[15,28,42,56,69,84,131,162,193,240,265,280,385,400],
[15,28,42,69,112,134,212,265,312,400],
[7,14,28,42,49,120,163,224,277,336,385,448],
[31,62,93,124,155,186,217,248,279,310,341,372,403,434,465,496,527,558,589,620,651,682,713,744,775,806,837,868,899,930,961,992],
[31,62,93,124,155,186,217,248,279,310,341,372,403,434,465,496,558,620,682,744,806,868,930,992],
[31,62,93,124,155,186,217,248,279,310,341,372,403,434,465,496,620,744,868,992],
[31,62,93,124,155,186,217,248,279,310,341,372,403,434,465,496,744,992],
[31,62,93,124,155,186,217,248,279,310,341,372,403,434,465,496,992],
[31,62,93,124,155,186,217,248,310,372,434,496,589,620,713,744,868,992],
[31,62,93,124,155,186,217,248,310,372,434,496,620,744,868,992],
[31,62,93,124,155,186,217,248,310,372,434,496,713,744,992],
[31,62,93,124,155,186,217,248,310,372,434,496,744,992],
[31,62,93,124,155,186,217,248,310,372,434,496,581,705,868,992],
[31,62,93,124,155,186,217,248,310,372,434,496,705,992],
[31,62,93,124,155,186,217,248,310,372,434,496,558,620,682,744],
[31,62,93,124,155,186,217,248,310,372,434,496,620,744],
[31,62,93,124,155,186,217,248,310,372,434,496,744],
[31,62,93,124,155,186,217,248,372,496,651,713,960],
[31,62,93,124,155,186,217,248,372,496,713,960],
[31,62,93,124,155,186,217,248,372,496,527,651,772,896],
[31,62,93,124,155,186,217,248,372,496,651,896],
[31,62,93,124,155,186,217,248,372,496,682,744],
[31,62,93,124,155,186,217,248,496,651,896],
[31,62,93,124,155,186,217,248,496,527,768],
[31,62,93,124,155,186,217,248,263,325,387,449,566,628,690,752,806,868,930,992],
[31,62,93,124,155,186,217,248,263,294,325,387,418,449,628,752,868,992],
[31,62,93,124,155,186,217,248,263,294,325,356,387,418,449,752,992],
[31,62,93,124,155,186,217,248,294,356,418,721,752,992],
[31,62,93,124,186,248,341,372,496,620,744,868,992],
[31,62,93,124,186,248,341,372,496,515,674,833,992],
[31,62,93,124,186,248,341,372,496,558,620,868],
[31,62,93,124,186,248,341,372,496,620,868],
[31,62,93,124,186,248,341,372,496,550,868],
[31,62,93,124,186,248,341,372,496,620],
[31,62,93,124,186,248,372,496,589,620,868],
[31,62,93,124,186,248,372,496,558,804],
[31,62,93,124,186,248,275,337,434,496,620,744,992],
[31,62,93,124,186,248,275,337,434,496,550,612,930,992],
[31,62,93,124,186,248,275,337,434,496,581,612,833,992],
[31,62,93,124,186,248,275,337,434,496,612,992],
[31,62,93,124,186,248,275,337,434,496,620,864],
[31,62,93,124,186,248,275,337,434,496,558,620,682,744],
[31,62,93,124,186,248,275,337,434,496,620,744],
[31,62,93,124,186,248,337,496,620,744,992],
[31,62,93,124,186,248,337,496,558,682,928],
[31,62,93,124,186,248,337,496,527,650,769,896],
[31,62,93,124,186,248,337,496,558,620,864],
[31,62,93,124,186,248,337,496,589,620,833,864],
[31,62,93,124,186,248,337,496,620,864],
[31,62,93,124,186,248,337,496,558,800],
[31,62,93,124,186,248,337,496,589,712],
[31,62,93,124,186,248,263,294,418,597,628,752,837,868,992],
[31,62,93,124,186,248,263,294,325,418,628,752,868,992],
[31,62,93,124,186,248,263,294,325,356,418,593,752,833,992],
[31,62,93,124,186,248,263,325,418,480,566,628,806,868],
[31,62,93,124,186,248,263,294,325,418,480,628,868],
[31,62,93,124,186,248,259,321,418,628,752,992],
[31,62,93,124,147,178,209,376,496,527,589,840],
[31,62,93,124,147,178,209,376,496,589,840],
[31,62,93,124,147,178,209,376,496,527,776],
[31,62,93,124,178,209,240,364,480,539,659,776,896],
[31,62,93,124,147,178,209,267,298,329,387,418,449,632,752,872,992],
[31,62,93,124,147,209,267,298,329,360,387,449,566,628,690,752,930,992],
[31,62,93,124,147,178,209,267,298,329,360,387,418,449,628,752,992],
[31,62,93,124,147,178,209,240,267,298,329,360,519,550,581,612,899,930,961,992],
[31,62,93,124,147,178,209,240,267,298,329,360,387,449,550,612,930,992],
[31,62,93,124,147,178,209,240,267,298,329,360,387,418,449,612,992],
[31,62,93,124,147,178,209,240,298,360,418,581,612,705,992],
[31,62,124,153,248,275,306,401,496,554,744,802,992],
[31,62,124,153,248,275,306,401,496,550,612,802,992],
[31,62,124,153,248,275,306,401,496,558,620,802,864],
[31,62,124,153,248,275,306,401,496,558,620,744],
[31,62,124,153,248,275,306,401,496,554,744],
[31,62,124,153,248,263,294,356,385,562,752,802,992],
[31,62,124,153,248,263,356,385,480,566,688,806,928],
[31,62,124,153,248,263,385,480,566,628,806,868],
[31,62,124,147,240,269,364,570,690,808],
[31,62,124,147,240,267,360,570,690,810],
[31,62,89,120,149,180,209,306,496,556,616,676,992],
[31,62,89,120,149,180,209,306,496,558,676,802,928],
[31,62,89,120,149,180,209,306,496,527,645,770,896],
[31,62,89,120,149,180,302,360,420,531,562,721,752,802,992],
[31,62,89,120,149,180,209,302,360,420,562,752,802,992],
[31,62,89,120,149,180,209,240,302,360,420,515,705,802,992],
[31,62,89,149,209,302,360,420,480,572,632,692,752],
[31,62,89,149,180,209,302,360,420,480,570,632,752],
[31,62,89,120,149,180,209,302,360,420,480,562,752],
[31,62,89,120,149,209,267,298,329,360,449,566,692,752,802,992],
[31,62,89,120,149,180,209,267,298,329,360,449,562,752,802,992],
[31,62,89,120,149,180,209,240,267,298,329,360,519,550,645,676,771,802,961,992],
[31,62,89,120,149,180,209,240,267,298,329,360,449,550,676,802,992],
[31,62,89,135,193,224,310,422,572,632,820],
[31,62,120,135,193,224,310,422,541,601,788],
[31,60,90,120,149,180,275,338,401,496,521,616,897,992],
[31,60,90,120,149,180,240,267,330,360,519,645,676,771,834,897,992],
[31,60,90,120,149,180,240,267,330,360,385,518,676,834,992],
[15,30,45,60,75,90,105,150,165,180,210,225,376,496,647,707,960],
[30,45,60,75,90,105,150,165,180,195,210,225,376,496,527,647,776,896],
[15,30,45,60,75,90,105,150,165,180,195,210,225,376,496,647,896],
[30,45,60,75,90,105,120,135,150,165,180,195,210,225,496,527,768],
[30,45,60,75,90,105,120,150,180,210,353,496,527,646,769,896],
[45,60,75,90,105,120,150,180,210,353,496,527,542,769,784],
[30,45,60,90,120,131,161,210,308,496,527,586,772,832]]
private def patternCache : Array (List ℕ) := #[[1,2,4],
[5,3,10,12],
[1,3,6,4],
[5,19,10,44,48],
[5,3,10,28,16],
[5,3,10,12,16],
[9,3,6,20,24],
[85,51,15,170,204,240],
[5,19,15,58,44,48],
[5,3,15,26,28,16],
[1,11,7,14,4,8],
[5,3,11,26,20,24],
[9,5,3,18,20,24],
[69,19,138,44,304,448],
[5,19,74,44,176,192],
[85,1331,783,170,2764,3312,3840],
[85,51,271,170,972,752,768],
[85,51,15,170,460,496,256],
[85,51,271,170,204,752,768],
[85,51,15,170,204,496,256],
[85,51,15,170,204,240,256],
[5,19,79,58,236,176,192],
[197,339,15,58,684,816,960],
[69,19,15,58,236,176,192],
[69,19,207,442,44,304,448],
[5,19,79,250,44,176,192],
[69,19,15,186,44,176,192],
[5,19,79,58,44,176,192],
[69,19,15,58,44,176,192],
[5,19,79,122,44,48,64],
[37,35,15,26,28,80,96],
[49,19,7,14,76,104,112],
[9,35,7,22,84,88,96],
[9,35,7,118,20,88,96],
[9,35,7,118,84,24,96],
[9,35,7,22,84,24,96],
[9,35,7,38,20,88,96],
[21845,13107,3855,255,43690,52428,61680,65280],
[85,1331,783,255,4010,2764,3312,3840],
[85,51,271,255,938,972,752,768],
[85,51,15,255,426,460,496,256],
[69,19,207,63,442,492,304,448],
[5,19,79,63,250,236,176,192],
[69,19,15,63,186,236,176,192],
[5,83,207,63,250,172,48,192],
[5,19,79,63,122,108,48,64],
[37,35,47,31,26,28,80,96],
[53,339,15,207,970,684,816,960],
[85,51,15,143,426,460,368,384],
[9,35,7,31,118,84,88,96],
[9,35,103,31,118,84,24,96],
[9,107,7,39,118,20,88,96],
[45,67,27,199,466,420,312,448],
[341,195,51,15,682,780,816,960],
[85,131,51,15,426,332,368,384],
[337,197,51,15,554,652,816,960],
[170,153,135,85,102,120,320,384],
[20565,1331,13071,41130,2764,52464,3840,61440],
[85,1331,21263,12458,2764,44272,52992,61440],
[4181,1331,783,8362,2764,31984,20224,28672],
[85,1331,783,4266,2764,15600,12032,12288],
[4181,1331,783,8362,2764,3312,20224,28672],
[85,1331,783,4266,2764,3312,12032,12288],
[1109,3123,271,2218,972,752,4864,7168],
[85,1075,271,1194,972,752,2816,3072],
[1109,51,271,2218,972,752,4864,7168],
[1109,51,271,2218,4044,752,768,3072],
[261,19,79,570,236,176,1216,1792],
[197,339,1039,58,684,2864,3008,3072],
[69,19,271,826,236,1712,1216,1792],
[69,19,271,314,236,176,704,768],
[261,19,79,1786,812,176,1216,1792],
[69,19,271,186,812,1712,1216,1792],
[69,19,1599,2698,492,5424,6592,7680],
[4677,3603,63,9354,492,18736,29120,32256],
[69,1555,63,2698,492,5424,6592,7680],
[69,19,511,2698,1580,5424,6592,7680],
[49,659,7,398,76,1384,1648,1920],
[137,35,391,22,852,88,608,896],
[21845,13107,3855,255,43690,52428,61680,65280,0],
[21845,13107,3855,255,43690,52428,61680,65280,0],
[21845,13107,3855,255,43690,52428,61680,65280,0],
[21845,13107,3855,255,43690,52428,61680,65280,0],
[21845,13107,3855,255,43690,52428,61680,65280,0],
[21845,13107,3855,255,43690,52428,61680,65280,0],
[21845,13107,3855,255,43690,52428,61680,65280,0],
[21845,13107,3855,255,43690,52428,61680,65280,0],
[21845,13107,3855,255,43690,52428,61680,65280,0],
[21845,13107,3855,255,43690,52428,61680,65280,0],
[85,1331,21263,12543,4010,64204,44272,52992,61440],
[85,1331,783,4351,4010,15052,15600,12032,12288],
[61525,21811,13071,255,4010,43724,52464,3840,61440],
[12373,1331,21263,255,4010,64204,44272,52992,61440],
[4181,1331,783,255,4010,15052,15600,12032,12288],
[20565,1331,13071,61695,44970,2764,52464,3840,61440],
[85,1331,21263,12543,65450,2764,44272,52992,61440],
[4181,1331,783,12543,28586,2764,31984,20224,28672],
[85,1331,783,4351,16298,2764,15600,12032,12288],
[12373,1331,21263,255,53162,2764,44272,52992,61440],
[4181,1331,783,255,12202,2764,15600,12032,12288],
[85,1331,21263,12543,4010,2764,44272,52992,61440],
[85,1331,783,4351,4010,2764,15600,12032,12288],
[12373,1331,21263,255,4010,2764,44272,52992,61440],
[4181,1331,783,255,4010,2764,15600,12032,12288],
[4181,1331,783,12543,28586,2764,3312,20224,28672],
[85,1331,783,4351,16298,2764,3312,12032,12288],
[4181,1331,783,255,12202,2764,3312,12032,12288],
[85,1331,783,4351,4010,2764,3312,12032,12288],
[4181,1331,783,255,4010,2764,3312,12032,12288],
[85,1331,4879,12543,16298,2764,11504,3840,12288],
[85,1331,783,4351,8106,2764,7408,3840,4096],
[85,1331,783,4351,8106,2764,3312,3840,4096],
[3157,1075,271,255,938,7116,7920,4864,7168],
[85,1075,271,1279,938,972,3824,2816,3072],
[3157,3123,5391,255,938,972,10992,13056,15360],
[1109,1075,271,255,938,972,3824,2816,3072],
[5205,3123,271,255,11178,13260,752,8960,15360],
[3157,1075,271,3327,938,7116,752,4864,7168],
[85,1075,271,3327,938,7116,752,4864,7168],
[1109,51,271,1279,938,4044,752,2816,3072],
[3157,1075,271,255,938,7116,752,4864,7168],
[1109,1075,271,1279,938,972,752,2816,3072],
[85,1075,271,1279,938,972,752,2816,3072],
[1109,1075,271,255,938,972,752,2816,3072],
[85,1075,271,3327,4010,3020,752,768,3072],
[5205,3123,271,255,11178,13260,752,768,15360],
[85,563,527,767,426,460,496,1280,1536],
[597,563,527,255,426,460,496,1280,1536],
[4181,1331,783,4095,8362,31436,31984,20224,28672],
[85,1331,783,4095,4266,15052,15600,12032,12288],
[85,1075,271,1023,1194,972,3824,2816,3072],
[69,19,2767,1599,442,8172,5424,6592,7680],
[9797,2579,207,7743,442,30188,22832,25024,32256],
[2629,19,207,1599,442,8172,5424,6592,7680],
[2629,1555,207,63,442,6636,5424,6592,7680],
[69,19,2767,1599,442,492,5424,6592,7680],
[2629,19,207,1599,442,492,5424,6592,7680],
[2629,1555,207,63,442,492,5424,6592,7680],
[69,19,1743,575,1978,492,304,1472,1536],
[69,531,1743,63,1978,492,304,1472,1536],
[261,19,79,831,250,236,1712,1216,1792],
[261,787,79,63,250,236,1712,1216,1792],
[261,19,79,831,1786,236,176,1216,1792],
[197,339,1039,3135,826,7852,6960,5056,7168],
[2629,211,15,1599,442,7980,5552,6592,7680],
[3845,5459,783,63,250,10924,12528,15552,16128],
[197,5459,3087,63,826,10924,13104,13248,15360],
[1605,211,527,63,442,3884,2480,3520,3584],
[197,339,1039,63,826,3756,2864,3008,3072],
[197,339,1039,3135,7994,684,6960,5056,7168],
[5317,339,15,3135,11066,684,11056,13248,15360],
[5317,339,3087,63,11066,684,9008,13248,15360],
[197,339,1039,63,3898,684,2864,3008,3072],
[197,339,1039,3135,826,684,6960,5056,7168],
[5317,339,15,3135,826,684,11056,13248,15360],
[3269,339,1039,63,826,684,4912,7104,7168],
[197,339,1039,63,826,684,2864,3008,3072],
[2629,211,15,1599,5562,7980,432,6592,7680],
[197,5459,3087,63,16186,10924,816,13248,15360],
[197,339,1039,63,3898,3756,816,3008,3072],
[197,339,1039,1087,3898,684,816,3008,3072],
[5317,339,15,3135,11066,684,816,13248,15360],
[197,339,1039,63,3898,684,816,3008,3072],
[197,5459,3087,63,16186,10924,13104,960,15360],
[197,339,1039,63,3898,3756,2864,960,3072],
[197,5459,3087,63,826,10924,13104,960,15360],
[197,339,1039,63,826,3756,2864,960,3072],
[197,339,1039,3135,3898,684,2864,960,3072],
[197,339,1039,63,3898,684,2864,960,3072],
[197,339,1039,63,826,684,2864,960,3072],
[69,19,271,831,186,2028,1712,1216,1792],
[69,19,271,831,1978,236,1712,1216,1792],
[69,787,271,63,1978,236,1712,1216,1792],
[69,787,271,831,186,236,1712,1216,1792],
[69,19,271,831,186,236,1712,1216,1792],
[1349,787,271,63,186,236,2736,3264,3840],
[69,787,271,63,186,236,1712,1216,1792],
[69,275,783,63,1978,1772,176,1216,1792],
[1349,19,783,831,2746,236,176,3264,3840],
[69,19,271,319,954,236,176,704,768],
[69,275,271,63,954,236,176,704,768],
[69,19,271,831,186,1004,688,192,768],
[261,19,1871,255,570,2028,176,1216,1792],
[197,339,1039,1023,58,3756,2864,3008,3072],
[69,19,271,255,826,2028,1712,1216,1792],
[69,19,271,255,314,1004,176,704,768],
[69,275,271,255,314,236,176,704,768],
[197,339,527,63,1594,3756,3376,2496,3584],
[197,5459,3087,63,3130,10924,816,13248,15360],
[197,339,1039,63,1082,3756,816,3008,3072],
[69,275,783,255,1978,556,176,1216,1792],
[1349,19,783,255,2746,812,176,3264,3840],
[69,19,271,255,954,300,176,704,768],
[261,83,207,63,250,1964,560,1216,1792],
[261,83,207,63,1786,172,560,1216,1792],
[5,83,1487,831,250,172,560,1216,1792],
[261,83,207,63,250,172,560,1216,1792],
[133,19,79,447,122,108,304,576,896],
[133,403,79,63,122,108,304,576,896],
[677,419,47,31,1306,1564,80,96,1920],
[805,787,271,79,218,236,1712,1216,1792],
[85,1587,527,143,426,460,3440,2432,3584],
[1621,563,1551,143,426,3532,368,2432,3584],
[85,563,1551,143,426,3532,368,2432,3584],
[597,51,527,143,426,1996,368,1408,1536],
[85,563,527,1679,426,460,368,1408,1536],
[597,563,15,1679,426,460,368,1408,1536],
[597,563,527,143,426,460,368,1408,1536],
[85,563,527,143,426,460,368,1408,1536],
[1109,307,1039,783,938,3788,240,2816,3072],
[69,19,1599,511,2698,8172,5424,6592,7680],
[581,19,3647,511,1162,4076,2352,448,3584],
[69,19,1599,511,650,2028,1328,448,1536],
[4677,467,63,3647,9354,32300,18736,29120,32256],
[169,2659,7,1567,342,5396,5528,6624,7680],
[1673,675,391,31,118,2388,3160,3680,3968],
[169,2659,1543,31,342,5396,4504,6624,7680],
[1321,99,775,31,214,2708,3224,3296,3840],
[105,1315,7,799,3990,148,2776,3296,3840],
[105,803,263,31,1942,148,1240,1760,1792],
[1321,99,775,31,2774,148,3224,3296,3840],
[105,1315,7,799,3990,2708,216,3296,3840],
[105,1315,775,31,3990,2708,216,3296,3840],
[2729,99,1543,31,5462,5396,408,6624,7680],
[169,2659,1543,1567,342,5396,408,6624,7680],
[169,2659,7,1567,342,5396,408,6624,7680],
[169,2659,1543,31,342,5396,408,6624,7680],
[2729,99,1543,31,342,5396,408,6624,7680],
[169,611,1543,31,3926,3348,2456,480,3584],
[169,611,7,1567,342,1300,1432,480,1536],
[169,611,1543,31,342,3348,2456,480,3584],
[169,611,7,1567,1878,276,1432,480,1536],
[137,35,391,31,886,852,88,608,896],
[137,35,391,31,118,852,88,608,896],
[49,659,7,127,398,1356,1384,1648,1920],
[105,1315,775,31,790,2708,216,3296,3840],
[169,1547,7,2663,1558,340,5528,6624,7680],
[169,1547,519,103,1558,340,3480,2528,3584],
[137,107,7,935,118,276,88,608,896],
[9,747,391,39,118,276,88,608,896],
[137,107,391,39,118,276,88,608,896],
[41,395,7,743,982,84,280,608,896],
[41,395,135,103,982,84,280,608,896],
[117,1315,787,15,3978,204,2768,3296,3840],
[341,195,3123,1039,682,780,6960,5056,7168],
[341,5315,3123,15,682,780,11056,13248,15360],
[85,131,2611,1551,426,5452,6512,4480,7680],
[53,67,787,271,1994,172,1712,1216,1792],
[85,2691,1587,527,426,332,5488,6528,7680],
[805,67,787,271,218,172,1712,1216,1792],
[85,131,1587,527,426,332,3440,2432,3584],
[805,1347,787,15,218,172,2736,3264,3840],
[29,67,1483,775,2018,564,184,1216,1792],
[29,1347,203,775,2018,564,184,1216,1792],
[793,1347,203,775,230,564,184,1216,1792],
[4681,3591,455,63,9362,18724,28728,29120,32256],
[585,3079,455,63,5266,10532,12856,13248,15360],
[2641,197,51,1551,298,5516,6448,6592,7680],
[5457,197,51,3087,10794,652,816,13248,15360],
[137,37,107,391,850,276,88,608,896],
[1361,75,263,46,820,248,2720,3264,3840],
[21845,13107,3855,255,65535,43690,52428,61680,65280,0],
[21845,13107,3855,255,65535,43690,52428,61680,65280,0],
[21845,13107,3855,255,65535,43690,52428,61680,65280,0],
[21845,13107,3855,255,65535,43690,52428,61680,65280,0],
[21845,13107,3855,255,65535,43690,52428,61680,65280,0],
[20565,1331,13071,61695,4095,44970,64204,52464,3840,61440],
[85,1331,21263,12543,4095,65450,64204,44272,52992,61440],
[4181,1331,783,12543,4095,28586,31436,31984,20224,28672],
[85,1331,783,4351,4095,16298,15052,15600,12032,12288],
[12373,1331,21263,255,4095,53162,64204,44272,52992,61440],
[4181,1331,783,255,4095,12202,15052,15600,12032,12288],
[85,21811,13071,61695,4095,65450,43724,52464,3840,61440],
[85,1331,4879,12543,4095,16298,15052,11504,3840,12288],
[85,1331,783,4351,4095,8106,6860,7408,3840,4096],
[3157,1075,271,3327,1023,938,7116,7920,4864,7168],
[1109,51,271,1279,1023,938,4044,3824,2816,3072],
[3157,3123,5391,3327,1023,938,972,10992,13056,15360],
[1109,1075,271,1279,1023,938,972,3824,2816,3072],
[85,1075,271,3327,1023,4010,3020,3824,768,3072],
[597,563,15,767,511,426,460,2032,1280,1536],
[597,563,527,767,511,426,460,496,1280,1536],
[3925,21811,13071,255,61695,61610,43724,52464,3840,61440],
[11605,6963,18191,255,49407,53930,58572,47344,16128,49152],
[21845,13107,3855,255,33023,43690,52428,61680,32512,32768],
[2133,1331,783,255,6399,14250,15052,15600,9984,14336],
[69,19,2767,1599,511,8122,8172,5424,6592,7680],
[2629,1555,207,63,511,5562,6636,5424,6592,7680],
[69,531,3791,1599,511,4026,3564,304,2496,3584],
[69,19,1743,575,511,1978,2028,304,1472,1536],
[69,531,1743,63,511,1978,1516,304,1472,1536],
[69,19,719,575,511,954,1004,304,448,512],
[261,19,1871,831,255,1786,2028,176,1216,1792],
[5,275,847,319,255,1018,236,176,704,768],
[197,339,1039,3135,1023,7994,7852,6960,5056,7168],
[197,5459,3087,63,1023,16186,10924,13104,13248,15360],
[5317,339,3087,63,1023,11066,16044,9008,13248,15360],
[197,339,1039,63,1023,3898,3756,2864,3008,3072],
[197,339,1039,1087,1023,3898,3756,816,3008,3072],
[197,5459,3087,15423,1023,16186,10924,13104,960,15360],
[197,339,1039,3135,1023,3898,3756,2864,960,3072],
[69,19,271,831,255,1978,2028,1712,1216,1792],
[69,787,271,831,255,1978,236,1712,1216,1792],
[1349,787,271,831,255,186,236,2736,3264,3840],
[69,275,783,831,255,1978,1772,176,1216,1792],
[1349,19,783,831,255,2746,4076,176,3264,3840],
[69,19,271,319,255,954,1004,176,704,768],
[69,275,271,319,255,954,236,176,704,768],
[325,19,271,831,255,186,1004,688,192,768],
[4677,467,14031,63,3647,28090,32300,18736,29120,32256],
[325,723,5583,63,3135,16058,15660,10800,13248,15360],
[10565,1235,975,63,6207,22202,31532,21552,26560,30720],
[197,5459,15567,63,3135,16186,10924,816,13248,15360],
[325,723,6607,63,2111,7866,7468,1584,6080,6144],
[197,339,527,63,1599,3898,3756,3376,2496,3584],
[1621,563,1551,3727,511,426,3532,368,2432,3584],
[597,51,527,1679,511,426,1996,368,1408,1536],
[597,563,527,1679,511,426,460,368,1408,1536],
[1573,1555,143,2703,1663,474,492,5488,6528,7680],
[5845,3507,15,41871,24703,59690,62028,23664,40832,57344],
[3445,21715,12303,975,61503,62090,43820,52272,4032,61440],
[10965,6579,16399,1935,49279,54570,58956,47216,16256,49152],
[21845,13107,61455,3855,255,43690,52428,240,3840,61440],
[13653,21299,49167,3855,255,51882,44236,12528,16128,49152],
[21845,13107,32783,3855,255,43690,52428,28912,32512,32768],
[10325,1331,6159,783,255,22442,31436,25840,18176,30720],
[169,2659,7,1567,511,8022,5396,5528,6624,7680],
[169,2659,1543,31,511,8022,5396,4504,6624,7680],
[169,2659,1543,1567,511,8022,5396,408,6624,7680],
[169,611,1543,3615,511,3926,3348,2456,480,3584],
[169,611,7,1567,511,1878,1300,1432,480,1536],
[297,2659,231,31,1567,7894,5268,5400,6624,7680],
[169,2595,2663,31,1567,8022,340,5528,6624,7680],
[105,1315,3879,31,799,3990,2708,216,3296,3840],
[41,395,103,743,415,982,84,280,608,896],
[41,939,7,743,415,982,84,280,608,896],
[85,131,2611,1551,511,8106,5452,6512,4480,7680],
[85,2691,1587,527,511,8106,332,5488,6528,7680],
[1621,2691,1587,527,511,426,332,5488,6528,7680],
[2581,9795,371,207,7743,30186,22668,22832,25024,32256],
[85,5251,691,399,3199,16298,10572,10864,13184,15360],
[6229,10499,1331,783,255,26538,21196,21744,26368,30720],
[29,35,2731,1639,7711,8162,5460,6552,480,7680],
[45,1091,347,3271,7231,8146,6820,4920,960,7168],
[85,2179,691,399,6271,8106,5452,5744,1920,6144],
[1397,18627,6163,975,14399,64138,42796,46128,51136,63488],
[2773,20867,51,1935,12415,62762,44620,43120,53120,61440],
[21845,13059,61491,3855,255,43690,3276,49392,3840,61440],
[5461,41731,24627,3855,255,60074,7372,20720,40704,57344],
[29,203,1483,775,1863,2018,564,184,1216,1792],
[793,203,1483,775,1863,230,564,184,1216,1792],
[5457,197,51,3087,1023,10794,10892,13104,13248,15360],
[44177,25989,7219,911,127,4714,17228,39024,58240,64512],
[1169,10629,6195,911,127,21098,25420,21616,26496,30720],
[51541,50355,17295,4223,13994,15180,48240,61312,12288,49152],
[51882,50777,49607,20543,13653,14758,15928,44992,12288,49152],
[38229,36019,33679,8319,27306,29516,31856,57216,24576,32768],
[43690,39321,34695,32895,21845,26214,30840,32640,16384,32768],
[21546,12953,12679,4223,3029,3430,3704,43904,52224,61440],
[10773,6476,6339,6207,21994,1715,1852,1472,26112,30720],
[1122,3241,5383,3103,925,854,10904,736,13056,15360]]
private def witnessCache : Array (List ℕ) := #[[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[0x82],
[],
[],
[],
[0x83],
[],
[],
[],
[],
[],
[],
[0x83],
[],
[0x43],
[],
[0x83],
[0x43],
[0x83],
[0x43],
[0xc3,0xce],
[0x843,0x84e],
[0x843,0x84e],
[0xc83,0xc8e],
[0x103,0x10e],
[0x103,0x10e],
[0xc83,0xc8e],
[0x983,0x98e],
[],
[],
[],
[],
[],
[0x83],
[0x43],
[0xc3],
[0xc3,0xce],
[0xc3,0xce],
[],
[],
[0x103,0x10e],
[0xc3,0xce],
[0x83,0x8e],
[],
[],
[],
[],
[],
[],
[0x84],
[0x44,0x64],
[0x104,0x10f,0x124],
[0x44,0x64],
[0x104,0x10f,0x124],
[0x844,0xc4f,0x9b,0xc64,0x872,0x75],
[0x1084,0x87,0x108f,0xc9b,0x9d,0xa1,0x10a4,0xcab,0xcad,0x10b2,0xcb5],
[0xc44,0xc4f,0x15b,0xc64,0xc72,0x75],
[0x1044,0x47,0x104f,0xc5b,0x5d,0x61,0x564,0xc6b,0xc6d,0x1072,0x575],
[0xa14c4,0x14c7,0xa14cf,0x10d1,0x150db,0x10dd,0x10e1,0xa14e4,0x10e7,0x10eb,0x150ed,0x214f2,0x214f5],
[0x1484,0x87,0x148f,0xc9b,0x9d,0xa1,0x14a4,0xcab,0xcad,0x14b2,0xcb5],
[0x18c4,0x18c7,0x18cf,0x14d1,0x18db,0x14dd,0x14e1,0x18e4,0x14e7,0x14eb,0x18ed,0x18f2,0x18f5],
[0x188550c4,0x150c7,0x10c9,0x9d0cf,0x150d1,0xd5,0x10d7,0x4d51b,0x50dd,0x950e1,0x91ce4,0xe5,0x150e7,0xea,0x14c52b,0x950ed,0x188550f2,0x9d0f5],
[0x10c4,0xd07,0xd0f,0x14d1,0xd1b,0xd1d,0x121,0xd24,0x14e7,0xd2b,0xd2d,0xd32,0xd35],
[0x18c4,0x14c7,0x18cf,0x10d1,0x18db,0x10dd,0x10e1,0x18e4,0x10e7,0x10eb,0x18ed,0x18f2,0x18f5],
[0x1904,0x190f,0x15b,0x1924,0x1932,0x135],
[0x44,0x64],
[0xc84,0x108f,0xdb,0x10a4,0xcb2,0xb5],
[0xc4,0xcf,0xdb,0xe4,0xf2,0x135],
[0x1884,0x1887,0x188f,0x1091,0x189b,0x109d,0x10a1,0x18a4,0x10a7,0x10ab,0x18ad,0x18b2,0x18b5],
[0x11c54c4,0x1894c7,0x14c9,0x11c54cf,0x104d1,0xd5,0x14d7,0x958db,0x8c55d,0x108c561,0x1145ce4,0xe5,0x104e7,0xea,0x10c56b,0x11894ed,0x11c54f2,0x1055cf5],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[0x84],
[0x204,0x20f,0x224],
[],
[0x44],
[0x44,0x4f,0x64],
[],
[0x84],
[0x44,0x64],
[0x204,0x20f,0x224],
[0x44],
[0x44,0x4f,0x64],
[0x84],
[0x204,0x20f,0x224],
[0x44],
[0x44,0x4f,0x64],
[0x44,0x64],
[0x204,0x20f,0x224],
[0x44,0x4f,0x64],
[0x204,0x20f,0x224],
[0x44,0x4f,0x64],
[0x104,0x10f,0x124],
[0x104,0x10f,0x9b,0x124,0x132,0x135],
[0x104,0x10f,0x9b,0x124,0x132,0x135],
[0x844,0xc8f,0x5b,0xca4,0x872,0xb5],
[0x104,0x87,0x10f,0x11b,0x9d,0xa1,0x124,0x12b,0x12d,0x132,0x135],
[0x844,0x84f,0x864],
[0x844,0x47,0x84f,0x85b,0x5d,0x61,0x864,0x86b,0x86d,0x872,0x875],
[0xc4,0xcf,0xe4],
[0x104,0x10f,0x5b,0x124,0x132,0xb5],
[0x104,0x10f,0x15b,0x124,0x132,0xb5],
[0x104,0x47,0x10f,0x11b,0x5d,0x61,0x124,0x12b,0x12d,0x132,0x135],
[0x844,0xc8f,0x5b,0xca4,0x872,0xb5],
[0x104,0x47,0x10f,0x11b,0x5d,0x61,0x124,0x12b,0x12d,0x132,0x135],
[0x104,0x87,0x10f,0x11b,0x9d,0xa1,0x124,0x12b,0x12d,0x132,0x135],
[0x844,0x47,0x84f,0x85b,0x5d,0x61,0x864,0x86b,0x86d,0x872,0x875],
[0x104,0x87,0x10f,0x11b,0x9d,0xa1,0x124,0x12b,0x12d,0x132,0x135],
[0xc4,0xcf,0xe4],
[0x104,0x107,0x10f,0x111,0x11b,0x11d,0x121,0x124,0x127,0x12b,0x12d,0x132,0x135],
[0x1444,0x847,0x144f,0x851,0x145b,0x85d,0x121,0x1464,0x867,0x146b,0x146d,0x1472,0x1475],
[0x44,0x64],
[0x144,0x14f,0x164],
[0x104,0x87,0x10f,0x11b,0x9d,0xa1,0x124,0x12b,0x12d,0x132,0x135],
[0x184,0x18f,0x15b,0x1a4,0x1b2,0x1f5],
[0x44,0x64],
[0x184,0x18f,0xdb,0x1a4,0x1b2,0x75],
[0x844,0x84f,0xdb,0x864,0x872,0x75],
[0x1944,0x21cf,0x15b,0x21e4,0x1972,0x1f5],
[0xc44,0x1c4f,0xdb,0x1c64,0xc72,0x75],
[0x844,0x84f,0xdb,0x864,0x872,0x75],
[0x10c4,0x10c7,0x14cf,0x14d1,0x14db,0x14dd,0xe1,0x14e4,0x14e7,0x14eb,0x14ed,0x14f2,0x14f5],
[0x14c4,0x14c7,0x14cf,0x14d1,0x14db,0x14dd,0xe1,0x14e4,0x14e7,0x14eb,0x14ed,0x14f2,0x14f5],
[0x1cc4,0x1907,0x190f,0x18d1,0x191b,0x191d,0x121,0x1924,0x18e7,0x192b,0x192d,0x1932,0x1935],
[0x1884,0x1487,0x188f,0xc91,0x189b,0xc9d,0xca1,0x18a4,0xca7,0xcab,0x18ad,0x18b2,0x18b5],
[0x14c4,0x1507,0x150f,0x18d1,0x151b,0x151d,0x121,0x1524,0x18e7,0x152b,0x152d,0x1532,0x1535],
[0xc84,0xc8f,0x15b,0xca4,0xcb2,0xb5],
[0x844,0x84f,0x15b,0x864,0x872,0x75],
[0xc44,0xc4f,0xc64],
[0x10c4,0x10cf,0x10e4],
[0xc44,0x47,0xc4f,0x85b,0x5d,0x61,0xc64,0x86b,0x86d,0xc72,0x875],
[0x10c4,0x87,0x1ccf,0xc9b,0x9d,0xa1,0x10e4,0xcab,0xcad,0x1cf2,0xcb5],
[0x144,0x14f,0x1db,0x164,0x172,0xb5],
[0x84,0x8f,0xa4],
[0x84,0x8f,0xa4],
[0x1884,0x87,0x188f,0xc9b,0x9d,0xa1,0x964,0xcab,0xcad,0x18b2,0x975],
[0xc84,0xc8f,0x15b,0xca4,0xcb2,0xb5],
[0x84,0x8f,0xa4],
[0xc44,0xc8f,0x5b,0xca4,0xc72,0xb5],
[0x1884,0x87,0x188f,0xc9b,0x9d,0xa1,0x18a4,0xcab,0xcad,0x18b2,0xcb5],
[0x844,0x84f,0x85b,0x864,0x872,0x75],
[0x144,0x14f,0x164],
[0x1484,0x87,0x148f,0xc9b,0x9d,0xa1,0x964,0xcab,0xcad,0x14b2,0x975],
[0x1884,0x87,0x188f,0xc9b,0x9d,0xa1,0x964,0xcab,0xcad,0x18b2,0x975],
[0x84,0x8f,0xa4],
[0x1884,0x87,0x188f,0xc9b,0x9d,0xa1,0x964,0xcab,0xcad,0x18b2,0x975],
[0x144,0x14f,0x164],
[0x1484,0x87,0x148f,0xc9b,0x9d,0xa1,0x964,0xcab,0xcad,0x14b2,0x975],
[0x10c4,0x10cf,0x10e4],
[0x10c4,0x87,0x1ccf,0xc9b,0x9d,0xa1,0x10e4,0xcab,0xcad,0x1cf2,0xcb5],
[0x1884,0x87,0x188f,0xc9b,0x9d,0xa1,0x1524,0xcab,0xcad,0x18b2,0x1535],
[0x1884,0x87,0x188f,0xc9b,0x9d,0xa1,0x964,0xcab,0xcad,0x18b2,0x975],
[0x1884,0x87,0x188f,0xc9b,0x9d,0xa1,0x18a4,0xcab,0xcad,0x18b2,0xcb5],
[0x1cc4,0x1907,0x190f,0x14d1,0x191b,0x191d,0x121,0x1924,0x14e7,0x192b,0x192d,0x1932,0x1935],
[0x1cc4,0x1507,0x150f,0x18d1,0x151b,0x151d,0x121,0x1524,0x18e7,0x152b,0x152d,0x1532,0x1535],
[0x1884,0xd47,0xd4f,0xc91,0xd5b,0xd5d,0x161,0xd64,0xca7,0xd6b,0xd6d,0xd72,0xd75],
[0x1884,0x907,0x90f,0xc91,0x91b,0x91d,0x121,0x924,0xca7,0x92b,0x92d,0x932,0x935],
[0x1cc4,0xd07,0xd0f,0x14d1,0xd1b,0xd1d,0x121,0xd24,0x14e7,0xd2b,0xd2d,0xd32,0xd35],
[0xc44,0x47,0xc4f,0x85b,0x5d,0x61,0xc64,0x86b,0x86d,0xc72,0x875],
[0x1884,0xc87,0x188f,0xc91,0x189b,0xc9d,0x14a1,0x18a4,0xca7,0x14ab,0x18ad,0x18b2,0x18b5],
[0x1944,0x1947,0x194f,0x1951,0x195b,0x195d,0x161,0x1964,0x1967,0x196b,0x196d,0x1972,0x1975],
[0x1044,0x47,0x104f,0x185b,0x5d,0x61,0x524,0x186b,0x186d,0x1072,0x535],
[0x10c4,0x1507,0x109,0x150f,0x1511,0xd5,0x117,0x151b,0x151d,0x1521,0x10e4,0xe5,0x1527,0xea,0x152b,0x152d,0x1532,0x1535],
[0x18c84,0x10c7,0x149,0x1948f,0x10d1,0xd5,0x157,0x1909b,0x94dd,0x8d61,0x18ca4,0xe5,0x10e7,0xea,0x996b,0x1896d,0x194b2,0x9975],
[0x10c4,0x1907,0x189,0x190f,0x1911,0xd5,0x197,0x191b,0x191d,0x121,0xd24,0xe5,0x1927,0xea,0x192b,0x192d,0x1932,0x1935],
[0xd44,0x10c7,0x10cf,0xd51,0x10db,0x10dd,0xe1,0x10e4,0xd67,0x10eb,0x10ed,0x10f2,0x10f5],
[0x104,0x87,0x10f,0x11b,0x9d,0xa1,0x124,0x12b,0x12d,0x132,0x135],
[0x1cc4,0x1907,0x190f,0x1cd1,0x191b,0x191d,0x121,0x1924,0x1ce7,0x192b,0x192d,0x1932,0x1935],
[0x1904,0x1907,0x189,0x190f,0x1911,0xd5,0x197,0x191b,0x191d,0x121,0x1924,0xe5,0x1927,0xea,0x192b,0x192d,0x1932,0x1935],
[0x1184,0x1907,0x1909,0x190f,0x1911,0xd5,0x1917,0x191b,0x191d,0x121,0x1924,0xe5,0x1927,0xea,0x192b,0x192d,0x1932,0x1935],
[0x10c4,0x87,0x1ccf,0xc9b,0x9d,0xa1,0x10e4,0xcab,0xcad,0x1cf2,0xcb5],
[0xe04,0xe0f,0xe24],
[0xe04,0x207,0xe0f,0xa1b,0x21d,0x221,0xe24,0xa2b,0xa2d,0xe32,0xa35],
[0x1504,0x1507,0x150f,0x1511,0x151b,0x151d,0x121,0x1524,0x1527,0x152b,0x152d,0x1532,0x1535],
[0x1044,0x47,0x104f,0x185b,0x5d,0x61,0x524,0x186b,0x186d,0x1072,0x535],
[0x1504,0x1507,0x149,0x150f,0x1511,0xd5,0x157,0x151b,0x151d,0x121,0x1524,0xe5,0x1527,0xea,0x152b,0x152d,0x1532,0x1535],
[0x1650c4,0xd87,0x150cf,0xd91,0x150db,0x10d9d,0x9a1,0x1650e4,0xda7,0x150eb,0x10dad,0x150f2,0x150f5],
[0x1d44,0x10c7,0x94f,0x10d1,0x95b,0x95d,0x161,0x1d64,0x10e7,0x96b,0x96d,0x972,0x975],
[0x10c4,0x10c7,0x10cf,0x10d1,0x10db,0x10dd,0xe1,0x10e4,0x10e7,0x10eb,0x10ed,0x10f2,0x10f5],
[0x1650c4,0x10c7,0x150cf,0x10d1,0x150db,0x150dd,0x8e1,0x1650e4,0x10e7,0x150eb,0x150ed,0x150f2,0x150f5],
[0x504,0x507,0x14c9,0x50f,0x1911,0xd5,0x14d7,0x191b,0x191d,0x121,0x1924,0xe5,0x1927,0xea,0x192b,0x192d,0x1932,0x1935],
[0x1650c4,0x10c7,0xc89,0x1650cf,0x10d1,0x95,0xc97,0x14d1b,0x114dd,0x150e1,0xc9a4,0xa5,0x10e7,0xaa,0x150eb,0x150ed,0x94d32,0x98f5],
[0x1444,0x847,0x144f,0x851,0x145b,0x85d,0x1061,0x1464,0x867,0x106b,0x146d,0x1472,0x1475],
[0x1444,0x847,0x144f,0x851,0x145b,0x85d,0x1061,0x1464,0x867,0x106b,0x146d,0x1472,0x1475],
[0x1884,0xc7,0x10cf,0x10db,0xdd,0xe1,0x18a4,0x10ab,0x10ed,0x10f2,0x10f5],
[0x1444,0x87,0x150f,0x109b,0x9d,0xa1,0x1464,0xc6b,0x10ad,0x1532,0x10b5],
[0x10c4,0x87,0x150f,0x109b,0x9d,0xa1,0x10e4,0x10ab,0x10ad,0x1532,0x10b5],
[0x1444,0xc47,0x144f,0xc51,0x145b,0xc5d,0x1061,0x1464,0xc67,0x106b,0x146d,0x1472,0x1475],
[0x1884,0xd07,0xd0f,0xc91,0x189b,0xc9d,0x14a1,0x18a4,0xca7,0x14ab,0x18ad,0x18b2,0xd35],
[0x1444,0x847,0x144f,0x851,0x145b,0x85d,0x1461,0x1464,0x867,0x146b,0x146d,0x1472,0x1475],
[0x1444,0x847,0x144f,0x851,0x145b,0x85d,0x1061,0x1464,0x867,0x106b,0x146d,0x1472,0x1475],
[0x1884,0xc87,0x188f,0xc91,0x189b,0xc9d,0x10a1,0x18a4,0xca7,0x10ab,0x18ad,0x18b2,0x18b5],
[0xc44,0x47,0xc4f,0x85b,0x5d,0x61,0xc64,0x86b,0x86d,0xc72,0x875],
[0x104,0x10f,0x11b,0x124,0x132,0x175],
[0xc4,0xc7,0xcf,0xdb,0xdd,0xe1,0xe4,0xeb,0xed,0xf2,0xf5],
[0x104,0x107,0x10f,0x111,0x11b,0x11d,0xe1,0x124,0x127,0x12b,0x12d,0x132,0x135],
[0x44,0x64],
[0x1884,0x194f,0x9b,0x1964,0x18b2,0x175],
[0x844,0x47,0x84f,0x85b,0x5d,0x61,0x864,0x86b,0x86d,0x872,0x875],
[0xc84,0x10cf,0x9b,0x10e4,0xcb2,0xf5],
[0x1444,0x47,0x144f,0xc5b,0x5d,0x61,0x1464,0xc6b,0xc6d,0x1472,0xc75],
[0x1c84,0x87,0x148f,0x209b,0x9d,0xa1,0x964,0x1cab,0x20ad,0x14b2,0x975],
[0x1c84,0x1c87,0x1c8f,0x1091,0x1c9b,0x109d,0x10a1,0x1ca4,0x10a7,0x10ab,0x1cad,0x1cb2,0x1cb5],
[0x10c4,0x47,0x10cf,0xc5b,0x5d,0x61,0x10e4,0xc6b,0xc6d,0x10f2,0xc75],
[0x1884,0x87,0x188f,0x189b,0x9d,0xa1,0x964,0x18ab,0x18ad,0x18b2,0x975],
[0xc84,0x87,0xc8f,0xc9b,0x9d,0xa1,0x964,0xcab,0xcad,0xcb2,0x975],
[0x1844,0x10cf,0x5b,0x10e4,0x1872,0xf5],
[0xc84,0x14cf,0x9b,0x14e4,0xcb2,0xf5],
[0x1884,0x194f,0x9b,0x1964,0x18b2,0x175],
[0xc84,0x10cf,0x9b,0x10e4,0xcb2,0xf5],
[0x1444,0x10cf,0x5b,0x10e4,0x1472,0xf5],
[0xc84,0x87,0xc8f,0xc9b,0x9d,0xa1,0x964,0xcab,0xcad,0xcb2,0x975],
[0x1c84,0x1c87,0x1c8f,0x1491,0x1c9b,0x149d,0x14a1,0x1ca4,0x14a7,0x14ab,0x1cad,0x1cb2,0x1cb5],
[0xc84,0x87,0xc8f,0xc9b,0x9d,0xa1,0xca4,0xcab,0xcad,0xcb2,0xcb5],
[0x1c84,0x1507,0x150f,0x1c91,0x1c9b,0x1c9d,0x1ca1,0x1ca4,0x1ca7,0x1cab,0x1cad,0x1cb2,0x1535],
[0x1584,0x1947,0x149,0x194f,0x1951,0xd5,0x157,0x195b,0x195d,0x1961,0x15a4,0xe5,0x1967,0xea,0x196b,0x196d,0x1972,0x1975],
[0x1950c84,0x150c7,0x10c9,0xa550f,0x150d1,0xd5,0x10d7,0x1950db,0x150dd,0x25950e1,0x1950ca4,0xe5,0x150e7,0xea,0x1950eb,0x25914ed,0x9950f2,0xa5535],
[0x1884,0x1887,0x188f,0x1491,0x189b,0x149d,0x14a1,0x18a4,0x14a7,0x14ab,0x18ad,0x18b2,0x18b5],
[0xe04,0x207,0xe0f,0xa1b,0x21d,0x221,0xe24,0xa2b,0xa2d,0xe32,0xa35],
[0xa04,0x148f,0x21b,0x14a4,0xa32,0xb5],
[0xa04,0x207,0xa0f,0xa1b,0x21d,0x221,0xa24,0xa2b,0xa2d,0xa32,0xa35],
[0x125484,0x125487,0x109,0x16490f,0x14911,0x95,0x117,0x16491b,0x16491d,0x14921,0x1650a4,0xa5,0x14927,0xaa,0x1650ab,0x16492d,0x164932,0x164935],
[0x251cc4,0x10c7,0x89,0x25d0cf,0x10d1,0xd5,0x97,0x255cdb,0x108dd,0x10ca1,0x25d0e4,0xe5,0x10e7,0xea,0x1490eb,0x14d0ad,0x19490f2,0x1490f5],
[0x1e5484,0x1087,0xc89,0x1e548f,0x1091,0x95,0xc97,0x254c9b,0x1149d,0xd0a1,0x1650a4,0xa5,0x10a7,0xaa,0x150ab,0x150ad,0x1650b2,0x150b5],
[0x1504,0x1507,0x109,0x150f,0x1511,0x95,0x117,0x151b,0x151d,0x1521,0x1524,0xa5,0x1527,0xaa,0x152b,0x152d,0x1532,0x1535],
[0x259484,0xc87,0x149,0x25894f,0xc91,0x95,0x157,0x1d209b,0xd49d,0xc961,0x1e0ca4,0xa5,0xca7,0xaa,0x114cab,0x108d6d,0x514cb2,0x114cb5],
[0xc84,0x47,0xc8f,0x85b,0x5d,0x61,0xca4,0x86b,0x86d,0xcb2,0x875],
[0x1044,0x104f,0xdb,0x1064,0x1072,0x75],
[0x44,0x4f,0x64],
[0x18c4,0x18cf,0xdb,0x18e4,0x10f2,0x175],
[0x1d04,0x10c7,0x1d0f,0x10d1,0x1d1b,0x10dd,0x1ce1,0x1d24,0x10e7,0x1ceb,0x1d2d,0x1d32,0x1d35],
[0xc84,0x108f,0xdb,0x10a4,0xcb2,0xb5],
[0x1444,0xc47,0x144f,0xc51,0x145b,0xc5d,0x1461,0x1464,0xc67,0x146b,0x146d,0x1472,0x1475],
[0x1d04,0x107,0x1d0f,0x151b,0x11d,0x121,0x1d24,0x14eb,0x152d,0x1d32,0x1535],
[0xc44,0x47,0xc4f,0x85b,0x5d,0x61,0xc64,0x86b,0x86d,0xc72,0x875],
[0x14c4,0x14c7,0x14cf,0x14d1,0x14db,0x14dd,0x14e1,0x14e4,0x14e7,0x14eb,0x14ed,0x14f2,0x14f5],
[0x218c84,0x947,0xe0490f,0xc91,0x20c9b,0xc9d,0x10e1,0x218ca4,0xca7,0x10eb,0x20cad,0x20cb2,0x20cb5],
[0x1444,0x1047,0x144f,0x851,0x145b,0x85d,0x861,0x1464,0x867,0x86b,0x146d,0x1472,0x1475],
[0x44,0x64],
[0x84,0x8f,0xa4],
[0x1844,0x1c4f,0x11b,0x1c64,0x1872,0x75],
[0x1444,0x144f,0x1464],
[0x850c4,0x150c7,0x10c9,0x1d88550cf,0x150d1,0xd5,0x10d7,0x10c55b,0x150dd,0x90c561,0x1d8850e4,0xe5,0x150e7,0xea,0x50d6b,0x1d854ed,0x1d8550f2,0x1d88550f5],
[0x1d044,0x47,0x1ca104f,0x145b,0x5d,0x61,0x1ca1064,0x146b,0x146d,0x19472,0x1475],
[],
[],
[],
[],
[],
[],
[0x84],
[0x44,0x64],
[0x244,0x24f,0x264],
[0x44],
[0x44,0x4f,0x64],
[0x104],
[0x104,0x10f,0x124],
[0x104,0x10f,0x9b,0x124,0x132,0x135],
[0x104,0x10f,0x5b,0x124,0x132,0xb5],
[0x104,0x47,0x10f,0x11b,0x5d,0x61,0x124,0x12b,0x12d,0x132,0x135],
[0x104,0x10f,0x124],
[0x104,0x47,0x10f,0x11b,0x5d,0x61,0x124,0x12b,0x12d,0x132,0x135],
[0x104,0x87,0x10f,0x11b,0x9d,0xa1,0x124,0x12b,0x12d,0x132,0x135],
[0x104,0x107,0x10f,0x111,0x11b,0x11d,0x121,0x124,0x127,0x12b,0x12d,0x132,0x135],
[0x104,0x107,0x10f,0x111,0x11b,0x11d,0x121,0x124,0x127,0x12b,0x12d,0x132,0x135],
[],
[],
[],
[0x44,0x4f,0x64],
[0x144,0x14f,0x15b,0x164,0x172,0x235],
[0x144,0x14f,0xdb,0x164,0x172,0x75],
[0xc4,0xc7,0xcf,0xdb,0xdd,0xe1,0xe4,0xeb,0xed,0xf2,0xf5],
[0x144,0x147,0x14f,0x151,0x15b,0x15d,0xe1,0x164,0x167,0x16b,0x16d,0x172,0x175],
[0x144,0x147,0x14f,0x151,0x15b,0x15d,0xe1,0x164,0x167,0x16b,0x16d,0x172,0x175],
[0x144,0x147,0xc9,0x14f,0x151,0x155,0xd7,0x15b,0x15d,0x161,0x164,0x165,0x167,0x16a,0x16b,0x16d,0x172,0x175],
[0x10c4,0x10c7,0x10cf,0x10d1,0x10db,0x10dd,0xe1,0x10e4,0x10e7,0x10eb,0x10ed,0x10f2,0x10f5],
[0x15c4,0x10c7,0xc9,0x194f,0x1951,0x1d5,0xd7,0x195b,0x195d,0x161,0x1964,0x1e5,0x1967,0x1ea,0x196b,0x196d,0x1972,0x1975],
[0x144,0x14f,0x21b,0x164,0x172,0xb5],
[0x144,0x14f,0x164],
[0x84,0x8f,0xa4],
[0x144,0x87,0x14f,0x15b,0x9d,0xa1,0x164,0x16b,0x16d,0x172,0x175],
[0x144,0x87,0x14f,0x15b,0x9d,0xa1,0x164,0x16b,0x16d,0x172,0x175],
[0x104,0x10f,0x124],
[0x144,0x87,0x14f,0x15b,0x9d,0xa1,0x164,0x16b,0x16d,0x172,0x175],
[0x20c4,0x1507,0x150f,0x20d1,0x151b,0x151d,0x121,0x1524,0x20e7,0x152b,0x152d,0x1532,0x1535],
[0x1c84,0x1507,0x150f,0xc91,0x151b,0x151d,0x121,0x1524,0xca7,0x152b,0x152d,0x1532,0x1535],
[0xc44,0x47,0xc4f,0x85b,0x5d,0x61,0x1524,0x86b,0x86d,0xc72,0x1535],
[0x10c4,0x1507,0x150f,0x1511,0x151b,0x151d,0x121,0x1524,0x1527,0x152b,0x152d,0x1532,0x1535],
[0x1c4,0x47,0x1cf,0x1db,0x5d,0x61,0x1e4,0x1eb,0x1ed,0x1f2,0x1f5],
[0x10c4,0x1507,0x109,0x114f,0x1151,0xd5,0x117,0x115b,0x115d,0x161,0x1164,0xe5,0x1167,0xea,0x116b,0x116d,0x1172,0x1175],
[0x10c4,0x1507,0x109,0x114f,0x1151,0xd5,0x117,0x115b,0x115d,0x161,0x1d64,0xe5,0x1167,0xea,0x116b,0x116d,0x1172,0x1175],
[0x10c4,0x1507,0x1c9,0x150f,0x1511,0xd5,0x1d7,0x151b,0x151d,0x121,0x1524,0xe5,0x1527,0xea,0x152b,0x152d,0x1532,0x1535],
[0x44,0x64],
[0x204,0x20f,0x224],
[0x44,0x64],
[0xc4,0xcf,0xe4],
[0xc4,0xcf,0x9b,0xe4,0xf2,0xf5],
[0x1484,0x87,0x148f,0xc9b,0x9d,0xa1,0x1964,0xcab,0xcad,0x14b2,0x1975],
[0x144,0x87,0x14f,0x15b,0x9d,0xa1,0x164,0x16b,0x16d,0x172,0x175],
[0x144,0x147,0x14f,0x151,0x15b,0x15d,0x161,0x164,0x167,0x16b,0x16d,0x172,0x175],
[0x144,0x147,0x14f,0x151,0x15b,0x15d,0x161,0x164,0x167,0x16b,0x16d,0x172,0x175],
[0x144,0x14f,0x19b,0x164,0x172,0x75],
[],
[],
[],
[],
[],
[],
[0x44,0x64],
[0x144,0x14f,0x9b,0x164,0x172,0x1f5],
[0x144,0x14f,0x9b,0x164,0x172,0xf5],
[0x144,0x14f,0x9b,0x164,0x172,0xf5],
[0x144,0x87,0x14f,0x15b,0x9d,0xa1,0x164,0x16b,0x16d,0x172,0x175],
[0x144,0x147,0x14f,0x151,0x15b,0x15d,0x161,0x164,0x167,0x16b,0x16d,0x172,0x175],
[0x184,0x18f,0x9b,0x1a4,0x1b2,0x135],
[0x184,0x18f,0x21b,0x1a4,0x1b2,0xb5],
[0x1c84,0x87,0x1c8f,0x109b,0x9d,0xa1,0x18e4,0x10ab,0x10ad,0x1cb2,0x18f5],
[0x1484,0x1907,0x109,0x190f,0x1911,0x95,0x117,0x191b,0x191d,0x1921,0x14a4,0xa5,0x1927,0xaa,0x192b,0x192d,0x1932,0x1935],
[0x1084,0x1087,0x89,0x108f,0x1091,0x1095,0x97,0x109b,0x109d,0x10a1,0x10a4,0x10a5,0x10a7,0x10aa,0x10ab,0x10ad,0x10b2,0x10b5],
[0x144,0x14f,0xdb,0x164,0x172,0x175],
[0x144,0x14f,0xdb,0x164,0x172,0xb5],
[0x144,0x14f,0x5b,0x164,0x172,0xb5],
[0x44,0x64],
[0x84,0x8f,0xa4],
[0x44,0x64],
[0x144,0x14f,0x1db,0x164,0x172,0x175],
[0x144,0x14f,0xdb,0x164,0x172,0x175],
[0x144,0x14f,0xdb,0x164,0x172,0x175],
[0x44],
[0x44],
[],
[],
[0xc84,0x14c7,0x14cf,0x1091,0xc9b,0x109d,0x10a1,0xca4,0x10a7,0x10ab,0xcad,0xcb2,0x14f5],
[0x1844,0x14c7,0x14cf,0x851,0x185b,0x85d,0x861,0x1864,0x867,0x86b,0x186d,0x1872,0x14f5],
[0x144,0x14f,0x164],
[],
[0x84,0xa4],
[],
[],
[],
[],
[0x44],
[0x44,0x64],
[0x1084,0x108f,0x18a4]]


private def runProofCase (_rep ci : ℕ) (h : PackedShape) (cs : List ℕ) (t : ℕ)
    (rows mis pat wit : List ℕ) :=
  if classWeightCalc cs > 2*(t-1) || mis.length > cs.length then true else
  let hw := (wit.find? (fun w => w % 64 == ci)).getD 0
  let W := decodedVertices 10 (hw >>> 6)
  (h.1 != []) && W.all (· < rows.length) &&
    !(packedVerify h.1 (2^mis.length-1) (2^cs.length-1) (fun v => pat.getD v 0)
      (fun v => rows.getD v 0) W (cornerTable h cs.length) (cacheRow h cs.length (2^cs.length-1)))

private def checkRepCase (rep ci : ℕ) :=
  let info := andCatalogue[rep]?.getD (0,[])
  runProofCase rep ci (cachedShapes[ci]?.getD ([],#[],0)) (shapeClasses[ci]?.getD []) info.1 info.2
    (cachedMIS[rep]?.getD []) (patternCache[rep]?.getD []) (witnessCache[rep]?.getD [])


private def repFacts (ri : ℕ) :=
  let rows := (andCatalogue[ri]?.getD (0,[])).2
  let ms := cachedMIS[ri]?.getD []
  let pat := patternCache[ri]?.getD []
  decide ms.Nodup && ms.all (fun m => (m < 2^rows.length) && rowMaskOK rows.length rows m) &&
    (List.range rows.length).all (fun v => pat.getD v 0 ==
      corner.packBits 16 (fun i => (ms.getD i 0).testBit v))

private def shapeFacts (ci : ℕ) :=
  let cs := shapeClasses[ci]?.getD []
  let h := cachedShapes[ci]?.getD ([],#[],0)
  (classWeightCalc cs == (classUses cs).card) &&
  (h.1.isEmpty ||
    (((List.range 256).all (fun p => h.1.contains (corner.profileNumber cs p))) &&
     (cacheRow h cs.length (2^cs.length-1) == packRows h.1 (2^cs.length-1) (2^cs.length-1)) &&
     (List.range h.1.length).all fun i => cornerTable h cs.length i ==
        packRows h.1 (2^cs.length-1) (h.1.getD i 0)))

private def verifiedRep (ri : ℕ) :=
  repFacts ri && (List.range 57).all (checkRepCase ri)

private def columnPack (host : List ℕ) (g : ℕ → ℕ) := packLanes (host.map g)

private theorem columnPack_add (h : List ℕ) (a b : ℕ → ℕ) :
    columnPack h (fun w => a w + b w) = columnPack h a + columnPack h b := by
  induction h with
  | nil => simp [columnPack,packLanes]
  | cons w h ih =>
    simp only [columnPack,List.map_cons,packLanes] at ih ⊢
    rw [ih,Nat.mul_add]
    omega

private theorem columnPack_const (h : List ℕ) (a : ℕ) :
    columnPack h (fun _ => a) = ones h.length * a := by
  induction h with
  | nil => simp [columnPack,packLanes,ones]
  | cons w h ih =>
    simp only [columnPack,List.map_cons,packLanes,ones,List.length_cons,List.replicate_succ] at ih ⊢
    rw [ih]
    ring

private theorem columnPack_congr (h : List ℕ) (a b : ℕ → ℕ) (hw : ∀ w ∈ h, a w = b w) :
    columnPack h a = columnPack h b := by
  exact congrArg packLanes (List.map_congr_left hw)

private theorem columnPack_merge (h : List ℕ) (a b c : ℕ → ℕ) (hw : ∀ w ∈ h, a w+b w=c w) :
    columnPack h a + columnPack h b = columnPack h c := by
  rw [← columnPack_add]
  exact columnPack_congr _ _ _ hw

private theorem cacheColumn_sum (h : PackedShape) (x b : ℕ)
    (valid : ∀ i < b, h.2.1[i]?.getD 0 = columnPack h.1 (fun w => (w.testBit i).toNat)) :
    sumSources b x h.2.1 = columnPack h.1
      (fun w => ∑ i : Fin b, ((x &&& w).testBit i.val).toNat) := by
  induction b with
  | zero => simp [sumSources,columnPack_const]
  | succ k ih =>
    have step : sumSources (k+1) x h.2.1 = sumSources k x h.2.1 +
        (if x.testBit k then h.2.1[k]?.getD 0 else 0) := by
      cases hk : x.testBit k <;> simp [sumSources,List.range_succ,List.filter_append,List.foldl_append,hk]
    simp_rw [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    rw [step,ih (fun i hi => valid i (by omega)),columnPack_add]
    cases hk : x.testBit k with
    | true => simp [hk,valid k (by omega),Nat.testBit_and]
    | false => simp [hk,Nat.testBit_and,columnPack_const]

private theorem weight_split (u w : ℕ) :
    weight (u &&& w) + weight (withoutBits u w) = weight u := by
  have pos : sites (u &&& w) = (sites u).filter (fun i => w.testBit i.val = true) := by
    ext i
    simp [sites,Nat.testBit_and]
  have neg : sites (withoutBits u w) = (sites u).filter (fun i => ¬ w.testBit i.val = true) := by
    ext i
    simp [sites,bit_without]
  simp only [weight_spec,pos,neg]
  exact Finset.card_filter_add_card_filter_not _

private theorem minus_beneath (f u w : ℕ) (hw : f &&& w = w) :
    withoutBits f u &&& w = withoutBits w u := by
  apply Nat.eq_of_testBit_eq
  intro i
  have H := congrArg (fun m : ℕ => m.testBit i) hw
  simp only [Nat.testBit_and,bit_without] at H ⊢
  cases hwbit : w.testBit i <;> cases hubit : u.testBit i <;> cases hfbit : f.testBit i <;> simp_all

private theorem columnCache_correct (h : PackedShape) (k f u : ℕ)
    (bitcols : ∀ i < 16, h.2.1[i]?.getD 0 = columnPack h.1 (fun w => (w.testBit i).toNat))
    (total : h.2.2 = columnPack h.1 weight)
    (hfull : weight f = k)
    (hu : f &&& u = u) (hh : ∀ w ∈ h.1, f &&& w = w) :
    cacheRow h k u = packRows h.1 f u := by
  let A (w : ℕ) := (requirements f u w).1
  let B (w : ℕ) := (requirements f u w).2.1
  let D (w : ℕ) := (requirements f u w).2.2.1
  let E (w : ℕ) := (requirements f u w).2.2.2
  have q : sumSources 16 u h.2.1 = columnPack h.1 A := by
    rw [cacheColumn_sum _ _ _ bitcols]
    apply columnPack_congr
    intro w _
    simp only [A,requirements,hu,weight_spec,sites,Finset.card_filter,Bool.toNat]
    apply Finset.sum_congr rfl
    intro i _
    cases (u &&& w).testBit i.val <;> rfl
  have ab : columnPack h.1 A + columnPack h.1 B = ones h.1.length * weight u := by
    rw [← columnPack_const]
    exact columnPack_merge _ _ _ _ (fun w _ => by simpa [A,B,requirements,hu] using weight_split u w)
  have ad : columnPack h.1 A + columnPack h.1 D = h.2.2 := by
    rw [total]
    exact columnPack_merge _ _ _ _ (fun w hw => by
      simpa only [A,D,requirements,hu,minus_beneath _ _ _ (hh _ hw),Nat.and_comm w u] using weight_split w u)
  have de : columnPack h.1 D + columnPack h.1 E = ones h.1.length * (k-weight u) := by
    have sub : weight (withoutBits f u) = k-weight u := by
      have H := weight_split f u
      rw [hu,hfull] at H
      omega
    rw [← columnPack_const,← sub]
    exact columnPack_merge _ _ _ _ (fun w _ => weight_split (withoutBits f u) w)
  change (sumSources 16 u h.2.1,_,_,_) =
    (columnPack h.1 A,columnPack h.1 B,columnPack h.1 D,columnPack h.1 E)
  simp only [q,Prod.mk.injEq,true_and]
  omega


private def cheapShape (ci : ℕ) :=
  let cs := shapeClasses[ci]?.getD []
  let h := cachedShapes[ci]?.getD ([],#[],0)
  let f := 2^cs.length - 1
  (classWeightCalc cs == (classUses cs).card) &&
  (h.1.isEmpty ||
    (((List.range 256).all (fun p => h.1.contains (corner.profileNumber cs p))) &&
      (weight f == cs.length) && h.1.all (fun u => f &&& u == u) &&
      (h.2.2 == columnPack h.1 weight) &&
      (List.range 16).all (fun i => h.2.1[i]?.getD 0 ==
        columnPack h.1 (fun w => (w.testBit i).toNat))))


private theorem cheapShape_sound (ci : ℕ) (ok : cheapShape ci = true) : shapeFacts ci = true := by
  let h := cachedShapes[ci]?.getD ([],#[],0)
  let cs := shapeClasses[ci]?.getD []
  let f := 2^cs.length-1
  simp only [cheapShape,Bool.and_eq_true,Bool.or_eq_true,List.all_eq_true,List.mem_range,
    beq_iff_eq] at ok
  simp only [shapeFacts,Bool.and_eq_true,Bool.or_eq_true,List.all_eq_true,List.mem_range,
    beq_iff_eq]
  refine ⟨ok.1,ok.2.imp_right ?_⟩
  rintro ⟨⟨⟨⟨host,full⟩,bounds⟩,total⟩,bits⟩
  let model u (hu : f &&& u = u) := columnCache_correct h cs.length f u bits total full hu bounds
  refine ⟨⟨host,model f (Nat.and_self _)⟩,?_⟩
  intro i hi
  change cacheRow h cs.length (h.1.getD i 0) = packRows h.1 f (h.1.getD i 0)
  apply model
  rw [List.getD_eq_getElem _ _ hi]
  exact bounds _ (List.getElem_mem _)


set_option maxRecDepth 65536 in
set_option maxHeartbeats 48000000 in
private theorem cheapShape_all : (List.range 57).all cheapShape = true := by decide +kernel

private theorem cacheOK_all (i : ℕ) (hi : i < 57) : shapeFacts i = true :=
  cheapShape_sound i (List.all_eq_true.mp cheapShape_all i (List.mem_range.mpr hi))


set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_0 : ((List.range 8).all fun i => verifiedRep (0+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_8 : ((List.range 8).all fun i => verifiedRep (8+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_16 : ((List.range 8).all fun i => verifiedRep (16+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_24 : ((List.range 8).all fun i => verifiedRep (24+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_32 : ((List.range 8).all fun i => verifiedRep (32+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_40 : ((List.range 8).all fun i => verifiedRep (40+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_48 : ((List.range 8).all fun i => verifiedRep (48+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_56 : ((List.range 8).all fun i => verifiedRep (56+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_64 : ((List.range 8).all fun i => verifiedRep (64+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_72 : ((List.range 8).all fun i => verifiedRep (72+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_80 : ((List.range 8).all fun i => verifiedRep (80+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_88 : ((List.range 8).all fun i => verifiedRep (88+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_96 : ((List.range 8).all fun i => verifiedRep (96+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_104 : ((List.range 8).all fun i => verifiedRep (104+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_112 : ((List.range 8).all fun i => verifiedRep (112+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_120 : ((List.range 8).all fun i => verifiedRep (120+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_128 : ((List.range 8).all fun i => verifiedRep (128+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_136 : ((List.range 8).all fun i => verifiedRep (136+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_144 : ((List.range 8).all fun i => verifiedRep (144+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_152 : ((List.range 8).all fun i => verifiedRep (152+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_160 : ((List.range 8).all fun i => verifiedRep (160+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_168 : ((List.range 8).all fun i => verifiedRep (168+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_176 : ((List.range 8).all fun i => verifiedRep (176+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_184 : ((List.range 8).all fun i => verifiedRep (184+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_192 : ((List.range 8).all fun i => verifiedRep (192+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_200 : ((List.range 8).all fun i => verifiedRep (200+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_208 : ((List.range 8).all fun i => verifiedRep (208+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_216 : ((List.range 8).all fun i => verifiedRep (216+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_224 : ((List.range 8).all fun i => verifiedRep (224+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_232 : ((List.range 8).all fun i => verifiedRep (232+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_240 : ((List.range 8).all fun i => verifiedRep (240+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_248 : ((List.range 8).all fun i => verifiedRep (248+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_256 : ((List.range 8).all fun i => verifiedRep (256+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_264 : ((List.range 8).all fun i => verifiedRep (264+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_272 : ((List.range 8).all fun i => verifiedRep (272+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_280 : ((List.range 8).all fun i => verifiedRep (280+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_288 : ((List.range 8).all fun i => verifiedRep (288+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_296 : ((List.range 8).all fun i => verifiedRep (296+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_304 : ((List.range 8).all fun i => verifiedRep (304+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_312 : ((List.range 8).all fun i => verifiedRep (312+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_320 : ((List.range 8).all fun i => verifiedRep (320+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_328 : ((List.range 8).all fun i => verifiedRep (328+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_336 : ((List.range 8).all fun i => verifiedRep (336+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_344 : ((List.range 8).all fun i => verifiedRep (344+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_352 : ((List.range 8).all fun i => verifiedRep (352+i)) = true := by decide +kernel

set_option maxHeartbeats 48000000 in
set_option maxRecDepth 65536 in
private theorem repOK_360 : ((List.range 1).all fun i => verifiedRep (360+i)) = true := by decide +kernel

private theorem repOK_all (i : ℕ) (hi : i < 361) : verifiedRep i = true := by

  by_cases z0 : i < 8

  · have h := List.all_eq_true.mp repOK_0 (i-0) (List.mem_range.mpr (by omega))

    simpa only [show 0+(i-0)=i by omega] using h

  by_cases z8 : i < 16

  · have h := List.all_eq_true.mp repOK_8 (i-8) (List.mem_range.mpr (by omega))

    simpa only [show 8+(i-8)=i by omega] using h

  by_cases z16 : i < 24

  · have h := List.all_eq_true.mp repOK_16 (i-16) (List.mem_range.mpr (by omega))

    simpa only [show 16+(i-16)=i by omega] using h

  by_cases z24 : i < 32

  · have h := List.all_eq_true.mp repOK_24 (i-24) (List.mem_range.mpr (by omega))

    simpa only [show 24+(i-24)=i by omega] using h

  by_cases z32 : i < 40

  · have h := List.all_eq_true.mp repOK_32 (i-32) (List.mem_range.mpr (by omega))

    simpa only [show 32+(i-32)=i by omega] using h

  by_cases z40 : i < 48

  · have h := List.all_eq_true.mp repOK_40 (i-40) (List.mem_range.mpr (by omega))

    simpa only [show 40+(i-40)=i by omega] using h

  by_cases z48 : i < 56

  · have h := List.all_eq_true.mp repOK_48 (i-48) (List.mem_range.mpr (by omega))

    simpa only [show 48+(i-48)=i by omega] using h

  by_cases z56 : i < 64

  · have h := List.all_eq_true.mp repOK_56 (i-56) (List.mem_range.mpr (by omega))

    simpa only [show 56+(i-56)=i by omega] using h

  by_cases z64 : i < 72

  · have h := List.all_eq_true.mp repOK_64 (i-64) (List.mem_range.mpr (by omega))

    simpa only [show 64+(i-64)=i by omega] using h

  by_cases z72 : i < 80

  · have h := List.all_eq_true.mp repOK_72 (i-72) (List.mem_range.mpr (by omega))

    simpa only [show 72+(i-72)=i by omega] using h

  by_cases z80 : i < 88

  · have h := List.all_eq_true.mp repOK_80 (i-80) (List.mem_range.mpr (by omega))

    simpa only [show 80+(i-80)=i by omega] using h

  by_cases z88 : i < 96

  · have h := List.all_eq_true.mp repOK_88 (i-88) (List.mem_range.mpr (by omega))

    simpa only [show 88+(i-88)=i by omega] using h

  by_cases z96 : i < 104

  · have h := List.all_eq_true.mp repOK_96 (i-96) (List.mem_range.mpr (by omega))

    simpa only [show 96+(i-96)=i by omega] using h

  by_cases z104 : i < 112

  · have h := List.all_eq_true.mp repOK_104 (i-104) (List.mem_range.mpr (by omega))

    simpa only [show 104+(i-104)=i by omega] using h

  by_cases z112 : i < 120

  · have h := List.all_eq_true.mp repOK_112 (i-112) (List.mem_range.mpr (by omega))

    simpa only [show 112+(i-112)=i by omega] using h

  by_cases z120 : i < 128

  · have h := List.all_eq_true.mp repOK_120 (i-120) (List.mem_range.mpr (by omega))

    simpa only [show 120+(i-120)=i by omega] using h

  by_cases z128 : i < 136

  · have h := List.all_eq_true.mp repOK_128 (i-128) (List.mem_range.mpr (by omega))

    simpa only [show 128+(i-128)=i by omega] using h

  by_cases z136 : i < 144

  · have h := List.all_eq_true.mp repOK_136 (i-136) (List.mem_range.mpr (by omega))

    simpa only [show 136+(i-136)=i by omega] using h

  by_cases z144 : i < 152

  · have h := List.all_eq_true.mp repOK_144 (i-144) (List.mem_range.mpr (by omega))

    simpa only [show 144+(i-144)=i by omega] using h

  by_cases z152 : i < 160

  · have h := List.all_eq_true.mp repOK_152 (i-152) (List.mem_range.mpr (by omega))

    simpa only [show 152+(i-152)=i by omega] using h

  by_cases z160 : i < 168

  · have h := List.all_eq_true.mp repOK_160 (i-160) (List.mem_range.mpr (by omega))

    simpa only [show 160+(i-160)=i by omega] using h

  by_cases z168 : i < 176

  · have h := List.all_eq_true.mp repOK_168 (i-168) (List.mem_range.mpr (by omega))

    simpa only [show 168+(i-168)=i by omega] using h

  by_cases z176 : i < 184

  · have h := List.all_eq_true.mp repOK_176 (i-176) (List.mem_range.mpr (by omega))

    simpa only [show 176+(i-176)=i by omega] using h

  by_cases z184 : i < 192

  · have h := List.all_eq_true.mp repOK_184 (i-184) (List.mem_range.mpr (by omega))

    simpa only [show 184+(i-184)=i by omega] using h

  by_cases z192 : i < 200

  · have h := List.all_eq_true.mp repOK_192 (i-192) (List.mem_range.mpr (by omega))

    simpa only [show 192+(i-192)=i by omega] using h

  by_cases z200 : i < 208

  · have h := List.all_eq_true.mp repOK_200 (i-200) (List.mem_range.mpr (by omega))

    simpa only [show 200+(i-200)=i by omega] using h

  by_cases z208 : i < 216

  · have h := List.all_eq_true.mp repOK_208 (i-208) (List.mem_range.mpr (by omega))

    simpa only [show 208+(i-208)=i by omega] using h

  by_cases z216 : i < 224

  · have h := List.all_eq_true.mp repOK_216 (i-216) (List.mem_range.mpr (by omega))

    simpa only [show 216+(i-216)=i by omega] using h

  by_cases z224 : i < 232

  · have h := List.all_eq_true.mp repOK_224 (i-224) (List.mem_range.mpr (by omega))

    simpa only [show 224+(i-224)=i by omega] using h

  by_cases z232 : i < 240

  · have h := List.all_eq_true.mp repOK_232 (i-232) (List.mem_range.mpr (by omega))

    simpa only [show 232+(i-232)=i by omega] using h

  by_cases z240 : i < 248

  · have h := List.all_eq_true.mp repOK_240 (i-240) (List.mem_range.mpr (by omega))

    simpa only [show 240+(i-240)=i by omega] using h

  by_cases z248 : i < 256

  · have h := List.all_eq_true.mp repOK_248 (i-248) (List.mem_range.mpr (by omega))

    simpa only [show 248+(i-248)=i by omega] using h

  by_cases z256 : i < 264

  · have h := List.all_eq_true.mp repOK_256 (i-256) (List.mem_range.mpr (by omega))

    simpa only [show 256+(i-256)=i by omega] using h

  by_cases z264 : i < 272

  · have h := List.all_eq_true.mp repOK_264 (i-264) (List.mem_range.mpr (by omega))

    simpa only [show 264+(i-264)=i by omega] using h

  by_cases z272 : i < 280

  · have h := List.all_eq_true.mp repOK_272 (i-272) (List.mem_range.mpr (by omega))

    simpa only [show 272+(i-272)=i by omega] using h

  by_cases z280 : i < 288

  · have h := List.all_eq_true.mp repOK_280 (i-280) (List.mem_range.mpr (by omega))

    simpa only [show 280+(i-280)=i by omega] using h

  by_cases z288 : i < 296

  · have h := List.all_eq_true.mp repOK_288 (i-288) (List.mem_range.mpr (by omega))

    simpa only [show 288+(i-288)=i by omega] using h

  by_cases z296 : i < 304

  · have h := List.all_eq_true.mp repOK_296 (i-296) (List.mem_range.mpr (by omega))

    simpa only [show 296+(i-296)=i by omega] using h

  by_cases z304 : i < 312

  · have h := List.all_eq_true.mp repOK_304 (i-304) (List.mem_range.mpr (by omega))

    simpa only [show 304+(i-304)=i by omega] using h

  by_cases z312 : i < 320

  · have h := List.all_eq_true.mp repOK_312 (i-312) (List.mem_range.mpr (by omega))

    simpa only [show 312+(i-312)=i by omega] using h

  by_cases z320 : i < 328

  · have h := List.all_eq_true.mp repOK_320 (i-320) (List.mem_range.mpr (by omega))

    simpa only [show 320+(i-320)=i by omega] using h

  by_cases z328 : i < 336

  · have h := List.all_eq_true.mp repOK_328 (i-328) (List.mem_range.mpr (by omega))

    simpa only [show 328+(i-328)=i by omega] using h

  by_cases z336 : i < 344

  · have h := List.all_eq_true.mp repOK_336 (i-336) (List.mem_range.mpr (by omega))

    simpa only [show 336+(i-336)=i by omega] using h

  by_cases z344 : i < 352

  · have h := List.all_eq_true.mp repOK_344 (i-344) (List.mem_range.mpr (by omega))

    simpa only [show 344+(i-344)=i by omega] using h

  by_cases z352 : i < 360

  · have h := List.all_eq_true.mp repOK_352 (i-352) (List.mem_range.mpr (by omega))

    simpa only [show 352+(i-352)=i by omega] using h

  by_cases z360 : i < 361

  · have h := List.all_eq_true.mp repOK_360 (i-360) (List.mem_range.mpr (by omega))

    simpa only [show 360+(i-360)=i by omega] using h

  omega

set_option maxRecDepth 4096 in
/- Distinct maximal independent sets require distinct circuit choices. The checked counts rule out their placement in each affordable circuit shape. -/
private theorem catalogue_from_checks {n t : ℕ} (ri : ℕ) (rows : List ℕ)
    (hcatalogue : andCatalogue[ri]?.getD (0,[]) = (t,rows))
    (hn : rows.length = n) (ht : t ≤ 5)
    (G : SimpleGraph (Fin n))
    (hadj : ∀ a b : Fin n, (rows.getD a.val 0).testBit b.val = true ↔ G.Adj a b)
    (C : PEqualNP.AndCount.AndCountCircuit n) (hc : C.Computes G)
    (hr : verifiedRep ri = true)
    (hclasses : ∀ ci < 57, shapeFacts ci = true)
    (hchoose : ∃ h, shapeCheck (corner.reachSignature (corner.topology C)) h = true) :
    t ≤ C.size := by
  by_contra! hall
  have hk : C.size ≤ 4 := by omega
  let ms := cachedMIS[ri]?.getD []
  let pat := patternCache[ri]?.getD []
  let wit := witnessCache[ri]?.getD []
  obtain ⟨hint,hintOK⟩ := hchoose
  let j := hint % 64
  let cs := shapeClasses[j]?.getD []
  let host := cachedShapes[j]?.getD ([],#[],0)
  obtain ⟨hj,hlen,_,_⟩ := corner.classified_raw hintOK
  change j < 57 at hj
  change cs.length ≤ 16 at hlen
  have T := hclasses j hj
  change ((classWeightCalc cs == (classUses cs).card) && _) = true at T
  obtain ⟨hweight,hTable⟩ := Bool.and_eq_true_iff.mp T
  have affordable : classWeightCalc cs ≤ 2*(t-1) := by
    have hw := classUses_bound C hk hint hintOK
    have eq := beq_iff_eq.mp hweight
    change (classUses cs).card ≤ 2*C.size at hw
    omega
  obtain ⟨facts,casesOK⟩ := Bool.and_eq_true_iff.mp hr
  unfold repFacts at facts
  rw [hcatalogue] at facts
  change (decide ms.Nodup && _ && _) = true at facts
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at facts
  obtain ⟨⟨nodup,goodMS⟩,matchPat⟩ := facts
  have good (m) (hm : m ∈ ms) : m < 2^n ∧ rowMaskOK n rows m = true := by
    simpa only [hn] using goodMS m hm
  have sizeBound : ms.length ≤ 16 :=
    (sampleRows_count rows G hadj C hc ms nodup good).trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) hk)
  let place W (hW : ∀ v ∈ W,v < n) :=
    sampleRows_placement rows G hadj C hc hk hint hintOK ms nodup good W hW
  have fits : ms.length ≤ cs.length := by
    obtain ⟨_,f,inj,lands,_,_,_⟩ := place [] (by simp)
    let site (k : Fin ms.length) : Fin 16 := ⟨k.val,lt_of_lt_of_le k.isLt sizeBound⟩
    have mem (k) : site k ∈ sampleSlots ms := by
      simp [sampleSlots,Nat.testBit_two_pow_sub_one,site,k.isLt]
    let loc (k : Fin ms.length) : Fin cs.length :=
      ⟨(f (site k)).val,by simpa only [Nat.testBit_two_pow_sub_one,decide_eq_true_eq] using lands _ (mem k)⟩
    have on : Function.Injective loc := by
      intro a b eq
      have e : f (site a) = f (site b) := Fin.ext (congrArg (fun x : Fin cs.length => x.val) eq)
      have same : site a = site b := inj (mem a) (mem b) e
      exact Fin.ext (congrArg (fun x : Fin 16 => x.val) same)
    simpa using Fintype.card_le_of_injective loc on
  have ok := List.all_eq_true.mp casesOK j (List.mem_range.mpr hj)
  unfold checkRepCase at ok
  rw [hcatalogue] at ok
  change runProofCase ri j host cs t rows ms pat wit = true at ok
  let W := decodedVertices 10 (((wit.find? (fun w => w % 64 == j)).getD 0) >>> 6)
  have sel : ¬ (classWeightCalc cs > 2*(t-1) ∨ ms.length > cs.length) := by omega
  simp only [runProofCase, Bool.or_eq_true, decide_eq_true_eq, sel, ite_false, Bool.and_eq_true,
    Bool.not_eq_true', bne_iff_ne,List.all_eq_true,decide_eq_true_eq] at ok
  change (host.1 ≠ [] ∧ ∀ x ∈ W, x < rows.length) ∧
    packedVerify host.1 (2^ms.length-1) (2^cs.length-1) (fun v => pat.getD v 0)
      (fun v => rows.getD v 0) W (cornerTable host cs.length) (cacheRow host cs.length (2^cs.length-1)) =
        false at ok
  have hW : ∀ v ∈ W, v < n := by simpa only [hn] using ok.1.2
  change (host.1.isEmpty || _) = true at hTable
  simp only [Bool.or_eq_true,List.isEmpty_iff] at hTable
  have data := hTable.resolve_left ok.1.1
  simp only [Bool.and_eq_true,List.all_eq_true,List.mem_range,List.contains_iff_mem,beq_iff_eq] at data
  obtain ⟨⟨hHost,had⟩,hrows⟩ := data
  obtain ⟨profile,f,hinj,hcF,hpr,hagr,hed⟩ := place W hW
  have passing := packed_verify_pass host.1 (2^ms.length-1) (2^cs.length-1) (fun v => pat.getD v 0)
    (fun v => rows.getD v 0) W profile f hinj
    (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcF i hi⟩) (fun v hv => by
      have existsP := hpr v hv
      change profile v ∈ rowClassHost cs at existsP
      simp only [rowClassHost,List.mem_mergeSort,List.mem_eraseDups,List.mem_map,List.mem_range] at existsP
      obtain ⟨p,hp,eq⟩ := existsP
      rw [← eq]
      exact hHost p hp)
    (fun v hv i hi => by
      rw [matchPat v (ok.1.2 v hv)]
      exact hagr v hv i hi)
    hed (cornerTable host cs.length) (cacheRow host cs.length (2^cs.length-1))
    (fun i hi => by
      rw [← List.getD_eq_getElem host.1 0 hi]
      exact hrows i hi) had
  rw [ok.2] at passing
  exact Bool.noConfusion passing

theorem andCatalogue_bound {n t : ℕ} (ri : ℕ) (hi : ri < 361) (rows : List ℕ)
    (hcatalogue : andCatalogue[ri]?.getD (0,[]) = (t,rows))
    (hn : rows.length = n) (ht : t ≤ 5) (G : SimpleGraph (Fin n))
    (hadj : ∀ a b : Fin n, (rows.getD a.val 0).testBit b.val = true ↔ G.Adj a b)
    (C : PEqualNP.AndCount.AndCountCircuit n) (hc : C.Computes G) : t ≤ C.size :=
  catalogue_from_checks ri rows hcatalogue hn ht G hadj C hc (repOK_all ri hi) cacheOK_all
    (classification_hint _ (corner.signature_listed _))

end PEqualNP.Outside.L_meta_217
namespace PEqualNP.Outside.L_meta_217
private def orbitSeedFamily (seed : Nat) := seed % 4294967296
private def orbitSeedSize (seed : Nat) := (seed >>> 32) % 8
private def orbitRepId (seed : Nat) := (seed >>> 35) % 512
private def orbitBase (seed : Nat) : List Nat :=
  (List.range 32).filter fun m => (orbitSeedFamily seed).testBit m

private def orbitActionOK (t c act : Nat) : Bool :=
  minimumActionOK t c (act % 32768) (act >>> 15)

private def orbitSeedOK (cat : Array (Nat × List Nat)) (t c seed : Nat) : Bool :=
  let base := orbitBase seed
  let idx := orbitRepId seed
  let row := cat[idx]?.getD (0,[])
  base.length == orbitSeedSize seed && orbitSet base == orbitSeedFamily seed &&
    row.1 == t && matrixCheck t c base row.2 (unrankPerm (t+base.length) (seed >>> 44))

private def orbitLeaf (seeds acts : Array Nat) (find : Nat → Nat) (which : Nat) (ls : List Nat) : Bool :=
  match acts[which]? with
  | none => false
  | some act =>
    let fam := orbitImage (act >>> 15) ls
    match seeds[find fam]? with
    | none => false
    | some seed => ls.length == orbitSeedSize seed && fam == orbitSeedFamily seed

private theorem orbitLeaf_sound {t c : Nat} (ht : 2 ≤ t) (ht' : t ≤ 5)
    (cat : Array (Nat × List Nat)) (seeds acts : Array Nat)
    (seedOK : ∀ s ∈ seeds, orbitSeedOK cat t c s = true)
    (actOK : ∀ a ∈ acts, orbitActionOK t c a = true)
    (known : ∀ (idx s : Nat) (rows : List Nat), cat[idx]? = some (s,rows) → ∀ K : SimpleGraph (Fin rows.length),
      (∀ a b : Fin rows.length, (rows.getD a.val 0).testBit b.val = true ↔ K.Adj a b) →
      AndBound _ s K)
    (find : Nat → Nat) (which : Nat) (ls : List Nat)
    (ok : orbitLeaf seeds acts find which ls = true)
    (J : SimpleGraph (Fin (t+ls.length)))
    (model : ∀ i j : Fin (t+ls.length), splitEdge t c ls i.val j.val = true ↔ J.Adj i j) :
    AndBound _ t J := by
  cases ha : acts[which]? with
  | none => simp [orbitLeaf,ha] at ok
  | some act =>
    cases hs : seeds[find (orbitImage (act >>> 15) ls)]? with
    | none => simp [orbitLeaf,ha,hs] at ok
    | some seed =>
      simp only [orbitLeaf,ha,hs,Bool.and_eq_true,beq_iff_eq] at ok
      have h := seedOK seed (Array.mem_of_getElem? hs)
      simp only [orbitSeedOK,Bool.and_eq_true,beq_iff_eq] at h
      obtain ⟨⟨⟨blen,bset⟩,same⟩,mat⟩ := h
      have match_ : orbitCheck (act >>> 15) (orbitBase seed).length (orbitSet (orbitBase seed)) ls = true := by
        simpa only [orbitCheck,Bool.and_eq_true,beq_iff_eq,blen,bset] using ok
      apply orbitTransport ht' (Bool.and_eq_true_iff.mp (actOK act (Array.mem_of_getElem? ha))).1 ls (orbitBase seed)
        (List.nodup_range.filter _) match_ _ J model
      cases hc : cat[orbitRepId seed]? with
      | none => simp [hc] at same; omega
      | some row =>
        rcases row with ⟨s,rows⟩
        simp [hc] at same
        subst s
        simp [hc] at mat
        exact rep_transport _ _ _ (matrixCheck_sound mat) (known _ _ _ hc)

private def orbitHash (n buckets a b : Nat) (offsets : Array Nat) (fam : Nat) : Nat :=
  let bucket := ((fam*a) >>> 15) % buckets
  let offset := (offsets[bucket/16]?.getD 0 >>> (9*(bucket % 16))) % 512
  (((fam*b) >>> 15) + offset) % n

private def orbitChoice (data : Array Nat) (idx : Nat) : Nat :=
  let chunk := data[idx/32]?.getD 0
  let width := chunk % 8
  (chunk >>> (3+width*(idx % 32))) % 2^width

private structure OrbitBank where
  seeds : Array Nat
  acts : Array Nat
  hints : Array Nat
  buckets : Nat
  a : Nat
  b : Nat
  offsets : Array Nat

private def orbitRead (bank : OrbitBank) (ls : List Nat) (idx : Nat) : Bool :=
  orbitLeaf bank.seeds bank.acts
    (orbitHash bank.seeds.size bank.buckets bank.a bank.b bank.offsets)
    (orbitChoice bank.hints idx) ls

private def orbitBankOK (cat : Array (Nat × List Nat)) (t c : Nat) (bank : OrbitBank) : Bool :=
  bank.seeds.all (orbitSeedOK cat t c) && bank.acts.all (orbitActionOK t c)

private theorem orbitRead_sound {t c : Nat} (ht : 2 ≤ t) (ht' : t ≤ 5)
    (cat : Array (Nat × List Nat)) (bank : OrbitBank)
    (ok : orbitBankOK cat t c bank = true)
    (known : ∀ (idx s : Nat) (rows : List Nat), cat[idx]? = some (s,rows) → ∀ K : SimpleGraph (Fin rows.length),
      (∀ a b : Fin rows.length, (rows.getD a.val 0).testBit b.val = true ↔ K.Adj a b) →
      AndBound _ s K)
    (ls : List Nat) (idx : Nat) (pass : orbitRead bank ls idx = true)
    (J : SimpleGraph (Fin (t+ls.length)))
    (model : ∀ i j : Fin (t+ls.length), splitEdge t c ls i.val j.val = true ↔ J.Adj i j) :
    AndBound _ t J := by
  simp only [orbitBankOK,Bool.and_eq_true,Array.all_eq_true_iff_forall_mem] at ok
  exact orbitLeaf_sound ht ht' cat bank.seeds bank.acts ok.1 ok.2 known _ _ ls pass J model

private def pAct0 : Nat := 0x7fbee6f3ac5eb6a4e3283dae62d2a41ca620c2204681
private def pAct1 : Nat := 0x7fdde6f59c5ed5a4e5183dcd62d4941cc520c4104688
private def pAct2 : Nat := 0x7fdbd7799c5ed39569183dcb5358941cc31148104650
private def pAct3 : Nat := 0x7fbbcfb9ac5eb38da9283dab4b98a41ca30988204611
private def pAct4 : Nat := 0x7f7ed773cc5e769563483d6e5352c41c661142404642
private def pAct5 : Nat := 0x7fdde5ed5a6f59c4e5183dcd61cc522d4940c41044c8
private def pAct6 : Nat := 0x7fdbd5ed397799c569183dcb51cc31358941481042d0
private def pAct7 : Nat := 0x7fd7b7795a6f539671183dc73358522d431250104458
private def pAct8 : Nat := 0x7fbbcdeb38fb9ac5a9283dab49ca30b98a41882040d1
private def pAct9 : Nat := 0x7fbee5eb6a6f3ac4e3283dae61ca622d2a40c22044c1
private def pAct10 : Nat := 0x7f7ed5e769773cc563483d6e51c661352c41424042c2
private def pAct11 : Nat := 0x7f779fb56977358f31483d671b946135250b1040421a
private def pAct12 : Nat := 0x7efeb76bca6e7a9663883cee334ac22c6a1242804443
private def pAct13 : Nat := 0x7fb7afb96a6f338eb1283da72b98622d230a90204419
private def pAct14 : Nat := 0x7f7dcfb5cc5e758da5483d6d4b94c41c65098440460a
private def pAct15 : Nat := 0x7efdafadca6e798ea5883ced2b8cc22c690a8480440b
private def pAct16 : Nat := 0x7efdaee798fadca6a5883ced2ac690b8cc228480408b
private def pAct17 : Nat := 0x7efb9f6b98fada9729883ceb1b4a90b8ca1308804053
private def pAct18 : Nat := 0x7fdde6f59c3dcd62d4945ed5a4e5181cc520c4103888
private def pAct19 : Nat := 0x7fdde5ed5a3dcd61cc526f59c4e5182d4940c41028c8
private def pAct20 : Nat := 0x7fdbd5ed393dcb51cc317799c56918358941481018d0
private def pAct21 : Nat := 0x7fdde3dcd66f59c2d4945ed5a1cc524e5180c4103508
private def pAct22 : Nat := 0x7fbbcdeb38bdab49ca30fb9ac5a928398a41882008d1
private def pAct23 : Nat := 0x7fbee5eb6a3dae61ca626f3ac4e3282d2a40c22028c1
private def pAct24 : Nat := 0x7fbee6f3ac3dae62d2a45eb6a4e3281ca620c2203881
private def pAct25 : Nat := 0x7fdbd7799c3dcb5358945ed39569181cc31148103850
private def pAct26 : Nat := 0x7fd7b7795a3dc73358526f539671182d431250102858
private def pAct27 : Nat := 0x7fd7b3dc737795a358526f5392d43167118250102318
private def pAct28 : Nat := 0x7fbee3dae66f3ac2d2a45eb6a1ca624e3280c2203501
private def pAct29 : Nat := 0x7fbbcfb9ac3dab4b98a45eb38da9281ca30988203811
private def pAct30 : Nat := 0x7fcf7778d66f4b5670945ec73568524e431460103460
private def pAct31 : Nat := 0x7f7ed5e7693d6e51c661773cc56348352c41424018c2
private def pAct32 : Nat := 0x7f779fb5693d671b946177358f314835250b1040181a
private def pAct33 : Nat := 0x7f779bd671fb5693946177358b5250f314831040111a
private def pAct34 : Nat := 0x7eef3face376ad2f28c26e6b1ea4a166290e20802223
private def pAct35 : Nat := 0x7eef3f6ad2face3728c26e6b1e6290ea4a1620802063
private def pAct36 : Nat := 0x7fdbd3dcb57799c358945ed391cc3156918148103310
private def pAct37 : Nat := 0x7faf6fb8e66f2b4eb0a45ea72da8624e230ca0203421
private def pAct38 : Nat := 0x7f7ed773cc3d6e5352c45e769563481c661142403842
private def pAct39 : Nat := 0x7efeb76bca3cee334ac26e7a9663882c6a1242802843
private def pAct40 : Nat := 0x7efeb3cee376bca34ac26e7a92c6a166388242802303
private def pAct41 : Nat := 0x7dfe775bc66d7a5653845cf6354b424c721443003444
private def pAct42 : Nat := 0x7dfd6ed794f9dc6695845cf52cc710d8d4248500308c
private def pAct43 : Nat := 0x7fdde3dcd65ed5a1cc526f59c2d4944e5180c4102708
private def pAct44 : Nat := 0x7fd7b6f5397795a671183dc732d43135852250104298
private def pAct45 : Nat := 0x7fd7b3dc736f5392d4317795a3585267118250101518
private def pAct46 : Nat := 0x7fcf7778d65ec73568526f4b5670944e431460102660
private def pAct47 : Nat := 0x7fcf75ec73778d6568526f4b54e431670944601022e0
private def pAct48 : Nat := 0x7fbbcbdab4fb9ac398a45eb389ca30da928188203111
private def pAct49 : Nat := 0x7fb7afb96a3da72b98626f338eb1282d230a90202819
private def pAct50 : Nat := 0x7fb7aef338fb96a6b1283da72ad230b9862290204099
private def pAct51 : Nat := 0x7fb7abda72fb96a398626f338ad230eb128290202119
private def pAct52 : Nat := 0x7fb7abda72ef338ad230fb96a398626b128290200519
private def pAct53 : Nat := 0x7faf6ef2b4fb8e66b0a45ea72ce230da8624a02030a1
private def pAct54 : Nat := 0x7faf6ef2b4dea72ce230fb8e66b0a45a8624a02006a1
private def pAct55 : Nat := 0x7f7dcde758fb5cc5a5483d6d49c650b94c41844040ca
private def pAct56 : Nat := 0x7f779f7358fb569731483d671b5250b946131040405a
private def pAct57 : Nat := 0x7f6f5f72d4fb4e5730c45e671d6250da461520403062
private def pAct58 : Nat := 0x7f6f5de671fb4e55a461772d4d6250f30c45204010e2
private def pAct59 : Nat := 0x7efdafadca3ced2b8cc26e798ea5882c690a8480280b
private def pAct60 : Nat := 0x7efdabced2fadca38cc26e798ac690ea58828480210b
private def pAct61 : Nat := 0x7efdabced2ee798ac690fadca38cc26a58828480050b
private def pAct62 : Nat := 0x7eef3ee6b1f6ad2e6290face36a4a1728c26208002a3
private def pAct63 : Nat := 0x7dfe76d7a55cf634c72175bc66538454b42443001684
private def pAct64 : Nat := 0x7dfe75cf6375bc654b426d7a54c721653844430022c4
private def pAct65 : Nat := 0x7dfd6ed794dcf52cc710f9dc66958458d4248500068c
private def pAct66 : Nat := 0x7dfb5f9da575b94f19845cf31d8d2154b10d09003214
private def pAct67 : Nat := 0x7df73f9d6375b52f19426d731e952165310e1100221c
private def pAct68 : Nat := 0x7fbee3dae65eb6a1ca626f3ac2d2a44e3280c2202701
private def pAct69 : Nat := 0x7f7dcfb5cc3d6d4b94c45e758da5481c65098440380a
private def pAct70 : Nat := 0x7dfb5f5b94dcf31d4b10f9da57198458d21509000654
private def pAct71 : Nat := 0x7dfd6dcf52ed794cc710f9dc658d42695844850004cc
private def pAct72 : Nat := 0x7dfb5dcf31f5b94d4b10f9da558d21719845090002d4
private def pAct73 : Nat := 0x7df73f5b52ed731e5310f9d63719426952161100045c
private def pAct74 : Nat := 0x7df73ed731f5b52e5310f9d63695217194261100029c
private def pAct75 : Nat := 0x7fcf76f4b55ec734e431778d667094568524601016a0
private def pAct76 : Nat := 0x7eef3f6ad2ee6b1e6290face3728c26a4a1620800463
private def pAct77 : Nat := 0x7dfb5dcf31f9da558d2175b94d4b10f19845090010d4
private def orb_2_0 : OrbitBank := ⟨#[0xa00000006,0x120000000a],#[pAct0,pAct1],#[0x19],1,0x8ca385,0xb0e5b5,#[0x0]⟩
private def orb_2_1 : OrbitBank := ⟨#[0x100000008,0x501200000006],#[pAct0,pAct1],#[0x19],1,0x9d8c31,0x75a1b1,#[0x0]⟩
private def orb_3_0 : OrbitBank := ⟨#[0x7905b0000002c,0x4b00000086,0x6300000068,0x190430000001a,0x2b604b0000002a,0x3b00000016],#[pAct2,pAct0,pAct3,pAct4,pAct1],#[0x104863],3,0x8dce61,0xdd07f1,#[0x403]⟩
private def orb_3_1 : OrbitBank := ⟨#[0x602200000090,0x603200000060,0x5005300000086,0x6502200000028,0xc005b00000034,0x701a00000018,0x26d04b00000026,0x6204300000016],#[pAct0,pAct1],#[0x779],4,0x45a80b,0xc592f,#[0x281c0800]⟩
private def orb_3_3 : OrbitBank := ⟨#[0x6002a00000028,0x25804b00000016,0x6002200000018],#[pAct2,pAct1],#[0x29],2,0xd76859,0x26dc1,#[0x1]⟩
private def orb_3_7 : OrbitBank := ⟨#[0x5e05300000016],#[pAct2,pAct0,pAct3,pAct1],#[0x1a],1,0xe767af,0x75e58f,#[0x0]⟩
private def orb_4_0 : OrbitBank := ⟨#[0x14400008016,0x97621440000022a,0x7217400000780,0x2ab215c00000384,0x721c400001680,0x7915400000286,0x16871a400000258,0x9d061840000022c,0x12c00000116,0x17011ac00000168,0x972c13c0000012a,0x7914c00000246,0x5a41340000011a,0x276118400000294,0x5a21bc00000660,0x7913c00000186,0x27dd17c0000012c,0x2d041b400000690,0x34c18c00000682,0x9d0615c0000024a,0x9aa91b400000268],#[pAct5,pAct2,pAct6,pAct0,pAct7,pAct8,pAct9,pAct3,pAct4,pAct10,pAct11,pAct12,pAct1,pAct13,pAct14,pAct15],#[0x61062006fbe059f25d6594],11,0x8b6ec7,0x9b78a7,#[0xc0a00010200010048040402]⟩
private def orb_4_1 : OrbitBank := ⟨#[0x89d019400002046,0xbd719c00001086,0xe2e16c00008016,0x357018400002114,0x13af11300002048,0x8bd013c00000126,0x4390cb00001090,0xf008b00008110,0x8c9f18400000234,0xe2e14c00001016,0x11c90cb00002018,0xf10ab00000290,0x34861a400000350,0x78ef15c00001034,0x8c2014400000226,0x2a80ab00000248,0x4540d300001180,0x8fc115c00000252,0xf407b00000118,0xd5e19400002052,0x8f5115c00001026,0x10c0fb00001240,0x113008300000128,0x2570bb00001060,0x7bc0f300002440,0x11df0bb00000260,0x10c10300001280,0x43c0c300001018,0x10b0b300000160,0x7b60bb00002140,0x223a1a400001124,0xf0716400000186,0x113e08b00000228,0xf108300000190,0x10e613400000116,0x11c90d300001028,0x8a4119c00000384,0xe2e15400002016,0xdf210b00000680,0x357117c00000134,0x12e615400000246,0x8a9916c00000286,0x8c251b400001224],#[pAct5,pAct0,pAct9,pAct1],#[0x6ecece7e69fe46682,0x187f86a],22,0x6c3e0b,0x46443,#[0x18381801018200400000001401060000603,0x11000440021]⟩
private def orb_4_3 : OrbitBank := ⟨#[0xf1911300001900,0x11ea0bb00000610,0x10e00db00000428,0x8a3914400000216,0x10e00cb00000424,0x11d111300001810,0xb4110b00001804,0x10e009300000128,0x10f509b00000228,0x11ea0e300000620,0x12770db00000920,0x11ea0d300000520,0x89d016c00000816,0x768017400001502,0x11d111b00001820,0x10e00eb00000824,0x133718c00001406,0x8fea15c00000512,0x8a4118400000314,0x2b710300001408,0x89d013c00000116,0x13af15400000416,0x2cf0ab00000418,0x10f508b00000218,0x10e008300000118,0x1380ab00000910,0xe220f300001600],#[pAct2,pAct1],#[0x3dcc3c49],14,0x786927,0xfadae1,#[0x802804020b008000200020040200]⟩
private def orb_4_7 : OrbitBank := ⟨#[0x8c9916c00000216,0x8c2319c00000314,0x107416400000116,0x1de12300001600,0xdae10b00000610],#[pAct2,pAct0,pAct3,pAct1,pAct4],#[0x1b51b],3,0x5cbd25,0xe5be63,#[0x4]⟩
private def orb_4_11 : OrbitBank := ⟨#[0x10e008b00000118,0x10e00a300000228,0x10e009b00000128,0x89d014400000116],#[pAct5,pAct6,pAct2,pAct1,pAct7],#[0x331b],2,0x7a7f8b,0x8b5781,#[0x200]⟩
private def orb_4_12 : OrbitBank := ⟨#[0x53f10300000460,0x10b80f300000428,0x706a00000240,0x890017400000426,0x291d19c00000194,0x11420bb00000128,0x20711300000482,0x2c914c00000116,0x24f918c00000434,0x34712300001480,0x53d10b00000490,0x3f0c300000142,0x707200000280,0x3f0cb00000182,0x3260eb00008014,0x9ab615c0000011a,0x10810d300000148,0x11420e300000228],#[pAct9,pAct2,pAct16,pAct17,pAct13,pAct10,pAct11,pAct1],#[0x1eaf3afc2dfa3c3],9,0x4f49c9,0x8fea83,#[0x900024160c008000c02]⟩
private def orb_4_13 : OrbitBank := ⟨#[0x26d0db00000148,0x26d0ab00000118,0x114f15400000116,0x26d0cb00000142,0x6007200000240,0x13af19400001016,0x106811300001018,0x2cf11b00001048,0x2cf11300001042],#[pAct9,pAct1],#[0xfb9],5,0x231077,0x1204f1,#[0x180001]⟩
private def orb_4_15 : OrbitBank := ⟨#[0x11420eb00000214,0x8c3016c00000116],#[pAct2,pAct1],#[0x19],1,0x9d8c31,0x75a1b1,#[0x0]⟩
private def orb_5_0 : OrbitBank := ⟨#[0x36102bae500020660,0x778a7add00010660,0x109c818e500028114,0x31dd419f500034028,0x1140b1d00011680,0x2a48d5b3d00021680,0x31da518b50002402a,0x36bc96a1d00010268,0x320a4086500020246,0x36be96a2500020268,0x2f90eb89d0002401a,0x35839aafd00182402,0x35f95fa5d00030680,0x102664a9500182404,0x1659ab0d00061280,0x64ec0afd00060680,0xc4e31a0d00024118,0x10b0379ad00020344,0x1277e5a1d00010690,0xc4e12ad500020690,0x3734ca86d00020286,0x2a3585d00010286,0xc789a8fd00030580,0xde72c9f500021580,0xb13049fd00020294,0x369a0d94d00020682,0x159f22b3d00092440,0xfff019ed00082444,0x25f744a9500062048,0xa8500082442,0x2d186500024016,0x3620fbaa500062018,0x159f23b3500062440,0x84d80000116,0x1654593d00010682,0x1a9d00021442,0x3699bf9d500020780,0x1d8928350001011a,0xa5a0faf500082450,0x3699dd9b500020384,0x36c1798f500082016,0x2f1a9bb1500024128,0x31c1c9aad00021448,0x109f558dd00010294,0x24f08ad00010780,0xb410a3d00062042,0x31d781b2500024228,0xb3a74a3500020684,0x82d00010116,0x35523083d0001012a,0x2b8b2d01168000,0x361043a3500082142,0x10158b97d00062044,0x178b6aa2d00092140,0x10c3f68d50001012c,0xfff019dd00082144,0xb142aa500021482,0x178b98aad00031480,0x11d7879d500082150,0x10b042a5d00021484,0x5899896d00082046,0x310a659dd0002402c,0x36beae94500020462,0x11ff2dae500062140,0x11618b87500010384,0x2a358f500020486,0x3699dd9bd00020348,0x2d184500018016,0x112929b4500182440,0x1150a287d00038014,0x1ef50e8b500078010,0x355b308450001022a,0xc61cfacd00020560,0x13dd494d00068012,0x2b88cd00178000,0xc75a0a1500010168,0x355c3884d0002022a,0x2bae798fd00020470,0x2a45ee9ed00168002,0x3733448dd0001022c,0x109c818ed00082114,0x31d579a2d00020468,0x2d186d00028016,0x1659ab0500061240,0x2a3585500010246,0x3733448750001024a,0x3734ca87d0002024a,0x369a0d93500020582,0x127504a2500068110,0x276483d00010186,0x3734ca8ed0002024c,0x13dd59b500020492,0xc64d294500034018,0x36be96a0d00020258,0x11eb5a9bd00020590,0xc5105a0500010258,0x18f56ab2500168100,0x3734ca8e50002022c,0xb15d79350002401c],#[pAct18,pAct5,pAct19,pAct20,pAct2,pAct0,pAct21,pAct6,pAct22,pAct9,pAct23,pAct24,pAct3,pAct25,pAct7,pAct26,pAct27,pAct28,pAct8,pAct29,pAct4,pAct30,pAct10,pAct11,pAct31,pAct32,pAct33,pAct12,pAct34,pAct35,pAct36,pAct37,pAct38,pAct39,pAct40,pAct41,pAct42,pAct1,pAct43,pAct44,pAct45,pAct46,pAct47,pAct48,pAct49,pAct50,pAct51,pAct52,pAct53,pAct54,pAct14,pAct55,pAct56,pAct57,pAct58,pAct15,pAct59,pAct16,pAct60,pAct61,pAct17,pAct62,pAct63,pAct64,pAct65,pAct66,pAct67],#[0x157eb599554fd7a3406d297847203e7609280244529b460d8a150a047,0x2a8279e2d18d139c6c69ea504011854084f1060e4905422d19564b1cf,0x4a41326000173a48015b424541025234e414cdd09d182cf343ee1af,0x128616],50,0x2759c1,0x633daf,#[0x18100202000500000008000015040180003,0xd00000171f83c3e06000200000048242601,0x1100054000d0000e0d0000066140d8007003,0x1f]⟩
private def orb_5_1 : OrbitBank := ⟨#[0x269abfa6500030580,0x32f71d9d500132004,0x2ec1b69410000190,0x52cf549c00021240,0xf88e4ad500122104,0x14eb008e520010114,0x258a939400012440,0x9cb641c00024018,0x54de280c00182400,0x761d42c10000160,0x3e6875400122040,0x4f95c28c00010228,0x14be06acd00031140,0x3247b8ab500082114,0x3308c687500011026,0x3fbe065400101820,0x26abec97500134004,0x2ce6ae87d00101034,0xa5b1e9e520000452,0xf88eca0d10010124,0x3e5c80401102008,0x14eb048d500010134,0x3b73190d00108016,0x31e930a4500102406,0x40b44a400128100,0x5126e31c00021028,0x3b1c40410000118,0x369a0d95500020582,0x3df26b400101280,0x4ffca98510000186,0x4543988d00018016,0x89d03f420000448,0x3e6047c00091020,0xa2ab68a520000146,0x3808da4500112042,0x32f71394d00122006,0x3b8a42400061010,0x1a67148400022140,0x3277d78a500024026,0x31fc4f9b500020344,0x44f1086d20000116,0x47cac64410020240,0x33d6f594500021142,0x2ce4ae87500011034,0x44e7958c00081060,0xef9e4bc00111800,0x32702e8e500020234,0xa896098d00204106,0x2c4bff98d00024034,0x14c3b9a0500010350,0x2d3c1e89d10000126,0x54b8d47c00021180,0x5029ca4d00124006,0xef144ac00101900,0x3247b8abd00081124,0x4eed166c00204208,0x272f9f99d00138004,0xf6725a3500122014,0x44e98a9d01101006,0x413d49400011280,0x510774bc00101208,0x4eee992d00082046,0x5136c3cc10000228,0x326e1690d00082016,0x55ec456400162000,0x32f2b7f401204200,0x320a4086d00020246,0x258a839c20010440,0x323b5683d00010126,0x50f9b4ac00112008,0x2ce6adaad01101024,0x3d8f19ad00101106,0x510774b400102108,0x1c4d167400082440,0x31d819a6d00032044,0xf61fa93510000134,0x32f71f9b500032014,0xf2ec6cc00122400,0x275ffd94500101214,0x31fa549c500010384,0xff99694500031050,0x3b112d400028110,0x326e1691500081026,0xf6725a4d00124014,0x52cbc65410010280,0x2d42d19a500128006,0x5276139c00024220,0x3b73192500204016,0x2ce94989d00021052,0x2ce6788a500102052,0x33b9da87500010252,0x41305dc00214200,0x3b8d2cc00010290,0x9b1a8a4d10000350,0x26ca4193500034014,0x5289a2e400010260,0xec4799fd00022114,0xef9555c00192000,0xf1e556401204100,0x3b8d41c00021090,0xecba30400091010,0x31ed8996500022046,0x2ce97da2d00101224,0x2767c6cc01102040,0x4ec1883500010116,0x27486e98500081034,0x4e92886500101016,0x2167afa6500031084,0xf20269f501112004,0x1a7a63cc01118000,0x330ac686d00022016,0x34747a6d00102502,0x961f2cc00010248,0x493bb57c00124200,0x32f71f9bd00031024,0x4543985500011016,0x42fc795d00012052,0x325cd0a1d00011224,0x122df5fc00102048,0x325f49a0d00021124,0x3277d786500021016,0x289d21a0d00034110,0x4ef8147c00021048,0x33ae48b2510020224,0x2d865197510000252,0x31ed8995500021086,0x3e687b401182000,0x26ca4195500038014,0x584ae8f500024016,0x572776f400062040,0x2d7e380401101080,0x5007f30400021018,0x32472c84500010226,0xf6725a5500128014,0x588b651c00012048,0x4622938400021060,0x1b829eaad00031440,0x215b7ca7510000384,0x3b8f69400102018,0x2c5a47aed00204304,0x4651caa501102006,0xf8bb8acd00111204,0x44e9cabd00101806,0x3b1455410000290,0x3b105c400204210,0x4f99229400020228,0x475c156410000260,0x5262642c00062010,0x1c25349c00101240,0x274c4d8fd00101304,0x5121e2fc00012018,0xfbd3c8c520000446,0x2dcba0b1510010224,0x6eff5d400168000,0x448804f400010680,0x55e38aa500021442,0x278d748400102140,0x44b266fc00061080,0x15153a9bd00112104,0x413d48c00011240,0x3208ba88d00010286,0x326e2e8dd00010234,0x526063a400101028,0x1ad403ac00101810,0xecbc4c401108010,0x8ca17c401204008,0x14edd4a5d01102014,0x52a8179c00022440,0x330ade8ed00021034,0x32d756e400021480,0x89d056c10000248,0x3286b79e500204206,0x4f7d628400010128,0x3b107fc01101008,0x2c66d98bd00028016,0x44f1086510000116,0x36c17f99500082052,0x32fc3f94500101206,0x258c03fc20040440,0x54b9e6b400182100,0x3e6e6c400121800,0x2e12d198d00204112,0xef224b400101180,0x33239f9bd00020350,0x5121e31400011028,0x3247b8ac500081224,0x3b46090500081016,0x33108c8b510000226,0xf26231c00118100,0x4284696520000152,0x1a6ea49c10010240,0x4eed070400102408,0x3b1029480010110,0x3d8f19b500102106,0x3b8c5bc00068010,0x4ecc938c00024028,0x4651cac501108006,0x330ac687d00021026,0x31e93299d10000286,0x81f641420000148,0x12a267cc10020480,0x1a1524ec00020490,0x32f71393500112006,0x1097168fd00031044,0x268767dc00244200,0x2d6c9e9dd10000234,0xf1f331400011180,0x5262643400061020,0x54b8d4a400021280,0x3b1c40c20000118,0x3d8d264401124000,0x33bb6087d00020252,0x3de76ac00101108,0x31fc4f9cd00020384,0x5136c3ac10000128,0x50f9b4c400122008,0x2e3c118ed00024112,0xec4130c00108110,0x3e6e6bc00121400,0x52cbc67c10020280,0x4e8b372400124008,0x5619c7bc00182040,0x734d43400101600,0x14eb019b500102114,0x1c65e48400020460,0x44ba174410000680,0x14edd29ad00031014,0x2767c1a4500032050,0x554bf85d00010246,0x31ae038bd00020486,0x54df22d400020290,0x528d02ec00020260,0x1a3223a410010180,0x12a2659400204108,0x1a41c43400112400,0x14eb018dd00012114,0x4f3602d400020248,0x3b1128c00018110,0x4932338400024120,0xa584f98d00102046,0x271ebeb3d01122004,0x257a12e400012140,0x413238400214100,0x3d8f19cd00108106,0x257a02ec20010140,0x572776ec00092040,0x2ffce75401204010,0x3b0fd6dc00081240,0x3f64667c01128000,0x2ff5240c00101090,0x40c02dc00010160,0x89562ec00101060,0x320a4089500020286,0x3de1c91500118006,0x54df455400182010,0x3583aa8a500022052,0x89065b400204018,0x31ec0395d00012046,0x55f436d400082140,0xecbd2fc00011090,0x37487ba5500182006,0x3b7318f500102016,0x44e9cab500101086,0x4db640400101018,0x54df541c00092010,0x3b1428400010190,0x89062e400011060,0x3b2227c00010118,0x489ac88500010186,0x40b449c00124100,0x5890652400022048,0x3248b284d00020226,0x4ec1897510000246,0x31ed8993500021046,0xf88eda0500011124,0x44f1089580000116,0x325f49a2500021224,0x2ffce5dc00102440,0x3248c5ae500121204,0x4ffc9a8d01204006,0x26bfa4a8d00124024,0x3de1d9c500011086,0x2c356fa4500034024,0x5126e30c00022018,0xeccb2f400011018,0x2ce6968ed00101026,0x1a14f42c00102410,0x4543985d00012016,0x275ff39bd00101124,0x5701d4fc00020680],#[pAct18,pAct5,pAct19,pAct0,pAct21,pAct24,pAct9,pAct23,pAct28,pAct1,pAct43,pAct68],#[0x331cb44551555d11480d123804a54a254,0x31aaab2445bc2cccc93b915525000208c,0x240b0020c800a200b09c999c9bbd934,0x4ca5000240b480a00b4910004cca55004,0x2499999111509abd5514a8d3a22949004,0x28ca8a230c910049d2a882a0ca8a2230c,0x1834440b199a9b9c08d2a8a52490049ac,0x182ba844441ccb1004449baac41ca8434,0x224c80244c8a48a4a4810244820c8a24,0x484],145,0x5ecbbd,0xbb2e3b,#[0x38100205000000000008000401008440007,0x80c00068300005018100004000440003,0x103838090000c0000000540008008083607,0xe80c0002080080602000040400020000003,0x8500c000391c00000b0000001110141c00,0x200000002400800250c84836050786c0200,0x1900404000fa8802080403002050482c3208,0x2831cc0204a8d8a1100030261f6980000ab,0x140026040100804068000284208682031,0x0]⟩
private def orb_5_3 : OrbitBank := ⟨#[0x3fba668c08011020,0x543163b401000920,0x33b0d291500052012,0x53fe34a401020810,0x55c747d401082400,0x53fe34d402010420,0x2c5ce08ad00011502,0x3d8dc58c04012010,0x57d303ec00040428,0x52a6474c04122000,0x2c5f598b501001502,0x5278d52c00011820,0x56fa770c00092400,0x4f21c73401042008,0x4f2514fc00021804,0x36adcf99d00081502,0x94f169404000124,0x9aa95c404001204,0x3326e19bd00030510,0x55f4ba3d01041006,0x31d58095501000816,0x454370401011800,0xf3a209fd02010114,0x4ffb655404001024,0x804b7c401042400,0x36adc992d08001106,0x4ee5029400020218,0x9aaf55404001108,0x4f2514a400021408,0x31d8199cd00030814,0x3e94067c04101020,0x502883bc04000224,0x505d871c00061800,0x56fa770400052400,0x52a3733c00020620,0x52a624dc01020420,0x4aa638c08011010,0x57b5152402000418,0x548cc57401082100,0x32993986d02000116,0x3159888bd00040816,0x575cf9d500041502,0x929141400042404,0x31ebc9a5d00031404,0x5163650c00040920,0x4ec007bc04102004,0x369a1e9e502001406,0x5028080c00141800,0x5028646404001208,0x31e645a2501020214,0x33c1b787500010512,0x4ec004ac01000424,0x48d6e38404010210,0x52cbc3a404010120,0x527137ac02040420,0x5136270c00041820,0x5271379c02040410,0x5028647404002108,0x48f325dc04011200,0x4ecc92d400020418,0x4514139c01001600,0x4ec792fc00010424,0x5198244c00061200,0x4ecc937400020824,0x548ca38c00021900,0x566cb4fc00060810,0x5702e65401001408,0x9aaf47c00041108,0xb128796d04001016,0x3e94065404011020,0x450d839400011600,0x5051934c02000128,0x289c280c01041800,0x55bf458401062000,0x4ffb645400042018,0x52cbc3c404010220,0x9a4649400011408,0x3b44a4fc08011004,0x2c4c788bd08000116,0x52a372ec00020610,0x31e62884d00020216,0x53fe347c01010810,0x5836372c01082004,0x3c80e6fc00051800,0x9aa95bc00041804,0x331082a5500081412,0x5051931c01000218,0x5028644400041208,0x1330c5fc04012004,0x32013994d00021406,0x4b5666c08101100,0x436e892d08001016,0x52a624bc01010420,0x572ff5a400081600,0x53fe34e401020820,0x2c5f6589d01000512,0x225cb6af504101102,0x31d58096502000416,0x575cf96d04001106,0x49212cc00010910,0x31d8199b500030414,0x9aad41c04000118,0x543163bc02000520,0x572ff59c00082500,0x3645a395500050812,0x4ec0028400010118,0x4eed238c04000218,0x575c39b500040512,0x4ee502ac00020228,0x4f21c72401042004,0x48f6856404021100,0x4f9be43c00042108,0x4ee0028c00010218,0x331082a3500041412,0x940040c00040424,0x5405e2d400020910,0x586ae86d00040416,0x3dbba74404112000,0x4ec0029c00010128,0x4a2d541401001900,0x9aaf5dc00041600,0x48f3252408011100,0x52a3731c00020520,0x527c352400021810,0x31da5186d00020416,0x575cf94d00041406,0x9aaf4a400041408,0x31e645a0d01010214,0x4ffb659c04002018,0x529e72e400010610,0x57b5154402000428,0x52cb246c04021200,0x575cf93500041106,0x2e4be29d504011102,0x369a1e9dd01001406,0x9cb62cc00010418,0x31d58083d00010116,0x5735693d00011406,0x3db306f402041100,0x4ec7936c00010824,0x572ff59400042500,0x13ae755c04001018,0x3286b886501000116,0x4f21a64c04021008,0x4ec7941c00041018,0x24ae079c02011400,0x4ec0047c01000418,0x4ecc932c00020428,0x575cd8f504000116,0x4514864401021400,0x4ec0050401000824,0x6ca756c01052000,0x32993987d01000216,0x548cd46404022100,0x949580401040420,0x327ac6e401040810,0x31e42884500010216,0x440c168c00042408,0x4f21c71402041008,0x4514d38401000610,0x327ac6dc01042010,0x505d066404022004,0x5028830401000118,0x34b207f404101200,0x5028834401000128,0x2887509ed04101012,0x3286b88a504000216,0x2c5f799f501011402,0x333aba8fd00051102,0x566cb51400060820,0x3161619a500081406,0x48f3551c00011900,0x31e9178e500020314,0x53fe34cc01010820,0x2dab9397d01041102,0x4f21a68404022008,0x5051935401000228,0x2c5f598c502001502,0x355f099f500031500,0x1d60348400040610,0x49202d408010110,0x9d057b404101008,0x5278a56404021010,0x6af85b404002104,0x33db47bc04102100,0x3db346ec00041900,0x520fe44400062100,0x4ffb657404001028,0x4ee002a400010228,0x25ee67dc02041400,0x543163ac01000520,0x31d58093501000416,0x4f9be45400082104,0x3286b0afd00141402,0xfc8959401001810,0x32730699504002016,0x4eed23d404000228,0x31d8518f500041016,0x355f1a8b500021502,0x31d85191d00082016,0x5405e32c00020920,0x5278d51c00011810,0x529e731400010520,0x1ad0648402010410,0x513626d400042410,0x466941c01000910,0x4adc3f408101010,0x4eed23b404000128,0x2e24808ed04010112,0x137bf6cc00061400,0x4ec007d404102008,0x52a6249c01020410,0x9d062d400040418,0x5278a5a404022010,0x5028642c00041204,0x543163c401000620,0x57d303e400040824,0x4ec004cc01000428,0x50a3e41c00042104,0x97636b404011008,0x529e733400010620,0x584ae85d00010416,0x4ffb07a401040820,0x35fc94a9501041402,0x31da5189500020816,0x4ec7932400010428,0x33c48a94501010412,0x3299578ed01000314,0x527c353400021820,0x32730690d00042016,0x548cd43c00092100,0x2887509dd04011012,0x1ad3c67408101004,0x566cb50400050820,0x548b964c01021800,0x5136272c00081420,0x35237e8a502000512,0x5136273c00082410,0x4ec7943c00041028,0x586ada8504101006,0x4ffb65ac08001024,0x56fa771400062400,0x1ac314ec00040910,0x47b0b57c01041200,0x4f21a65c04012008,0x97636c401041008,0x5244063c08101020,0x4ec0053c02000424,0x52cb243400051200,0x513626ec00041810,0x2bc21798d04000314,0x583de5ac00082404,0x5278a45c00062010,0x55f3fa5d00051402,0x52cbc39c04020210,0x975d75404021004,0x4c6a5d404102010,0x31e69e8dd00010314,0x5028081400182400,0x47b8572401042100,0x4837e5fc04012100,0x513626b400041420,0x5051930c02000118,0x5702e66402001408,0x33c3b787d00020512,0x137be6e400091400,0x516364b400040520,0x4ecc930c00020424,0xf9b17cc01081400,0x313846d401001804,0x5278a58404021020,0x52cbc3ec08010120,0x4eed23e408000124,0x55f4ba3504011006,0x31d85188d00010816,0x6b3947c00052100,0x3b44d4f400011804,0x548ca39c00021600,0x5400e32400010920,0x54b9b65c01001820,0x586adaa501040412,0x516364d400040620,0x4f21c6f402041004,0x52cbc3dc04020220],#[pAct18,pAct2,pAct25,pAct1],#[0x3a3c7ff8824857fea,0x7a3bcced1447aa40a,0x69511afeaa02f07aa,0x6baafe1f81ea6eeca,0x2a0a9167e7a84ee3a,0x47ff88a0bea222482,0x3ccbe9442faed5142,0x7e2ecbaebad15510a,0x61fb04bee07ff82],142,0x6ee2d7,0xc60fd5,#[0x4000000203000000c060000a00008040005,0x41000208100c210d0140001048000000,0x430010980800080001c0000080080c16,0x280400884381c2e010a8040409,0x300000004100c0803000a00006000001a00,0x82002228082202000180404000001c00,0x3003c641f002f80000000000e4005a1cb803,0x332803c7d61b7c001d013b000004d8dc0410,0x58000007006b10a8003712089805408]⟩
private def orb_5_7 : OrbitBank := ⟨#[0x325f439cd00020314,0x2638afa6500030510,0x32702dabd01010214,0x275fff98501000314,0x564ef4fc00020610,0x4fa0b76c01021400,0x43b7890501000116,0x32701689500020216,0x734d60c01001600,0x5101e71c00061200,0x562ce92d02000416,0x550c36d402010410,0x43d344f400010610,0x314b798bd00020416,0x32702dab502010114,0x326e1688d00010216,0x4fcd95cc02001402,0x4fcd95ec00021600,0x32702dac501020214,0x4f5215bc00021402,0x4fa0b76402011400,0x325cca9c500010314,0x8b9326b02041000,0x113286fc00031400,0x4d88088500010116,0x1d2e067402040410,0x75b45e400011600,0x43d9d58c01000610,0x36379799502000512,0x3a01e6dc01020410,0x325f3591501000216,0x36379795500020512,0x325f3590d02000116],#[pAct2,pAct18,pAct0,pAct3,pAct24,pAct25,pAct29,pAct38,pAct1,pAct4,pAct14,pAct69],#[0xc440c1181981b1bbd8ccc5388b4409b4,0x44],17,0x51c531,0x91644f,#[0xf8341a0006800160000000000500800000c,0x0]⟩
private def orb_5_11 : OrbitBank := ⟨#[0x5476638c00190100,0x4ec002a400010128,0x52a6033c00060120,0x31d58089500080116,0x548523f401190000,0x31d8198e500030114,0x547663cc00150200,0x4ec692bc00020228,0x5271152400180110,0x5476639c00160100,0x5271154c00180220,0x36974e9ed01140006,0x31d7f984d00020116,0x4ec0034c00040224,0x2c4e588cd01150002,0x4ec002d400040118,0x54b2368401180020,0x53e792d400090110,0x4f1a04c400140204,0x4f1a051400180204,0x31fce094d00140106,0x53e7935c00090220,0x4ec692ac00020128,0x52a6035400050220,0x3553c68b500150102,0x56fb667401180004,0x4f1a04e400140208,0x4ec0035c00040228,0x4ec0028c00010118,0x52a602ec00060110,0x4ec0037c00080224,0x52a6036400060220,0x5271153400180120,0x4ec002b400010228,0x4ec0037400080124,0x56fb667c01140008,0x547663d400190200,0x5271154400180210,0x31d58086d00040116,0x4ec0032c00040128,0x547663dc00160200,0x53e7932c00090120,0x52a6031c00050120,0x54b2366c01180010,0x4f1a04fc00180104,0x33c48887d00050112,0x44ee03fc01160000,0x4ec0030c00040124,0x4f1a04a400140108,0x4ec6929400020118,0x31d58084500010116],#[pAct5,pAct2,pAct6,pAct1,pAct7,pAct44],#[0x48dcb68425b136da48296349b,0x6db4236d2012483],26,0x15f06b,0x13e12b,#[0x9000000003030000a0201000000f,0x12001005c1403008382200]⟩
private def orb_5_12 : OrbitBank := ⟨#[0x129b645c00400418,0xa5630c00810102,0x196d22b00182000,0x786257c00160400,0x4de433a400020148,0x115877e400082410,0x1c9b95c404200014,0x36d2439f500030424,0xbe8f3bc01800102,0x66c76f400180402,0x4e46c64c00060480,0x36c1988750001011a,0x4de4338400020418,0x1ca0a6e400410420,0x106144c01160000,0x308951a9500061018,0x36c6698a500080126,0x1e61e43400031400,0x1c72f6f400180410,0x4fce633400010228,0x10825300140200,0x37a756400181002,0x5262659400092010,0x3a2746c00181020,0x9aee85500010116,0xc1aa6fc00031800,0x2b10e1a7500400522,0x60de6abd00420114,0xaa4745400028014,0xbade7a3d00061014,0x10fb87a6d00190104,0x18b4a6d400020490,0x1456e76c00421400,0x309b889850040011a,0xf865e8fd00030510,0x565616d400092100,0x711923b00082040,0x319dd68ad00010426,0xe64e69400024102,0x339c6994d00020522,0x4de6a43400140108,0x1428c47c00410108,0x524ba4dc00060220,0x1ca0a6cc00140420,0x4fd4f33c00020228,0x387346fc00140180,0x27d75e98d00080134,0x7dae1fb00420200,0x5fb4490500400116,0x1bf669d500091012,0x159124b400030180,0x645781c02400420,0x12e046400081060,0x457a056c00420402,0x110d309cd00810114,0xf0741c00020814,0x36c41187d0002011a,0x10a26300080240,0x4fb5760c00024028,0x43b4879402400018,0x1428c6ac00030140,0x304a06a400400814,0x31c6bf99d00400426,0x1e61f63401801400,0x2389c1a6500030910,0x1c72f71400180440,0x4de433c400020448,0x46e987cc00420420,0x36269994500060112,0x4fce62e400010128,0x1023b494500030414,0xab3e42c00021402,0x390922b04200040,0x3261e786500020116,0x48f20301800200,0xafce5f402400014,0x10a1e300810200,0x36d2408b500020426,0x1556b80c00061080,0x43e174b400090140,0x7da652400810402,0x107af66401800402,0x524ba49c00060120,0x4cdc065400420108,0x1e5a65ec00811400,0xa5a2f400010142,0x86a097d00071010,0x10165c400081024,0x261a77400401820,0x573c961400400228,0x2cdaa798500024016,0xab3e44400021600,0x14e3f6c400061040,0x576993bc00080224,0x5697d5bc00021802,0x3d04950400038100,0xa5a2fc00010182,0x22bfc79c00090420,0x10100293d00010434,0x36eaf999500082106,0x855e8f500080116,0x4d64958c00400128,0x319fd58c500080426,0x314e4ea2d00060118,0x339c6993500020512,0x1b2024b00024200,0x4c4b85f400400218,0xacfe37480010014,0x339c699d500020530,0x976544400410408,0x37f507ec04210008,0x524935ec00021820,0x1e5f745c01800014,0xbe8f42c00180102,0x4d91955400081042,0x54c8540c00020182,0x3bd8d76c00164000,0x915644c00140408,0x855e91d80000116,0x5fb4490d00800116,0x31d57faed00080530,0x144124b00020840,0x37565dc00091020,0x110d349c500010194,0x4271f79400400620,0x1ca0a71c00140480,0xf1e69c00400214,0xaac65cc00801402,0x4ebc99a500400434,0x14e4c5e400011480,0x437f95fc00024108,0x23fa16f400190400,0x5791176400092400,0x3a3a075400181004,0x1bf669b500090112,0xa2f53c01810002,0x14dc764c00181040,0x524914a400020620,0x18b466dc00420410,0x4b23972400062010,0x31c47f9dd00020434,0x4c5e158c00024018,0x23d275a401800410,0x3d2da5fc00080160,0xa52069400080142,0x23cd64fc00810410,0x10d1d300010280,0x118d182404201008,0x54c885dc00180120,0x7daa51c00010482,0xab3e62c00801600,0x144422300148000,0x4e46c64400060420,0x3138189150040011c,0x2feeb997d00061012,0x4e47958400420408,0x5763931c00020218,0x45d0543400160100,0x36c4118ed0002011c,0x10d1cb00010240,0x562914d400090220,0x100fffa4500180114,0x4db324b00410800,0x484413e400028102,0x60b92ab500020194,0x31616389d00020416,0x4f4c340400020142,0x57bc15dc00021408,0x373175c01180020,0x4e42639400010428,0x1c72975c00181400,0x1457c76400021480,0xa5630400410102,0x4e9ff5a400400428,0x3490978c00400920,0x142936b400060180,0x21b429abd00034014,0x57bc15cc00082402,0x159004ac00430100,0x5249147c00020610,0x2bb119a3500091014,0x31c47f9e500080434,0x4d2e25b00140800,0x339c6995500020912,0x43e164bc00060140,0xa50642400140102,0x4d125b00180200,0x94c31e300020280,0x736626b00184000,0x524914fc00020920,0x10c57a7d00400912,0xf1e6a400800214,0x4db2231400010148,0x5836241400020482,0x1ca044bc00030440,0x949d699500800512,0x45bf26302410000,0x31c6bf92d00800416,0x177fc48400090120,0x10c24300420800,0x10a1db00410200,0x3d0494ac00034100,0x1b1625b01420000,0x8ad11db00020240,0x3b9cf70400030480,0x4de433ac00020442,0x392686dc00062100,0x35d517dc00180420,0x4fd4f2ec00020128,0x144fa6ec00021804,0x22b472c00068010,0x2b277e8fd00070110,0x4ebff60400400824,0x484a03ac00420102,0x1c7324f400010490,0x37316f401180002,0x3626699bd00030118,0x4e99965400020460,0x43b416b400091040,0x4e99966400080460,0x11b2072400430400,0x4af0957c00061020,0x855e96d00081016,0xacff36c00018014,0x2527e0aed04210006,0x8ac15b400082014,0x1c72f70400180140,0x1c73c49400010460,0x39d697ec04200018,0x57a7838c00020824,0x101f060400800610,0x110d309ad00030114,0x4ebff7ec00081420,0x5782039c00020428,0x5791176c00062400,0x4fd4f30400020214,0x32eb89a5d00030520,0x4f84f78402400028],#[pAct2,pAct9,pAct16,pAct13,pAct10,pAct17,pAct11,pAct1],#[0x54dacd7736b97b524a2e81ffb,0x1abd917854514a9ad8001ce1b,0x5a9254f2c12616178a23118a3,0x33cfe7ae1b2a426234081a963,0x1ea2fca33f3c9ffffd88c37b3,0x2984fad5eef90bbcb9a9ffffb,0x4bbf7f7ff7d3c382ea5cbc2bb,0x1f968e5e1c13],119,0x41e203,0xce491f,#[0x4800140005808040203000060e008000c00,0x18000024028004e00030100000000400202,0x36000003c0000008080805018004e0f,0x1000801801984003f018000002208000800,0x81c0400488080c3c0080008181302c0000,0x1811008a0060283c0003009482014,0x1c84c00000b000182e0d8383a00000ec0064,0x33c12030c311c21a]⟩
private def orb_5_13 : OrbitBank := ⟨#[0x2cd5d692d00401016,0x30129eaed10030104,0x1ca0548400060110,0x9a3370c00411008,0x38a126b00421000,0x1c72f70c00180140,0x3163bb8bd00080116,0x473945fc10010018,0x4fc6758401120008,0x976543c00410108,0x4c6827302401000,0x10f91d300010240,0x567c068410020208,0x786f46c01160000,0x8c3032400010148,0x43b4071400061040,0x1328e55401400102,0x1c72f6b400120140,0x8ac06a400400214,0x9d0772c01400018,0x324e459b500030114,0x45fc938c00101042,0x1328f41c00410102,0xafed798d00101106,0x5126f46410020018,0x1ca044b400030140,0x5683a66410020108,0x4d5e968c00101048,0x117426b00181000,0x129b645400400118,0x4fd4f2d400020118,0x9a2575c00161000,0x78205b410000118,0x4fa8147c00110108,0x4d8c872401100018,0x4738a59410010042,0x43b416ec00091010,0x100fffa3500120114,0x4fa814c400120204,0x1381759c00401108,0x4fd4f32c00020218,0x4fa814cc00110208,0x2d75d58a500101016,0x8bd043c00100148,0x5755668c00021048,0x976656c01110008,0x55f4e97501110006,0x9a3371400141008,0x9d7f5ac00401018,0x8c302fc00010142,0x4fcdf52400021204,0x976657401410008,0xa86b090d00400116,0x8ac069400100214,0x10f823310080040,0x4ff4677c00401208,0x4ff3364c00121008,0x5870695d00011016,0x10f824b00100240,0x2d762c98d10010016,0x4fd4f30c00020214,0x8ada20300420200,0x1ca054d400060140,0x4d8c951c00011018,0x3d0e17e410090010,0x5683a68c00420108,0x8ac05cc10080014,0x4f84f77c02400018,0x326e1692d00081016,0x4fd1885d00010116,0x19f564ec00090110,0x1381759400101108,0x4ffaf65c00101208,0x10f822b10020040,0x324e3994d00120106,0x1c72f6d400420110,0x4ff3041400021042,0x9a336f400141002,0x129b641c00100142,0x4fc6756401120004,0x4fa855dc00160100,0x880121300080240,0x325f3796500021106,0x43b4170c00091040,0x43b4865c10010048,0x8ad11e300020240,0x45fcf41400101018,0x567c066c10020204,0x4d9195ac00081042,0x26df23b10000240,0x97dc7d401401008,0x324e579d500130104,0x1381547410000148,0x1c72f6ec00180110,0x9d0773401100048,0x4fac08f500100116,0x117225b00140200,0x4dea33e400080142,0x8ac05c410020014,0x4fa2e61c00400218,0x12c8444400140108,0x4fa814a400120108,0x43b4170400031040,0x4f4ea41400420102,0x572fba4500111006,0x5621ca8d01101006,0x330ac68a500021016,0x4fa814e400120208,0x43b406f400061010,0x976655c01410002,0x8c302cc00010118,0x3248bfa6d00031104,0x4fa814ac00110204,0x4fa7b5bc00180102,0x4de433ec00020148,0x1381160400401204,0x586afa5501400016,0x253823b02410000,0x12a622b01420000,0x45fd064c00121040,0x9d1652c00011048,0x364e4a9e510020106,0x57bc152400021108,0x8d9475400121004,0x2bb119a4500031014,0x12c8442c00140102,0x4f4c340c00020142,0x116065b410000142,0x4fcdf53400021208,0x97dc7bc01401002,0x1ca0450c00090140,0x97dc7c401101008,0x9a3370400111008,0x9d0772401100042,0x4ff3638c00021018,0x8bd041c00100118,0x88c26b01180000,0x25f624301400200,0x9a336ec00411002,0x4495759400430100,0x1a2216ec00190100,0x324e3993500110106,0x1c6b678c02400110,0xafed799500401106,0x138115fc00101204,0x128f24b00410200,0x128b860402400014,0x44e7392510000116,0x128d67e410080110,0x1328e57401400108,0x3261e786d00020116,0x9d1651c00011042,0x38a6c7ec10060010,0x4fdaf3b400100218,0x8bc722300180200,0x586afa4d01100016],#[pAct9,pAct1],#[0x2bdd5b7f9,0x260fc1979,0x58517fee1,0x1ff92fac9,0x689d9d89],78,0xe49155,0x7f5f7f,#[0x38000c00008082a01008000200010100403,0x18005605070681201038200000008000000,0x30200e2109848000b001401007008101c07,0x2e800000d0b0201e020002c8000018b80806,0xa2000e8040e6c1381ce4000a04c0c00]⟩
private def orb_5_15 : OrbitBank := ⟨#[0x8c0f23302140000,0x5244173c02040110,0x4fa855ec00160100,0x5629151400060210,0x314e829a501040016,0x4f4705bc00140102,0x4fd4f37400020214,0x4fa2e45401000214,0x8ac022300140200,0x4fb0645c01020014,0x57a795ac02040014,0x564775a401060010,0x5244172c01040210,0x562914fc00060110,0x3634c799d01050012,0x313a798bd00040116,0x324c3691d02000116,0x32515e91501010016,0x324e459cd00030114,0x36269995500050112,0x576993e400040214,0x5647759c02050010,0x325f6e88d00010116,0x5629150400050210,0x4fc6545402010014,0x3261e789500020116,0x4fc615d401140002,0x339a69a5501040112,0x4fce636c00010214,0x45cf863401160000,0x324c3690d01000116],#[pAct2,pAct1],#[0x3f8ffc079],16,0x22e975,0x1a9eaf,#[0x28140604048040c010001c00020001c0000]⟩
private def orb_5_75 : OrbitBank := ⟨#[0x4ec002c400020228,0x4ec002ac00010128,0x31d58084d00010116,0x4ec002bc00010228,0x4ec0029400010118],#[pAct18,pAct19,pAct5,pAct20,pAct6,pAct2,pAct1,pAct27,pAct30],#[0x31bc34],3,0x5e38db,0xb9da21,#[0x40400]⟩
private def orb_5_76 : OrbitBank := ⟨#[0x4fce633c00010228,0x5631161400024018,0x75a274400144002,0x57bc15d400042402,0x8ac41eb00020240,0x569475bc00011802,0x437905fc00014108,0x4713474400054020,0x4e4263f400040482,0x5244150400020910,0x577d03cc00020424,0x5769963400044028,0x54c3640c00010182,0x31c2069dd00010434,0x32fa36a5500052102,0x5764177400094020,0x5789f67400040920,0x9baf23300082400,0x524445ec00011820,0x101b159400050810,0x524414a400010620,0x57bc15a400042108,0x7dbb21300028100,0xe69e69400014102,0x36d5179ed00040522,0xabe26300024100,0x4d8c95d400044024,0x524414ac00020510,0x45fdf5f400024014,0x145306ec00011804,0x94b61f300020280,0x8ac120b00024200,0x18bf773c00048110,0x577d03dc00020428,0x5262657400062010,0x57a283d400020824,0x97de46400044108,0x339a6995500010912,0x57b715dc00011408,0x36c19887d0001011a,0x36c1988ed0001011c,0x5101e73c00092100,0x97de46c00041408,0x8c7821b00082040,0x4c59158c00014018,0x315f648b500040416,0x18b806d400010490,0x36eaf999d00042106,0x414b979400064010,0x5750061c00028014,0x4e93067c00040460,0x5769962c00084024,0x94b61e300010280,0x4ddf439c00040418,0x4df7a41400040814,0x575d035400020218,0x325f6e86500010116,0x57bc159c00082104,0x145ae76400011480,0xe3724300042040,0x9b0020b00020840,0x2cd8a798500014016,0x524414cc00020610,0x4fee646c00041028,0x4fce634400020214,0x57a7b68400060820,0x47226b00041800,0x339a6993500010512,0x5789f67c00040620,0x4fee646400042018,0x101b155c00052010,0x1b2e24b00014200,0x78e756400041402,0x31c2069ed00040434,0x57a2838c00010824,0x4d8c958400041048,0x2a7859a7500054012,0x483f13e400018102,0x880d1fb00020440,0x8ac41db00010240,0x5862777c00068010,0x36d0408b500010426,0x4fb0762400024028,0x4ddf43c400010448,0x46d897bc00044120,0x131b27300184000,0x66a823b00084100,0x60d18ab500010194,0x9c6c20300020480,0x776155400042014,0x156e22b00081400,0xaa7d45400018014,0x339a699d500010530,0x4e93667400040490,0x1155d7bc00042410,0x3469a78c00094010,0x32fa36a4d00051102,0x57bc156400041108,0x5244151400020920,0x313ad199d00044016,0x575d031c00010218,0x5244147c00010610,0x144f24b00010840,0x57a7b66c00050820,0x4fce630400010214,0x36e84f9dd00040512,0x4ddf43ac00010442,0x4fee647400082014,0x4620997500041106,0x155923300148000,0x456f15ac00048102,0x4d8c95a400044018,0xab8e44400011600,0x456f155400044102,0x45f6056c00041042,0xfee24300044200,0x31d306af500040530,0x289026b00041080,0x101b159c00058010,0x5832c41400010482,0x57a283c400020418,0x57a283b400020814,0xab8e42c00011402,0x4e93065400010460,0x4fb0760c00014028,0x8ac121b00084200,0x4fce636400020228,0x524414c400020520,0x4ddf43dc00040448,0x319dd68cd00040426,0x5101e73400061200,0x4ddf43a400010148,0x5764178400064020,0x5101e72400051200,0x57bc158400041208,0x524414fc00010920,0x9a3374c00144008,0x57a783f400040824,0x4ddf163400042408,0x4d91960400084014,0x339a6994d00010522,0x4e4263fc00040428,0x57a283ac00020414,0x77615ac00048014,0x348f16d400040910,0x882a20300040840,0x524414e400020620,0x577d039c00010428,0x57b5765400040610,0x990722300021800,0x4d8c956400041018,0x4eb967f400041420,0x5101e72c00062100,0x4fce62ec00010128,0x78e156c00041204,0x4ddf438400010418,0xf5741c00010814,0x78e758400041600,0x2cd5d697500041016,0x57a7b65c00060810,0x4ddf43cc00040442,0x24825b00021400,0x4f47440400010142,0x315f6489d00010416,0x3bd2d78400164000],#[pAct18,pAct2,pAct25,pAct1],#[0x6598600fe187e59b2,0x4f2d4ecc3cd4e61fa,0xaaf4bb7b13b5a6ea,0x14223738618180002,0x3981801818609c522,0x1962],83,0x5e907d,0x793e4b,#[0x90000000000080404000040601000000203,0x30020d80c0200000005c0403000000c,0x200c0e06040001223000640400090680402,0x810000a0181c00040485866001701c0464,0x3d84002113281820070201c060521090981a,0x380600]⟩
private def orb_5_77 : OrbitBank := ⟨#[0x44bb063c00101048,0x8ac41f300020240,0x4fc7653c00021104,0x4fc7653400011208,0x4fee63d400021018,0x4fc7652400011204,0x4ff363f400101018,0x8ac41e300010240,0x4fce634c00020214,0x5134766400101204,0x45f603f400101042,0x4ddf43ec00010148,0x57b7154400021108,0x5750668c00011048,0x4fce630c00010214,0x4ffaf66c00101108,0x4fee041400011042,0x4ffaf68400101208,0x2e10e28c500101016,0x4fce635c00020218,0x4fce62d400010118,0x4f47440c00010142,0x4fce632c00010218,0x330fef9e500101106,0x3308c68a500011016,0x8c7820300021040,0x4fc7654c00021208,0x57b7152400011108,0x325f6e86d00010116,0x325cbe96500011106,0x4fee638c00011018,0x4fc7654400021204,0x5121e3bc00021014],#[pAct18,pAct1],#[0x3d572ded1,0x9],17,0xc5c7b,0x52b25,#[0x20042e000d83400170000014130000c0202,0x0]⟩
private def orb_5_79 : OrbitBank := ⟨#[0x4fce637400010214,0x325f6e89500010116,0x4fce637c00020214],#[pAct18,pAct2,pAct1],#[0x112],2,0xd76859,0x26dc1,#[0x2]⟩
private def orb_5_86 : OrbitBank := ⟨#[0x13a943c00010160,0x2cd24301000420,0xafbf69400010412,0x4db1f7ec01040210,0x5791a60402010042,0x13a955c01000142,0x575d038c00010224,0x43a0063c00040260,0x3d7fc59400010340,0x12c621b02000440,0x27fb1e98d00010314,0x316b3a8c500040216,0x5791a5cc02040012,0x9d6796d01000116,0x575d03d400020224,0x4db2255401000412,0x36d81a99502010016,0x4fcdd47402000124,0x28f26300020410,0x13a957401000160,0x36d54a8a500010216,0x741e77c02010060,0x3d7ef5fc00010610,0x575d041400010242,0x4db2257401000442,0x578a246401000224,0x13af41c00010124,0x4dab468400040640,0x8c2521b02000420,0x314bafaed00050310,0x4db9a62c02040042,0x576393f400040224,0x4d8c93b400010442,0x4dab465c00010640,0x586b668c00010260,0x315cd49e500040314,0x10d146401000610,0x215423b02000140,0x9ab020300020240,0x98165b402000114,0x163524b00010420,0x9b4223302040020,0x13af55401000124,0x5791a59c02010024,0x4dab666c00040340,0x11f2a7e402040110,0x13ad5c401000214,0x2cf22b01000240,0x4dd8a66400040610,0x9b2a20b00020420,0x578a23bc00020214,0x708023b02000410,0x9d678f500010116],#[pAct24,pAct1],#[0x155350d89,0xa94df9],27,0xf2f173,0x679445,#[0x80203000784200000000000070102208,0xd0680b0000012010000c0803]⟩
private def orb_5_87 : OrbitBank := ⟨#[0x879321300020410,0x4db225ac01000412,0x4d8c93e400010412,0x325f3592d01000116,0x313ad18bd00010116],#[pAct24,pAct1],#[0xf9],4,0x9477d3,0x2fedcb,#[0x20080001]⟩
private def orb_5_116 : OrbitBank := ⟨#[0x4dac99a500040134,0x5782378400060220,0x4fc7462400020228,0x4e9365a400040128,0x129a645c00040118,0x985174c00140208,0x34ad078c00090120,0x11030a7d00090112,0x2affe3a7500050122,0x305696a400080114,0x31c1ee99d00040126,0x4d58058c00010128,0x5789962c00080224,0x3149189150001011c,0x4dab05d400040224,0x424c179400060120,0x5ff9b90500010116,0x5782377400090220,0x26c777400180120,0x12d727300180200,0x10a469c00020114,0x30ab7a9850001011a,0x5789963400040228,0x4729874400050220,0x4fc7460c00010228,0x5730061400020128,0x4c6fa5f400020118,0x4e99f60400080124],#[pAct5,pAct65,pAct2,pAct6,pAct70,pAct71,pAct72,pAct73,pAct1,pAct7,pAct44,pAct74],#[0x40981d3d88b10c4181cc4d5441854],14,0x9d33eb,0x68ea31,#[0x2602048080208000200002030040200]⟩
private def orb_5_117 : OrbitBank := ⟨#[0x4ff3377c00120108,0x115eb62c01120004,0x129a55cc01100006,0x4fc7461c00020118,0x9b1f5ac00100118,0x8c606a400020114,0xaee6999500110106,0x135c960400120104,0x24ef23301100008,0xa865890d00010116,0x129a645400010118,0x2ce6d692d00100116,0x135d759c00110108],#[pAct5,pAct1],#[0xdbc9],7,0x16d7eb,0x9a251f,#[0x200005010000000]⟩
private def orb_5_235 : OrbitBank := ⟨#[0x31e8f991d00010116],#[pAct25,pAct5,pAct36,pAct75,pAct1],#[0x23],1,0xe767af,0x75e58f,#[0x0]⟩
private def orb_5_236 : OrbitBank := ⟨#[0x715c23b00010240,0x4fd495b400010142,0x8c3d21b00020240,0x133047400011042,0x9a9692500010116],#[pAct25,pAct9,pAct60,pAct76,pAct77,pAct74,pAct49,pAct1],#[0x3b13b],3,0x1076a1,0xe0ae33,#[0x100200]⟩
private def orbitBank : Nat → Nat → OrbitBank
  | 2, 0 => orb_2_0
  | 2, 1 => orb_2_1
  | 3, 0 => orb_3_0
  | 3, 1 => orb_3_1
  | 3, 3 => orb_3_3
  | 3, 7 => orb_3_7
  | 4, 0 => orb_4_0
  | 4, 1 => orb_4_1
  | 4, 3 => orb_4_3
  | 4, 7 => orb_4_7
  | 4, 11 => orb_4_11
  | 4, 12 => orb_4_12
  | 4, 13 => orb_4_13
  | 4, 15 => orb_4_15
  | 5, 0 => orb_5_0
  | 5, 1 => orb_5_1
  | 5, 3 => orb_5_3
  | 5, 7 => orb_5_7
  | 5, 11 => orb_5_11
  | 5, 12 => orb_5_12
  | 5, 13 => orb_5_13
  | 5, 15 => orb_5_15
  | 5, 75 => orb_5_75
  | 5, 76 => orb_5_76
  | 5, 77 => orb_5_77
  | 5, 79 => orb_5_79
  | 5, 86 => orb_5_86
  | 5, 87 => orb_5_87
  | 5, 116 => orb_5_116
  | 5, 117 => orb_5_117
  | 5, 235 => orb_5_235
  | 5, 236 => orb_5_236
  | _, _ => ⟨#[],#[],#[],0,0,0,#[]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_2_0 : orbitBankOK andCatalogue 2 0 orb_2_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_2_1 : orbitBankOK andCatalogue 2 1 orb_2_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_3_0 : orbitBankOK andCatalogue 3 0 orb_3_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_3_1 : orbitBankOK andCatalogue 3 1 orb_3_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_3_3 : orbitBankOK andCatalogue 3 3 orb_3_3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_3_7 : orbitBankOK andCatalogue 3 7 orb_3_7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_4_0 : orbitBankOK andCatalogue 4 0 orb_4_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_4_1 : orbitBankOK andCatalogue 4 1 orb_4_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_4_3 : orbitBankOK andCatalogue 4 3 orb_4_3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_4_7 : orbitBankOK andCatalogue 4 7 orb_4_7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_4_11 : orbitBankOK andCatalogue 4 11 orb_4_11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_4_12 : orbitBankOK andCatalogue 4 12 orb_4_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_4_13 : orbitBankOK andCatalogue 4 13 orb_4_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_4_15 : orbitBankOK andCatalogue 4 15 orb_4_15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_0 : orbitBankOK andCatalogue 5 0 orb_5_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_1 : orbitBankOK andCatalogue 5 1 orb_5_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_3 : orbitBankOK andCatalogue 5 3 orb_5_3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_7 : orbitBankOK andCatalogue 5 7 orb_5_7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_11 : orbitBankOK andCatalogue 5 11 orb_5_11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_12 : orbitBankOK andCatalogue 5 12 orb_5_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_13 : orbitBankOK andCatalogue 5 13 orb_5_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_15 : orbitBankOK andCatalogue 5 15 orb_5_15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_75 : orbitBankOK andCatalogue 5 75 orb_5_75 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_76 : orbitBankOK andCatalogue 5 76 orb_5_76 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_77 : orbitBankOK andCatalogue 5 77 orb_5_77 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_79 : orbitBankOK andCatalogue 5 79 orb_5_79 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_86 : orbitBankOK andCatalogue 5 86 orb_5_86 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_87 : orbitBankOK andCatalogue 5 87 orb_5_87 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_116 : orbitBankOK andCatalogue 5 116 orb_5_116 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_117 : orbitBankOK andCatalogue 5 117 orb_5_117 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_235 : orbitBankOK andCatalogue 5 235 orb_5_235 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem ok_orb_5_236 : orbitBankOK andCatalogue 5 236 orb_5_236 = true := by decide +kernel
private theorem orbitBanksValid (t c : Nat) : orbitBankOK andCatalogue t c (orbitBank t c) = true := by
  unfold orbitBank
  split
  · exact ok_orb_2_0
  · exact ok_orb_2_1
  · exact ok_orb_3_0
  · exact ok_orb_3_1
  · exact ok_orb_3_3
  · exact ok_orb_3_7
  · exact ok_orb_4_0
  · exact ok_orb_4_1
  · exact ok_orb_4_3
  · exact ok_orb_4_7
  · exact ok_orb_4_11
  · exact ok_orb_4_12
  · exact ok_orb_4_13
  · exact ok_orb_4_15
  · exact ok_orb_5_0
  · exact ok_orb_5_1
  · exact ok_orb_5_3
  · exact ok_orb_5_7
  · exact ok_orb_5_11
  · exact ok_orb_5_12
  · exact ok_orb_5_13
  · exact ok_orb_5_15
  · exact ok_orb_5_75
  · exact ok_orb_5_76
  · exact ok_orb_5_77
  · exact ok_orb_5_79
  · exact ok_orb_5_86
  · exact ok_orb_5_87
  · exact ok_orb_5_116
  · exact ok_orb_5_117
  · exact ok_orb_5_235
  · exact ok_orb_5_236
  · simp [orbitBankOK]

private def prefixDepth : Nat → Nat → Nat
  | 5, 0 => 2
  | 5, 1 => 7
  | 5, 3 => 6
  | 5, 11 => 1
  | 5, 12 => 10
  | 5, 13 => 5
  | 5, 76 => 6
  | 5, 77 => 1
  | 5, 86 => 3
  | _, _ => 0
private def countdownWords : Nat → Nat → Array Nat
  | 2, 0 => #[0x602a]
  | 2, 1 => #[0x602a]
  | 3, 0 => #[0x202702e0400d0200680941801008b]
  | 3, 1 => #[0x8064020812009204a02d]
  | 3, 3 => #[0x200a01003405c0a01002b]
  | 3, 7 => #[0x402c1006a]
  | 4, 0 => #[0x240300301402e4300301400405805018b,0x228300100be0b4200600201dc2688004b,0x200a90600600200200a00b20801000c108c,0xd06002003604004006006804504004a06006c,0x403d0100201c00b84f0420c81603002b,0x200e208d04012308110004012e03008002c,0x610029]
  | 4, 1 => #[0x4825008007104001000800cd020010018004704d,0x3c1410400080064810d0200180021c11d044010d02e,0x1024810e08c020822c08006104001000800c704d,0x3f02002002d02002002003905104002006c,0x3c080023408002000c5020008002e808e02000a702e,0x182380a00800200100194040020030008e0a402d,0xc100100200c81702304b]
  | 4, 3 => #[0x381280f80400228130086040026013008604002d,0x3008302000c7020c080021c08b020c08003a808202e,0x8811008007d02181a8080041025810c08004b02d]
  | 4, 7 => #[0x40e03c0e03c1006c0b0401f02c1006a,0x30400d81502702b]
  | 4, 11 => #[0x17030080381805010034180601004a,0xc0c01202002a0c01802005c0500801506b,0xc080341e0300802a]
  | 4, 12 => #[0xa8180100c01e4180100c00403805006b,0x1106002002702d0a00400600c00e706008508c,0x520200a006204a0600200af04d06002802c,0xe04906008006706008508004007005604504c,0x14010004041810800109043c105040010b060020904e,0x1002102d02002002a02002002002702f04404c,0x80400801203a0981002f02b]
  | 4, 13 => #[0x4008602000dc021c08d0220080025008d022008002e,0x604029]
  | 4, 15 => #[0xe03802c]
  | 5, 0 => #[0x1b48440b68c63bab486,0x403001e038012008032034037112008032c,0x2e03001200803203403670c01b92601002ec,0x200201800e00e02470dd1a00a02a026010c,0x1541200601600200ea0e00530c012006016c,0x1d0c02600401401200601603a03d10c03c004c,0xa68280240020010074224002001007000550ad,0x1f91200202404014a015412002024e14b14c,0x121200602000202200e02d104f0a010a10004c,0x12002018028f0c01ba2600401e01220a010c,0x7003805802d08d0098214012105082ae1801ad,0x20023108008006006020020002002022022c,0x1e008008006006020020022023208008006c,0x1e008008006020022d0b91001000400401ec,0xa00800800200201c01da0a00ba10010004c,0x7407007dc045820013a14008004000803ad0ad,0x20a00a01001140800830530800800200200ec,0x1000800400e007003cc1400a0080040010008d,0xa0e00530800600600200200e00f208006006c,0x6f04c04004a0400400540800600600200ec,0x1000aa1000600100080076100020010010006d,0x150bd10004208006304005808006003908006c,0x1908003c0a00800200201d40800200201c002c,0x200201c30ba1000401e10820a11000401ec,0x1800200e00e02400e70df0c00a01020a008c,0x130c00600601600200f106006016006002002c,0x90400401400540600601600600200ea0e004c,0x1d0400401400400600601600620cd04c0c004c,0x400401400600601630d406006016002f0cc,0xd03000800400200150180040020010008007b0cd,0x1a06002024314015806002003906002002002c,0x10c20600201800200220dc04004206504004c,0x201800202801c042002f0c51a00a02bd04c,0x201802810d71a00a02a002002018029202c,0x403001e039a0a10230a00a40b80c01a002c,0x17010601e1cc32340a15498202e9,0x70dd0a02a20c01a00200201802820c01b910c,0x10e00530c00600601600200201800e00e024c,0x1400600601620c004004015406006016002c,0xc0830419d0420300080040020018030008004d,0x10683418020106004029]
  | 5, 1 => #[0x1810018020080c0080a0281202f08a,0x600200aa0a00530800600601000200b106c,0x6f0910510800490400400e005406006010c,0x1002801400a0058c1000800e002001800c010d,0x120600600600200b106006006006002002002c,0x200aa0a00530600600600600200200a00ac,0x13024410008a044820010008004a03001800c006d,0x1200a709a08004004004004006006006006c,0x200b10600601000600200200c00200a00ac,0x140600601000600200aa0a005308006006010c,0xc018080064134160400520801007004b,0x1000200200c00a00a01270990400400e004c,0x400f40600601000200aa0a005308006006c,0x5002c408004007001800c0107843012210004d,0x600200200a00b20600600600200200200ac,0xa0400400540600600600200aa0a005306006c,0x12709908004004004006006006f04c04004c,0x210a00530800600601000200200c00a00ac,0x400e00600601020800400400f406006010c,0x390200200c00200200200c002f08c09a04c,0x784a8240119020010030004003984000800400cd,0x10008019908e01000801a7090810008018002d,0x61408001000220194808001000200048c30006c108f,0x482001001c0043846408210308b015025212c02d,0x51c22409d045020012a10d050044412210004d,0xf08d0510601000600200200c00200a00a012c,0x5004f05b04a0400530800601000200b204c,0x490400400e00540601000600210a005304c,0x20810400400e005304004f08104f08d04c08c,0x10008004002001000fa0800e0020018020006d,0x16010008004002001000c204002001000b204002d,0x6008002000c5020008002000e10200080020008002e,0x640080011c020004600800100020005f8080010002f,0x228112080040020014605f02e816008004002d,0x200a00a00a00b704005304005105e04c04c,0x5a04005904005605106006006002002002c,0x200c002f08c09a08004004004804004004c,0x200360800200200c00320200200c002002c,0x200c20970200200c00220830950200200cc,0x20820610308082001001c004104700c410102d,0x1b020004002006000800400c7841c2320800ed,0x4c3000d8420002000800c08219083c21402000800ce,0x400e709902108209803b03702002002002c,0xc00a00a012209304005108208c04c08004c,0x20820800400400f904005308006010002002c,0x10008004002a010008004002001000ee0800ed,0x2780c404002f010008005a020010008005602d,0x200c00200200c208209908004004904004c,0x100080061060010008004002001ec20410002d,0x6818002000b40600080031c180020008003b418002e,0x9043b61cb0e0075018004012687b03a21c00ed,0x3000800400a0058813e0ab045020013a0c002d,0xf05b04a0400540600600200b004f05a05206c,0x10008004002001e4100080060030810009004d,0x8002e418002000800328180020008002000a106e,0x7010a040011d060009a06000800390180020009706e,0x50400540640520600600200200a00b205004c,0x1000a80c0020010008004003c840010008006d,0x30e00f806002003906002002003a06002002c,0x10008004003a02001040c5040026818004012d,0x48e0e2c3800e6818002000c4060008002000a106e,0xb205d04a04005d0600201220e00f406002c,0x1a02001000c4040025018609206003000800400ad,0x1c06002003906002002003406002002002002c,0x2002002003e08004004206404005a06002c,0x100080040030810008004002001000f208406d,0xe40200080025c08002000b9020008002000ca02e,0x68c08e811b022e0400080010002f0040008d010002f,0x8002e4108040011c0e0c3800fac080020008002e,0x2002003a02002002002003402002002002c,0x10008004002f84b00c204002f010008005902d,0x164080040020015008004002001000f404002d,0xe82010814080020008002000c70280080027008002e,0xcb0600180020008002841800600080020008002e,0xe022c10009d06003000ae0c006001e81800c002d,0x40400540600630530600600200200a00b104c,0xa830018004002001d420010008002001000c006d,0x4206006304005806006003906006002002c,0x1000aa040020010008004003d040020010004d,0x1081000be0400200164080040020016808004002d,0x11040020a040020010008005e08004002000aa02d,0x17030008018002104702320c0020060008004f08d,0x5c19a060008002483570800180020031606000800ce,0x100080059060010008004003b820418210204d,0x2002209b08004207f06003d06002003806c,0xc30940600200c002f09d0410820600200cc,0x7848c200083060010008005d04103742000c002d,0x200d80200200c00230950200200c002002c,0x1b08502002002002003f08408409c03e08102c,0x1406006010002f09d0830810200200c002208c,0x1c03001800c003902001001c0060030041e11b08d,0x1406006010002f09d08004004004006006006c,0x140200200c002f09d0400400e006006010308c,0x4219026408002000920d1c20002000800c0821b08e,0x19020038410308a0300400042092840823611d02d,0x20014605e020016c08004002c010008004002d,0x30810200200c002209a08c]
  | 5, 3 => #[0x1001c8080040010008004002003001a408004d,0x11902000800324080020008002601cf040008002e,0x1000800ca05c024410008a04881000ce08f04d,0xc0018902000424040410c820a04000850080019804f,0x601cf0400080020008006901000400080020008002e,0x8810009c08a0400264080040039010008004002d,0xc100043c0d20400080020018a04b8111040010a04e,0x12c080020008002000970200080020008002000a702e,0x8003c008002000a5020008002c8080020008002e,0xa404000a8810002000650080014402000400099010002f,0x10008004002b810008004002001000ce05402d,0xca0200080024408002000a8020008002000b502e,0x94097025408002000d802000940200091020008002e,0x15808002000c5020008002000970200080020008002e,0x11808002000fa02000b90200080029c080020008002e,0x800200097020008002000800290093031808002e,0x130080024c0800240080020008002f808002000b102e,0x1000ae040020010008006502b015008004002d,0x14c080050020010008007e02001000e204002d,0x8f020008002000800294096025008002000cc02e,0x5204004203a02003702002003302002002c,0x2002007f04004002002002002006007204c,0x108100090020014408004002001381f608002d,0x5303704002002006205904b04004a05102c,0x2002007204004002002002002006007204c,0x190100081040010c10008204981000b008002d,0x3702002003302002002002f02002002002c,0x100080066040021008004002001000b205a02d,0x100080020009002000800280080020008002b008002e,0x80029c096025008002000ce0200093020008002e,0x1902003702002003202002002003302002002c,0x10412004002001d0100040020010019e09402d,0x2006f05303504002002006205804a05102c,0x1000800640400108104092020015410004002d,0x4302002002003803802003502002003202c,0x5504002002002006305204004004004004c,0x8002001800648100049c10a050c111040011204e,0x3205440800100021c0f88100010002000e68100020002f,0x502b81220800450244084080047826811408004d,0x116040017404000800608119042c100042811904e,0x1000800c0069020013208a05a824410009204d,0x10a0454100048c0ef040008002001d4040010002e,0x400080010003fc080c1000202041a080810c820b04f,0x34002830200025502000200026f0200020002000255030,0x25f02000200024a020002000200033d020002000200030,0x120400047f02000200020002c8020002000200031e0262030,0x2006006404004d04205b04b04005204004c,0x21010009304202001040ad04b020010004002d,0x1e0a4c0800100020005b410002210400080c100020404f,0x1824c1060820548200080040061823410409904d,0x10200100080040020014008304d]
  | 5, 7 => #[0xc05c458160360c0200200401403b83008b,0x8c04102806008d04005a0780200400400cc,0xb0600800400a00e706009902602706008706c,0x160750200400c202710802603102603802602c,0x2b0080080040020031204f060040818010b06d,0x1481001000800c3016008c04b04002240a008004d,0x1d81001000800c4814408c05c024813010404a04d,0x4706f03102202202902203002602e02b04c,0x200114161060020010014206603241000800ad,0x30690400a004207506206c06e04106d04e04c,0x101080960c008002001001400e383002420c206d,0x40c0210300840c02681004b]
  | 5, 11 => #[0x1c0581003e0260400b02006a0801003006b,0xa0581003e0260400b02006a0801003006b,0x1a0700f0130200740981003a0801003006b,0x1305804e06002102b02d02302002d02302002c,0x2e04006204006904006802604006a05104c,0x160700981003a0700f0130200700e01302b,0x1008a022008702280fa0200081022c08d020c08002e,0x1104604004c05204604005305c04704004f02c,0xe4080160400d4100200600f41002a04b,0x60400e813020074100330400801803904b,0x201f40800420248100098043020012409604d02d,0x86040018504001000600194043408502000d402e,0x58100350400801803d02c0801f01302b,0x1a04c0801d0400801803102c0801e81302b,0x480c81003804c080190360740981002b,0xb02c02302002e04006304006b04b05104e06c,0x40640801703604c080190360740981002b,0x381000434100042c1120418100043c085031408002e,0x140640801c0260400e8200680801003006b,0x1703202002402002c]
  | 5, 12 => #[0x710800200710690600400a00400e008006c,0x4830010014004007002000e504901800a208008d,0x4001bc092030014410010006884000800d106d,0x190400e008006104e03704008007d04e03704c,0x13c09902000c402000ba02800e30264080031008002e,0x3808002bc0ce025408002880a002a00ba02a809902e,0x1104090400040004000407041704000337020002010222030,0x3010b04241000400100041c112052c10d04dc11104e,0x1208001000200053008041008222041a089c100821e04f,0x3825810208504002001000a4040827411808b04d,0x441110400100041c11d05841210444111040010004e,0xe0e3504000e000c110c110c00040005250401044b0421050,0x2000100e0816058f020003800180c0c058600010000811051,0x20015c0810418200100082053023c11808b04d,0x9810c0c804f02001c0080059040010020408304d,0x2008003d02002402003703502002602002c,0x22020302220221022302190240022e0311040002000225050,0x10c0ac044029010c0c406102c01080a606102d,0x31c18a18002b8200080100020040008012204d,0x286000ee04e027834c1960c706881001a204002d,0x1102e02f06d06b06707102007102002006706c,0x2c180072418c062c180063818c062c180065430002e,0x8408e0334099020009a02000960c54180063818c06e,0x386b44100004750200010040804042302078100008340400031,0x458100010008440b1830086010c4a183c300060c0cf,0xa81e01000400208200080101020011008004402d,0x100202080021810c0ac042021814408406102d,0x380be02540b702380cb02540960400080080008008e,0x12c0800080810202420454090810e027c045408b071102f,0x90670650c002007706002302303604002008c,0x1101640a20cd065831c1a204006881000800d106d,0x20fc0803e0200401d83906e0d43001006b,0x150c002006202007103106e02007202303206c,0x20028018506003981800ce066032c1940c006d,0x1c0020003170600100038002000a06180830086e806f,0x70101c0803c1210030301014049,0x400a00240240370600400a00200c106008c,0x670650c00360600600800e00200c00800ec,0x610610c003102203106106f02006e02002c,0x2002c40c0040030030a0c006a860008604002d,0xb060406020c06080d06080c8,0x60808605102101840aa05606007003001000ed,0x8c099031009902000b1026010106002000e001000ae,0x181000a406102701000b6043031013c08006302d,0xa04000820117040010002000200058a0800100020002f,0x1814808606102c81e8100040080820008010002d,0x8002008008008104002402303708303502c,0xf02e02f0400800710800200600a00f604002c,0x160e102202f04008006e0800200600a00f104c,0x25c10004302001080a2042030813c08004e02d,0x704300095041020014a08e046020013a08304d,0x1015c100040020020008010104001002020a104d,0x881080c004e02b0200200100020040010204302d,0x600c007606104008008004004002202202c,0x7102303206006e02006e02002006a06906c,0x2002c40c004005003000c302001081800c00cd,0x106040a020c06080e0406080e8,0xc40200200600600d60600e00c00800e00ac,0x60a020c0e06080e0b06040a8,0x19b828000c00080007000100014000c0181008082c0c000f1,0x400380020005900800100050302000454091810e02f,0x5820013a083040025c28004002082000801240ad,0x1002020a10400404180095041020014a08e04d,0x88410002000a0804000e2830004000400200010008f,0x400140140020010010004008085000801c004d,0xc00180850002001c00100050303101400200040002f,0xa00600e00c00400a00670610770600a00ac,0x6080e0b060a0a020606080c8,0x60c060e0c0b060a0606060e8,0x16c140018007000c001400280030006001800180030002f,0x200810a00800e004005f0400400a402002c,0x1f0a00800800800800410400400a002008004c,0x90a0202080a020e0504040a8,0xa10600a00a00600600a00800e00400bd0ac,0x15bee979fc3,0x10c0a0606060c068]
  | 5, 13 => #[0x8018c09005102301000a4063024014408c04002d,0x817408c050023010009e061024014008c04002d,0x7010140800040b020f81018082204060200010380f4c0400031,0xe02002102302003502102d02502003702102c,0x3010009605f0250118080050031812808c04002d,0x50200020e038b0200020c020702050200020a021d020a030,0x3010000cce04000201010080800040b020101000082e0407031,0xd02502003702102e02502002b03f02603102c,0x32d020302030200028503c402010203020002150201030,0xf036f0282020202020200020b02020200021702070205030,0x1950201020202140201020c02160201020d020b021a0206030,0x2c05dc08101010216040408b0106037e040c081016702f,0x202a602870202038e030]
  | 5, 15 => #[0xf03303303403103103203203303403403402c,0xd0208020c020a020d020f021303210201020c020e0211030,0xc02c02e03102f03303303403102a02902d02c,0x1a0428084810d03680408084010c02140434087811302f,0x502a]
  | 5, 75 => #[0x1020034280602005c300c0280a02008a,0x5818024040054180300400a03005008b,0x140400d06018040170c02809c0c02a,0x1802805008012c0801506c0500801606b,0x80140600a0110200150a00c0200270cb,0x170c02e0300803818050100341806a,0x1008038190400d0601804a]
  | 5, 76 => #[0x1404008010072040080100200c01801002b,0x2002002007204004002002002002006006c,0x6821410008f02001000c0040020010008c0dd04d,0x1404504004a02002006003404504005202002c,0x11302041100414100043c0800304100020008006e,0xf05104902002002006006002003205604504c,0x2002002006006f05404504004a02002006c,0x10f02d0080020008607641000200080071010004e,0x504005205604504005202204004b05004504c,0x14d040c100042410f04141000428080060008f04e,0xf02002704c02002003804002002002007504c,0x10019e091048010811806204001000800d104d,0x300180040032820811208e04902300d808002d,0x4008030074040080100720400801002b,0x2002607d04002002002007204004002002c,0x504005202002804504004f02002003d02002c,0x180200080040067821410008a020010018005404d,0x6006002002f05604504005302304004e02c,0x120bc128200540400803905c0a40801002b,0xf81f810004002003c810008002001000800c006d,0x3a01080800468200116090042820012c08004d,0x6e04f02002104c02002003804002002002c,0x9820c144080020010019208e048814410004002d,0x1404008010032040080100200400801002b,0x3602002002002002d02002002002002002c,0x10008006702001000aa040020015808004002d,0x1000cc04002001000ec040032010008005d02d,0x940800200080020008002000cc024c0b002000ad02e,0x1d0100080040038810008004002001c008004002d,0x4000880100020004000d88150020004cc080010002f,0x1b40a204f02001000c2040027010008005802d,0x800224080020008002000800200080032808002e,0x400801003a040080100200400d01002b,0x1900800400278100080056020010008005602d,0x9813c08004002001b8080052020013c08004002d,0x40008001990200040008001000200040009d811502f,0x10008004002001ac0a6040028010008004d02d,0x2003502002002002d02002002002002a02c,0x1000d804002e8100080057020010008005d02d,0x8002000c202440a902000a60200080028008002e,0x14204d4080013202000400095810002000400095010002f,0x74080100200400d0100200400801002b,0x1002002e02002002003d02002003502002002c,0x100080074029814409c04002001000ce04002d,0x80020008002280800200080020008003c408002e,0xe02002002003d02002003502002002002d02c,0x1d00a6051027010008004003381000a004002d,0x8002280800200080020008003c4080020008002e,0x1602003202002002f02002002002c02002002c,0x6902002002002006006002003204005e02c,0x7204004002002002002006006a02002002c,0x4e02002f02002002002607d04002002002c,0x304004a02002006002f04504005202002204c,0x2006006002002905004504005403504002c,0x34810a080054824c100084040023411204002d,0x3404305104002205002003004002002002c,0xe8080100200e4080100200401803002b,0x1404002002002006f04004002002002002006c,0x2007404004604005304102304005302002c,0x2a02002002002002003204004304002002c,0x3202002002f02002002002c02002002002c,0x1000a4080043010008004002001000e005602d,0x2002003202002002002002a02002002002c,0x1481000a00400200180080040027010008005302d,0x1cc080020008002000b6024c0910238080020008002e,0x78080100200400d0100200400801002b,0x10018007002a81000a6040020013c08004002d,0x2104d02002003a04002002002006a02002c,0x904f05303204002204a02002006002e05102c,0x1000800c0029821014808304501000800c002d,0x405204102205102003104002002002006a02c,0x2002e02002002002a02002002002003404c,0x2001000850200100080040037015008005102d,0x2006007604102002002006003204004004c,0x2607a04002002002007004004002002002c,0x4f02002804504004c02002003b02002002c,0x2820012004304002300d808002001001a808504d,0x1000800ee0400200080040020030019e09404d,0x39c106080044823c10a080049820013807804d,0x1a04002002002007004004002002002002006c,0xbc080120400b00801e0200400801606b,0x6904f04504005103304002002006f04504c,0x1000a60840400294124080040010008004006d,0x2002003302002002002002b02002002002c,0x1380800400200184080040027010008005402d,0x10008004003b814c0a204002001ac08005002d,0x380800200080020008b0200080020008002000f402e,0x1000de056020014c080040027810008004002d,0x2003b02002003302002002002b02002002c,0x1c40a405002001000ca040027810009a04002d,0x380800200080022c080020008002000dd020008002e,0x12c08004002001000da055020014408004002d,0x10008006d02a81000a2040020013808004002d,0xe04004002002002002006007204004502002c,0x5104002304005102003204002002002006c,0x4404004002002002002006007504004404c,0x2002002003204004602002002002003204c,0x1b40a8040029010008004e020010008004d02d,0x205002003004002002002007702002002002c,0x2002003504002002002007404305104002c,0x204010040100401502a]
  | 5, 77 => #[0x1402f02c02002d02802002802002502002002c,0x3d02c02002d02802002802002502002002c,0x2003c02c02002d02802002802002502002c,0x2502002003902002d02602002802002502c,0x802002502002003c02c02002d02802002802c,0x602002802002502002003802002d02602002c,0x502002003602702002502002003702002d02c,0x2502002003c02c02002d02802002802002c,0x2802002502002003802002d02602002802c,0x2003502702002502002003702002d02602c,0x2502002003702002d02602002802002502c,0x2e02002003302702002502002003402702c,0x2003c02c02002d02802002802002502002c,0x2502002003802002d02602002802002502c,0x1502702002502002003702002d02602002802c,0x2003702002d02602002802002502002002c,0x2003302702002502002003402702002502c,0x3702002d02602002802002502002002d02c,0x3302702002502002003402702002502002c,0x2b02002003302702002502002002c02002c,0x140802a]
  | 5, 79 => #[0xe0500801c02e0500801604e05c0a01002b,0x80400d0170280400b02702e0500801c02b,0x802b]
  | 5, 86 => #[0x1140dc05e0200170080048026010008004502d,0x1802000206020c0200020002050379021f02370206022d030,0x301030080004000202810300f0e040002010108c08140400031,0x8002080df026808002080a30228080026008002e,0x281b00ac04002e010009004c020010008a04f02d,0xc03a4020c0201020902000200020502df022f02210200030,0x1603202c02102902002002502c]
  | 5, 87 => #[0x3408802000fa023408d0220080025808d022008002e,0x140580801e02b]
  | 5, 116 => #[0x20040100a03f040280f4280603808a,0x805c100630c0058428130200741803008b,0xc0c0248280720b81f0400200801006610b,0x80328200c61800f0300800841804802b,0x4004d04004b0530200200400400400c704c,0x942803005a0401002102e0840d01904b,0x802c0200ac1401d820040140138200ab,0x80100500ee080280750a00c03804a04b,0x803581704018c3001d0260400e83008b,0x502381140810438560080083024829c08004004d,0x606008506006008009104206d02004402002c,0x1403a8500601c0268160601380981002b,0x740981003a0c0180400800802807704b,0x405c1086002c2140981003206c0e81302b,0xc02302002e06008306008b06b07106e08002c,0x80328200c61800c81b03a04c0801b02b,0x903181800cf0228128174040020020010018704d,0x110180300801381803b0421401802a06b,0x1703202002402002a02902002c02302002d06c]
  | 5, 117 => #[0x3011c08c048023011c08c065021811808e04602d,0x281180c6043023011c08c04a02281180c604302d,0x11810c08c04702301300b6041023011c08c04902d,0x602702602b03b02102602702602902502602c,0xc02202502602a03b02102c]
  | 5, 235 => #[0x201304a040180480260940803008b]
  | 5, 236 => #[0x14300e02c0c00803c18040200803806a,0x5408010034080380500860902001204b,0xc01a8600640d02803006c1202001808b,0xe4230100300400a81002005c308340ab,0x804305c0400410460470460490210a70c60ac,0x40200803c1305c0f0e00d0200802a]
  | _, _ => #[]
private def countdownPositions : Nat → Nat → Array Nat
  | 2, 0 => #[0x5]
  | 2, 1 => #[0x5]
  | 3, 0 => #[0x9]
  | 3, 1 => #[0x9]
  | 3, 3 => #[0x6]
  | 3, 7 => #[0x4]
  | 4, 0 => #[0x11]
  | 4, 1 => #[0x11]
  | 4, 3 => #[0xc]
  | 4, 7 => #[0x8]
  | 4, 11 => #[0x8]
  | 4, 12 => #[0x11]
  | 4, 13 => #[0xa]
  | 4, 15 => #[0xa]
  | 5, 0 => #[0x1f,0x1a20021,0x6849000,0x684941f]
  | 5, 1 => #[0x1a,0xac23,0x17000,0x1741a,0x822019,0xe29822,0xe32400,0xe32819,0xe3941a,0x665883d,0x986d800,0x986dc1a,0xdc78819,0x10887837,0x1088e000,0x1088e419,0x10890c39,0x13ea0c39,0x140abc00,0x140ac039,0x16eb3034,0x18ebd034,0x18ec1c00,0x18ec201e,0x18ec3839,0x1a0ce839,0x1a0d3c00,0x1a0d401f,0x1a0d5834,0x1a0d941e,0x1a0da800,0x1a0dac01,0x1a0dac00,0x1a0db03a,0x1b0e5000,0x1b0e5400,0x1b0e5800,0x1b0e5c35,0x1b0ea400,0x1b0ea800,0x1b0eac00,0x1b0eb03a,0x200f0800,0x200f0c00,0x200f1000,0x200f141e,0x200f2800,0x200f2c00,0x200f3022,0x21cfa037,0x21cfe000,0x21cfe41b,0x21d0041d,0x21d0341d,0x21d04800,0x21d04c23,0x21d04c22,0x21d0981e,0x21d0ac00,0x21d0b01b,0x21d0b01a,0x21d0c801,0x21d0c800,0x1a,0x21d0cc1d,0x22110032,0x22112800,0x22112c1d,0x1a,0x1a,0x1a,0x1a,0x22715c1d,0x2451d032,0x24520000,0x2452041a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a,0x1a]
  | 5, 3 => #[0x12,0x2c0b012,0x3015427,0x741e827,0x8a27024,0xca2e024,0xca34424,0xca3a824,0xca3e400,0xca3e800,0xca3ec12,0xcc47c12,0xec4d400,0xec4d800,0xec4dc24,0xec51817,0xec52c00,0xec53000,0xec53426,0x11659826,0x1165d412,0x12862412,0x12865423,0x12867c16,0x12868c00,0x12869000,0x12869400,0x12869800,0x12869c00,0x1286a000,0x1286a412,0x1286bc13,0x1286bc12,0x16477c12,0x17c800e5,0x1a483c7a,0x1c2850c2,0x1f887869,0x1f888869,0x1f889820,0x1f889800,0x1f889c00,0x1f88a012,0x2088f412,0x21890c00,0x21891000,0x21891421,0x21891401,0x21891400,0x21891800,0x21891c6d,0x22c92c32,0x22c92c12,0x23895c12,0x2389681e,0x23896801,0x23896800,0x23896c00,0x23897000,0x23897400,0x23897800,0x23897c00,0x23898002,0x12]
  | 5, 7 => #[0x10]
  | 5, 11 => #[0xf,0x542240f]
  | 5, 12 => #[0x17,0x80c019,0x1e13400,0x1e13817,0x2a1dc16,0x522630a,0x5a26000,0x5a26416,0x5a2a800,0x5a2ac00,0x5a2b000,0x5a2b419,0x722f800,0x722fc00,0x7230000,0x7230425,0x7230400,0x7230800,0x7230c00,0x7231111,0x7831018,0x9a34018,0x9a36000,0x9a36422,0x9a36400,0x9a36800,0x9a36c00,0x9a37000,0x9a37400,0x9a37800,0x9a37c00,0x9a38017,0x9a38016,0xb243416,0xba47800,0xba47ed1,0xba47dd5,0xd249cc4,0xd249c00,0xd24a022,0xd24a000,0xd24a400,0xd24a800,0xd24ac16,0xd24c400,0xd24c800,0xd24cc00,0xd24d001,0xd24d000,0xd24d400,0xd24d800,0xd24dc38,0xd24dc16,0xd24f816,0xd250400,0xd250801,0xd250800,0xd250c00,0xd251000,0xd251400,0xd251800,0xd251c00,0xd252000,0x17,0xd252416,0xde54816,0xe456c00,0xe457096,0x17,0x17,0x17,0x17,0xe457000,0xe457400,0xe457800,0xe457c16,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0xe458800,0xe458c17,0x10065800,0x10065c00,0x10066000,0x100664e8,0x11267000,0x11267400,0x11267800,0x11267c00,0x11268000,0x11268417,0x11e6bc00,0x11e6c000,0x11e6c400,0x11e6c801,0x11e6c800,0x11e6cc00,0x11e6d000,0x11e6d400,0x11e6d800,0x11e6dc17,0x11e6e800,0x11e6ec00,0x11e6f000,0x11e6f400,0x11e6f800,0x11e6fc00,0x11e70000,0x11e70400,0x11e70800,0x17,0x11e70c00,0x11e71016,0x12a76c00,0x12a77000,0x12a77400,0x12a77822,0x12a77800,0x12a77c00,0x12a78000,0x12a78400,0x12a78800,0x12a78c01,0x12a78c00,0x12a79000,0x12a79400,0x17,0x12a79800,0x12a79c00,0x12a7a000,0x12a7a400,0x12a7a800,0x12a7ac01,0x12a7ac00,0x17,0x12a7b000,0x12a7b400,0x12a7b800,0x17,0x12a7bc00,0x17,0x17,0x17,0x12a7c000,0x12a7c416,0x1367e000,0x1367e400,0x17,0x17,0x17,0x17,0x1367e800,0x1367ec00,0x1367f000,0x1367f401,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x1367f400,0x1367f818,0x13684400,0x13684800,0x13684c00,0x136850c5,0x13685000,0x13685400,0x13685800,0x13685c00,0x13686000,0x13686417,0x13687400,0x13687800,0x13687c00,0x13688001,0x13688000,0x13688400,0x13688800,0x13688c3a,0x13688c18,0x1448ac17,0x1448b800,0x1448bc01,0x1448bc00,0x1448c000,0x1448c400,0x1448c800,0x1448cc00,0x1448d000,0x1448d400,0x17,0x1448d816,0x14a93016,0x14a95800,0x14a95c17,0x14a9681a,0x14a9941f,0x14a99400,0x14a99801,0x14a99800,0x14a99c00,0x14a9a000,0x14a9a401,0x14a9a400,0x14a9a800,0x14a9ac00,0x17,0x14a9b000,0x14a9b400,0x14a9b800,0x14a9bc17,0x14a9bc16,0x14a9c801,0x14a9c800,0x17,0x14a9cc00,0x14a9d000,0x14a9d400,0x17,0x14a9d800,0x17,0x17,0x17,0x14a9dc00,0x14a9e016,0x14a9fc00,0x14aa0000,0x17,0x17,0x17,0x17,0x14aa0400,0x14aa0800,0x14aa0c00,0x14aa1001,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x14aa1000,0x14aa1416,0x14aa6c00,0x14aa7000,0x14aa7400,0x14aa7822,0x14aa7800,0x14aa7c00,0x14aa8000,0x14aa8400,0x14aa8800,0x14aa8c00,0x14aa9000,0x14aa9400,0x14aa9800,0x17,0x14aa9c00,0x14aaa000,0x14aaa400,0x14aaa800,0x14aaac00,0x14aab001,0x14aab000,0x17,0x14aab400,0x14aab800,0x14aabc00,0x17,0x14aac000,0x17,0x17,0x17,0x14aac400,0x14aac816,0x14aae000,0x14aae400,0x14aae800,0x14aaec01,0x14aaec00,0x17,0x14aaf000,0x14aaf400,0x14aaf800,0x17,0x14aafc00,0x17,0x17,0x17,0x14ab0000,0x14ab0400,0x14ab0800,0x17,0x14ab0c00,0x17,0x17,0x17,0x14ab1000,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x14ab1400,0x14ab1816,0x14ab2400,0x14ab2800,0x17,0x17,0x17,0x17,0x14ab2c00,0x14ab3000,0x14ab3400,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x14ab3800,0x14ab3e6e,0x18cb5400,0x18cb5800,0x18cb5c00,0x18cb60c8,0x18cb6000,0x18cb6400,0x18cb6800,0x18cb6c00,0x18cb7000,0x18cb7424,0x1a4b7400,0x1a4b7800,0x1a4b7c00,0x1a4b8001,0x1a4b8000,0x1a4b8400,0x1a4b8800,0x1a4b8c17,0x1b0b981a,0x1babc41f,0x1babc400,0x1babc801,0x1babc800,0x1babcc00,0x1babd000,0x1babd400,0x1babd800,0x1babdc00,0x1babe000,0x17,0x1babe400,0x1babe8c5,0x1cebf000,0x1cebf400,0x1cebf800,0x1cebfc21,0x1cebfc00,0x1cec0000,0x1cec0400,0x1cec0800,0x1cec0c00,0x1cec1001,0x1cec1000,0x1cec1400,0x1cec1800,0x17,0x1cec1c00,0x1cec2000,0x1cec2400,0x1cec2820,0x1cec281f,0x1cec2801,0x1cec2800,0x17,0x1cec2c00,0x1cec3000,0x1cec3400,0x17,0x1cec3800,0x17,0x17,0x17,0x1cec3c00,0x1cec4088,0x1dcc4400,0x1dcc4800,0x17,0x17,0x17,0x17,0x1dcc4c00,0x1dcc5000,0x1dcc5400,0x1dcc5801,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x1dcc5800,0x1dcc5c00,0x1dcc6000,0x1dcc6400,0x1dcc6800,0x1dcc6c17,0x1dcc7800,0x1dcc7c00,0x1dcc8000,0x1dcc8400,0x1dcc8800,0x1dcc8c00,0x1dcc9000,0x1dcc9400,0x1dcc9800,0x17,0x1dcc9c00,0x1dcca000,0x1dcca400,0x1dcca800,0x1dccac00,0x1dccb001,0x1dccb000,0x17,0x1dccb400,0x1dccb800,0x1dccbc00,0x17,0x1dccc000,0x17,0x17,0x17,0x1dccc400,0x1dccc800,0x1dcccc00,0x1dccd000,0x1dccd400,0x1dccd801,0x1dccd800,0x17,0x1dccdc00,0x1dcce000,0x1dcce400,0x17,0x1dcce800,0x17,0x17,0x17,0x1dccec00,0x1dccf000,0x1dccf400,0x17,0x1dccf800,0x17,0x17,0x17,0x1dccfc00,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x1dcd0000,0x1dcd0400,0x1dcd0800,0x1dcd0c00,0x17,0x17,0x17,0x17,0x1dcd1000,0x1dcd1400,0x1dcd1800,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x1dcd1c00,0x1dcd20b6,0x1dcd2800,0x1dcd2c00,0x1dcd3000,0x1dcd341f,0x1dcd3400,0x1dcd3800,0x1dcd3c00,0x1dcd4000,0x1dcd4400,0x1dcd4801,0x1dcd4800,0x1dcd4c00,0x1dcd5000,0x17,0x1dcd5400,0x1dcd5800,0x1dcd5c00,0x1dcd6000,0x1dcd6400,0x1dcd6801,0x1dcd6800,0x17,0x1dcd6c00,0x1dcd7000,0x1dcd7400,0x17,0x1dcd7800,0x17,0x17,0x17,0x1dcd7c00,0x1dcd801f,0x1dcd8000,0x1dcd8400,0x1dcd8800,0x1dcd8c01,0x1dcd8c00,0x17,0x1dcd9000,0x1dcd9400,0x1dcd9800,0x17,0x1dcd9c00,0x17,0x17,0x17,0x1dcda000,0x1dcda400,0x1dcda800,0x17,0x1dcdac01,0x17,0x17,0x17,0x1dcdac00,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x1dcdb000,0x1dcdb41d,0x1dcdb400,0x1dcdb800,0x17,0x17,0x17,0x17,0x1dcdbc00,0x1dcdc000,0x1dcdc400,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x1dcdc800,0x1dcdcc00,0x1dcdd000,0x1dcdd400,0x1dcdd800,0x1dcddc01,0x1dcddc00,0x17,0x1dcde000,0x1dcde400,0x1dcde800,0x17,0x1dcdec00,0x17,0x17,0x17,0x1dcdf000,0x1dcdf400,0x1dcdf800,0x17,0x1dcdfc00,0x17,0x17,0x17,0x1dce0000,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x1dce0400,0x1dce0800,0x1dce0c00,0x17,0x1dce1000,0x17,0x17,0x17,0x1dce1400,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x1dce1800,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x1dce1c00,0x1dce2000,0x1dce2400,0x17,0x17,0x17,0x17,0x17,0x1dce2800,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17,0x17]
  | 5, 13 => #[0xe,0x1006ba6,0x2e06800,0x2e06c0e,0x340c00e,0x461158b,0x4611400,0x461180e,0x4614a67,0x6a199c4,0x7419800,0x7419c85,0x9c1ad2d,0xda1d882,0xda1d800,0xda1dd6f,0xda1dd57,0xfa21195,0x12221000,0x12221467,0x122220bf,0x13823c77,0x13823c00,0x13824016,0x1382458e,0x13824c84,0x13824c00,0x138250a6,0x1382508e,0x13825017,0x13825000,0x13825402]
  | 5, 15 => #[0xf]
  | 5, 75 => #[0xa]
  | 5, 76 => #[0x12,0x3426012,0x5045012,0x7a5d812,0x866dc12,0xb67b012,0xba84812,0xbe8e012,0xbe93400,0xbe93800,0xbe93c12,0xdaa7c12,0xe6b1c00,0xe6b2000,0xe6b2412,0xecb7812,0xecb9000,0xecb9400,0xecb9812,0x10cc3012,0x112c8412,0x126d1012,0x126d5412,0x126d9012,0x126da400,0x126da800,0x126dac00,0x126db000,0x126db400,0x126db800,0x126dbc12,0x126dd413,0x126dd412,0x136ecc12,0x13ef8812,0x13f02412,0x13f07812,0x14b0ec12,0x14b12812,0x14b16412,0x14b17800,0x14b17c00,0x14b18012,0x14b1dc12,0x14b1fc00,0x14b20000,0x14b20412,0x14b21801,0x14b21800,0x14b21c00,0x14b22012,0x14b25c12,0x14b27012,0x14b2a012,0x14b2b412,0x14b2c401,0x14b2c400,0x14b2c800,0x14b2cc00,0x14b2d000,0x14b2d400,0x14b2d800,0x14b2dc02,0x12]
  | 5, 77 => #[0xb,0x3223c0b]
  | 5, 79 => #[0x8]
  | 5, 86 => #[0xc,0x2407b6d,0x4007800,0x4007c0c,0x400c40c,0x5011d92,0x6011c00,0x601200c]
  | 5, 87 => #[0xa]
  | 5, 116 => #[0x10]
  | 5, 117 => #[0xa]
  | 5, 235 => #[0x6]
  | 5, 236 => #[0xb]
  | _, _ => #[]

private def countdownWord (t c i : Nat) : Nat :=
  let w := (countdownWords t c)[i/12]?.getD 0
  let width := w % 32
  (w >>> (5+width*(i % 12))) % (1 <<< width)

private def countdownStart (t c i : Nat) : Nat × Nat × Nat :=
  let s := (countdownPositions t c)[i]?.getD 0
  (s % 1024,(s >>> 10) % 2048,s >>> 21)

private def graphPiece := countdownPiece (fun t c => (orbitBank t c).acts) countdownWord
  (fun t c => orbitRead (orbitBank t c)) prefixDepth countdownStart

private theorem allActions (t c a : Nat) (ha : a ∈ (orbitBank t c).acts) :
    minimumActionOK t c (a % 32768) (a >>> 15) = true := by
  have checked := orbitBanksValid t c
  simp only [orbitBankOK, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at checked
  exact checked.2 a ha

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_2_0 : rangePass (graphPiece 2 0) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_2_1 : rangePass (graphPiece 2 1) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_3_0 : rangePass (graphPiece 3 0) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_3_1 : rangePass (graphPiece 3 1) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_3_3 : rangePass (graphPiece 3 3) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_3_7 : rangePass (graphPiece 3 7) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_4_0 : rangePass (graphPiece 4 0) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_4_1 : rangePass (graphPiece 4 1) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_4_3 : rangePass (graphPiece 4 3) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_4_7 : rangePass (graphPiece 4 7) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_4_11 : rangePass (graphPiece 4 11) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_4_12 : rangePass (graphPiece 4 12) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_4_13 : rangePass (graphPiece 4 13) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_4_15 : rangePass (graphPiece 4 15) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_0_0_2 : rangePass (graphPiece 5 0) 0 2 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_0_2_2 : rangePass (graphPiece 5 0) 2 2 := by unfold rangePass; decide +kernel
private theorem part_5_0 : rangePass (graphPiece 5 0) 0 4 := @rangeJoin (graphPiece 5 0) 0 2 2 part_5_0_0_2 part_5_0_2_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_1_0_8 : rangePass (graphPiece 5 1) 0 8 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_1_8_1 : rangePass (graphPiece 5 1) 8 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_1_9_1 : rangePass (graphPiece 5 1) 9 1 := by unfold rangePass; decide +kernel
private theorem part_5_1_8_2 : rangePass (graphPiece 5 1) 8 2 := @rangeJoin (graphPiece 5 1) 8 1 1 part_5_1_8_1 part_5_1_9_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_1_10_2 : rangePass (graphPiece 5 1) 10 2 := by unfold rangePass; decide +kernel
private theorem part_5_1_8_4 : rangePass (graphPiece 5 1) 8 4 := @rangeJoin (graphPiece 5 1) 8 2 2 part_5_1_8_2 part_5_1_10_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_1_12_4 : rangePass (graphPiece 5 1) 12 4 := by unfold rangePass; decide +kernel
private theorem part_5_1_8_8 : rangePass (graphPiece 5 1) 8 8 := @rangeJoin (graphPiece 5 1) 8 4 4 part_5_1_8_4 part_5_1_12_4
private theorem part_5_1_0_16 : rangePass (graphPiece 5 1) 0 16 := @rangeJoin (graphPiece 5 1) 0 8 8 part_5_1_0_8 part_5_1_8_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_1_16_4 : rangePass (graphPiece 5 1) 16 4 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_1_20_4 : rangePass (graphPiece 5 1) 20 4 := by unfold rangePass; decide +kernel
private theorem part_5_1_16_8 : rangePass (graphPiece 5 1) 16 8 := @rangeJoin (graphPiece 5 1) 16 4 4 part_5_1_16_4 part_5_1_20_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_1_24_8 : rangePass (graphPiece 5 1) 24 8 := by unfold rangePass; decide +kernel
private theorem part_5_1_16_16 : rangePass (graphPiece 5 1) 16 16 := @rangeJoin (graphPiece 5 1) 16 8 8 part_5_1_16_8 part_5_1_24_8
private theorem part_5_1_0_32 : rangePass (graphPiece 5 1) 0 32 := @rangeJoin (graphPiece 5 1) 0 16 16 part_5_1_0_16 part_5_1_16_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_1_32_16 : rangePass (graphPiece 5 1) 32 16 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_1_48_16 : rangePass (graphPiece 5 1) 48 16 := by unfold rangePass; decide +kernel
private theorem part_5_1_32_32 : rangePass (graphPiece 5 1) 32 32 := @rangeJoin (graphPiece 5 1) 32 16 16 part_5_1_32_16 part_5_1_48_16
private theorem part_5_1_0_64 : rangePass (graphPiece 5 1) 0 64 := @rangeJoin (graphPiece 5 1) 0 32 32 part_5_1_0_32 part_5_1_32_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_1_64_64 : rangePass (graphPiece 5 1) 64 64 := by unfold rangePass; decide +kernel
private theorem part_5_1 : rangePass (graphPiece 5 1) 0 128 := @rangeJoin (graphPiece 5 1) 0 64 64 part_5_1_0_64 part_5_1_64_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_3_0_2 : rangePass (graphPiece 5 3) 0 2 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_3_2_2 : rangePass (graphPiece 5 3) 2 2 := by unfold rangePass; decide +kernel
private theorem part_5_3_0_4 : rangePass (graphPiece 5 3) 0 4 := @rangeJoin (graphPiece 5 3) 0 2 2 part_5_3_0_2 part_5_3_2_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_3_4_4 : rangePass (graphPiece 5 3) 4 4 := by unfold rangePass; decide +kernel
private theorem part_5_3_0_8 : rangePass (graphPiece 5 3) 0 8 := @rangeJoin (graphPiece 5 3) 0 4 4 part_5_3_0_4 part_5_3_4_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_3_8_8 : rangePass (graphPiece 5 3) 8 8 := by unfold rangePass; decide +kernel
private theorem part_5_3_0_16 : rangePass (graphPiece 5 3) 0 16 := @rangeJoin (graphPiece 5 3) 0 8 8 part_5_3_0_8 part_5_3_8_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_3_16_16 : rangePass (graphPiece 5 3) 16 16 := by unfold rangePass; decide +kernel
private theorem part_5_3_0_32 : rangePass (graphPiece 5 3) 0 32 := @rangeJoin (graphPiece 5 3) 0 16 16 part_5_3_0_16 part_5_3_16_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_3_32_2 : rangePass (graphPiece 5 3) 32 2 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_3_34_2 : rangePass (graphPiece 5 3) 34 2 := by unfold rangePass; decide +kernel
private theorem part_5_3_32_4 : rangePass (graphPiece 5 3) 32 4 := @rangeJoin (graphPiece 5 3) 32 2 2 part_5_3_32_2 part_5_3_34_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_3_36_4 : rangePass (graphPiece 5 3) 36 4 := by unfold rangePass; decide +kernel
private theorem part_5_3_32_8 : rangePass (graphPiece 5 3) 32 8 := @rangeJoin (graphPiece 5 3) 32 4 4 part_5_3_32_4 part_5_3_36_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_3_40_8 : rangePass (graphPiece 5 3) 40 8 := by unfold rangePass; decide +kernel
private theorem part_5_3_32_16 : rangePass (graphPiece 5 3) 32 16 := @rangeJoin (graphPiece 5 3) 32 8 8 part_5_3_32_8 part_5_3_40_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_3_48_16 : rangePass (graphPiece 5 3) 48 16 := by unfold rangePass; decide +kernel
private theorem part_5_3_32_32 : rangePass (graphPiece 5 3) 32 32 := @rangeJoin (graphPiece 5 3) 32 16 16 part_5_3_32_16 part_5_3_48_16
private theorem part_5_3 : rangePass (graphPiece 5 3) 0 64 := @rangeJoin (graphPiece 5 3) 0 32 32 part_5_3_0_32 part_5_3_32_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_7 : rangePass (graphPiece 5 7) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_11_0_1 : rangePass (graphPiece 5 11) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_11_1_1 : rangePass (graphPiece 5 11) 1 1 := by unfold rangePass; decide +kernel
private theorem part_5_11 : rangePass (graphPiece 5 11) 0 2 := @rangeJoin (graphPiece 5 11) 0 1 1 part_5_11_0_1 part_5_11_1_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_0_2 : rangePass (graphPiece 5 12) 0 2 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_2_2 : rangePass (graphPiece 5 12) 2 2 := by unfold rangePass; decide +kernel
private theorem part_5_12_0_4 : rangePass (graphPiece 5 12) 0 4 := @rangeJoin (graphPiece 5 12) 0 2 2 part_5_12_0_2 part_5_12_2_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_4_2 : rangePass (graphPiece 5 12) 4 2 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_6_2 : rangePass (graphPiece 5 12) 6 2 := by unfold rangePass; decide +kernel
private theorem part_5_12_4_4 : rangePass (graphPiece 5 12) 4 4 := @rangeJoin (graphPiece 5 12) 4 2 2 part_5_12_4_2 part_5_12_6_2
private theorem part_5_12_0_8 : rangePass (graphPiece 5 12) 0 8 := @rangeJoin (graphPiece 5 12) 0 4 4 part_5_12_0_4 part_5_12_4_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_8_8 : rangePass (graphPiece 5 12) 8 8 := by unfold rangePass; decide +kernel
private theorem part_5_12_0_16 : rangePass (graphPiece 5 12) 0 16 := @rangeJoin (graphPiece 5 12) 0 8 8 part_5_12_0_8 part_5_12_8_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_16_16 : rangePass (graphPiece 5 12) 16 16 := by unfold rangePass; decide +kernel
private theorem part_5_12_0_32 : rangePass (graphPiece 5 12) 0 32 := @rangeJoin (graphPiece 5 12) 0 16 16 part_5_12_0_16 part_5_12_16_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_32_4 : rangePass (graphPiece 5 12) 32 4 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_36_4 : rangePass (graphPiece 5 12) 36 4 := by unfold rangePass; decide +kernel
private theorem part_5_12_32_8 : rangePass (graphPiece 5 12) 32 8 := @rangeJoin (graphPiece 5 12) 32 4 4 part_5_12_32_4 part_5_12_36_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_40_8 : rangePass (graphPiece 5 12) 40 8 := by unfold rangePass; decide +kernel
private theorem part_5_12_32_16 : rangePass (graphPiece 5 12) 32 16 := @rangeJoin (graphPiece 5 12) 32 8 8 part_5_12_32_8 part_5_12_40_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_48_16 : rangePass (graphPiece 5 12) 48 16 := by unfold rangePass; decide +kernel
private theorem part_5_12_32_32 : rangePass (graphPiece 5 12) 32 32 := @rangeJoin (graphPiece 5 12) 32 16 16 part_5_12_32_16 part_5_12_48_16
private theorem part_5_12_0_64 : rangePass (graphPiece 5 12) 0 64 := @rangeJoin (graphPiece 5 12) 0 32 32 part_5_12_0_32 part_5_12_32_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_64_64 : rangePass (graphPiece 5 12) 64 64 := by unfold rangePass; decide +kernel
private theorem part_5_12_0_128 : rangePass (graphPiece 5 12) 0 128 := @rangeJoin (graphPiece 5 12) 0 64 64 part_5_12_0_64 part_5_12_64_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_128_128 : rangePass (graphPiece 5 12) 128 128 := by unfold rangePass; decide +kernel
private theorem part_5_12_0_256 : rangePass (graphPiece 5 12) 0 256 := @rangeJoin (graphPiece 5 12) 0 128 128 part_5_12_0_128 part_5_12_128_128
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_256_128 : rangePass (graphPiece 5 12) 256 128 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_384_128 : rangePass (graphPiece 5 12) 384 128 := by unfold rangePass; decide +kernel
private theorem part_5_12_256_256 : rangePass (graphPiece 5 12) 256 256 := @rangeJoin (graphPiece 5 12) 256 128 128 part_5_12_256_128 part_5_12_384_128
private theorem part_5_12_0_512 : rangePass (graphPiece 5 12) 0 512 := @rangeJoin (graphPiece 5 12) 0 256 256 part_5_12_0_256 part_5_12_256_256
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_512_64 : rangePass (graphPiece 5 12) 512 64 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_576_64 : rangePass (graphPiece 5 12) 576 64 := by unfold rangePass; decide +kernel
private theorem part_5_12_512_128 : rangePass (graphPiece 5 12) 512 128 := @rangeJoin (graphPiece 5 12) 512 64 64 part_5_12_512_64 part_5_12_576_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_640_128 : rangePass (graphPiece 5 12) 640 128 := by unfold rangePass; decide +kernel
private theorem part_5_12_512_256 : rangePass (graphPiece 5 12) 512 256 := @rangeJoin (graphPiece 5 12) 512 128 128 part_5_12_512_128 part_5_12_640_128
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_12_768_256 : rangePass (graphPiece 5 12) 768 256 := by unfold rangePass; decide +kernel
private theorem part_5_12_512_512 : rangePass (graphPiece 5 12) 512 512 := @rangeJoin (graphPiece 5 12) 512 256 256 part_5_12_512_256 part_5_12_768_256
private theorem part_5_12 : rangePass (graphPiece 5 12) 0 1024 := @rangeJoin (graphPiece 5 12) 0 512 512 part_5_12_0_512 part_5_12_512_512
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_13_0_2 : rangePass (graphPiece 5 13) 0 2 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_13_2_2 : rangePass (graphPiece 5 13) 2 2 := by unfold rangePass; decide +kernel
private theorem part_5_13_0_4 : rangePass (graphPiece 5 13) 0 4 := @rangeJoin (graphPiece 5 13) 0 2 2 part_5_13_0_2 part_5_13_2_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_13_4_4 : rangePass (graphPiece 5 13) 4 4 := by unfold rangePass; decide +kernel
private theorem part_5_13_0_8 : rangePass (graphPiece 5 13) 0 8 := @rangeJoin (graphPiece 5 13) 0 4 4 part_5_13_0_4 part_5_13_4_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_13_8_2 : rangePass (graphPiece 5 13) 8 2 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_13_10_2 : rangePass (graphPiece 5 13) 10 2 := by unfold rangePass; decide +kernel
private theorem part_5_13_8_4 : rangePass (graphPiece 5 13) 8 4 := @rangeJoin (graphPiece 5 13) 8 2 2 part_5_13_8_2 part_5_13_10_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_13_12_4 : rangePass (graphPiece 5 13) 12 4 := by unfold rangePass; decide +kernel
private theorem part_5_13_8_8 : rangePass (graphPiece 5 13) 8 8 := @rangeJoin (graphPiece 5 13) 8 4 4 part_5_13_8_4 part_5_13_12_4
private theorem part_5_13_0_16 : rangePass (graphPiece 5 13) 0 16 := @rangeJoin (graphPiece 5 13) 0 8 8 part_5_13_0_8 part_5_13_8_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_13_16_4 : rangePass (graphPiece 5 13) 16 4 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_13_20_4 : rangePass (graphPiece 5 13) 20 4 := by unfold rangePass; decide +kernel
private theorem part_5_13_16_8 : rangePass (graphPiece 5 13) 16 8 := @rangeJoin (graphPiece 5 13) 16 4 4 part_5_13_16_4 part_5_13_20_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_13_24_8 : rangePass (graphPiece 5 13) 24 8 := by unfold rangePass; decide +kernel
private theorem part_5_13_16_16 : rangePass (graphPiece 5 13) 16 16 := @rangeJoin (graphPiece 5 13) 16 8 8 part_5_13_16_8 part_5_13_24_8
private theorem part_5_13 : rangePass (graphPiece 5 13) 0 32 := @rangeJoin (graphPiece 5 13) 0 16 16 part_5_13_0_16 part_5_13_16_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_15 : rangePass (graphPiece 5 15) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_75 : rangePass (graphPiece 5 75) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_76_0_1 : rangePass (graphPiece 5 76) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_76_1_1 : rangePass (graphPiece 5 76) 1 1 := by unfold rangePass; decide +kernel
private theorem part_5_76_0_2 : rangePass (graphPiece 5 76) 0 2 := @rangeJoin (graphPiece 5 76) 0 1 1 part_5_76_0_1 part_5_76_1_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_76_2_1 : rangePass (graphPiece 5 76) 2 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_76_3_1 : rangePass (graphPiece 5 76) 3 1 := by unfold rangePass; decide +kernel
private theorem part_5_76_2_2 : rangePass (graphPiece 5 76) 2 2 := @rangeJoin (graphPiece 5 76) 2 1 1 part_5_76_2_1 part_5_76_3_1
private theorem part_5_76_0_4 : rangePass (graphPiece 5 76) 0 4 := @rangeJoin (graphPiece 5 76) 0 2 2 part_5_76_0_2 part_5_76_2_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_76_4_2 : rangePass (graphPiece 5 76) 4 2 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_76_6_2 : rangePass (graphPiece 5 76) 6 2 := by unfold rangePass; decide +kernel
private theorem part_5_76_4_4 : rangePass (graphPiece 5 76) 4 4 := @rangeJoin (graphPiece 5 76) 4 2 2 part_5_76_4_2 part_5_76_6_2
private theorem part_5_76_0_8 : rangePass (graphPiece 5 76) 0 8 := @rangeJoin (graphPiece 5 76) 0 4 4 part_5_76_0_4 part_5_76_4_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_76_8_8 : rangePass (graphPiece 5 76) 8 8 := by unfold rangePass; decide +kernel
private theorem part_5_76_0_16 : rangePass (graphPiece 5 76) 0 16 := @rangeJoin (graphPiece 5 76) 0 8 8 part_5_76_0_8 part_5_76_8_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_76_16_16 : rangePass (graphPiece 5 76) 16 16 := by unfold rangePass; decide +kernel
private theorem part_5_76_0_32 : rangePass (graphPiece 5 76) 0 32 := @rangeJoin (graphPiece 5 76) 0 16 16 part_5_76_0_16 part_5_76_16_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_76_32_4 : rangePass (graphPiece 5 76) 32 4 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_76_36_4 : rangePass (graphPiece 5 76) 36 4 := by unfold rangePass; decide +kernel
private theorem part_5_76_32_8 : rangePass (graphPiece 5 76) 32 8 := @rangeJoin (graphPiece 5 76) 32 4 4 part_5_76_32_4 part_5_76_36_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_76_40_8 : rangePass (graphPiece 5 76) 40 8 := by unfold rangePass; decide +kernel
private theorem part_5_76_32_16 : rangePass (graphPiece 5 76) 32 16 := @rangeJoin (graphPiece 5 76) 32 8 8 part_5_76_32_8 part_5_76_40_8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_76_48_16 : rangePass (graphPiece 5 76) 48 16 := by unfold rangePass; decide +kernel
private theorem part_5_76_32_32 : rangePass (graphPiece 5 76) 32 32 := @rangeJoin (graphPiece 5 76) 32 16 16 part_5_76_32_16 part_5_76_48_16
private theorem part_5_76 : rangePass (graphPiece 5 76) 0 64 := @rangeJoin (graphPiece 5 76) 0 32 32 part_5_76_0_32 part_5_76_32_32
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_77_0_1 : rangePass (graphPiece 5 77) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_77_1_1 : rangePass (graphPiece 5 77) 1 1 := by unfold rangePass; decide +kernel
private theorem part_5_77 : rangePass (graphPiece 5 77) 0 2 := @rangeJoin (graphPiece 5 77) 0 1 1 part_5_77_0_1 part_5_77_1_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_79 : rangePass (graphPiece 5 79) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_86_0_1 : rangePass (graphPiece 5 86) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_86_1_1 : rangePass (graphPiece 5 86) 1 1 := by unfold rangePass; decide +kernel
private theorem part_5_86_0_2 : rangePass (graphPiece 5 86) 0 2 := @rangeJoin (graphPiece 5 86) 0 1 1 part_5_86_0_1 part_5_86_1_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_86_2_2 : rangePass (graphPiece 5 86) 2 2 := by unfold rangePass; decide +kernel
private theorem part_5_86_0_4 : rangePass (graphPiece 5 86) 0 4 := @rangeJoin (graphPiece 5 86) 0 2 2 part_5_86_0_2 part_5_86_2_2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_86_4_4 : rangePass (graphPiece 5 86) 4 4 := by unfold rangePass; decide +kernel
private theorem part_5_86 : rangePass (graphPiece 5 86) 0 8 := @rangeJoin (graphPiece 5 86) 0 4 4 part_5_86_0_4 part_5_86_4_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_87 : rangePass (graphPiece 5 87) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_116 : rangePass (graphPiece 5 116) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_117 : rangePass (graphPiece 5 117) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_235 : rangePass (graphPiece 5 235) 0 1 := by unfold rangePass; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem part_5_236 : rangePass (graphPiece 5 236) 0 1 := by unfold rangePass; decide +kernel

private theorem everyPiece (t : Nat) (ht : 2 ≤ t) (ht' : t ≤ 5) (c : Nat) (hc : c ∈ coreCodes t) :
    rangePass (graphPiece t c) 0 (2^(prefixDepth t c)) := by
  interval_cases t
  · simp only [coreCodes,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · exact part_2_0
    · exact part_2_1
  · simp only [coreCodes,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact part_3_0
    · exact part_3_1
    · exact part_3_3
    · exact part_3_7
  · simp only [coreCodes,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact part_4_0
    · exact part_4_1
    · exact part_4_3
    · exact part_4_7
    · exact part_4_11
    · exact part_4_12
    · exact part_4_13
    · exact part_4_15
  · simp only [coreCodes,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact part_5_0
    · exact part_5_1
    · exact part_5_3
    · exact part_5_7
    · exact part_5_11
    · exact part_5_12
    · exact part_5_13
    · exact part_5_15
    · exact part_5_75
    · exact part_5_76
    · exact part_5_77
    · exact part_5_79
    · exact part_5_86
    · exact part_5_87
    · exact part_5_116
    · exact part_5_117
    · exact part_5_235
    · exact part_5_236

set_option maxRecDepth 16384 in
private theorem andCatalogueSize : andCatalogue.size = 361 := by decide +kernel

private theorem knownGraphs (idx t : Nat) (rows : List Nat) (ht : t ≤ 5)
    (entry : andCatalogue[idx]? = some (t,rows))
    (J : SimpleGraph (Fin rows.length))
    (model : ∀ i j, (rows.getD i.val 0).testBit j.val = true ↔ J.Adj i j) : AndBound _ t J := by
  have bound : idx < andCatalogue.size := by
    by_contra! bad
    rw [Array.getElem?_eq_none (by omega)] at entry
    contradiction
  have size := andCatalogueSize
  intro C A hm he hA
  obtain ⟨D,hsize,_,hD⟩ := collapse_and_count J C A hm he hA
  exact (andCatalogue_bound idx (by omega) rows (by simp [entry]) rfl ht J model D hD).trans hsize


private theorem allCatalogueSmall : andCatalogue.all (fun r => decide (r.1 ≤ 5)) = true := by decide +kernel

private theorem orbitPositive (t c : Nat) (ls : List Nat) (i : Nat) (ht : 2 ≤ t) (ht' : t ≤ 5)
    (h : orbitRead (orbitBank t c) ls i = true)
    (J : SimpleGraph (Fin (t+ls.length)))
    (model : ∀ a b, splitEdge t c ls a.val b.val = true ↔ J.Adj a b) : AndBound _ t J := by
  apply orbitRead_sound ht ht' andCatalogue (orbitBank t c) (orbitBanksValid t c) _ ls i h J model
  intro idx s rows entry
  have bounded := Array.all_eq_true_iff_forall_mem.mp allCatalogueSmall (s,rows) (Array.mem_of_getElem? entry)
  exact knownGraphs idx s rows (of_decide_eq_true bounded) entry

end PEqualNP.Outside.L_meta_217

open PEqualNP.Outside.L_meta_217

theorem PEqualNP.Outside.L_meta_217 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), t ≤ 5 → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → ∀ A : Finset ℕ, (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → t ≤ A.card := by
  intro n t G C ht hf hl hm he A hA
  exact rank_from_countdown (fun t c => (orbitBank t c).acts) countdownWord
    (fun t c => orbitRead (orbitBank t c)) prefixDepth countdownStart allActions everyPiece orbitPositive G ht hf hl C A hm he hA
